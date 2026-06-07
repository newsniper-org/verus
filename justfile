# Path to Claude Code's auto-memory dir for this project.
# Derived from the absolute project path by replacing `/` with `-`,
# matching the encoding Claude Code uses under ~/.claude/projects/.
_memory_dir := env_var("HOME") + "/.claude/projects/" + replace(justfile_directory(), "/", "-") + "/memory"

# Latest session UUID is mirrored to a stable path for resume helpers.
_session_file := justfile_directory() + "/.claude-latest-session-id"

# Default: list available recipes.
default:
    @just --list

# Safe to re-run; rsync makes updates incremental.
# Mirror Claude Code's auto-memory into .claude-memories/ for version control.
mirror-memory:
    @mkdir -p .claude-memories
    @if [ -d "{{_memory_dir}}" ] && [ -n "$(ls -A '{{_memory_dir}}' 2>/dev/null)" ]; then \
        rsync -a --delete '{{_memory_dir}}/' .claude-memories/ ; \
        echo "✓ Mirrored {{_memory_dir}} → .claude-memories/" ; \
    else \
        echo "⚠ {{_memory_dir}} is empty or missing — nothing to mirror" ; \
    fi

# Depends on `mirror-memory` so the auto-memory snapshot travels
# alongside the reply.  No-op when `.local-replies-to/<recipient>/`
# is empty or missing.  rsync without --delete (replies accumulate).
# Example:
#   just mirror-local-replies-to adsmt ~/AD1/.local-replies-from/verus-fork/
# Mirror a recipient's reply outbox to their expected inbox path.
mirror-local-replies-to recipient target: mirror-memory
    @src=".local-replies-to/{{recipient}}" ; \
        if [ -d "$src" ] && [ -n "$(ls -A "$src" 2>/dev/null)" ]; then \
            mkdir -p '{{target}}' ; \
            rsync -a "$src/" '{{target}}' ; \
            echo "✓ Mirrored $src/ → {{target}}" ; \
        else \
            echo "⚠ $src/ empty or missing — nothing to mirror to {{target}}" ; \
        fi

# Use after a system update or fresh checkout to pick up where you left off.
# Restore Claude Code memory from .claude-memories/ and print a resume hint.
claude-resume:
    @echo "=== verus-fork: Claude Code resume helper ==="
    @echo ""
    @if [ -d .claude-memories ] && [ -n "$(ls -A .claude-memories 2>/dev/null)" ]; then \
        mkdir -p '{{_memory_dir}}' ; \
        rsync -a .claude-memories/ '{{_memory_dir}}/' ; \
        echo "✓ Restored .claude-memories/ → {{_memory_dir}}" ; \
    else \
        echo "⚠ .claude-memories/ empty or missing — nothing to restore" ; \
    fi
    @echo ""
    @latest=$(ls -t .claude-conversations/*.md 2>/dev/null | head -1); \
    if [ -n "$latest" ]; then \
        echo "Latest design conversation: $latest" ; \
        echo "  Size: $(wc -l < "$latest") lines" ; \
    else \
        echo "No .claude-conversations/ logs found." ; \
    fi
    @echo ""
    @if [ -f "{{_session_file}}" ]; then \
        echo "Last recorded session: $(cat '{{_session_file}}')" ; \
    fi
    @echo ""
    @echo "To resume context, start Claude Code in this directory and ask:"
    @echo "  \"Read the latest file in .claude-conversations/ and continue.\""

# Other Claude Code agents (in unrelated working dirs) pull the
# snapshot from there on demand.  Always safe to run.
# Refresh the read-only status snapshot at ~/verus-fork-status/.
status:
    @scripts/snapshot-status.sh
    @echo "✓ Snapshot refreshed at ${VERUS_FORK_STATUS_DIR:-$HOME/verus-fork-status}/"
    @echo "  HEAD: $(cat ${VERUS_FORK_STATUS_DIR:-$HOME/verus-fork-status}/head.txt)"

# §3.5.H — bake the adsmt AOT prelude bank (.luart-cdcl) and print the
# `export VERUS_ADSMT_AOT_LUART=…` activation line.  Frontend-agnostic:
# `just aot-bake-prelude` bakes the Verus prelude; pass `--from-smt2 <f>` for
# an arbitrary SMT-LIB axiom set.  Cache dir is $VERUS_ADSMT_AOT_CACHE_DIR
# (default target-verus/release/aot).  Activate with:
#   eval "$(just aot-bake-prelude --quiet)"
# Bake the adsmt AOT prelude bank + print its activation line.
aot-bake-prelude *ARGS:
    @scripts/aot-bake-prelude.sh {{ARGS}}

# Slow — runs the full workspace suite.  Run before sharing the
# snapshot externally if the count matters to the consumer.
# Run the test suite and cache the passing count in the snapshot.
status-tests:
    @echo "Running cargo test --workspace --all-features (this takes a minute)..."
    @count=$(cargo test --workspace --all-features 2>&1 | awk '/^test result/ { ok+=$4 } END { print ok }'); \
        echo "$count tests passing as of $(date -u +%Y-%m-%dT%H:%M:%SZ)" \
            > "${VERUS_FORK_STATUS_DIR:-$HOME/verus-fork-status}/tests.txt" ; \
        echo "✓ tests.txt updated: $count passing"
    @just status

# Auto-refresh the status snapshot after every commit.  OFF by
# default — opt in here; undo with `just uninstall-status-hook`.
# Wire snapshot-status.sh into the git post-commit hook.
install-status-hook:
    @mkdir -p .git/hooks
    @printf '#!/usr/bin/env bash\nset +e\n"$(git rev-parse --show-toplevel)/scripts/snapshot-status.sh" 2>/dev/null\nexit 0\n' \
        > .git/hooks/post-commit
    @chmod +x .git/hooks/post-commit
    @echo "✓ Installed .git/hooks/post-commit — snapshot will refresh after every commit"

# Remove the post-commit status-refresh hook from `install-status-hook`.
uninstall-status-hook:
    @if [ -f .git/hooks/post-commit ]; then \
        rm -f .git/hooks/post-commit ; \
        echo "✓ Removed .git/hooks/post-commit" ; \
    else \
        echo "⚠ No .git/hooks/post-commit installed" ; \
    fi
