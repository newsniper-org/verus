<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# `.local-backlog/` — 내부 전용, **미러 대상이 아님**

이 트리는 **와이어가 아닙니다.**

와이어는 다음 네 디렉터리뿐입니다:

- `.local-replies-to/<peer>/`   — 우리가 보내는 것
- `.local-replies-from/<peer>/` — 우리가 받은 것(미러)
- `.local-requests-to/<peer>/`
- `.local-requests-from/<peer>/`

그 네 트리에 파일을 떨어뜨리는 행위는 **프로젝트 상태에 대한 주장**이고,
상대는 그것을 실제 산출물로 읽습니다(2026-09-06에 실제로 그렇게 됐습니다 —
설계-패스 프로브가 코퍼스 디렉터리에 떨어져 adsmt가 "재생성이 돌고 있다"고
믿고 URGENT 통지를 냈습니다).

따라서 **발신 전 초안·내부 대조표·미결 추적은 전부 여기**에 둡니다.
여기 있는 것은 어떤 것도 상대에게 전달되지 않습니다.
