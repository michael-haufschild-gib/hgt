# CLG/TTF compensated arithmetic pairing — sign still open

User's latest scope: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` is READ ONLY. Do not modify or revert concurrent changes there. Full chain remains literal theta source → all signed center-mixed Hankel forms nonnegative → Fourier current → Xi orientation → RH. No unconditional RH proof/falsification obtained. Goal active; no external blocking condition.

Direct attempt and paper proof checkpoint: `docs/drafts/pipeline/1-in-progress/clg-ttf-all-polynomial-source-energy.md`, section `Retain the seed's zero mean inside each arithmetic cell`, equations (13)–(19). This extends `mem:rh_frontier/clg_ttf_arithmetic_square_attempt_2026_09_07`.

Using actual seed g(t)=(4π²t⁴−6πt²)e^(−πt²), define φ_t(x)=e^(x/2)g(t e^x), φ_0=0, and R_n=φ_n−∫_n^(n+1)φ_t dt, n≥0. Existing Lean seed zero-mean theorem implies ΣR_n=Φ pointwise. Primitive g=−2π d/dt(t³e^(−πt²)) gives R_0=2πe^(5x/2)e^(−πe^(2x)) and explicit endpoint corrections for all n.

For |a|<1/2, σ=a+1/2>0, K_a=e^(ay)φ_1(y): e^(ax)φ_t=t^(−σ)K_a(x+log t), scale derivative=t^(−σ−1)(K_a'−σK_a)(x+log t). FTC/Minkowski yields ||x^k D^j(e^(ax)R_n)||_p ≤ C n^(−σ−1)(1+log(n+1))^k for p=1,2 and every fixed j,k. Hence every fixed polynomial filtered signed current is legitimate absolutely convergent full double pairing. This repairs raw full-line Fubini but supplies no sign.

At s=σ−ib transforms are F_R0=A(s)/(s−1), F_Rn=A(s)[n^(−s)−∫_n^(n+1)t^(−s)dt]. Complete bracket = continuum-subtracted zeta continuation. Thus no independent sign-producing arithmetic identity obtained.

Stronger diagnostic, PAPER ONLY: Taylor in cell parameter gives n^(3/2)R_n(y−log n)=B(y)+O(1/n) in weighted Schwartz seminorms, B=φ_1/4−φ_1'/2≠0. For fixed nonzero real polynomial r and f_n=r(−iD)(e^(ax)R_n), recentered n^(σ+1)f_n→r(−iD)(e^(ay)B)≠0 with O(1/n) weighted L2 control. Therefore 2∫x|f_n|²/||f_n||²=−2log n+O(1); every fixed filter's large-cell diagonal current is negative. Does not determine full cross-sum sign.

Exact unfiltered pair PAPER formula: β=a+5/2, P=u²+v², h=u²v²/P², u,v>0: I_a(u,v)=∫e^(2ax)φ_uφ_v=2π²u²v²(πP)^(−β)Γ(β)[9−6β+4β(β+1)h]. At a=0 bracket −6+35h changes sign (positive diagonal, negative u=1,v=3). Gram positivity does not imply positivity of its aperture derivative. No full compensated cross-pair estimate established.

STATUS extended only the existing CANNOT-THETA-SHELL-FUBINI entry with this admissible replacement and essential cross terms; explicit paper/not-Lean status. CLG/TTF not retired. No Lean source edits, new theorem, audit, build, or numerical computation this turn. Scoped git diff --check passed. Final process inspection showed no lake build/lake env lean/lean process. No owned process to clean up. No commits/pushes.

Next work must directly attack full all-order sign with actual arithmetic identity. Do not promote repaired convergence, finite coefficient queues, receiver equivalences, or more routine no-go infrastructure as significant RH proof progress. The proved sign gap is unchanged.
