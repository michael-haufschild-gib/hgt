# Mass-shifted hard-edge adaptive bilinear arithmetic source

Formalized exact source-first producer requested for §9.3.

- `RHTower.XiShiftedHardEdgeAdaptiveArithmeticSourceLaw`: reciprocal clearing `C_{y,N}P=(Ref_N P)(y+U)` conjugates adaptive bilinear shear to reverse Euler:
  `C_{y,M+N+2}(A_ad(A,B)) = R_{y,M+N+2}(C_{y,M}A * C_{y,N}B)`, where `R_{y,d}S=d*S-(U+y)S'`.
- Arithmetic capstones identify completed bilinear and mixed-amplitude `P^sharp` aggregates with this landing before reflection aggregation. This is amplitude/admission-sensitive and source-first, not fixed reporting.
- Exact affine obstruction: `A=1-(y+a)X`, `a>0`, gives a negative source value at `U=(3a+y)/2`, namely `-(a+y)^2/2`. Pointwise/coefficientwise positivity is false.
- `RHTower.XiShiftedHardEdgeHausdorffDiagonalLanding`: inverse clearing satisfies `U_{y,D}(U^j)=X^(D-j)(1-yX)^j`; any moment pairing becomes a complete scaled-Hausdorff diagonal sum. Reverse Euler coefficient law is `(d-k)S_k-y(k+1)S_(k+1)`, and `R_{y,d}` has zero kernel on polynomials of degree `<d`. Thus producer loses no finite information.
- Complete-diagonal arithmetic capstones formalized for bilinear and mixed completed sources.
- `RHTower.XiShiftedCanonicalAdmissionHardEdgeSourceLaw` inserts actual inverse-Hankel admission into this producer. On every `(n+2)` positive Hankel chamber, its mixed-sign complete-diagonal aggregate equals `2 h_n E_n > 0`; a nonpositive actual aggregate therefore certifies chamber failure with no admission-mismatch branch. Targeted build passed `11755/11755`; four capstones have only standard axioms.
- Both modules wired into `RHTower.lean`; direct Lean and targeted builds passed (`11753/11753`, `11754/11754`); axiom audits only `propext`, `Classical.choice`, `Quot.sound`; forbidden scan and `git diff --check` clean.
- Report equations §9.3 (9.3.498)–(9.3.511); stage-3 card `mass-shifted-hard-edge-adaptive-arithmetic-source-law.md`.

Exact remaining gate: prove admitted complete-diagonal pairing of `2((N+1)S^2-(y+U)SS')` is nonnegative along actual cofinal `N≈sqrt(y)`. Admission/null-flag constraints must kill paired transport negative mass; pointwise sign cannot. RH not proved.