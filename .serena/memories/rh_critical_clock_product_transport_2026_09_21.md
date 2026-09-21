# Actual critical clock product and density cancellation

New certified module `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalClockProductTransport.lean`; own paper/fact card `docs/drafts/pipeline/3-formalized/rh-critical-clock-product-transport.md`. Do not redo the off-critical single-head moment result.

Source g_P(t)=H_P(exp t)/exp t is EXACTLY the original normalized Mobius-divisor Abel current at fully processed integer walls (`mobiusDivisorCriticalClockHead_complete_integer_wall`). Prime insertion is g_(P+p)(t)=g_P(t)-g_P(t-log p)/sqrt(p), with no source sign assumptions.

Finite pairing C_P(y,T)=integral_(t<=T) g_P(t+y)g_P(t) equals the actual normalized arithmetic product with clock measure dx/x. Joint insertion/cutoff shift a=log p retains BOTH endpoints: C_new(y,T+a)=C(y,T+a)+C(y,T)/p-[C(y+a,T)+C(y-a,T+a)]/sqrt(p). Finite reciprocity C(y,T)=C(-y,T+y). All integrability facts supplied.

Literal triangular pairing D_P(y,T)=integral_(t<=T)(1-t/T)g_P(t+y)g_P(t); A_P=T D_P holds also at T=0 because source vanishes at nonpositive times. Same joint law for A preserves every old/new clock factor. Original weight is not replaced by stronger single-head decay.

Capstone `RHTower.mobiusDivisorCriticalClockTriangularPairing_density_cancellation` (line589 at creation): rho_P=squarefreeDensity*prod_(q in P) q/(q+1), rho_new=rho_P*p/(p+1). Exact balance
rho_new*A_new(0,T+a)-rho_P*A_P(0,T+a)+2*rho_P*sqrt(p)/(p+1)*A_P(a,T)
= -rho_P/(p+1)*(A_P(0,T+a)-A_P(0,T)) <=0.
The actual density absorbs the positive copied diagonal; the remaining negative boundary surplus is proved from age-diagonal monotonicity. Public statement quantifies all finite Nat.Primes cores, every prime, every real cutoff, using erased core to handle existing membership unconditionally.

LIMITS: This does not bound the remaining signed correlation through exhaustive cores. rho is the actual density of the corpus's physical fixed-core profile; no uniform identification with finite arithmetic selection energy as core varies is proved. Need cumulative mixed-correlation control AND uniform finite-counting comparison/exhaustion for RH. The quadratic triangular observable is not asserted equal to scalar Suzuki prime-polar action.

Validation: scratch lake env lean passed; all audited capstones use only propext, Classical.choice, Quot.sound. Named final lake build GaloisForLFunctions.RHTower.MobiusDivisorCriticalClockProductTransport passed (120s); umbrella wired; no full/umbrella build; index and whitespace checks passed. Global lint still FAILED on same 4 unrelated unreachable modules named in own card, no error for this module. All owned Lean/search jobs terminal; scratch Lean removed. No commit/push or edits to shared frontier/other agents' logs.
