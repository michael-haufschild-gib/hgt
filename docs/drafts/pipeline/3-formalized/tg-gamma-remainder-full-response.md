# TG C9.17: full actual Gamma remainder admission

- **Stage:** 3-formalized
- **Route:** TG, source-faithful Gamma endpoint completion
- **Statement:** For every positive aperture and finite physical time-band window, the literal Gamma remainder operators composed with the time-band operator converge in Schatten-one norm under every cofinal removal of both Gamma cutoffs. The complete original Sonin response pair has the same cutoff-independent admission.
- **Lean:** both leaf final audits pass, empty diagnostics; all seventeen foundation queries standard only, index verified, no own lint finding

## Dependency-closed paper proof

Put r(u)=gamma(u)/u-1/(2u^2) and Delta(u)=D_exp(u)+D_exp(-u)-2I.
For eps>0 define K_(eps,R)f=integral_[eps,R] r(u)Delta(u)f du.
The vector orbit is continuous and has norm <=4||f||. On this compact
interval r is continuous. Its strong integral is therefore a bounded
complex-linear map with norm <=4 integral |r|; no Bochner integral in
the operator norm is used. Its ground action is exactly the difference
of the actual truncated Gamma and homogeneous principal vectors.

Passing each bounded intertwiner through the strong integral proves
commutation with monomial transfer, parity and reflection. Fourier
reverses u and the symmetric difference is invariant. Adjoint reversal
of dilation and reality of r prove self-adjointness of the full integral.
For ANY difference K between two such cutoffs, the corpus's exact
monomial identity f_n=a^n P_n T_n f_0 therefore yields
 ||Kf_n||^2+a^(2n)n(n+1)||R_(n+1/2)Kf_0||^2=a^(2n)||Kf_0||^2.
Thus ||Kf_n||<=a^n||Kf_0||, without a cutoff-dependent operator norm.

The actual physical Fourier Taylor terms A_n have output in span(f_n),
and sum in operator norm to the original time-band operator A.
The exact monomial masses imply a^n||f_0||<=(n+1)||f_n||. Consequently
 ||K A_n|| <= (||Kf_0||/||f_0||)(n+1)||A_n||.
Each KA_n has rank at most one; its trace norm equals its operator norm.
The known factorial weighted series is summable, so the series converges
in the genuine complete Schatten-one space. Its bounded-operator image
is exactly KA. Therefore
 ||KA||_1 <= C(a,c,d)||Kf_0||,
 C=(sum_n (n+1)||A_n||)/||f_0||,
for every two-cutoff difference, with all source coefficients preserved.

C9.14 proves that K_(eps,R)f_0 converges to its actual full Bochner
remainder g. For the canonical exhaustion eps_n=1/(n+1), R_n=n,
the preceding bound makes K_n A a Cauchy sequence in Schatten one.
Let T be its actual limit. Fixing ANY other finite cutoff and passing
the same difference bound along this exhaustion proves
 ||K_(eps,R)A-T||_1 <= C ||K_(eps,R)f_0-g||.
This proves convergence to the SAME T for every cofinal family, with
no relation between its two endpoints, and no arithmetic assumption.
The canonical exhaustion is an existence construction, not a restriction
on allowed Gamma cutoffs or the final limit.

For the full response use actual projections A0,B0, correction J and
right factor W. The established identity
 J=A0 B0(1-A0 W)+B0 A0 W
and Fourier time-band factorization show that the fixed bounded nuclear
map L(T)=reflection*T*Fourier*(1-A0 W)+inverseFourier*T*W sends K A
to KJ, using the proved reflection and inverse-Fourier commutations.
The two left-source components coincide because K is self-adjoint.
The corpus's bounded paired-response map applied to (L(T),L(T)) is
therefore the limit of the complete original response pair. Every finite
source is identified before passage to the limit.

## Scope

This closes the full relative Gamma remainder admission, not the raw
Gamma endpoint. The singular homogeneous reference remains retained.
Its actual functional-calculus domain, the arithmetic energy summability,
original Hardy identification and strict sub-unit law remain open.
Neither an RH proof nor an RH falsification is claimed.

## Targeted Lean verification

`SoninGammaRemainderOperator.lean` and `SoninGammaRemainderResponse.lean`
both pass `lake --old env lean <leaf> -o <olean>` in formal/, exit 0 with
empty diagnostics. Seventeen public declarations; both leaves wired.
All seventeen foundation queries pass with only propext, Classical.choice
and Quot.sound. Index exits 0; all seventeen public declarations verified.
Global lint exits 1 on thirteen unrelated unreachable modules, with no own
finding; exact diagnostics in /tmp/tg-c917-lint.log. No umbrella/full build was used.
An initial completion-proof elaboration timeout was resolved by isolating
the exact distance bound and using `using!` for the existing norm-instance
representations. No heartbeat setting was raised.
