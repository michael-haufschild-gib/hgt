# Birmingham--Mokhtari augmented Einstein mode evaluation

- **ID:** hawking-bm-augmented-einstein-mode-evaluation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Birmingham--Mokhtari `hep-th/0609028` · exact BM modules
- **Statement:** Determine the full gauge-fixed Einstein three-jet and causal quadratic responses on exact `d=4`, `M=0` Birmingham--Mokhtari modes, including horizon charge closure and angular mode products.

## Goal
Evaluate the total nonlinear `++-` return from the Einstein boundary problem rather than assigning a scalar reciprocal-Jost factor to an unevaluated source.

## Gates
- [x] 0 → 1  in-progress: exact linear modes, composite frequencies, and nonlinear data requirements identified
- [ ] 1 → 2  fully-proven: full augmented source and causal Green kernels evaluated
- [ ] 2 → 3  formalized: closed theorem formalized and axiom-audited
- [ ] 3 → 4  publication-ready: standalone proof with source conventions and novelty audit

## Approach
Let `chi` be the BM angular square root, `d_n=2n+3/2`, `omega₊=chi-I*d_n`, and `omega₋=-chi-I*d_k`. Time-translation invariance fixes

`Omega₊₊=2*chi-I*(4n+3)`,

`Omega₊₋=-I*(2n+2k+3)`,

`Omega₊₊₋=chi-I*(4n+2k+9/2)`.

For BM connection parameters

`A=3/4-I*(omega-chi)/2`, `B=3/4-I*(omega+chi)/2`, `c=1-I*omega`,

the exact channel values are

`A(Omega₊₊)=-2n-3/4-I*chi/2`,

`B(Omega₊₊)=-2n-3/4-3I*chi/2`,

`c(Omega₊₋)=-N`, `N=2n+2k+2`,

`A(Omega₊₋)=-n-k-3/4+I*chi/2`,

`B(Omega₊₋)=-n-k-3/4-I*chi/2`,

`A(Omega₊₊₋)=-2n-k-3/2`.

Let `S` and `V` be the forbidden constant-branch and decaying-branch coefficients in the BM boundary expansion. With `a=A-1/2` and `b=B-1/2`,

`S=Gamma(c) Gamma(1/2)/(Gamma(A) Gamma(B))`,

`V=Gamma(c) Gamma(-1/2)/(Gamma(a) Gamma(b))`.

The normalization-invariant boundary response is their projective ratio

`mathscr R(omega,chi)=V/S=-2 Gamma(A)Gamma(B)/(Gamma(A-1/2)Gamma(B-1/2))`.

The common `Gamma(c)` pole cancels. At the mixed Hawking--Matsubara frequency and real `chi`, conjugation gives the exact identity

`mathscr R₊₋=-2 |Gamma(-n-k-3/4+I*chi/2)/Gamma(-n-k-5/4+I*chi/2)|^2 < 0`.

All four Gamma arguments are quarter-shifted away from nonpositive integers, so `mathscr R₊₋` is finite and nonzero, including at `chi=0`. The pole of each separately horizon-normalized coefficient, and the associated logarithmic Frobenius representative, is not a pole of projective response. Likewise, the zero of reciprocal forbidden coefficient `1/S` is a normalization zero, not vanishing physical response. For the second harmonic,

`mathscr R₊₊=-2 Gamma(A₊₊)Gamma(B₊₊)/(Gamma(A₊₊-1/2)Gamma(B₊₊-1/2))`,

with `A₊₊` and `B₊₊` as above.

At the cubic frequency, `A(Omega₊₊₋)` is a negative half-integer. Hence the same-fibre plus Jost factor is nonzero, and for `Re chi != 0` so is the full radial Jost determinant. The local `++-` monomial misses every same-fibre BM QNM.

Actual `B` and `C` values require Kodama--Ishibashi metric reconstruction, gauge and boundary jets, horizon harmonic product coefficients, and radial source integrals. Use the one-sided transform `fhat(omega)=int_0^infinity exp(I*omega*t)f(t)dt`. For a causal BM monomial, `H(t)exp(-I*Omega*t)` transforms to `I/(omega-Omega)`. If `Y_lambda` is a complete horizon harmonic system, source-faithful causal responses have the form

`uhat₊₊(omega,r) = -I sum_lambda Y_lambda/(omega-Omega₊₊) int G^ret_lambda(r,r';omega) S_{lambda,++}(r') dr'`,

`uhat₊₋(omega,r) = Mhat₀(omega,r)-I sum_lambda Y_lambda/(omega-Omega₊₋) int G^ret_lambda(r,r';omega) S_{lambda,+-}(r') dr'`.

`M₀` lies in the exceptional zero-frequency constraint kernel. A horizon-normalized Green representative may require a logarithmic finite part at `c=-N`, but its boundary response must reproduce the finite projective ratio above; the common `Gamma(c)` pole cannot act as physical gain. The direct third jet is

`C_aug(p,p,m)=exp(-I*Omega₊₊₋*t) sum_lambda C_{lambda,++-}(r)Y_lambda`,

including bulk, horizon, and outer-boundary components. BM eigenvalue/Jost data determine none of the coefficients `S_lambda`, `C_lambda`, or `M₀`: they depend on the chosen horizon eigenfunctions and their product algebra.

The bulk trace-reversed Einstein jet nevertheless has a closed coordinate-free form. With background derivative `nabla`, put

`H_h^mu_nu=gbar^(mu alpha) h_(alpha nu)`,

`K(h)^rho_(mu nu)=(1/2)gbar^(rho sigma)(nabla_mu h_(nu sigma)+nabla_nu h_(mu sigma)-nabla_sigma h_(mu nu))`,

`D(A)_(mu nu)=nabla_rho A^rho_(nu mu)-nabla_nu A^rho_(rho mu)`,

`Q(A,B)_(mu nu)=A^rho_(rho lambda)B^lambda_(nu mu)-A^rho_(nu lambda)B^lambda_(rho mu)`.

Define `U=H_p K(m)+H_m K(p)`, `V=H_p K(p)`, and

`W=H_p H_p K(m)+H_p H_m K(p)+H_m H_p K(p)`.

Expansion of `(gbar+h)^(-1)` in the exact connection-difference Ricci formula gives

`B_bulk(p,p)/2 = -D(V)+Q(K(p),K(p))`,

`B_bulk(p,m) = -D(U)+Q(K(p),K(m))+Q(K(m),K(p))`,

`C_bulk(p,p,m)/2 = D(W)-Q(K(p),U)-Q(U,K(p))-Q(K(m),V)-Q(V,K(m))`.

The cosmological term is linear and contributes nothing to `B_bulk` or `C_bulk`. Gauge-driver, ingoing-horizon, and AdS-boundary residuals contribute their own second and third jets. These formulas are the exact local tensors to reconstruct and project on BM harmonics; no scalar parity split substitutes for them.

The half-overtone miss excludes a coincident source/Jost pole, not a causal residue. For a half-line source `H(t) exp(-I Omega t)`, its Laplace transform is a Cauchy factor with nonzero value at every distinct QNM. Retarded `R₊₊` and `R₊₋` also contain homogeneous QNM tails and continuum contributions generated by turn-on. Therefore direct `C` and both cascades can contribute finite analytic numerators to a target simple Jost pole. Their exact contribution is a causal frequency convolution, not a grade projection or evaluation at `Omega₊₊₋` alone.

Writing `star` for causal frequency convolution, the total transformed source is

`Shat₊₊₋(omega)=B(phat star uhat₊₋)(omega)+B(mhat star uhat₊₊)(omega)+I*C_aug(p,p,m)/(2*(omega-Omega₊₊₋))`.

For a simple target BM pole `omega_*` with augmented adjoint state `ell_*`, the complete source section and response residue are

`Sigma_*=ell_*(Shat₊₊₋(omega_*))`,

`Res response at omega_* = Sigma_*/D_aug'(omega_*)`.

This is the required single contour expression: insert harmonic source coefficients into full retarded kernels, convolve time characters, add augmented third jet, then pair with target adjoint BM mode. Stationary constraint memory is one summand, not the whole section.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** BM linear master data contain no horizon harmonic multiplication coefficients, nonlinear metric reconstruction, augmented boundary jets, or sourced radial kernels. Equal linear eigenvalue/Jost data therefore do not determine `C`, `R₊₊`, or full `R₊₋`.
- **Strongest positive survivor:** Exact channel-frequency/Jost classification; normalization-invariant mixed response is a finite, nonzero, strictly negative norm-square; full residue requires a causal convolution numerator rather than an on-shell scalar Green factor.
- **New insight:** Hawking--Matsubara resonance changes a horizon-normalized Frobenius representative but not its projective boundary response. Local cubic source misses the QNM lattice, so it cannot create a higher coincident pole; causal turn-on can still contribute to the same simple-pole residue. Cancellation remains a full augmented causal-source problem among finite channels.
- **Status:** Frequency/Jost classification and projective `R₊₋`, `R₊₊` formulas are Lean-proved in `ThetaCuspHawkingBMCausalChannelEvaluation.lean` and `ThetaCuspHawkingBMProjectiveCausalResponse.lean`. Full sourced kernels and tensor coefficients remain open because horizon multiplication and augmented Einstein source data have not been supplied.

## Log
- 2026-08-25 — Entered Stage 1 after corpus and source audit.
- 2026-08-27 — Closed Gauss endpoint infrastructure without analytic-continuation premises:
  coefficient/GammaSeq asymptotics, absolute summability, contiguous transport, Euler-integral
  summation, and global nonresonant Gauss summation now compile in Lean.
- 2026-08-27 — Identified horizon-regular endpoint value and Wronskian-defined forbidden/source
  connection coefficient with literal BM Gamma coefficient. Open connection core is square-root
  Abel edge identifying normalizable coefficient with
  `Gamma(c) Gamma(-1/2)/(Gamma(a) Gamma(b))`; afterward, `LAND + DYN` still requires augmented
  causal-source projection and source-global equality.
- 2026-08-27 — Closed `HB-GAUSS-SQRT-ABEL` in Lean. Half-order coefficient asymptotics,
  complex Abel transfer, componentwise one-sided L'Hopital, exact forbidden/normalizable outer
  residues, and connection-phase uniqueness identify the Cramer normalizable coefficient with
  the literal BM decaying Gamma/Jost coefficient. Targeted build and axiom audit pass.

## Closed conjecture: square-root Abel connection edge

Label: `HB-GAUSS-SQRT-ABEL` — **PROVED IN LEAN**.

For ordinary coefficients `t_j(a,b,c)` with `c-a-b=1/2`, nonresonance gives

`sqrt(n) (n+1) t_(n+1) -> L := Gamma(c)/(Gamma(a)Gamma(b))`.

The corpus theorem `tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul`, applied to real and imaginary
parts, should therefore give

`sqrt(1-x) R'(x) -> sqrt(pi) L`, `x -> 1-`.

One-sided L'Hopital applied to

`(R(x)-R(1))/sqrt(1-x)`

then gives `-2 sqrt(pi) L = Gamma(-1/2)L`. Since forbidden outer factor is `1+O(1-x)` and
normalizable outer branch divided by `sqrt(1-x)` tends to `1`, exact connection phase forces

`RegularAdSNormalizableConnectionCoefficient = Gamma(c) Gamma(-1/2)/(Gamma(a)Gamma(b))`.

Hostile checks: use `Ico 0 1`/left-neighborhood filter conversion explicitly; justify every
real/imag `tsum` interchange from derivative-series summability inside radius one; prove derivative
of square root and denominator nonvanishing only eventually on `x<1`; use exact Gamma recurrence at
`-1/2`, not a remembered numerical identity. Failure of any transfer becomes new infrastructure,
not reason to abandon route.

Formal survivor:

`d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq`

in `ThetaCuspHawkingBMSecondHarmonicGaussSquareRootEndpoint.lean`. Its only axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Current conjecture: physical BM Green-cut incidence

Label: `HB-GREEN-CUT-INCIDENCE`.

### First infrastructure theorem: exact resonant regular branch

Hostile parameter audit found a half-shift defect in the existing monodromy coefficient: its
Pochhammer factors used BM connection exponents `RadialA/B`, while the literal mixed differential
operator uses original Gauss parameters
`HypergeometricA/B = RadialA/B - 1/2`. The Frobenius obstruction must use the latter. Every
definition and downstream theorem was corrected before Green-cut construction continued.

Let `N = 2n+2k+2`, `c=-N`, and let `a,b` be the original mixed hypergeometric parameters. Put

`F(z) = 2F1(a+N+1,b+N+1;N+2;z)` and `u(z)=z^(N+1)F(z)`.

The shifted denominator `N+2` is positive, so its Gauss series has radius one. Substituting

`u' = (N+1)z^N F + z^(N+1)F'`,

`u'' = N(N+1)z^(N-1)F + 2(N+1)z^N F' + z^(N+1)F''`

into `z(1-z)u'' + [-N-(a+b+1)z]u' - ab u` factors the result as `z^(N+1)` times

`z(1-z)F'' + [(N+2)-(a+b+2N+3)z]F' -(a+N+1)(b+N+1)F`,

which vanishes by the ordinary Gauss ODE. Hence `u` is the actual regular exponent-`N+1`
solution, with leading coefficient one. For a resonant companion `P_N + kappa*u*log z + tail`,
the order-`N` obstruction of `P_N` is `-(a+N)(b+N)q_N`; the non-log part of
`L(u log z)` has leading coefficient `N+1`. Thus

`kappa = (-1)^N (a)_(N+1)(b)_(N+1)/(N!(N+1)!)`,

now with the literal operator parameters. Lean now formalizes `u`, its two derivatives, original
mixed jet equation, unit-Wronskian renormalization, actual Xi-fibre monodromy mode, and corrected
nonzero leading horizon coefficient in
`ThetaCuspHawkingBMMixedHorizonRegularBranch.lean`. Targeted builds through the causal-optical
consumer pass, and axiom audit returns only `propext`, `Classical.choice`, and `Quot.sound`.

### Second infrastructure theorem: finite resonant truncation and terminal obstruction

Define

`q_j = ordinaryHypergeometricCoefficient a b (-N) j`

and `P_N(z)=sum_(j=0)^N q_j z^j`. For `j <= N`, the denominator
`(-N)_j` is nonzero; for `j=N+1`, it contains the zero factor `-N+N`, so Lean's field-valued
coefficient is exactly zero. Hence `q_0=1`, and for `j<N` the corpus recurrence gives

`(j+1)(j-N)q_(j+1)=(j+a)(j+b)q_j`.

At the top index,

`q_N=(-1)^N (a)_N(b)_N/(N!)^2`.

Writing

`L_(a,b,-N)y=z(1-z)y''+[-N-(a+b+1)z]y'-ab y`,

the coefficient of `z^j` in `L(P_N)` is

`(j+1)(j-N)q_(j+1)-(j+a)(j+b)q_j`.

Every coefficient below `N` vanishes, while the terminal coefficient is exactly

`-(N+a)(N+b)q_N`.

For the already constructed regular branch `u=z^(N+1)(1+O(z))`, the non-logarithmic part of
`L(u log z)` has leading coefficient `N+1` at `z^N`. Therefore the unique logarithmic scale
cancelling the terminal obstruction is

`kappa=(N+a)(N+b)q_N/(N+1)`

`      =(-1)^N(a)_(N+1)(b)_(N+1)/(N!(N+1)!)`.

Hostile checks: never invoke the generic successor recurrence at `j=N`; prove denominator
nonvanishing only for `j<=N`; prove `q_(N+1)=0` from the actual inverse-zero convention; retain the
analytic tail because `P_N+kappa*u*log z` cancels only the terminal coefficient, not the higher
non-logarithmic residual. First formalize these coefficient identities and terminal balance, then
construct the unique analytic tail recurrence and its convergent sum.

For that tail, put `A=a+N+1`, `B=b+N+1`, and

`f_k=ordinaryHypergeometricCoefficient A B (N+2) k`.

Define `r_0=0` and, for `k>=1`,

`r_k-r_(k-1)=1/(a+N+k)+1/(b+N+k)-1/k-1/(N+1+k)`.

Then the analytic part of a normalized companion is

`H(z)=P_N(z)+kappa*z^(N+1)*sum_(k>=0) f_k r_k z^k`,

and the full logarithmic solution is `Y(z)=H(z)+kappa*u(z)log z`. In Euler form, the
non-logarithmic forcing of `u log z` has coefficient

`g_m=(2m-N-1)u_m-(2m-2+a+b)u_(m-1)`.

At `m=N+1`, `g_(N+1)=N+1`, exactly cancelling the terminal truncation monomial. For
`m=N+1+k`, `k>=1`, the shifted Gauss recurrence reduces the remaining coefficient equation to
the displayed increment law for `r_k`. Thus every formal coefficient vanishes. This is DLMF
15.10.8 after the negative-integer parameter transport, but expressed by finite reciprocal sums
rather than digamma values; choosing `r_0=0` fixes the otherwise free additive multiple of `u`.

For physical BM parameters with `Re chi != 0`, all reciprocal denominators are nonzero and their
norms have a uniform coarse bound from the fixed nonzero imaginary part. Hence `|r_k|=O(k)`.
The shifted Gauss series and its derivative series converge for `|z|<1`, so
`sum f_k r_k z^k` converges there. This supplies the analytic tail without importing a digamma
continuation theorem.

Next proof obligation: formalize the finite truncation obstruction, build the full logarithmic
companion, prove its exact branch discontinuity, and sew endpoint-selected Green responses.

The corpus theorem `d4BMXiMixedHorizon_retardedSection_eq_advancedSection_iff` already reduces the
critical-line selector to three exact dynamical identities. Construct physical endpoint-selected
retarded and advanced `++` and `+-` response maps from the exact radial bases and Cauchy kernels,
then prove:

1. mixed retarded-minus-advanced response on the literal quadratic residual equals the actual
   Xi-fibre unit-Wronskian logarithmic monodromy mode;
2. nonresonant `++` retarded-minus-advanced response vanishes on the literal second-harmonic
   residual;
3. augmented Einstein cokernel pairing with the monodromy mode equals the exact horizon optical
   norm-square.

The first two statements are Green-kernel boundary-value theorems; the third is the missing
Einstein--Green reciprocity theorem. Birmingham--Mokhtari provides exact linear hypergeometric QNM
data, while available nonlinear-QNM literature gives general excitation/bilinear-form frameworks,
not these source-faithful topological-black-hole identities. Missing reconstruction and source
infrastructure must therefore be built rather than assumed.

Hostile checks: no abstract response maps may survive in final theorem; retarded/advanced labels
must be fixed by horizon and AdS boundary values, not sign conventions; direct third jet must cancel
only after forming complete causal cut; all radial integrals must use exact integrating measure and
unit Wronskian; reciprocity must include gauge, horizon, and AdS boundary terms; no positivity claim
may be analytically continued from real momentum to complex Xi momentum.

### Analytic closure of the resonant companion

Corpus search exposed `HTGeometry.DigammaGaussSeries`: each reciprocal-pair increment
`1/(j+1)-1/(s+j)` is absolutely summable when `Re s>0`. The tail increment is exactly
`-g_A(j)-g_B(j)+g_(N+2)(j)`. Therefore, in chamber `Re A>0` and `Re B>0`, its increment series is
absolutely summable and every partial sum `r_k` is bounded by one fixed `l1` norm. This strengthens
coarse `O(k)` estimate above to `O(1)` and proves logarithmic analytic tail has radius at least one,
same as shifted regular Gauss factor.

For arbitrary coefficient sequences `h,u`, absolute convergence of each scalar formal series on
`|z|<1`, together with exact formal identity
`E(h)+kappa*M(u)=0`, implies analytic Euler identity

`z^2(1-z)H''+(cz-(a+b+1)z^2)H'-abzH`
` + kappa*(2z(1-z)U'+(c-1-(a+b)z)U)=0`.

Proof is coefficient-faithful: multiply convergent value and derivative series by `z,z^2,z^3`,
identify each shifted coefficient with formal Euler and logarithmic-forcing coefficients, then use
uniqueness of sums. No termwise-differentiation premise beyond formal-series radius API is added.
Instantiating this lift with resonant `H,U` closes analytic non-logarithmic equation. Remaining local
step is product-rule reconstruction of `Y=H+kappa*U*log z` away from `z=0`, followed by explicit
sheet-jump identity `Y_+-Y_-=2*pi*i*kappa*U`.

Lean closure is stronger than this paper obligation: `Y` has two actual derivatives on principal
slit unit disk and satisfies homogeneous resonant Gauss equation there. On every Xi fibre, shifted
parameters lie in positive chamber, coefficientwise regular branch equals pre-existing exact BM
regular radial branch, and arbitrary two sheets separated by `2*pi*i` differ pointwise by
`d4BMXiMixedHorizonExactMonodromyMode`. Scalar source amplitudes therefore lift this deck action to
an explicit linear response map whose sheet difference is amplitude times exact monodromy mode.
This closes radial monodromy incidence after source projection. It does not identify nonlinear
Einstein quadratic residual's source projection; physical endpoint sewing and Einstein--Green
reciprocity remain next open core.

### Canonical finite-radiation optical landing

Let `V=C^4` be existing gauge-fixed BM radiation space and
`R=d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation amplitude orthogonalMixing q`. Define
complex-linear horizon optical reader

`pi_q(v)=d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient(q)*v_0`.

By definition, `pi_q(R)` is exact mixed-horizon optical source projection. Composing `pi_q` with
sheet response gives a concrete linear map `V -> (unit-disk radial functions)`, and sheet difference
on `R` is

`pi_q(R) * d4BMXiMixedHorizonExactMonodromyMode`.

Freeze first slot of Hermitian Gram at `R`:

`ell_R(v)=conj(pi_q(R))*pi_q(v)`.

This is complex-linear in `v`, while
`ell_R(R)=normSq(pi_q(R))=horizon orthogonal-helicity flux`. Multiplying deck coefficient by this
Gram gives exact Xi mixed causal optical section. This closes finite-radiation projection and Gram
cokernel algebra without falsely treating `normSq` itself as complex-linear. Remaining theorem is
geometric: prove augmented Einstein mixed residual maps to `R` under endpoint-sewn radial Green
operator and that its cyclic left-QNM pairing is this `ell_R`.

## Endpoint-sewn mixed Green conjecture and paper proof

Let `U` be resonant regular branch and `Y_sigma` logarithmic companion on sheet `sigma`. Write

`D_sigma(t)=t(1-t)(U(t)Y_sigma'(t)-U'(t)Y_sigma(t))`.

For two sheets with `log_+ - log_- = 2*pi*i`, Frobenius formula gives

`Y_+ - Y_- = M U`,  `Y_+' - Y_-' = M U'`,

where `M=2*pi*i*d4HypergeometricResonantFrobeniusLogCoefficient`. Hence

`D_+(t)-D_-(t)=t(1-t)(U(t) M U'(t)-U'(t) M U(t))=0`.

Define two endpoint pieces of Green kernel

`G_sigma^R(t,z)=U(t)Y_sigma(z)/D_sigma(t)`,
`G_sigma^L(t,z)=U(z)Y_sigma(t)/D_sigma(t)`.

They agree on diagonal. If `D_sigma(t) != 0`, their field-derivative jump obeys

`t(1-t)(partial_z G_sigma^R(t,t)-partial_z G_sigma^L(t,t))=1`.

More importantly, both sheet differences are same rank-one kernel:

`G_+^R-G_-^R = G_+^L-G_-^L = M * U(t)/D_-(t) * U(z)`.

Therefore every finite radial source packet has exact causal jump

`R_+(z)-R_-(z)=M*(sum_t source(t) U(t)/D_-(t))*U(z)`.

This derives mixed response incidence from endpoint sewing rather than declaring arbitrary scalar
sheet response. Remaining geometric bridge becomes exact projection identity: weighted radial
Einstein source integral must equal canonical finite-radiation optical reader. Literature supplies
Wronskian/Green template but not this BM resonant source identification; current corpus contains
`++` Cauchy and polarized Green identities, not mixed logarithmic endpoint sewing.

### Wronskian nondegeneracy conjecture

On physical mixed parameters, exponent balance is
`a+b+N+1=1/2`. Thus integrating factor is real
`p(t)=sqrt(1-t)/t^N`. For principal companion `Y` and regular branch `U`, set

`W_p(t)=p(t)(U(t)Y'(t)-U'(t)Y(t))`.

Both solve same Gauss equation, so direct Lagrange cancellation gives `W_p'=0` on `0<t<1`.
Horizon normalizations `U=t^(N+1)(1+O(t))`, `U'=(N+1)t^N(1+O(t))`, `Y=1+o(1)`, and
`tY'=o(1)` give `W_p -> -(N+1)`. Connectedness therefore forces

`W_p(t)=-(N+1)`,
`D(t)=t(1-t)(UY'-U'Y)=-(N+1)t^(N+1)sqrt(1-t)`.

Hence `D(t)` is nonzero at every radial interior point. This removes conjugate-point assumptions
from mixed endpoint Green kernel. Proof requires actual logarithmic endpoint estimates, not only
formal series identities.

### Lean closure of Wronskian nondegeneracy

The endpoint estimate can be made without bounding `log t` term-by-term. In the Wronskian, the
explicit logarithmic contributions cancel algebraically:

`U Y' - U' Y = U H' - U' H + kappa U^2/t`.

Differentiate the exact corpus factorization `U(t)=t^(N+1)F(t)` inside unit disk. This gives

`U'(t)=(N+1)t^N F(t)+t^(N+1)F'(t)`.

Substitution into normalized Wronskian yields log-free horizon normal form

`W_p(t)=sqrt(1-t) *`
`  (t F H' - ((N+1)F+tF')H + kappa t^(N+1)F^2)`.

All four power-series jets are continuous at zero, while coefficient normalizations give
`F(0)=H(0)=1`. Therefore `W_p(t)->-(N+1)` from right. Interior Sturm identity gives `W_p'=0`, so
connectedness forces `W_p=-(N+1)` everywhere on `0<t<1`. Consequently principal endpoint Green
denominator equals

`D(t)=(t(1-t)/p(t))*W_p(t)`

and is nonzero on radial interior. Lean now proves exact Abel limit, global constant, denominator
nonvanishing, and premise-free unit diagonal derivative jump in
`ThetaCuspHawkingBMMixedHorizonLogarithmicCompanionGreenNondegenerate.lean`.

Status: `[PAPER-PROVED] [LEAN-PROVED]`. Remaining open core is not radial conjugate-point control;
it is geometric Einstein--Green reciprocity identifying endpoint source projection with canonical
finite-radiation optical reader.

## Failed conjecture: `++` horizon monodromy as retarded/advanced Green cut

Candidate: use clockwise and counterclockwise Frobenius multipliers of exact complementary `++`
solution as advanced and retarded endpoint Green sheets. This fails projectively. If `U,V` are
regular/complementary solutions and `mu != 0`, then

`D_mu(t)=p(t)(U(t)(mu V'(t))-U'(t)(mu V(t)))=mu D(t)`.

Both endpoint-selected pieces are invariant:

`U(t) mu V(z)/D_mu(t)=U(t)V(z)/D(t)`,
`U(z) mu V(t)/D_mu(t)=U(z)V(t)/D(t)`.

Clockwise and counterclockwise multipliers are complex exponentials and therefore nonzero. Their
nontrivial scalar difference is genuine mode monodromy but induces zero Green-operator difference.
Thus Frobenius sheet scaling cannot be two blocks of Peierls propagator.

Strongest positive survivor: endpoint Green operator depends only on projective complementary
solution line. A nonzero causal cut requires retarded and advanced data to select distinct outer
boundary response lines—an affine shear by independent forbidden/normalizable AdS data—not two
normalizations of same horizon line. This matches existing polarized-boundary concomitant
factorization through `advancedResponse-retardedResponse`.

Status: `[NO-GO] [PAPER-PROVED] [LEAN-PROVED]`. Lean proves projective invariance for both endpoint
pieces and every finite radial packet in
`ThetaCuspHawkingBMSecondHarmonicHorizonMonodromyGreenNoGo.lean`. Next conjecture must construct distinct
augmented outer response lines before `++/--` polarization; mixed additive logarithmic sheet jump
cannot substitute because Peierls skewness kills mixed self-pairing.

## Distinct outer-response Krein conjecture and paper proof

Let `S,V` be exact forbidden and normalizable AdS solutions, with normalized outer Wronskian
`W(S,V)=-1/2`. Let horizon-regular solution have exact connection expansion

`U=A*S+B*V`.

For boundary response parameter `r`, define outer projective line representative

`O_r=S+r*V`

and endpoint Green denominator `D_r=W(U,O_r)`. Bilinearity and alternation give

`D_r=(r*A-B)*W(S,V)=-(r*A-B)/2`.

Thus denominator vanishes at exactly one response line, `r=B/A`, once `A != 0`. Corpus Gamma
identification proves `A` is forbidden/source Gamma coefficient. Its numerator and denominator
Gamma factors are nonzero on every nonresonant Xi fibre, so `A != 0`; `B/A` is exact BM
projective boundary response.

Define right endpoint piece `G_r(t,z)=U(t)O_r(z)/D_r(t)`. For two nonsingular response lines
`r_a,r_b`, common-denominator expansion gives

`G_(r_a)(t,z)-G_(r_b)(t,z)`
`  = ((r_a-r_b)/2) * U(t)*U(z)/(D_(r_a)(t)*D_(r_b)(t))`.

Proof uses no spectral ansatz: expand both denominators by `D_r=-(r*A-B)/2`, then replace
`A*S(z)+B*V(z)` by `U(z)`. Same identity holds for left endpoint piece. Hence every finite radial
source packet has exact source-global rank-one cut

`R_(r_a)(z)-R_(r_b)(z)=Pi_(r_a,r_b)(source)*U(z)`,

where

`Pi_(r_a,r_b)(source)=sum_t source(t)*(r_a-r_b)*U(t)`
`  /(2*D_(r_a)(t)*D_(r_b)(t))`.

This is precise positive replacement exposed by horizon-scaling no-go. It supplies normalized
Krein resolvent identity and finite-source globalization. It does not manufacture physical
retarded/advanced parameters: remaining causal obligation is derive two distinct response lines
from augmented Einstein boundary data, then identify their difference with polarized `++/--`
Peierls response.

Lean closure in `ThetaCuspHawkingBMSecondHarmonicOuterResponseKrein.lean` proves: forbidden/source
coefficient nonvanishing; exact coefficient ratio equals BM projective response; denominator
factorization and its iff nondegeneracy criterion; unit normalized diagonal derivative jump; equal
right/left rank-one Krein differences; finite-source factorization; and actual Xi-fibre
specialization. No denominator premise survives in source-global theorem beyond explicit exclusion
of unique projective pole line.

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Canonical horizon-basis Green Krein conjecture

Fix exact normalizable AdS branch `V`. Sew it separately to regular horizon solution `U` and
complementary horizon solution `C`. Their normalized denominators are

`D_U=W(U,V)=A*W(S,V)=-A/2`,
`D_C=W(C,V)=A_c*W(S,V)=-A_c/2`.

Both are nonzero by regular and complementary Gauss coefficient theorems. Define right endpoint
kernels

`G_U(t,z)=U(t)*V(z)/D_U(t)`,
`G_C(t,z)=C(t)*V(z)/D_C(t)`.

Using connection expansions `U=A*S+B*V`, `C=A_c*S+B_c*V`,

`U(t)D_C(t)-C(t)D_U(t)`
` = W(S,V)*(A_c*U(t)-A*C(t))`
` = -W(S,V)*(A*B_c-B*A_c)*V(t)`
` = -(4n+3+2*i*chi)*V(t)`.

Therefore canonical horizon-basis kernel difference is exact rank one:

`G_U-G_C = -(4n+3+2*i*chi)*V(t)*V(z)/(D_U(t)*D_C(t))`.

Same formula holds for left endpoint pieces. Every finite radial source packet inherits
source-global factorization by `V(z)`. This constructs a premise-free nonresonant causal-propagator
candidate from actual canonical horizon lines and physical normalizable AdS line. It does not label
regular/complementary pair retarded/advanced; that requires time-domain/gauge-fixed Einstein
incidence.

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`. Lean now proves both canonical
denominators nonzero, right/left endpoint rank-one differences, unit derivative jumps, finite
source-response factorization, and actual-Xi specialization. Physical retarded/advanced incidence
remains open.

## Complementary Gauss connection conjecture

Complementary horizon factor has parameters

`a_c=a-c+1`, `b_c=b-c+1`, `c_c=2-c`.

Its Gauss gap is unchanged:

`c_c-a_c-b_c=c-a-b=1/2`.

For `chi.re != 0`, imaginary parts of `a_c,b_c,c_c,c_c-a_c,c_c-b_c` are respectively
`3chi.re/2`, `chi.re/2`, `2chi.re`, `chi.re/2`, `3chi.re/2`; none can be a nonpositive integer.
Global Gauss summation therefore gives complementary forbidden boundary coefficient

`A_c=Gamma(c_c)*Gamma(1/2)/(Gamma(c_c-a_c)*Gamma(c_c-b_c))`.

Dominated Abel convergence at `z -> 1-`, together with `z^(1-c)->1`, identifies this Gamma quotient
with Wronskian/Cramer coefficient
`d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient`. All Gamma factors are nonzero by same
imaginary-part exclusions, hence `A_c != 0`.

Consequences: complementary projective AdS response `B_c/A_c` is finite. Regular and complementary
projective responses are distinct because their difference has numerator exact nonzero connection
determinant. This converts canonical independent horizon basis into two distinct finite outer
response lines. Physical retarded/advanced incidence remains separate, but no projective-chart or
denominator gap remains.

Lean closure in
`ThetaCuspHawkingBMSecondHarmonicComplementaryGaussConnectionCoefficient.lean` proves complete
Gauss parameter audit, complementary Abel boundary value, Gamma/Cramer identification,
nonvanishing, exact projective response separation formula, and regular/complementary inequality.

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

### Literature audit of causal response selection

- Birmingham--Mokhtari, arXiv:hep-th/0609028, derives exact topological-AdS gravitational QNM
  frequencies from hypergeometric master equations, but not nonlinear augmented retarded-minus-
  advanced source response or Peierls pairing.
- Son--Starinets, arXiv:hep-th/0205051, gives Lorentzian AdS/CFT retarded prescription and relates
  QNM frequencies to retarded poles; it supplies general ingoing/source-response rule, not exact
  BM second-harmonic Einstein source coefficient.
- van Rees, arXiv:0902.4010, derives ingoing horizon condition from real-time gauge/gravity duality,
  including higher-point context, but does not compute this augmented BM quadratic response.
- Khavkine, arXiv:1402.1282, proves Peierls/covariant-phase-space equivalence under gauge,
  hyperbolicity, and global hypotheses; it does not establish those hypotheses or endpoint values
  for this asymptotically AdS BM fibre.

Conclusion: literature validates architecture—ingoing retarded selection, advanced/retarded
reciprocity, conserved radial flux—but does not close project-specific full Einstein source-to-
response coefficient. Novelty remains unverified because absence was not established by exhaustive
bibliographic review.

## Exact horizon-to-AdS determinant reciprocity

Apply radial-to-boundary theorem to regular horizon connection vector `(A,B)` and Schwarz conjugate
of complementary horizon connection vector `(A_c,B_c)`. Choose `--` coefficients
`(conj(A_c),conj(B_c))`. Polarized current becomes

`J=(B_c*A-A_c*B)/2`.

Exact corpus connection determinant is

`A*B_c-B*A_c=-2*(4n+3+2*i*chi)`.

Therefore every radial interior point obeys exact two-endpoint reciprocity

`J=-(4n+3+2*i*chi)`.

On every Xi fibre this is nonzero because angular momentum has nonzero real part. This supplies a
canonical phase-normalized nonzero polarized carrier between independent regular/complementary
horizon lines without dividing by possibly zero complementary forbidden coefficient. It does not
identify those two horizon lines with augmented retarded/advanced Einstein blocks; exact horizon
basis file explicitly leaves that incidence separate.

Lean closure is included in
`ThetaCuspHawkingBMSecondHarmonicOuterPolarizedReciprocity.lean`: exact current equals negative
complementary Frobenius exponent, and every Xi specialization is premise-free nonzero on radial
interior.

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Exact radial-to-boundary polarized reciprocity conjecture

Use exact `++` AdS basis `S,V`. Its Schwarz conjugates form `--` basis at conjugate momentum. For
arbitrary outer coefficient vectors define

`y=s_pp*S+r_pp*V`,
`v=s_mm*conj(S)+r_mm*conj(V)`.

Linearity of exact BM jets proves `y` solves `++` equation and `v` solves `--` equation. Their
polarized radial current is

`J=p*(conj(v)*y'-conj(v')*y)`.

Expanding four determinant terms cancels same-basis contributions and leaves

`J=W(S,V)*(conj(s_mm)*r_pp-conj(r_mm)*s_pp)`.

Exact global outer normalization `W(S,V)=-1/2` therefore gives, at every `0<z<1`,

`J=(conj(r_mm)*s_pp-conj(s_mm)*r_pp)/2`
` = d4BMAdSBoundaryPolarizedConcomitant(s_pp,r_pp,s_mm,r_mm)`.

No endpoint limit or assumed boundary flux is needed. If

`r_pp=retardedResponse*s_pp`,
`r_mm=conj(advancedResponse)*s_mm`,

then exact radial current is

`conj(s_mm)*s_pp*(advancedResponse-retardedResponse)/2`.

This is sought phase-normalized radial/AdS reciprocity for homogeneous outer data. It still does
not derive augmented retarded and advanced responses from full Einstein source; source-global
Krein identity above supplies propagation once those two physical lines are constructed.

Lean closure in `ThetaCuspHawkingBMSecondHarmonicOuterPolarizedReciprocity.lean` proves actual first
and second derivatives for both outer combinations, exact `++` and Schwarz `--` solution-jet
equations, radius-independent equality of polarized radial current with boundary concomitant, and
its exact advanced-minus-retarded response factorization.

Status: `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Exact physical horizon-incidence conjecture

Birmingham--Mokhtari, arXiv:hep-th/0609028, Eq. (23)--(31), use

`z=1-l^2/r^2`, `alpha=-i*omega/2`, `c=1-i*omega`,

and the physical master field

`Phi_in(t,z)=exp(-i*omega*t)*z^alpha*(1-z)^beta*F(a,b;c;z)`.

For four-dimensional scalar and vector gravitational modes, `beta=0`. The reduced equation has
regular and complementary horizon factors

`R(z)=F(a,b;c;z)`,
`C(z)=z^(1-c)*F(a-c+1,b-c+1;2-c;z)`.

Set asymptotic horizon null coordinates

`v_z=t+log(z)/2`, `u_z=t-log(z)/2`.

Since `c=1+2*alpha`, the complementary physical exponent is

`alpha+1-c=-alpha`.

Therefore, on the positive radial interval,

`exp(-i*omega*t)*z^alpha*R(z)=exp(-i*omega*v_z)*F(a,b;c;z)`,

`exp(-i*omega*t)*z^alpha*C(z)=`
`exp(-i*omega*u_z)*F(a-c+1,b-c+1;2-c;z)`.

Both analytic factors have unit horizon value. Thus regular canonical horizon line is exactly
future-horizon ingoing and complementary canonical horizon line is exactly past-horizon outgoing
for the BM Fourier convention `exp(-i*omega*t)`. Consequently the two premise-free
horizon/normalizable kernels constructed above are the exact ingoing and outgoing frequency-domain
Green blocks.

Hostile qualification: for complex frequency, outgoing incidence at the same `omega` does not by
itself prove that this block is the Schwarz-conjugate advanced distribution. That needs conjugate
frequency transport and time-domain support. No `retarded`/`advanced` relabel is permitted before
that further theorem.

Lean closure in `ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonIncidence.lean` proves the generic
`c=1+2*alpha` relation, ingoing/outgoing phase factorizations, canonical unit horizon amplitudes,
regular/complementary physical master-field incidence, exact ingoing/outgoing Green-block Krein
difference, finite source-global response, and actual-Xi specialization.

Status: `[LITERATURE-DERIVED] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Canonical physical Green equality no-go

The exact normalizable AdS branch obeys

`V(z)/sqrt(1-z) -> 1` as `z -> 1-`.

Hence this ratio is eventually nonzero. Choose an interior point `t` in that neighborhood; then
`V(t) != 0`. For `chi.re != 0`, the complementary horizon exponent

`lambda=4n+3+2*i*chi`

and both canonical Green denominators `D_in(t),D_out(t)` are nonzero. The physical horizon-basis
Krein identity on the diagonal gives

`G_in(t,t)-G_out(t,t)=-lambda*V(t)^2/(D_in(t)*D_out(t)) != 0`.

Every actual Xi fibre satisfies `chi.re != 0`. Therefore canonical physical ingoing and outgoing
frequency-domain Green blocks are never equal as functions on any Xi fibre, including fibres on
the critical line. A proposed endpoint

`G_in=G_out iff critical line`

is false and must be retired.

Positive survivor: every Xi fibre has an explicit interior one-point radial source whose physical
ingoing-minus-outgoing response is nonzero and lies exactly on the rank-one normalizable AdS line.
This is a canonical noncollapse/spectral-density witness. It can feed a polarized optical law, but
RH selection must come from a further arithmetic or nonlinear incidence condition, not equality
of canonical radial propagators.

Lean closure in
`ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonGreenNoncollapseNoGo.lean` proves eventual and
existential normalizable-branch nonvanishing, a nonzero interior diagonal kernel difference,
functional inequality of canonical ingoing/outgoing kernels on every Xi fibre, and an explicit
unit point-source noncollapse witness.

Status: `[NO-GO] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Factorized angular-radial point-source selector

For every Xi fibre, canonical Green noncollapse provides an interior point `t` with

`DeltaG(q,t)=G_in(q;t,t)-G_out(q;t,t) != 0`.

Let `kappa(q)` be the exact Teukolsky orthogonal-helicity mixing coefficient. Its norm square is
the orthogonal mixing energy of a unit source, and the corpus optical transgression proves

`kappa(q)=0 iff re(q)=1/2`.

Define the factorized point-source observable

`O(q,t)=kappa(q)*DeltaG(q,t)`.

At the selected interior point, `DeltaG(q,t)` is nonzero, so

`O(q,t)=0 iff kappa(q)=0 iff re(q)=1/2`.

This is an exact source-global angular/radial incidence: arithmetic critical-line information is
carried only by the angular helicity factor, while the physical radial causal cut is a certified
nonzero carrier. It removes all radial denominator and source-support premises.

Hostile qualification: the zero-locus theorem is a receiver, not RH. Unconditional RH still needs
one upstream Einstein/Peierls/Ward law forcing this actual factorized observable to vanish for every
Xi fibre. Canonical Green sewing alone forces the opposite radial statement and cannot provide that
law.

Lean closure: `ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonPolarizedSelector.lean`
formalizes the exact mixing zero locus, factorized observable, canonical noncollapse-point selector,
and the global equivalence between universal selector vanishing and RH. Targeted build and axiom
audit pass; only standard theorem-prover axioms remain.

Status: `[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

## Corrected Peierls-polarized BM landing

The one-channel conjecture that the mixed `+-` response carries the complete cubic causal cut
fails. Cyclicity turns that contribution into a Peierls self-pairing, hence zero; setting the
`++` jump to zero then kills the whole cut. The surviving corpus identity is instead

`Cut(++-) = 2 Omega(Q++, Q--)`,

where `Q++` and `Q--` are independently polarized same-grade quadratic sources.

The exact BM Schwarz radial infrastructure supplies a canonical nonzero carrier. For an interior
radius `z`, regular `++` and Schwarz-complementary `--` outer solutions have polarized current

`J_BM(n,q,z) = -alpha_comp(n,chi(q)) != 0`.

For nonzero seed amplitude `A`, define the source-faithful candidate

`P(n,A,q,z) = 2 |kappa(q)|^2 |carrier(A,q)|^2 J_BM(n,q,z)`.

This factorization is not merely assembled from unrelated scalars. If both independent Schwarz
fibres are scaled by the literal separated source amplitude

`a(A,q)=kappa(q)*carrier(A,q)`,

sesquilinearity of the exact BM concomitant gives

`P(n,A,q,z)=2 J_BM[a(A,q)Y++,a(A,q)Y--](z)`.

Thus the candidate is twice an actual conserved source-scaled polarized radial current.
Exact outer reciprocity further identifies that current with the AdS boundary symplectic
concomitant of the correspondingly scaled forbidden/normalizable connection data. The landing
premise is therefore reduced to equality between augmented Peierls source pairing and this literal
boundary concomitant; angular, nonlinear-carrier, radial, and endpoint factorization are closed.

The Einstein carrier and BM current are nonzero on every Xi fibre, while
`kappa(q)=0 iff re(q)=1/2`. Therefore

`P(n,A,q,z)=0 iff re(q)=1/2`.

A hostile functional-equation cancellation conjecture also fails sharply. Reflection sends the
continued BM angular momentum by

`chi(reflect(q)) = -chi(q) + i/2`,

so the two complementary exponents add to `8n+5`. Consequently the unscaled canonical polarized
currents obey the exact rigidity law

`J_BM(n,q,z) + J_BM(n,reflect(q),z) = -(8n+5) != 0`.

Thus reflection pairing cannot erase the radial carrier. Any global cancellation would have to
come from actual source amplitudes or Peierls dynamics, not functional-equation antisymmetry of
the canonical BM current.

If augmented retarded and advanced graded blocks are restrictions of one skew Peierls propagator,
Einstein Hessian pairing is cyclic, and its polarized `Q++/Q--` source pairing equals the displayed
BM angular-radial factor, the complete nonlinear cokernel cut equals `P`. Under that precise weld,
retarded and advanced total sections agree exactly on the critical line.

Hostile qualification: this is corrected conditional landing, not RH. Missing hard theorem is now
one explicit field-theoretic incidence: actual augmented Einstein--Teukolsky action pairing on the
two quadratic source profiles must equal the now-literal BM AdS boundary concomitant. Frequency-domain
ingoing/outgoing kernel equality is neither required nor true, and radial current conservation
alone does not establish global time-oriented Peierls support.

Lean closure: `ThetaCuspHawkingBMSecondHarmonicPeierlsPolarizedLanding.lean` formalizes the exact
BM Schwarz current, its affine reflection law and noncancelling pair sum, literal source-scaled
current realization, critical-line zero locus, Peierls landing under one displayed source-pairing
incidence, and corrected retarded/advanced section equivalence.

Status: `[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.
