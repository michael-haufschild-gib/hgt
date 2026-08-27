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
definition and downstream theorem is being corrected before Green-cut construction continues.

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

now with the literal operator parameters. Next proof obligation: formalize `u`, its two
derivatives, original mixed jet equation, horizon leading normalization, then build the full
logarithmic companion and endpoint-selected Green responses.

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
