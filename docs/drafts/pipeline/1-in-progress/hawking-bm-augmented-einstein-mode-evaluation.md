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

Thus `R₊₊` has regular same-fibre inverse-Jost factors given by the corresponding Gamma values. The transient `R₊₋` channel is an exact odd Hawking--Matsubara Frobenius resonance. If `c=-N+epsilon` is approached at fixed angular fibre, then `dA/dc=dB/dc=1/2` and the non-normalizable BM connection coefficient has Laurent expansion

`Gamma(c) Gamma(1/2)/(Gamma(A) Gamma(B))`

`= P₋₁/epsilon + P₋₁*(H_N-gamma_E-(digamma(A₀)+digamma(B₀))/2)+O(epsilon)`,

where `P₋₁=(-1)^N Gamma(1/2)/(N! Gamma(A₀) Gamma(B₀))`. Here `N` is even, so the residue sign is positive. Retarded analytic continuation therefore determines a logarithmic finite-part transfer, not the reciprocal Jost scalar used in the earlier fibre radiation abstraction.

At the cubic frequency, `A(Omega₊₊₋)` is a negative half-integer. Hence the same-fibre plus Jost factor is nonzero, and for `Re chi != 0` so is the full radial Jost determinant. The local `++-` monomial misses every same-fibre BM QNM.

Actual `B` and `C` values require Kodama--Ishibashi metric reconstruction, gauge and boundary jets, horizon harmonic product coefficients, and radial source integrals. Use the one-sided transform `fhat(omega)=int_0^infinity exp(I*omega*t)f(t)dt`. For a causal BM monomial, `H(t)exp(-I*Omega*t)` transforms to `I/(omega-Omega)`. If `Y_lambda` is a complete horizon harmonic system, source-faithful causal responses have the form

`uhat₊₊(omega,r) = -I sum_lambda Y_lambda/(omega-Omega₊₊) int G^ret_lambda(r,r';omega) S_{lambda,++}(r') dr'`,

`uhat₊₋(omega,r) = Mhat₀(omega,r)-I sum_lambda Y_lambda/(omega-Omega₊₋) int G^ret_lambda(r,r';omega) S_{lambda,+-}(r') dr'`.

`M₀` lies in the exceptional zero-frequency constraint kernel; the transient term uses the logarithmic Matsubara Green kernel above. The direct third jet is

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
- **Strongest positive survivor:** Exact channel-frequency/Jost classification, logarithmic mixed-channel transfer, and proof that full residue requires a causal convolution numerator rather than an on-shell scalar Green factor.
- **New insight:** Mixed transient response is a Hawking--Matsubara logarithmic channel. Local cubic source misses the QNM lattice, so it cannot create a higher coincident pole; nevertheless causal turn-on lets it contribute to the same simple-pole residue. Cancellation remains a full augmented causal-source problem.
- **Status:** Frequency and Jost theorem is Lean-proved in `ThetaCuspHawkingBMCausalChannelEvaluation.lean`. Full tensor coefficients remain open because required horizon multiplication and augmented Einstein source data have not been supplied.

## Log
- 2026-08-25 — Entered Stage 1 after corpus and source audit.
