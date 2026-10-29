# Lower-order Gamma coupling of complete-cell averages and details

- **ID:** acs-gamma-mixed-block-lower-order
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Statement:** For actual complete pairs `F=g+h`, the Gamma polarization obeys `|Γ(F)-Γ(g)-Γ(h)|² ≤ C Γ(g) ∫h²`, uniformly in horizon and coefficients.

## Goal

Factor the mixed Gamma block through ordinary detail square mass, then prove
uniform finite-head approximation in the original complete-source Gamma norm.
This supplies uniform finite-head control of the actual Gamma coupling.
It does not assert a sign for the first-prime or polar source, or compactness
of low-generator translation orbits.

## Approach

Use one-sided mean-zero cancellation. For `x∈I_a`, subtract the far-end
charge `gammaFarCharge(L_a,U_a,y)` from the kernel for `y∉I_a`.
The charge is independent of `x`, while `g(x)=q_a` and `∫I_a h=0`.
It therefore contributes zero to the mixed pairing.

The surviving positive kernel is exactly the existing interval row defect.
Its entire exterior mass is bounded by `exp(1/2) w_a`. This avoids any
comparison between different pair widths or construction of a symmetric
replacement kernel.

## Dependency-closed paper proof [PROVED HERE]

Let `I_a=(L_a,U_a)`, `L_a=log(2a)`, `U_a=log(2a+2)`, for `1≤a≤X`.
Put `K(x,y)=ω(|y-x|)`, `E=exp(1/2)`. The actual source is `F=g+h`,
where `g=q_a` and `h=d_a H_a` on `I_a`, with both sources zero almost
everywhere outside the pair union.

On `I_a×I_aᶜ` let `R_a(x,y)=K(x,y)-gammaFarCharge(L_a,U_a,y)`.
The existing pointwise far-charge inequality gives `0≤R_a≤K`, and
`gamma_interval_row_defect_le` gives `∫∫R_a≤E w_a` (endpoints are null).
All these measures are finite. The full kernel on `I_a×I_aᶜ` is finite
as well, by `gamma_interval_exterior_kernel_le`.

Symmetry of `K` gives

`B(q,d,X)=Γ(F)-Γ(g)-Γ(h)=2 Σ_a ∫I_a∫I_aᶜ K(x,y) Δg(x,y) h(x)`.

Inside `I_a×I_a`, `Δg=0`. In each remaining integral, the far-charge
term factors as `∫I_a h` times an exterior integral, and hence vanishes.
Thus the same equality holds with `R_a` replacing `K`. Fubini is valid
because sources are bounded and each crossing-kernel measure is finite.
The full polarization is integrable by the compact-BV Gamma bounds.

Set `A=Σ_a∫∫R_a(Δg)²`, `D=Σ_a∫∫R_a h(x)²`.
Pairwise disjointness of the `I_a`, together with `R_a≤K`, gives
`A≤∫∫K(Δg)²=2Γ(g)`. On `I_a`, `|h|≤|d_a|`; consequently
`D≤E Σ_a w_a d_a²`. The existing width and balanced-mass bounds give
`w_a≤1/a≤16/(4a+3)≤16M_a` for every `a≥1`. Therefore
`D≤16 E Σ_a M_a d_a²=16 E ∫h²`.

Cauchy–Schwarz on the finite sum of these positive measures gives

`|B(q,d,X)|²≤4 A D≤128 exp(1/2) Γ(g)∫h²`.

This is an unconditional estimate on the actual source family.

## Uniform finite-head approximation [PROVED HERE]

Let `C₁>0` be the already-formalized homogeneous coarse recovery constant:
`Γ(g)≤C₁Γ(F)`. For `d_tail(a)=1_(A≤a)d_a`, the existing exact weighted
variance bound gives `κ_A ∫h_tail²≤Γ(F)`, where `κ_A=log(1/w_A)→∞`.
Apply the new mixed estimate with `q,d_tail`, keeping the original `F`
only in the two controlling inequalities. Then

`κ_A |B(q,d_tail,X)|² ≤128 exp(1/2) C₁ Γ(F)²`.

Given `ε>0`, choose one `A≥1` with `κ_A ε²≥128 exp(1/2) C₁`. Taking nonnegative
square roots gives `|B(q,d_tail,X)|≤εΓ(F)` for every `q,d,X`.
The original mixed Gamma integral is linear in `d`, so

`|B(q,d,X)-B(q,d_head,X)|≤εΓ(F)`,

where `d_head(a)=1_(a<A)d_a`. Only finitely many actual Haar coefficients
enter this head, independent of horizon. No coefficient bound, spectral
assumption, or coarse square-mass correction is used.

## Lean formalization [VERIFIED]

- `ArithmeticCastelnuovoSeveri/GammaMixedPairing.lean`: symmetric Gamma
  measure, actual polarization, finite crossing measures, exact far-charge
  cancellation (`integral_gammaCross_mixed_eq_remainder`).
- `ArithmeticCastelnuovoSeveri/GammaFiniteMeanZeroCoupling.lean`: disjoint
  interval assembly and the lower-order bound
  (`gamma_mixed_sq_le_interval_mass`).
- `ArithmeticCastelnuovoSeveri/GammaCouplingUsesOnlyDetailMass.lean`: actual
  complete-cell application (`completeGammaMixed_sq_le`) and linearity
  (`completeGammaMixed_sub`), for every `q,d,X`, with no analytic assumptions.
- `ArithmeticIndexDescent/GammaCouplingHasUniformFiniteHeads.lean`: uniform
  finite-head approximation in the original Gamma norm
  (`completeGammaMixed_tail_sq_le`, `exists_uniform_finite_head_for_gamma_mixed`).

All three support modules passed kernel checks while building the oleans
needed by their importing modules. The final application passed
`lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/GammaCouplingHasUniformFiniteHeads.lean`
with no diagnostics. Both umbrellas contain the corresponding imports;
umbrellas were not compiled.

No axiom checks, web searches, novelty checks, or numerical experiments run.

## Status

Paper proof and exact Lean formalization complete. The
[homogeneous projection bound](acs-homogeneous-gamma-coarse-recovery.md)
is an established dependency. First-prime terms, coarse odd higher powers,
finite detail heads and joint actual polar/archimedean payment remain open.
No full Weil sign or index bound follows from this theorem alone.
