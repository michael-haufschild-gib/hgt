# The Canonical System of the Window Tower (CSW)

Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`; umbrella
`CanonicalSystemOfTheWindowTower.lean`. Every theorem is unconditional; equivalences with RH are
labelled. Companion of GWZ (`GrowingWindowsOfSpecZ`, kick law, lattice Schur parameters): CSW
computes the frozen two-collar data in closed form and states window growth as a continuum Schur
step.

## 1. Question

Review-0311 §2.5.1: for every prime-power stage `n = N+1` and collar width `ε`, compute the frozen
two-collar form `S^N_ε`, its evolution in `ε` and across stages, and its collar coupling in closed
form at the first two prime stages.

## 2. Answer

| Part | Statement | Lean |
|---|---|---|
| Coupling kernel | Ordered tests `f < g` couple through `κ(x) = 2cosh(x/2) − ω(x) = e^{x/2} − e^{−x/2}/(e^{2x}−1)` and the folds: `Q(f+g) = Q(f) + Q(g) + 2(∫_0^∞ κ c_{fg} − Σ_n Λ(n)n^{−1/2} c_{fg}(log n))` | `weilQuad_add_of_ordered`, `two_mul_cosh_sub_archLevyDensity` |
| Trivial divisor | `κ(x) = e^{(1−½)x} − Σ_{k≥1} e^{(−2k−½)x}`: pole `s = 1` with `+`, trivial zeros `s = −2k` with `−`; the Gamma pole `s = 0` cancels against the pole term | `hasSum_collarKernel` |
| Transmission | Across a cut the archimedean place and the pole transmit only the trivial-divisor moments: `∫_0^∞ κ c_{fg} = μ_1(f)ν_1(g) − Σ_{k≥1} μ_{−2k}(f)ν_{−2k}(g)` | `OrderedAt.integral_collarKernel_mul_eq_moments`, `weilQuad_add_of_ordered_of_primeFree` |
| Gluing | `Q(f+g+h) = Q(f+g) + Q(g+h) − Q(g) + 2Ξ(f,h)` for ordered pieces: a window is two windows of the previous length glued along the interior | `weilQuad_chain_three` |
| Two-collar identity | On a stage test `x_L + y + x_R`: `Q = F − 2w⟨x_L, J x_R⟩`, `F = Q(x_L+y) + Q(y+x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩`; `F` is the stage datum `Q_N` | `weilQuad_stageTest`, `stageForm_stageTest`, `stage_nonneg_iff` |
| Closed form | `F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L),ν(y)⟩ + ⟨μ(y),ν(x_R)⟩ + ⟨μ(x_L),ν(x_R)⟩) − 2Σ_{m<n} w_m(⟨x_L,τ_m y⟩ + ⟨y,τ_m x_R⟩)`: the interior receives the trivial-divisor moments and the earlier-fold transports of the collars | `frozenTwoCollar_eq_transmitted` |
| Stage 1 | No earlier fold: the frozen form sees the collars through `Q(x_L)`, `Q(x_R)` and their moment sequences only | `firstStage_frozenTwoCollar_eq`, `firstStage_frozen_congr` |
| Stage 2 | The only earlier fold is `T₂`: moments plus `−2w₂(⟨x_L,τ₂y⟩ + ⟨y,τ₂x_R⟩)` | `secondStage_frozenTwoCollar_eq` |
| Growth law | `Q ≥ 0` on `W_{ℓ+ε}` ⟺ `Q ≥ 0` on `W_ℓ` and `W(τ_εu, v)² ≤ Q(u)Q(v)` for all `u, v` on `W_ℓ`: window growth is a translation contraction | `window_nonneg_iff_contraction` |
| Stage disk | At `ℓ = log(N+1)`: `W(τ_εu, v) = W_N(τ_εu, v) − w∫u(y)v(y+ℓ−ε)`; the fold lies in the disk of centre the frozen pairing and radius `√(Q(u)Q(v))` | `weilPair_stage_eq`, `stage_nonneg_iff_disk` |
| RH | RH ⟺ every growth step is a translation contraction | `riemannHypothesis_iff_translation_contraction` |

Evolution: in `ε` the disk centre moves by translation of one previous-window test against the
other (linear); across a stage the coupling receives the impulse `−w⟨x_L, J x_R⟩`, entering through
the lag `ℓ − ε`; composite stages carry none. The Riccati form of the law is the elimination of the
interior in the chain law.

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Ordered pair | `OrderedAt a f g` | `f = 0` right of `a`, `g = 0` left of `a` |
| Cross-correlation | `crossCorr f g x` | `∫ f(u) g(u + x)` |
| Collar kernel | `collarKernel x` | `e^{x/2} − e^{−x/2}/(e^{2x} − 1)` |
| Ordered coupling | `orderedCoupling f g` | `∫_0^∞ κ c_{fg} − Σ_n Λ(n)n^{−1/2} c_{fg}(log n)` |
| Moments | `leftMoment f σ`, `rightMoment g σ`, `trivialExponent k` | `∫ f e^{−σu}`, `∫ g e^{σv}`, `σ_k = −(2(k+1) + ½)` |
| Moment pairing | `momentPairing f g` | `μ_{1/2}ν_{1/2} − Σ_k μ_{σ_k}ν_{σ_k}` |
| Frozen two-collar form | `frozenTwoCollar xL y xR` | `Q(x_L+y) + Q(y+x_R) − Q(y) + 2⟨μ(x_L), ν(x_R)⟩` |
| Frozen pairing | `frozenPair N f g` | polarization of the stage datum `Q_N` |

## 4. Remark

`S^N_ε = inf_y F(x_L, y, x_R)`; at stage 1 it is `Q(x_L) + Q(x_R) + 2⟨μ(x_L), ν(x_R)⟩ + Φ_ε(μ(x_L), ν(x_R))`,
`Φ_ε(α, β) = inf_y [Q(y) + 2⟨α, ν(y)⟩ + 2⟨μ(y), β⟩]`, one function of the two moment sequences
(`firstStage_frozen_congr`). The disk law states the stage without this infimum.

## 5. The unshifted local Weil spaces

For `0<a<a*(ζ)`, the exact Weil norm is complete and its literal Fourier transform is entire,
injective, and bounded at each evaluation point. Aperture inclusions are isometries. Compact
division extends to unitary zero-moving; source conjugation extends to an antiunitary involution.

Write `v_z` for the evaluation vector, `K_a(w,z)=F(v_w)(z)`, and
`E_a(z)=(z+i)K_a(i,z)`. Then

`|E_a(z)|²-|E_a♯(z)|²=4 Im(z) ‖v_i‖² ‖v_z‖²`.

`E_a` is Hermite–Biehler, has no real zeros, and reconstructs `K_a` through its full
Christoffel–Darboux identity. These are properties of the literal unshifted form.

At finite contact a nonzero null ground vector has a nonzero Fourier value. A bound on the earlier
diagonal kernels would extend by smooth-core density and contradict that value. Thus some fixed
`K_a(z,z)` tends monotonically to infinity at contact. Window positivity still holds at contact.
The aperture differential equation and prime-entry regularity are not established here.

## 6. Bounded completed Riesz sources

Every Fourier-evaluation Riesz vector before contact has two bounded real inverse-Doob
coordinates and a bounded measurable physical representative, zero outside the exact aperture.
Positive-level truncation retains all prime-power jumps. The cutoff archimedean kernel has
uniformly divergent row mass and bounded off-diagonal action; its exact mixed-energy identity
forces high positive and negative truncations to vanish. Fourier forcing and both polar terms
are derived from the actual completed Riesz equation.

The endpoints are `evalVector_bounded_real_graph_coordinates`,
`evalVector_physical_essentially_bounded`, and
`evalVector_has_bounded_physical_representative`.
`evalVector_operator_domain_and_apply` places each physical source in the literal
restricted Weil operator domain. Its image is
`1_{[-a,a]}(x) exp(-i conj(z)x)`, bounded by `exp(a|Im z|)`.
Boundary traces and aperture variation remain separate obligations.

## 7. The logarithmic reference

The literal Gamma multiplier is `(1/2)log(1+ξ²)+c₀` minus the Fourier
transform of `r(|t|)`, where `r(t)=ω(t)-exp(-t)/(2t)` is nonnegative,
bounded by `3/4`, and integrable. Its convolution is bounded, self-adjoint,
and preserves essential boundedness.

`logarithmicDirichletForm_eq` identifies the literal positive logarithmic form
on the complete archimedean domain. Every actual evaluation Riesz source lies
in its restricted operator domain, with essentially bounded forcing
`evaluationForcing+(logarithmicDirichletAdjustment-ccmRestrictedWeilBoundedRemainder)u`.
The full finite prime sum and both polar terms remain present.

For `Ψ(t)=1+(1/2)log(1+t²)`, the positive Poisson factor
`κ(s)=exp((1/π)∫₀∞s log(Ψ(t))/(s²+t²)dt)` satisfies
`κ(s)/√log(s)→1`. It is increasing for `s>0`, at least one, and tends to
one as `s↓0`. Its literal slit-plane extension is holomorphic, nonzero,
and respects conjugation; `complexLogReferenceFactor_ofReal` identifies
its positive real values exactly. The actual Poisson integral gives the
pointwise boundary modulus `|κ(iy)|²=Ψ(y)` for `y≠0`, and analytic uniqueness
gives `κ(z)κ(-z)=1+(1/2)Log(1-z²)` for every nonreal `z`.
Its reciprocal tends uniformly to zero at infinity over all nonreal directions.
Reflection continues the factor across zero and `(-1,0)`, with unit value at zero.
Its unique zero is `-b`, where `b=√(1-exp(-2))`; the zero is simple and the
reciprocal has positive residue `κ(b)(1-b²)/b`.
Removing this pole gives a bounded analytic remainder with continuous upper
boundary values. Its jump on `-t`, `t>1`, is `-2πiρ(t)`, where
`ρ(t)=2κ(t)/((2+log(t²-1))²+π²)` is positive and bounded.
The exact positive representation is
`κ(s)⁻¹=R/(s+b)+∫₁∞ρ(t)/(s+t)dt`, including integrability.
The causal mixture `v(x)=R exp(-bx)+∫₁∞ρ(t)exp(-tx)dt`, zero for `x≤0`,
is positive, continuous and decreasing on the positive half-line. Its Laplace
transform is exactly `κ(s)⁻¹`, and its full integral is one. Its cumulative
mass has the exact normalization `V(x)√log(1/x)→1` as `x↓0`.
Its literal Fourier transform is `v̂(ξ)=κ(2πiξ)⁻¹` at every frequency;
the continued boundary modulus is `|κ(iy)|²=Ψ(y)`, including zero.
Multiplication by the actual factor `κ(2πiξ)` preserves positive-half-line
support whenever its result is in L². Bounded holomorphic regularizers
`κ(z)/(1+εz)` and strong L² convergence prove this on the full graph domain.
The range of causal convolution `W` is exactly the finite logarithmic energy
domain. Its form pulls back to the ordinary L² inner product. Thus `WW*`
is the unique finite-energy solution operator for every half-line L² forcing.
Its literal kernel is `G₊(x,y)=∫₀^{min(x,y)}v(x-s)v(y-s)ds`, integrable off
the potentially singular diagonal. Schur composition proves its actual L²
operator representation. Application to Weil Riesz boundary traces remains open.
For measurable input continuous from the right at zero, the causal convolution
has exact normalized limit `u(x)√log(1/x)→h(0)`. Positivity of the density
and its exact renewal mass prove this without an assumed trace theorem.
Backward convolution is continuous at zero for L² forcing essentially bounded
near the endpoint. Its readout integral is absolutely convergent. L¹ translation
continuity treats bounded forcing; square-integrability of `v` away from zero
and dominated convergence treat the remote part.
The actual Green solution has the measurable representative
`u(x)=∫₀ˣv(t)(W*f)(x-t)dt`. For L² forcing essentially bounded near zero,
`u(x)√log(1/x)→∫₀∞v(y)f(y)dy`; the coefficient is absolutely convergent.
For every whole-line L² source, the extended literal jump energy
`∫₀∞exp(-t)/(2t) ‖τ_tu-u‖²dt` equals
`∫(Ψ(2πξ)-1)|û(ξ)|²dξ`. Its finiteness, or absolute integrability of
the translation losses, is exactly the logarithmic multiplier graph condition.
Every bounded real Lipschitz cutoff preserves this complete energy domain.
Its translation loss is at most `‖χ‖∞‖τ_tu-u‖+Lip(χ)|t|‖u‖`.
The explicit endpoint cutoff is one up to `a` and zero from `3a/2`,
with Lipschitz constant `2/a`, so the two endpoint cutoffs overlap.
