# Arithmetic Polarization (APol)

**One question.** Over `𝔽_q` the sign of the explicit formula comes from a *polarization*: the
theta divisor of the Jacobian makes the Rosati trace `τ(ξ ξ′)` an intersection number of effective
classes, a trace form that is at once **positive** and **equivariant** under the Frobenius. Over
`ℤ` the corpus has every other layer of Weil's argument — the identities, the theorem of the
square, the budget — and every positivity it can build from invariance is isotropic at off-line
zeros. What could play the polarization over `ℤ`, by which mechanism can a positivity be a theorem
about a structure rather than a consequence of a symmetry, and what does each mechanism give?

APol is the theory of **positive structures on reflection pairs** `{ρ, ρ* = 1 − ρ̄}` and of the
operations that localize, collide, complete and count them. Its organizing principle:

> *Positivity excludes a pair only through an indefinite fibre.* A symmetry hyperbolic at the pair
> makes every invariant positive fibre isotropic; a symmetry elliptic at the pair makes the fibre
> definite, positive on one sector and negative on the other; a collision turns the pair into a
> determinant, which is positive and sees no sign.

Namespace `GaloisForLFunctions.ArithmeticPolarization`; umbrella `ArithmeticPolarization.lean`.
Everything is unconditional; RH and its partial forms appear only inside equivalences.

---

## 1. Place in the research

The B-tier obstacles of the frontier (B1.3, B1.6, B1.9, B1.10, B3.5, B3.25–B3.28) are one missing
object: a **polarization of the correspondence surface of `Spec ℤ`**, a positive structure whose
positivity is a theorem about the structure (counting, or a non-hyperbolic localizing symmetry),
which sees the sign of prime-power atoms, and whose exterior part collides conjugate zeros without
an ordinate-dependent conductor. APol extends three programmes by that object and answers, in
sharp form, which of its candidate sources exist over `ℤ` and what each one costs.

| Programme | What APol takes | What APol adds |
|---|---|---|
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | correspondence surfaces, the local form `2 Re(u v̄)`, boosts and separating isometries, determinant and Rosati degrees, the real-anchor law, height-coupled systems, escape-state classification | the elliptic and collided local types, their localizers and price; the two forms `W` and `D`; the leading-line law; parity of collisions |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, charged statistics, loss laws, gauge mass of escape states | charged weights `Λ(n) cos(γ log n)` as the arithmetic side of elliptic localization; the first gauge charge as an archimedean twist |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | positive Poisson pairs, the `κ = 1` collapse, the exhaustion map | rigidity of coupled classes as a forcing statement; the capacity of intrinsic charge |

| Further programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | scaling surface, curve data, golden datum, effectivity with RR + ample, the universal floor law, Fejér barrier of harmonic coupling, window certificates |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Rosati positivity = orbit Hodge index, damping automorphisms, theta `h⁰` of `Spec ℤ` |
| [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md), [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | completed positive systems, `ζ ∈ CompletedPositiveSystem 1 1`, positive-definite functions |
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | single-height detection with modulated tests, the sharp conductor horizon, Kronecker syndeticity |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | height shifts, window certificates for every prime weight, the Liouville twist |
| [ArithmeticKunnethTheory](../ArithmeticKunnethTheory/README.md) | product receivers and depth homogeneity |
| `Zeta23`, RHTower | zero configurations `ZeroConfig`, Weil's form `Z.W`, the explicit formula for `ζ`, `ξ` and its symmetries, digamma and transform bounds |

---

## 2. Why

**The exhaustion map has one shape.** Every positivity the corpus has proved for a carrier that
sees off-line pairs is a consequence of invariance and is isotropic there: Hecke operators, the
archimedean flow and gauge twists act on off-line fibres by boosts (ACP P4), separating isometries
are boosts (ACP P13), the successor is unipotent (ACP P5), non-localizing positivity is
source-blind (ACP P6), positivity on nonnegative tests is shared by dominated twins (ACP P7),
one-variable positivity is Landau–Fejér positivity (ACP P25).

**What a polarization does over `𝔽_q`.** The Rosati trace of an endomorphism `ξ` is an intersection
number `ξ*Θ · Θ^{g−1}`; `ξ*Θ` is the divisor of a section, an effective class; effective classes meet
an ample class nonnegatively. The positivity is a count and holds on the *whole* ring, while the
Frobenius is a similitude. Weil's step is then pure algebra: an anisotropic eigenvector of a
similitude has an eigenvalue of modulus `√q` (Π1).

**Four candidate sources over `ℤ`**, each examined here:

1. *An equivariant positive form* — the polarization itself (§4.1).
2. *Elliptic localization* — a localizing operation that is not hyperbolic at off-line pairs (§4.2).
3. *Collision* — an exterior structure turning complex quartets into real points that a count can
   see (§4.3).
4. *Counting* — a section count with Riemann–Roch on the square of `Spec ℤ` (§4.5).

The answer, in one paragraph. The test space of `ζ` carries two forms: Weil's form `W`, which is
Hecke-equivariant and whose positivity is RH, and the collided form `D = Σ_ρ m_ρ |f̂(ρ)|²`, which is
positive and whose Hecke-equivariance is RH; `W = D − Δ` with an off-line defect `Δ` uniform in
depth. `D` is a collision (it pairs `ρ` with `ρ̄`), it is not computed by the explicit formula, and
the global collision has no analytic carrier. Among reflection-commuting affine operations the only
non-hyperbolic localizers are the point reflections `σ_γ`, which are the functional equation conjugated by the archimedean flow: elliptic
localization is twisting, it collides the quartets at one ordinate into real pairs, its odd sector
forces, and it pays with gauge-charged prime weights and a conductor `log γ`. Its positive
completions are height couplings, which collide evenly and hit the Fejér barrier. Lattice counts on
the square of `Spec ℤ` collapse to the diagonal or factor, producing determinant positivity only.

---

## 3. Objects and language

| Over `𝔽_q` | APol object | Over `ℤ` | Lean |
|---|---|---|---|
| `(End J ⊗ ℚ, ′, Tr)` | algebra with involution and a polarization | Hecke algebra of `ℝ_{>0}` | `IsPolarization` |
| Frobenius spectrum | reflection-closed spectrum with weights | zeros `ρ ↦ 1 − ρ̄` | `ReflSpectrum`, `Zeta23.ZeroConfig` |
| Rosati trace form | Weil's form `W(f,f) = Σ m f̂(ρ) conj f̂(ρ*)` | explicit formula | `Z.W` |
| — | collided form `D(f) = Σ m |f̂(ρ)|²`, off-line defect `Δ` | not computed by the explicit formula | `collidedForm`, `offLineDefect` |
| Frobenius on a pair | local type: boost, swap, rotation; collided | Hecke, `σ_γ`, critical, real pairs | `localForm` (ACP) |
| — | reflection-commuting affine maps `s ↦ ½ + λ(s − ½) + iκ` | dilations, archimedean flow | `affine`, `rosatiRefl` |
| — | point reflection `σ_γ(s) = 1 + 2iγ − s`; test localizer `e^{−2iγu} f(−u)` | twisted functional equation | `sigma`, `sigmaTest` |
| — | twist `e^{−iγu} f`; shifted configuration `Z − iγ` | archimedean twist `ζ(s + iγ)` | `twist`, `shiftConfig` |
| `Λ²H¹` | exterior point `ρ + ρ′ − ½`; collided point `2 Re ρ − ½` | — | `extPoint` |
| `D ⊗ χ` | coupled datum `D ⊗ (e^{iθ} ⊕ e^{−iθ})` | height-coupled lift | `coupleDatum`, `heightCoupledΛ` (ACP) |
| — | charged weight `Λ(n) cos(γ log n)`; leading-line sum | Fejér barrier | `leadingSum`, `cosPoly` |
| — | coupled class `HeightCoupledSystem 2 1 1 γ` and its rigidity | `ζ_γ = ζ(s)² ζ(s ± iγ)` | `CoupledRigid` |
| `h⁰` on `C × C` | lattice counts on `ℤ²` with the product metric | lattice zeta functions | `rankOne_latticeZeta` |

**Words.**

- *Polarization*: a functional `τ` with `τ(v′v)` real, nonnegative, zero only at `v = 0`.
  *Anisotropic* vector: `τ(v′v) ≠ 0`.
- *Equivariant* form: invariant under the Hecke translations. *Collided* form: a sum of
  `|f̂(ρ)|²`, pairing each point with its conjugate. *Off-line defect*: `Σ (m/2)|f̂(ρ) − f̂(ρ*)|²`.
- *Local type* at a pair: hyperbolic (boost, isotropy), elliptic (swap: definite sectors), collided
  (the pair becomes real or becomes a modulus square).
- *Elliptic localizer* at ordinate `γ`: `σ_γ`. *Even/odd sector*: `σ_γ`-symmetric/antisymmetric
  tests. *Blind half*, *forcing half*: even and odd sectors.
- *Twist* at `γ`: `e^{−iγu} f`. *Conductor* of a localizer: the shift of the digamma density.
  *Conductor horizon*: the aperture below which the conductor pays the whole prime sum.
- *Charged weight*: a prime weight changing sign at prime powers. *Positive completion*: a harmonic
  lift `Π_k F(s ± ikγ)^{b_k}` with a nonnegative cosine polynomial.
- *Collision parity*: the multiplicity with which a collided point appears — even for couplings,
  odd for exterior squares.
- *Diagonal collapse*: a count on the square whose arithmetic depends only on `s₁ + s₂`.

Parameters: ordinate `γ`, depth `a = Re ρ − ½`, aperture `A` (support of tests), height `T`,
translation `L`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms and pillar theorems

### 4.1 The polarization and the two forms

| Pillar | Statement | Lean |
|---|---|---|
| **Π1 Polarization law** | In a complex `*`-algebra, a similitude `ξ′ξ = c` has `|μ|² = c` at every anisotropic eigenvector; a polarization makes all eigenvectors anisotropic. In the spectral model of a reflection-closed spectrum the Frobenius is always a similitude (`F′F = 1`), the Rosati form is a polarization iff the spectrum is unitary, and an off-circle eigenvector is isotropic. | `normSq_eq_of_similitude`, `normSq_eq_of_hasEigenvalue_of_polarization`, `ReflSpectrum.frob_star_mul_frob`, `ReflSpectrum.rosatiForm_nonneg_iff_unitary`, `ReflSpectrum.rosatiForm_single` |
| **Π2 The two forms** | `Re W = D − Δ` for every configuration (polarization identity `2 Re(u v̄) = |u|² + |v|² − |u − v|²` summed over the zeros); `W ≤ D`; `Δ = 0` on critical configurations and `Δ > 0` for a test separating an off-line point. Hecke translations are isometries of `W` for every configuration; `D(T_L f) = Σ m e^{2(Re ρ−½)L}|f̂(ρ)|²`, whose symmetric second difference is `Σ m (2 cosh(2aL) − 2)|f̂|²`. Spectral-model calibration: the Frobenius preserves `D` iff the spectrum is unitary. | `re_W_eq_collided_sub_defect`, `re_W_le_collided`, `offLineDefect_eq_zero_of_critical`, `offLineDefect_pos`, `W_translate_translate`, `collidedForm_translate`, `collidedForm_second_difference`, `ReflSpectrum.re_rosatiForm_eq_collided_sub_defect`, `ReflSpectrum.collided_frob_invariant_iff_unitary` |
| **Π3 RH as the coincidence of the two forms** | For `ζ` the collided form converges on every `C²` compactly supported test, is faithful, and is coercive at every aperture: `D(f) ≥ c_A‖f‖₂²` for tests in `[−A, A]` (Gårding inequality from the explicit-formula density and `D ≥ Re W`, plus compactness of the low frequencies and faithfulness); the zeros sample every Paley–Wiener space. On every aperture `D` is the logarithmic Sobolev norm: `c_A ∫|f̂|² log(|σ|+4) ≤ D(f) ≤ C_A ∫|f̂|² log(|σ|+4)` (upper: at each zero `f̂(ρ)` is the convolution of the line values with `χ̂(· − ia)`, Cauchy–Schwarz, Lorentzian zero mass `O(log)`; lower: the density exceeds `(1/4π) log` off a window, plus coercivity). Weil's form obeys the same Gårding inequality, so at every aperture it is negative on at most `2AT₀K/π` orthonormal tests (Bessel for the exponentials on `[−A, A]`). RH ⇔ `Re W = D` on every real test ⇔ `D` is invariant under every Hecke translation of every real test. | `zeta_summable_collided`, `collidedForm_eq_zero_iff`, `re_W_ge_sub_lowMass`, `collidedForm_ge_sub_lowMass`, `exists_collidedForm_coercive`, `collidedForm_le_log`, `log_le_collidedForm`, `collidedForm_equiv_logSobolev`, `card_negative_orthonormal_le`, `riemannHypothesis_iff_W_eq_collided`, `riemannHypothesis_iff_collided_hecke_invariant` |

Over `𝔽_q` one form is positive and equivariant. Over `ℤ`, `W` is equivariant and `D` positive;
each property of the other form is RH.

### 4.2 Elliptic localization

| Pillar | Statement | Lean |
|---|---|---|
| **Π4 Classification** | Affine maps commuting with `s ↦ 1 − s̄` are `s ↦ ½ + λ(s − ½) + iκ`. Such a map sends an off-line point into its pair iff it is the identity or `σ_γ`, `γ = Im ρ`, and `σ_γ` swaps the pair; a critical point is fixed by a one-parameter family of dilations. `σ_γ = τ_γ ∘ σ_0 ∘ τ_{−γ}`; point reflections compose to vertical translations. | `affine_commute_rosatiRefl_iff`, `affine_mem_pair_iff`, `affine_fixes_critical_iff`, `sigma_eq_tau_comp_fe_comp_tau`, `sigma_comp_sigma`, `sigma_swaps`, `sigma_eq_self_iff` |
| **Π5 Definite sectors** | On `G ∘ σ_γ = ±G` the local form of a pair of ordinate `γ` is `±2|G(ρ)|²`. | `localForm_of_sigma_symmetric`, `localForm_of_sigma_antisymmetric` |
| **Π6 Dihedral dilemma** | Positivity on the span of a fibre vector, its boost and their swaps forces the vector to vanish; a positive carrier stable under one Hecke operator and `σ_γ` is blind at every off-line pair of ordinate `γ`. `σ_γ` conjugates `p^{s−½}` to `p^{2iγ}p^{½−s}`; the twisted symmetric symbol is `σ_γ`-invariant and scalar on the pairs of ordinate `γ`, equal to `2p^{iγ} cosh(a log p)`. | `eq_zero_of_boost_swap_nonneg`, `hecke_swap_blind`, `heckeSymbol_sigma`, `twistedSymSymbol_sigma`, `twistedSymSymbol_pair`, `twistedSymSymbol_eq_cosh` |
| **Π7 Sectors are twists; the twist identity; collision** | `tr(e^{−iγu}f)(s) = tr f(s − iγ)`, `tr(f(−·))(s) = tr f(1 − s)`, `tr(σ_γ f) = tr f ∘ σ_γ`. `σ_γ`-symmetric (antisymmetric) tests are exactly the twists of even (odd) tests. `Z.W(e^{−iγu}f, e^{−iγu}g) = (Z − iγ).W(f, g)` exactly. Ordinate-`γ` quartets become real pairs; at a point of ordinate `γ` the summand is `+m|tr|²` on the even and `−m|tr|²` on the odd sector. | `tr_twist`, `tr_fe`, `tr_sigmaTest`, `sigmaTest_twist_even`, `sigmaTest_twist_odd`, `exists_even_of_sigmaTest_eq`, `exists_odd_of_sigmaTest_eq_neg`, `shiftConfig`, `W_twist`, `shift_quartet`, `Wsummand_of_sigma_symmetric`, `Wsummand_of_sigma_antisymmetric`, `Wsummand_real_even`, `Wsummand_real_odd` |
| **Π8 The price** | The twisted explicit formula: shifted poles (spectral points `−iγ`, `1 − iγ`), phased prime weights, the digamma density shifted by `γ`. On real even kernels the atoms are `2 cos(γ log n) K(log n)`, and for `γ ≠ 0` some prime power has `cos(γ log n) < 0`: every elliptic localizer off the real axis is gauge charged. Below the conductor horizon `(4 + ε)e^A ≲ log γ` positivity of `ζ`'s twisted form is a theorem, proved by paying the prime sum in absolute value: a source-blind positivity. | `literatureRHS_twist`, `twisted_explicit_formula`, `twisted_atoms_of_real_even`, `exists_vonMangoldt_pos_cos_neg`, `elliptic_sector_nonneg_below_conductor_horizon` |
| **Π9 The forcing half** | The single-height detector `sinh(δu)(a² − u²)₊^{5/2}`, twisted to the ordinate of a candidate zero, lies in the odd sector; positivity of Weil's form on it forbids an isolated off-line zero once the depth signal beats the local zero count, at aperture `≍ (1/2δ) log log γ`. The even sector never forces. | `sigmaTest_twist_sinhTest`, `Wsummand_twist_sinhTest`, `odd_sector_nonneg_forces_offLine_companion`, `even_sector_summand_nonneg` |

### 4.3 Collision

| Pillar | Statement | Lean |
|---|---|---|
| **Π10 Collision law** | `ρ + ρ̄ − ½ = 2 Re ρ − ½`: collision doubles depth and forgets the ordinate; the exterior divisor is reflection-equivariant; RH = every collided point is `½`. The twist collides exactly one ordinate. A function analytic on a connected neighbourhood of `[−½, 3/2]` vanishing at every collided point of an infinite configuration, to the number of points colliding there, is zero; for `ζ` unconditionally. | `extPoint_conj`, `extPoint_conj_re`, `extPoint_rosatiRefl`, `extPoint_conj_eq_half_iff`, `shift_collides_at_ordinate`, `eqOn_zero_of_vanishes_on_collision`, `zeta_global_collision_not_analytic` |
| **Π11 Collision parity** | The coupled datum `D ⊗ (e^{iθ} ⊕ e^{−iθ})` is a curve datum; at `θ = −arg β` it turns the impure eigenvalue into a real one (the complex fake's `2i ↦ 2`), yet every kernel count of every coupled datum is a modulus square. Over `ℤ` the height-coupled completion vanishes to even order at every real point. Exterior squares collide oddly and their counts force unitarity (ACP P17). | `coupleDatum`, `couple_detDeg_eq_normSq`, `couple_detDeg_nonneg`, `complexFake_couple_collides`, `heightCoupled_order_even` |
| **Π12 Escape kernels are collided** | The Cauchy denominator of an escape kernel is `ext(z_k, z̄_l) − ½`; every escape form is the Pick form of the conjugate exterior divisor of the dominant zeros, positive definite on distinct ordinates. | `cauchy_denominator_eq_extPoint`, `escapeForm_eq_exteriorCauchyForm`, `exteriorCauchyForm_pos` |

### 4.4 Completion, rigidity and the base

| Pillar | Statement | Lean |
|---|---|---|
| **Π13 Positive configurations, leading-line law and Fejér barrier** | A finite polar configuration `Σ c(z)/(s − z)` has positive-definite vertical sections right of its points iff its exponential polynomial `Σ c(z)e^{zt}` has nonnegative real part on `t > 0` (Laplace–Bochner); one positive-definite vertical section already forces this, with no conjugation symmetry (Fejér sums), so positivity of one section propagates to all sections right of the configuration. On a line with ordinates in `ωℤ`, positivity is a single Hermitian square `|Q(e^{iωt})|²` (Fejér–Riesz): positive completions on commensurable lines are couplings. On a configuration with all ordinates in `ωℤ`, each line's trigonometric sum is nonnegative wherever all the lines to its right vanish (line hierarchy). The trigonometric sum of the rightmost line of a positive configuration is nonnegative for all ordinates (Bohr large returns), and that line is itself a positive configuration. A harmonic lift of a deepest quartet puts `2m cos(γt)P(γt)` on that line; for a nonnegative cosine polynomial `P ≢ 0` this is negative somewhere, so no positive multiplier removes the whole lifted divisor. | `posDef_polarSum_of_scaleWeight_nonneg`, `posDef_polarSum_iff_scaleWeight_nonneg`, `posDef_polarSum_above_leading`, `posDef_section_iff_scaleWeight_nonneg`, `posDef_section_of_posDef_section`, `posDef_latticeLine_iff_normSq`, `leadingSum_eq_normSq`, `leadingSum_nonneg_of_higher_eq_zero`, `secondLine_nonneg_of_lattice`, `leadingSum_nonneg`, `posDef_polarSum_of_line`, `posDef_leadingLine`, `harmonicLift_leading`, `exists_cos_mul_neg`, `not_removes_lifted_divisor` |
| **Π14 Rigidity excludes zeros** | `ζ_γ ∈ HeightCoupledSystem 2 1 1 γ`; rigidity of that class at `γ` excludes every off-line zero at ordinate `γ` (a zero contracts inside the class and raises the order at `½` by four); rigidity at every ordinate is RH. | `zeta_mem_heightCoupledClass`, `CoupledRigid`, `xi_ne_zero_of_rigid`, `riemannHypothesis_of_forall_rigid` |
| **Π15 Twists are rate neutral** | The twisted orbit correlation is `e^{iγt}` times the orbit correlation of `Z − iγ`, whose depth spectrum is that of `Z`; every growth bound transfers both ways. | `translate_twist`, `W_translate_twist`, `shiftConfig_re`, `twisted_growth_iff` |

### 4.5 Counting and charge

| Pillar | Statement | Lean |
|---|---|---|
| **Π16 Diagonal collapse** | The lattice of a Hecke graph `ℤ(n, m)` has lattice zeta `n^{−s₁}m^{−s₂}ζ(s₁ + s₂)`; `ℤ²` has `ζ(s₁)ζ(s₂)`. On the reflection plane `s₂ = 1 − s̄₁` the diagonal variable is `1 + 2i Im s₁`, on the line where `ζ ≠ 0`, and the product is `ξ(s)ξ(1 − s̄) = |ξ(s)|²`. | `rankOne_latticeZeta`, `fullLattice_latticeZeta`, `reflection_plane_diagonal`, `riemannZeta_reflection_plane_diagonal_ne_zero`, `xi_mul_xi_reflection_plane` |
| **Π17 The first gauge charge is a twist** | On kernels reading only the atom `2`, the Liouville weight's Weil functional is `ζ`'s at the twist by `π / log 2` plus explicit archimedean and polar differences; on autocorrelations, `W_λ(f) = W_ζ(e^{−iγ₂u}f) + Δ_arch + Δ_pole`. No ordinate flips `2` and `3` together. | `exp_twist_log_two`, `weilFullFunctional_liouville_eq_twist`, `liouville_window_eq_zeta_twisted`, `not_twist_flips_two_and_three` |

---

## 5. The questions and their answers

1. **What is the polarization?** The abstract law is Π1: Weil's step needs only anisotropic
   eigenvectors of a similitude. Over `ℤ` the ample class exists (`H + V`, ACS); what is missing
   is a form with both properties of a polarization. `ζ` has two forms, each with one property:
   `W` equivariant (Π2), `D` positive (Π2); RH is the coincidence of the two (Π3), equivalently the
   equivariance of `D`, equivalently the positivity of `W`. `D` is a collision: it is not of the form
   `Σ_ρ H(ρ)` with `H` holomorphic, so the explicit formula does not compute it. A polarization
   argument over `ℤ` must compute `D` (or `Δ`) from a structure, or prove the equivariance of a
   computable positive form.
2. **What counts sections?** Lattice counts on the square of `Spec ℤ` (theta series with the product
   metric) see `ζ(s₁ + s₂)` for rank-one lattices and `ζ(s₁)ζ(s₂)` for `ℤ²` (Π16). On the reflection
   plane the first reads only the line `Re = 1`, the second is a modulus square: lattice counting
   produces boundary or determinant positivity, never Rosati positivity. The Riemann–Roch of a
   lattice of fixed rank (Poisson summation) is linear in its degree; a quadratic term, which Weil's
   form would have to be, needs rank growing with the class, and no lattice of the square has it. Combined with ACS's universal floor law (every
   ample cone with RR forces the defect floor), the counting route requires a genuinely
   two-variable section theory.
3. **Which localizer is not hyperbolic?** Exactly the point reflections `σ_γ` (Π4), the functional
   equation conjugated by the archimedean flow. Their fibres are definite (Π5); their sectors are
   the even and odd tests of the twist (Π7); the odd sector is the forcing half and its first theorem
   is the single-height detector (Π9). Combined with a Hecke separation at the same pair they blind
   it (Π6): an elliptic localizer can only use the twisted symmetric Hecke operators, which are
   scalar on the pair.
4. **Where is the gauge charge?** In the prime side of every elliptic sector: `Λ(n) cos(γ log n)`,
   negative at some prime power for every `γ ≠ 0` (Π8). The first gauge charge, the flip of `Λ(2)`,
   *is* the twist at `π / log 2` on the first-prime window, up to archimedean and polar terms (Π17);
   separating `ζ` from that twin is a comparison of `ζ`'s form with itself at heights `0` and
   `π / log 2`. From the second prime on, gauge charge is not archimedean (Π17).
5. **What is the exterior square of the spectrum?** Its points are `ρ + ρ′ − ½`; conjugate pairs
   collide on the real axis at twice their depth (Π10). Ordinate-local collisions are twists. The
   global collision has no analytic carrier near `[−½, 3/2]` (Π10). Couplings collide evenly and are
   blind to kernel counts, exterior squares collide oddly and count (Π11): the height-coupled lifts
   are couplings.
6. **Is a coupled class rigid?** No: rigidity of `HeightCoupledSystem 2 1 1 γ` at `γ` would
   exclude every off-line zero at ordinate `γ` (Π14), but at every critical ordinate the outward
   splitting `((s − ½)² + β²)/(s − ½)²` is Bochner-positive and produces non-proportional members
   ([BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md),
   `not_coupledRigid_of_xi_critical_zero`). The surviving form of the question is one-sided: the
   central vanishing ceiling `ord_{½}(Λ) ≤ ord_{½}(Λ_γ)` across the class, which the outward
   deformations respect, the inward collapses violate, and which at every ordinate is RH.
7. **What pays `ζ`'s own zeros?** The off-line defect `Δ = D − Re W` (Π2): each off-line pair pays
   `m|f̂(ρ) − f̂(ρ*)|²` whatever its depth, critical zeros pay nothing, and `Δ ≡ 0` iff RH (Π3). This
   is the depth-uniform capacity; it is computable exactly when the collided form is.
8. **How does the archimedean place enter?** As the conductor of elliptic localization (Π8): the
   twist shifts the digamma density by `γ`, which pays the entire prime sum below the conductor
   horizon — a source-blind positivity — and the poles move to `−iγ, 1 − iγ`. In the first gauge
   charge, the difference between `ζ` and its twin is purely archimedean and polar (Π17).
9. **What are escape states of `ζ`?** Phase kernels over the dominant translated zeros (ACP
   P20–P27), which are Pick forms of the conjugate exterior divisor (Π12): collided objects, positive
   by construction, classifying the dominant zeros without excluding them. Exclusion needs the
   gauge mass (ACG: RH ⇔ every escape state has positive gauge mass); completeness for `ζ` is the
   explicit-formula split of the cofactor profile (B3.2), an analytic input of explicit-formula type.
10. **How does an average become a point?** Through hyperbolic growth on the forcing half: positivity
    on the odd twisted detector forces every off-line zero of depth `δ` to have an off-line companion
    nearby, at aperture `≍ (1/2δ) log log γ` (Π9), below the zero-spacing scale `log γ`; horizon averages diagonalize escape kernels (ACP P21). For
    critical zeros a correspondence of length `L` resolves heights `1/L` (ACP P11).
11. **What is the base?** Not the twists: they are rate neutral (Π15), and positive completions are
    Fejér-limited (Π13); family averages lose linearly (ACP P23); a fixed loss is RH (ACP P8).

---

## 6. Traps

| Trap | Truth |
|---|---|
| An elliptic symmetry gives a positivity that can exclude a zero | Its fibres are definite: off-line pairs are positive on the even sector; only the odd sector forces |
| The functional equation is the elliptic localizer | It is one only at ordinate `0`; at ordinate `γ` the localizer is its conjugate by the archimedean flow |
| Elliptic localization is free | Its prime side is charged and its archimedean side carries the conductor `log γ` |
| Hecke separation can be combined with elliptic symmetry | A boost and the swap at one pair blind it |
| The polarization over `ℤ` is missing | A positive form exists (`D`); what is missing is its equivariance, i.e. its computation |
| `W ≥ 0` is weaker than `W = D` | They are equivalent for `ζ`; the defect is the whole content |
| A collision that produces a real point can be counted | Couplings collide evenly: their kernel counts are modulus squares |
| Squaring the explicit formula collides all conjugate pairs | No analytic function carries the global collision |
| A two-variable lattice count is a surface count | It collapses to the diagonal or factors |
| A positive completion of a charged weight removes the quartet | Its leading line is `2m cos θ P(θ)`, negative somewhere |
| Twisting amplifies | It moves ordinates and keeps every depth |
| Escape positivity excludes zeros | Escape kernels are collided forms, positive by construction |
| The Liouville twin differs from `ζ` arithmetically on the first window | It is `ζ` at height `π / log 2` up to archimedean and polar terms |

---

## 7. Tools

**From sibling programmes:** polar and scaling surfaces, curve data and fakes, the local form and
its isometries, Hecke symbols, completed positive and height-coupled systems with their contraction
calculus, Post–Widder scale weights and the real-anchor law, zero configurations and the explicit
formula, height shifts and single-height detection, window certificates, escape kernels.

**Built here:**

- the polarization calculus: anisotropy, similitudes, reflection-closed spectral models;
- the two forms `W`, `D` and the defect `Δ`: decomposition, domination, Hecke behaviour, second
  differences, convergence for `ζ`;
- the reflection-commuting affine group, point reflections, the archimedean flow on the spectral
  plane;
- test operations (twist, reflection, localizer) and their transforms; sector characterizations;
- shifted configurations and the twist identity of Weil's form;
- the twisted explicit formula, charged weights, the charge theorem;
- the twisted symmetric Hecke symbols and the dihedral dilemma;
- the classification of positive polar configurations by their exponential polynomial; the
  leading-line law; positivity of cosine–Laplace weights from positive-definite sums
  (`HTGeometry.LaplaceWeights.nonneg_of_laplace_posDef`); the Fejér–Riesz factorization
  (`HTGeometry.fejerRiesz`); cosine polynomials as
  Chebyshev polynomials; the barrier inequality;
- strip values of a test as convolutions of its line values (`tr_eq_integral_conv`) and the local
  estimate `|f̂(s)|² ≤ B_A ∫ |f̂(σ)|²/(1 + (Im s − σ)²)` in the critical strip
  (`normSq_tr_le_local`);
- exterior points, collided points, the non-analyticity of global collision;
- coupled curve data and the parity of collisions;
- lattice zeta functions of the square and the reflection plane;
- translation, rate neutrality of twists;
- the exterior Cauchy form of escape kernels.

---

## 8. Open research topics

1. **Compute the defect.** An arithmetic structure computing `D` or `Δ` (equivalently the global
   collision) without the zeros. Any such structure gives `W ≥ 0` as `D ≥ Δ`.
2. **The forcing half beyond the conductor horizon.** Odd-sector positivity of `ζ`'s twisted form at
   apertures between `log log γ` (the conductor horizon) and `log γ` (the zero spacing).
3. **Odd collisions over `ℤ`.** A two-variable structure whose collided points appear with odd
   multiplicity at every ordinate at once; couplings collide evenly, the global exterior square has
   no analytic carrier.
4. **The central ceiling of the coupled class** beyond rational deformations: for rational coupled
   deformations the ceiling at `γ` is equivalent to the absence of zeros at ordinate `γ`
   ([BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md),
   `rationalCentralVanishingCeiling_iff`); what remains is a ceiling for the whole class that does
   not pass through the zeros at `γ`.
5. **A two-variable section count** with rank growing in the class and Riemann–Roch whose quadratic
   term is Weil's form.
6. **The separating aperture of the first twin** (W8): compare `W_ζ(f)` and
   `W_ζ(e^{−iπu/log 2} f) + Δ_arch + Δ_pole` on the odd window.
7. **Equivariant positive forms from counting**: a positive form whose Hecke equivariance is a
   theorem (as over `𝔽_q`), and its relation to `D`.

---

## 9. Success criteria and contribution standard

APol succeeds when it produces a positivity theorem of a type the corpus does not contain — an
equivariant positive form, a forcing elliptic sector beyond the conductor horizon, an odd collision,
a rigidity law, a section count — or a sharp no-go naming the missing input, with its positive
survivor. Its present no-gos and survivors: the only non-hyperbolic localizers are twists (survivor:
the forcing half); Hecke and elliptic symmetry blind each other (survivor: twisted symmetric
operators); couplings collide evenly (survivor: real-anchor contraction); positive completions are
Fejér-limited (survivor: the leading-line law); lattice counts collapse (survivor: boundary
positivity on the reflection plane); the global collision is not analytic (survivor: the
collided form `D` as a convergent positive form).

| Criterion | Test |
|---|---|
| Selectivity | distinguishes `ζ` from the battery: `CompletedPositiveSystem 2 1` pairs and quartets and their height-coupled lifts, pole-order-3 and strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems, the golden datum, the complex fake, `Γ_ℝ^d` solutions, dominated and flipped twins |
| Gauge charge | separates the gauge point `0` from its twins |
| Localization | isolates a reflection pair and states its aperture |
| Local type | positivity not forced by a symmetry hyperbolic at off-line pairs |
| Two forms | states what it gives for `W`, for `D` and for `Δ` |
| Collision parity | states the multiplicity of its collided points |
| Calibration | Weil for curves; exterior-count purity; the Fejér barrier; the `κ = 1` collapse |

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. name its mechanism (equivariant, positive, elliptic, collided, counting, charged) and the layer of
   Weil's argument it concerns;
3. state the local type of its operations at off-line pairs and the sector on which it forces;
4. state its gauge charge, its conductor and its collision parity;
5. say what it gives on the golden datum, the complex fake, curves and the battery;
6. keep identities apart from signs;
7. record the positive survivor of every no-go.

Principles: positivity forces only through indefinite fibres; elliptic means definite, not
positive; localization in height is a twist and costs a conductor; a completion is a coupling and
collides evenly; the positive form `D` exists, its computation is the problem; identities first,
sign last; a reformulation is not a reduction.

---

## 10. Modules

| Module | Content |
|---|---|
| `ThePolarizationLaw` | Anisotropy and similitudes; polarizations; the spectral model, its Rosati form, its two forms |
| `TheEllipticLocalizers` | Reflection-commuting affine maps; stabilizers; point reflections and the archimedean flow; definite sectors; the dihedral dilemma; twisted symmetric Hecke symbols |
| `TwistedSectorsCollideQuartets` | Transforms of twisted and reflected tests; sectors as twists; shifted configurations; the twist identity; collision of quartets; sector signs |
| `ThePriceOfEllipticLocalization` | Twists and autocorrelations; the twisted explicit formula; charged weights; the charge theorem; the conductor horizon |
| `TheForcingHalfOfEllipticLocalization` | The odd-sector detector; odd-sector positivity forbids isolated off-line zeros; the even sector cannot force |
| `TheFejerBarrierForCoupledContraction` | Leading-line sums; the leading-line law; harmonic lifts; Chebyshev form of cosine polynomials; the barrier |
| `TheCollisionLaw` | Exterior and collided points; ordinate-local collision; non-analyticity of the global collision |
| `CouplingCollidesEvenly` | Coupled curve data; kernel counts as modulus squares; the coupled complex fake; even orders of height-coupled lifts |
| `EscapeKernelsAreCollidedForms` | Cauchy denominators as exterior points; escape forms as exterior Cauchy forms |
| `RigidityOfTheCoupledClassExcludesItsZeros` | Coupled rigidity; exclusion of zeros at the ordinate; RH from rigidity at every ordinate |
| `TwistsAreRateNeutral` | Twisted orbit correlations; depth preservation; transfer of growth bounds |
| `TheDiagonalCollapse` | Lattice zeta functions of the square; the reflection plane |
| `TheFirstGaugeChargeIsATwist` | The flip at `2` as the twist at `π / log 2`; the Liouville window identity; the second charge |
| `TheOscillatoryCapacity` | Collided form and defect; `Re W = D − Δ`; convergence for `ζ`; RH as `W = D` |
| `HeckeInvarianceOfTheCollidedPolarizationIsRH` | Hecke isometries of `W`; translation of `D`; second differences; RH as equivariance of `D` |
| `TheCollidedFormIsAPolarization` | Faithfulness of `D`; sampling at aperture `3/10`; Hecke similitudes of `D` are RH |
| `TheDepthProfileCarriesTheGlobalCollision` | Depth profile `L ↦ D(T_L f)`; its rate law `2 · (deepest seen depth)` |
| `TheLocalWeylLawOfTheCollidedForm` | `D(e^{−iγu} f) ≍ ‖f‖² log|γ|` |
| `TheLeadingLineIsPositive` | Leading-line law for arbitrary ordinates via Bohr large returns |
| `PositivityIsInheritedByTheLeadingLine` | One-line configurations; inheritance of positivity by the leading line |
| `PositivePolarConfigurationsAreNonnegativeExponentialPolynomials` | Classification of positive polar configurations; positivity at the leading abscissa |
| `PositiveLatticeLinesAreCouplings` | Positive lattice lines are Hermitian squares; the commensurable leading line is a coupling |
| `TheSelectivityBatteryOfPolarization` | Golden and complex-fake spectra fail both forms; couplings hide the golden real pair |
| `OneVerticalSectionDecidesPositivity` | One positive-definite vertical section decides the configuration; rigidity across abscissae |
| `PositivityDescendsThroughTheZerosOfHigherLines` | Line hierarchy of lattice configurations: each line is nonnegative on the common zeros of the lines to its right |
| `TheCollidedFormSamplesHighFrequencies` | Weil's form as an explicit-formula density integral; the Gårding inequality for `D` |
| `TheCollidedFormIsCoerciveAtEveryAperture` | Mollification and the convolution theorem; Arzelà–Ascoli on the line; compactness of low frequencies; coercivity of `D` at every aperture |
| `WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture` | Bessel's inequality for the exponentials on `[−A, A]`; at most `2AT₀K/π` orthonormal negative directions of `W` at aperture `A` |
| `TheCollidedFormIsTheLogarithmicSobolevNorm` | Convolution representation and local estimate in the strip; the two-sided equivalence of `D` with `∫|f̂|² log(|σ|+4)` at every aperture |
