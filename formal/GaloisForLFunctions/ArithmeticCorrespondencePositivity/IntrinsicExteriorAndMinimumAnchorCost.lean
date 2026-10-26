import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions
import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass

/-!
# Intrinsic exterior obstructions, sharp minimum anchor cost, and Fejér entry-cost halving

`ExteriorAndHeightCoupledQuartetContractions` eliminates the marginal `Δκ ≥ 1` boundary pole tax on
complex off-critical quartets `{1/2 ± a ± iγ}` (`0 < a < 1/2`, `γ ≠ 0`) by lifting any
`CompletedPositiveSystem κ d` to `HeightCoupledSystem (2κ) κ d γ` (`F_γ(s) = F(s)² F(s+iγ) F(s−iγ)`),
paying a one-time entry cost of central pole order `2κ`, shifted boundary poles `κ_γ = κ` at
`{±iγ, 1 ± iγ}`, and shifted archimedean Gamma factors `(Γ_ℝ(s + iγ) Γ_ℝ(s − iγ))^d`.

This module resolves both the entry-cost reduction problem (whether shifted poles can be cancelled
or twisted out via intrinsic second-exterior, Rankin–Selberg, boundary-twist, or multi-shift Fejér
constructions at `κ_γ = 0` or lower central pole cost) and the dual Post–Widder / Hadamard converse
problem (the sharp minimum boundary-pole and archimedean-Gamma cost of any positive-definite
mapping sending `{1/2 ± a ± iγ}` to a weight-`≥ 2` real anchor at `1/2 + a`):

* **Intrinsic second-exterior and isobaric shift packet dichotomy**
  (`degreeOne_exteriorTwo_eq_zero`, `isobaricExteriorTwoPoly`, `isobaricExteriorTwoPoly_eq`,
  `isobaricExteriorTwoPoly_pi_neg`, `isobaricExteriorTwoPoly_nonneg_of_five_le`,
  `isobaricExteriorTwoPoly_ratio_ge`, `centeredScaleCross_re_gt_one`). Local degree-`1` Adams
  exterior squares vanish identically. On the isobaric shift packet
  `1^{⊕ m₀} ⊕ |·|^{iγ} ⊕ |·|^{−iγ}` (`g_{m₀}(θ) = m₀ + 2 cos θ`), the Adams exterior trace
  `(g_{m₀}(θ)² − g_{m₀}(2θ))/2 = ((m₀² − m₀ + 2)/2) + 2 m₀ cos θ` cancels `cos 2θ`: at `m₀ = 0`
  `κ_γ = 0` holds with zero quartet collision; for `1 ≤ m₀ ≤ 4` nonnegativity fails at `θ = π`; and
  for `m₀ ≥ 5` nonnegativity holds with `κ_γ = m₀ κ ≥ 5κ > 0` and central-to-anchor ratio
  `≥ 11/5 > 2`. Globally in scale `t`, centered bilinear squaring cross-couples the pole `s = 1`
  with `ρ = 1/2 + a + iγ` (`a > 0`) to place singularities at `1 + a + iγ` inside `Re s > 1`.
* **Exact boundary-twist absorption to `κ_γ = 0`, sharp origin-capacity floor, and ordinate pole decay**
  (`isEvenPosDef_boundaryTwistFactor`, `HeightCoupledSystem.absorbShiftedPoles`,
  `two_mul_le_origin_of_poleCancelling_posDef`, `re_logDeriv_shiftedPolePoly_two_eq`,
  `re_neg_logDeriv_boundaryTwistFactor_two_eq`, `HeightCoupledSystem.archimedean_budget_exact`,
  `CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound`). Multiplying
  `HeightCoupledSystem κ₀ κγ d γ F Λ` by `boundaryTwistFactor γ ^ κγ` unconditionally eliminates
  shifted poles (`κ_γ ↦ 0`) on the exact same completion `Λ` at `κ₀ ↦ κ₀ + 2 κ_γ` (`4κ` on
  `heightCouple`, strictly minimal by `total_zero_mass_le`). Conversely, keeping `κ_γ = κ` strictly
  improves the `s = 2` pole budget by `3 γ² (γ² + 3) κ / ((4 + γ²)(1 + γ²)) > 0` and halves the
  ordinate-quartet pole ceiling to `(9 + 12/(4 + γ²) + 6/(1 + γ²)) κ → 9κ` as `|γ| → ∞`.
* **Single-system real-anchor planting (`κ_γ = 0, Δd = 0`) and functor-independent Hadamard converse**
  (`realPairPlanter`, `isEvenPosDef_realPairPlanter`, `CompletedPositiveSystem.plantRealPair`,
  `CompletedPositiveSystem.plantDoubleRealAnchor`, `polarSum_sum_weights_nonneg`,
  `two_le_pole_cost_of_doubleRealAnchor_polarSum`,
  `CompletedPositiveSystem.anchored_quartet_pole_lower_bound`,
  `CompletedPositiveSystem.three_le_pole_of_anchored_quartet`). `realPairPlanter a s` plants a
  weight-`2` real anchor at `1/2 + a` inside `CompletedPositiveSystem (κ + 2) d` (`Δκ = 2`,
  minimal among zero-planting polar sums). Completely independent of how `(F*, Λ*)` is constructed,
  any `CompletedPositiveSystem κ* d*` carrying `M = ∑_{a ∈ A} m(a)` weight-`2` real-anchored
  quartets along `Im s = γ` satisfies
  `16 M + (144/(9 + 4γ²)) M + 4 ord_{1/2}(Λ*) + (72/(9 + 4γ²)) ord_{1/2 + iγ}(Λ*) + 5 d* < 9 κ*`,
  forcing `κ* ≥ 3` already for `M = 1, d* ≥ 1` (attained at `κ = 1, d = 1 ⟹ κ* = 3`).
* **Sharp Fejér–Egerváry–Szász multiplier converse, two-sided shifted-Gamma sandwich, and degree-`K`
  Fejér entry-cost halving** (`fejer_egervary_szasz_first_harmonic_le`,
  `cosine_multiplier_anchor_cost_lower`, `re_logDeriv_Gammaℝ_two_shift_ge`,
  `re_logDeriv_Gammaℝ_pair_two_sandwich`, `IsEvenPosDef.fejerShift`, `FejerCoupledSystem`,
  `CompletedPositiveSystem.fejerCouple`, `FejerCoupledSystem.contractCollidedQuartet`,
  `FejerCoupledSystem.archimedean_budget`, `CompletedPositiveSystem.fejerOrdinateQuartet_bound`,
  `CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound`, `tendsto_fejer_central_pole_coeff`).
  Discrete quadrature at `(2r + 1)π/(K + 2)` proves `c₁ ≤ 2 c₀ cos(π/(K + 2))` for every degree-`K`
  nonnegative cosine polynomial, forcing `c₀ ≥ 1 / cos(π/(K + 2)) > 1` whenever `c₁ ≥ 2` and
  shifted Gamma cost `∈ [d(log(3 + |γ|) − 5), d(log(3 + |γ|) + 1/2)]` per unit pair across all
  `γ ∈ ℝ`. Dually, `FejerCoupledSystem K` achieves zero-marginal-tax quartet contraction at
  normalized central pole cost `(9(K + 1)/(2K)) κ ↘ (9/2) κ` (reaching `(27/4) κ < 8 κ` at `K = 2`).
-/

open Complex Polynomial Finset Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri MultiplicativePositivityGeometry StripBochnerWeilForcing HTGeometry

/-! ### 1. Intrinsic second-exterior and isobaric shift packet dichotomy -/

/-- **Local degree-`1` Adams exterior vanishing.** On any one-dimensional local Euler parameter
tuple `α : Fin 1 → ℂ`, the `m`-th Adams exterior-square power sum `((∑ α_i^m)² − ∑ α_i^{2m}) / 2`
vanishes identically. -/
theorem degreeOne_exteriorTwo_eq_zero (α : Fin 1 → ℂ) (m : ℕ) :
    ((∑ i : Fin 1, α i ^ m) ^ 2 - ∑ i : Fin 1, α i ^ (2 * m)) / 2 = 0 := by
  simp only [Fin.sum_univ_one]
  rw [pow_mul', sub_self, zero_div]

/-- Local prime-power trace `g_{m₀}(θ) = m₀ + 2 cos θ` of the isobaric shift packet
`1^{⊕ m₀} ⊕ |·|^{iγ} ⊕ |·|^{−iγ}` at `θ = γ log p^r`. -/
def isobaricShiftTrace (m₀ : ℕ) (θ : ℝ) : ℝ :=
  (m₀ : ℝ) + 2 * Real.cos θ

/-- Adams second-exterior trace `(g_{m₀}(θ)² − g_{m₀}(2θ)) / 2` of the isobaric shift packet. -/
def isobaricExteriorTwoPoly (m₀ : ℕ) (θ : ℝ) : ℝ :=
  (isobaricShiftTrace m₀ θ ^ 2 - isobaricShiftTrace m₀ (2 * θ)) / 2

/-- **Exact `cos 2θ` cancellation in the isobaric exterior square.** The second harmonic `4 cos² θ`
in `g_{m₀}(θ)²` cancels `2 cos 2θ = 4 cos² θ − 2` in `g_{m₀}(2θ)`, leaving
`((m₀² − m₀ + 2) / 2) + 2 m₀ cos θ`. -/
theorem isobaricExteriorTwoPoly_eq (m₀ : ℕ) (θ : ℝ) :
    isobaricExteriorTwoPoly m₀ θ =
      (((m₀ : ℝ) ^ 2 - (m₀ : ℝ) + 2) / 2) + 2 * (m₀ : ℝ) * Real.cos θ := by
  unfold isobaricExteriorTwoPoly isobaricShiftTrace
  rw [Real.cos_two_mul]
  ring

/-- At `m₀ = 0` (`|·|^{iγ} ⊕ |·|^{−iγ}` with no central copy), `isobaricExteriorTwoPoly 0 θ = 1`
has `κ_γ = 0` (`cos θ` coefficient `0`) and completely erases the height `γ`. -/
theorem isobaricExteriorTwoPoly_zero_central (θ : ℝ) :
    isobaricExteriorTwoPoly 0 θ = 1 := by
  rw [isobaricExteriorTwoPoly_eq]
  norm_num

/-- **Positivity failure for `1 ≤ m₀ ≤ 4`.** At `θ = π`, `isobaricExteriorTwoPoly m₀ π < 0` for
every `m₀ ∈ {1, 2, 3, 4}`, so the Adams exterior square of `1^{⊕ m₀} ⊕ |·|^{iγ} ⊕ |·|^{−iγ}` fails
pointwise nonnegativity below `m₀ = 5`. -/
theorem isobaricExteriorTwoPoly_pi_neg {m₀ : ℕ} (h1 : 1 ≤ m₀) (h4 : m₀ ≤ 4) :
    isobaricExteriorTwoPoly m₀ Real.pi < 0 := by
  rw [isobaricExteriorTwoPoly_eq, Real.cos_pi]
  have hm : m₀ = 1 ∨ m₀ = 2 ∨ m₀ = 3 ∨ m₀ = 4 := by omega
  rcases hm with rfl | rfl | rfl | rfl <;> norm_num

/-- **Positivity threshold `m₀ ≥ 5` with persistent shifted poles and worse central ratio.**
For `m₀ ≥ 5`, `isobaricExteriorTwoPoly m₀ θ > 0` for all `θ ∈ ℝ`, while its shifted-pole weight is
`m₀ ≥ 5 > 0` (`κ_γ ≠ 0`) and its central-to-half-anchor ratio `((m₀² − m₀ + 2)/2) / m₀ ≥ 11/5 > 2`
strictly exceeds `HeightCoupledSystem`'s ratio `2`. -/
theorem isobaricExteriorTwoPoly_nonneg_of_five_le {m₀ : ℕ} (h5 : 5 ≤ m₀) (θ : ℝ) :
    0 < isobaricExteriorTwoPoly m₀ θ := by
  rw [isobaricExteriorTwoPoly_eq]
  have hm5 : (5 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast h5
  have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hquad : (0 : ℝ) ≤ ((m₀ : ℝ) - 5) * (m₀ : ℝ) := by nlinarith
  nlinarith

theorem isobaricExteriorTwoPoly_ratio_ge {m₀ : ℕ} (h5 : 5 ≤ m₀) :
    (11 / 5 : ℝ) ≤ (((m₀ : ℝ) ^ 2 - (m₀ : ℝ) + 2) / 2) / (m₀ : ℝ) := by
  have hm5 : (5 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast h5
  have hm_pos : (0 : ℝ) < (m₀ : ℝ) := by linarith
  rw [le_div_iff₀ hm_pos]
  have hfac : (0 : ℝ) ≤ (5 * (m₀ : ℝ) - 2) * ((m₀ : ℝ) - 5) := by nlinarith
  linarith

/-- **Scale-space bilinear pole-zero cross-singularity.** Under centered scale multiplication
`(z₁, z₂) ↦ z₁ + z₂ − 1/2`, the boundary pole `z₁ = 1` and any right-half off-critical zero
`z₂ = 1/2 + a + iγ` (`a > 0`) cross-couple to `1 + a + iγ` with `Re > 1`, placing a singularity
strictly inside the convergence half-plane `{s : Re s > 1}`. -/
theorem centeredScaleCross_re_gt_one {a : ℝ} (ha : 0 < a) (γ : ℝ) :
    1 < ((1 : ℂ) + (1 / 2 + (a : ℂ) + (γ : ℂ) * I) - 1 / 2).re := by
  have h : (1 : ℂ) + (1 / 2 + (a : ℂ) + (γ : ℂ) * I) - 1 / 2 =
      ((1 + a : ℝ) : ℂ) + (γ : ℂ) * I := by push_cast; ring
  rw [h]
  simp [ha]

/-! ### 2. Reusable Laplace, product, and Hadamard zero-order machinery -/

private theorem re_one_div_laplace_cos_aux (a b : ℝ) (ha : 0 < a) :
    (1 / ((a : ℂ) + (b : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.cos (b * t) := by
  set w : ℂ := -((a : ℂ) + (b : ℂ) * I)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hint_c : IntegrableOn (fun t : ℝ => Complex.exp (w * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hw_re 0
  have hval := integral_exp_mul_complex_Ioi hw_re 0
  have hrhs_eq : -Complex.exp (w * (0 : ℝ)) / w = 1 / ((a : ℂ) + (b : ℂ) * I) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [w]
    rw [div_neg, neg_div, neg_neg]
  rw [hrhs_eq] at hval
  have hre_int : (∫ t : ℝ in Ioi 0, Complex.exp (w * t)).re =
      ∫ t : ℝ in Ioi 0, (Complex.exp (w * t)).re :=
    (Complex.reCLM.integral_comp_comm hint_c).symm
  rw [← hval, hre_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw_t_re : (w * (t : ℂ)).re = -a * t := by simp [w]
  have hw_t_im : (w * (t : ℂ)).im = -(b * t) := by simp [w]
  rw [Complex.exp_re, hw_t_re, hw_t_im, Real.cos_neg]

private theorem integrableOn_exp_cos_Ioi_aux (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.cos (b * t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0)
    ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem isEvenPosDef_laplace_cos_aux {w φ : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hw_cont : Continuous w)
    (hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ w t)
    (hw_le : ∀ t : ℝ, 0 < t → w t ≤ C * Real.exp (-a * t))
    (hφ : ∀ u : ℝ, φ u = ∫ t : ℝ in Ioi 0, w t * Real.cos (t * u)) :
    IsEvenPosDef φ := by
  have hint_dom : IntegrableOn (fun t : ℝ => C * Real.exp (-a * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0).const_mul C
  have hint_ker : ∀ u : ℝ,
      IntegrableOn (fun t : ℝ => w t * Real.cos (t * u)) (Ioi 0) := by
    intro u
    refine Integrable.mono' hint_dom
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nn t ht)]
    exact (mul_le_of_le_one_right (hw_nn t ht) (Real.abs_cos_le_one _)).trans (hw_le t ht)
  refine ⟨fun u => ?_, fun n x c => ?_⟩
  · rw [hφ (-u), hφ u]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_neg, Real.cos_neg]
  · have hsum_int : ∑ i, ∑ j, c i * c j * φ (x i - x j) =
        ∫ t : ℝ in Ioi 0, w t * ∑ i, ∑ j, c i * c j * Real.cos (t * (x i - x j)) := by
      simp_rw [hφ, ← integral_const_mul]
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, ∫ t : ℝ in Ioi 0, c i * c j * (w t * Real.cos (t * (x i - x j))) =
          ∫ t : ℝ in Ioi 0, ∑ j : Fin n, c i * c j * (w t * Real.cos (t * (x i - x j))) :=
        fun i => (integral_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)).symm
      simp_rw [h1]
      rw [← integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    refine mul_nonneg (hw_nn t ht) ?_
    rw [gram_cos_eq]
    positivity

private theorem isEvenPosDef_add_aux {φ ψ : ℝ → ℝ}
    (hφ : IsEvenPosDef φ) (hψ : IsEvenPosDef ψ) :
    IsEvenPosDef (fun u => φ u + ψ u) where
  even u := by rw [hφ.even, hψ.even]
  posDef n x c := by
    have h : (∑ i, ∑ j, c i * c j * (φ (x i - x j) + ψ (x i - x j))) =
        (∑ i, ∑ j, c i * c j * φ (x i - x j)) + ∑ i, ∑ j, c i * c j * ψ (x i - x j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h]
    exact add_nonneg (hφ.posDef n x c) (hψ.posDef n x c)

private theorem isEvenPosDef_nsmul_aux (n : ℕ) {φ : ℝ → ℝ} (hφ : IsEvenPosDef φ) :
    IsEvenPosDef (fun u => (n : ℝ) * φ u) := by
  induction n with
  | zero =>
      refine ⟨fun _ => by simp, fun m x c => ?_⟩
      simp
  | succ n ih =>
      have heq : (fun u => ((n + 1 : ℕ) : ℝ) * φ u) = fun u => (n : ℝ) * φ u + φ u := by
        funext u; push_cast; ring
      rw [heq]
      exact isEvenPosDef_add_aux ih hφ

private theorem sq_add_sq_eq_mul_I_aux (w : ℂ) (x γ : ℝ) :
    (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
      (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by
  calc (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2
      = (w - (x : ℂ)) ^ 2 - ((γ : ℂ) * I) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    _ = (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by ring

/-- **Unified Hadamard zero-pair lower bound at `s = 2` (central, real off-central, and critical
ordinate contributions).** For any entire order-one function `Λ` satisfying `Λ(1 − s) = Λ(s)`,
`Λ(s̄) = conj(Λ(s))`, `Λ(2) ≠ 0`, and having all zeros in `0 ≤ Re ρ ≤ 1`, every finite set
`X ⊂ (1/2, 1]` and every finite set `Γ ⊂ (0, ∞)` satisfy
`(2/3) ord_{1/2}(Λ) + (4/3) ∑_{x ∈ X} ord_x(Λ) + ∑_{γ ∈ Γ} (12 / (9 + 4γ²)) ord_{1/2 + iγ}(Λ) ≤ Re(Λ'/Λ(2))`. -/
theorem re_logDeriv_two_ge_of_entire_sym {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ) (hoΛ : OrderOneEnvelope Λ)
    (hsym : ∀ s : ℂ, Λ (1 - s) = Λ s)
    (hconj : ∀ s : ℂ, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s))
    (h2 : Λ 2 ≠ 0)
    (hstrip : ∀ ρ : ℂ, Λ ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1)
    (X : Finset ℝ) (hX : ∀ x ∈ X, 1 / 2 < x ∧ x ≤ 1)
    (Γ : Finset ℝ) (hΓ : ∀ γ ∈ Γ, 0 < γ) :
    (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
      (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) +
      (∑ γ ∈ Γ, (12 / (9 + 4 * γ ^ 2)) *
        ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ)) ≤
      (logDeriv Λ 2).re := by
  open GaloisForLFunctions.EntireZeroDivisor RHTower RHTower.CompletionZeroPairs
    RHTower.WeilLineIntegral in
  classical
  have hanΛ : AnalyticOnNhd ℂ Λ univ := hΛ.differentiableOn.analyticOnNhd isOpen_univ
  have hntop : ∀ w : ℂ, analyticOrderAt Λ w ≠ ⊤ := fun w =>
    hanΛ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ 2) (mem_univ w)
      (by rw [(hanΛ 2 (mem_univ 2)).analyticOrderAt_eq_zero.mpr h2]; exact ENat.zero_ne_top)
  have hord_sym : ∀ w : ℂ, analyticOrderAt Λ (1 - w) = analyticOrderAt Λ w := fun w => by
    have h := RHTower.analyticOrderAt_comp_one_sub hΛ w
    rwa [show (fun z => Λ (1 - z)) = Λ from funext hsym] at h
  have hord_conj : ∀ w : ℂ, analyticOrderAt Λ (starRingEnd ℂ w) = analyticOrderAt Λ w := fun w =>
    RHTower.analyticOrderAt_conj_of_conjEquivariant hconj
      (hanΛ w (mem_univ w)) (hanΛ (starRingEnd ℂ w) (mem_univ _))
  set f : ℂ → ℂ := fun z => Λ (z + 2) with hfdef
  have hfd : Differentiable ℂ f := hΛ.comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨C, hC, hgrow⟩ := hoΛ
  have hsum_c : HasSum (fun q : ZeroCopy f =>
      (1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2) (logDeriv Λ 2) :=
    hasSum_logDeriv_zeroPairs hΛ one_ne_zero
      (fun w => by rw [hsym w, one_mul]) hC.le
      (fun w => by simpa only [orderOneWeight] using hgrow w) h2 h2
  set term : ZeroCopy f → ℝ := fun q => ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re
  have hsum_re : HasSum term (logDeriv Λ 2).re := hsum_c.mapL Complex.reCLM
  have hterm_nn : ∀ q : ZeroCopy f, 0 ≤ term q := by
    intro q
    have hzq0 : Λ (zeroCopyPoint f q + 2) = 0 := by simpa [hfdef] using apply_zeroCopyPoint hf q
    obtain ⟨h0, h1⟩ := hstrip _ hzq0
    simp only [term, gPair]
    have ha : 0 ≤ (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      exact div_nonneg (by rw [h2re]; linarith) (Complex.normSq_nonneg _)
    have hb : 0 ≤ (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      have h1re : (1 : ℂ).re = 1 := by norm_num
      exact div_nonneg (by rw [h2re, h1re]; linarith) (Complex.normSq_nonneg _)
    have he : ((1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
        1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2))))).re =
        ((1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re +
          (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re) / 2 := by
      have : (1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
          1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) =
          (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
            1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) / 2 := by ring
      rw [this, Complex.div_ofNat_re, Complex.add_re]
    linarith
  have hdiv_toNat : ∀ w : ℂ,
      ((MeromorphicOn.divisor f univ) (w - 2)).toNat = (analyticOrderAt Λ w).toNat := by
    intro w
    have hg_an : AnalyticAt ℂ (fun z : ℂ => z + 2) (w - 2) := by fun_prop
    have hg_d : deriv (fun z : ℂ => z + 2) (w - 2) ≠ 0 := by
      rw [((hasDerivAt_id' (w - 2)).add_const 2).deriv]; exact one_ne_zero
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := Λ) hg_an hg_d
    have hfeq : Λ ∘ (fun z : ℂ => z + 2) = f := rfl
    rw [hfeq, sub_add_cancel] at hcomp
    rw [divisor_univ_eq_analyticOrder hf, hcomp]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hntop w)
    rw [← hn]; simp
  let cAt : ℂ → Finset (ZeroCopy f) := fun w =>
    if hw : w - 2 ∈ (MeromorphicOn.divisor f univ).support then
      Finset.univ.map ⟨fun j : Fin ((MeromorphicOn.divisor f univ) (w - 2)).toNat =>
        ⟨⟨w - 2, hw⟩, j⟩, fun j₁ j₂ heq => by
          simp only [Sigma.mk.injEq, heq_eq_eq] at heq; exact heq.2⟩
    else ∅
  have hc_pt : ∀ w : ℂ, ∀ q ∈ cAt w, zeroCopyPoint f q + 2 = w := by
    intro w q hq
    dsimp only [cAt] at hq
    split_ifs at hq with hw
    · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hq
      change (w - 2) + 2 = w; ring
    · exact absurd hq (Finset.notMem_empty _)
  have hc_card : ∀ w : ℂ, (cAt w).card = (analyticOrderAt Λ w).toNat := by
    intro w
    dsimp only [cAt]
    split_ifs with hw
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hdiv_toNat]
    · symm; rw [← hdiv_toNat]
      by_contra hne
      have hpos : 0 < ((MeromorphicOn.divisor f univ) (w - 2)).toNat := Nat.pos_of_ne_zero hne
      apply hw; rw [Function.mem_support]; intro hz0; rw [hz0] at hpos; simp at hpos
  have hc_disj : ∀ w₁ w₂ : ℂ, w₁ ≠ w₂ → Disjoint (cAt w₁) (cAt w₂) := by
    intro w₁ w₂ hne; rw [Finset.disjoint_left]; intro q h1 h2
    exact hne ((hc_pt w₁ q h1).symm.trans (hc_pt w₂ q h2))
  let pairCopies : ℝ → Finset (ZeroCopy f) := fun x =>
    cAt (x : ℂ) ∪ cAt (1 - (x : ℂ))
  let critCopies : ℝ → Finset (ZeroCopy f) := fun γ =>
    cAt (1 / 2 + (γ : ℂ) * I) ∪ cAt (1 / 2 - (γ : ℂ) * I)
  have hhalf_disj_pair : ∀ x ∈ X, Disjoint (cAt (1 / 2 : ℂ)) (pairCopies x) := by
    intro x hx
    obtain ⟨hx_gt, _⟩ := hX x hx
    rw [Finset.disjoint_union_right]
    refine ⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hhalf_disj_crit : ∀ γ ∈ Γ, Disjoint (cAt (1 / 2 : ℂ)) (critCopies γ) := by
    intro γ hγm
    have hγ0 := hΓ γ hγm
    rw [Finset.disjoint_union_right]
    refine ⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩
    · have := congrArg Complex.im h; simp at this; linarith
    · have := congrArg Complex.im h; simp at this; linarith
  have hpair_disj_crit : ∀ x ∈ X, ∀ γ ∈ Γ, Disjoint (pairCopies x) (critCopies γ) := by
    intro x hx γ _
    obtain ⟨hx_gt, _⟩ := hX x hx
    simp only [pairCopies, critCopies, Finset.disjoint_union_left, Finset.disjoint_union_right]
    refine ⟨⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩,
            ⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩⟩ <;>
    · have := congrArg Complex.re h; simp at this; linarith
  have hpair_disj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (pairCopies x) (pairCopies y) := by
    intro x hx y hy hxy
    obtain ⟨hx_gt, _⟩ := hX x hx
    obtain ⟨hy_gt, _⟩ := hX y hy
    simp only [pairCopies, Finset.disjoint_union_left, Finset.disjoint_union_right]
    refine ⟨⟨hc_disj _ _ (fun h => hxy (Complex.ofReal_inj.mp h)), hc_disj _ _ (fun h => ?_)⟩,
            ⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩⟩
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · apply hxy; have := congrArg Complex.re h; simp at this; linarith
  have hcrit_disj : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → Disjoint (critCopies γ₁) (critCopies γ₂) := by
    intro γ₁ hγ₁ γ₂ hγ₂ hne
    have h1 := hΓ γ₁ hγ₁
    have h2' := hΓ γ₂ hγ₂
    simp only [critCopies, Finset.disjoint_union_left, Finset.disjoint_union_right]
    refine ⟨⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩,
            ⟨hc_disj _ _ (fun h => ?_), hc_disj _ _ (fun h => ?_)⟩⟩ <;>
    · have := congrArg Complex.im h; simp at this; exact hne (by linarith)
  have hsum_half : ((2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ)) ≤
      ∑ q ∈ cAt (1 / 2 : ℂ), term q := by
    have hpt_val : ∀ q ∈ cAt (1 / 2 : ℂ), term q = 2 / 3 := by
      intro q hq
      rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl, hc_pt _ q hq]
      unfold gPair; norm_num
    rw [Finset.sum_congr rfl hpt_val, Finset.sum_const, hc_card, nsmul_eq_mul, mul_comm]
  have hsum_pair : ∀ x ∈ X,
      (4 / 3 : ℝ) * ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) ≤ ∑ q ∈ pairCopies x, term q := by
    intro x hx
    obtain ⟨hx_gt, _⟩ := hX x hx
    have hne_x : (x : ℂ) ≠ 1 - (x : ℂ) := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    dsimp only [pairCopies]
    rw [Finset.sum_union (hc_disj _ _ hne_x)]
    have hval1 : ∀ q ∈ cAt (x : ℂ), term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
      intro q hq
      rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl, hc_pt _ q hq]
      unfold gPair
      have e1 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
      have e2 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
      have ec : (1 / 2 : ℂ) * (1 / (((2 - x : ℝ) : ℂ)) + 1 / (((1 + x : ℝ) : ℂ))) =
          ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
      rw [e1, e2, ec, Complex.ofReal_re]
    have hval2 : ∀ q ∈ cAt (1 - (x : ℂ)), term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
      intro q hq
      rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl, hc_pt _ q hq]
      unfold gPair; rw [sub_sub_cancel]
      have e1 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
      have e2 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
      have ec : (1 / 2 : ℂ) * (1 / (((1 + x : ℝ) : ℂ)) + 1 / (((2 - x : ℝ) : ℂ))) =
          ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
      rw [e1, e2, ec, Complex.ofReal_re]
    rw [Finset.sum_congr rfl hval1, Finset.sum_congr rfl hval2,
        Finset.sum_const, Finset.sum_const, hc_card, hc_card, hord_sym (x : ℂ), nsmul_eq_mul]
    have hge43 : (4 / 3 : ℝ) ≤ 1 / (2 - x) + 1 / (1 + x) := by
      have hp1 : 0 < 2 - x := by linarith
      have hp2 : 0 < 1 + x := by linarith
      rw [div_add_div _ _ hp1.ne' hp2.ne', div_le_div_iff₀ (by norm_num) (mul_pos hp1 hp2)]
      nlinarith [sq_nonneg (x - 1 / 2)]
    have hord_nn : (0 : ℝ) ≤ ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsum_crit : ∀ γ ∈ Γ,
      (12 / (9 + 4 * γ ^ 2)) * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) =
        ∑ q ∈ critCopies γ, term q := by
    intro γ hγm
    have hγ0 := hΓ γ hγm
    have hne_c : (1 / 2 + (γ : ℂ) * I) ≠ (1 / 2 - (γ : ℂ) * I) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    dsimp only [critCopies]
    rw [Finset.sum_union (hc_disj _ _ hne_c)]
    have hre_inv_p : (1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I))).re = 6 / (9 + 4 * γ ^ 2) := by
      have he : (2 : ℂ) - (1 / 2 + (γ : ℂ) * I) = ((3 / 2 : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [he, one_div, Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_zero, add_zero, zero_add, sub_zero, mul_one]
      rw [neg_mul_neg]
      have hden_eq : (3 / 2 : ℝ) * (3 / 2) + γ * γ = (9 + 4 * γ ^ 2) / 4 := by ring
      rw [hden_eq]
      have hden : (9 + 4 * γ ^ 2 : ℝ) ≠ 0 := by positivity
      field_simp [hden]; ring
    have hre_inv_m : (1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I))).re = 6 / (9 + 4 * γ ^ 2) := by
      have he : (2 : ℂ) - (1 / 2 - (γ : ℂ) * I) = ((3 / 2 : ℝ) : ℂ) + (γ : ℂ) * I := by
        push_cast; ring
      rw [he, one_div, Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hden : (3 / 2) * (3 / 2) + γ * γ ≠ 0 := by positivity
      field_simp [hden]; ring
    have hval_p : ∀ q ∈ cAt (1 / 2 + (γ : ℂ) * I), term q = 6 / (9 + 4 * γ ^ 2) := by
      intro q hq
      rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl, hc_pt _ q hq]
      unfold gPair
      have hs1 : (1 : ℂ) - (1 / 2 + (γ : ℂ) * I) = 1 / 2 - (γ : ℂ) * I := by ring
      rw [hs1]
      have hmul : ((1 / 2 : ℂ) * (1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I)) +
          1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I)))).re =
          ((1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I))).re +
            (1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I))).re) / 2 := by
        have : (1 / 2 : ℂ) * (1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I)) +
            1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I))) =
            (1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I)) +
              1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I))) / 2 := by ring
        rw [this, Complex.div_ofNat_re, Complex.add_re]
      rw [hmul, hre_inv_p, hre_inv_m]; ring
    have hval_m : ∀ q ∈ cAt (1 / 2 - (γ : ℂ) * I), term q = 6 / (9 + 4 * γ ^ 2) := by
      intro q hq
      rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl, hc_pt _ q hq]
      unfold gPair
      have hs1 : (1 : ℂ) - (1 / 2 - (γ : ℂ) * I) = 1 / 2 + (γ : ℂ) * I := by ring
      rw [hs1]
      have hmul : ((1 / 2 : ℂ) * (1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I)) +
          1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I)))).re =
          ((1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I))).re +
            (1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I))).re) / 2 := by
        have : (1 / 2 : ℂ) * (1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I)) +
            1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I))) =
            (1 / ((2 : ℂ) - (1 / 2 - (γ : ℂ) * I)) +
              1 / ((2 : ℂ) - (1 / 2 + (γ : ℂ) * I))) / 2 := by ring
        rw [this, Complex.div_ofNat_re, Complex.add_re]
      rw [hmul, hre_inv_p, hre_inv_m]; ring
    have hconj_c : (1 / 2 : ℂ) - (γ : ℂ) * I = starRingEnd ℂ (1 / 2 + (γ : ℂ) * I) := by
      simp [map_ofNat]; ring
    rw [Finset.sum_congr rfl hval_p, Finset.sum_congr rfl hval_m,
        Finset.sum_const, Finset.sum_const, hc_card, hc_card, hconj_c, hord_conj,
        nsmul_eq_mul]
    ring
  set S_tot : Finset (ZeroCopy f) :=
    (cAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies) ∪ Γ.biUnion critCopies
  have hd1 : Disjoint (cAt (1 / 2 : ℂ)) (X.biUnion pairCopies) := by
    rw [Finset.disjoint_biUnion_right]
    exact hhalf_disj_pair
  have hd2 : Disjoint (cAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies) (Γ.biUnion critCopies) := by
    rw [Finset.disjoint_union_left]
    refine ⟨by rw [Finset.disjoint_biUnion_right]; exact hhalf_disj_crit, ?_⟩
    rw [Finset.disjoint_biUnion_left]
    intro x hx
    rw [Finset.disjoint_biUnion_right]
    exact fun γ hγm => hpair_disj_crit x hx γ hγm
  have hsum_Stot : ∑ q ∈ S_tot, term q =
      (∑ q ∈ cAt (1 / 2 : ℂ), term q) +
      (∑ x ∈ X, ∑ q ∈ pairCopies x, term q) +
      (∑ γ ∈ Γ, ∑ q ∈ critCopies γ, term q) := by
    dsimp [S_tot]
    rw [Finset.sum_union hd2, Finset.sum_union hd1,
        Finset.sum_biUnion (fun x hx y hy hxy => hpair_disj x hx y hy hxy),
        Finset.sum_biUnion (fun γ₁ h₁ γ₂ h₂ hne => hcrit_disj γ₁ h₁ γ₂ h₂ hne)]
  have hX_le : (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) ≤
      ∑ x ∈ X, ∑ q ∈ pairCopies x, term q := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun x hx => hsum_pair x hx
  have hΓ_eq : (∑ γ ∈ Γ, (12 / (9 + 4 * γ ^ 2)) *
      ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ)) =
      ∑ γ ∈ Γ, ∑ q ∈ critCopies γ, term q :=
    Finset.sum_congr rfl fun γ hγm => hsum_crit γ hγm
  have htot_le : ∑ q ∈ S_tot, term q ≤ (logDeriv Λ 2).re :=
    sum_le_hasSum S_tot (fun q _ => hterm_nn q) hsum_re
  linarith [hsum_half, hX_le, hΓ_eq, hsum_Stot, htot_le]

/-! ### 3. Exact boundary-twist absorption to `κ_γ = 0`, capacity floor, and ordinate pole decay -/

theorem shiftedPolePoly_eq_boundaryTwistPoly (γ : ℝ) (s : ℂ) :
    shiftedPolePoly γ s = boundaryTwistPoly γ s := by
  unfold shiftedPolePoly boundaryTwistPoly
  ring

private theorem boundaryTwistFactor_ne_zero_of_one_lt_re (γ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    boundaryTwistFactor γ s ≠ 0 := by
  unfold boundaryTwistFactor
  rw [← shiftedPolePoly_eq_boundaryTwistPoly]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hsp : shiftedPolePoly γ s ≠ 0 := by
    unfold shiftedPolePoly
    have h1 := sq_add_sq_eq_mul_I_aux s 0 γ
    simp only [Complex.ofReal_zero, sub_zero, zero_add, zero_sub] at h1
    have h2 := sq_add_sq_eq_mul_I_aux s 1 γ
    simp only [Complex.ofReal_one] at h2
    rw [h1, h2]
    refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
      (mul_ne_zero (fun h => ?_) (fun h => ?_)) <;>
    · have := congrArg Complex.re h; simp at this; linarith
  exact div_ne_zero hsp (pow_ne_zero 2 (mul_ne_zero hs0 hs1))

private theorem differentiableAt_boundaryTwistFactor_of_one_lt_re (γ : ℝ) {s : ℂ}
    (hs : 1 < s.re) : DifferentiableAt ℂ (boundaryTwistFactor γ) s := by
  unfold boundaryTwistFactor
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  exact (by unfold boundaryTwistPoly; fun_prop : DifferentiableAt ℂ (boundaryTwistPoly γ) s).div
    (by fun_prop) (pow_ne_zero 2 (mul_ne_zero hs0 hs1))

/-- **Bochner positivity of `boundaryTwistFactor γ` on `σ > 1`.** Its vertical `−logDeriv` section
has nonnegative Laplace density `2 e^{−σt} (e^t + 1) (1 − cos(γt)) ≥ 0` on `(0, ∞)`. -/
theorem isEvenPosDef_boundaryTwistFactor (γ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef fun u : ℝ =>
      (-logDeriv (boundaryTwistFactor γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
  refine isEvenPosDef_laplace_cos_aux (C := 8) (a := σ - 1) (by linarith) (by fun_prop)
    (w := fun t => 2 * Real.exp (-σ * t) * (Real.exp t + 1) * (1 - Real.cos (γ * t)))
    (fun t _ => by
      have hc : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith))
    (fun t ht => by
      have hc : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
      have h1 : 1 ≤ Real.exp t := Real.one_le_exp ht.le
      have h2 : 1 - Real.cos (γ * t) ≤ 2 := by linarith
      have h3 : Real.exp t + 1 ≤ 2 * Real.exp t := by linarith
      calc 2 * Real.exp (-σ * t) * (Real.exp t + 1) * (1 - Real.cos (γ * t))
          ≤ 2 * Real.exp (-σ * t) * (2 * Real.exp t) * 2 := by
            have ha : 0 ≤ 2 * Real.exp (-σ * t) * (Real.exp t + 1) := by positivity
            have hb : 2 * Real.exp (-σ * t) * (Real.exp t + 1) ≤
                2 * Real.exp (-σ * t) * (2 * Real.exp t) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
            exact (mul_le_mul_of_nonneg_left h2 ha).trans (mul_le_mul_of_nonneg_right hb (by norm_num))
        _ = 8 * (Real.exp (-σ * t) * Real.exp t) := by ring
        _ = 8 * Real.exp (-(σ - 1) * t) := by rw [← Real.exp_add]; congr 2; ring)
    (fun u => ?_)
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hn1 : s - (1 + (γ : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hn2 : s - (1 - (γ : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hn3 : s - (γ : ℂ) * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hn4 : s - (-(γ : ℂ) * I) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hbt_eq : boundaryTwistFactor γ =
      fun z : ℂ => ((z - (1 + (γ : ℂ) * I)) * (z - (1 - (γ : ℂ) * I)) *
        (z - (γ : ℂ) * I) * (z - (-(γ : ℂ) * I))) / (z ^ 2 * (z - 1) ^ 2) := by
    funext z
    unfold boundaryTwistFactor boundaryTwistPoly
    have f1 := sq_add_sq_eq_mul_I_aux z 1 γ
    simp only [Complex.ofReal_one] at f1
    have f2 := sq_add_sq_eq_mul_I_aux z 0 γ
    simp only [Complex.ofReal_zero, sub_zero, zero_add, zero_sub] at f2
    rw [f1, f2, mul_pow]
    congr 1; ring
  have hd_sub : ∀ c : ℂ, DifferentiableAt ℂ (fun z : ℂ => z - c) s := fun _ => by fun_prop
  have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have hld_num : logDeriv (fun z : ℂ => (z - (1 + (γ : ℂ) * I)) * (z - (1 - (γ : ℂ) * I)) *
      (z - (γ : ℂ) * I) * (z - (-(γ : ℂ) * I))) s =
      1 / (s - (1 + (γ : ℂ) * I)) + 1 / (s - (1 - (γ : ℂ) * I)) +
        1 / (s - (γ : ℂ) * I) + 1 / (s - (-(γ : ℂ) * I)) := by
    rw [logDeriv_mul (f := fun z => (z - (1 + (γ : ℂ) * I)) * (z - (1 - (γ : ℂ) * I)) *
          (z - (γ : ℂ) * I)) (g := fun z => z - (-(γ : ℂ) * I)) s
          (mul_ne_zero (mul_ne_zero hn1 hn2) hn3) hn4
          (((hd_sub _).mul (hd_sub _)).mul (hd_sub _)) (hd_sub _),
        logDeriv_mul (f := fun z => (z - (1 + (γ : ℂ) * I)) * (z - (1 - (γ : ℂ) * I)))
          (g := fun z => z - (γ : ℂ) * I) s (mul_ne_zero hn1 hn2) hn3
          ((hd_sub _).mul (hd_sub _)) (hd_sub _),
        logDeriv_mul (f := fun z => z - (1 + (γ : ℂ) * I))
          (g := fun z => z - (1 - (γ : ℂ) * I)) s hn1 hn2 (hd_sub _) (hd_sub _),
        hd_lin, hd_lin, hd_lin, hd_lin]
  have hld_den : logDeriv (fun z : ℂ => z ^ 2 * (z - 1) ^ 2) s = 2 * (1 / s) + 2 * (1 / (s - 1)) := by
    have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
    rw [logDeriv_mul (f := fun z : ℂ => z ^ 2) (g := fun z : ℂ => (z - 1) ^ 2) s
          (pow_ne_zero 2 hs0) (pow_ne_zero 2 hs1) (hid.fun_pow 2) ((hd_sub 1).fun_pow 2),
        logDeriv_fun_pow hid 2, logDeriv_fun_pow (hd_sub 1) 2, hd_lin 1]
    have h0 : logDeriv (fun z : ℂ => z) s = 1 / s := by rw [logDeriv_apply, deriv_id'', one_div]
    rw [h0]; push_cast; ring
  have hld : -logDeriv (boundaryTwistFactor γ) s =
      (2 * (1 / (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I)) -
        1 / (((σ - 1 : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) -
        1 / (((σ - 1 : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I)) +
      (2 * (1 / ((σ : ℂ) + (u : ℂ) * I)) -
        1 / ((σ : ℂ) + ((u - γ : ℝ) : ℂ) * I) -
        1 / ((σ : ℂ) + ((u + γ : ℝ) : ℂ) * I)) := by
    rw [hbt_eq,
        logDeriv_div
          (f := fun z : ℂ => (z - (1 + (γ : ℂ) * I)) * (z - (1 - (γ : ℂ) * I)) *
            (z - (γ : ℂ) * I) * (z - (-(γ : ℂ) * I)))
          (g := fun z : ℂ => z ^ 2 * (z - 1) ^ 2) s
          (mul_ne_zero (mul_ne_zero (mul_ne_zero hn1 hn2) hn3) hn4)
          (mul_ne_zero (pow_ne_zero 2 hs0) (pow_ne_zero 2 hs1))
          ((((hd_sub _).mul (hd_sub _)).mul (hd_sub _)).mul (hd_sub _))
          ((differentiableAt_id.fun_pow 2).mul ((hd_sub 1).fun_pow 2)),
        hld_num, hld_den]
    have e1 : s - 1 = (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) := by dsimp [s]; push_cast; ring
    have e2 : s - (1 + (γ : ℂ) * I) = (((σ - 1 : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
      dsimp [s]; push_cast; ring
    have e3 : s - (1 - (γ : ℂ) * I) = (((σ - 1 : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
      dsimp [s]; push_cast; ring
    have e4 : s - (γ : ℂ) * I = ((σ : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
      dsimp [s]; push_cast; ring
    have e5 : s - (-(γ : ℂ) * I) = ((σ : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
      dsimp [s]; push_cast; ring
    rw [e1, e2, e3, e4, e5]; dsimp [s]; ring
  change (-logDeriv (boundaryTwistFactor γ) s).re = _
  rw [hld]
  have h2a : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  rw [Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.sub_re, Complex.sub_re, h2a, h2a,
      re_one_div_laplace_cos_aux (σ - 1) u (by linarith),
      re_one_div_laplace_cos_aux (σ - 1) (u - γ) (by linarith),
      re_one_div_laplace_cos_aux (σ - 1) (u + γ) (by linarith),
      re_one_div_laplace_cos_aux σ u (by linarith),
      re_one_div_laplace_cos_aux σ (u - γ) (by linarith),
      re_one_div_laplace_cos_aux σ (u + γ) (by linarith)]
  have i1 := integrableOn_exp_cos_Ioi_aux (σ - 1) u (by linarith)
  have i2 := integrableOn_exp_cos_Ioi_aux (σ - 1) (u - γ) (by linarith)
  have i3 := integrableOn_exp_cos_Ioi_aux (σ - 1) (u + γ) (by linarith)
  have i4 := integrableOn_exp_cos_Ioi_aux σ u (by linarith)
  have i5 := integrableOn_exp_cos_Ioi_aux σ (u - γ) (by linarith)
  have i6 := integrableOn_exp_cos_Ioi_aux σ (u + γ) (by linarith)
  have j1 := integral_sub (i1.const_mul 2) i2
  have j2 := integral_sub ((i1.const_mul 2).sub i2) i3
  dsimp only [Pi.sub_apply] at j2
  have j3 := integral_sub (i4.const_mul 2) i5
  have j4 := integral_sub ((i4.const_mul 2).sub i5) i6
  dsimp only [Pi.sub_apply] at j4
  have j_all := integral_add (((i1.const_mul 2).sub i2).sub i3) (((i4.const_mul 2).sub i5).sub i6)
  dsimp only [Pi.sub_apply] at j_all
  rw [← integral_const_mul, ← integral_const_mul, ← j1, ← j2, ← j3, ← j4, ← j_all]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hexp : Real.exp (-(σ - 1) * t) = Real.exp (-σ * t) * Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have hc1 : Real.cos ((u - γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) + Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u - γ) * t = t * u - γ * t by ring, Real.cos_sub]
  have hc2 : Real.cos ((u + γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) - Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u + γ) * t = t * u + γ * t by ring, Real.cos_add]
  rw [hexp, hc1, hc2, mul_comm u t]
  ring

/-- **Unconditional absorption of shifted boundary poles (`κ_γ ↦ 0`) on `HeightCoupledSystem`.**
Multiplying `F` by `boundaryTwistFactor γ ^ κγ` eliminates all shifted boundary poles at
`{±iγ, 1 ± iγ}` (`κ_γ = 0`) while preserving `IsEvenPosDef` on `σ > 1` and keeping the exact same
entire completion `Λ`, trading `κ_γ` shifted pole quartets for `2 κ_γ` central pole pairs
(`κ₀ ↦ κ₀ + 2 κ_γ`, yielding `4 κ` on `CompletedPositiveSystem.heightCouple`). -/
theorem HeightCoupledSystem.absorbShiftedPoles {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) :
    HeightCoupledSystem (κ₀ + 2 * κγ) 0 d γ
      (fun s => F s * boundaryTwistFactor γ s ^ κγ) Λ where
  degree_pos := hHC.degree_pos
  diffOn_F := hHC.diffOn_F.mul
    ((show DifferentiableOn ℂ (boundaryTwistFactor γ) {s : ℂ | 1 < s.re} from
      fun s hs => (differentiableAt_boundaryTwistFactor_of_one_lt_re γ hs).differentiableWithinAt).pow κγ)
  ne_zero_F := fun s hs =>
    mul_ne_zero (hHC.ne_zero_F s hs) (pow_ne_zero κγ (boundaryTwistFactor_ne_zero_of_one_lt_re γ hs))
  posDef_neg_logDeriv := fun {σ} hσ => by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : (fun u : ℝ =>
        (-logDeriv (fun s => F s * boundaryTwistFactor γ s ^ κγ)
          ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
          (κγ : ℝ) * (-logDeriv (boundaryTwistFactor γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I
      have hs : 1 < s.re := by simp [s]; exact hσ
      have hFd : DifferentiableAt ℂ F s := (hHC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs)
      have htd : DifferentiableAt ℂ (boundaryTwistFactor γ) s :=
        differentiableAt_boundaryTwistFactor_of_one_lt_re γ hs
      rw [logDeriv_mul (f := F) (g := fun z => boundaryTwistFactor γ z ^ κγ) s
            (hHC.ne_zero_F s hs)
            (pow_ne_zero κγ (boundaryTwistFactor_ne_zero_of_one_lt_re γ hs))
            hFd (htd.fun_pow κγ),
          logDeriv_fun_pow htd κγ, neg_add, Complex.add_re]
      congr 1
      have : -((κγ : ℂ) * logDeriv (boundaryTwistFactor γ) s) =
          ((κγ : ℝ) : ℂ) * (-logDeriv (boundaryTwistFactor γ) s) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
    rw [heq]
    exact isEvenPosDef_add_aux (hHC.posDef_neg_logDeriv hσ)
      (isEvenPosDef_nsmul_aux κγ (isEvenPosDef_boundaryTwistFactor γ hσ))
  entire_Λ := hHC.entire_Λ
  orderOne_Λ := hHC.orderOne_Λ
  sym_Λ := hHC.sym_Λ
  conj_Λ := hHC.conj_Λ
  completed_eq := fun s hs => by
    have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    have hden : (s * (s - 1)) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hs0 hs1)
    have hmul : (s * (s - 1)) ^ 2 * boundaryTwistFactor γ s = shiftedPolePoly γ s := by
      unfold boundaryTwistFactor
      rw [mul_div_cancel₀ _ hden, shiftedPolePoly_eq_boundaryTwistPoly]
    have hpow : (s * (s - 1)) ^ (2 * κγ) * boundaryTwistFactor γ s ^ κγ =
        shiftedPolePoly γ s ^ κγ := by
      rw [pow_mul, ← mul_pow, hmul]
    rw [hHC.completed_eq s hs, pow_zero, mul_one, pow_add]
    calc (s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s * F s
        = (s * (s - 1)) ^ κ₀ * ((s * (s - 1)) ^ (2 * κγ) * boundaryTwistFactor γ s ^ κγ) *
            coupledGamma γ d s * F s := by rw [hpow]
      _ = (s * (s - 1)) ^ κ₀ * (s * (s - 1)) ^ (2 * κγ) * coupledGamma γ d s *
            (F s * boundaryTwistFactor γ s ^ κγ) := by ring

/-- **Sharp origin-capacity floor for additive pole-cancelling boundary divisors (`2 m ≤ D(0)`).**
Any `IsEvenPosDef` boundary divisor `D` with no off-origin poles (`∀ u ≠ 0, D(u) ≤ 0`) that cancels
poles of weight `m` at height `±γ` (`γ ≠ 0`, `D(γ) ≤ −m`) must add at least `2 m` to the origin
pole order `D(0)`, proving `Δκ₀ = 2 κ_γ` (`4 κ` on `heightCouple`) is strictly minimal among
additive positive-definite pole-cancelling twists. -/
theorem two_mul_le_origin_of_poleCancelling_posDef {D : ℝ → ℝ}
    (hD : IsEvenPosDef D) (hnp : ∀ u : ℝ, u ≠ 0 → D u ≤ 0)
    {γ m : ℝ} (hγ : γ ≠ 0) (hm : D γ ≤ -m) :
    2 * m ≤ D 0 := by
  have hpos : 0 < |γ| := abs_pos.mpr hγ
  have hDabs : D |γ| = D γ := by
    rcases le_or_gt 0 γ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, hD.even]
  have hmass := total_zero_mass_le hD hnp (Z := {|γ|}) (by simpa using hpos)
  rw [Finset.sum_singleton, hDabs] at hmass
  linarith

/-- **Exact ordinate-dependent logarithmic derivative of `shiftedPolePoly γ` at `s = 2`.** -/
theorem re_logDeriv_shiftedPolePoly_two_eq (γ : ℝ) :
    (logDeriv (shiftedPolePoly γ) 2).re = 4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2) := by
  let p₁ : ℂ → ℂ := fun w => w ^ 2 + (γ : ℂ) ^ 2
  let p₂ : ℂ → ℂ := fun w => (w - 1) ^ 2 + (γ : ℂ) ^ 2
  have hp₁_val : p₁ 2 = ((4 + γ ^ 2 : ℝ) : ℂ) := by dsimp [p₁]; push_cast; ring
  have hp₂_val : p₂ 2 = ((1 + γ ^ 2 : ℝ) : ℂ) := by dsimp [p₂]; push_cast; ring
  have hp₁_pos : 0 < 4 + γ ^ 2 := by positivity
  have hp₂_pos : 0 < 1 + γ ^ 2 := by positivity
  have hp₁_nz : p₁ 2 ≠ 0 := by rw [hp₁_val]; exact Complex.ofReal_ne_zero.mpr hp₁_pos.ne'
  have hp₂_nz : p₂ 2 ≠ 0 := by rw [hp₂_val]; exact Complex.ofReal_ne_zero.mpr hp₂_pos.ne'
  have hd₁ : HasDerivAt p₁ 4 2 :=
    (((hasDerivAt_id (2 : ℂ)).pow 2).add_const ((γ : ℂ) ^ 2)).congr_deriv (by norm_num)
  have hd₂ : HasDerivAt p₂ 2 2 :=
    ((((hasDerivAt_id (2 : ℂ)).sub_const 1).pow 2).add_const ((γ : ℂ) ^ 2)).congr_deriv
      (by norm_num)
  have hsp : shiftedPolePoly γ = fun z => p₁ z * p₂ z := rfl
  rw [hsp, logDeriv_mul (f := p₁) (g := p₂) 2 hp₁_nz hp₂_nz hd₁.differentiableAt hd₂.differentiableAt,
      logDeriv_apply, logDeriv_apply, hd₁.deriv, hd₂.deriv, hp₁_val, hp₂_val]
  have hc : (4 : ℂ) / ((4 + γ ^ 2 : ℝ) : ℂ) + (2 : ℂ) / ((1 + γ ^ 2 : ℝ) : ℂ) =
      (((4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, Complex.ofReal_re]

/-- **Exact positive Hadamard penalty of twisting out shifted poles at `s = 2`.** Absorbing
`shiftedPolePoly γ` into `(s(s − 1))²` via `boundaryTwistFactor γ` strictly increases the pole
cost at `s = 2` by `3 γ² (γ² + 3) / ((4 + γ²)(1 + γ²)) > 0` for every `γ ≠ 0`. -/
theorem re_neg_logDeriv_boundaryTwistFactor_two_eq (γ : ℝ) :
    (-logDeriv (boundaryTwistFactor γ) 2).re =
      3 * γ ^ 2 * (γ ^ 2 + 3) / ((4 + γ ^ 2) * (1 + γ ^ 2)) := by
  have hsp_nz : boundaryTwistPoly γ 2 ≠ 0 := by
    rw [← shiftedPolePoly_eq_boundaryTwistPoly]
    unfold shiftedPolePoly
    have h1 : ((2 : ℂ) ^ 2 + (γ : ℂ) ^ 2) = ((4 + γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : (((2 : ℂ) - 1) ^ 2 + (γ : ℂ) ^ 2) = ((1 + γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
      (Complex.ofReal_ne_zero.mpr (by positivity))
  have hden_nz : ((2 : ℂ) * ((2 : ℂ) - 1)) ^ 2 ≠ 0 := by norm_num
  have hbt : boundaryTwistFactor γ = fun s => shiftedPolePoly γ s / (s * (s - 1)) ^ 2 := by
    funext s; unfold boundaryTwistFactor; rw [shiftedPolePoly_eq_boundaryTwistPoly]
  have hqd : DifferentiableAt ℂ (fun s : ℂ => s * (s - 1)) 2 := by fun_prop
  have hq_ld : logDeriv (fun s : ℂ => (s * (s - 1)) ^ 2) 2 = 3 := by
    rw [logDeriv_fun_pow hqd 2,
        logDeriv_mul (f := fun s : ℂ => s) (g := fun s : ℂ => s - 1) 2
          (by norm_num) (by norm_num) differentiableAt_id (by fun_prop),
        logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'']
    norm_num
  rw [hbt,
      logDeriv_div (f := shiftedPolePoly γ) (g := fun s => (s * (s - 1)) ^ 2) 2
        (by rwa [shiftedPolePoly_eq_boundaryTwistPoly]) hden_nz
        (by unfold shiftedPolePoly; fun_prop) (hqd.fun_pow 2),
      hq_ld, neg_sub, Complex.sub_re, re_logDeriv_shiftedPolePoly_two_eq]
  have h3re : (3 : ℂ).re = 3 := by norm_num
  rw [h3re]
  have hp1 : (4 + γ ^ 2 : ℝ) ≠ 0 := by positivity
  have hp2 : (1 + γ ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hp1, hp2]
  ring

/-- **Exact ordinate-decaying archimedean budget for `HeightCoupledSystem`.** Retaining the exact
ordinate evaluation `4/(4 + γ²) + 2/(1 + γ²)` instead of the `γ = 0` worst case `3` strengthens
`HeightCoupledSystem.archimedean_budget` across every height `γ ∈ ℝ`. -/
theorem HeightCoupledSystem.archimedean_budget_exact {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 1 / 2 < x ∧ x ≤ 1) :
    (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
      (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) <
    (3 / 2 : ℝ) * (κ₀ : ℝ) + (4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2)) * (κγ : ℝ) +
      (d : ℝ) * Real.log (3 + |γ|) - (7 / 6 : ℝ) * (d : ℝ) := by
  have hpos2 : 0 ≤ (-logDeriv F (2 : ℂ)).re := by
    have hpd := (hHC.posDef_neg_logDeriv (σ := 2) (by norm_num)).posDef 1 (fun _ => 0) (fun _ => 1)
    simpa using hpd
  have hdecomp := congrArg Complex.re (hHC.neg_logDeriv_F_eq (s := 2) (by norm_num))
  have hre2 : ((κ₀ : ℂ) * (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)) +
      (κγ : ℂ) * logDeriv (shiftedPolePoly γ) 2 +
      (2 * d : ℕ) * logDeriv Complex.Gammaℝ 2 +
      (d : ℂ) * (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I) +
        logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)) - logDeriv Λ 2).re =
      (3 / 2 : ℝ) * (κ₀ : ℝ) + (4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2)) * (κγ : ℝ) +
      2 * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re +
      (d : ℝ) * ((logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
        (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re) - (logDeriv Λ 2).re := by
    rw [Complex.sub_re, Complex.add_re, Complex.add_re, Complex.add_re,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        Complex.add_re, Complex.add_re, Nat.cast_mul, Nat.cast_ofNat,
        re_logDeriv_shiftedPolePoly_two_eq]
    have hp1 : (1 / (2 : ℂ)).re = 1 / 2 := by norm_num
    have hp2 : (1 / ((2 : ℂ) - 1)).re = 1 := by norm_num
    rw [hp1, hp2]; ring
  rw [hre2] at hdecomp
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hHC.degree_pos
  have hd_central : 2 * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re < -(5 / 3 : ℝ) * (d : ℝ) := by
    have := mul_lt_mul_of_pos_left re_logDeriv_Gammaℝ_two_lt (by positivity : (0 : ℝ) < 2 * (d : ℝ))
    linarith
  have hΓp_le : (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 :=
    by simpa using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := γ) (by norm_num) le_rfl
  have hΓm_le : (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 := by
    have he : (2 : ℂ) - (γ : ℂ) * I = ((2 : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by push_cast; ring
    rw [he]
    simpa [abs_neg] using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := -γ) (by norm_num) le_rfl
  have hd_shifted : (d : ℝ) * ((logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
      (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re) ≤
      (d : ℝ) * Real.log (3 + |γ|) + (1 / 2 : ℝ) * (d : ℝ) := by
    have hsum_le : (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
        (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) + 1 / 2 := by linarith
    have := mul_le_mul_of_nonneg_left hsum_le hd_pos.le
    linarith
  have hhad := re_logDeriv_two_ge_of_entire_sym hHC.entire_Λ hHC.orderOne_Λ hHC.sym_Λ hHC.conj_Λ
    hHC.two_ne_zero (fun _ hρ => hHC.zero_re_mem_Icc hρ) X hX ∅
    (fun _ h => absurd h (Finset.notMem_empty _))
  simp only [Finset.sum_empty, add_zero] at hhad
  linarith

/-- **Ordinate-decaying quartet multiplicity bound (`18 κ ↦ (9 + O(1/γ²)) κ`).** Keeping `κ_γ = κ`
halves the asymptotic pole cost of `ordinateQuartet_multiplicity_archimedean_bound` from `18 κ` to
`9 κ` as `|γ| → ∞`. -/
theorem CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ) {γ : ℝ} (hγ : γ ≠ 0)
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2) :
    8 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) +
      4 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      4 * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) <
    (9 + 12 / (4 + γ ^ 2) + 6 / (1 + γ ^ 2)) * (κ : ℝ) +
      3 * (d : ℝ) * Real.log (3 + |γ|) - (7 / 2 : ℝ) * (d : ℝ) := by
  obtain ⟨Fc, Λc, hHCc, hhalf, _⟩ :=
    CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled hS hγ A hA
  have hbud := hHCc.archimedean_budget_exact ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
  simp only [Finset.sum_empty, mul_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat] at hbud
  have hcast : ((analyticOrderAt Λc (1 / 2)).toNat : ℝ) =
      2 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      2 * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) +
      4 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) := by
    rw [hhalf]; push_cast; ring
  rw [hcast] at hbud
  have hrhs : (9 + 12 / (4 + γ ^ 2) + 6 / (1 + γ ^ 2)) * (κ : ℝ) =
      9 * (κ : ℝ) + 3 * ((4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2)) * (κ : ℝ)) := by ring
  rw [hrhs]
  linarith

/-! ### 4. Single-system real-anchor planting (`κ_γ = 0, Δd = 0`) and Hadamard minimum pole law -/

/-- Unshifted boundary-to-strip real-pair planter
`R_a(s) = realPairFactor (1/2 + a) s = (s − (1/2 + a))(s − (1/2 − a)) / (s(s − 1))`
trading one central pole pair `{0, 1}` for a symmetric real zero pair `{1/2 ± a}`. -/
def realPairPlanter (a : ℝ) (s : ℂ) : ℂ :=
  realPairFactor (1 / 2 + a) s

private theorem realPairPlanter_ne_zero_of_one_lt_re {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    {s : ℂ} (hs : 1 < s.re) : realPairPlanter a s ≠ 0 := by
  unfold realPairPlanter realPairFactor realPairPoly
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hn1 : s - ((1 / 2 + a : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hn2 : s - ((1 - (1 / 2 + a) : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  exact div_ne_zero (mul_ne_zero hn1 hn2) (mul_ne_zero hs0 hs1)

private theorem differentiableAt_realPairPlanter_of_one_lt_re (a : ℝ) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (realPairPlanter a) s := by
  unfold realPairPlanter realPairFactor
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  exact (by unfold realPairPoly; fun_prop : DifferentiableAt ℂ (realPairPoly (1 / 2 + a)) s).div
    (by fun_prop) (mul_ne_zero hs0 hs1)

/-- **Bochner positivity of `realPairPlanter a` on `σ > 1` (`0 < a < 1/2`).** Its vertical
`−logDeriv` section has nonnegative Laplace cosine density
`e^{−σt} (e^{(1/2 + a)t} − 1) (e^{(1/2 − a)t} − 1) ≥ 0` on `(0, ∞)`. -/
theorem isEvenPosDef_realPairPlanter {a σ : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) :
    IsEvenPosDef fun u : ℝ =>
      (-logDeriv (realPairPlanter a) ((σ : ℂ) + (u : ℂ) * I)).re := by
  set β : ℝ := 1 / 2 + a
  have hβ0 : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  let w : ℝ → ℝ := fun t =>
    Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1)
  have hexp_expand : ∀ t : ℝ, w t =
      Real.exp (-(σ - 1) * t) + Real.exp (-σ * t) -
        Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
    intro t
    dsimp only [w]
    have p1 : Real.exp (-σ * t) * Real.exp (β * t) * Real.exp ((1 - β) * t) =
        Real.exp (-(σ - 1) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have p2 : Real.exp (-σ * t) * Real.exp (β * t) = Real.exp (-(σ - β) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have p3 : Real.exp (-σ * t) * Real.exp ((1 - β) * t) = Real.exp (-(σ - (1 - β)) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-σ * t) * (Real.exp (β * t) - 1) * (Real.exp ((1 - β) * t) - 1)
        = Real.exp (-σ * t) * Real.exp (β * t) * Real.exp ((1 - β) * t) +
            Real.exp (-σ * t) -
            Real.exp (-σ * t) * Real.exp (β * t) -
            Real.exp (-σ * t) * Real.exp ((1 - β) * t) := by ring
      _ = Real.exp (-(σ - 1) * t) + Real.exp (-σ * t) -
            Real.exp (-(σ - β) * t) - Real.exp (-(σ - (1 - β)) * t) := by
          rw [p1, p2, p3]
  refine isEvenPosDef_laplace_cos_aux (w := w) (C := 2) (a := σ - 1)
    (by linarith) (by dsimp only [w]; fun_prop)
    (fun t ht => ?_) (fun t ht => ?_) (fun u => ?_)
  · have h1 : 0 ≤ Real.exp (β * t) - 1 := sub_nonneg.mpr (Real.one_le_exp (by nlinarith))
    have h2 : 0 ≤ Real.exp ((1 - β) * t) - 1 := sub_nonneg.mpr (Real.one_le_exp (by nlinarith))
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le h1) h2
  · rw [hexp_expand t]
    have hle_exp : Real.exp (-σ * t) ≤ Real.exp (-(σ - 1) * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (-(σ - β) * t), Real.exp_pos (-(σ - (1 - β)) * t)]
  · set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
    have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hn1 : s - (β : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hn2 : s - ((1 - β : ℝ) : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
    have hld : -logDeriv (realPairPlanter a) s =
        1 / s + 1 / (s - 1) - 1 / (s - (β : ℂ)) - 1 / (s - ((1 - β : ℝ) : ℂ)) := by
      change -logDeriv (realPairFactor β) s = _
      unfold realPairFactor realPairPoly
      rw [logDeriv_div
            (f := fun z : ℂ => (z - (β : ℂ)) * (z - ((1 - β : ℝ) : ℂ)))
            (g := fun z : ℂ => z * (z - 1))
            s (mul_ne_zero hn1 hn2) (mul_ne_zero hs0 hs1)
            ((differentiableAt_id.sub_const _).mul (differentiableAt_id.sub_const _))
            (differentiableAt_id.mul (differentiableAt_id.sub_const 1)),
          logDeriv_mul (f := fun z : ℂ => z - (β : ℂ))
            (g := fun z : ℂ => z - ((1 - β : ℝ) : ℂ)) s hn1 hn2
            (differentiableAt_id.sub_const _) (differentiableAt_id.sub_const _),
          logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hs0 hs1
            differentiableAt_id (differentiableAt_id.sub_const 1),
          hd_lin, hd_lin, hd_lin]
      have hid' : logDeriv (fun z : ℂ => z) s = 1 / s := by
        rw [logDeriv_apply, deriv_id'', one_div]
      rw [hid']; ring
    have e1 : s - 1 = (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) := by dsimp [s]; push_cast; ring
    have e2 : s - (β : ℂ) = (((σ - β : ℝ) : ℂ) + (u : ℂ) * I) := by dsimp [s]; push_cast; ring
    have e3 : s - ((1 - β : ℝ) : ℂ) = (((σ - (1 - β) : ℝ) : ℂ) + (u : ℂ) * I) := by
      dsimp [s]; push_cast; ring
    change (-logDeriv (realPairPlanter a) s).re = _
    rw [hld, Complex.sub_re, Complex.sub_re, Complex.add_re, e1, e2, e3]
    dsimp [s]
    rw [re_one_div_laplace_cos_aux σ u (by linarith),
        re_one_div_laplace_cos_aux (σ - 1) u (by linarith),
        re_one_div_laplace_cos_aux (σ - β) u (by linarith),
        re_one_div_laplace_cos_aux (σ - (1 - β)) u (by linarith)]
    have i0 := integrableOn_exp_cos_Ioi_aux σ u (by linarith)
    have i1 := integrableOn_exp_cos_Ioi_aux (σ - 1) u (by linarith)
    have i2 := integrableOn_exp_cos_Ioi_aux (σ - β) u (by linarith)
    have i3 := integrableOn_exp_cos_Ioi_aux (σ - (1 - β)) u (by linarith)
    have j1 := integral_add i0 i1
    have j2 := integral_sub (i0.add i1) i2
    dsimp only [Pi.add_apply] at j2
    have j3 := integral_sub ((i0.add i1).sub i2) i3
    dsimp only [Pi.sub_apply, Pi.add_apply] at j3
    rw [← j1, ← j2, ← j3]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hexp_expand t, mul_comm u t]
    ring

/-- **Single real-pair planting (`Δκ = 1, κ_γ = 0, Δd = 0`).** Multiplying any
`CompletedPositiveSystem κ d F Λ` by `realPairPlanter a` (`0 < a < 1/2`) increments
`ord_{1/2 + a}` by `+1` and preserves all zero orders outside `{1/2 ± a}` at cost `κ + 1`. -/
theorem CompletedPositiveSystem.plantRealPair {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    CompletedPositiveSystem (κ + 1) d
      (fun s => F s * realPairPlanter a s)
      (fun s => Λ s * realPairPoly (1 / 2 + a) s) ∧
    (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s) ((1 / 2 + a : ℝ) : ℂ)).toNat =
      (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat + 1 ∧
    (∀ z : ℂ, z ≠ ((1 / 2 + a : ℝ) : ℂ) → z ≠ ((1 / 2 - a : ℝ) : ℂ) →
      (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s) z).toNat =
        (analyticOrderAt Λ z).toNat) := by
  have hpoly_order : OrderOneEnvelope (realPairPoly (1 / 2 + a)) := by
    have hid := RHTower.orderOneEnvelope_id
    have h1 : OrderOneEnvelope (fun s : ℂ => s - ((1 / 2 + a : ℝ) : ℂ)) :=
      (hid.add (orderOneEnvelope_const (-((1 / 2 + a : ℝ) : ℂ)))).congr fun s => by ring
    have h2 : OrderOneEnvelope (fun s : ℂ => s - ((1 - (1 / 2 + a) : ℝ) : ℂ)) :=
      (hid.add (orderOneEnvelope_const (-((1 - (1 / 2 + a) : ℝ) : ℂ)))).congr fun s => by ring
    exact h1.mul h2
  have hS' : CompletedPositiveSystem (κ + 1) d
      (fun s => F s * realPairPlanter a s)
      (fun s => Λ s * realPairPoly (1 / 2 + a) s) :=
    { degree_pos := hS.degree_pos
      diffOn_F := hS.diffOn_F.mul
        (fun s hs => (differentiableAt_realPairPlanter_of_one_lt_re a hs).differentiableWithinAt)
      ne_zero_F := fun s hs =>
        mul_ne_zero (hS.ne_zero_F s hs) (realPairPlanter_ne_zero_of_one_lt_re ha0 ha1 hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * realPairPlanter a s) ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (realPairPlanter a) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := realPairPlanter a) s
                (hS.ne_zero_F s hs) (realPairPlanter_ne_zero_of_one_lt_re ha0 ha1 hs)
                ((hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (differentiableAt_realPairPlanter_of_one_lt_re a hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_aux (hS.posDef_neg_logDeriv hσ)
          (isEvenPosDef_realPairPlanter ha0 ha1 hσ)
      entire_Λ := hS.entire_Λ.mul (by unfold realPairPoly; fun_prop)
      orderOne_Λ := hS.orderOne_Λ.mul hpoly_order
      sym_Λ := fun s => by
        rw [hS.sym_Λ]; congr 1; unfold realPairPoly; push_cast; ring
      conj_Λ := fun s => by
        rw [map_mul, hS.conj_Λ]; congr 1
        unfold realPairPoly; simp only [map_mul, map_sub, Complex.conj_ofReal]
      completed_eq := fun s hs => by
        have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
        have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
        have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
        have hmul : (s * (s - 1)) * realPairPlanter a s = realPairPoly (1 / 2 + a) s := by
          unfold realPairPlanter realPairFactor
          exact mul_div_cancel₀ _ hden
        rw [hS.completed_eq s hs, pow_succ]
        calc (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s * realPairPoly (1 / 2 + a) s
            = (s * (s - 1)) ^ κ * ((s * (s - 1)) * realPairPlanter a s) *
                Complex.Gammaℝ s ^ d * F s := by rw [hmul]; ring
          _ = (s * (s - 1)) ^ κ * (s * (s - 1)) * Complex.Gammaℝ s ^ d *
                (F s * realPairPlanter a s) := by ring }
  set x₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ)
  set x₂ : ℂ := ((1 / 2 - a : ℝ) : ℂ)
  have hx₂_eq : (((1 - (1 / 2 + a) : ℝ) : ℂ)) = x₂ := by dsimp [x₂]; push_cast; ring
  have hord_x₁ : (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s) x₁).toNat =
      (analyticOrderAt Λ x₁).toNat + 1 := by
    have hfac : (fun s => Λ s * realPairPoly (1 / 2 + a) s) =
        (Λ * fun s => s - x₂) * ((· - x₁) ^ 1) := by
      funext s; unfold realPairPoly; rw [hx₂_eq]; dsimp [x₁]; simp; ring
    have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr fun h => by
      have := congrArg Complex.re h; simp [x₁, x₂] at this; linarith
    have han_sub2 : AnalyticAt ℂ (fun s : ℂ => s - x₂) x₁ := by fun_prop
    have han_mon1 : AnalyticAt ℂ ((· - x₁) ^ 1) x₁ :=
      ((differentiable_id.sub_const x₁).pow 1).analyticAt x₁
    have h1 : analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s) x₁ =
        analyticOrderAt Λ x₁ + (1 : ℕ) := by
      rw [hfac,
          analyticOrderAt_mul ((hS.entire_Λ.analyticAt x₁).mul han_sub2) han_mon1,
          analyticOrderAt_mul (hS.entire_Λ.analyticAt x₁) han_sub2,
          han_sub2.analyticOrderAt_eq_zero.mpr hx12, add_zero,
          analyticOrderAt_centeredMonomial]
    rw [h1, ENat.toNat_add (hS.orderAt_ne_top x₁) (ENat.coe_ne_top 1), ENat.toNat_coe]
  have hord_other : ∀ z : ℂ, z ≠ x₁ → z ≠ x₂ →
      (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s) z).toNat =
        (analyticOrderAt Λ z).toNat := by
    intro z hz1 hz2
    have hpnz : realPairPoly (1 / 2 + a) z ≠ 0 := by
      unfold realPairPoly; rw [hx₂_eq]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (sub_ne_zero.mpr hz2)
    have hanP : AnalyticAt ℂ (realPairPoly (1 / 2 + a)) z := by unfold realPairPoly; fun_prop
    have hprod : (fun s => Λ s * realPairPoly (1 / 2 + a) s) = Λ * realPairPoly (1 / 2 + a) := rfl
    rw [hprod, analyticOrderAt_mul (hS.entire_Λ.analyticAt z) hanP,
        hanP.analyticOrderAt_eq_zero.mpr hpnz, add_zero]
  exact ⟨hS', hord_x₁, hord_other⟩

/-- **Double real-anchor planting (`Δκ = 2, κ_γ = 0, Δd = 0`).** Multiplying any
`CompletedPositiveSystem κ d F Λ` by `realPairPlanter a ^ 2` (`0 < a < 1/2`) plants a weight-`2`
real anchor at `1/2 + a` while keeping `κ_γ = 0`, `d` unchanged, and every zero order outside
`{1/2 ± a}` invariant, at cost `κ ↦ κ + 2`. -/
theorem CompletedPositiveSystem.plantDoubleRealAnchor {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    CompletedPositiveSystem (κ + 2) d
      (fun s => F s * realPairPlanter a s ^ 2)
      (fun s => Λ s * realPairPoly (1 / 2 + a) s ^ 2) ∧
    (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s ^ 2) ((1 / 2 + a : ℝ) : ℂ)).toNat =
      (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 ∧
    (∀ z : ℂ, z ≠ ((1 / 2 + a : ℝ) : ℂ) → z ≠ ((1 / 2 - a : ℝ) : ℂ) →
      (analyticOrderAt (fun s => Λ s * realPairPoly (1 / 2 + a) s ^ 2) z).toNat =
        (analyticOrderAt Λ z).toNat) := by
  obtain ⟨hS₁, hord₁, hout₁⟩ := CompletedPositiveSystem.plantRealPair hS ha0 ha1
  obtain ⟨hS₂, hord₂, hout₂⟩ := CompletedPositiveSystem.plantRealPair hS₁ ha0 ha1
  have hF_eq : (fun s => F s * realPairPlanter a s * realPairPlanter a s) =
      fun s => F s * realPairPlanter a s ^ 2 := funext fun s => by ring
  have hΛ_eq : (fun s => Λ s * realPairPoly (1 / 2 + a) s * realPairPoly (1 / 2 + a) s) =
      fun s => Λ s * realPairPoly (1 / 2 + a) s ^ 2 := funext fun s => by ring
  rw [hF_eq, hΛ_eq] at hS₂
  rw [hΛ_eq] at hord₂ hout₂
  refine ⟨hS₂, by omega, fun z hz1 hz2 => ?_⟩
  rw [hout₂ z hz1 hz2, hout₁ z hz1 hz2]

/-- **Short-scale Post–Widder residue sum law (`t ↓ 0`).** Every conjugation-symmetric polar sum
with positive-definite vertical sections on `σ > σ₁` has nonnegative total residue weight
`0 ≤ ∑_{z ∈ S} c(z)`. -/
theorem polarSum_sum_weights_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S)
    (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) :
    0 ≤ ∑ z ∈ S, c z := by
  have hcont : Continuous (polarScaleWeight S c) := by unfold polarScaleWeight; fun_prop
  have h0 : polarScaleWeight S c 0 = ∑ z ∈ S, c z := by
    unfold polarScaleWeight; simp
  have hlim : Tendsto (fun n : ℕ => polarScaleWeight S c (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (∑ z ∈ S, c z)) := by
    rw [← h0]
    exact (hcont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
    posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re hpd (by positivity))

/-- **Sharp `Δκ ≥ 2` polar-sum converse for planting a weight-`2` real anchor.** Any
conjugation-symmetric positive-definite polar sum that plants zeros off `{0, 1}` (`c(z) ≤ 0` for
`z ∉ {0, 1}`), plants a double real anchor `c(1/2 ± a) ≤ −2` (`0 < a < 1/2`), and spends at most
`Δκ` at each of `s = 0` and `s = 1` satisfies `2 ≤ Δκ`, proving `plantDoubleRealAnchor` is minimal
among zero-planting multipliers. -/
theorem two_le_pole_cost_of_doubleRealAnchor_polarSum {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ a Δκ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S)
    (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (hc_nonpos : ∀ z ∈ S, z ≠ 0 → z ≠ 1 → c z ≤ 0)
    (hc0 : (0 : ℂ) ∈ S → c 0 ≤ Δκ)
    (hc1 : (1 : ℂ) ∈ S → c 1 ≤ Δκ)
    (hx₁_mem : ((1 / 2 + a : ℝ) : ℂ) ∈ S)
    (hx₂_mem : ((1 / 2 - a : ℝ) : ℂ) ∈ S)
    (hcx₁ : c ((1 / 2 + a : ℝ) : ℂ) ≤ -2)
    (hcx₂ : c ((1 / 2 - a : ℝ) : ℂ) ≤ -2) :
    2 ≤ Δκ := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hsum_nn := polarSum_sum_weights_nonneg hS_conj hc_conj hS_re hpd
  set x₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ)
  set x₂ : ℂ := ((1 / 2 - a : ℝ) : ℂ)
  let c' : ℂ → ℝ := fun z => if z ∈ S then c z else 0
  set T : Finset ℂ := S ∪ {0, 1}
  set P : Finset ℂ := {0, 1, x₁, x₂}
  have hsum_eq : ∑ z ∈ T, c' z = ∑ z ∈ S, c z := by
    rw [← Finset.sum_subset (Finset.subset_union_left : S ⊆ T)
      (fun z _ hnot => by simp [c', hnot])]
    exact Finset.sum_congr rfl fun z hz => by simp [c', hz]
  have hP_sub : P ⊆ T := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_right _ (by simp)
    · exact Finset.mem_union_right _ (by simp)
    · exact Finset.mem_union_left _ hx₁_mem
    · exact Finset.mem_union_left _ hx₂_mem
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have h0x₁ : (0 : ℂ) ≠ x₁ := fun h => by have := congrArg Complex.re h; simp [x₁] at this; linarith
  have h0x₂ : (0 : ℂ) ≠ x₂ := fun h => by have := congrArg Complex.re h; simp [x₂] at this; linarith
  have h1x₁ : (1 : ℂ) ≠ x₁ := fun h => by have := congrArg Complex.re h; simp [x₁] at this; linarith
  have h1x₂ : (1 : ℂ) ≠ x₂ := fun h => by have := congrArg Complex.re h; simp [x₂] at this; linarith
  have hx12 : x₁ ≠ x₂ := fun h => by have := congrArg Complex.re h; simp [x₁, x₂] at this; linarith
  have hP_sum : ∑ z ∈ P, c' z = c' 0 + c' 1 + c' x₁ + c' x₂ := by
    dsimp [P]
    rw [Finset.sum_insert (by simp [h01, h0x₁, h0x₂]),
        Finset.sum_insert (by simp [h1x₁, h1x₂]),
        Finset.sum_pair hx12]
    ring
  have hc'0 : c' 0 < 2 := by
    dsimp [c']; split_ifs with h0
    · exact (hc0 h0).trans_lt hlt
    · norm_num
  have hc'1 : c' 1 < 2 := by
    dsimp [c']; split_ifs with h1
    · exact (hc1 h1).trans_lt hlt
    · norm_num
  have hc'x₁ : c' x₁ ≤ -2 := by simp [c', hx₁_mem, hcx₁]
  have hc'x₂ : c' x₂ ≤ -2 := by simp [c', hx₂_mem, hcx₂]
  have hrest_le : ∑ z ∈ T \ P, c' z ≤ 0 := by
    refine Finset.sum_nonpos fun z hz => ?_
    rw [Finset.mem_sdiff] at hz
    have hz_not : ¬(z = 0 ∨ z = 1 ∨ z = x₁ ∨ z = x₂) := by simpa [P] using hz.2
    push Not at hz_not
    dsimp [c']; split_ifs with hzS
    · exact hc_nonpos z hzS hz_not.1 hz_not.2.1
    · rfl
  have hsplit : ∑ z ∈ T, c' z = (∑ z ∈ P, c' z) + ∑ z ∈ T \ P, c' z := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hP_sub]
  linarith [hsum_nn, hsum_eq, hsplit, hP_sum, hc'0, hc'1, hc'x₁, hc'x₂, hrest_le]

private theorem contractAnchoredQuartet_iter_iem :
    ∀ (k : ℕ) {κ d : ℕ} {a γ : ℝ} {F Λ : ℂ → ℂ},
      CompletedPositiveSystem κ d F Λ →
      0 < a → a < 1 / 2 → γ ≠ 0 →
      2 * k ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat →
      k ≤ (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat →
      ∃ Fc Λc : ℂ → ℂ,
        CompletedPositiveSystem κ d Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 * k ∧
        (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
          (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 * k ∧
        (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 * k =
          (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat ∧
        (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + k =
          (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat)
  | 0, _, _, _, _, F, Λ, hS, _, _, _, _, _ =>
      ⟨F, Λ, hS, by omega, by omega, by omega, by omega, fun _ _ _ _ => rfl⟩
  | k + 1, _, _, a, γ, F, Λ, hS, ha0, ha1, hγ, hreal, hquart => by
      have hreal2 : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat := by omega
      have hq0 : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 :=
        hS.eq_zero_of_one_le_order_toNat (by omega)
      obtain ⟨Λ₁, hS₁, _, h1, h2, h3, h4, h5⟩ :=
        CompletedPositiveSystem.contractComplexQuartet_of_doubleRealAnchor hS ha0 le_rfl ha1 hγ
          hreal2 hq0
      obtain ⟨Fc, Λc, hSc, hc1, hc2, hc3, hc4, hc5⟩ :=
        contractAnchoredQuartet_iter_iem k hS₁ ha0 ha1 hγ (by omega) (by omega)
      refine ⟨Fc, Λc, hSc, by omega, by omega, by omega, by omega, fun z hz0 hza1 hza2 => ?_⟩
      rw [hc5 z hz0 hza1 hza2, h5 z hz0 hza1 hza2 hza1 hza2]

/-- **Functor-independent Hadamard pole lower bound for weight-`2` real-anchored quartets.**
Completely independent of how `(F, Λ)` is constructed, ANY unshifted
`CompletedPositiveSystem κ d F Λ` carrying multiplicities `2 m(a) ≤ ord_{1/2 + a}(Λ)` and
`m(a) ≤ ord_{1/2 + a + iγ}(Λ)` (`γ ≠ 0`) across a finite set `A ⊂ (0, 1/2)` obeys
`16 M + (144 / (9 + 4γ²)) M + 4 ord_{1/2}(Λ) + (72 / (9 + 4γ²)) ord_{1/2 + iγ}(Λ) + 5 d < 9 κ`,
where `M = ∑_{a ∈ A} m(a)`. -/
theorem CompletedPositiveSystem.anchored_quartet_pole_lower_bound
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    {γ : ℝ} (hγ : γ ≠ 0) (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2)
    (m : ℝ → ℕ)
    (hreal : ∀ a ∈ A, 2 * m a ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat)
    (hquart : ∀ a ∈ A, m a ≤ (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat) :
    16 * (∑ a ∈ A, (m a : ℝ)) +
      (144 / (9 + 4 * γ ^ 2)) * (∑ a ∈ A, (m a : ℝ)) +
      4 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      (72 / (9 + 4 * γ ^ 2)) * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) +
      5 * (d : ℝ) <
    9 * (κ : ℝ) := by
  classical
  have hcontract_all : ∀ B : Finset ℝ, B ⊆ A →
      ∃ Fc Λc : ℂ → ℂ,
        CompletedPositiveSystem κ d Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat =
          (analyticOrderAt Λ (1 / 2)).toNat + 4 * ∑ a ∈ B, m a ∧
        (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
          (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 * ∑ a ∈ B, m a ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → (∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b) →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat) := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨F, Λ, hS, by simp, by simp, fun _ _ _ => rfl⟩
    | @insert a B ha_not ih =>
        intro hB_sub
        have ha_mem : a ∈ A := hB_sub (Finset.mem_insert_self a B)
        obtain ⟨ha0, ha1⟩ := hA a ha_mem
        obtain ⟨F₁, Λ₁, hS₁, hhalf₁, hcrit₁, hout₁⟩ :=
          ih (Finset.Subset.trans (Finset.subset_insert a B) hB_sub)
        have ha_sep : ∀ b ∈ B, (1 / 2 + a : ℝ) ≠ 1 / 2 + b ∧ (1 / 2 + a : ℝ) ≠ 1 / 2 - b := by
          intro b hb
          have hb0 : 0 < b := (hA b (hB_sub (Finset.mem_insert_of_mem hb))).1
          have hab : a ≠ b := fun heq => ha_not (heq ▸ hb)
          exact ⟨fun h => hab (by linarith), fun h => by linarith⟩
        have hord_F₁_real : (analyticOrderAt Λ₁ ((1 / 2 + a : ℝ) : ℂ)).toNat =
            (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat :=
          hout₁ ((1 / 2 + a : ℝ) : ℂ) (by simp; linarith) (fun b hb => by simpa using ha_sep b hb)
        have hord_F₁_quart : (analyticOrderAt Λ₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat =
            (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
          refine hout₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) (by simp; linarith) fun b hb => ?_
          have hre : (1 / 2 + (a : ℂ) + (γ : ℂ) * I).re = 1 / 2 + a := by simp
          rw [hre]; exact ha_sep b hb
        obtain ⟨Fc, Λc, hSc, hc_half, hc_crit, _, _, hc_out⟩ :=
          contractAnchoredQuartet_iter_iem (m a) hS₁ ha0 ha1 hγ
            (by rw [hord_F₁_real]; exact hreal a ha_mem)
            (by rw [hord_F₁_quart]; exact hquart a ha_mem)
        refine ⟨Fc, Λc, hSc, ?_, ?_, ?_⟩
        · rw [Finset.sum_insert ha_not, hc_half, hhalf₁]; omega
        · rw [Finset.sum_insert ha_not, hc_crit, hcrit₁]; omega
        · intro z hz0 hz_ins
          have hz_a := hz_ins a (Finset.mem_insert_self a B)
          have hz_B : ∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b :=
            fun b hb => hz_ins b (Finset.mem_insert_of_mem hb)
          rw [hc_out z hz0 hz_a.1 hz_a.2, hout₁ z hz0 hz_B]
  obtain ⟨Fc, Λc, hSc, hhalf_c, hcrit_c, _⟩ := hcontract_all A Finset.Subset.rfl
  have hord_abs : (analyticOrderAt Λc (1 / 2 + ((|γ| : ℝ) : ℂ) * I)).toNat =
      (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat := by
    congr 1
    rcases le_or_gt 0 γ with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0]
      have hconj_eq : (1 / 2 : ℂ) + ((-γ : ℝ) : ℂ) * I =
          starRingEnd ℂ (1 / 2 + (γ : ℂ) * I) := by
        push_cast; simp [map_ofNat]
      rw [hconj_eq, hSc.orderAt_conj]
  have hhad := re_logDeriv_two_ge_of_entire_sym hSc.entire_Λ hSc.orderOne_Λ hSc.sym_Λ hSc.conj_Λ
    hSc.two_ne_zero (fun _ hρ => hSc.zero_re_mem_Icc hρ)
    ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
    {|γ|} (by simp [abs_pos.mpr hγ])
  simp only [Finset.sum_empty, mul_zero, add_zero, Finset.sum_singleton, sq_abs] at hhad
  rw [hord_abs] at hhad
  have hpos2 : 0 ≤ (-logDeriv Fc (2 : ℂ)).re := by
    have hpd := (hSc.posDef_neg_logDeriv (σ := 2) (by norm_num)).posDef 1 (fun _ => 0) (fun _ => 1)
    simpa using hpd
  have hdecomp := congrArg Complex.re (hSc.neg_logDeriv_F_eq (s := 2) (by norm_num))
  have hre2 : ((κ : ℂ) * (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)) +
      (d : ℂ) * logDeriv Complex.Gammaℝ 2 - logDeriv Λc 2).re =
      (3 / 2 : ℝ) * (κ : ℝ) + (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re - (logDeriv Λc 2).re := by
    rw [Complex.sub_re, Complex.add_re,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.add_re]
    have hp1 : (1 / (2 : ℂ)).re = 1 / 2 := by norm_num
    have hp2 : (1 / ((2 : ℂ) - 1)).re = 1 := by norm_num
    rw [hp1, hp2]; ring
  rw [hre2] at hdecomp
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hSc.degree_pos
  have hd_lt : (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re < -(5 / 6 : ℝ) * (d : ℝ) := by
    have := mul_lt_mul_of_pos_left re_logDeriv_Gammaℝ_two_lt hd_pos
    linarith
  have hhalf_cast : ((analyticOrderAt Λc (1 / 2)).toNat : ℝ) =
      ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) + 4 * ∑ a ∈ A, (m a : ℝ) := by
    rw [hhalf_c]; push_cast; ring
  have hcrit_cast : ((analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) =
      ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) + 2 * ∑ a ∈ A, (m a : ℝ) := by
    rw [hcrit_c]; push_cast; ring
  rw [hhalf_cast, hcrit_cast] at hhad
  have h6 := mul_le_mul_of_nonneg_left hhad (by norm_num : (0 : ℝ) ≤ 6)
  have h6_eq : 6 *
      ((2 / 3 : ℝ) * (((analyticOrderAt Λ (1 / 2)).toNat : ℝ) + 4 * ∑ a ∈ A, (m a : ℝ)) +
        (12 / (9 + 4 * γ ^ 2)) *
          (((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) + 2 * ∑ a ∈ A, (m a : ℝ))) =
      16 * (∑ a ∈ A, (m a : ℝ)) +
        (144 / (9 + 4 * γ ^ 2)) * (∑ a ∈ A, (m a : ℝ)) +
        4 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
        (72 / (9 + 4 * γ ^ 2)) * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) := by
    ring
  rw [h6_eq] at h6
  linarith

/-- **Sharp `κ ≥ 3` floor for any unshifted `CompletedPositiveSystem` carrying an anchored complex
quartet.** Whenever `0 < a < 1/2`, `γ ≠ 0`, `2 ≤ ord_{1/2 + a}(Λ)`, and `Λ(1/2 + a + iγ) = 0`,
`3 ≤ κ` unconditionally (`21 < 9 κ`). -/
theorem CompletedPositiveSystem.three_le_pole_of_anchored_quartet
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    {a γ : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (hreal : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat)
    (hquart : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    3 ≤ κ := by
  have hq1 : 1 ≤ (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat :=
    hS.one_le_order_toNat_of_eq_zero hquart
  have hbound := CompletedPositiveSystem.anchored_quartet_pole_lower_bound hS hγ {a}
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact ⟨ha0, ha1⟩) (fun _ => 1)
    (fun x hx => by rw [Finset.mem_singleton.mp hx, mul_one]; exact hreal)
    (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hq1)
  simp only [Finset.sum_singleton, Nat.cast_one, mul_one] at hbound
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hS.degree_pos
  have h144 : (0 : ℝ) ≤ 144 / (9 + 4 * γ ^ 2) := by positivity
  have h4 : (0 : ℝ) ≤ 4 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) := by positivity
  have h72 : (0 : ℝ) ≤
      (72 / (9 + 4 * γ ^ 2)) * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) := by
    positivity
  have h21 : (21 : ℝ) < 9 * (κ : ℝ) := by linarith
  by_contra hlt
  have hle2 : (κ : ℝ) ≤ 2 := by exact_mod_cast (by omega : κ ≤ 2)
  linarith

/-! ### 5. Fejér–Egerváry–Szász multiplier converse, two-sided shifted-Gamma law, and Fejér coupling -/

private theorem sum_range_sub_iem (g : ℕ → ℝ) :
    ∀ n : ℕ, ∑ r ∈ Finset.range n, (g (r + 1) - g r) = g n - g 0
  | 0 => by simp
  | n + 1 => by rw [Finset.sum_range_succ, sum_range_sub_iem g n]; ring

private theorem sin_nat_mul_pi_iem : ∀ k : ℕ, Real.sin ((k : ℝ) * Real.pi) = 0
  | 0 => by simp
  | k + 1 => by
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add, sin_nat_mul_pi_iem k, Real.sin_pi]
      ring

private theorem sum_cos_odd_grid_eq_zero_iem {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m < M) :
    ∑ r ∈ Finset.range M,
      Real.cos ((m : ℝ) * (((2 * r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ))) = 0 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  set β : ℝ := (m : ℝ) * Real.pi / (M : ℝ)
  have hβ_pos : 0 < β := by
    dsimp [β]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    exact div_pos (mul_pos hm_pos Real.pi_pos) hM_pos
  have hβ_lt : β < Real.pi := by
    dsimp [β]
    rw [div_lt_iff₀ hM_pos]
    have hm_lt : (m : ℝ) < (M : ℝ) := by exact_mod_cast hmM
    nlinarith [Real.pi_pos]
  have hsin_ne : Real.sin β ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt).ne'
  have hstep : ∀ r : ℕ,
      2 * Real.sin β * Real.cos ((m : ℝ) * (((2 * r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ))) =
        Real.sin (2 * ((r + 1 : ℕ) : ℝ) * β) - Real.sin (2 * (r : ℝ) * β) := by
    intro r
    have hang : (m : ℝ) * (((2 * r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ)) =
        (2 * (r : ℝ) + 1) * β := by
      dsimp [β]; push_cast; ring
    have ha1 : 2 * ((r + 1 : ℕ) : ℝ) * β = (2 * (r : ℝ) + 1) * β + β := by push_cast; ring
    have ha2 : 2 * (r : ℝ) * β = (2 * (r : ℝ) + 1) * β - β := by ring
    rw [hang, ha1, ha2, Real.sin_add, Real.sin_sub]
    ring
  have hsum : 2 * Real.sin β *
      ∑ r ∈ Finset.range M,
        Real.cos ((m : ℝ) * (((2 * r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ))) = 0 := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun r _ => hstep r,
        sum_range_sub_iem (fun r : ℕ => Real.sin (2 * (r : ℝ) * β)) M]
    have hMβ : 2 * (M : ℝ) * β = ((2 * m : ℕ) : ℝ) * Real.pi := by
      dsimp [β]; field_simp [hM_pos.ne']; push_cast; ring
    rw [hMβ, sin_nat_mul_pi_iem (2 * m)]
    simp
  have h2sin : 2 * Real.sin β ≠ 0 := mul_ne_zero two_ne_zero hsin_ne
  exact (mul_eq_zero.mp hsum).resolve_left h2sin

/-- **Discrete Fejér–Egerváry–Szász first-harmonic inequality.** For every degree-`K` (`1 ≤ K`)
nonnegative cosine polynomial `P(θ) = c₀ + ∑_{k ∈ Icc 1 K} c_k cos(kθ) ≥ 0`, discrete quadrature at
`θ_r = (2r + 1)π / (K + 2)` (`0 ≤ r < K + 2`) with nonnegative weights `cos(π/(K + 2)) − cos θ_r`
proves `c₁ ≤ 2 c₀ cos(π / (K + 2))`. -/
theorem fejer_egervary_szasz_first_harmonic_le {K : ℕ} (hK : 1 ≤ K) {c₀ : ℝ} {c : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ c₀ + ∑ k ∈ Finset.Icc 1 K, c k * Real.cos ((k : ℝ) * θ)) :
    c 1 ≤ 2 * c₀ * Real.cos (Real.pi / ((K : ℝ) + 2)) := by
  set M : ℕ := K + 2
  have hM_cast : (M : ℝ) = (K : ℝ) + 2 := by dsimp [M]; push_cast; ring
  have hM_pos : (0 : ℝ) < (M : ℝ) := by rw [hM_cast]; positivity
  set α : ℝ := Real.pi / (M : ℝ)
  let θ : ℕ → ℝ := fun r => ((2 * r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ)
  have hw_nn : ∀ r ∈ Finset.range M, 0 ≤ Real.cos α - Real.cos (θ r) := by
    intro r hr
    have hr_lt : r < M := Finset.mem_range.mp hr
    rw [Real.cos_sub_cos]
    have hp_ang : (α + θ r) / 2 = ((r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ) := by
      dsimp [α, θ]; push_cast; field_simp [hM_pos.ne']; ring
    have hm_ang : (α - θ r) / 2 = -((r : ℝ) * Real.pi / (M : ℝ)) := by
      dsimp [α, θ]; push_cast; field_simp [hM_pos.ne']; ring
    rw [hp_ang, hm_ang, Real.sin_neg]
    have h1_nn : 0 ≤ Real.sin (((r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
      rw [div_le_iff₀ hM_pos]
      have hr1 : ((r + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hr_lt)
      nlinarith [Real.pi_pos]
    have h2_nn : 0 ≤ Real.sin ((r : ℝ) * Real.pi / (M : ℝ)) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
      rw [div_le_iff₀ hM_pos]
      have hrle : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hr_lt.le
      nlinarith [Real.pi_pos]
    have hid : -2 * Real.sin (((r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ)) *
        -Real.sin ((r : ℝ) * Real.pi / (M : ℝ)) =
        2 * Real.sin (((r + 1 : ℕ) : ℝ) * Real.pi / (M : ℝ)) *
          Real.sin ((r : ℝ) * Real.pi / (M : ℝ)) := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg zero_le_two h1_nn) h2_nn
  have hquad_nn : 0 ≤ ∑ r ∈ Finset.range M,
      (Real.cos α - Real.cos (θ r)) *
        (c₀ + ∑ k ∈ Finset.Icc 1 K, c k * Real.cos ((k : ℝ) * θ r)) :=
    Finset.sum_nonneg fun r hr => mul_nonneg (hw_nn r hr) (hP (θ r))
  have hsum_c0 : ∑ r ∈ Finset.range M, (Real.cos α - Real.cos (θ r)) * c₀ =
      (M : ℝ) * (c₀ * Real.cos α) := by
    have hsplit : ∑ r ∈ Finset.range M, (Real.cos α - Real.cos (θ r)) * c₀ =
        (∑ _r ∈ Finset.range M, c₀ * Real.cos α) -
          c₀ * ∑ r ∈ Finset.range M, Real.cos ((1 : ℝ) * θ r) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [one_mul]; ring
    have hc1 : ∑ r ∈ Finset.range M, Real.cos ((1 : ℝ) * θ r) = 0 := by
      simpa [θ] using sum_cos_odd_grid_eq_zero_iem (m := 1) le_rfl (by omega : 1 < M)
    rw [hsplit, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc1]
    ring
  have hsum_k : ∀ k ∈ Finset.Icc 1 K,
      ∑ r ∈ Finset.range M,
        (Real.cos α - Real.cos (θ r)) * (c k * Real.cos ((k : ℝ) * θ r)) =
      if k = 1 then -(M : ℝ) * (c 1 / 2) else 0 := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    have hprod_id : ∀ r : ℕ,
        (Real.cos α - Real.cos (θ r)) * (c k * Real.cos ((k : ℝ) * θ r)) =
          (c k * Real.cos α) * Real.cos ((k : ℝ) * θ r) -
            (c k / 2) * Real.cos (((k + 1 : ℕ) : ℝ) * θ r) -
            (c k / 2) * Real.cos (((k - 1 : ℕ) : ℝ) * θ r) := by
      intro r
      have hp : ((k + 1 : ℕ) : ℝ) * θ r = (k : ℝ) * θ r + θ r := by push_cast; ring
      have hm : ((k - 1 : ℕ) : ℝ) * θ r = (k : ℝ) * θ r - θ r := by
        rw [Nat.cast_sub hk1]; ring
      rw [hp, hm, Real.cos_add, Real.cos_sub]
      ring
    have hsum_split : ∑ r ∈ Finset.range M,
        (Real.cos α - Real.cos (θ r)) * (c k * Real.cos ((k : ℝ) * θ r)) =
        (c k * Real.cos α) * (∑ r ∈ Finset.range M, Real.cos ((k : ℝ) * θ r)) -
          (c k / 2) * (∑ r ∈ Finset.range M, Real.cos (((k + 1 : ℕ) : ℝ) * θ r)) -
          (c k / 2) * (∑ r ∈ Finset.range M, Real.cos (((k - 1 : ℕ) : ℝ) * θ r)) := by
      simp_rw [hprod_id, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum_split,
        sum_cos_odd_grid_eq_zero_iem hk1 (by omega : k < M),
        sum_cos_odd_grid_eq_zero_iem (by omega : 1 ≤ k + 1) (by omega : k + 1 < M)]
    rcases eq_or_ne k 1 with rfl | hkne
    · simp [nsmul_eq_mul]; ring
    · rw [if_neg hkne, sum_cos_odd_grid_eq_zero_iem (by omega : 1 ≤ k - 1) (by omega : k - 1 < M)]
      ring
  have hquad_eq : ∑ r ∈ Finset.range M,
      (Real.cos α - Real.cos (θ r)) *
        (c₀ + ∑ k ∈ Finset.Icc 1 K, c k * Real.cos ((k : ℝ) * θ r)) =
      (M : ℝ) * (c₀ * Real.cos α - c 1 / 2) := by
    have h1 : ∑ r ∈ Finset.range M,
        (Real.cos α - Real.cos (θ r)) *
          (c₀ + ∑ k ∈ Finset.Icc 1 K, c k * Real.cos ((k : ℝ) * θ r)) =
        (∑ r ∈ Finset.range M, (Real.cos α - Real.cos (θ r)) * c₀) +
          ∑ k ∈ Finset.Icc 1 K, ∑ r ∈ Finset.range M,
            (Real.cos α - Real.cos (θ r)) * (c k * Real.cos ((k : ℝ) * θ r)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.range M) (t := Finset.Icc 1 K)]
    have h1_mem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
    rw [h1, hsum_c0, Finset.sum_congr rfl hsum_k, Finset.sum_ite_eq' _ _ _]
    simp only [h1_mem, ite_true]
    ring
  rw [hquad_eq] at hquad_nn
  have hinner_nn : 0 ≤ c₀ * Real.cos α - c 1 / 2 :=
    (mul_nonneg_iff_of_pos_left hM_pos).mp hquad_nn
  have hα_eq : α = Real.pi / ((K : ℝ) + 2) := by dsimp [α]; rw [hM_cast]
  rw [← hα_eq]
  linarith


/-- **Sharp minimum central pole cost of degree-`K` cosine shift multipliers (`c₁ ≥ 2`).**
Any nonnegative cosine polynomial `c₀ + ∑_{k ∈ Icc 1 K} c_k cos(kθ) ≥ 0` (`1 ≤ K`) that collides a
conjugate quartet pair onto a real anchor of weight `c₁ ≥ 2` must pay central pole weight
`1 / cos(π / (K + 2)) ≤ c₀`, so `1 < c₀` for every finite shift bandwidth `K`. -/
theorem cosine_multiplier_anchor_cost_lower {K : ℕ} (hK : 1 ≤ K) {c₀ : ℝ} {c : ℕ → ℝ}
    (hP : ∀ θ : ℝ, 0 ≤ c₀ + ∑ k ∈ Finset.Icc 1 K, c k * Real.cos ((k : ℝ) * θ))
    (hc1 : 2 ≤ c 1) :
    1 / Real.cos (Real.pi / ((K : ℝ) + 2)) ≤ c₀ ∧ 1 < c₀ := by
  have hfe := fejer_egervary_szasz_first_harmonic_le hK hP
  set α : ℝ := Real.pi / ((K : ℝ) + 2)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) + 2 := by linarith
  have hα_pos : 0 < α := div_pos Real.pi_pos hden
  have hα_lt_half : α < Real.pi / 2 := by
    dsimp [α]
    rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [Real.pi_pos]
  have hcos_pos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα_lt_half⟩
  have hcos_lt_one : Real.cos α < 1 := by
    have hdiff := Real.cos_sub_cos 0 α
    rw [Real.cos_zero, zero_add, zero_sub, neg_div, Real.sin_neg] at hdiff
    have hsin_pos : 0 < Real.sin (α / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    nlinarith [hdiff, sq_pos_of_pos hsin_pos]
  have hle : 1 / Real.cos α ≤ c₀ := by
    rw [div_le_iff₀ hcos_pos]
    linarith
  have hgt1 : 1 < 1 / Real.cos α := (one_lt_div hcos_pos).mpr hcos_lt_one
  exact ⟨hle, hgt1.trans_le hle⟩

/-- **All-height lower bound on `Re logDeriv Γ_ℝ(2 + iγ)`.** Shifting `ψ(1 + iγ/2)` twice to
`3 + iγ/2` (`‖w‖ ≥ max(3, (3 + |γ|)/3)`) yields `log(3 + |γ|)/2 − 5/2 ≤ Re(Γ_ℝ'/Γ_ℝ)(2 + iγ)` for
every `γ ∈ ℝ` without height cutoffs. -/
theorem re_logDeriv_Gammaℝ_two_shift_ge (γ : ℝ) :
    Real.log (3 + |γ|) / 2 - 5 / 2 ≤ (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re := by
  set s : ℂ := 2 + (γ : ℂ) * I with hsdef
  set z : ℂ := s / 2 with hzdef
  have hsre : s.re = 2 := by simp [hsdef]
  have hsim : s.im = γ := by simp [hsdef]
  have hzre : z.re = 1 := by rw [hzdef, Complex.div_ofNat_re, hsre]; norm_num
  have hzim : z.im = γ / 2 := by rw [hzdef, Complex.div_ofNat_im, hsim]
  have hne0 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hc := congrArg Complex.re hm
    simp only [hzre, Complex.neg_re, Complex.natCast_re] at hc
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hne1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m hm
    have hc := congrArg Complex.re hm
    simp only [Complex.add_re, hzre, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hc
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hd1 := congrArg Complex.re (Complex.digamma_apply_add_one z hne0)
  have hd2 := congrArg Complex.re (Complex.digamma_apply_add_one (z + 1) hne1)
  rw [Complex.add_re] at hd1 hd2
  have hinv0 : (z⁻¹).re ≤ 1 := by
    rw [Complex.inv_re, Complex.normSq_apply, hzre, hzim]
    have hns : (1 : ℝ) ≤ 1 * 1 + γ / 2 * (γ / 2) := by nlinarith [sq_nonneg (γ / 2)]
    exact div_le_one_of_le₀ hns (by positivity)
  have hinv1 : ((z + 1)⁻¹).re ≤ 1 / 2 := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, hzre, hzim, Complex.one_re, Complex.one_im, add_zero]
    have hden_pos : (0 : ℝ) < (1 + 1) * (1 + 1) + γ / 2 * (γ / 2) := by
      nlinarith [sq_nonneg (γ / 2)]
    rw [div_le_div_iff₀ hden_pos two_pos]
    nlinarith [sq_nonneg (γ / 2)]
  set w : ℂ := z + 1 + 1
  have hwre : w.re = 3 := by simp [w, hzre]; ring
  have hwim : w.im = γ / 2 := by simp [w, hzim]
  have hwnorm_ge3 : (3 : ℝ) ≤ ‖w‖ := by
    calc (3 : ℝ) = w.re := hwre.symm
      _ ≤ ‖w‖ := Complex.re_le_norm w
  have hwpos : 0 < ‖w‖ := by linarith
  have hwnorm_lo : (3 + |γ|) / 3 ≤ ‖w‖ := by
    have hsq : ‖w‖ ^ 2 = 9 + γ ^ 2 / 4 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hwre, hwim]; ring
    have h9 : (3 + |γ|) ^ 2 ≤ (3 * ‖w‖) ^ 2 := by
      have habs2 : |γ| ^ 2 = γ ^ 2 := sq_abs γ
      have hdiff : (0 : ℝ) ≤ (5 / 4) * (|γ| - 12 / 5) ^ 2 :=
        mul_nonneg (by norm_num) (sq_nonneg (|γ| - 12 / 5))
      nlinarith [hsq, habs2, hdiff]
    have hle3 : 3 + |γ| ≤ 3 * ‖w‖ := by
      nlinarith [h9, abs_nonneg γ, hwpos]
    linarith
  have hstir := norm_digamma_sub_log_le_of_re_pos (z := w) (by rw [hwre]; norm_num) (by linarith)
  have hpsi_w : Real.log (3 + |γ|) - Real.log 3 - 1 ≤ (Complex.digamma w).re := by
    have hge : -(3 / ‖w‖) ≤ (Complex.digamma w - Complex.log w).re := by
      have habs : |(Complex.digamma w - Complex.log w).re| ≤ 3 / ‖w‖ :=
        (Complex.abs_re_le_norm _).trans hstir
      exact (abs_le.mp habs).1
    rw [Complex.sub_re, Complex.log_re] at hge
    have hlog_ge : Real.log (3 + |γ|) - Real.log 3 ≤ Real.log ‖w‖ := by
      rw [← Real.log_div (by positivity) (by norm_num)]
      exact Real.log_le_log (by positivity) hwnorm_lo
    have hdiv_le1 : 3 / ‖w‖ ≤ 1 := div_le_one_of_le₀ hwnorm_ge3 hwpos.le
    linarith
  have h3pi_lt : Real.log 3 + Real.log Real.pi ≤ 5 / 2 := by
    rw [← Real.log_mul (by norm_num) Real.pi_pos.ne']
    have hpi_hi : Real.pi < 3.15 := Real.pi_lt_d2
    have hexp_lo : (2.71 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hexp5 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
      rw [sq, ← Real.exp_add, ← Real.exp_nat_mul]; congr 1; norm_num
    have hpow5 : (3 * 3.15 : ℝ) ^ 2 < (2.71 : ℝ) ^ 5 := by norm_num
    have hsq_lt : (3 * Real.pi) ^ 2 < Real.exp (5 / 2) ^ 2 := by
      have hp1 : (3 * Real.pi) ^ 2 < (3 * 3.15) ^ 2 :=
        pow_lt_pow_left₀ (by linarith) (by positivity) two_ne_zero
      have hp2 : (2.71 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
        pow_lt_pow_left₀ hexp_lo (by norm_num) (by norm_num)
      linarith [hexp5]
    have hlt_exp : 3 * Real.pi < Real.exp (5 / 2) := by
      nlinarith [hsq_lt, Real.pi_pos, Real.exp_pos (5 / 2)]
    have hlog := Real.log_lt_log (by positivity) hlt_exp
    rw [Real.log_exp] at hlog
    exact hlog.le
  have hG : logDeriv Complex.Gammaℝ s =
      Complex.digamma z / 2 - ((Real.log Real.pi : ℝ) : ℂ) / 2 :=
    RHTower.logDeriv_Gammaℝ_digamma (by rw [hsre]; norm_num)
  change _ ≤ (logDeriv Complex.Gammaℝ s).re
  rw [hG]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith [hd1, hd2, hinv0, hinv1, hpsi_w, h3pi_lt]

/-- **All-height two-sided shifted-Gamma cost sandwich at `s = 2`.** Every conjugate shifted
archimedean pair `(Γ_ℝ(2 + iγ), Γ_ℝ(2 − iγ))` satisfies
`log(3 + |γ|) − 5 ≤ Re(logDeriv Γ_ℝ(2 + iγ) + logDeriv Γ_ℝ(2 − iγ)) ≤ log(3 + |γ|) + 1/2`
for all `γ ∈ ℝ`. -/
theorem re_logDeriv_Gammaℝ_pair_two_sandwich (γ : ℝ) :
    Real.log (3 + |γ|) - 5 ≤
      (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
        (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ∧
    (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
      (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤
      Real.log (3 + |γ|) + 1 / 2 := by
  have he_m : (2 : ℂ) - (γ : ℂ) * I = 2 + ((-γ : ℝ) : ℂ) * I := by push_cast; ring
  have hlo_p := re_logDeriv_Gammaℝ_two_shift_ge γ
  have hlo_m : Real.log (3 + |γ|) / 2 - 5 / 2 ≤
      (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re := by
    rw [he_m]
    simpa [abs_neg] using re_logDeriv_Gammaℝ_two_shift_ge (-γ)
  have hhi_p : (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 :=
    by simpa using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := γ) (by norm_num) le_rfl
  have hhi_m : (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 := by
    rw [he_m]
    simpa [abs_neg] using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := -γ) (by norm_num) le_rfl
  exact ⟨by linarith, by linarith⟩

/-- Degree-`K` Fejér shift operator
`(K + 1) φ(u) + ∑_{k ∈ Icc 1 K} (K + 1 − k) (φ(u + kγ) + φ(u − kγ))`. -/
def fejerShift (K : ℕ) (γ : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ((K + 1 : ℕ) : ℝ) * φ u +
    ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * (φ (u + (k : ℝ) * γ) + φ (u - (k : ℝ) * γ))

private theorem sum_fejer_triangle_iem :
    ∀ (K : ℕ) (f : ℝ → ℝ),
      ∑ p ∈ Finset.range (K + 1), ∑ q ∈ Finset.range (K + 1), f ((p : ℝ) - (q : ℝ)) =
        ((K + 1 : ℕ) : ℝ) * f 0 +
          ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * (f (k : ℝ) + f (-(k : ℝ)))
  | 0, f => by simp
  | K + 1, f => by
      have ih := sum_fejer_triangle_iem K f
      have hstep_M : ∀ M : ℕ,
          ∑ p ∈ Finset.range (M + 1), ∑ q ∈ Finset.range (M + 1), f ((p : ℝ) - (q : ℝ)) =
            (∑ p ∈ Finset.range M, ∑ q ∈ Finset.range M, f ((p : ℝ) - (q : ℝ))) +
              f 0 +
              ∑ p ∈ Finset.range M, (f ((M : ℝ) - (p : ℝ)) + f ((p : ℝ) - (M : ℝ))) := by
        intro M
        rw [Finset.sum_range_succ]
        simp_rw [Finset.sum_range_succ]
        rw [Finset.sum_add_distrib, sub_self, Finset.sum_add_distrib]
        ring
      have hlhs : ∑ p ∈ Finset.range (K + 2), ∑ q ∈ Finset.range (K + 2), f ((p : ℝ) - (q : ℝ)) =
          (∑ p ∈ Finset.range (K + 1), ∑ q ∈ Finset.range (K + 1), f ((p : ℝ) - (q : ℝ))) +
            f 0 +
            ∑ p ∈ Finset.range (K + 1),
              (f (((K + 1 : ℕ) : ℝ) - (p : ℝ)) + f ((p : ℝ) - ((K + 1 : ℕ) : ℝ))) :=
        hstep_M (K + 1)
      have hbij : ∑ p ∈ Finset.range (K + 1),
          (f (((K + 1 : ℕ) : ℝ) - (p : ℝ)) + f ((p : ℝ) - ((K + 1 : ℕ) : ℝ))) =
          ∑ k ∈ Finset.Icc 1 (K + 1), (f (k : ℝ) + f (-(k : ℝ))) := by
        refine Finset.sum_nbij' (fun p => K + 1 - p) (fun k => K + 1 - k)
          (fun p hp => by
            have := Finset.mem_range.mp hp
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          (fun k hk => by
            have := Finset.mem_Icc.mp hk
            exact Finset.mem_range.mpr (by omega))
          (fun p hp => by have := Finset.mem_range.mp hp; omega)
          (fun k hk => by have := Finset.mem_Icc.mp hk; omega)
          fun p hp => ?_
        have hp_le : p ≤ K + 1 := (Finset.mem_range.mp hp).le
        have hc1 : ((K + 1 - p : ℕ) : ℝ) = ((K + 1 : ℕ) : ℝ) - (p : ℝ) := Nat.cast_sub hp_le
        rw [hc1, show -(((K + 1 : ℕ) : ℝ) - (p : ℝ)) = (p : ℝ) - ((K + 1 : ℕ) : ℝ) by ring]
      have hIcc_ins : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot_mem : K + 1 ∉ Finset.Icc 1 K := by simp
      have hrhs : ((K + 2 : ℕ) : ℝ) * f 0 +
          ∑ k ∈ Finset.Icc 1 (K + 1), ((K + 2 - k : ℕ) : ℝ) * (f (k : ℝ) + f (-(k : ℝ))) =
          (((K + 1 : ℕ) : ℝ) * f 0 +
            ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * (f (k : ℝ) + f (-(k : ℝ)))) +
          f 0 +
          ∑ k ∈ Finset.Icc 1 (K + 1), (f (k : ℝ) + f (-(k : ℝ))) := by
        rw [hIcc_ins, Finset.sum_insert hnot_mem, Finset.sum_insert hnot_mem]
        have htop : ((K + 2 - (K + 1) : ℕ) : ℝ) = 1 := by
          rw [show K + 2 - (K + 1) = 1 by omega]; norm_num
        have hstep : ∀ k ∈ Finset.Icc 1 K,
            ((K + 2 - k : ℕ) : ℝ) * (f (k : ℝ) + f (-(k : ℝ))) =
              ((K + 1 - k : ℕ) : ℝ) * (f (k : ℝ) + f (-(k : ℝ))) +
                (f (k : ℝ) + f (-(k : ℝ))) := by
          intro k hk
          have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
          have hsub : K + 2 - k = (K + 1 - k) + 1 := by omega
          rw [hsub, Nat.cast_succ]; ring
        rw [htop, Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
        push_cast; ring
      rw [hlhs, ih, hbij, hrhs]

private theorem sum_fejer_weights_iem (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) = (K : ℝ) * ((K + 1 : ℕ) : ℝ) / 2 := by
  have h := sum_fejer_triangle_iem K (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  have h2 : ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * ((1 : ℝ) + 1) =
      2 * ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [h2] at h
  have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h ⊢
  linarith

/-- **Bochner positivity preservation under degree-`K` Fejér height coupling.** For any
`IsEvenPosDef φ`, `K : ℕ`, and `γ ∈ ℝ`, `fejerShift K γ φ` is even and positive definite. -/
theorem IsEvenPosDef.fejerShift {φ : ℝ → ℝ} (hφ : IsEvenPosDef φ) (K : ℕ) (γ : ℝ) :
    IsEvenPosDef (GaloisForLFunctions.ArithmeticCorrespondencePositivity.fejerShift K γ φ) where
  even u := by
    unfold GaloisForLFunctions.ArithmeticCorrespondencePositivity.fejerShift
    rw [hφ.even]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have h1 : -u + (k : ℝ) * γ = -(u - (k : ℝ) * γ) := by ring
    have h2 : -u - (k : ℝ) * γ = -(u + (k : ℝ) * γ) := by ring
    rw [h1, h2, hφ.even, hφ.even, add_comm]
  posDef n x c := by
    let e := finProdFinEquiv (m := K + 1) (n := n)
    have hbig := hφ.posDef ((K + 1) * n)
      (fun idx => x (e.symm idx).2 + ((e.symm idx).1.val : ℝ) * γ)
      (fun idx => c (e.symm idx).2)
    have hreindex : (∑ idx₁ : Fin ((K + 1) * n), ∑ idx₂ : Fin ((K + 1) * n),
        c (e.symm idx₁).2 * c (e.symm idx₂).2 *
          φ ((x (e.symm idx₁).2 + ((e.symm idx₁).1.val : ℝ) * γ) -
            (x (e.symm idx₂).2 + ((e.symm idx₂).1.val : ℝ) * γ))) =
        ∑ i : Fin n, ∑ j : Fin n, c i * c j *
          GaloisForLFunctions.ArithmeticCorrespondencePositivity.fejerShift K γ φ (x i - x j) := by
      rw [← e.sum_comp]
      simp_rw [← e.sum_comp, e.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcomm1 : ∀ p : Fin (K + 1),
          (∑ q : Fin (K + 1), ∑ j : Fin n,
            c i * c j * φ ((x i + (p.val : ℝ) * γ) - (x j + (q.val : ℝ) * γ))) =
          ∑ j : Fin n, ∑ q : Fin (K + 1),
            c i * c j * φ ((x i + (p.val : ℝ) * γ) - (x j + (q.val : ℝ) * γ)) :=
        fun _ => Finset.sum_comm
      rw [Finset.sum_congr rfl fun p _ => hcomm1 p, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [← Finset.mul_sum]
      congr 1
      have hq_range : ∀ p : Fin (K + 1),
          (∑ q : Fin (K + 1), φ ((x i + (p.val : ℝ) * γ) - (x j + (q.val : ℝ) * γ))) =
          ∑ q ∈ Finset.range (K + 1), φ ((x i + (p.val : ℝ) * γ) - (x j + (q : ℝ) * γ)) :=
        fun p => Fin.sum_univ_eq_sum_range
          (fun q : ℕ => φ ((x i + (p.val : ℝ) * γ) - (x j + (q : ℝ) * γ))) (K + 1)
      rw [Finset.sum_congr rfl fun p _ => hq_range p,
          Fin.sum_univ_eq_sum_range
            (fun p : ℕ => ∑ q ∈ Finset.range (K + 1),
              φ ((x i + (p : ℝ) * γ) - (x j + (q : ℝ) * γ))) (K + 1)]
      have harg : ∀ p q : ℕ,
          φ ((x i + (p : ℝ) * γ) - (x j + (q : ℝ) * γ)) =
            φ ((x i - x j) + ((p : ℝ) - (q : ℝ)) * γ) :=
        fun p q => congrArg φ (by ring)
      simp_rw [harg]
      have htri := sum_fejer_triangle_iem K (fun d => φ ((x i - x j) + d * γ))
      simpa [GaloisForLFunctions.ArithmeticCorrespondencePositivity.fejerShift, neg_mul,
        sub_eq_add_neg] using htri
    rwa [← hreindex]

/-- Degree-`K` Fejér shifted boundary pole product
`∏_{k ∈ Icc 1 K} shiftedPolePoly (kγ) s ^ ((K + 1 − k) κγ)`. -/
def fejerShiftedPoleProd (K κγ : ℕ) (γ : ℝ) (s : ℂ) : ℂ :=
  ∏ k ∈ Finset.Icc 1 K, shiftedPolePoly ((k : ℝ) * γ) s ^ ((K + 1 - k) * κγ)

/-- Degree-`K` Fejér coupled archimedean Gamma factor
`Γ_ℝ(s)^{(K + 1) d} ∏_{k ∈ Icc 1 K} (Γ_ℝ(s + ikγ) Γ_ℝ(s − ikγ))^{(K + 1 − k) d}`. -/
def fejerCoupledGamma (K d : ℕ) (γ : ℝ) (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ ((K + 1) * d) *
    ∏ k ∈ Finset.Icc 1 K,
      (Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)

/-- **Degree-`K` Fejér height-coupled completed positive system** at base ordinate `γ ∈ ℝ`, with
central pole order `κ₀`, Fejér shifted pole base `κγ`, and archimedean degree `d ≥ 1`. -/
structure FejerCoupledSystem (K κ₀ κγ d : ℕ) (γ : ℝ) (F Λ : ℂ → ℂ) : Prop where
  degree_pos : 1 ≤ d
  diffOn_F : DifferentiableOn ℂ F {s : ℂ | 1 < s.re}
  ne_zero_F : ∀ s : ℂ, 1 < s.re → F s ≠ 0
  posDef_neg_logDeriv : ∀ {σ : ℝ}, 1 < σ →
    IsEvenPosDef (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re)
  entire_Λ : Differentiable ℂ Λ
  orderOne_Λ : OrderOneEnvelope Λ
  sym_Λ : ∀ s : ℂ, Λ (1 - s) = Λ s
  conj_Λ : ∀ s : ℂ, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s)
  completed_eq : ∀ s : ℂ, 1 < s.re →
    Λ s = (s * (s - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ s * fejerCoupledGamma K d γ s * F s

/-- Degree-`K` Fejér Euler/Dirichlet carrier
`F_{K,γ}(s) = F(s)^{K + 1} ∏_{k ∈ Icc 1 K} (F(s + ikγ) F(s − ikγ))^{K + 1 − k}`. -/
def fejerCoupledF (K : ℕ) (F : ℂ → ℂ) (γ : ℝ) (s : ℂ) : ℂ :=
  F s ^ (K + 1) *
    ∏ k ∈ Finset.Icc 1 K,
      (F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)

/-- Degree-`K` Fejér completed carrier
`Λ_{K,γ}(s) = Λ(s)^{K + 1} ∏_{k ∈ Icc 1 K} (Λ(s + ikγ) Λ(s − ikγ))^{K + 1 − k}`. -/
def fejerCoupledΛ (K : ℕ) (Λ : ℂ → ℂ) (γ : ℝ) (s : ℂ) : ℂ :=
  Λ s ^ (K + 1) *
    ∏ k ∈ Finset.Icc 1 K,
      (Λ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Λ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)


private theorem differentiableAt_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (s : ℂ) (hd : ∀ i ∈ S, DifferentiableAt ℂ (g i) s) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ S, g i w) s := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact differentiableAt_const 1
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) = g a * fun w => ∏ i ∈ B, g i w :=
        funext fun w => Finset.prod_insert ha
      rw [heq]
      exact (hd a (Finset.mem_insert_self a B)).mul
        (ih fun i hi => hd i (Finset.mem_insert_of_mem hi))

private theorem differentiableOn_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (U : Set ℂ)
    (hd : ∀ i ∈ S, DifferentiableOn ℂ (g i) U) :
    DifferentiableOn ℂ (fun w => ∏ i ∈ S, g i w) U := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact differentiableOn_const 1
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) = g a * fun w => ∏ i ∈ B, g i w :=
        funext fun w => Finset.prod_insert ha
      rw [heq]
      exact (hd a (Finset.mem_insert_self a B)).mul
        (ih fun i hi => hd i (Finset.mem_insert_of_mem hi))

private theorem differentiable_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (hd : ∀ i ∈ S, Differentiable ℂ (g i)) :
    Differentiable ℂ (fun w => ∏ i ∈ S, g i w) := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact differentiable_const 1
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) = g a * fun w => ∏ i ∈ B, g i w :=
        funext fun w => Finset.prod_insert ha
      rw [heq]
      exact (hd a (Finset.mem_insert_self a B)).mul
        (ih fun i hi => hd i (Finset.mem_insert_of_mem hi))

private theorem analyticAt_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (z : ℂ) (hg : ∀ i ∈ S, AnalyticAt ℂ (g i) z) :
    AnalyticAt ℂ (fun w => ∏ i ∈ S, g i w) z := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact analyticAt_const
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) = g a * fun w => ∏ i ∈ B, g i w :=
        funext fun w => Finset.prod_insert ha
      rw [heq]
      exact (hg a (Finset.mem_insert_self a B)).mul
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private theorem logDeriv_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (s : ℂ)
    (hnz : ∀ i ∈ S, g i s ≠ 0) (hd : ∀ i ∈ S, DifferentiableAt ℂ (g i) s) :
    logDeriv (fun w => ∏ i ∈ S, g i w) s = ∑ i ∈ S, logDeriv (g i) s := by
  induction S using Finset.induction_on with
  | empty => simp [logDeriv_apply]
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) =
          fun w => g a w * ∏ i ∈ B, g i w := funext fun w => Finset.prod_insert ha
      have hB_nz : (∏ i ∈ B, g i s) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => hnz i (Finset.mem_insert_of_mem hi)
      have hB_d : DifferentiableAt ℂ (fun w => ∏ i ∈ B, g i w) s :=
        differentiableAt_finset_prod_iem B g s fun i hi => hd i (Finset.mem_insert_of_mem hi)
      rw [heq,
          logDeriv_mul (f := g a) (g := fun w => ∏ i ∈ B, g i w) s
            (hnz a (Finset.mem_insert_self a B)) hB_nz
            (hd a (Finset.mem_insert_self a B)) hB_d,
          Finset.sum_insert ha,
          ih (fun i hi => hnz i (Finset.mem_insert_of_mem hi))
             (fun i hi => hd i (Finset.mem_insert_of_mem hi))]

private theorem orderOneEnvelope_pow_iem {f : ℂ → ℂ} (hf : OrderOneEnvelope f) :
    ∀ n : ℕ, OrderOneEnvelope (fun s => f s ^ n)
  | 0 => (orderOneEnvelope_const 1).congr fun s => by simp
  | n + 1 => ((orderOneEnvelope_pow_iem hf n).mul hf).congr fun s => by rw [pow_succ]

private theorem orderOneEnvelope_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (hg : ∀ i ∈ S, OrderOneEnvelope (g i)) :
    OrderOneEnvelope (fun s => ∏ i ∈ S, g i s) := by
  induction S using Finset.induction_on with
  | empty => exact (orderOneEnvelope_const 1).congr fun s => by simp
  | @insert a B ha ih =>
      exact ((hg a (Finset.mem_insert_self a B)).mul
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))).congr
        fun s => (Finset.prod_insert ha (f := fun i => g i s)).symm

private theorem analyticOrderAt_pow_iem {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    ∀ n : ℕ, analyticOrderAt (fun w => f w ^ n) z = n • analyticOrderAt f z
  | 0 => by
      have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
      simpa using hc.analyticOrderAt_eq_zero.mpr one_ne_zero
  | n + 1 => by
      have heq : (fun w => f w ^ (n + 1)) = (fun w => f w ^ n) * f :=
        funext fun w => pow_succ (f w) n
      have hfn : AnalyticAt ℂ (fun w => f w ^ n) z := hf.pow n
      rw [heq, analyticOrderAt_mul hfn hf, analyticOrderAt_pow_iem hf n, succ_nsmul]

private theorem analyticOrderAt_finset_prod_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (g : ι → ℂ → ℂ) (z : ℂ) (hg : ∀ i ∈ S, AnalyticAt ℂ (g i) z) :
    analyticOrderAt (fun w => ∏ i ∈ S, g i w) z = ∑ i ∈ S, analyticOrderAt (g i) z := by
  induction S using Finset.induction_on with
  | empty =>
      have hc : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
      simpa using hc.analyticOrderAt_eq_zero.mpr one_ne_zero
  | @insert a B ha ih =>
      have heq : (fun w => ∏ i ∈ insert a B, g i w) = g a * fun w => ∏ i ∈ B, g i w :=
        funext fun w => Finset.prod_insert ha
      have hB_an : AnalyticAt ℂ (fun w => ∏ i ∈ B, g i w) z :=
        analyticAt_finset_prod_iem B g z fun i hi => hg i (Finset.mem_insert_of_mem hi)
      rw [heq, analyticOrderAt_mul (hg a (Finset.mem_insert_self a B)) hB_an,
          Finset.sum_insert ha,
          ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

private theorem enat_sum_ne_top_and_toNat_iem {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → ℕ∞) (hnt : ∀ i ∈ S, a i ≠ ⊤) :
    (∑ i ∈ S, a i) ≠ ⊤ ∧ (∑ i ∈ S, a i).toNat = ∑ i ∈ S, (a i).toNat := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x B hx ih =>
      obtain ⟨hB_nt, hB_to⟩ := ih fun i hi => hnt i (Finset.mem_insert_of_mem hi)
      have hx_nt : a x ≠ ⊤ := hnt x (Finset.mem_insert_self x B)
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      refine ⟨?_, ?_⟩
      · obtain ⟨nx, hnx⟩ := ENat.ne_top_iff_exists.mp hx_nt
        obtain ⟨nB, hnB⟩ := ENat.ne_top_iff_exists.mp hB_nt
        rw [← hnx, ← hnB, ← Nat.cast_add]
        exact ENat.coe_ne_top _
      · rw [ENat.toNat_add hx_nt hB_nt, hB_to]

private theorem logDeriv_comp_add_const_iem {f : ℂ → ℂ} {s c : ℂ}
    (hf : DifferentiableAt ℂ f (s + c)) :
    logDeriv (fun w : ℂ => f (w + c)) s = logDeriv f (s + c) := by
  have hd : HasDerivAt (fun w : ℂ => f (w + c)) (deriv f (s + c) * 1) s :=
    hf.hasDerivAt.comp s ((hasDerivAt_id s).add_const c)
  rw [logDeriv_apply, logDeriv_apply, hd.deriv, mul_one]

private theorem logDeriv_comp_sub_const_iem {f : ℂ → ℂ} {s c : ℂ}
    (hf : DifferentiableAt ℂ f (s - c)) :
    logDeriv (fun w : ℂ => f (w - c)) s = logDeriv f (s - c) := by
  have heq : (fun w : ℂ => f (w - c)) = fun w : ℂ => f (w + -c) :=
    funext fun w => congrArg f (sub_eq_add_neg w c)
  have hs : s + -c = s - c := (sub_eq_add_neg s c).symm
  rw [heq, logDeriv_comp_add_const_iem (by rwa [hs]), hs]

private theorem shiftedPolePoly_ne_zero_of_one_lt_re_iem (δ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    shiftedPolePoly δ s ≠ 0 := by
  unfold shiftedPolePoly
  have h1 := sq_add_sq_eq_mul_I_aux s 0 δ
  simp only [Complex.ofReal_zero, sub_zero, zero_add, zero_sub] at h1
  have h2 := sq_add_sq_eq_mul_I_aux s 1 δ
  simp only [Complex.ofReal_one] at h2
  rw [h1, h2]
  refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
    (mul_ne_zero (fun h => ?_) (fun h => ?_)) <;>
  · have := congrArg Complex.re h; simp at this; linarith

namespace FejerCoupledSystem

variable {K κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}

theorem ne_zero_of_one_lt_re (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) {s : ℂ} (hs : 1 < s.re) :
    Λ s ≠ 0 := by
  rw [hFC.completed_eq s hs]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hsp : fejerShiftedPoleProd K κγ γ s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      pow_ne_zero _ (shiftedPolePoly_ne_zero_of_one_lt_re_iem ((k : ℝ) * γ) hs)
  have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓ_prod : fejerCoupledGamma K d γ s ≠ 0 := by
    unfold fejerCoupledGamma
    refine mul_ne_zero (pow_ne_zero _ hΓ0) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    exact pow_ne_zero _ (mul_ne_zero
      (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
      (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)))
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero κ₀ (mul_ne_zero hs0 hs1)) hsp) hΓ_prod)
    (hFC.ne_zero_F s hs)

theorem two_ne_zero (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) : Λ 2 ≠ 0 :=
  hFC.ne_zero_of_one_lt_re (by norm_num)

theorem zero_re_mem_Icc (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) {ρ : ℂ} (hρ : Λ ρ = 0) :
    0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 < (1 - ρ).re := by simp; linarith
    exact hFC.ne_zero_of_one_lt_re h1 (by rw [hFC.sym_Λ, hρ])
  · by_contra hgt
    rw [not_le] at hgt
    exact hFC.ne_zero_of_one_lt_re hgt hρ

theorem analyticOnNhd_univ (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) : AnalyticOnNhd ℂ Λ univ :=
  hFC.entire_Λ.differentiableOn.analyticOnNhd isOpen_univ

theorem orderAt_ne_top (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) (z : ℂ) :
    analyticOrderAt Λ z ≠ ⊤ :=
  hFC.analyticOnNhd_univ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ 2) (mem_univ z)
    (by rw [(hFC.analyticOnNhd_univ 2 (mem_univ 2)).analyticOrderAt_eq_zero.mpr hFC.two_ne_zero]
        exact ENat.zero_ne_top)

theorem eq_zero_of_one_le_order_toNat (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) {ρ : ℂ}
    (hm : 1 ≤ (analyticOrderAt Λ ρ).toNat) : Λ ρ = 0 := by
  by_contra hnz
  rw [(hFC.analyticOnNhd_univ ρ (mem_univ ρ)).analyticOrderAt_eq_zero.mpr hnz] at hm
  simp at hm

theorem neg_logDeriv_F_eq (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv F s =
      (κ₀ : ℂ) * (1 / s + 1 / (s - 1)) +
      (∑ k ∈ Finset.Icc 1 K,
        (((K + 1 - k) * κγ : ℕ) : ℂ) * logDeriv (shiftedPolePoly ((k : ℝ) * γ)) s) +
      (((K + 1) * d : ℕ) : ℂ) * logDeriv Complex.Gammaℝ s +
      (∑ k ∈ Finset.Icc 1 K,
        (((K + 1 - k) * d : ℕ) : ℂ) *
          (logDeriv Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
            logDeriv Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I))) -
      logDeriv Λ s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Λ =ᶠ[𝓝 s] fun w =>
      (w * (w - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ w * fejerCoupledGamma K d γ w * F w :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) fun w hw => hFC.completed_eq w hw
  have hΛ_ld : logDeriv Λ s =
      logDeriv (fun w =>
        (w * (w - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ w * fejerCoupledGamma K d γ w * F w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hq0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  have hqd : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1)) s := by fun_prop
  have hsp_nz : fejerShiftedPoleProd K κγ γ s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      pow_ne_zero _ (shiftedPolePoly_ne_zero_of_one_lt_re_iem ((k : ℝ) * γ) hs)
  have hsp_d_at : ∀ k : ℕ, DifferentiableAt ℂ (shiftedPolePoly ((k : ℝ) * γ)) s :=
    fun k => by unfold shiftedPolePoly; fun_prop
  have hsp_d : DifferentiableAt ℂ (fejerShiftedPoleProd K κγ γ) s := by
    unfold fejerShiftedPoleProd
    exact differentiableAt_finset_prod_iem (Finset.Icc 1 K)
      (fun k w => shiftedPolePoly ((k : ℝ) * γ) w ^ ((K + 1 - k) * κγ)) s
      fun k _ => (hsp_d_at k).fun_pow _
  have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s :=
    GaloisForLFunctions.differentiableAt_Gammaℝ (by linarith)
  have hΓp_nz : ∀ k : ℕ, Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) ≠ 0 :=
    fun _ => Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΓm_nz : ∀ k : ℕ, Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) ≠ 0 :=
    fun _ => Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΓp_d_at : ∀ k : ℕ, DifferentiableAt ℂ Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) :=
    fun _ => GaloisForLFunctions.differentiableAt_Gammaℝ (by simp; linarith)
  have hΓm_d_at : ∀ k : ℕ, DifferentiableAt ℂ Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) :=
    fun _ => GaloisForLFunctions.differentiableAt_Gammaℝ (by simp; linarith)
  have hΓpair_d : ∀ k : ℕ, DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) s :=
    fun k => ((hΓp_d_at k).comp s (differentiableAt_id.add_const _)).mul
      ((hΓm_d_at k).comp s (differentiableAt_id.sub_const _))
  have hcG_nz : fejerCoupledGamma K d γ s ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hΓ0) (Finset.prod_ne_zero_iff.mpr fun k _ =>
      pow_ne_zero _ (mul_ne_zero (hΓp_nz k) (hΓm_nz k)))
  have hcG_d : DifferentiableAt ℂ (fejerCoupledGamma K d γ) s := by
    unfold fejerCoupledGamma
    exact (hΓd.fun_pow _).mul
      (differentiableAt_finset_prod_iem (Finset.Icc 1 K)
        (fun k w => (Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)) s
        fun k _ => (hΓpair_d k).fun_pow _)
  have hFd : DifferentiableAt ℂ F s := (hFC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs)
  have hq_ld : logDeriv (fun w : ℂ => w * (w - 1)) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s hs0 hs1
          differentiableAt_id (differentiableAt_id.sub_const 1),
        logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'', one_div, one_div]
  have hsp_ld : logDeriv (fejerShiftedPoleProd K κγ γ) s =
      ∑ k ∈ Finset.Icc 1 K,
        (((K + 1 - k) * κγ : ℕ) : ℂ) * logDeriv (shiftedPolePoly ((k : ℝ) * γ)) s := by
    unfold fejerShiftedPoleProd
    rw [logDeriv_finset_prod_iem (Finset.Icc 1 K)
          (fun k w => shiftedPolePoly ((k : ℝ) * γ) w ^ ((K + 1 - k) * κγ)) s
          (fun k _ => pow_ne_zero _ (shiftedPolePoly_ne_zero_of_one_lt_re_iem ((k : ℝ) * γ) hs))
          (fun k _ => (hsp_d_at k).fun_pow _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact logDeriv_fun_pow (hsp_d_at k) ((K + 1 - k) * κγ)
  have hcG_ld : logDeriv (fejerCoupledGamma K d γ) s =
      (((K + 1) * d : ℕ) : ℂ) * logDeriv Complex.Gammaℝ s +
        ∑ k ∈ Finset.Icc 1 K,
          (((K + 1 - k) * d : ℕ) : ℂ) *
            (logDeriv Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
              logDeriv Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) := by
    unfold fejerCoupledGamma
    have hprod_nz : (∏ k ∈ Finset.Icc 1 K,
        (Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (mul_ne_zero (hΓp_nz k) (hΓm_nz k))
    have hprod_d : DifferentiableAt ℂ (fun w => ∏ k ∈ Finset.Icc 1 K,
        (Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)) s :=
      differentiableAt_finset_prod_iem (Finset.Icc 1 K)
        (fun k w => (Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)) s
        fun k _ => (hΓpair_d k).fun_pow _
    rw [logDeriv_mul (f := fun w => Complex.Gammaℝ w ^ ((K + 1) * d))
          (g := fun w => ∏ k ∈ Finset.Icc 1 K,
            (Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
              Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d))
          s (pow_ne_zero _ hΓ0) hprod_nz (hΓd.fun_pow _) hprod_d,
        logDeriv_fun_pow hΓd ((K + 1) * d),
        logDeriv_finset_prod_iem (Finset.Icc 1 K)
          (fun k w => (Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d)) s
          (fun k _ => pow_ne_zero _ (mul_ne_zero (hΓp_nz k) (hΓm_nz k)))
          (fun k _ => (hΓpair_d k).fun_pow _)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [logDeriv_fun_pow (hΓpair_d k) ((K + 1 - k) * d),
        logDeriv_mul
          (f := fun w => Complex.Gammaℝ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I))
          (g := fun w => Complex.Gammaℝ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I))
          s (hΓp_nz k) (hΓm_nz k)
          ((hΓp_d_at k).comp s (differentiableAt_id.add_const _))
          ((hΓm_d_at k).comp s (differentiableAt_id.sub_const _)),
        logDeriv_comp_add_const_iem (hΓp_d_at k),
        logDeriv_comp_sub_const_iem (hΓm_d_at k)]
  rw [hΛ_ld,
      logDeriv_mul
        (f := fun w => (w * (w - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ w *
          fejerCoupledGamma K d γ w)
        (g := F) s
        (mul_ne_zero (mul_ne_zero (pow_ne_zero κ₀ hq0) hsp_nz) hcG_nz) (hFC.ne_zero_F s hs)
        (((hqd.fun_pow κ₀).mul hsp_d).mul hcG_d) hFd,
      logDeriv_mul
        (f := fun w => (w * (w - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ w)
        (g := fejerCoupledGamma K d γ) s
        (mul_ne_zero (pow_ne_zero κ₀ hq0) hsp_nz) hcG_nz
        ((hqd.fun_pow κ₀).mul hsp_d) hcG_d,
      logDeriv_mul
        (f := fun w => (w * (w - 1)) ^ κ₀)
        (g := fejerShiftedPoleProd K κγ γ) s
        (pow_ne_zero κ₀ hq0) hsp_nz (hqd.fun_pow κ₀) hsp_d,
      logDeriv_fun_pow hqd κ₀, hq_ld, hsp_ld, hcG_ld]
  ring

end FejerCoupledSystem

/-- **Unconditional degree-`K` Fejér height coupling.** For any `CompletedPositiveSystem κ d F Λ`,
bandwidth `K : ℕ`, and ordinate `γ ∈ ℝ`, `(fejerCoupledF K F γ, fejerCoupledΛ K Λ γ)` forms a
`FejerCoupledSystem K ((K + 1) * κ) κ d γ`. -/
theorem CompletedPositiveSystem.fejerCouple {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (K : ℕ) (γ : ℝ) :
    FejerCoupledSystem K ((K + 1) * κ) κ d γ
      (fejerCoupledF K F γ) (fejerCoupledΛ K Λ γ) where
  degree_pos := hS.degree_pos
  diffOn_F := by
    unfold fejerCoupledF
    refine (hS.diffOn_F.pow (K + 1)).mul
      (differentiableOn_finset_prod_iem (Finset.Icc 1 K)
        (fun k s => (F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k))
        {s : ℂ | 1 < s.re} fun k _ => ?_)
    have hUp : MapsTo (fun s : ℂ => s + (((k : ℝ) * γ : ℝ) : ℂ) * I)
        {s : ℂ | 1 < s.re} {s : ℂ | 1 < s.re} :=
      fun s hs => by change 1 < (s + _).re; simp; exact hs
    have hUm : MapsTo (fun s : ℂ => s - (((k : ℝ) * γ : ℝ) : ℂ) * I)
        {s : ℂ | 1 < s.re} {s : ℂ | 1 < s.re} :=
      fun s hs => by change 1 < (s - _).re; simp; exact hs
    exact ((hS.diffOn_F.comp (differentiableOn_id.add_const _) hUp).mul
      (hS.diffOn_F.comp (differentiableOn_id.sub_const _) hUm)).pow (K + 1 - k)
  ne_zero_F := fun s hs => by
    unfold fejerCoupledF
    exact mul_ne_zero (pow_ne_zero _ (hS.ne_zero_F s hs))
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (mul_ne_zero
        (hS.ne_zero_F _ (by simp; exact hs))
        (hS.ne_zero_F _ (by simp; exact hs))))
  posDef_neg_logDeriv := fun {σ} hσ => by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    let φ : ℝ → ℝ := fun u => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re
    have hshift : IsEvenPosDef (fejerShift K γ φ) :=
      IsEvenPosDef.fejerShift (hS.posDef_neg_logDeriv hσ) K γ
    have heq : (fun u : ℝ =>
        (-logDeriv (fejerCoupledF K F γ) ((σ : ℂ) + (u : ℂ) * I)).re) = fejerShift K γ φ := by
      funext u
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I
      have hs : 1 < s.re := by simp [s]; exact hσ
      have hFd : DifferentiableAt ℂ F s := (hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs)
      have hFp_nz : ∀ k : ℕ, F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) ≠ 0 :=
        fun _ => hS.ne_zero_F _ (by simp [s]; exact hσ)
      have hFm_nz : ∀ k : ℕ, F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) ≠ 0 :=
        fun _ => hS.ne_zero_F _ (by simp [s]; exact hσ)
      have hFp_at : ∀ k : ℕ, DifferentiableAt ℂ F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) :=
        fun _ => (hS.diffOn_F _ (by simp [s]; exact hσ)).differentiableAt
          (hopen.mem_nhds (by simp [s]; exact hσ))
      have hFm_at : ∀ k : ℕ, DifferentiableAt ℂ F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) :=
        fun _ => (hS.diffOn_F _ (by simp [s]; exact hσ)).differentiableAt
          (hopen.mem_nhds (by simp [s]; exact hσ))
      have hpair_d : ∀ k : ℕ, DifferentiableAt ℂ
          (fun w : ℂ => F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) s :=
        fun k => ((hFp_at k).comp s (differentiableAt_id.add_const _)).mul
          ((hFm_at k).comp s (differentiableAt_id.sub_const _))
      have hprod_nz : (∏ k ∈ Finset.Icc 1 K,
          (F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (mul_ne_zero (hFp_nz k) (hFm_nz k))
      have hprod_d : DifferentiableAt ℂ (fun w => ∏ k ∈ Finset.Icc 1 K,
          (F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) s :=
        differentiableAt_finset_prod_iem (Finset.Icc 1 K)
          (fun k w => (F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) s
          fun k _ => (hpair_d k).fun_pow _
      unfold fejerCoupledF
      rw [logDeriv_mul (f := fun w => F w ^ (K + 1))
            (g := fun w => ∏ k ∈ Finset.Icc 1 K,
              (F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
                F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k))
            s (pow_ne_zero _ (hS.ne_zero_F s hs)) hprod_nz (hFd.fun_pow _) hprod_d,
          logDeriv_fun_pow hFd (K + 1),
          logDeriv_finset_prod_iem (Finset.Icc 1 K)
            (fun k w => (F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
              F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) s
            (fun k _ => pow_ne_zero _ (mul_ne_zero (hFp_nz k) (hFm_nz k)))
            (fun k _ => (hpair_d k).fun_pow _),
          neg_add, Complex.add_re]
      unfold fejerShift
      congr 1
      · have : -(((K + 1 : ℕ) : ℂ) * logDeriv F s) =
            (((K + 1 : ℕ) : ℝ) : ℂ) * (-logDeriv F s) := by push_cast; ring
        rw [this, Complex.re_ofReal_mul]
      · rw [← Finset.sum_neg_distrib, Complex.re_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [logDeriv_fun_pow (hpair_d k) (K + 1 - k),
            logDeriv_mul
              (f := fun w => F (w + (((k : ℝ) * γ : ℝ) : ℂ) * I))
              (g := fun w => F (w - (((k : ℝ) * γ : ℝ) : ℂ) * I))
              s (hFp_nz k) (hFm_nz k)
              ((hFp_at k).comp s (differentiableAt_id.add_const _))
              ((hFm_at k).comp s (differentiableAt_id.sub_const _)),
            logDeriv_comp_add_const_iem (hFp_at k),
            logDeriv_comp_sub_const_iem (hFm_at k)]
        have ep : s + (((k : ℝ) * γ : ℝ) : ℂ) * I =
            (σ : ℂ) + ((u + (k : ℝ) * γ : ℝ) : ℂ) * I := by dsimp [s]; push_cast; ring
        have em : s - (((k : ℝ) * γ : ℝ) : ℂ) * I =
            (σ : ℂ) + ((u - (k : ℝ) * γ : ℝ) : ℂ) * I := by dsimp [s]; push_cast; ring
        rw [ep, em]
        have hneg : -(((K + 1 - k : ℕ) : ℂ) *
            (logDeriv F ((σ : ℂ) + ((u + (k : ℝ) * γ : ℝ) : ℂ) * I) +
              logDeriv F ((σ : ℂ) + ((u - (k : ℝ) * γ : ℝ) : ℂ) * I))) =
            (((K + 1 - k : ℕ) : ℝ) : ℂ) *
              ((-logDeriv F ((σ : ℂ) + ((u + (k : ℝ) * γ : ℝ) : ℂ) * I)) +
                (-logDeriv F ((σ : ℂ) + ((u - (k : ℝ) * γ : ℝ) : ℂ) * I))) := by
          push_cast; ring
        rw [hneg, Complex.re_ofReal_mul, Complex.add_re]
    rwa [heq]
  entire_Λ := by
    unfold fejerCoupledΛ
    exact (hS.entire_Λ.pow (K + 1)).mul
      (differentiable_finset_prod_iem (Finset.Icc 1 K)
        (fun k s => (Λ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Λ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k))
        fun k _ =>
          ((hS.entire_Λ.comp (differentiable_id.add_const _)).mul
            (hS.entire_Λ.comp (differentiable_id.sub_const _))).pow _)
  orderOne_Λ := by
    unfold fejerCoupledΛ
    refine (orderOneEnvelope_pow_iem hS.orderOne_Λ (K + 1)).mul
      (orderOneEnvelope_finset_prod_iem (Finset.Icc 1 K) _ fun k _ => ?_)
    have hop : OrderOneEnvelope (fun s : ℂ => Λ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I)) :=
      (hS.orderOne_Λ.comp_affine 1 ((((k : ℝ) * γ : ℝ) : ℂ) * I)).congr
        fun s => congrArg Λ (by ring)
    have hom : OrderOneEnvelope (fun s : ℂ => Λ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) :=
      (hS.orderOne_Λ.comp_affine 1 (-((((k : ℝ) * γ : ℝ) : ℂ) * I))).congr
        fun s => congrArg Λ (by ring)
    exact orderOneEnvelope_pow_iem (hop.mul hom) (K + 1 - k)
  sym_Λ := fun s => by
    unfold fejerCoupledΛ
    rw [hS.sym_Λ s]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    have e1 : 1 - s + (((k : ℝ) * γ : ℝ) : ℂ) * I =
        1 - (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) := by ring
    have e2 : 1 - s - (((k : ℝ) * γ : ℝ) : ℂ) * I =
        1 - (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) := by ring
    rw [e1, e2, hS.sym_Λ, hS.sym_Λ, mul_comm]
  conj_Λ := fun s => by
    unfold fejerCoupledΛ
    simp only [map_mul, map_pow, map_prod, ← hS.conj_Λ]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    have e1 : starRingEnd ℂ s + (((k : ℝ) * γ : ℝ) : ℂ) * I =
        starRingEnd ℂ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I) := by simp
    have e2 : starRingEnd ℂ s - (((k : ℝ) * γ : ℝ) : ℂ) * I =
        starRingEnd ℂ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) := by simp; ring
    rw [e1, e2, mul_comm]
  completed_eq := fun s hs => by
    unfold fejerCoupledΛ fejerShiftedPoleProd fejerCoupledGamma fejerCoupledF
    have h0 : Λ s ^ (K + 1) =
        (s * (s - 1)) ^ ((K + 1) * κ) * Complex.Gammaℝ s ^ ((K + 1) * d) * F s ^ (K + 1) := by
      rw [hS.completed_eq s hs, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          Nat.mul_comm κ (K + 1), Nat.mul_comm d (K + 1)]
    have hterm : ∀ k ∈ Finset.Icc 1 K,
        (Λ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) * Λ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k) =
          shiftedPolePoly ((k : ℝ) * γ) s ^ ((K + 1 - k) * κ) *
          (Complex.Gammaℝ (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            Complex.Gammaℝ (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ ((K + 1 - k) * d) *
          (F (s + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            F (s - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k) := by
      intro k _
      set δ : ℝ := (k : ℝ) * γ
      have hp : 1 < (s + (δ : ℂ) * I).re := by simp; exact hs
      have hm : 1 < (s - (δ : ℂ) * I).re := by simp; exact hs
      have hsp_id : ((s + (δ : ℂ) * I) * (s + (δ : ℂ) * I - 1)) *
          ((s - (δ : ℂ) * I) * (s - (δ : ℂ) * I - 1)) = shiftedPolePoly δ s := by
        unfold shiftedPolePoly
        calc ((s + (δ : ℂ) * I) * (s + (δ : ℂ) * I - 1)) *
              ((s - (δ : ℂ) * I) * (s - (δ : ℂ) * I - 1))
            = (s ^ 2 - (δ : ℂ) ^ 2 * I ^ 2) * ((s - 1) ^ 2 - (δ : ℂ) ^ 2 * I ^ 2) := by ring
          _ = (s ^ 2 + (δ : ℂ) ^ 2) * ((s - 1) ^ 2 + (δ : ℂ) ^ 2) := by
              rw [Complex.I_sq]; ring
      have hpair : Λ (s + (δ : ℂ) * I) * Λ (s - (δ : ℂ) * I) =
          shiftedPolePoly δ s ^ κ *
            (Complex.Gammaℝ (s + (δ : ℂ) * I) * Complex.Gammaℝ (s - (δ : ℂ) * I)) ^ d *
            (F (s + (δ : ℂ) * I) * F (s - (δ : ℂ) * I)) := by
        rw [hS.completed_eq _ hp, hS.completed_eq _ hm]
        calc ((s + (δ : ℂ) * I) * (s + (δ : ℂ) * I - 1)) ^ κ *
              Complex.Gammaℝ (s + (δ : ℂ) * I) ^ d * F (s + (δ : ℂ) * I) *
              (((s - (δ : ℂ) * I) * (s - (δ : ℂ) * I - 1)) ^ κ *
                Complex.Gammaℝ (s - (δ : ℂ) * I) ^ d * F (s - (δ : ℂ) * I))
            = (((s + (δ : ℂ) * I) * (s + (δ : ℂ) * I - 1)) ^ κ *
                ((s - (δ : ℂ) * I) * (s - (δ : ℂ) * I - 1)) ^ κ) *
              (Complex.Gammaℝ (s + (δ : ℂ) * I) ^ d * Complex.Gammaℝ (s - (δ : ℂ) * I) ^ d) *
              (F (s + (δ : ℂ) * I) * F (s - (δ : ℂ) * I)) := by ring
          _ = shiftedPolePoly δ s ^ κ *
                (Complex.Gammaℝ (s + (δ : ℂ) * I) * Complex.Gammaℝ (s - (δ : ℂ) * I)) ^ d *
                (F (s + (δ : ℂ) * I) * F (s - (δ : ℂ) * I)) := by
              rw [← mul_pow, ← mul_pow, hsp_id]
      rw [hpair, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          Nat.mul_comm κ (K + 1 - k), Nat.mul_comm d (K + 1 - k)]
    rw [h0, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring

private theorem analyticOrderAt_comp_add_const_iem {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (z c : ℂ) :
    analyticOrderAt (fun w : ℂ => f (w + c)) z = analyticOrderAt f (z + c) := by
  have hg_an : AnalyticAt ℂ (fun w : ℂ => w + c) z := by fun_prop
  have hg_d : deriv (fun w : ℂ => w + c) z ≠ 0 := by
    rw [((hasDerivAt_id' z).add_const c).deriv]; exact one_ne_zero
  exact analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg_an hg_d

private theorem analyticOrderAt_comp_sub_const_iem {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z c : ℂ) :
    analyticOrderAt (fun w : ℂ => f (w - c)) z = analyticOrderAt f (z - c) := by
  have heq : (fun w : ℂ => f (w - c)) = fun w : ℂ => f (w + -c) :=
    funext fun w => congrArg f (sub_eq_add_neg w c)
  rw [heq, analyticOrderAt_comp_add_const_iem hf z (-c), ← sub_eq_add_neg]

/-- **Exact vanishing-order formula for `fejerCoupledΛ`.** -/
theorem CompletedPositiveSystem.orderAt_fejerCoupledΛ {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (K : ℕ) (γ : ℝ) (z : ℂ) :
    (analyticOrderAt (fejerCoupledΛ K Λ γ) z).toNat =
      (K + 1) * (analyticOrderAt Λ z).toNat +
        ∑ k ∈ Finset.Icc 1 K, (K + 1 - k) *
          ((analyticOrderAt Λ (z + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat +
            (analyticOrderAt Λ (z - (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat) := by
  have han : ∀ w : ℂ, AnalyticAt ℂ Λ w := fun w => hS.entire_Λ.analyticAt w
  have hprod_eq : fejerCoupledΛ K Λ γ =
      (fun w => Λ w ^ (K + 1)) *
        fun w => ∏ k ∈ Finset.Icc 1 K,
          (Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
            Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k) := rfl
  have hterm_an : ∀ k : ℕ, AnalyticAt ℂ
      (fun w => (Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) z :=
    fun k => (((hS.entire_Λ.comp (differentiable_id.add_const _)).mul
      (hS.entire_Λ.comp (differentiable_id.sub_const _))).pow _).analyticAt z
  have hprod_an : AnalyticAt ℂ (fun w => ∏ k ∈ Finset.Icc 1 K,
      (Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) z :=
    analyticAt_finset_prod_iem (Finset.Icc 1 K) _ z fun k _ => hterm_an k
  have hterm_ord : ∀ k : ℕ,
      analyticOrderAt
        (fun w => (Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) ^ (K + 1 - k)) z =
        (K + 1 - k) •
          (analyticOrderAt Λ (z + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
            analyticOrderAt Λ (z - (((k : ℝ) * γ : ℝ) : ℂ) * I)) := by
    intro k
    have hp_an : AnalyticAt ℂ (fun w => Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I)) z :=
      (hS.entire_Λ.comp (differentiable_id.add_const _)).analyticAt z
    have hm_an : AnalyticAt ℂ (fun w => Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) z :=
      (hS.entire_Λ.comp (differentiable_id.sub_const _)).analyticAt z
    have hpm_an : AnalyticAt ℂ
        (fun w => Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
          Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) z := hp_an.mul hm_an
    have hmul_eq : (fun w => Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I) *
        Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I)) =
        (fun w => Λ (w + (((k : ℝ) * γ : ℝ) : ℂ) * I)) *
          fun w => Λ (w - (((k : ℝ) * γ : ℝ) : ℂ) * I) := rfl
    rw [analyticOrderAt_pow_iem hpm_an, hmul_eq,
        analyticOrderAt_mul hp_an hm_an,
        analyticOrderAt_comp_add_const_iem hS.entire_Λ,
        analyticOrderAt_comp_sub_const_iem hS.entire_Λ]
  have hnsmul_nt : ∀ (n : ℕ) {e : ℕ∞}, e ≠ ⊤ → n • e ≠ ⊤ := by
    intro n e he
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp he
    rw [← hm, nsmul_eq_mul, ← Nat.cast_mul]
    exact ENat.coe_ne_top _
  have hnsmul_toNat : ∀ (n : ℕ) {e : ℕ∞}, e ≠ ⊤ → (n • e).toNat = n * e.toNat := by
    intro n e he
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp he
    rw [← hm, nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_coe, ENat.toNat_coe]
  have hpair_nt : ∀ k : ℕ,
      analyticOrderAt Λ (z + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
        analyticOrderAt Λ (z - (((k : ℝ) * γ : ℝ) : ℂ) * I) ≠ ⊤ := by
    intro k
    obtain ⟨m₁, hm₁⟩ := ENat.ne_top_iff_exists.mp (hS.orderAt_ne_top _)
    obtain ⟨m₂, hm₂⟩ := ENat.ne_top_iff_exists.mp (hS.orderAt_ne_top _)
    rw [← hm₁, ← hm₂, ← Nat.cast_add]; exact ENat.coe_ne_top _
  obtain ⟨hsum_nt, hsum_to⟩ := enat_sum_ne_top_and_toNat_iem (Finset.Icc 1 K)
    (fun k => (K + 1 - k) •
      (analyticOrderAt Λ (z + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
        analyticOrderAt Λ (z - (((k : ℝ) * γ : ℝ) : ℂ) * I)))
    (fun k _ => hnsmul_nt _ (hpair_nt k))
  have hord_all : analyticOrderAt (fejerCoupledΛ K Λ γ) z =
      (K + 1) • analyticOrderAt Λ z +
        ∑ k ∈ Finset.Icc 1 K, (K + 1 - k) •
          (analyticOrderAt Λ (z + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
            analyticOrderAt Λ (z - (((k : ℝ) * γ : ℝ) : ℂ) * I)) := by
    have hpow_an : AnalyticAt ℂ (fun w => Λ w ^ (K + 1)) z := (han z).pow (K + 1)
    rw [hprod_eq, analyticOrderAt_mul hpow_an hprod_an,
        analyticOrderAt_pow_iem (han z),
        analyticOrderAt_finset_prod_iem (Finset.Icc 1 K) _ z (fun k _ => hterm_an k),
        Finset.sum_congr rfl fun k _ => hterm_ord k]
  rw [hord_all, ENat.toNat_add (hnsmul_nt _ (hS.orderAt_ne_top z)) hsum_nt,
      hnsmul_toNat _ (hS.orderAt_ne_top z), hsum_to]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hnsmul_toNat _ (hpair_nt k),
      ENat.toNat_add (hS.orderAt_ne_top _) (hS.orderAt_ne_top _)]

/-- **Real-axis phase-collision formula for `fejerCoupledΛ` (`±ikγ ↦ 2 (K + 1 − k)`).** -/
theorem CompletedPositiveSystem.orderAt_fejerCoupledΛ_real {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (K : ℕ) (γ x : ℝ) :
    (analyticOrderAt (fejerCoupledΛ K Λ γ) (x : ℂ)).toNat =
      (K + 1) * (analyticOrderAt Λ (x : ℂ)).toNat +
        2 * ∑ k ∈ Finset.Icc 1 K, (K + 1 - k) *
          (analyticOrderAt Λ ((x : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat := by
  rw [CompletedPositiveSystem.orderAt_fejerCoupledΛ hS K γ (x : ℂ), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hconj_eq : (x : ℂ) - (((k : ℝ) * γ : ℝ) : ℂ) * I =
      starRingEnd ℂ ((x : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * I) := by simp; ring
  rw [hconj_eq, hS.orderAt_conj]
  ring

private theorem orderOneEnvelope_sub_const_iem (c : ℂ) :
    OrderOneEnvelope (fun s : ℂ => s - c) :=
  (RHTower.orderOneEnvelope_id.add (orderOneEnvelope_const (-c))).congr fun s => by ring

private theorem dslope_entire_and_orderOne_iem {f : ℂ → ℂ} {z₀ : ℂ}
    (hd : Differentiable ℂ f) (hf : OrderOneEnvelope f) (hz₀ : f z₀ = 0) :
    Differentiable ℂ (dslope f z₀) ∧
      OrderOneEnvelope (dslope f z₀) ∧
      ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := by
  have hD : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 z₀)).mpr
      hd.differentiableOn
  have hid : ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := fun s => by
    simpa [hz₀, smul_eq_mul] using sub_smul_dslope f z₀ s
  refine ⟨hD, ?_, hid⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  obtain ⟨C, _, hb⟩ := hf
  obtain ⟨D, _, hDb⟩ := orderOneEnvelope_const (B : ℂ)
  refine ⟨C + D, by linarith, fun z => ?_⟩
  by_cases hz : ‖z - z₀‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hBabs : B ≤ ‖(B : ℂ)‖ := by simpa using le_abs_self B
    exact (hB z hmem).trans (hBabs.trans ((hDb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : D ≤ C + D) z))))
  · have hn := congrArg norm (hid z)
    rw [norm_mul] at hn
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by
      have hz1 : 1 ≤ ‖z - z₀‖ := le_of_not_ge hz
      nlinarith [norm_nonneg (dslope f z₀ z)]
    exact hle.trans ((hb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : C ≤ C + D) z)))

private theorem exists_quotient_pow_sub_iem :
    ∀ (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ},
      Differentiable ℂ f → OrderOneEnvelope f →
      (m : ℕ∞) ≤ analyticOrderAt f z₀ →
      ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ OrderOneEnvelope Q ∧
        (∀ s : ℂ, (s - z₀) ^ m * Q s = f s) ∧
        analyticOrderAt f z₀ = (m : ℕ) + analyticOrderAt Q z₀ ∧
        (∀ w : ℂ, w ≠ z₀ → analyticOrderAt Q w = analyticOrderAt f w)
  | 0, f, _, hdf, hof, _ =>
      ⟨f, hdf, hof, fun s => by simp, by simp, fun _ _ => rfl⟩
  | m + 1, f, z₀, hdf, hof, hm => by
      have hf0 : f z₀ = 0 := by
        by_contra hnz
        rw [(hdf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hnz] at hm
        exact absurd hm (by simp)
      obtain ⟨hdg, hog, hg_eq⟩ := dslope_entire_and_orderOne_iem hdf hof hf0
      have hfeq : (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) = f :=
        funext fun s => by simpa using hg_eq s
      have han_lin : AnalyticAt ℂ ((fun x : ℂ => x - z₀) ^ 1) z₀ :=
        ((differentiable_id.sub_const z₀).pow 1).analyticAt z₀
      have hord_f : analyticOrderAt f z₀ = (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
        calc analyticOrderAt f z₀
            = analyticOrderAt (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) z₀ := by rw [hfeq]
          _ = (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
              rw [analyticOrderAt_mul han_lin (hdg.analyticAt z₀), analyticOrderAt_centeredMonomial]
      have hm' : (m : ℕ∞) ≤ analyticOrderAt (dslope f z₀) z₀ := by
        rw [hord_f] at hm
        rcases eq_top_or_lt_top (analyticOrderAt (dslope f z₀) z₀) with htop | hlt
        · rw [htop]; exact le_top
        · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
          rw [← hk] at hm ⊢; norm_cast at hm ⊢; omega
      obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_z₀, hQ_ord⟩ := exists_quotient_pow_sub_iem m hdg hog hm'
      refine ⟨Q, hdQ, hoQ, fun s => ?_, ?_, fun w hw => ?_⟩
      · calc (s - z₀) ^ (m + 1) * Q s
            = (s - z₀) * ((s - z₀) ^ m * Q s) := by rw [pow_succ]; ring
          _ = f s := by rw [hQ_eq s, hg_eq s]
      · have h1m : ((1 : ℕ) : ℕ∞) + (m : ℕ) = ((m + 1 : ℕ) : ℕ∞) := by norm_cast; omega
        rw [hord_f, hQ_z₀, ← add_assoc, h1m]
      · have han_w : AnalyticAt ℂ ((fun x : ℂ => x - z₀) ^ 1) w :=
          ((differentiable_id.sub_const z₀).pow 1).analyticAt w
        have hlin0 : analyticOrderAt ((fun x : ℂ => x - z₀) ^ 1) w = 0 :=
          han_w.analyticOrderAt_eq_zero.mpr (by simp [sub_ne_zero.mpr hw])
        have hord_prod_w : analyticOrderAt (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) w =
            analyticOrderAt (dslope f z₀) w := by
          rw [analyticOrderAt_mul han_w (hdg.analyticAt w), hlin0, zero_add]
        rw [hfeq] at hord_prod_w
        rw [hQ_ord w hw, hord_prod_w]

private theorem exists_quotient_prod_pow_iem :
    ∀ (L : List (ℂ × ℕ)) (f : ℂ → ℂ),
      (L.map Prod.fst).Nodup → Differentiable ℂ f → OrderOneEnvelope f →
      (∀ p ∈ L, (p.2 : ℕ∞) ≤ analyticOrderAt f p.1) →
      ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ OrderOneEnvelope Q ∧
        (∀ s : ℂ, (L.map (fun p => (s - p.1) ^ p.2)).prod * Q s = f s) ∧
        (∀ p ∈ L, analyticOrderAt f p.1 = (p.2 : ℕ) + analyticOrderAt Q p.1) ∧
        (∀ w : ℂ, w ∉ L.map Prod.fst → analyticOrderAt Q w = analyticOrderAt f w)
  | [], f, _, hdf, hof, _ =>
      ⟨f, hdf, hof, fun s => by simp, by simp, fun _ _ => rfl⟩
  | (r, m) :: ps, f, hnd, hdf, hof, hord => by
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨Q₁, hdQ₁, hoQ₁, hQ₁_eq, hQ₁_r, hQ₁_ord⟩ :=
        exists_quotient_pow_sub_iem m hdf hof (hord (r, m) (by simp))
      have hord₁ : ∀ p ∈ ps, (p.2 : ℕ∞) ≤ analyticOrderAt Q₁ p.1 := by
        intro p hp
        have hne : p.1 ≠ r := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [hQ₁_ord p.1 hne]
        exact hord p (List.mem_cons_of_mem _ hp)
      obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_in, hQ_out⟩ :=
        exists_quotient_prod_pow_iem ps Q₁ hnd.2 hdQ₁ hoQ₁ hord₁
      refine ⟨Q, hdQ, hoQ, fun s => ?_, fun p hp => ?_, fun w hw => ?_⟩
      · simp only [List.map_cons, List.prod_cons]
        rw [mul_assoc, hQ_eq s, hQ₁_eq s]
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hps
        · rw [hQ₁_r, hQ_out r hnd.1]
        · have hne : p.1 ≠ r := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨p, hps, rfl⟩)
          rw [← hQ₁_ord p.1 hne, hQ_in p hps]
      · simp only [List.map_cons, List.mem_cons, not_or] at hw
        rw [hQ_out w hw.2, hQ₁_ord w hw.1]

private theorem continuous_eq_of_mul_eq_off_finset_iem {g₁ g₂ P : ℂ → ℂ} (S : Finset ℂ)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hP : ∀ z : ℂ, z ∉ S → P z ≠ 0)
    (hmul : ∀ z : ℂ, g₁ z * P z = g₂ z * P z) :
    ∀ s : ℂ, g₁ s = g₂ s := by
  intro s
  have hU : ((S.erase s : Set ℂ)ᶜ) ∈ 𝓝 s :=
    (S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  have hev : g₁ =ᶠ[𝓝[≠] s] g₂ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz1 hz2
    have hzS : z ∉ S := fun hmem => hz1 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hz2, hmem⟩))
    exact mul_right_cancel₀ (hP z hzS) (hmul z)
  exact tendsto_nhds_unique (hg₁.continuousAt.continuousWithinAt.congr' hev)
    hg₂.continuousAt.continuousWithinAt

/-- **Zero-marginal-tax collided quartet contraction inside `FejerCoupledSystem K`.** -/
theorem FejerCoupledSystem.contractCollidedQuartet {K κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (hreal : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      FejerCoupledSystem K κ₀ κγ d γ (fun s => F s * coupledQuartetSymSquare a a γ s) Λc ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 ∧
      (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 =
        (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat ∧
      (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
        (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
      (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
        (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat) := by
  classical
  set x₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ)
  set x₂ : ℂ := ((1 / 2 - a : ℝ) : ℂ)
  set r₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₂ : ℂ := ((1 / 2 + a : ℝ) : ℂ) - (γ : ℂ) * I
  set r₃ : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₄ : ℂ := ((1 / 2 - a : ℝ) : ℂ) - (γ : ℂ) * I
  have hr₁_eq : r₁ = 1 / 2 + (a : ℂ) + (γ : ℂ) * I := by dsimp [r₁]; push_cast; ring
  have hr₁ : Λ r₁ = 0 := by rwa [hr₁_eq]
  have hr₂ : Λ r₂ = 0 := by
    have he : r₂ = starRingEnd ℂ r₁ := by dsimp [r₁, r₂]; simp [map_ofNat]; ring
    rw [he, hFC.conj_Λ, hr₁, map_zero]
  have hr₄ : Λ r₄ = 0 := by
    have he : r₄ = 1 - r₁ := by dsimp [r₁, r₄]; push_cast; ring
    rw [he, hFC.sym_Λ, hr₁]
  have hr₃ : Λ r₃ = 0 := by
    have he : r₃ = 1 - r₂ := by dsimp [r₂, r₃]; push_cast; ring
    rw [he, hFC.sym_Λ, hr₂]
  have hord_x₁ : (2 : ℕ∞) ≤ analyticOrderAt Λ x₁ := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hFC.orderAt_ne_top x₁)
    rw [← hk] at hreal ⊢; simp only [ENat.toNat_coe] at hreal; exact_mod_cast hreal
  have hord_x₂ : (2 : ℕ∞) ≤ analyticOrderAt Λ x₂ := by
    have hx₂_sym : x₂ = 1 - x₁ := by dsimp [x₁, x₂]; push_cast; ring
    have hcomp := RHTower.analyticOrderAt_comp_one_sub hFC.entire_Λ x₁
    rw [show (fun w => Λ (1 - w)) = Λ from funext hFC.sym_Λ] at hcomp
    rw [hx₂_sym, hcomp]; exact hord_x₁
  have hord_zero : ∀ {w : ℂ}, Λ w = 0 → (1 : ℕ∞) ≤ analyticOrderAt Λ w := by
    intro w hw
    have hne0 : analyticOrderAt Λ w ≠ 0 := fun hz =>
      ((hFC.entire_Λ.analyticAt w).analyticOrderAt_eq_zero.mp hz) hw
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hFC.orderAt_ne_top w)
    rcases eq_or_ne k 0 with rfl | hk0
    · exact absurd hk.symm hne0
    · rw [← hk]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hdistinct :
      x₁ ≠ x₂ ∧ x₁ ≠ r₁ ∧ x₁ ≠ r₂ ∧ x₁ ≠ r₃ ∧ x₁ ≠ r₄ ∧
      x₂ ≠ r₁ ∧ x₂ ≠ r₂ ∧ x₂ ≠ r₃ ∧ x₂ ≠ r₄ ∧
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₃ ≠ r₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp [x₁, x₂, r₁, r₂, r₃, r₄] at hre him
      first | linarith | exact hγ (by linarith)
  rcases hdistinct with
    ⟨hx12, hx1r1, hx1r2, hx1r3, hx1r4, hx2r1, hx2r2, hx2r3, hx2r4,
     hr12, hr13, hr14, hr23, hr24, hr34⟩
  let L : List (ℂ × ℕ) := [(x₁, 2), (x₂, 2), (r₁, 1), (r₂, 1), (r₃, 1), (r₄, 1)]
  have hnd : (L.map Prod.fst).Nodup := by
    simp [L, hx12, hx1r1, hx1r2, hx1r3, hx1r4, hx2r1, hx2r2, hx2r3, hx2r4,
      hr12, hr13, hr14, hr23, hr24, hr34]
  obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_in, hQ_out⟩ :=
    exists_quotient_prod_pow_iem L Λ hnd hFC.entire_Λ hFC.orderOne_Λ (fun p hp => by
      simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hord_x₁
      · exact hord_x₂
      · exact hord_zero hr₁
      · exact hord_zero hr₂
      · exact hord_zero hr₃
      · exact hord_zero hr₄)
  let D_poly : ℂ → ℂ := fun s => realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s
  let C_poly : ℂ → ℂ := fun s => (s - 1 / 2) ^ 4 * quartetCritPoly γ s
  have hReal_fac : ∀ s : ℂ, realPairPoly (1 / 2 + a) s = (s - x₁) * (s - x₂) := fun s => by
    unfold realPairPoly
    have hx₂' : (((1 - (1 / 2 + a) : ℝ) : ℂ)) = x₂ := by dsimp [x₂]; push_cast; ring
    rw [hx₂']
  have hOff_fac : ∀ s : ℂ, quartetOffPoly a γ s =
      (s - r₁) * (s - r₂) * (s - r₃) * (s - r₄) := fun s => by
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I_aux s (1 / 2 + a) γ, sq_add_sq_eq_mul_I_aux s (1 / 2 - a) γ]
    dsimp [r₁, r₂, r₃, r₄]; ring
  have hD_fac : ∀ s : ℂ, D_poly s =
      (s - x₁) ^ 2 * (s - x₂) ^ 2 * ((s - r₁) * (s - r₂) * (s - r₃) * (s - r₄)) := fun s => by
    dsimp [D_poly]; rw [hReal_fac, mul_pow, hOff_fac]
  have hQ_poly : ∀ s : ℂ, D_poly s * Q s = Λ s := fun s => by
    have h := hQ_eq s
    simp only [L, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one, mul_one] at h
    rw [hD_fac s]
    linear_combination h
  let Λc : ℂ → ℂ := fun s => Q s * C_poly s
  have hdC : Differentiable ℂ C_poly := by dsimp [C_poly]; unfold quartetCritPoly; fun_prop
  have hdΛc : Differentiable ℂ Λc := hdQ.mul hdC
  have ho_crit : OrderOneEnvelope (quartetCritPoly γ) := by
    let p₁ := orderOneEnvelope_sub_const_iem (1 / 2 + (γ : ℂ) * I)
    let p₂ := orderOneEnvelope_sub_const_iem (1 / 2 - (γ : ℂ) * I)
    refine ((p₁.mul p₂).mul (p₁.mul p₂)).congr fun s => ?_
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I_aux s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]; ring
  have hoΛc : OrderOneEnvelope Λc :=
    hoQ.mul ((orderOneEnvelope_pow_iem (orderOneEnvelope_sub_const_iem (1 / 2)) 4).mul ho_crit)
  have hrel : ∀ s : ℂ, Λc s * D_poly s = Λ s * C_poly s := fun s => by
    dsimp [Λc]; rw [← hQ_poly s]; ring
  let S_roots : Finset ℂ := {x₁, x₂, r₁, r₂, r₃, r₄}
  have hD_nz_off : ∀ z : ℂ, z ∉ S_roots → D_poly z ≠ 0 := by
    intro z hz
    simp only [S_roots, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [hD_fac z]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hz.1))
        (pow_ne_zero 2 (sub_ne_zero.mpr hz.2.1)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz.2.2.1)
        (sub_ne_zero.mpr hz.2.2.2.1)) (sub_ne_zero.mpr hz.2.2.2.2.1))
        (sub_ne_zero.mpr hz.2.2.2.2.2))
  have hsym_c : ∀ s : ℂ, Λc (1 - s) = Λc s := by
    refine continuous_eq_of_mul_eq_off_finset_iem S_roots
      (hdΛc.continuous.comp (by fun_prop)) hdΛc.continuous hD_nz_off fun z => ?_
    have hD_sym : D_poly z = D_poly (1 - z) := by
      dsimp [D_poly]; unfold realPairPoly quartetOffPoly; push_cast; ring
    have hC_sym : C_poly (1 - z) = C_poly z := by
      dsimp [C_poly]; unfold quartetCritPoly; ring
    rw [hD_sym, hrel (1 - z), hFC.sym_Λ z, hC_sym, ← hD_sym, ← hrel z]
  have hconj_c : ∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s) := by
    have hinv := continuous_eq_of_mul_eq_off_finset_iem S_roots
      (Complex.continuous_conj.comp (hdΛc.continuous.comp Complex.continuous_conj))
      hdΛc.continuous hD_nz_off fun z => by
        have hD_conj : starRingEnd ℂ (D_poly (starRingEnd ℂ z)) = D_poly z := by
          dsimp [D_poly]; unfold realPairPoly quartetOffPoly
          simp only [map_mul, map_add, map_pow, map_sub, Complex.conj_ofReal,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        have hC_conj : starRingEnd ℂ (C_poly (starRingEnd ℂ z)) = C_poly z := by
          dsimp [C_poly]; unfold quartetCritPoly; simp [map_ofNat]
        have h1 := congrArg (starRingEnd ℂ) (hrel (starRingEnd ℂ z))
        rw [map_mul (starRingEnd ℂ) (Λc (starRingEnd ℂ z)),
            map_mul (starRingEnd ℂ) (Λ (starRingEnd ℂ z)),
            hD_conj, hC_conj, hFC.conj_Λ z, Complex.conj_conj, ← hrel z] at h1
        simpa only [Function.comp_apply] using h1
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hQ_ntop : ∀ w : ℂ, analyticOrderAt Q w ≠ ⊤ := by
    intro w
    by_cases hw : w ∈ L.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      have hin := hQ_in p hp
      intro htop; rw [htop, add_top] at hin; exact hFC.orderAt_ne_top p.1 hin
    · rw [hQ_out w hw]; exact hFC.orderAt_ne_top w
  have hCrit_fac : ∀ s : ℂ, quartetCritPoly γ s =
      (s - (1 / 2 + (γ : ℂ) * I)) ^ 2 * (s - (1 / 2 - (γ : ℂ) * I)) ^ 2 := fun s => by
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I_aux s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]; ring
  have hC_nz_off_crit : ∀ w : ℂ, w.re ≠ 1 / 2 → C_poly w ≠ 0 := by
    intro w hw
    dsimp [C_poly]; rw [hCrit_fac w]
    refine mul_ne_zero (pow_ne_zero 4 (fun h => ?_))
      (mul_ne_zero (pow_ne_zero 2 (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_))) <;>
    · have := congrArg Complex.re h; simp at this; exact hw (by linarith)
  have hΛc_ord_off_crit : ∀ w : ℂ, w.re ≠ 1 / 2 → analyticOrderAt Λc w = analyticOrderAt Q w := by
    intro w hw
    have hΛc_eq : Λc = Q * C_poly := rfl
    rw [hΛc_eq, analyticOrderAt_mul (hdQ.analyticAt w) (hdC.analyticAt w),
        (hdC.analyticAt w).analyticOrderAt_eq_zero.mpr (hC_nz_off_crit w hw), add_zero]
  have hnot_mem_crit : ∀ w : ℂ, w.re = 1 / 2 → w ∉ L.map Prod.fst := by
    intro w hw hmem
    simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp [x₁, x₂, r₁, r₂, r₃, r₄] at hw; linarith)
  have hord_half : (analyticOrderAt Λc (1 / 2)).toNat =
      (analyticOrderAt Λ (1 / 2)).toNat + 4 := by
    have hΛc_eq : Λc = (Q * quartetCritPoly γ) * ((· - (1 / 2 : ℂ)) ^ 4) :=
      funext fun s => by dsimp [Λc, C_poly]; ring
    have hd_crit : Differentiable ℂ (quartetCritPoly γ) := by unfold quartetCritPoly; fun_prop
    have hcrit_nz : quartetCritPoly γ (1 / 2) ≠ 0 := by
      rw [hCrit_fac]
      refine mul_ne_zero (pow_ne_zero 2 (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_)) <;>
      · have := congrArg Complex.im h; simp at this; exact hγ (by linarith)
    have han_mon : AnalyticAt ℂ ((· - (1 / 2 : ℂ)) ^ 4) (1 / 2) :=
      ((differentiable_id.sub_const (1 / 2 : ℂ)).pow 4).analyticAt (1 / 2)
    have h1 : analyticOrderAt Λc (1 / 2) = analyticOrderAt Λ (1 / 2) + (4 : ℕ) := by
      rw [hΛc_eq,
          analyticOrderAt_mul ((hdQ.mul hd_crit).analyticAt _) han_mon,
          analyticOrderAt_mul (hdQ.analyticAt _) (hd_crit.analyticAt _),
          (hd_crit.analyticAt _).analyticOrderAt_eq_zero.mpr hcrit_nz, add_zero,
          hQ_out (1 / 2) (hnot_mem_crit (1 / 2) (by norm_num)),
          analyticOrderAt_centeredMonomial]
    rw [h1, ENat.toNat_add (hFC.orderAt_ne_top (1 / 2)) (ENat.coe_ne_top 4), ENat.toNat_coe]
  have hord_real : (analyticOrderAt Λc x₁).toNat + 2 = (analyticOrderAt Λ x₁).toNat := by
    have hx₁_re : x₁.re ≠ 1 / 2 := by simp [x₁]; linarith
    have hin := hQ_in (x₁, 2) (by simp [L])
    dsimp only at hin
    rw [← hΛc_ord_off_crit x₁ hx₁_re] at hin
    have hne : analyticOrderAt Λc x₁ ≠ ⊤ := by
      rw [hΛc_ord_off_crit x₁ hx₁_re]; exact hQ_ntop x₁
    rw [hin, ENat.toNat_add (ENat.coe_ne_top 2) hne, ENat.toNat_coe]; omega
  have hord_quart : (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
      (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
    rw [← hr₁_eq]
    have hr₁_re : r₁.re ≠ 1 / 2 := by simp [r₁]; linarith
    have hin := hQ_in (r₁, 1) (by simp [L])
    dsimp only at hin
    rw [← hΛc_ord_off_crit r₁ hr₁_re] at hin
    have hne : analyticOrderAt Λc r₁ ≠ ⊤ := by
      rw [hΛc_ord_off_crit r₁ hr₁_re]; exact hQ_ntop r₁
    rw [hin, ENat.toNat_add (ENat.coe_ne_top 1) hne, ENat.toNat_coe]; omega
  have hord_other : ∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
      (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat := by
    intro z hz0 hza1 hza2
    have hnot : z ∉ L.map Prod.fst := by
      intro hmem
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hza1 (by simp [x₁])
      · exact hza2 (by simp [x₂])
      · exact hza1 (by simp [r₁])
      · exact hza1 (by simp [r₂])
      · exact hza2 (by simp [r₃])
      · exact hza2 (by simp [r₄])
    rw [hΛc_ord_off_crit z hz0, hQ_out z hnot]
  have hP_nz : ∀ s : ℂ, 1 < s.re → realPairPoly (1 / 2 + a) s ≠ 0 := by
    intro s hs; refine mul_ne_zero (fun h => ?_) (fun h => ?_) <;>
    · have := congrArg Complex.re h; simp at this; linarith
  have hOff_nz : ∀ s : ℂ, 1 < s.re → quartetOffPoly a γ s ≠ 0 := by
    intro s hs
    rw [hOff_fac s]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_)) (fun h => ?_))
      (fun h => ?_) <;>
    · have := congrArg Complex.re h; simp [r₁, r₂, r₃, r₄] at this; linarith
  have hCrit_nz : ∀ s : ℂ, 1 < s.re → quartetCritPoly γ s ≠ 0 := by
    intro s hs; rw [hCrit_fac s]
    refine mul_ne_zero (pow_ne_zero 2 (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_)) <;>
    · have := congrArg Complex.re h; simp at this; linarith
  have hW_nz : ∀ s : ℂ, 1 < s.re → coupledQuartetSymSquare a a γ s ≠ 0 := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz s hs)))
      (div_ne_zero (hCrit_nz s hs) (hOff_nz s hs))
  have hW_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (coupledQuartetSymSquare a a γ) s := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    exact (((DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop)
      (hP_nz s hs)).fun_pow 2).mul
      (DifferentiableAt.div (by unfold quartetCritPoly; fun_prop)
        (by unfold quartetOffPoly; fun_prop) (hOff_nz s hs)))
  have hFCc : FejerCoupledSystem K κ₀ κγ d γ
      (fun s => F s * coupledQuartetSymSquare a a γ s) Λc :=
    { degree_pos := hFC.degree_pos
      diffOn_F := hFC.diffOn_F.mul (fun s hs => (hW_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hFC.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * coupledQuartetSymSquare a a γ s)
              ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (coupledQuartetSymSquare a a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := coupledQuartetSymSquare a a γ) s
                (hFC.ne_zero_F s hs) (hW_nz s hs)
                ((hFC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hW_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_aux (hFC.posDef_neg_logDeriv hσ)
          (isEvenPosDef_coupledQuartetSymSquare ha0 le_rfl ha1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hden_nz : D_poly s ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 (hP_nz s hs)) (hOff_nz s hs)
        apply mul_right_cancel₀ hden_nz
        have hW_mul : coupledQuartetSymSquare a a γ s * D_poly s = C_poly s := by
          dsimp [D_poly, C_poly]
          unfold coupledQuartetSymSquare midpointSymSquare
          have hp2 : realPairPoly (1 / 2 + a) s ^ 2 ≠ 0 := pow_ne_zero 2 (hP_nz s hs)
          have ho : quartetOffPoly a γ s ≠ 0 := hOff_nz s hs
          rw [div_pow]
          calc ((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + a) s ^ 2 *
                (quartetCritPoly γ s / quartetOffPoly a γ s) *
                (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s)
              = (((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + a) s ^ 2 *
                  realPairPoly (1 / 2 + a) s ^ 2) *
                (quartetCritPoly γ s / quartetOffPoly a γ s * quartetOffPoly a γ s) := by ring
            _ = ((s - 1 / 2) ^ 2) ^ 2 * quartetCritPoly γ s := by
                rw [div_mul_cancel₀ _ hp2, div_mul_cancel₀ _ ho]
            _ = (s - 1 / 2) ^ 4 * quartetCritPoly γ s := by ring
        calc Λc s * D_poly s
            = Λ s * C_poly s := hrel s
          _ = ((s * (s - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ s *
                fejerCoupledGamma K d γ s * F s) *
                (coupledQuartetSymSquare a a γ s * D_poly s) := by
              rw [hFC.completed_eq s hs, hW_mul]
          _ = (s * (s - 1)) ^ κ₀ * fejerShiftedPoleProd K κγ γ s *
                fejerCoupledGamma K d γ s *
                (F s * coupledQuartetSymSquare a a γ s) * D_poly s := by ring }
  exact ⟨Λc, hFCc, hord_half, hord_real, hord_quart, hord_other⟩

/-- **Exact archimedean budget for `FejerCoupledSystem K`.** -/
theorem FejerCoupledSystem.archimedean_budget {K κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hFC : FejerCoupledSystem K κ₀ κγ d γ F Λ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 1 / 2 < x ∧ x ≤ 1) :
    (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
      (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) <
    (3 / 2 : ℝ) * (κ₀ : ℝ) +
      (κγ : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          (4 / (4 + ((k : ℝ) * γ) ^ 2) + 2 / (1 + ((k : ℝ) * γ) ^ 2))) +
      (d : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
      (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / 12) * (d : ℝ) := by
  have hpos2 : 0 ≤ (-logDeriv F (2 : ℂ)).re := by
    have hpd := (hFC.posDef_neg_logDeriv (σ := 2) (by norm_num)).posDef 1 (fun _ => 0) (fun _ => 1)
    simpa using hpd
  have hdecomp := congrArg Complex.re (hFC.neg_logDeriv_F_eq (s := 2) (by norm_num))
  have hre_sp : (∑ k ∈ Finset.Icc 1 K,
      (((K + 1 - k) * κγ : ℕ) : ℂ) * logDeriv (shiftedPolePoly ((k : ℝ) * γ)) 2).re =
      (κγ : ℝ) * ∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          (4 / (4 + ((k : ℝ) * γ) ^ 2) + 2 / (1 + ((k : ℝ) * γ) ^ 2)) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Nat.cast_mul,
        re_logDeriv_shiftedPolePoly_two_eq]
    ring
  have hre_G : (∑ k ∈ Finset.Icc 1 K,
      (((K + 1 - k) * d : ℕ) : ℂ) *
        (logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
          logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I))).re =
      (d : ℝ) * ∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
            (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.add_re, Nat.cast_mul]
    ring
  have hre2 : ((κ₀ : ℂ) * (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)) +
      (∑ k ∈ Finset.Icc 1 K,
        (((K + 1 - k) * κγ : ℕ) : ℂ) * logDeriv (shiftedPolePoly ((k : ℝ) * γ)) 2) +
      (((K + 1) * d : ℕ) : ℂ) * logDeriv Complex.Gammaℝ 2 +
      (∑ k ∈ Finset.Icc 1 K,
        (((K + 1 - k) * d : ℕ) : ℂ) *
          (logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I) +
            logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I))) -
      logDeriv Λ 2).re =
      (3 / 2 : ℝ) * (κ₀ : ℝ) +
      (κγ : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          (4 / (4 + ((k : ℝ) * γ) ^ 2) + 2 / (1 + ((k : ℝ) * γ) ^ 2))) +
      ((K + 1 : ℕ) : ℝ) * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re +
      (d : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
            (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re)) -
      (logDeriv Λ 2).re := by
    rw [Complex.sub_re, Complex.add_re, Complex.add_re, Complex.add_re,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        Complex.add_re, hre_sp, hre_G, Nat.cast_mul]
    have hp1 : (1 / (2 : ℂ)).re = 1 / 2 := by norm_num
    have hp2 : (1 / ((2 : ℂ) - 1)).re = 1 := by norm_num
    rw [hp1, hp2]; ring
  rw [hre2] at hdecomp
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hFC.degree_pos
  have hK1_pos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hd_central : ((K + 1 : ℕ) : ℝ) * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re <
      -(5 / 6 : ℝ) * ((K + 1 : ℕ) : ℝ) * (d : ℝ) := by
    have := mul_lt_mul_of_pos_left re_logDeriv_Gammaℝ_two_lt (mul_pos hK1_pos hd_pos)
    linarith
  have hG_sum_le : ∑ k ∈ Finset.Icc 1 K,
      ((K + 1 - k : ℕ) : ℝ) *
        ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
          (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re) ≤
      (∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
        ((K : ℝ) * ((K + 1 : ℕ) : ℝ) / 4) := by
    have hterm_le : ∀ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
            (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re) ≤
        ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|) +
          (1 / 2 : ℝ) * ((K + 1 - k : ℕ) : ℝ) := by
      intro k _
      have hsnd := (re_logDeriv_Gammaℝ_pair_two_sandwich ((k : ℝ) * γ)).2
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at hsnd
      have := mul_le_mul_of_nonneg_left hsnd (Nat.cast_nonneg (K + 1 - k))
      linarith
    calc ∑ k ∈ Finset.Icc 1 K,
          ((K + 1 - k : ℕ) : ℝ) *
            ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
              (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re)
        ≤ ∑ k ∈ Finset.Icc 1 K,
            (((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|) +
              (1 / 2 : ℝ) * ((K + 1 - k : ℕ) : ℝ)) := Finset.sum_le_sum hterm_le
      _ = (∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
            (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (∑ k ∈ Finset.Icc 1 K, ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
            ((K : ℝ) * ((K + 1 : ℕ) : ℝ) / 4) := by
          rw [sum_fejer_weights_iem K]; ring
  have hd_shifted : (d : ℝ) * (∑ k ∈ Finset.Icc 1 K,
      ((K + 1 - k : ℕ) : ℝ) *
        ((logDeriv Complex.Gammaℝ (2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).re +
          (logDeriv Complex.Gammaℝ (2 - (((k : ℝ) * γ : ℝ) : ℂ) * I)).re)) ≤
      (d : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
      ((K : ℝ) * ((K + 1 : ℕ) : ℝ) / 4) * (d : ℝ) := by
    have := mul_le_mul_of_nonneg_left hG_sum_le hd_pos.le
    linarith
  have hhad := re_logDeriv_two_ge_of_entire_sym hFC.entire_Λ hFC.orderOne_Λ hFC.sym_Λ hFC.conj_Λ
    hFC.two_ne_zero (fun _ hρ => hFC.zero_re_mem_Icc hρ) X hX ∅
    (fun _ h => absurd h (Finset.notMem_empty _))
  simp only [Finset.sum_empty, add_zero] at hhad
  have hconst_id : -(5 / 6 : ℝ) * ((K + 1 : ℕ) : ℝ) * (d : ℝ) +
      ((K : ℝ) * ((K + 1 : ℕ) : ℝ) / 4) * (d : ℝ) =
      (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / 12) * (d : ℝ) := by ring
  linarith

private theorem fejerContractCollidedQuartet_iter_iem :
    ∀ (m : ℕ) {K κ₀ κγ d : ℕ} {γ a : ℝ} {F Λ : ℂ → ℂ},
      FejerCoupledSystem K κ₀ κγ d γ F Λ →
      0 < a → a < 1 / 2 → γ ≠ 0 →
      2 * m ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat →
      m ≤ (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat →
      ∃ Fc Λc : ℂ → ℂ,
        FejerCoupledSystem K κ₀ κγ d γ Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 * m ∧
        (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 * m =
          (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat ∧
        (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + m =
          (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat)
  | 0, _, _, _, _, _, _, F, Λ, hFC, _, _, _, _, _ =>
      ⟨F, Λ, hFC, by omega, by omega, by omega, fun _ _ _ _ => rfl⟩
  | m + 1, _, _, _, _, γ, a, F, Λ, hFC, ha0, ha1, hγ, hreal, hquart => by
      have hreal2 : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat := by omega
      have hq0 : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 :=
        hFC.eq_zero_of_one_le_order_toNat (by omega)
      obtain ⟨Λ₁, hFC₁, h1, h2, h3, h4⟩ :=
        hFC.contractCollidedQuartet ha0 ha1 hγ hreal2 hq0
      obtain ⟨Fc, Λc, hFCc, hc1, hc2, hc3, hc4⟩ :=
        fejerContractCollidedQuartet_iter_iem m hFC₁ ha0 ha1 hγ (by omega) (by omega)
      refine ⟨Fc, Λc, hFCc, by omega, by omega, by omega, fun z hz0 hza1 hza2 => ?_⟩
      rw [hc4 z hz0 hza1 hza2, h4 z hz0 hza1 hza2]

/-- **Degree-`K` Fejér ordinate-`γ` quartet multiplicity bound (`(9(K + 1)/(2K)) κ ↘ (9/2) κ`).**
Lifting any `CompletedPositiveSystem κ d F Λ` to `FejerCoupledSystem K` (`1 ≤ K`) and contracting
`K · ord_{1/2 + a + iγ}(Λ)` collided quartets across `a ∈ A` drives the normalized central pole
coefficient down to `9(K + 1)/(2K) · κ`. -/
theorem CompletedPositiveSystem.fejerOrdinateQuartet_bound
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    {K : ℕ} (hK : 1 ≤ K) {γ : ℝ} (hγ : γ ≠ 0)
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2) :
    8 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) +
      (2 * ((K + 1 : ℕ) : ℝ) / (K : ℝ)) * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      (4 / (K : ℝ)) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          ((analyticOrderAt Λ (1 / 2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat : ℝ)) <
    (9 * ((K + 1 : ℕ) : ℝ) / (2 * (K : ℝ))) * (κ : ℝ) +
      (3 * (κ : ℝ) / (K : ℝ)) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) *
          (4 / (4 + ((k : ℝ) * γ) ^ 2) + 2 / (1 + ((k : ℝ) * γ) ^ 2))) +
      (3 * (d : ℝ) / (K : ℝ)) * (∑ k ∈ Finset.Icc 1 K,
        ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)) +
      (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / (4 * (K : ℝ))) * (d : ℝ) := by
  classical
  have hcontract_all : ∀ B : Finset ℝ, B ⊆ A →
      ∃ Fc Λc : ℂ → ℂ,
        FejerCoupledSystem K ((K + 1) * κ) κ d γ Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat =
          (K + 1) * (analyticOrderAt Λ (1 / 2)).toNat +
          2 * (∑ k ∈ Finset.Icc 1 K, (K + 1 - k) *
            (analyticOrderAt Λ (1 / 2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat) +
          4 * K * ∑ a ∈ B, (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → (∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b) →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt (fejerCoupledΛ K Λ γ) z).toNat) := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨fejerCoupledF K F γ, fejerCoupledΛ K Λ γ,
          CompletedPositiveSystem.fejerCouple hS K γ, ?_, fun _ _ _ => rfl⟩
        have hhalf_eq : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
        have h0 := CompletedPositiveSystem.orderAt_fejerCoupledΛ_real hS K γ (1 / 2)
        rw [← hhalf_eq] at h0
        rw [Finset.sum_empty, mul_zero, add_zero]
        exact h0
    | @insert a B ha_not ih =>
        intro hB_sub
        obtain ⟨ha0, ha1⟩ := hA a (hB_sub (Finset.mem_insert_self a B))
        obtain ⟨F₁, Λ₁, hFC₁, hhalf₁, hout₁⟩ :=
          ih (Finset.Subset.trans (Finset.subset_insert a B) hB_sub)
        have ha_sep : ∀ b ∈ B, (1 / 2 + a : ℝ) ≠ 1 / 2 + b ∧ (1 / 2 + a : ℝ) ≠ 1 / 2 - b := by
          intro b hb
          have hb0 : 0 < b := (hA b (hB_sub (Finset.mem_insert_of_mem hb))).1
          have hab : a ≠ b := fun heq => ha_not (heq ▸ hb)
          exact ⟨fun h => hab (by linarith), fun h => by linarith⟩
        have hcast_a : (((1 / 2 + a : ℝ) : ℂ)) + ((((1 : ℕ) : ℝ) * γ : ℝ) : ℂ) * I =
            1 / 2 + (a : ℂ) + (γ : ℂ) * I := by push_cast; ring
        set ma : ℕ := (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat
        have h1_mem : 1 ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
        have hreal_ge : 2 * (K * ma) ≤ (analyticOrderAt Λ₁ ((1 / 2 + a : ℝ) : ℂ)).toNat := by
          rw [hout₁ ((1 / 2 + a : ℝ) : ℂ) (by simp; linarith)
                (fun b hb => by simpa using ha_sep b hb),
              CompletedPositiveSystem.orderAt_fejerCoupledΛ_real hS K γ (1 / 2 + a)]
          have hsingle := Finset.single_le_sum
            (f := fun k : ℕ => (K + 1 - k) *
              (analyticOrderAt Λ (((1 / 2 + a : ℝ) : ℂ) + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat)
            (fun _ _ => Nat.zero_le _) h1_mem
          rw [hcast_a, show K + 1 - 1 = K by omega] at hsingle
          dsimp [ma] at hsingle ⊢
          omega
        have hquart_ge : K * ma ≤
            (analyticOrderAt Λ₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
          have hre_a : (1 / 2 + (a : ℂ) + (γ : ℂ) * I).re = 1 / 2 + a := by simp
          rw [hout₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) (by simp; linarith)
                (fun b hb => by rw [hre_a]; exact ha_sep b hb),
              CompletedPositiveSystem.orderAt_fejerCoupledΛ hS K γ
                (1 / 2 + (a : ℂ) + (γ : ℂ) * I)]
          have hKma : K * ma ≤ (K + 1) * ma := Nat.mul_le_mul_right ma (by omega)
          exact hKma.trans (Nat.le_add_right _ _)
        obtain ⟨Fc, Λc, hFCc, hc_half, _, _, hc_out⟩ :=
          fejerContractCollidedQuartet_iter_iem (K * ma) hFC₁ ha0 ha1 hγ hreal_ge hquart_ge
        refine ⟨Fc, Λc, hFCc, ?_, ?_⟩
        · rw [Finset.sum_insert ha_not, hc_half, hhalf₁]
          dsimp [ma]; ring
        · intro z hz0 hz_ins
          have hz_a := hz_ins a (Finset.mem_insert_self a B)
          have hz_B : ∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b :=
            fun b hb => hz_ins b (Finset.mem_insert_of_mem hb)
          rw [hc_out z hz0 hz_a.1 hz_a.2, hout₁ z hz0 hz_B]
  obtain ⟨Fc, Λc, hFCc, hhalf_c, _⟩ := hcontract_all A Finset.Subset.rfl
  have hbud := hFCc.archimedean_budget ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
  simp only [Finset.sum_empty, mul_zero, add_zero] at hbud
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hK_ne : (K : ℝ) ≠ 0 := hK_pos.ne'
  set S_half : ℝ := ((analyticOrderAt Λ (1 / 2)).toNat : ℝ)
  set S_crit : ℝ := ∑ k ∈ Finset.Icc 1 K,
    ((K + 1 - k : ℕ) : ℝ) *
      ((analyticOrderAt Λ (1 / 2 + (((k : ℝ) * γ : ℝ) : ℂ) * I)).toNat : ℝ)
  set S_quart : ℝ :=
    ∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)
  set S_pole : ℝ := ∑ k ∈ Finset.Icc 1 K,
    ((K + 1 - k : ℕ) : ℝ) *
      (4 / (4 + ((k : ℝ) * γ) ^ 2) + 2 / (1 + ((k : ℝ) * γ) ^ 2))
  set S_log : ℝ := ∑ k ∈ Finset.Icc 1 K,
    ((K + 1 - k : ℕ) : ℝ) * Real.log (3 + (k : ℝ) * |γ|)
  have hhalf_cast : ((analyticOrderAt Λc (1 / 2)).toNat : ℝ) =
      ((K + 1 : ℕ) : ℝ) * S_half + 2 * S_crit + 4 * (K : ℝ) * S_quart := by
    rw [hhalf_c]; dsimp [S_half, S_crit, S_quart]; push_cast; ring
  rw [hhalf_cast, Nat.cast_mul] at hbud
  change (2 / 3 : ℝ) * (((K + 1 : ℕ) : ℝ) * S_half + 2 * S_crit + 4 * (K : ℝ) * S_quart) <
      (3 / 2 : ℝ) * (((K + 1 : ℕ) : ℝ) * (κ : ℝ)) +
        (κ : ℝ) * S_pole + (d : ℝ) * S_log +
        (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / 12) * (d : ℝ) at hbud
  have hmul := mul_lt_mul_of_pos_left hbud (show (0 : ℝ) < 3 / (K : ℝ) by positivity)
  have hlhs_eq : (3 / (K : ℝ)) * ((2 / 3 : ℝ) *
      (((K + 1 : ℕ) : ℝ) * S_half + 2 * S_crit + 4 * (K : ℝ) * S_quart)) =
      8 * S_quart + (2 * ((K + 1 : ℕ) : ℝ) / (K : ℝ)) * S_half +
        (4 / (K : ℝ)) * S_crit := by
    field_simp [hK_ne]; ring
  have hrhs_eq : (3 / (K : ℝ)) *
      ((3 / 2 : ℝ) * (((K + 1 : ℕ) : ℝ) * (κ : ℝ)) +
        (κ : ℝ) * S_pole + (d : ℝ) * S_log +
        (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / 12) * (d : ℝ)) =
      (9 * ((K + 1 : ℕ) : ℝ) / (2 * (K : ℝ))) * (κ : ℝ) +
      (3 * (κ : ℝ) / (K : ℝ)) * S_pole +
      (3 * (d : ℝ) / (K : ℝ)) * S_log +
      (((K + 1 : ℕ) : ℝ) * (3 * (K : ℝ) - 10) / (4 * (K : ℝ))) * (d : ℝ) := by
    field_simp [hK_ne]; ring
  rw [hlhs_eq, hrhs_eq] at hmul
  exact hmul

/-- **Bandwidth-`2` Fejér quartet bound (`(27/4) κ = 6.75 κ < 8 κ`, breaking the single-quartet
threshold at `κ = 1`).** -/
theorem CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    {γ : ℝ} (hγ : γ ≠ 0) (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2) :
    8 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) +
      3 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      4 * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) +
      2 * ((analyticOrderAt Λ (1 / 2 + ((2 * γ : ℝ) : ℂ) * I)).toNat : ℝ) <
    (27 / 4 : ℝ) * (κ : ℝ) +
      (3 / 2 : ℝ) * (κ : ℝ) *
        (2 * (4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2)) +
          (4 / (4 + (2 * γ) ^ 2) + 2 / (1 + (2 * γ) ^ 2))) +
      (3 / 2 : ℝ) * (d : ℝ) * (2 * Real.log (3 + |γ|) + Real.log (3 + 2 * |γ|)) -
      (3 / 2 : ℝ) * (d : ℝ) := by
  have h := CompletedPositiveSystem.fejerOrdinateQuartet_bound hS (K := 2) (by decide) hγ A hA
  have hIcc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by decide
  rw [hIcc] at h
  simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)] at h
  have hc1 : ((((1 : ℕ) : ℝ) * γ : ℝ) : ℂ) = (γ : ℂ) := by push_cast; ring
  have hc2 : ((((2 : ℕ) : ℝ) * γ : ℝ) : ℂ) = ((2 * γ : ℝ) : ℂ) := by push_cast; ring
  have hr1 : ((1 : ℕ) : ℝ) * γ = γ := by norm_num
  have hr2 : ((2 : ℕ) : ℝ) * γ = 2 * γ := by norm_num
  have ha1 : ((1 : ℕ) : ℝ) * |γ| = |γ| := by norm_num
  have ha2 : ((2 : ℕ) : ℝ) * |γ| = 2 * |γ| := by norm_num
  have hn1 : ((2 + 1 : ℕ) : ℝ) = 3 := by norm_num
  have hn2 : ((2 + 1 - 1 : ℕ) : ℝ) = 2 := by norm_num
  have hn3 : ((2 + 1 - 2 : ℕ) : ℝ) = 1 := by norm_num
  rw [hc1, hc2, hr1, hr2, ha1, ha2, hn1, hn2, hn3] at h
  convert h using 1 <;> ring

/-- **Asymptotic central-pole halving (`9(K + 1)/(2K) → 9/2` as `K → ∞`).** -/
theorem tendsto_fejer_central_pole_coeff :
    Tendsto (fun K : ℕ => (9 : ℝ) * ((K + 1 : ℕ) : ℝ) / (2 * (K : ℝ))) atTop (𝓝 (9 / 2)) := by
  have hlim : Tendsto (fun K : ℕ => (9 / 2 : ℝ) + (9 / 2 : ℝ) * (K : ℝ)⁻¹)
      atTop (𝓝 ((9 / 2 : ℝ) + (9 / 2 : ℝ) * 0)) :=
    tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (9 / 2))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  push_cast
  field_simp [hKne]

#print axioms degreeOne_exteriorTwo_eq_zero
#print axioms isobaricExteriorTwoPoly_eq
#print axioms isobaricExteriorTwoPoly_zero_central
#print axioms isobaricExteriorTwoPoly_pi_neg
#print axioms isobaricExteriorTwoPoly_nonneg_of_five_le
#print axioms isobaricExteriorTwoPoly_ratio_ge
#print axioms centeredScaleCross_re_gt_one
#print axioms re_logDeriv_two_ge_of_entire_sym
#print axioms shiftedPolePoly_eq_boundaryTwistPoly
#print axioms isEvenPosDef_boundaryTwistFactor
#print axioms HeightCoupledSystem.absorbShiftedPoles
#print axioms two_mul_le_origin_of_poleCancelling_posDef
#print axioms re_logDeriv_shiftedPolePoly_two_eq
#print axioms re_neg_logDeriv_boundaryTwistFactor_two_eq
#print axioms HeightCoupledSystem.archimedean_budget_exact
#print axioms CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound
#print axioms isEvenPosDef_realPairPlanter
#print axioms CompletedPositiveSystem.plantRealPair
#print axioms CompletedPositiveSystem.plantDoubleRealAnchor
#print axioms polarSum_sum_weights_nonneg
#print axioms two_le_pole_cost_of_doubleRealAnchor_polarSum
#print axioms CompletedPositiveSystem.anchored_quartet_pole_lower_bound
#print axioms CompletedPositiveSystem.three_le_pole_of_anchored_quartet
#print axioms fejer_egervary_szasz_first_harmonic_le
#print axioms cosine_multiplier_anchor_cost_lower
#print axioms re_logDeriv_Gammaℝ_two_shift_ge
#print axioms re_logDeriv_Gammaℝ_pair_two_sandwich
#print axioms IsEvenPosDef.fejerShift
#print axioms FejerCoupledSystem.ne_zero_of_one_lt_re
#print axioms FejerCoupledSystem.two_ne_zero
#print axioms FejerCoupledSystem.zero_re_mem_Icc
#print axioms FejerCoupledSystem.analyticOnNhd_univ
#print axioms FejerCoupledSystem.orderAt_ne_top
#print axioms FejerCoupledSystem.eq_zero_of_one_le_order_toNat
#print axioms FejerCoupledSystem.neg_logDeriv_F_eq
#print axioms CompletedPositiveSystem.fejerCouple
#print axioms CompletedPositiveSystem.orderAt_fejerCoupledΛ
#print axioms CompletedPositiveSystem.orderAt_fejerCoupledΛ_real
#print axioms FejerCoupledSystem.contractCollidedQuartet
#print axioms FejerCoupledSystem.archimedean_budget
#print axioms CompletedPositiveSystem.fejerOrdinateQuartet_bound
#print axioms CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound
#print axioms tendsto_fejer_central_pole_coeff

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
