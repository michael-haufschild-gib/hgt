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
    · have := congrArg Complex.im h; simp at this; first | exact hne (by linarith) | linarith
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
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      have hden : (3 / 2) * (3 / 2) + -γ * -γ ≠ 0 := by positivity
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
      simp [map_ofNat]
    rw [Finset.sum_congr rfl hval_p, Finset.sum_congr rfl hval_m,
        Finset.sum_const, Finset.sum_const, hc_card, hc_card, hconj_c, hord_conj,
        nsmul_eq_mul, nsmul_eq_mul]
    ring
  set S_tot : Finset (ZeroCopy f) :=
    (cAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies) ∪ Γ.biUnion critCopies
  have hd1 : Disjoint (cAt (1 / 2 : ℂ)) (X.biUnion pairCopies) :=
    Finset.disjoint_biUnion_right.mpr hhalf_disj_pair
  have hd2 : Disjoint (cAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies) (Γ.biUnion critCopies) := by
    rw [Finset.disjoint_union_left]
    refine ⟨Finset.disjoint_biUnion_right.mpr hhalf_disj_crit, ?_⟩
    rw [Finset.disjoint_biUnion_left]
    intro x hx
    exact Finset.disjoint_biUnion_right.mpr fun γ hγm => hpair_disj_crit x hx γ hγm
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
  rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (i1.const_mul 2) i2, ← integral_sub ((i1.const_mul 2).sub i2) i3,
      ← integral_sub (i4.const_mul 2) i5, ← integral_sub ((i4.const_mul 2).sub i5) i6,
      ← integral_add (((i1.const_mul 2).sub i2).sub i3) (((i4.const_mul 2).sub i5).sub i6)]
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
    ((fun s hs => (differentiableAt_boundaryTwistFactor_of_one_lt_re γ hs).differentiableWithinAt).pow κγ)
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
  linarith
