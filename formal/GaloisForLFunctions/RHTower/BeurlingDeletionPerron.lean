import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct
import GaloisForLFunctions.RHTower.RiemannHypothesisZetaGrowth
import GaloisForLFunctions.RHTower.RiemannHypothesisLittlewoodBound
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.HTGeometry.SmoothedPerronContourShift
import Zeta23.RvM.ZetaGrowth

/-!
# The integers free of the deleted primes: Perron's formula under RH

Let `S` be a set of deleted primes with discrepancy bound (R) (`DeletionData α`, `0 < α < 1`), and
let `N'(x) = #{n ≤ x : n has no prime factor in S}`.  On `Re s > 1`,

`Σ_{n ∈ N'} n^{−s} = ζ(s) E(s) / ζ(s + 1 − α)`,   `E = exp(−corr − rem₁ + rem₂)`

(`LSeries_sFree_eq`).  With `ζ_u(s) = (s − 1)ζ(s)` (`zetaResidueUnit`), the numerator
`H(s) = ζ_u(s) E(s) (s − α)/ζ_u(s + 1 − α)` (`perronNum`) is holomorphic on `Re s > α/2` under RH,
since `Re(s + 1 − α) > 1 − α/2 > 1/2`.  Its growth:

* `|E(s)| ≪_κ (|t| + 2)^κ` on `Re s ≥ α/2 + δ` (`exists_norm_eFactor_le`), because
  `|log E| ≪ √log(|t| + 2)`;
* `|ζ(s + 1 − α)|^{−1} ≤ (|t| + 3)^κ` (RH, `exists_norm_riemannZeta_two_sided`);
* `|ζ(s)| ≪ |t|` on `Re s ≥ σ₀`, and `|ζ(σ₀ + it)| ≪ |t|^{1/2 − σ₀ + κ}` for `σ₀ < 1/2` (RH).

The smoothed Perron shift (`GaloisForLFunctions.HTGeometry.SmoothedPerron.exists_norm_sum_sub_le`) to `σ₀ = α/2 + δ` with
`θ = 1/2 − σ₀ + 3κ` gives

`N'(x) = a' x + O(x^{1/(3 − α) + η})`  for every `η > 0`,  `a' = H(1) = E(1)/ζ(2 − α)`

(`exists_norm_count_sub_le`).
-/

open Complex Finset Filter Topology

noncomputable section

namespace RHTower.BeurlingDeletion

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

/-! ## The factors -/

/-- `E(s) = exp(−corr(s) − rem₁(s) + rem₂(s))`. -/
def eFactor (s : ℂ) : ℂ := Complex.exp (-D.corr s - D.rem₁ s + rem₂ α s)

/-- `(s − α)/ζ_u(s + 1 − α)`, equal to `1/ζ(s + 1 − α)` for `s ≠ α`. -/
def qFactor (α : ℝ) (s : ℂ) : ℂ := (s - α) / zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))

/-- The Perron numerator `H(s) = ζ_u(s) E(s) (s − α)/ζ_u(s + 1 − α)`. -/
def perronNum (s : ℂ) : ℂ := zetaResidueUnit s * D.eFactor s * qFactor α s

/-- The density `a' = H(1)` of the integers free of `S`. -/
def density : ℂ := D.perronNum 1

theorem zetaResidueUnit_of_ne {s : ℂ} (hs : s ≠ 1) : zetaResidueUnit s = (s - 1) * riemannZeta s := by
  simp [zetaResidueUnit, Function.update_of_ne hs]

theorem qFactor_eq {s : ℂ} (hs : s ≠ (α : ℂ)) :
    qFactor α s = (riemannZeta (s + ((1 - α : ℝ) : ℂ)))⁻¹ := by
  have hw : s + ((1 - α : ℝ) : ℂ) ≠ 1 := by
    intro h; apply hs; push_cast at h; linear_combination h
  rw [qFactor, zetaResidueUnit_of_ne hw, show s + ((1 - α : ℝ) : ℂ) - 1 = s - α by push_cast; ring]
  have : s - α ≠ 0 := sub_ne_zero.mpr hs
  field_simp

theorem perronNum_div_eq {s : ℂ} (hs : s ≠ 1) :
    D.perronNum s / (s - 1) = riemannZeta s * (D.eFactor s * qFactor α s) := by
  rw [perronNum, zetaResidueUnit_of_ne hs]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

theorem perronNum_div_eq_LSeries (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    D.perronNum s / (s - 1) = LSeries D.sFreeInd s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hsα : s ≠ (α : ℂ) := fun h => by rw [h] at hs; simp at hs; linarith
  rw [D.perronNum_div_eq hs1, qFactor_eq hsα, D.LSeries_sFree_eq hα0 hα hs, eFactor]
  ring

/-- Under RH, `ζ_u(s + 1 − α) ≠ 0` on `Re s > α/2`. -/
theorem zetaResidueUnit_shift_ne_zero (hRH : RiemannHypothesis) (hα : α < 1) {s : ℂ}
    (hs : α / 2 < s.re) : zetaResidueUnit (s + ((1 - α : ℝ) : ℂ)) ≠ 0 := by
  set w := s + ((1 - α : ℝ) : ℂ) with hw
  by_cases h1 : w = 1
  · rw [h1, zetaResidueUnit_one]; exact one_ne_zero
  rw [zetaResidueUnit_of_ne h1]
  refine mul_ne_zero (sub_ne_zero.mpr h1) ?_
  refine RHTower.WeilSpectral.riemannZeta_ne_zero_of_half_lt hRH ?_ h1
  rw [hw]; simp; linarith

theorem differentiableOn_perronNum (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) :
    DifferentiableOn ℂ D.perronNum {s | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hE : DifferentiableAt ℂ D.eFactor s := by
    have h1 := (D.differentiableOn_corr hα0).differentiableAt (hU.mem_nhds hs)
    have h2 := (D.differentiableOn_rem₁ hα0 hα).differentiableAt (hU.mem_nhds hs)
    have h3 := (differentiableOn_rem₂ hα0 hα).differentiableAt (hU.mem_nhds hs)
    exact ((h1.neg.sub h2).add h3).cexp
  have hQ : DifferentiableAt ℂ (qFactor α) s := by
    have hz := (analyticAt_zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))).differentiableAt
    have hz' : DifferentiableAt ℂ (fun s : ℂ => zetaResidueUnit (s + ((1 - α : ℝ) : ℂ))) s :=
      hz.comp s (differentiableAt_id.add_const _)
    exact (differentiableAt_id.sub_const _).div hz' (zetaResidueUnit_shift_ne_zero hRH hα hs')
  exact (((analyticAt_zetaResidueUnit s).differentiableAt.mul hE).mul hQ).differentiableWithinAt

/-! ## Growth of the factors -/

/-- `e^{b √(log y)} ≤ e^{b²/(4κ)} y^κ` for `y ≥ 1`. -/
theorem exp_mul_sqrt_log_le {b κ y : ℝ} (hκ : 0 < κ) (hy : 1 ≤ y) :
    Real.exp (b * Real.sqrt (Real.log y)) ≤ Real.exp (b ^ 2 / (4 * κ)) * y ^ κ := by
  have hL : 0 ≤ Real.log y := Real.log_nonneg hy
  have hsq := Real.sq_sqrt hL
  have h1 : 4 * κ * (b * Real.sqrt (Real.log y)) ≤ b ^ 2 + 4 * κ ^ 2 * Real.log y := by
    nlinarith [sq_nonneg (2 * κ * Real.sqrt (Real.log y) - b)]
  have hkey : b * Real.sqrt (Real.log y) ≤ b ^ 2 / (4 * κ) + κ * Real.log y := by
    calc b * Real.sqrt (Real.log y) = 4 * κ * (b * Real.sqrt (Real.log y)) / (4 * κ) := by
          field_simp
      _ ≤ (b ^ 2 + 4 * κ ^ 2 * Real.log y) / (4 * κ) := by gcongr
      _ = b ^ 2 / (4 * κ) + κ * Real.log y := by field_simp
  calc Real.exp (b * Real.sqrt (Real.log y)) ≤ Real.exp (b ^ 2 / (4 * κ) + κ * Real.log y) :=
        Real.exp_le_exp.mpr hkey
    _ = Real.exp (b ^ 2 / (4 * κ)) * y ^ κ := by
        rw [Real.exp_add, Real.rpow_def_of_pos (by linarith), mul_comm κ]

/-- `|E(s)| ≪_κ (|t| + 2)^κ` on `Re s ≥ α/2 + δ`. -/
theorem exists_norm_eFactor_le (hα0 : 0 < α) (hα : α < 1) {δ : ℝ} (hδ : 0 < δ) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, α / 2 + δ ≤ s.re → ‖D.eFactor s‖ ≤ c * (|s.im| + 2) ^ κ := by
  set b : ℝ := 3 * D.baseConst (δ / 2) with hb
  set R : ℝ := (∑' p, D.maj₁ δ p) + ∑' p, maj₂ α δ p with hR
  refine ⟨Real.exp R * Real.exp (b ^ 2 / (4 * κ)), by positivity, fun s hs => ?_⟩
  have h1 := D.norm_corr_le hα0 hδ hs
  have h2 := D.norm_rem₁_le hα0 hα hδ hs
  have h3 := norm_rem₂_le hα hδ hs
  have hy : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlog : Real.log (|s.im| + 2) = Real.log (|s.im| + 2) := rfl
  rw [eFactor, Complex.norm_exp]
  calc Real.exp (-D.corr s - D.rem₁ s + rem₂ α s).re
      ≤ Real.exp (R + b * Real.sqrt (Real.log (|s.im| + 2))) := by
        refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
        calc ‖-D.corr s - D.rem₁ s + rem₂ α s‖ ≤ ‖D.corr s‖ + ‖D.rem₁ s‖ + ‖rem₂ α s‖ := by
              refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) le_rfl)
              rw [norm_neg]
          _ ≤ 3 * D.baseConst (δ / 2) * Real.sqrt (Real.log (|s.im| + 2)) +
                (∑' p, D.maj₁ δ p) + ∑' p, maj₂ α δ p := by gcongr
          _ = R + b * Real.sqrt (Real.log (|s.im| + 2)) := by rw [hR, hb]; ring
    _ = Real.exp R * Real.exp (b * Real.sqrt (Real.log (|s.im| + 2))) := Real.exp_add _ _
    _ ≤ Real.exp R * (Real.exp (b ^ 2 / (4 * κ)) * (|s.im| + 2) ^ κ) := by
        gcongr; exact exp_mul_sqrt_log_le hκ hy
    _ = _ := by ring

/-- Under RH, `|(s − α)/ζ_u(s + 1 − α)| ≤ (|t| + 3)^κ` on `α/2 + δ ≤ Re s ≤ 3/2`, `|t| ≥ T`. -/
theorem exists_norm_qFactor_le (hRH : RiemannHypothesis) (hα : α < 1) {δ : ℝ}
    (hδ : 0 < δ) (hδα : δ < α / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, α / 2 + δ ≤ s.re → s.re ≤ 3 / 2 → T ≤ |s.im| →
      ‖qFactor α s‖ ≤ (|s.im| + 3) ^ κ := by
  obtain ⟨T₀, hT₀⟩ := ZetaGrowth.exists_norm_riemannZeta_two_sided hRH
    (δ := 1 / 2 - α / 2 + δ) (by linarith) (by linarith) hκ
  refine ⟨max T₀ 1, le_max_right _ _, fun s hs1 hs2 hT => ?_⟩
  have him : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at hT; linarith [le_max_right T₀ 1]
  have hsα : s ≠ (α : ℂ) := fun h => him (by rw [h]; simp)
  rw [qFactor_eq hsα]
  have hw : s + ((1 - α : ℝ) : ℂ) = ((s.re + (1 - α) : ℝ) : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hw]
  have h := (hT₀ s.im (le_trans (le_max_left _ _) hT) (s.re + (1 - α)) (by linarith)
    (by linarith)).1
  have hpos : 0 < (|s.im| + 3) ^ (-κ) := by positivity
  rw [norm_inv]
  calc ‖riemannZeta (((s.re + (1 - α) : ℝ) : ℂ) + (s.im : ℂ) * I)‖⁻¹
      ≤ ((|s.im| + 3) ^ (-κ))⁻¹ := inv_anti₀ hpos h
    _ = (|s.im| + 3) ^ κ := by rw [Real.rpow_neg (by positivity), inv_inv]

/-- Under RH, `|E(s) (s − α)/ζ_u(s + 1 − α)| ≪ (|t| + 3)^{2κ}` on `α/2 + δ ≤ Re s ≤ 3/2`. -/
theorem exists_norm_eFactor_mul_qFactor_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : δ < α / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c T : ℝ, 0 < c ∧ 1 ≤ T ∧ ∀ s : ℂ, α / 2 + δ ≤ s.re → s.re ≤ 3 / 2 → T ≤ |s.im| →
      ‖D.eFactor s * qFactor α s‖ ≤ c * (|s.im| + 3) ^ (2 * κ) := by
  obtain ⟨c, hc, hE⟩ := D.exists_norm_eFactor_le hα0 hα hδ hκ
  obtain ⟨T, hT1, hQ⟩ := exists_norm_qFactor_le hRH hα hδ hδα hκ
  refine ⟨c, T, hc, hT1, fun s hs1 hs2 hT => ?_⟩
  have h3 : 0 < |s.im| + 3 := by positivity
  have hE' : ‖D.eFactor s‖ ≤ c * (|s.im| + 3) ^ κ :=
    (hE s hs1).trans (by gcongr; linarith)
  rw [norm_mul, show 2 * κ = κ + κ by ring, Real.rpow_add h3]
  calc ‖D.eFactor s‖ * ‖qFactor α s‖ ≤ (c * (|s.im| + 3) ^ κ) * (|s.im| + 3) ^ κ :=
        mul_le_mul hE' (hQ s hs1 hs2 hT) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-! ## The Perron asymptotic -/

/-- The number of integers `n ≤ X` free of the deleted primes. -/
def count (X : ℝ) : ℂ := ∑ n ∈ Finset.Iic ⌊X⌋₊, D.sFreeInd n

theorem sFreeInd_zero : D.sFreeInd 0 = 0 := by
  classical
  simp [sFreeInd, sFree]

theorem norm_sFreeInd_le (n : ℕ) : ‖D.sFreeInd n‖ ≤ 1 := by
  classical
  unfold sFreeInd; split_ifs <;> simp

/-- **Perron's formula for the integers free of the deleted primes, under RH.** -/
theorem exists_norm_count_sub_le (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {η : ℝ}
    (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ (1 / (3 - α) + η) := by
  -- parameters
  set τ : ℝ := min (min (η / 7) (α / 4)) (min ((1 - α) / 4) (1 / 8)) with hτ
  have hτ0 : 0 < τ := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
    (by norm_num))
  have hτη : τ ≤ η / 7 := (min_le_left _ _).trans (min_le_left _ _)
  have hτα : τ ≤ α / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hτα' : τ ≤ (1 - α) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ8 : τ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  set σ₀ : ℝ := α / 2 + τ with hσ₀
  have hσ₀0 : 0 < σ₀ := by positivity
  have hσ₀half : σ₀ < 1 / 2 := by linarith
  have hσ₀1 : σ₀ < 1 := by linarith
  have hτα2 : τ < α / 2 := by linarith
  obtain ⟨c, T, hc, hT1, hEQ⟩ := D.exists_norm_eFactor_mul_qFactor_le hRH hα0 hα hτ0 hτα2 hτ0
  obtain ⟨Cζ, hCζ, hζ⟩ := Zeta23.RvM.zeta_growth hσ₀0
  obtain ⟨CL, TL, hCL, hζL⟩ := ZetaGrowth.exists_norm_riemannZeta_left_le hRH hσ₀0 hσ₀half hτ0
  have hHd := D.differentiableOn_perronNum hRH hα0 hα
  -- the strip bound
  have hstrip : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → T ≤ |s.im| →
      ‖D.perronNum s / (s - 1)‖ ≤ (Cζ * c * 4 ^ (2 * τ)) * |s.im| ^ (1 + 2 * τ) := by
    intro s hs1 hs2 hT
    have ht1 : 1 ≤ |s.im| := hT1.trans hT
    have ht0 : 0 < |s.im| := by linarith
    have hs1' : s ≠ 1 := by
      intro h; rw [h] at ht1; simp at ht1; linarith
    rw [D.perronNum_div_eq hs1', norm_mul]
    have h4 : (|s.im| + 3) ^ (2 * τ) ≤ 4 ^ (2 * τ) * |s.im| ^ (2 * τ) := by
      rw [← Real.mul_rpow (by norm_num) ht0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    calc ‖riemannZeta s‖ * ‖D.eFactor s * qFactor α s‖
        ≤ (Cζ * |s.im|) * (c * (|s.im| + 3) ^ (2 * τ)) :=
          mul_le_mul (hζ s hs1 ht1) (hEQ s (by linarith) hs2 hT) (norm_nonneg _) (by positivity)
      _ ≤ (Cζ * |s.im|) * (c * (4 ^ (2 * τ) * |s.im| ^ (2 * τ))) := by gcongr
      _ = (Cζ * c * 4 ^ (2 * τ)) * (|s.im| ^ (1 : ℝ) * |s.im| ^ (2 * τ)) := by
          rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add ht0]
  -- the left line
  set θ : ℝ := 1 / 2 - σ₀ + 3 * τ with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  set TT : ℝ := max T TL with hTT
  have hcont : ContinuousOn (fun t : ℝ => D.perronNum ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I - 1))
      (Set.Icc (-TT) TT) := by
    refine ContinuousOn.div ?_ (by fun_prop) fun t _ => ?_
    · refine (hHd.continuousOn).comp (by fun_prop) fun t _ => ?_
      show α / 2 < ((σ₀ : ℂ) + t * I).re
      simp; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -TT) (b := TT)).exists_bound_of_continuousOn hcont
  set K₀ : ℝ := max (CL * c * 27 ^ τ) M₀ with hK₀
  have hleft : ∀ t : ℝ, ‖D.perronNum (σ₀ + t * I) / (σ₀ + t * I - 1)‖ ≤ K₀ * (|t| + 1) ^ θ := by
    intro t
    have ht1 : 1 ≤ (|t| + 1) ^ θ := Real.one_le_rpow (by linarith [abs_nonneg t]) hθ0
    by_cases ht : |t| ≤ TT
    · have hmem : t ∈ Set.Icc (-TT) TT := ⟨by linarith [neg_abs_le t], le_trans (le_abs_self t) ht⟩
      calc _ ≤ M₀ := hM₀ t hmem
        _ ≤ K₀ := le_max_right _ _
        _ ≤ K₀ * (|t| + 1) ^ θ := by
            have : 0 ≤ K₀ := le_trans (norm_nonneg _) ((hM₀ t hmem).trans (le_max_right _ _))
            nlinarith
    replace ht := lt_of_not_ge ht
    have hTt : T ≤ |t| := le_trans (le_max_left _ _) ht.le
    have hTLt : TL ≤ |t| := le_trans (le_max_right _ _) ht.le
    have ht0 : 0 < |t| := lt_of_lt_of_le (by linarith) hTt
    have hs1' : (σ₀ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [D.perronNum_div_eq hs1', norm_mul]
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    have him : ((σ₀ : ℂ) + t * I).im = t := by simp
    have hEQt := hEQ ((σ₀ : ℂ) + t * I) (by rw [hre]) (by rw [hre]; linarith)
      (by rw [him]; exact hTt)
    rw [him] at hEQt
    have hζt := hζL t hTLt
    have hu : 0 < |t| + 1 := by positivity
    have h3 : |t| + 3 ≤ 3 * (|t| + 1) := by linarith [abs_nonneg t]
    have hA : |t| ^ (1 / 2 - σ₀) ≤ (|t| + 1) ^ (1 / 2 - σ₀) :=
      Real.rpow_le_rpow ht0.le (by linarith) (by linarith)
    have hB : (|t| + 3) ^ (3 * τ) ≤ 27 ^ τ * (|t| + 1) ^ (3 * τ) := by
      rw [show (27 : ℝ) ^ τ = 3 ^ (3 * τ) by
        rw [show (27 : ℝ) = 3 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)],
        ← Real.mul_rpow (by norm_num) hu.le]
      exact Real.rpow_le_rpow (by positivity) h3 (by positivity)
    calc ‖riemannZeta ((σ₀ : ℂ) + t * I)‖ * ‖D.eFactor ((σ₀ : ℂ) + t * I) * qFactor α ((σ₀ : ℂ) + t * I)‖
        ≤ (CL * |t| ^ (1 / 2 - σ₀) * (|t| + 3) ^ τ) * (c * (|t| + 3) ^ (2 * τ)) :=
          mul_le_mul hζt hEQt (norm_nonneg _) (by positivity)
      _ = CL * c * |t| ^ (1 / 2 - σ₀) * ((|t| + 3) ^ τ * (|t| + 3) ^ (2 * τ)) := by ring
      _ = CL * c * |t| ^ (1 / 2 - σ₀) * (|t| + 3) ^ (3 * τ) := by
          rw [← Real.rpow_add (by positivity)]; ring_nf
      _ ≤ CL * c * (|t| + 1) ^ (1 / 2 - σ₀) * (27 ^ τ * (|t| + 1) ^ (3 * τ)) := by gcongr
      _ = CL * c * 27 ^ τ * ((|t| + 1) ^ (1 / 2 - σ₀) * (|t| + 1) ^ (3 * τ)) := by ring
      _ = CL * c * 27 ^ τ * (|t| + 1) ^ θ := by rw [← Real.rpow_add hu, hθ]
      _ ≤ K₀ * (|t| + 1) ^ θ := by gcongr; exact le_max_left _ _
  -- apply the smoothed Perron shift
  obtain ⟨C, hC⟩ := GaloisForLFunctions.HTGeometry.SmoothedPerron.exists_norm_sum_sub_le D.sFreeInd D.sFreeInd_zero
    D.norm_sFreeInd_le (H := D.perronNum) (a := α / 2) (σ₀ := σ₀) (by linarith) hσ₀0 hσ₀1 hHd
    (fun s hs => D.perronNum_div_eq_LSeries hα0 hα hs) (κ₁ := 1 + 2 * τ) (by linarith) hstrip
    hθ0 hθ1 hleft (κ := η / 2) (by linarith)
  have hexp : (θ + σ₀) / (1 + θ) + η / 2 ≤ 1 / (3 - α) + η := by
    have h3α : 2 < 3 - α := by linarith
    have h1θ : 0 < 1 + θ := by linarith
    have hθσ : θ + σ₀ = 1 / 2 + 3 * τ := by rw [hθ]; ring
    have h1θ' : 1 + θ = (3 - α + 4 * τ) / 2 := by rw [hθ, hσ₀]; ring
    rw [hθσ, h1θ']
    have hd : 0 < 3 - α + 4 * τ := by linarith
    have hkey : (1 / 2 + 3 * τ) / ((3 - α + 4 * τ) / 2) - 1 / (3 - α) ≤ η / 2 := by
      rw [div_div_eq_mul_div, div_sub_div _ _ hd.ne' (by linarith), div_le_iff₀ (by positivity)]
      have hprod : 4 ≤ (3 - α + 4 * τ) * (3 - α) := by nlinarith
      have h1 : τ * (14 - 6 * α) ≤ 2 * η := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hprod (by linarith : (0 : ℝ) ≤ η / 2)]
    linarith
  refine ⟨C, fun X hX => ?_⟩
  refine (hC X hX).trans ?_
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1 le_rfl)
    rwa [Real.one_rpow, mul_one] at this
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hC0

end DeletionData

end RHTower.BeurlingDeletion
