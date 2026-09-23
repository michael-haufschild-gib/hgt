import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyObservation
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficient
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.Field
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericTotality
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance frequencyTotalityGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private def rotatedMean (T : E →L[ℂ] E) (z : ℂ) (N : ℕ) : E →L[ℂ] E :=
  ((N : ℝ)⁻¹ : ℂ) • ∑ n ∈ Finset.range N, (z⁻¹) ^ n • T ^ n

private def obsCorr (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) : ℂ :=
  ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, ℓ ((T ^ n) u) * star (ℓ ((T ^ n) v))

private theorem unit_star (z : ℂ) (hz : ‖z‖ = 1) : star z = z⁻¹ :=
  (Circle.coe_inv_eq_conj ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩).symm

private theorem mean_observe (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (z : ℂ) (N : ℕ) (u : E) :
    ℓ (rotatedMean T z N u) =
      ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, (z⁻¹) ^ n * ℓ ((T ^ n) u) := by
  simp only [rotatedMean, smul_apply, sum_apply, map_smul, map_sum, smul_eq_mul]

private theorem corr_eigen (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (u v : E)
    (z : ℂ) (hz : ‖z‖ = 1) (he : ∀ n : ℕ, (T ^ n) v = z ^ n • v) (N : ℕ) :
    obsCorr T ℓ N u v = star (ℓ v) * ℓ (rotatedMean T z N u) := by
  rw [mean_observe]
  unfold obsCorr
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [he n, map_smul, smul_eq_mul, star_mul, star_pow, unit_star z hz]
  ring

private theorem corr_zero (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u : E) :
    obsCorr T ℓ N u 0 = 0 := by
  simp only [obsCorr, map_zero, star_zero, mul_zero, Finset.sum_const_zero]

private theorem corr_add (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v w : E) :
    obsCorr T ℓ N u (v + w) = obsCorr T ℓ N u v + obsCorr T ℓ N u w := by
  simp only [obsCorr, map_add, star_add, mul_add, Finset.sum_add_distrib]

private theorem corr_smul (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ)
    (u v : E) (c : ℂ) : obsCorr T ℓ N u (c • v) = star c * obsCorr T ℓ N u v := by
  simp only [obsCorr, map_smul, smul_eq_mul, star_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem core_corr_tendsto (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (u : E)
    (v : I → E) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i n, (T ^ n) (v i) = (z i) ^ n • v i)
    (hm : ∀ i, Tendsto (fun N : ℕ => rotatedMean T (z i) N u) atTop (𝓝 0))
    {w : E} (hw : w ∈ Submodule.span ℂ (Set.range v)) :
    Tendsto (fun N : ℕ => obsCorr T ℓ N u w) atTop (𝓝 0) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have ho : Tendsto (fun N : ℕ => ℓ (rotatedMean T (z i) N u)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, map_zero] using (ℓ.continuous.tendsto 0).comp (hm i)
    have hc : Tendsto (fun N : ℕ => star (ℓ (v i)) * ℓ (rotatedMean T (z i) N u))
        atTop (𝓝 (star (ℓ (v i)) * 0)) := tendsto_const_nhds.mul ho
    simpa only [corr_eigen T ℓ u (v i) (z i) (hz i) (he i), mul_zero] using hc
  | zero =>
    simpa only [corr_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  | add a b ha hb ia ib =>
    simpa only [corr_add, add_zero] using ia.add ib
  | smul c a ha ih =>
    have hc : Tendsto (fun N : ℕ => star c * obsCorr T ℓ N u a)
        atTop (𝓝 (star c * 0)) := tendsto_const_nhds.mul ih
    simpa only [corr_smul, mul_zero] using hc

private theorem norm_scalar_cesaro_le (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) (N : ℕ) :
    ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, f n‖ ≤ C := by
  by_cases hN : N = 0
  · subst N
    simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, norm_zero] using hC
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc
    ‖((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, f n‖ =
        (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f n‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg N)]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hi
    _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => hf n)) hi
    _ = C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

private theorem corr_gap (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) :
    obsCorr T ℓ N u u - obsCorr T ℓ N u v =
      ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
        ℓ ((T ^ n) u) * star (ℓ ((T ^ n) (u - v))) := by
  simp only [obsCorr, map_sub, star_sub, mul_sub, Finset.sum_sub_distrib]

private theorem norm_corr_gap_le (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u v : E) :
    ‖obsCorr T ℓ N u u - obsCorr T ℓ N u v‖ ≤ ‖ℓ‖ ^ (2 : ℕ) * ‖u‖ * ‖u - v‖ := by
  rw [corr_gap]
  apply norm_scalar_cesaro_le _ _ (by positivity)
  intro n
  have ha : ‖ℓ ((T ^ n) u)‖ ≤ ‖ℓ‖ * ‖u‖ :=
    (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht n u) (norm_nonneg ℓ))
  have hb : ‖ℓ ((T ^ n) (u - v))‖ ≤ ‖ℓ‖ * ‖u - v‖ :=
    (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht n (u - v)) (norm_nonneg ℓ))
  calc
    ‖ℓ ((T ^ n) u) * star (ℓ ((T ^ n) (u - v)))‖ =
        ‖ℓ ((T ^ n) u)‖ * ‖ℓ ((T ^ n) (u - v))‖ := by rw [norm_mul, norm_star]
    _ ≤ (‖ℓ‖ * ‖u‖) * (‖ℓ‖ * ‖u - v‖) := mul_le_mul ha hb (norm_nonneg _) (by positivity)
    _ = ‖ℓ‖ ^ (2 : ℕ) * ‖u‖ * ‖u - v‖ := by ring

private theorem self_corr_tendsto_zero (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (u : E) (A : Set E)
    (ha : ∀ v ∈ A, Tendsto (fun N : ℕ => obsCorr T ℓ N u v) atTop (𝓝 0))
    (hu : u ∈ closure A) : Tendsto (fun N : ℕ => obsCorr T ℓ N u u) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := ‖ℓ‖ ^ (2 : ℕ) * ‖u‖
  have hC : 0 ≤ C := by positivity
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (ε / (2 * (C + 1))) (by positivity)
  have hvn : ‖u - v‖ < ε / (2 * (C + 1)) := by simpa only [dist_eq_norm] using huv
  have hsmall : C * ‖u - v‖ < ε / 2 := by
    have hd := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hvn
    nlinarith [norm_nonneg (u - v)]
  have hevent := Metric.tendsto_nhds.mp (ha v hv) (ε / 2) (by linarith)
  filter_upwards [hevent] with N hN
  have hg := norm_corr_gap_le T ht ℓ N u v
  change ‖obsCorr T ℓ N u u - obsCorr T ℓ N u v‖ ≤ C * ‖u - v‖ at hg
  have htri := norm_add_le (obsCorr T ℓ N u u - obsCorr T ℓ N u v) (obsCorr T ℓ N u v)
  rw [sub_add_cancel] at htri
  simp only [dist_zero_right] at hN ⊢
  linarith

private theorem complex_self_square (z : ℂ) : z * star z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  change z * (starRingEnd ℂ) z = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem corr_self_re (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) (N : ℕ) (u : E) :
    (obsCorr T ℓ N u u).re = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ) := by
  have h : obsCorr T ℓ N u u =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [obsCorr, complex_self_square, ← Complex.ofReal_sum]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
  rw [h, Complex.ofReal_re]

private theorem mean_square_zero_of_modes (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (ℓ : E →L[ℂ] ℂ) (u : E)
    (v : I → E) (z : I → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i n, (T ^ n) (v i) = (z i) ^ n • v i)
    (hm : ∀ i, Tendsto (fun N : ℕ => rotatedMean T (z i) N u) atTop (𝓝 0))
    (hu : u ∈ closure (Submodule.span ℂ (Set.range v) : Set E)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((T ^ n) u)‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hc := self_corr_tendsto_zero T ht ℓ u (Submodule.span ℂ (Set.range v))
    (fun w hw => core_corr_tendsto T ℓ u v z hz he hm hw) hu
  have hr := (Complex.continuous_re.tendsto 0).comp hc
  simpa only [Function.comp_def, corr_self_re, Complex.zero_re] using! hr

private theorem scalar_family_injective (a : I → E →L[ℂ] ℂ)
    (hk : ∀ u : E, (∀ i, a i u = 0) → u = 0) :
    Function.Injective (fun u : E => fun i : I => a i u) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply hk
  intro i
  simp only [map_sub, congrFun huv i, sub_self]
end GenericTotality
local instance frequencyTotalityActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

private theorem zero_actual_means (b : ℝ) (u : causalFrequencySpace b)
    (hz : ∀ ω : ℝ, causalFrequencyCoefficient b ω u = 0) (ω : ℝ) :
    Tendsto (fun N : ℕ => rotatedMean causalBoundedChainShift
      (causalUnitBoundaryRate b ω).val N u.val) atTop (𝓝 0) := by
  have hp : causalFrequencyProjection b ω u = 0 := by
    have hs := causalFrequencyCoefficient_smul_mode b ω u
    have hc := congrArg (fun c : ℂ => c • causalFrequencyMode b ω) (hz ω)
    exact hs.symm.trans (hc.trans (zero_smul ℂ (causalFrequencyMode b ω)))
  simpa only [hp, Submodule.coe_zero, causalBoundedFrequencyMean, rotatedMean] using!
    causalFrequencyProjection_tendsto b ω u

/-- No actual completed-frequency vector is invisible to every scalar amplitude:
the common coefficient kernel is exactly zero. -/
theorem causalFrequencyCoefficient_eq_zero_iff (b : ℝ) (u : causalFrequencySpace b) :
    (∀ ω : ℝ, causalFrequencyCoefficient b ω u = 0) ↔ u = 0 := by
  constructor
  · intro hz
    apply (causalFrequencyObservationMeanSquare_vanish_iff b u).mp
    intro ℓ
    exact mean_square_zero_of_modes causalBoundedChainShift causalBoundedChainShift_pow_norm_le
      ℓ u.val (causalBoundedUnitEigenchain b) (fun ω => (causalUnitBoundaryRate b ω).val)
      (norm_causalUnitBoundaryRate b) (fun ω n => causalBoundedChainShift_pow_unitEigenchain b ω n)
      (zero_actual_means b u hz) u.property
  · rintro rfl ω
    exact (causalFrequencyCoefficient b ω).map_zero

/-- The full actual amplitude family uniquely determines every vector in the
completed frequency space, without assuming a summation formula. -/
theorem causalFrequencyCoefficient_injective (b : ℝ) :
    Function.Injective (fun u : causalFrequencySpace b => fun ω : ℝ =>
      causalFrequencyCoefficient b ω u) :=
  scalar_family_injective (causalFrequencyCoefficient b)
    (fun u hu => (causalFrequencyCoefficient_eq_zero_iff b u).mp hu)

/-- The actual rank-one frequency projections jointly separate the completed
frequency space: their common kernel is exactly zero. -/
theorem causalFrequencyProjection_eq_zero_iff (b : ℝ) (u : causalFrequencySpace b) :
    (∀ ω : ℝ, causalFrequencyProjection b ω u = 0) ↔ u = 0 := by
  constructor
  · intro hp
    apply (causalFrequencyCoefficient_eq_zero_iff b u).mp
    intro ω
    apply norm_eq_zero.mp
    simpa only [hp ω, norm_zero] using norm_causalFrequencyCoefficient_apply b ω u
  · rintro rfl ω
    exact (causalFrequencyProjection b ω).map_zero

end RHTower.FokasLenells
