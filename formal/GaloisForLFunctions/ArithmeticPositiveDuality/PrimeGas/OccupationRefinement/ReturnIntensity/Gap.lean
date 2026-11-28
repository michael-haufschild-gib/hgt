import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity.Alignment

/-! # An occupied energy difference determines continuity on every share -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity

open Filter Topology UniversalResponse ModeCapacities CoherentRay
open scoped NNReal

private def gapAmplitude (A : Response) (E : ℝ) (t : ℝ≥0) :=
  A.val (Real.exp (-(t:ℝ) * E))

private theorem relative (A : Response) (P : ℕ+ → ℝ) {m n : ℕ+} (gap : energy m < energy n) (t : ℝ≥0) :
    aligned A P n t / aligned A P m t = gapAmplitude A (energy n - energy m) t := by
  have share : Real.exp (-(t:ℝ) * (energy n - energy m)) ∈ Shares :=
    ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.property) (sub_nonneg.mpr gap.le))⟩
  have factor : survivalAmplitude A n t = survivalAmplitude A m t * gapAmplitude A (energy n - energy m) t := by
    rw [survivalAmplitude, show -(t:ℝ) * energy n =
      -(t:ℝ) * energy m + -(t:ℝ) * (energy n - energy m) by ring, Real.exp_add]
    exact A.property.1 _ (survival_share t.property m) _ share
  have qne : _root_.RHTower.overlapPhase (signal A P t) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [_root_.RHTower.overlapPhase_norm]; exact one_ne_zero)
  apply (div_eq_iff (mul_ne_zero qne (survival_ne A m t))).mpr
  rw [aligned, factor, aligned]
  ring

private theorem regular_of_gap (A : Response) {E : ℝ} (hE : 0 < E)
    (lim : Tendsto (gapAmplitude A E) (𝓝 0) (𝓝 1)) : ContinuousOn A.val Shares := by
  have two : 0 < energy 2 := Real.log_pos (by norm_num)
  let ratio : ℝ≥0 := ⟨energy 2 / E, (div_pos two hE).le⟩
  have scale : Tendsto (fun t : ℝ≥0 => t * ratio) (𝓝 0) (𝓝 0) := by
    have idlim : Tendsto (fun t : ℝ≥0 => t) (𝓝 0) (𝓝 0) := tendsto_id
    simpa only [zero_mul] using idlim.mul_const ratio
  apply continuous_from_mode A two
  change Tendsto _ _ _
  rw [survival_zero]
  apply (lim.comp scale).congr'
  refine Filter.Eventually.of_forall fun t => ?_
  change A.val (Real.exp (-((t * ratio : ℝ≥0):ℝ) * E)) =
    A.val (Real.exp (-(t:ℝ) * energy 2))
  rw [NNReal.coe_mul, ← neg_mul, mul_assoc, show (ratio:ℝ)*E=energy 2 from div_mul_cancel₀ _ hE.ne']

/-- With two positive masses, a phase-insensitive return detects precisely
the continuous critical powers, using the gap between the observed energies. -/
theorem two_levels_iff (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P)
    {m n : ℕ+} (order : m<n) (hm : 0<P m) (hn : 0<P n) :
    ContinuousAt (fun t => ‖signal A P t‖) 0 ↔ ∃! s : Conserving, ∀ x ∈ Shares, A.val x=power s.val x := by
  rw [← classification]
  constructor
  · intro h
    have gap : energy m < energy n :=
      Real.log_lt_log (by exact_mod_cast m.pos) (by exact_mod_cast (show m.val < n.val from order))
    have ratio := (aligned_limit A pos sum h hn).div (aligned_limit A pos sum h hm) one_ne_zero
    rw [div_one] at ratio
    have lim : Tendsto (gapAmplitude A (energy n-energy m)) (𝓝 0) (𝓝 1) :=
      ratio.congr' (Filter.Eventually.of_forall (relative A P gap))
    exact ⟨regular_of_gap A (sub_pos.mpr gap) lim,(response_iff A.val).mp A.property⟩
  · exact fun h => (continuous_signal A h.1 pos sum).norm

#print axioms two_levels_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity
