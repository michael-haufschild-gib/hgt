import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.Calibration.Response

/-! # Necessary and sufficient drift for finite vacuum readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology _root_.RHTower

/-- The measured probability on its Mertens scale. -/
def reading (N : ℕ) (x : ℝ) := Real.log N*vacuumProbability N x

/-- Signed damping displacement in the finite critical window. -/
def drift (N : ℕ) (x : ℝ) := (x-1/2)*Real.log N

private def atDrift (N : ℕ) (b : ℝ) := reading N (1/2+b/Real.log N)

private theorem reading_at_drift {N : ℕ} (hN : 2 ≤ N) (x : ℝ) :
    atDrift N (drift N x) = reading N x := by
  have hn : Real.log (N:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N from hN))).ne'
  rw [atDrift,drift,mul_div_cancel_right₀ _ hn]
  ring_nf

private theorem vacuum_eq_real_inv (N : ℕ) (x : ℝ) :
    vacuumProbability N x = (finiteSquarefreePartition (packet N) (2*x))⁻¹ := by
  rw [vacuumProbability,finiteSquarefreeBornWeight_eq]
  simp [finiteSquarefreeHamiltonian,squarefreeBitEnergy,one_div]

private theorem monotone_atDrift {N : ℕ} (hN : 2 ≤ N) : Monotone (atDrift N) := by
  intro b c hbc
  have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N from hN))
  apply mul_le_mul_of_nonneg_left _ hL.le
  rw [vacuum_eq_real_inv,vacuum_eq_real_inv]
  apply (inv_le_inv₀ (finiteSquarefreePartition_pos _ _) (finiteSquarefreePartition_pos _ _)).mpr
  apply Finset.prod_le_prod
  · intro p _
    exact (add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_pos _).le).le
  · intro p _
    apply add_le_add_right
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast p.val.property.one_le))
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right hbc hL.le) _) zero_le_two

private theorem bracket_lower {a y : ℝ} (hy : y < response a) : ∃ b < a, y < response b := by
  have H : Tendsto response (𝓝[<] a) (𝓝 (response a)) :=
    (continuous_response.tendsto a).mono_left nhdsWithin_le_nhds
  have hl : ∀ᶠ b in 𝓝[<] a, b < a := self_mem_nhdsWithin
  exact (hl.and (H.eventually_const_lt hy)).exists

private theorem bracket_upper {a y : ℝ} (hy : response a < y) : ∃ b > a, response b < y := by
  have H : Tendsto response (𝓝[>] a) (𝓝 (response a)) :=
    (continuous_response.tendsto a).mono_left nhdsWithin_le_nhds
  have hu : ∀ᶠ b in 𝓝[>] a, a < b := self_mem_nhdsWithin
  exact (hu.and (H.eventually_lt_const hy)).exists

private theorem read_compare {b c : ℕ → ℝ} (h : ∀ᶠ N in atTop, atDrift N (b N) < atDrift N (c N)) :
    ∀ᶠ N in atTop, b N < c N := by
  filter_upwards [eventually_ge_atTop 2,h] with N hN he
  exact lt_of_not_ge (fun hn => he.not_ge (monotone_atDrift hN hn))

private theorem drift_compare {b c : ℕ → ℝ} (h : ∀ᶠ N in atTop, b N ≤ c N) :
    ∀ᶠ N in atTop, atDrift N (b N) ≤ atDrift N (c N) := by
  filter_upwards [eventually_ge_atTop 2,h] with N hN he
  exact monotone_atDrift hN he

private theorem fixed_row (b : ℝ) : Tendsto (fun N => atDrift N b) atTop (𝓝 (response b)) := reading_fixed b

private theorem moving_row (b : ℕ → ℝ) (a : ℝ) :
    Tendsto (fun N => atDrift N (b N)) atTop (𝓝 (response a)) ↔ Tendsto b atTop (𝓝 a) := by
  constructor
  · intro h
    apply tendsto_order.mpr
    exact ⟨fun c hc => read_compare ((fixed_row c).eventually_lt h (response_strictMono hc)),
      fun c hc => read_compare (h.eventually_lt (fixed_row c) (response_strictMono hc))⟩
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro y hy
      obtain ⟨c,hc,hcy⟩ := bracket_lower hy
      exact ((fixed_row c).eventually_const_lt hcy).and (drift_compare ((h.eventually_const_lt hc).mono fun _ hn => hn.le)) |>.mono
        (fun _ he => he.1.trans_le he.2)
    · intro y hy
      obtain ⟨c,hc,hcy⟩ := bracket_upper hy
      exact ((fixed_row c).eventually_lt_const hcy).and (drift_compare ((h.eventually_lt_const hc).mono fun _ hn => hn.le)) |>.mono
        (fun _ he => he.2.trans_lt he.1)

private theorem physical_rows (x : ℕ → ℝ) :
    (fun N => atDrift N (drift N (x N))) =ᶠ[atTop] (fun N => reading N (x N)) :=
  (eventually_ge_atTop 2).mono (fun _ hn => reading_at_drift hn _)

/-- A finite positive limiting reading is equivalent to one precise logarithmic displacement. -/
theorem reading_tendsto_iff (x : ℕ → ℝ) (a : ℝ) :
    Tendsto (fun N => reading N (x N)) atTop (𝓝 (response a)) ↔
      Tendsto (fun N => drift N (x N)) atTop (𝓝 a) := by
  rw [← tendsto_congr' (physical_rows x)]
  exact moving_row _ a

/-- A calibrated positive vacuum reading forces the physical damping to the isometric line. -/
theorem reading_locates_line {x : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : Tendsto (fun N => reading N (x N)) atTop (𝓝 r)) : Tendsto x atTop (𝓝 (1/2)) := by
  let a := driftCalibration.symm ⟨r,hr⟩
  have ha : response a = r := congrArg Subtype.val (driftCalibration.apply_symm_apply ⟨r,hr⟩)
  have hd := (reading_tendsto_iff x a).mp (ha ▸ h)
  have hz := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have H := (tendsto_const_nhds (x := (1/2:ℝ))).add (hd.mul hz)
  rw [mul_zero,add_zero] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : Real.log (N:ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N from hN))).ne'
  change 1/2+((x N-1/2)*Real.log N)*(Real.log N)⁻¹ = x N
  rw [mul_assoc,mul_inv_cancel₀ hn,mul_one]
  ring

/-- A finite positive vacuum reading at fixed damping detects isometric two-copy composition. -/
theorem split_isometric_iff_positive_reading (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∃ r : ℝ, 0 < r ∧ Tendsto (fun N => reading N s.re) atTop (𝓝 r) := by
  rw [split_isometric_iff]
  constructor
  · intro hs
    refine ⟨responseConstant,responseConstant_pos,?_⟩
    simpa only [hs,reading,response,mul_zero,ein,intervalIntegral.integral_same,
      Real.exp_zero,mul_one,zero_div,add_zero] using reading_fixed 0
  · rintro ⟨r,hr,h⟩
    exact tendsto_nhds_unique tendsto_const_nhds (reading_locates_line hr h)

/-- Diverging readings and positive escape of the critical displacement are equivalent. -/
theorem reading_atTop_iff (x : ℕ → ℝ) :
    Tendsto (fun N => reading N (x N)) atTop atTop ↔ Tendsto (fun N => drift N (x N)) atTop atTop := by
  rw [← tendsto_congr' (physical_rows x)]
  constructor
  · intro h
    apply tendsto_atTop.mpr
    intro b
    have H := ((fixed_row b).eventually_lt_const (lt_add_of_pos_right (response b) zero_lt_one)).and
      (h (eventually_ge_atTop (response b+1)))
    exact (read_compare (H.mono fun _ hh => hh.1.trans_le hh.2)).mono fun _ hb => hb.le
  · intro h
    apply tendsto_atTop.mpr
    intro y
    have hev : ∀ᶠ b in atTop, y < response b := response_atTop (eventually_gt_atTop y)
    obtain ⟨b,hb⟩ := hev.exists
    exact (((fixed_row b).eventually_const_lt hb).and
      (drift_compare (h (eventually_ge_atTop b)))).mono fun _ hh => hh.1.le.trans hh.2

/-- Vanishing readings and negative escape of the critical displacement are equivalent. -/
theorem reading_zero_iff (x : ℕ → ℝ) :
    Tendsto (fun N => reading N (x N)) atTop (𝓝 0) ↔ Tendsto (fun N => drift N (x N)) atTop atBot := by
  rw [← tendsto_congr' (physical_rows x)]
  constructor
  · intro h
    apply tendsto_atBot.mpr
    intro b
    exact (read_compare (h.eventually_lt (fixed_row b) (response_pos b))).mono fun _ hb => hb.le
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro y hy
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hL : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N from hN))
      exact hy.trans_le (mul_nonneg hL.le (by rw [vacuum_eq_real_inv]; exact (inv_pos.mpr (finiteSquarefreePartition_pos _ _)).le))
    · intro y hy
      obtain ⟨b,hb⟩ := (response_atBot.eventually_lt_const hy).exists
      have hbound : ∀ᶠ N in atTop, drift N (x N) ≤ b := tendsto_atBot.mp h b
      have hrow := drift_compare (b := fun N => drift N (x N)) (c := fun _ => b) hbound
      exact (hrow.and ((fixed_row b).eventually_lt_const hb)).mono fun _ hh => hh.1.trans_lt hh.2

#print axioms reading_tendsto_iff
#print axioms split_isometric_iff_positive_reading
#print axioms reading_locates_line
#print axioms reading_atTop_iff
#print axioms reading_zero_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
