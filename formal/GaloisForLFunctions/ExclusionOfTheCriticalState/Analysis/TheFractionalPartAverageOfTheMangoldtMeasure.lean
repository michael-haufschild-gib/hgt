import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheStirlingErrorSplits

/-!
# A signed Mangoldt average against the positive fractional-part kernel

Subtracting the continuous density from a truncated fractional-part sum
leaves the Stirling error at the observation point and the reciprocal
Mangoldt remainder at the cutoff. The latter vanishes in natural order.
-/

noncomputable section
open Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticOfSquareRootPrecision

/-- The fractional-part sum with the truncated continuous main term. -/
def fractionalMangoldtError (x Y : ℝ) : ℝ :=
  (∑ n ∈ Icc 0 ⌊Y⌋₊, vonMangoldt n * Int.fract (x/n)) -
    x*(Real.log Y-Real.log x+1-Real.eulerMascheroniConstant)

/-- The integer parts count every prime power dividing the factorial. -/
private theorem mangoldt_floor_sum {x Y : ℝ} (hx : 0 ≤ x) (hY : x ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, vonMangoldt n * (⌊x/(n:ℝ)⌋:ℝ)) =
      Real.log ((⌊x⌋₊).factorial : ℕ) := by
  let N := ⌊x⌋₊
  let u := fun n : ℕ => vonMangoldt n * ((N/n:ℕ):ℝ)
  have hfloor (n : ℕ) : (⌊x/(n:ℝ)⌋:ℝ) = ((N/n:ℕ):ℝ) := by
    rw [← natCast_floor_eq_intCast_floor (div_nonneg hx (Nat.cast_nonneg _)), Nat.floor_div_natCast]
  have hsub : Icc 1 N ⊆ Icc 0 ⌊Y⌋₊ :=
    fun _ h => mem_Icc.2 ⟨Nat.zero_le _,(mem_Icc.1 h).2.trans (Nat.floor_mono hY)⟩
  have heq : (∑ n ∈ Icc 1 N, u n) = ∑ n ∈ Icc 0 ⌊Y⌋₊, u n := by
    apply sum_subset hsub
    intro n _ hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [u]
    have hlt : N < n := lt_of_not_ge fun h => hn (mem_Icc.2 ⟨hpos,h⟩)
    simp only [u,Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
  simp_rw [hfloor]
  change (∑ n ∈ Icc 0 ⌊Y⌋₊, u n) = _
  rw [← heq]
  have h := _root_.RHTower.Mertens.log_summatory_eq N
  have hs : Icc 1 N = Ioc 0 N := by ext n; simp [Nat.lt_iff_add_one_le]
  rw [← sum_log_eq_log_factorial, ← hs]
  exact h.symm

/-- At every cutoff past the observation point the only cutoff-dependent
term is the reciprocal Mangoldt remainder. -/
theorem fractionalMangoldtError_eq {x Y : ℝ} (hx : 0 ≤ x) (hY : x ≤ Y) :
    fractionalMangoldtError x Y = stirlingMain x - Real.log ((⌊x⌋₊).factorial : ℕ) +
      x*((∑ n ∈ Icc 0 ⌊Y⌋₊, vonMangoldt n / (n:ℝ))-Real.log Y+Real.eulerMascheroniConstant) := by
  have h (n : ℕ) : vonMangoldt n * Int.fract (x/n) =
      x*(vonMangoldt n/(n:ℝ))-vonMangoldt n*(⌊x/(n:ℝ)⌋:ℝ) := by
    rw [Int.fract]; ring
  unfold fractionalMangoldtError
  simp_rw [h]
  rw [sum_sub_distrib, ← mul_sum, mangoldt_floor_sum hx hY]
  dsimp only [stirlingMain]; ring

/-- The entire signed average tends to the Stirling error, whose size is
at most one plus the logarithm of the observation point. -/
theorem tendsto_fractionalMangoldtError {x : ℝ} (hx : 1 ≤ x) :
    Tendsto (fractionalMangoldtError x) atTop
      (𝓝 (stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ))) ∧
    |stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ)| ≤ 1+Real.log x := by
  have h := _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.add_const Real.eulerMascheroniConstant
  rw [neg_add_cancel] at h
  have hlim := (h.const_mul x).const_add (stirlingMain x-Real.log ((⌊x⌋₊).factorial : ℕ))
  rw [mul_zero,add_zero] at hlim
  refine ⟨hlim.congr' ((eventually_ge_atTop x).mono fun Y hY => (fractionalMangoldtError_eq (zero_le_one.trans hx) hY).symm),?_⟩
  obtain ⟨hm,hm'⟩ := stirlingMonotone_bounds hx (zero_lt_one.trans_le hx) le_rfl
  obtain ⟨hs,hs'⟩ := sawtooth_bounds hx
  rw [log_factorial_floor_eq,abs_le]
  constructor <;> linarith only [hm,hm',hs,hs',Real.log_nonneg hx]

open MeasureTheory Set intervalIntegral in
/-- Logarithmic density of the positive fractional-part test on the
positive ray. Each interval between consecutive log integers contributes
the corresponding difference of a logarithm and a harmonic increment. -/
theorem fractional_density_integral :
    ∫ v in Ioi (0:ℝ), Real.exp (-v)*Int.fract (Real.exp v) =
      1-Real.eulerMascheroniConstant := by
  let f := fun v : ℝ => Real.exp (-v)*Int.fract (Real.exp v)
  have hm : Measurable f := (by fun_prop : Measurable fun v : ℝ => Real.exp (-v)).mul
    (measurable_fract.comp Real.measurable_exp)
  have hbound (v : ℝ) : ‖f v‖ ≤ Real.exp (-v) := by
    rw [Real.norm_eq_abs, f, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
  have hi : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) 0
    simp only [neg_one_mul] at h
    exact h.mono' hm.aestronglyMeasurable.restrict (Eventually.of_forall hbound)
  have hil {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hi.mono_set fun _ h => lt_of_le_of_lt ha h.1)
  have hcell (n : ℕ) (hn : 1 ≤ n) :
      ∫ v in Real.log n..Real.log ((n:ℝ)+1), f v =
        Real.log ((n:ℝ)+1)-Real.log n-1/((n:ℝ)+1) := by
    have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hn1 : (0:ℝ) < (n:ℝ)+1 := by positivity
    have hab := Real.log_le_log hn0 (le_add_of_nonneg_right zero_le_one)
    have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ Real.log ((n:ℝ)+1) := by rw [ae_iff]; simp
    have heq : (∫ v in Real.log n..Real.log ((n:ℝ)+1), f v) =
        ∫ v in Real.log n..Real.log ((n:ℝ)+1), 1-(n:ℝ)*Real.exp (-v) := by
      apply integral_congr_ae (hae.mono fun v hv hmem => ?_)
      rw [uIoc_of_le hab] at hmem
      have hlow : (n:ℝ) ≤ Real.exp v := (Real.log_le_iff_le_exp hn0).mp hmem.1.le
      have hupp : Real.exp v < (n:ℝ)+1 := (Real.lt_log_iff_exp_lt hn1).mp (lt_of_le_of_ne hmem.2 hv)
      have hf : ⌊Real.exp v⌋ = (n:ℤ) := by rw [Int.floor_eq_iff]; push_cast; exact ⟨hlow,hupp⟩
      dsimp only [f]
      rw [Int.fract,hf,Int.cast_natCast,mul_sub,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_comm]
    rw [heq]
    have hd (v : ℝ) : HasDerivAt (fun w : ℝ => w+(n:ℝ)*Real.exp (-w)) (1-n*Real.exp (-v)) v := by
      convert (hasDerivAt_id' v).add (((hasDerivAt_id' v).neg.exp).const_mul (n:ℝ)) using 1 <;> ring
    rw [integral_eq_sub_of_hasDerivAt (fun v _ => hd v) ((by fun_prop :
      Continuous (fun v : ℝ => 1-(n:ℝ)*Real.exp (-v))).intervalIntegrable _ _)]
    rw [Real.exp_neg,Real.exp_neg,Real.exp_log hn0,Real.exp_log hn1]
    field_simp [hn0.ne',hn1.ne']
    <;> ring
  have hpartial (N : ℕ) (hN : 1 ≤ N) :
      ∫ v in (0:ℝ)..Real.log N, f v = 1-((harmonic N:ℝ)-Real.log N) := by
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hl := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn)
      have hstep := Real.log_le_log hn0 (le_add_of_nonneg_right zero_le_one)
      rw [Nat.cast_succ, ← integral_add_adjacent_intervals (b := Real.log n) (hil le_rfl hl)
        (hil hl hstep), ih, hcell n hn, harmonic_succ]
      push_cast
      ring
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 hi
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_nhds_unique hlim ((tendsto_const_nhds.sub Real.tendsto_harmonic_sub_log).congr'
    ((eventually_ge_atTop 1).mono fun n hn => (hpartial n hn).symm))

#print axioms fractional_density_integral
#print axioms tendsto_fractionalMangoldtError
end GaloisForLFunctions.ExclusionOfTheCriticalState
