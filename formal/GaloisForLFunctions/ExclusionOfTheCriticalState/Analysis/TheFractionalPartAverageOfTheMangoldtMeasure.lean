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

#print axioms tendsto_fractionalMangoldtError
end GaloisForLFunctions.ExclusionOfTheCriticalState
