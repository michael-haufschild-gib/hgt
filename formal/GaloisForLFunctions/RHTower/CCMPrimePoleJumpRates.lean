import GaloisForLFunctions.RHTower.CCMPrimePoleJumpBochner

/-!
# Prime jump rates in multiplicative coordinates

Inside both aperture endpoints, the literal pole-normalized rates at `log q`
reduce to rational functions of `q` and the prime-power index, times its von
Mangoldt coefficient. These identities make local curvature calculations exact.
-/

open MeasureTheory Set
noncomputable section
namespace RHTower

theorem primePoleProfile_log {q : ℝ} (hq : 0 < q) :
    primePoleProfile (Real.log q) = (q+1) / Real.sqrt q := by
  have he : (Real.exp (Real.log q / 2))^2 = q := by
    rw [pow_two, ← Real.exp_add, show Real.log q / 2 + Real.log q / 2 = Real.log q by ring,
      Real.exp_log hq]
  have hs : Real.sqrt q = Real.exp (Real.log q / 2) := by
    calc
      Real.sqrt q = Real.sqrt ((Real.exp (Real.log q / 2))^2) := congrArg Real.sqrt he.symm
      _ = _ := Real.sqrt_sq (Real.exp_pos _).le
  rw [primePoleProfile, show -(Real.log q) / 2 = -(Real.log q / 2) by ring, Real.exp_neg, hs]
  have hr := (Real.exp_pos (Real.log q / 2)).ne'
  field_simp
  nlinarith [he]

theorem ccmPrimePoleJumpRate_log_forward
    (a : SuzukiPositiveAperture) {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : 0 < n)
    (hx : Real.log q ∈ centralInterval a.1)
    (hy : Real.log (q*n) ∈ centralInterval a.1) :
    ccmPrimePoleJumpRate a (n,true) (Real.log q) =
      ArithmeticFunction.vonMangoldt n * (q*n+1) / ((n : ℝ)*(q+1)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hshift : ccmPrimePoleJumpShift (n,true) (Real.log q) = Real.log (q*n) := by
    simp only [ccmPrimePoleJumpShift, ↓reduceIte]
    exact (Real.log_mul hq.ne' hnR.ne').symm
  rw [ccmPrimePoleJumpRate, indicator_of_mem hx, hshift, indicator_of_mem hy,
    primePoleProfile_log (mul_pos hq hnR), primePoleProfile_log hq, Real.sqrt_mul hq.le]
  have hsq := Real.sq_sqrt hnR.le
  have hrq := (Real.sqrt_pos.mpr hq).ne'
  have hrn := (Real.sqrt_pos.mpr hnR).ne'
  have hq1 : q+1 ≠ 0 := by positivity
  field_simp
  ring_nf
  simp [hsq]

theorem ccmPrimePoleJumpRate_log_backward
    (a : SuzukiPositiveAperture) {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : 0 < n)
    (hx : Real.log q ∈ centralInterval a.1)
    (hy : Real.log (q/n) ∈ centralInterval a.1) :
    ccmPrimePoleJumpRate a (n,false) (Real.log q) =
      ArithmeticFunction.vonMangoldt n * (q+n) / ((n : ℝ)*(q+1)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hshift : ccmPrimePoleJumpShift (n,false) (Real.log q) = Real.log (q/n) := by
    simp only [ccmPrimePoleJumpShift, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]
    exact (Real.log_div hq.ne' hnR.ne').symm
  rw [ccmPrimePoleJumpRate, indicator_of_mem hx, hshift, indicator_of_mem hy,
    primePoleProfile_log (div_pos hq hnR), primePoleProfile_log hq, Real.sqrt_div hq.le]
  have hrq := (Real.sqrt_pos.mpr hq).ne'
  have hrn := (Real.sqrt_pos.mpr hnR).ne'
  have hq1 : q+1 ≠ 0 := by positivity
  field_simp

def ccmPrimePoleMultiplicativeTarget (j : ℕ × Bool) (q : ℝ) : ℝ :=
  if j.2 then q * j.1 else q / j.1

theorem ccmPrimePoleJumpShift_log {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) (b : Bool) :
    ccmPrimePoleJumpShift (n,b) (Real.log q) =
      Real.log (ccmPrimePoleMultiplicativeTarget (n,b) q) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  cases b
  · simp only [ccmPrimePoleJumpShift, ccmPrimePoleMultiplicativeTarget, Bool.false_eq_true,
      ↓reduceIte, ← sub_eq_add_neg]
    exact (Real.log_div hq.ne' hnR.ne').symm
  · simp only [ccmPrimePoleJumpShift, ccmPrimePoleMultiplicativeTarget, ↓reduceIte]
    exact (Real.log_mul hq.ne' hnR.ne').symm

theorem log_mem_centralInterval_log_iff {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    Real.log q ∈ centralInterval (Real.log A) ↔ A⁻¹ ≤ q ∧ q ≤ A := by
  change -Real.log A ≤ Real.log q ∧ Real.log q ≤ Real.log A ↔ _
  rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr hA) hq,
    Real.log_le_log_iff hq hA]

theorem ccmPrimePoleJumpRate_log_cutoff
    (a : SuzukiPositiveAperture) {A q : ℝ} (hA : 0 < A) (ha : a.1 = Real.log A)
    (hq : 0 < q) {n : ℕ} (hn : 0 < n) (b : Bool) :
    ccmPrimePoleJumpRate a (n,b) (Real.log q) =
      if A⁻¹ ≤ q ∧ q ≤ A then
        if A⁻¹ ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
            ccmPrimePoleMultiplicativeTarget (n,b) q ≤ A then
          ArithmeticFunction.vonMangoldt n * (if b then q*n+1 else q+n) / ((n : ℝ)*(q+1))
        else 0
      else 0 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < ccmPrimePoleMultiplicativeTarget (n,b) q := by
    cases b <;> simp [ccmPrimePoleMultiplicativeTarget, mul_pos hq hnR, div_pos hq hnR]
  have hxiff := log_mem_centralInterval_log_iff hA hq
  have hyiff := log_mem_centralInterval_log_iff hA ht
  rw [← ha] at hxiff hyiff
  by_cases hx : A⁻¹ ≤ q ∧ q ≤ A
  · rw [if_pos hx]
    by_cases hy : A⁻¹ ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
        ccmPrimePoleMultiplicativeTarget (n,b) q ≤ A
    · rw [if_pos hy]
      have hm := hxiff.mpr hx
      have htm := hyiff.mpr hy
      cases b
      · exact ccmPrimePoleJumpRate_log_backward a hq hn hm htm
      · exact ccmPrimePoleJumpRate_log_forward a hq hn hm htm
    · rw [if_neg hy]
      have hymem : Real.log (ccmPrimePoleMultiplicativeTarget (n,b) q) ∉ centralInterval a.1 :=
        fun h => hy (hyiff.mp h)
      simp [ccmPrimePoleJumpRate, hxiff.mpr hx, ccmPrimePoleJumpShift_log hq hn,
        hymem]
  · rw [if_neg hx]
    have hxmem : Real.log q ∉ centralInterval a.1 := fun h => hx (hxiff.mp h)
    simp [ccmPrimePoleJumpRate, hxmem]

end RHTower
