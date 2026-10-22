import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitBoundaryDiagonal
import GaloisForLFunctions.RHTower.LogarithmicExponentialEntryConvolution

/-!
# The actual signed boundary defect as a reflection integral

The complete Möbius tail pairing equals a reflection convolution of two
finite causal profiles. In this window the literal divisor source is the
exponential ramp. No absolute values replace the arithmetic coefficients.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

theorem ccmPrimeDeficitDivisorSource_square_window_eq_ramp
    {m k a b : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (ha : m < a) (hb : m < b)
    {T : ℝ} (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ)) =
      logarithmicExponentialRamp (T - Real.log (a * b : ℕ)) := by
  let s := T - Real.log (a * b : ℕ)
  change ccmPrimeDeficitDivisorSource s = logarithmicExponentialRamp s
  by_cases hs : s ≤ 0
  · rw [ccmPrimeDeficitDivisorSource_of_nonpos hs, logarithmicExponentialRamp_of_nonpos hs]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : 3 * (k : ℝ) ≤ m := by exact_mod_cast hk
  have haR : (m : ℝ) ≤ a := by exact_mod_cast (Nat.le_of_lt ha)
  have hbR : (m : ℝ) ≤ b := by exact_mod_cast (Nat.le_of_lt hb)
  have habpos : (0 : ℝ) < (a * b : ℕ) := by
    exact_mod_cast Nat.mul_pos (show 0 < a by omega) (show 0 < b by omega)
  have hab : (m : ℝ) ^ 2 ≤ (a : ℝ) * b := by
    simpa only [pow_two] using mul_le_mul haR hbR hmR.le (Nat.cast_nonneg a)
  have hsmall : ((m : ℝ) + k) ^ 2 < 2 * (m : ℝ) ^ 2 := by
    have hupper : (m : ℝ) + k ≤ 4 / 3 * m := by linarith
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (m : ℝ) + k) hupper
    nlinarith only [hsq, sq_pos_of_pos hmR]
  have hN : (0 : ℝ) < (m + k : ℕ) := by exact_mod_cast (show 0 < m + k by omega)
  have he : Real.exp T ≤ ((m : ℝ) + k) ^ 2 := by
    calc
      _ ≤ Real.exp (2 * Real.log (m + k : ℕ)) := Real.exp_le_exp.mpr hT
      _ = _ := by rw [two_mul, Real.exp_add, Real.exp_log hN, Nat.cast_add, pow_two]
  have hstop : s < Real.log 2 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mpr
    rw [Real.exp_sub, Real.exp_log habpos, div_lt_iff₀ habpos, Nat.cast_mul]
    nlinarith only [he, hsmall, hab]
  rw [ccmPrimeDeficitDivisorSource_before_two (le_of_not_ge hs) hstop,
    logarithmicExponentialRamp_of_nonneg (le_of_not_ge hs)]

def ccmPrimeDeficitBoundaryExpProfile (m k : ℕ) (t : ℝ) : ℝ :=
  logarithmicFiniteEntryProfile (logarithmicLongTail m moebiusCoeff) (m + 3 * k) Real.exp t

def ccmPrimeDeficitBoundaryCountProfile (m k : ℕ) (t : ℝ) : ℝ :=
  logarithmicFiniteEntryProfile (logarithmicLongTail m moebiusCoeff) (m + 3 * k) (fun _ => 1) t

theorem intervalIntegrable_ccmPrimeDeficitBoundaryProfile_pair (m k : ℕ) (T a b : ℝ) :
    IntervalIntegrable (fun s => ccmPrimeDeficitBoundaryExpProfile m k s *
      ccmPrimeDeficitBoundaryCountProfile m k (T - s)) volume a b :=
  intervalIntegrable_logarithmicFiniteExponentialEntry_pair _ _ _ _ _ _

theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_reflection
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction m T =
      ∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryExpProfile m k s *
        ccmPrimeDeficitBoundaryCountProfile m k (T - s) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_window_eq_strip hm hk h0 hT]
  unfold ccmPrimeDeficitBoundaryExpProfile ccmPrimeDeficitBoundaryCountProfile
  rw [integral_logarithmicFiniteExponentialEntry_pair]
  let w := logarithmicLongTail m moebiusCoeff
  let f := fun a b => w a * w b * logarithmicExponentialRamp (T - Real.log (a * b : ℕ))
  have hsource : (∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
      ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k),
        w a * w b * ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))) =
      ∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
        ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k), f a b := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have ham : m < a := by have := (Finset.mem_Icc.mp ha).1; omega
    have hbm : m < b := by have := (Finset.mem_Icc.mp hb).1; omega
    exact congrArg (fun x => w a * w b * x)
      (ccmPrimeDeficitDivisorSource_square_window_eq_ramp hm hk ham hbm hT)
  change (∑ a ∈ Finset.Icc (m + 1) (m + 3 * k),
    ∑ b ∈ Finset.Icc (m + 1) (m + 3 * k),
      w a * w b * ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ))) =
    ∑ a ∈ Finset.Icc 1 (m + 3 * k), ∑ b ∈ Finset.Icc 1 (m + 3 * k), f a b
  rw [hsource]
  have hsub : Finset.Icc (m + 1) (m + 3 * k) ⊆ Finset.Icc 1 (m + 3 * k) := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp ha).1; omega, (Finset.mem_Icc.mp ha).2⟩
  have hz {a : ℕ} (ha : a ∈ Finset.Icc 1 (m + 3 * k))
      (hnot : a ∉ Finset.Icc (m + 1) (m + 3 * k)) : w a = 0 := by
    have ham : ¬ m < a := by
      have := (Finset.mem_Icc.mp ha).2
      simp only [Finset.mem_Icc] at hnot
      omega
    simp [w, logarithmicLongTail, ham]
  have hi (a : ℕ) : (∑ b ∈ Finset.Icc (m + 1) (m + 3 * k), f a b) =
      ∑ b ∈ Finset.Icc 1 (m + 3 * k), f a b := by
    apply Finset.sum_subset hsub
    intro b hb hbnot
    simp only [f, hz hb hbnot, mul_zero, zero_mul]
  simp_rw [hi]
  apply Finset.sum_subset hsub
  intro a ha hanot
  apply Finset.sum_eq_zero
  intro b _
  simp only [f, hz ha hanot, zero_mul]

/-- Subtracting the already-controlled diagonal leaves the exact signed
cross term as a reflection integral minus that diagonal. -/
theorem ccmPrimeDeficitBoundaryOffDiagonal_eq_reflection_sub_diagonal
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) {T : ℝ} (h0 : 0 ≤ T)
    (hT : T ≤ 2 * Real.log (m + k : ℕ)) :
    ccmPrimeDeficitBoundaryOffDiagonal m k T =
      (∫ s in (0 : ℝ)..T, ccmPrimeDeficitBoundaryExpProfile m k s *
        ccmPrimeDeficitBoundaryCountProfile m k (T - s)) -
          ccmPrimeDeficitBoundaryDiagonal m k T := by
  have hsplit := ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_diagonal_add_offDiagonal
    hm hk h0 hT
  have href := ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_reflection hm hk h0 hT
  linarith only [hsplit, href]

end RHTower
