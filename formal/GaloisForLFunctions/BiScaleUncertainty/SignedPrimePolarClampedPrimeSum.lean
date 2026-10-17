import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRealFactorialStencil
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarContinuousFactorialLift

/-! Finite arithmetic sandwiches for clamped factorial sums.
The two finite summation caps are retained explicitly. -/

open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower ArithmeticFunction
noncomputable section
set_option autoImplicit false

private theorem sum_cutoff_count (K k : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, if j ≤ k then (1 : ℝ) else 0) = min K k := by
  rw [← Finset.sum_filter]
  have hs : (Finset.Icc 1 K).filter (fun j => j ≤ k) = Finset.Icc 1 (min K k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    tauto
  rw [hs]
  simp [Nat.card_Icc]

/-- The lower sharp count fits the finite cap; the upper count can be enlarged. -/
theorem clamped_count_bounds {ε w : ℝ} {K : ℕ}
    (hε : 0 < ε) (hw : 0 < w) (hcap : ⌊w⌋₊ ≤ K) :
    (⌊w⌋₊ : ℝ) ≤ ∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)/w) ∧
      (∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)/w)) ≤ ⌊(1+ε)*w⌋₊ := by
  constructor
  · calc
      _ = ∑ j ∈ Finset.Icc 1 K, if j ≤ ⌊w⌋₊ then (1 : ℝ) else 0 := by
        rw [sum_cutoff_count, min_eq_right hcap]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · have hjw : (j : ℝ) ≤ w := (by exact_mod_cast hj : (j : ℝ) ≤ ⌊w⌋₊).trans
            (Nat.floor_le hw.le)
          rw [clampedRamp_eq_one hε ((div_le_iff₀ hw).2 (by simpa using hjw))]
        · exact clampedRamp_nonneg _ _
  · calc
      _ ≤ ∑ j ∈ Finset.Icc 1 K, if j ≤ ⌊(1+ε)*w⌋₊ then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · exact clampedRamp_le_one _ _
        · have hwj : (1+ε)*w < (j : ℝ) := by
            by_contra! h
            exact hj (Nat.le_floor h)
          rw [clampedRamp_eq_zero hε ((le_div_iff₀ hw).2 (by linarith))]
      _ = (min K ⌊(1+ε)*w⌋₊ : ℕ) := sum_cutoff_count _ _
      _ ≤ _ := by exact_mod_cast min_le_right K ⌊(1+ε)*w⌋₊

theorem factorialLog_eq_extended_prime_sum {B M : ℕ} (hBM : B ≤ M) :
    floorSummatory chebyshevPsi B =
      ∑ m ∈ Finset.Icc 1 M, vonMangoldt m * ((B/m : ℕ) : ℝ) := by
  rw [floorSummatory_chebyshevPsi_eq_sum_vonMangoldt_mul_div]
  apply Finset.sum_subset (fun m hm => Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hBM⟩)
  intro m hm hnot
  have hBm : B < m := by
    simp only [Finset.mem_Icc] at hm hnot
    omega
  rw [Nat.div_eq_of_lt hBm]
  simp

/-- The exponential factor of the physical atomic packet has been removed. -/
def clampedPrimeFactorialSum (ε : ℝ) (K M : ℕ) (v : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, vonMangoldt m *
    ∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*(m : ℝ)/v)

/-- Both arithmetic caps are discharged by explicit size inequalities. -/
theorem clampedPrimeFactorialSum_bounds {ε v : ℝ} {K M : ℕ}
    (hε : 0 < ε) (hv : 0 < v) (hcap : v ≤ 2*(K : ℝ))
    (hM : (1+ε)*v ≤ M) :
    floorSummatory chebyshevPsi ⌊v⌋₊ ≤ clampedPrimeFactorialSum ε K M v ∧
      clampedPrimeFactorialSum ε K M v ≤ floorSummatory chebyshevPsi ⌊(1+ε)*v⌋₊ := by
  have hvU : v ≤ (1+ε)*v := by nlinarith
  have hVM : ⌊v⌋₊ ≤ M := Nat.floor_le_of_le (hvU.trans hM)
  have hUM : ⌊(1+ε)*v⌋₊ ≤ M := Nat.floor_le_of_le hM
  rw [factorialLog_eq_extended_prime_sum hVM, factorialLog_eq_extended_prime_sum hUM]
  unfold clampedPrimeFactorialSum
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      vonMangoldt m * ((⌊v⌋₊/m : ℕ) : ℝ) ≤
        vonMangoldt m * ∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*(m : ℝ)/v) ∧
      vonMangoldt m * (∑ j ∈ Finset.Icc 1 K, clampedRamp ε ((j : ℝ)*(m : ℝ)/v)) ≤
        vonMangoldt m * ((⌊(1+ε)*v⌋₊/m : ℕ) : ℝ) := by
    by_cases hm1 : m = 1
    · simp [hm1]
    have hm2 : 2 ≤ m := by have := (Finset.mem_Icc.mp hm).1; omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have h2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hwK : v/(m : ℝ) ≤ K := by
      apply (div_le_iff₀ hmR).2
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    have hc := clamped_count_bounds hε (div_pos hv hmR) (Nat.floor_le_of_le hwK)
    have he (j : ℕ) : (j : ℝ)/(v/(m : ℝ)) = (j : ℝ)*(m : ℝ)/v := by field_simp
    simp_rw [he] at hc
    rw [Nat.floor_div_natCast] at hc
    have hfloor : ⌊(1+ε)*(v/(m : ℝ))⌋₊ = ⌊(1+ε)*v⌋₊/m := by
      rw [← mul_div_assoc, Nat.floor_div_natCast]
    rw [hfloor] at hc
    exact ⟨mul_le_mul_of_nonneg_left hc.1 vonMangoldt_nonneg,
      mul_le_mul_of_nonneg_left hc.2 vonMangoldt_nonneg⟩
  exact ⟨Finset.sum_le_sum fun m hm => (hterm m hm).1,
    Finset.sum_le_sum fun m hm => (hterm m hm).2⟩

/-- A smoothing collar of arithmetic width at most two has only two carry terms. -/
theorem clampedPrimeFactorialSum_error {ε v : ℝ} {K M : ℕ}
    (hε : 0 < ε) (hv : 0 < v) (hcap : v ≤ 2*(K : ℝ))
    (hM : (1+ε)*v ≤ M) (hwidth : ε*v ≤ 2) :
    0 ≤ clampedPrimeFactorialSum ε K M v-floorSummatory chebyshevPsi ⌊v⌋₊ ∧
      clampedPrimeFactorialSum ε K M v-floorSummatory chebyshevPsi ⌊v⌋₊ ≤
        2*Real.log ((1+ε)*v+1) := by
  have hs := clampedPrimeFactorialSum_bounds hε hv hcap hM
  have hvU : v ≤ (1+ε)*v := by nlinarith
  have hfloor : ⌊(1+ε)*v⌋₊ < ⌊v⌋₊+3 := by
    apply (Nat.floor_lt (by positivity : 0 ≤ (1+ε)*v)).2
    push_cast
    have h := Nat.lt_floor_add_one v
    nlinarith
  have hi := factorialLog_short_increment (Nat.floor_mono hvU)
    (show ⌊(1+ε)*v⌋₊-⌊v⌋₊ ≤ 2 by omega)
    (Nat.floor_le (by positivity : 0 ≤ (1+ε)*v))
  norm_num only [Nat.cast_ofNat] at hi
  exact ⟨sub_nonneg.mpr hs.1, by linarith [hi.2]⟩

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
