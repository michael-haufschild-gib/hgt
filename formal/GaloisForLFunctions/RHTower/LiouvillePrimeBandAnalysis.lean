import GaloisForLFunctions.RHTower.LiouvillePrimeBandAlgebra
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Complete cofactor and nonlinear errors for a prime-phase band

The band-free cofactor response differs from the unrestricted density by the entire
excluded exponential tail. The common prime-phase source is differentiated termwise
on a neighborhood of the closed unit disc. Its nonlinear part and derivative are both
bounded by `(T + 1) * exp (-T)` when every selected prime exceeds `T`.

All integer coefficients, including repeated selected primes, remain present. The source
is identified with its complete arithmetic phase evaluation and with the original twist
at the baseline phases. These are analytic components of MC-C12.92; the simple-zero
assembly and the RH-critical Liouville lower bound are not asserted here.
-/

open Filter Finset
open scoped Topology BigOperators Classical

namespace RHTower.LiouvillePrimeBand
noncomputable section

private theorem exp_pow (t : ℝ) (n : ℕ) : Real.exp (-t) ^ n = Real.exp (-((n : ℝ) * t)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A full exponential tail, with no coefficient above the threshold discarded. -/
theorem norm_tsum_le_exp_tail {f : ℕ → ℂ} {t X : ℝ} (ht : 0 < t) (hX : 0 ≤ X)
    (hf : ∀ n, ‖f n‖ ≤ Real.exp (-((n : ℝ) * t)))
    (hzero : ∀ n : ℕ, (n : ℝ) ≤ X → f n = 0) :
    ‖∑' n, f n‖ ≤ Real.exp (-X * t) / (1 - Real.exp (-t)) := by
  have hq : Real.exp (-t) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos ht)
  have hs : Summable f :=
    (GaloisForLFunctions.HTGeometry.summable_exp_neg_nat_mul ht).of_norm_bounded hf
  have hb := norm_sub_le_of_geometric_bound_of_hasSum hq
    (C := 1) (fun n => by simpa only [one_mul, exp_pow] using hf n) hs.hasSum (⌊X⌋₊ + 1)
  have hz : (∑ n ∈ range (⌊X⌋₊ + 1), f n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply hzero n
    exact (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn) :
      (n : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX)
  rw [hz, zero_sub, norm_neg, one_mul, exp_pow] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hq.le)
  apply Real.exp_le_exp.mpr
  have hx := (Nat.lt_floor_add_one X).le
  push_cast
  nlinarith

/-- Complete band-free cofactor density. -/
def cofactorDensity (P : Finset ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if degree P n = 0 then
    RHTower.LiouvilleTwistedDensity.coefficient n * (Real.exp (-x) : ℂ) ^ n else 0

def cofactorResponse (P : Finset ℕ) (t : ℝ) (p : ℕ) : ℂ :=
  cofactorDensity P ((p : ℝ) * t) / (p : ℂ)

/-- Every excluded cofactor lies beyond `T`; the entire excluded tail is bounded. -/
theorem cofactorDensity_error {P : Finset ℕ} {T x : ℝ} (hT : 0 ≤ T)
    (hP : ∀ p ∈ P, T < (p : ℝ)) (hx : 1 ≤ x) :
    ‖cofactorDensity P x - RHTower.LiouvilleTwistedDensity.exponentialDensity x‖ ≤
      Real.exp (-T) / (1 - Real.exp (-1)) := by
  let f := fun n : ℕ => RHTower.LiouvilleTwistedDensity.coefficient n * (Real.exp (-x) : ℂ) ^ n
  have hnorm : ∀ n, ‖f n‖ ≤ Real.exp (-(n : ℝ)) := by
    intro n
    dsimp [f]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exp_pow]
    calc
      _ ≤ 1 * Real.exp (-((n : ℝ) * x)) := mul_le_mul_of_nonneg_right
        (RHTower.LiouvilleTwistedDensity.norm_coefficient_le_one n) (Real.exp_pos _).le
      _ ≤ Real.exp (-(n : ℝ)) := by
        rw [one_mul]
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hs : Summable f :=
    (GaloisForLFunctions.HTGeometry.summable_exp_neg_nat_mul (by norm_num : (0 : ℝ) < 1)).of_norm_bounded
      (fun n => by simpa using hnorm n)
  have hsf : Summable (fun n => if degree P n = 0 then f n else 0) := by
    apply (GaloisForLFunctions.HTGeometry.summable_exp_neg_nat_mul
      (by norm_num : (0 : ℝ) < 1)).of_norm_bounded
    intro n
    split_ifs
    · simpa using hnorm n
    · simp only [norm_zero]
      exact (Real.exp_pos _).le
  have heq : cofactorDensity P x - RHTower.LiouvilleTwistedDensity.exponentialDensity x =
      ∑' n : ℕ, ((if degree P n = 0 then f n else 0) - f n) := by
    rw [hsf.tsum_sub hs]
    rw [RHTower.LiouvilleTwistedDensity.exponentialDensity_eq_density]
    rfl
  rw [heq]
  have hb := norm_tsum_le_exp_tail (t := 1) (X := T) (by norm_num) hT
    (f := fun n => (if degree P n = 0 then f n else 0) - f n)
  apply (by simpa using hb : _)
  · intro n
    by_cases hn : degree P n = 0
    · simp [hn]
      positivity
    · simpa [hn] using hnorm n
  · intro n hn
    have hd : degree P n = 0 := by
      by_contra h
      exact (not_lt_of_ge hn) (degree_pos_escape hP (Nat.pos_of_ne_zero h))
    simp [hd]

/-- Summed cofactor error retains all selected primes. -/
theorem cofactorResponse_total_error {P : Finset ℕ} {T t : ℝ} (hT : 0 ≤ T)
    (hP : ∀ p ∈ P, T < (p : ℝ)) (ht : ∀ p ∈ P, 1 ≤ (p : ℝ) * t) :
    (∑ p ∈ P, ‖cofactorResponse P t p -
      RHTower.LiouvilleTwistedDensity.exponentialDensity ((p : ℝ) * t) / (p : ℂ)‖) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) * (Real.exp (-T) / (1 - Real.exp (-1))) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  rw [cofactorResponse, ← sub_div, norm_div, Complex.norm_natCast]
  have hb := cofactorDensity_error hT hP (ht p hp)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
    div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

/-- The actual source coefficient after fixing unit prime orientations. -/
def baseCoefficient (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  character P β 1 n / (n : ℂ) * (Real.exp (-t) : ℂ) ^ n

def term (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  baseCoefficient P β t n * z ^ degree P n

def derivativeTerm (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  baseCoefficient P β t n * (degree P n : ℂ) * z ^ (degree P n - 1)

/-- A full degree slice; the choice of degrees does not truncate the integer source. -/
def degreeSlice (D : Set ℕ) (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, if degree P n ∈ D then term P β t n z else 0

def source (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ → ℂ :=
  degreeSlice Set.univ P β t

def nonlinearRemainder (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) : ℂ → ℂ :=
  degreeSlice (Set.Ici 2) P β t

private theorem baseCoefficient_bounds {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) (t : ℝ) (n : ℕ) :
    ‖baseCoefficient P β t n‖ ≤ Real.exp (-((n : ℝ) * t)) ∧
      ‖baseCoefficient P β t n‖ * (degree P n : ℝ) ≤ Real.exp (-((n : ℝ) * t)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [baseCoefficient]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc := norm_character_one_le hβ n
  have hd : (degree P n : ℝ) ≤ n := by exact_mod_cast degree_le_self P n
  have hr : ‖character P β 1 n‖ / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr (hc.trans hn1)
  have hrd : (‖character P β 1 n‖ / (n : ℝ)) * (degree P n : ℝ) ≤ 1 := by
    calc
      _ = ‖character P β 1 n‖ * ((degree P n : ℝ) / n) := by ring
      _ ≤ 1 * 1 := mul_le_mul hc ((div_le_one hn0).mpr hd) (by positivity) zero_le_one
      _ = 1 := one_mul 1
  rw [baseCoefficient, norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), exp_pow]
  constructor
  · simpa using mul_le_mul_of_nonneg_right hr (Real.exp_pos (-((n : ℝ) * t))).le
  · calc
      _ = ((‖character P β 1 n‖ / (n : ℝ)) * (degree P n : ℝ)) *
          Real.exp (-((n : ℝ) * t)) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hrd (Real.exp_pos (-((n : ℝ) * t))).le

private theorem term_bounds {P : Finset ℕ} {β : ℕ → ℂ} (hβ : ∀ p ∈ P, ‖β p‖ = 1)
    (t : ℝ) {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖term P β t n z‖ ≤ (R * Real.exp (-t)) ^ n ∧
      ‖derivativeTerm P β t n z‖ ≤ (R * Real.exp (-t)) ^ n := by
  have hp : ∀ k ≤ n, ‖z‖ ^ k ≤ R ^ n := fun k hk =>
    (pow_le_pow_left₀ (norm_nonneg _) hz k).trans (pow_le_pow_right₀ hR hk)
  have he : Real.exp (-((n : ℝ) * t)) * R ^ n = (R * Real.exp (-t)) ^ n := by
    rw [mul_pow, exp_pow]
    ring
  obtain ⟨hb, hd⟩ := baseCoefficient_bounds hβ t n
  constructor
  · rw [term, norm_mul, norm_pow]
    exact (mul_le_mul hb (hp _ (degree_le_self P n)) (by positivity) (Real.exp_pos _).le).trans_eq he
  · rw [derivativeTerm, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    exact (mul_le_mul hd (hp _ ((Nat.sub_le _ _).trans (degree_le_self P n)))
      (by positivity) (Real.exp_pos _).le).trans_eq he

private theorem hasDerivAt_term (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (term P β t n) (derivativeTerm P β t n z) z := by
  unfold term derivativeTerm
  convert ((hasDerivAt_id z).pow (degree P n)).const_mul (baseCoefficient P β t n) using 1 <;>
    first | rfl | simp [mul_assoc]

/-- Every degree slice is holomorphic across the closed unit disc for positive damping. -/
theorem hasDerivAt_degreeSlice {P : Finset ℕ} {β : ℕ → ℂ} (hβ : ∀ p ∈ P, ‖β p‖ = 1)
    {t : ℝ} (ht : 0 < t) (D : Set ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasDerivAt (degreeSlice D P β t)
      (∑' n, if degree P n ∈ D then derivativeTerm P β t n z else 0) z := by
  let R := Real.exp (t / 2)
  have hR : 1 < R := by dsimp [R]; simpa using Real.exp_lt_exp.mpr (by linarith : (0 : ℝ) < t / 2)
  have hq0 : 0 ≤ R * Real.exp (-t) := by positivity
  have hq1 : R * Real.exp (-t) < 1 := by
    dsimp [R]
    rw [← Real.exp_add]
    simpa using Real.exp_lt_exp.mpr (by linarith : t / 2 + -t < (0 : ℝ))
  have hs := summable_geometric_of_lt_one hq0 hq1
  have hbase : Summable (fun n => if degree P n ∈ D then term P β t n (0 : ℂ) else 0) := by
    apply hs.of_norm_bounded
    intro n
    split_ifs
    · exact (term_bounds hβ t hR.le (by simpa using (zero_le_one.trans hR.le) : ‖(0 : ℂ)‖ ≤ R) n).1
    · simpa using pow_nonneg hq0 n
  change HasDerivAt (fun z => ∑' n, if degree P n ∈ D then term P β t n z else 0) _ z
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun n w => if degree P n ∈ D then term P β t n w else 0)
    (g' := fun n w => if degree P n ∈ D then derivativeTerm P β t n w else 0)
    (y₀ := (0 : ℂ)) (y := z) hs Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected ?_ ?_ ?_ hbase ?_
  · intro n w _
    by_cases hn : degree P n ∈ D
    · simpa [hn] using hasDerivAt_term P β t n w
    · simpa [hn] using (hasDerivAt_const w (0 : ℂ))
  · intro n w hw
    split_ifs
    · have hw' : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw
      exact (term_bounds hβ t hR.le hw'.le n).2
    · simpa using pow_nonneg hq0 n
  · exact Metric.mem_ball_self (by linarith)
  · simpa using hz.trans_lt hR

/-- Uniform bound for the complete nonlinear part and its complex derivative. -/
theorem nonlinearRemainder_bounds {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {T : ℝ} (hT : 0 < T)
    (hP : ∀ p ∈ P, T < (p : ℝ)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖nonlinearRemainder P β (1 / T) z‖ ≤ Real.exp (-T) / (1 - Real.exp (-(1 / T))) ∧
    ‖deriv (nonlinearRemainder P β (1 / T)) z‖ ≤ Real.exp (-T) / (1 - Real.exp (-(1 / T))) := by
  have ht : 0 < 1 / T := one_div_pos.mpr hT
  have htail : ∀ f : ℕ → ℂ, (∀ n, ‖f n‖ ≤ Real.exp (-((n : ℝ) * (1 / T)))) →
      (∀ n, ¬2 ≤ degree P n → f n = 0) →
      ‖∑' n, f n‖ ≤ Real.exp (-T) / (1 - Real.exp (-(1 / T))) := by
    intro f hf hz0
    have h := norm_tsum_le_exp_tail ht (sq_nonneg T) hf (fun (n : ℕ) hn => hz0 n (by
      intro hd
      exact (not_lt_of_ge hn) (degree_ge_two_escape hT.le hP hd)))
    have he : -(T ^ 2) * (1 / T) = -T := by field_simp
    simpa only [he] using h
  have hb := fun n => term_bounds hβ (1 / T) (le_refl 1) hz n
  constructor
  · unfold nonlinearRemainder degreeSlice
    simp only [Set.mem_Ici]
    apply htail
    · intro n
      split_ifs
      · simpa only [one_mul, exp_pow] using (hb n).1
      · simp only [norm_zero]
        exact (Real.exp_pos _).le
    · intro n hn
      simp [hn]
  · rw [nonlinearRemainder, (hasDerivAt_degreeSlice hβ ht (Set.Ici 2) hz).deriv]
    simp only [Set.mem_Ici]
    apply htail
    · intro n
      split_ifs
      · simpa only [one_mul, exp_pow] using (hb n).2
      · simp only [norm_zero]
        exact (Real.exp_pos _).le
    · intro n hn
      simp [hn]

/-- The parameterized series is exactly the complete arithmetic phase evaluation. -/
theorem source_eq_character (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (z : ℂ) :
    source P β t z = ∑' n : ℕ,
      character P β z n / (n : ℂ) * (Real.exp (-t) : ℂ) ^ n := by
  unfold source degreeSlice
  simp only [Set.mem_univ, ↓reduceIte]
  apply tsum_congr
  intro n
  rw [term, baseCoefficient, character_eq_monomial P β z n]
  ring

/-- Restoring the original selected prime phases recovers the actual full twist. -/
theorem source_baseline {P : Finset ℕ} (hP : 2 ∉ P) (t : ℝ) :
    source P (fun _ => -1) t 1 = RHTower.LiouvilleTwistedDensity.exponentialDensity t := by
  rw [source_eq_character, character_baseline hP,
    RHTower.LiouvilleTwistedDensity.exponentialDensity_eq_density]
  rfl

/-- The constant degree slice is the full band-free cofactor density. -/
theorem degreeSlice_zero (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (z : ℂ) :
    degreeSlice {0} P β t z = cofactorDensity P t := by
  unfold degreeSlice cofactorDensity
  apply tsum_congr
  intro n
  by_cases hn : degree P n = 0
  · simp [hn, term, baseCoefficient, character_eq_twist_of_degree_zero hn,
      RHTower.LiouvilleTwistedDensity.coefficient]
  · simp [hn]

/-- The full nonlinear tail is exponentially negligible as the band moves to infinity. -/
theorem nonlinearRemainder_bounds_exp {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {T : ℝ} (hT : 0 < T)
    (hP : ∀ p ∈ P, T < (p : ℝ)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖nonlinearRemainder P β (1 / T) z‖ ≤ (T + 1) * Real.exp (-T) ∧
    ‖deriv (nonlinearRemainder P β (1 / T)) z‖ ≤ (T + 1) * Real.exp (-T) := by
  have ht : 0 < 1 / T := one_div_pos.mpr hT
  have hq : Real.exp (-(1 / T)) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos ht)
  have hm : (T + 1) * Real.exp (-(1 / T)) ≤ T := by
    calc
      _ = T * ((1 / T + 1) * Real.exp (-(1 / T))) := by field_simp; ring
      _ ≤ T * (Real.exp (1 / T) * Real.exp (-(1 / T))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (Real.add_one_le_exp (1 / T)) (Real.exp_pos _).le) hT.le
      _ = T := by rw [← Real.exp_add]; simp
  have hb : Real.exp (-T) / (1 - Real.exp (-(1 / T))) ≤ (T + 1) * Real.exp (-T) := by
    rw [div_le_iff₀ (sub_pos.mpr hq)]
    nlinarith [mul_le_mul_of_nonneg_right hm (Real.exp_pos (-T)).le]
  obtain ⟨hr, hd⟩ := nonlinearRemainder_bounds hβ hT hP hz
  exact ⟨hr.trans hb, hd.trans hb⟩

end
end RHTower.LiouvillePrimeBand
