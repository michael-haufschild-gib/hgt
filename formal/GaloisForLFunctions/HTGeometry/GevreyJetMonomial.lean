import GaloisForLFunctions.HTGeometry.GevreyWeightedNorm
import GaloisForLFunctions.HTGeometry.MvPolynomialTaylorFamily

/-!
# Weighted bounds for monomials in a perturbation

A monomial `∏ⱼ (gⱼ)^{αⱼ}` in series that all satisfy the same weighted Gevrey bound of size `ε`
satisfies a bound of size `ε^{|α|}`.  If moreover every factor vanishes to order `M` and the
monomial has degree at least two, the bound gains `M r` units of weight: two of the factors are
separated in the Cauchy product, and their factorials are then bounded away from the total
factorial by a binomial coefficient.

The same decomposition of a monomial into one factor and the rest shows that replacing the
perturbation by a truncation of it changes a monomial of degree at least two only in degrees above
the truncation order plus `M` — which is why the coefficient recursion of a nonlinear equation is
still a recursion.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι]

/-! ### Weighted bounds for monomials -/

theorem gevreyWeightBound_one {w r : ℕ} {A : ℝ} (hA : 0 < A) :
    GevreyWeightBound w 1 A r (1 : PowerSeries ℂ) := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hz : PowerSeries.coeff n (1 : PowerSeries ℂ) = 0 := by
      rw [PowerSeries.coeff_one, if_neg (by omega)]
    rw [hz, norm_zero, zero_mul]
    positivity

omit [DecidableEq ι] in
/-- **A monomial of degree `d` in factors of weighted size `ε` has weighted size `ε^d`.** -/
theorem gevreyWeightBound_jetMonomial {a r : ℕ} (ha : 2 ≤ a) {A ε : ℝ} (hA : 0 < A)
    (hε0 : 0 ≤ ε) (g : ι → PowerSeries ℂ) (hg : ∀ j, GevreyWeightBound a ε A r (g j)) :
    ∀ (d : ℕ) (α : ι →₀ ℕ), jetDegree α = d →
      GevreyWeightBound a (((2 : ℝ) ^ (a + 2)) ^ d * ε ^ d) A r (jetMonomial g α) := by
  intro d
  induction d with
  | zero =>
      intro α hα
      rw [jetDegree_eq_zero_iff.mp hα, jetMonomial_zero]
      simpa using gevreyWeightBound_one (w := a) (r := r) hA
  | succ d ih =>
      intro α hα
      obtain ⟨j, β, rfl, hβ⟩ := exists_jetDegree_pred hα
      rw [jetMonomial_add, jetMonomial_single]
      have h1 := ih β hβ
      have heq : (2 : ℝ) ^ (a + 2) * (((2 : ℝ) ^ (a + 2)) ^ d * ε ^ d) * ε
          = ((2 : ℝ) ^ (a + 2)) ^ (d + 1) * ε ^ (d + 1) := by ring
      rw [← heq]
      exact GevreyWeightBound.mul ha hA (by positivity) hε0 h1 (hg j)

/-! ### Divisibility of monomials -/

omit [DecidableEq ι] in
theorem X_pow_dvd_jetMonomial {M : ℕ} {g : ι → PowerSeries ℂ}
    (hg : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ M ∣ g j) :
    ∀ (d : ℕ) (α : ι →₀ ℕ), jetDegree α = d → 1 ≤ d →
      (PowerSeries.X : PowerSeries ℂ) ^ M ∣ jetMonomial g α := by
  intro d
  induction d with
  | zero => intro _ _ hd; omega
  | succ d _ =>
      intro α hα _
      obtain ⟨j, β, rfl, _⟩ := exists_jetDegree_pred hα
      rw [jetMonomial_add, jetMonomial_single]
      exact Dvd.dvd.mul_left (hg j) _

omit [DecidableEq ι] in
theorem X_pow_dvd_jetMonomial_sub {n : ℕ} {u v : ι → PowerSeries ℂ}
    (huv : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (u j - v j)) :
    ∀ (d : ℕ) (α : ι →₀ ℕ), jetDegree α = d →
      (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (jetMonomial u α - jetMonomial v α) := by
  intro d
  induction d with
  | zero =>
      intro α hα
      rw [jetDegree_eq_zero_iff.mp hα]
      simp
  | succ d ih =>
      intro α hα
      obtain ⟨j, β, rfl, hβ⟩ := exists_jetDegree_pred hα
      simp only [jetMonomial_add, jetMonomial_single]
      have hrw : jetMonomial u β * u j - jetMonomial v β * v j
          = (jetMonomial u β - jetMonomial v β) * u j + jetMonomial v β * (u j - v j) := by
        ring
      rw [hrw]
      exact dvd_add (Dvd.dvd.mul_right (ih β hβ) _) (Dvd.dvd.mul_left (huv j) _)

omit [DecidableEq ι] in
/-- **Replacing the perturbation by a truncation moves a monomial of degree at least two by a
higher order.** -/
theorem X_pow_dvd_jetMonomial_sub_of_two_le {n M : ℕ} {u v : ι → PowerSeries ℂ}
    (hv : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ M ∣ v j)
    (hu : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ M ∣ u j)
    (huv : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (u j - v j))
    (α : ι →₀ ℕ) (hα : 2 ≤ jetDegree α) :
    (PowerSeries.X : PowerSeries ℂ) ^ (n + M) ∣ (jetMonomial u α - jetMonomial v α) := by
  obtain ⟨d, hd⟩ : ∃ d, jetDegree α = d + 1 := ⟨jetDegree α - 1, by omega⟩
  obtain ⟨j, β, rfl, hβ⟩ := exists_jetDegree_pred hd
  have hd1 : 1 ≤ d := by
    have := jetDegree_add β (Finsupp.single j 1)
    rw [jetDegree_single] at this
    omega
  simp only [jetMonomial_add, jetMonomial_single]
  have hrw : jetMonomial u β * u j - jetMonomial v β * v j
      = (jetMonomial u β - jetMonomial v β) * u j + jetMonomial v β * (u j - v j) := by
    ring
  rw [hrw, pow_add]
  refine dvd_add (mul_dvd_mul (X_pow_dvd_jetMonomial_sub huv d β hβ) (hu j)) ?_
  have hswap : (PowerSeries.X : PowerSeries ℂ) ^ n * (PowerSeries.X : PowerSeries ℂ) ^ M
      = (PowerSeries.X : PowerSeries ℂ) ^ M * (PowerSeries.X : PowerSeries ℂ) ^ n := by
    ring
  rw [hswap]
  exact mul_dvd_mul (X_pow_dvd_jetMonomial hv d β hβ hd1) (huv j)

omit [DecidableEq ι] in
/-- **A monomial of degree at least two in factors vanishing to order `M` gains `M r` units of
weight.** -/
theorem gevreyWeightBound_jetMonomial_dvd {a M r : ℕ} (ha : 2 ≤ a) {A ε : ℝ} (hA : 0 < A)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (g : ι → PowerSeries ℂ)
    (hdvd : ∀ j, (PowerSeries.X : PowerSeries ℂ) ^ M ∣ g j)
    (hg : ∀ j, GevreyWeightBound a ε A r (g j)) (α : ι →₀ ℕ) (hα : 2 ≤ jetDegree α) :
    GevreyWeightBound (a + M * r)
      (((2 : ℝ) ^ (a + 2)) ^ (jetDegree α) * ((M ! : ℝ)) ^ r * 2 ^ (M * r) * ε ^ 2) A r
      (jetMonomial g α) := by
  obtain ⟨d, hd⟩ : ∃ d, jetDegree α = d + 1 := ⟨jetDegree α - 1, by omega⟩
  obtain ⟨j, β, rfl, hβ⟩ := exists_jetDegree_pred hd
  have hd1 : 1 ≤ d := by
    have := jetDegree_add β (Finsupp.single j 1)
    rw [jetDegree_single] at this
    omega
  have h1 := gevreyWeightBound_jetMonomial ha hA hε0 g hg d β hβ
  have hdvdβ := X_pow_dvd_jetMonomial hdvd d β hβ hd1
  have hmul := GevreyWeightBound.mul_of_dvd ha hA (by positivity) hε0 hdvdβ (hdvd j) h1 (hg j)
  rw [jetMonomial_add, jetMonomial_single]
  refine hmul.mono_const ?_ hA
  have hεd : ε ^ (d + 1) ≤ ε ^ 2 := pow_le_pow_of_le_one hε0 hε1 (by omega)
  have hKpos : (0 : ℝ) ≤ ((2 : ℝ) ^ (a + 2)) ^ (d + 1) * ((M ! : ℝ)) ^ r * 2 ^ (M * r) := by
    positivity
  calc (2 : ℝ) ^ (a + 2) * ((M ! : ℝ)) ^ r * 2 ^ (M * r)
        * (((2 : ℝ) ^ (a + 2)) ^ d * ε ^ d) * ε
      = (((2 : ℝ) ^ (a + 2)) ^ (d + 1) * ((M ! : ℝ)) ^ r * 2 ^ (M * r)) * ε ^ (d + 1) := by ring
    _ ≤ (((2 : ℝ) ^ (a + 2)) ^ (d + 1) * ((M ! : ℝ)) ^ r * 2 ^ (M * r)) * ε ^ 2 :=
        mul_le_mul_of_nonneg_left hεd hKpos
    _ = ((2 : ℝ) ^ (a + 2)) ^ (jetDegree (β + Finsupp.single j 1)) * ((M ! : ℝ)) ^ r
          * 2 ^ (M * r) * ε ^ 2 := by
        rw [hd]

/-! ### Finite sums -/

theorem GevreyWeightBound.finsetSum {w r : ℕ} {A : ℝ} {κ : Type*} (s : Finset κ)
    (f : κ → PowerSeries ℂ) (C : κ → ℝ)
    (h : ∀ i ∈ s, GevreyWeightBound w (C i) A r (f i)) :
    GevreyWeightBound w (∑ i ∈ s, C i) A r (∑ i ∈ s, f i) := by
  intro n
  rw [map_sum]
  calc ‖∑ i ∈ s, PowerSeries.coeff n (f i)‖ * ((n : ℝ) + 1) ^ w
      ≤ (∑ i ∈ s, ‖PowerSeries.coeff n (f i)‖) * ((n : ℝ) + 1) ^ w :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
    _ = ∑ i ∈ s, ‖PowerSeries.coeff n (f i)‖ * ((n : ℝ) + 1) ^ w := by rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ s, C i * A ^ n * ((n ! : ℝ)) ^ r :=
        Finset.sum_le_sum fun i hi => h i hi n
    _ = (∑ i ∈ s, C i) * A ^ n * ((n ! : ℝ)) ^ r := by
        rw [Finset.sum_mul, Finset.sum_mul]

theorem exists_common_gevreyWeightBound {κ : Type*} (f : κ → PowerSeries ℂ) (w r : ℕ)
    (s : Finset κ) (hf : ∀ i ∈ s, IsGevreySeries (r : ℝ) (f i)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ i ∈ s, GevreyWeightBound w C A r (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨1, 1, one_pos, one_pos, by simp⟩
  | insert a s ha ih =>
      intro hf
      obtain ⟨C, A, hC, hA, hs⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      obtain ⟨C', A', hC', hA', h'⟩ :=
        exists_gevreyWeightBound (hf a (Finset.mem_insert_self a s)) w
      refine ⟨max C C', max A A', lt_of_lt_of_le hC (le_max_left _ _),
        lt_of_lt_of_le hA (le_max_left _ _), fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ((h'.mono_const (le_max_right _ _) hA').mono_base hA' (le_max_right _ _)
          (le_of_lt (lt_of_lt_of_le hC' (le_max_right _ _))))
      · exact (((hs j hj).mono_const (le_max_left _ _) hA).mono_base hA (le_max_left _ _)
          (le_of_lt (lt_of_lt_of_le hC (le_max_left _ _))))

end GaloisForLFunctions.HTGeometry
