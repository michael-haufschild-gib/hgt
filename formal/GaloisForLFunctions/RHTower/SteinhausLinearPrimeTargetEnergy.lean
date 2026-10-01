import GaloisForLFunctions.RHTower.SteinhausPrimeMixedFourthMoment
import GaloisForLFunctions.RHTower.SteinhausComplexConvolution

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Exact total mass of the linear square density. -/
theorem integral_normSq_linearPrimePoly
    (P : Finset ℕ) (b : ℕ → ℂ) (a : ℂ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ ω, ‖a + ∑ p ∈ P, b p * X p ω‖ ^ 2 ∂steinhausMeasure) =
      ‖a‖ ^ 2 + ∑ p ∈ P, ‖b p‖ ^ 2 := by
  classical
  let c : ℕ → ℂ := fun n => if n = 1 then a else b n
  have hP1 : 1 ∉ P := fun h => Nat.not_prime_one (hP 1 h)
  have he (ω : Omega) : a + ∑ p ∈ P, b p * X p ω =
      ∑ p ∈ insert 1 P, c p * X p ω := by
    rw [sum_insert hP1]
    simp only [c, ite_true, X_one, mul_one]
    congr 1
    exact sum_congr rfl (fun p hpP => by rw [if_neg (hP p hpP).ne_one])
  simp_rw [he]
  rw [integral_normSq_dpoly_complex c (insert 1 P)]
  · rw [sum_insert hP1]
    simp only [c, ite_true]
    congr 1
    exact sum_congr rfl (fun p hpP => by rw [if_neg (hP p hpP).ne_one])
  · intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact one_ne_zero
    · exact (hP n hn).ne_zero

/-- Constant, prime, and prime-product frequencies of a linear target
certificate are disjoint. Their exact energies therefore add. -/
theorem integral_primeTarget_linearDensity_energy
    (P : Finset ℕ) (u b : ℕ → ℂ) (a g : ℂ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ ω, ‖(∑ p ∈ P, u p * X p ω) - g‖ ^ 2 *
      ‖a + ∑ p ∈ P, b p * X p ω‖ ^ 2 ∂steinhausMeasure) =
      ‖g * a‖ ^ 2 + (∑ p ∈ P, ‖a * u p - g * b p‖ ^ 2) +
        (∑ p ∈ P, ‖u p‖ ^ 2) * (∑ p ∈ P, ‖b p‖ ^ 2) +
          ‖∑ p ∈ P, u p * (starRingEnd ℂ) (b p)‖ ^ 2 -
            ∑ p ∈ P, ‖u p‖ ^ 2 * ‖b p‖ ^ 2 := by
  classical
  let Q := prodSupport P P
  let S := insert 1 P ∪ Q
  let c : ℕ → ℂ := fun n =>
    if n = 1 then -(g * a) else
      if n ∈ P then a * u n - g * b n else dpolyComplexConv u b P P n
  have hP1 : 1 ∉ P := fun h => Nat.not_prime_one (hP 1 h)
  have hQ (n : ℕ) (hn : n ∈ Q) : n ≠ 0 ∧ n ≠ 1 ∧ n ∉ P := by
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := mem_image.mp hn
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    have hp2 := (hP p hp).two_le
    have hq2 := (hP q hq).two_le
    refine ⟨Nat.mul_ne_zero (hP p hp).ne_zero (hP q hq).ne_zero, by nlinarith, ?_⟩
    intro h
    exact Nat.not_prime_mul (hP p hp).ne_one (hP q hq).ne_one (hP (p * q) h)
  have hdisj : Disjoint (insert 1 P) Q := by
    apply disjoint_left.mpr
    intro n hn hqn
    rcases mem_insert.mp hn with rfl | hn
    · exact (hQ 1 hqn).2.1 rfl
    · exact (hQ n hqn).2.2 hn
  have hcP (p : ℕ) (hp : p ∈ P) : c p = a * u p - g * b p := by
    simp only [c, if_neg (hP p hp).ne_one, if_pos hp]
  have hcQ (n : ℕ) (hn : n ∈ Q) : c n = dpolyComplexConv u b P P n := by
    simp only [c, if_neg (hQ n hn).2.1, if_neg (hQ n hn).2.2]
  have hpoint (ω : Omega) :
      ((∑ p ∈ P, u p * X p ω) - g) * (a + ∑ p ∈ P, b p * X p ω) =
        ∑ n ∈ S, c n * X n ω := by
    rw [show S = insert 1 P ∪ Q from rfl, sum_union hdisj, sum_insert hP1]
    have h0 : c 1 * X 1 ω = -(g * a) := by simp [c, X_one]
    rw [h0, sum_congr rfl (fun p hp => congrArg (fun z => z * X p ω) (hcP p hp)),
      sum_congr rfl (fun n hn => congrArg (fun z => z * X n ω) (hcQ n hn))]
    change _ = _ + ∑ n ∈ prodSupport P P, dpolyComplexConv u b P P n * X n ω
    rw [← model_mul_complex u b P P (fun p hp => (hP p hp).ne_zero)
      (fun p hp => (hP p hp).ne_zero)]
    have he : (∑ p ∈ P, (a * u p - g * b p) * X p ω) =
        a * (∑ p ∈ P, u p * X p ω) - g * (∑ p ∈ P, b p * X p ω) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl (fun p _ => by ring)
    rw [he]
    ring
  have hnorm (ω : Omega) :
      ‖(∑ p ∈ P, u p * X p ω) - g‖ ^ 2 * ‖a + ∑ p ∈ P, b p * X p ω‖ ^ 2 =
        ‖∑ n ∈ S, c n * X n ω‖ ^ 2 := by
    rw [← hpoint, norm_mul, mul_pow]
  rw [integral_congr_ae (Filter.Eventually.of_forall hnorm), integral_normSq_dpoly_complex c S]
  · rw [show S = insert 1 P ∪ Q from rfl, sum_union hdisj, sum_insert hP1]
    have h0 : ‖c 1‖ ^ 2 = ‖g * a‖ ^ 2 := by simp [c]
    rw [h0, sum_congr rfl (fun p hp => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hcP p hp)),
      sum_congr rfl (fun n hn => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hcQ n hn))]
    change _ + ∑ n ∈ prodSupport P P, ‖dpolyComplexConv u b P P n‖ ^ 2 = _
    rw [← integral_normSq_product_steinhaus_eq_convolution u b P P
      (fun p hp => (hP p hp).ne_zero) (fun p hp => (hP p hp).ne_zero),
      integral_normSq_primePoly_mul_primePoly P u b hP]
    ring
  · intro n hn
    rcases mem_union.mp hn with hn | hn
    · rcases mem_insert.mp hn with rfl | hn
      · exact one_ne_zero
      · exact (hP n hn).ne_zero
    · exact (hQ n hn).1

end RHTower
