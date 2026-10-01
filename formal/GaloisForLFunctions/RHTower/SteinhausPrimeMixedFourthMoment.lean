import GaloisForLFunctions.RHTower.SteinhausFourthMoment
import GaloisForLFunctions.RHTower.PrimeSecondMomentDivergence

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel
open GaloisForLFunctions.RHTower

private theorem prime_mixed_diagonal_sum (P : Finset ℕ) (u b : ℕ → ℂ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, ∑ t ∈ P,
      if p * r = q * t then u p * (starRingEnd ℂ) (u q) * b r * (starRingEnd ℂ) (b t) else 0) =
      (∑ p ∈ P, u p * (starRingEnd ℂ) (u p)) * (∑ p ∈ P, b p * (starRingEnd ℂ) (b p)) +
        (∑ p ∈ P, u p * (starRingEnd ℂ) (b p)) * (∑ p ∈ P, (starRingEnd ℂ) (u p) * b p) -
          ∑ p ∈ P, (u p * (starRingEnd ℂ) (u p)) * (b p * (starRingEnd ℂ) (b p)) := by
  classical
  have hsplit (p) (hp : p ∈ P) (q) (hq : q ∈ P) (r) (hr : r ∈ P) (t : ℕ) :
      p * r = q * t ↔ ((p = q ∧ r = t) ∨ (p = t ∧ r = q)) := by
    constructor
    · exact prime_mul_eq_prime_mul (hP p hp) (hP q hq) (hP r hr)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring
  have hinner (p) (hp : p ∈ P) (q) (hq : q ∈ P) (r) (hr : r ∈ P) :
      (∑ t ∈ P, if p * r = q * t then u p * (starRingEnd ℂ) (u q) * b r * (starRingEnd ℂ) (b t) else 0) =
        if p = q then (u p * (starRingEnd ℂ) (u p)) * (b r * (starRingEnd ℂ) (b r))
        else if r = q then u p * (starRingEnd ℂ) (u q) * b q * (starRingEnd ℂ) (b p) else 0 := by
    by_cases hpq : p = q
    · subst q
      have he (t : ℕ) : p * r = p * t ↔ r = t := by
        constructor
        · intro h
          rcases (hsplit p hp p hp r hr t).mp h with h | h
          · exact h.2
          · exact h.2.trans h.1
        · rintro rfl; rfl
      simp only [he, sum_ite_eq, if_pos hr, ite_true]
      ring
    · by_cases hrq : r = q
      · subst r
        have he (t : ℕ) : p * q = q * t ↔ p = t := by
          rw [hsplit p hp q hq q hq t]
          simp [hpq]
        simp [he, hp, hpq]
      · have he (t : ℕ) : p * r ≠ q * t := by
          intro h
          rcases (hsplit p hp q hq r hr t).mp h with h | h
          · exact hpq h.1
          · exact hrq h.2
        simp [he, hpq, hrq]
  have hthird (p) (hp : p ∈ P) (q) (hq : q ∈ P) :
      (∑ r ∈ P, ∑ t ∈ P, if p * r = q * t then u p * (starRingEnd ℂ) (u q) * b r * (starRingEnd ℂ) (b t) else 0) =
        (if p = q then (u p * (starRingEnd ℂ) (u p)) * (∑ r ∈ P, b r * (starRingEnd ℂ) (b r)) else 0) +
          u p * (starRingEnd ℂ) (u q) * b q * (starRingEnd ℂ) (b p) -
            (if p = q then (u p * (starRingEnd ℂ) (u p)) * (b p * (starRingEnd ℂ) (b p)) else 0) := by
    rw [sum_congr rfl (fun r hr => hinner p hp q hq r hr)]
    by_cases hpq : p = q
    · subst q
      simp only [ite_true, eq_self, ← mul_sum]
      ring
    · simp [hpq, hq]
  have hsecond (p) (hp : p ∈ P) :
      (∑ q ∈ P, ∑ r ∈ P, ∑ t ∈ P,
        if p * r = q * t then u p * (starRingEnd ℂ) (u q) * b r * (starRingEnd ℂ) (b t) else 0) =
        (u p * (starRingEnd ℂ) (u p)) * (∑ r ∈ P, b r * (starRingEnd ℂ) (b r)) +
          (u p * (starRingEnd ℂ) (b p)) * (∑ q ∈ P, (starRingEnd ℂ) (u q) * b q) -
            (u p * (starRingEnd ℂ) (u p)) * (b p * (starRingEnd ℂ) (b p)) := by
    rw [sum_congr rfl (fun q hq => hthird p hp q hq), sum_sub_distrib, sum_add_distrib]
    simp only [sum_ite_eq, if_pos hp]
    congr 1
    congr 1
    rw [mul_sum]
    exact sum_congr rfl (fun q _ => by ring)
  rw [sum_congr rfl (fun p hp => hsecond p hp), sum_sub_distrib, sum_add_distrib,
    ← sum_mul, ← sum_mul]

/-- Exact mixed fourth moment of two complex prime carriers. Both pairings
are retained and their common diagonal is subtracted exactly once. -/
theorem integral_normSq_primePoly_mul_primePoly
    (P : Finset ℕ) (u b : ℕ → ℂ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ ω, ‖∑ p ∈ P, u p * X p ω‖ ^ 2 * ‖∑ p ∈ P, b p * X p ω‖ ^ 2
      ∂steinhausMeasure) =
      (∑ p ∈ P, ‖u p‖ ^ 2) * (∑ p ∈ P, ‖b p‖ ^ 2) +
        ‖∑ p ∈ P, u p * (starRingEnd ℂ) (b p)‖ ^ 2 - ∑ p ∈ P, ‖u p‖ ^ 2 * ‖b p‖ ^ 2 := by
  classical
  let F := fun p q r t : ℕ => u p * (starRingEnd ℂ) (u q) * b r * (starRingEnd ℂ) (b t)
  let C := fun (p q r t : ℕ) (ω : Omega) =>
    X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω)
  have hpoint (ω : Omega) :
      ((‖∑ p ∈ P, u p * X p ω‖ ^ 2 * ‖∑ p ∈ P, b p * X p ω‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, ∑ t ∈ P, F p q r t * C p q r t ω := by
    have he (a : ℕ → ℂ) : ((‖∑ p ∈ P, a p * X p ω‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ P, ∑ q ∈ P, (a p * X p ω) *
          ((starRingEnd ℂ) (a q) * (starRingEnd ℂ) (X q ω)) := by
      rw [ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
      simp only [map_mul]
    rw [ofReal_mul, he u, he b, sum_mul]
    apply sum_congr rfl; intro p _
    rw [sum_mul]
    apply sum_congr rfl; intro q _
    rw [mul_sum]
    apply sum_congr rfl; intro r _
    rw [mul_sum]
    apply sum_congr rfl; intro t _
    dsimp only [F, C]
    ring
  have hI (p q r t : ℕ) : Integrable (fun ω => F p q r t * C p q r t ω) steinhausMeasure :=
    integrable_smul_X_four _ p q r t
  have hI1 (p q r : ℕ) : Integrable (fun ω => ∑ t ∈ P, F p q r t * C p q r t ω) steinhausMeasure :=
    integrable_finsetSum _ (fun t _ => hI p q r t)
  have hI2 (p q : ℕ) : Integrable (fun ω => ∑ r ∈ P, ∑ t ∈ P,
      F p q r t * C p q r t ω) steinhausMeasure :=
    integrable_finsetSum _ (fun r _ => hI1 p q r)
  have hI3 (p : ℕ) : Integrable (fun ω => ∑ q ∈ P, ∑ r ∈ P, ∑ t ∈ P,
      F p q r t * C p q r t ω) steinhausMeasure :=
    integrable_finsetSum _ (fun q _ => hI2 p q)
  have hcast :
      ((∫ ω, ‖∑ p ∈ P, u p * X p ω‖ ^ 2 * ‖∑ p ∈ P, b p * X p ω‖ ^ 2
        ∂steinhausMeasure : ℝ) : ℂ) =
        ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, ∑ t ∈ P,
          if p * r = q * t then F p q r t else 0 := by
    rw [← integral_complex_ofReal, integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_finsetSum _ (fun p _ => hI3 p)]
    apply sum_congr rfl; intro p hp
    rw [integral_finsetSum _ (fun q _ => hI2 p q)]
    apply sum_congr rfl; intro q hq
    rw [integral_finsetSum _ (fun r _ => hI1 p q r)]
    apply sum_congr rfl; intro r hr
    rw [integral_finsetSum _ (fun t _ => hI p q r t)]
    apply sum_congr rfl; intro t ht
    rw [integral_const_mul]
    change F p q r t * (∫ ω, X p ω * (starRingEnd ℂ) (X q ω) * X r ω * (starRingEnd ℂ) (X t ω)
      ∂steinhausMeasure) = _
    rw [integral_X_four (hP p hp).ne_zero (hP q hq).ne_zero
      (hP r hr).ne_zero (hP t ht).ne_zero]
    split_ifs <;> simp
  dsimp only [F] at hcast
  rw [prime_mixed_diagonal_sum P u b hP] at hcast
  have hconj : (∑ p ∈ P, (starRingEnd ℂ) (u p) * b p) = (starRingEnd ℂ) (∑ p ∈ P, u p * (starRingEnd ℂ) (b p)) := by
    simp only [map_sum, map_mul, Complex.conj_conj]
  rw [hconj, Complex.mul_conj'] at hcast
  simp only [Complex.mul_conj'] at hcast
  exact_mod_cast hcast

end RHTower
