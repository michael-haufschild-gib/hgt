import GaloisForLFunctions.HTGeometry.LaguerreShiftSplits
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteRealRootDecomposition

/-!
# Real roots under the Laguerre shift `p ↦ p − c p′`

For a real polynomial `p` and `c ≠ 0`, `p − c p′ = −c·(p′ − p/c)` is a nonzero multiple of a
Laguerre shift, so the Rolle count `card_roots_le_laguerreShift` gives
(`card_roots_le_sub_C_mul_derivative_succ`)

`#{real roots of p} ≤ #{real roots of p − c p′} + 1`,

with multiplicity.  Since `p − c p′` has the degree of `p` and the number of real roots of a real
polynomial has the parity of its degree, the `+1` disappears (`card_roots_le_sub_C_mul_derivative`): the
operator `1 − cD` loses no real root and creates no nonreal root.  Composing `1 − bD` and `1 + bD`
with `b² = a` gives the same for the heat step `p ↦ p − a p″`, `a > 0`
(`card_roots_le_heatStep`, `nonrealCount_heatStep_le`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `p − c p′ = −c · (p′ − p/c)`, a nonzero multiple of a Laguerre shift. -/
theorem sub_C_mul_derivative_eq (p : ℝ[X]) {c : ℝ} (hc : c ≠ 0) :
    p - C c * derivative p = C (-c) * laguerreShift (1 / c) p := by
  rw [laguerreShift, mul_sub, ← mul_assoc, ← C_mul, show -c * (1 / c) = -1 by field_simp]
  simp only [C_neg, C_1]
  ring

/-- `p − c p′` loses at most one real root of `p` (the Rolle count `card_roots_le_laguerreShift`). -/
theorem card_roots_le_sub_C_mul_derivative_succ (p : ℝ[X]) {c : ℝ} (hc : c ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p - C c * derivative p).roots + 1 := by
  rw [sub_C_mul_derivative_eq p hc, roots_C_mul _ (neg_ne_zero.mpr hc)]
  exact card_roots_le_laguerreShift (1 / c) p

/-- The real roots of `A`, seen in `ℂ`, are exactly the real-axis roots of `A` mapped to `ℂ`. -/
theorem realPolynomialRealRootMultiset_eq_map_roots (A : ℝ[X]) :
    RiemannGaussian.realPolynomialRealRootMultiset A = A.roots.map Complex.ofRealHom := by
  classical
  ext z
  rw [RiemannGaussian.realPolynomialRealRootMultiset, Multiset.count_filter]
  by_cases hz : z.im = 0
  · rw [if_pos hz]
    have hzr : z = Complex.ofRealHom z.re := Complex.ext (by simp) (by simp [hz])
    rw [hzr, count_roots, ← eq_rootMultiplicity_map Complex.ofRealHom.injective,
      Multiset.count_map_eq_count' _ _ Complex.ofRealHom.injective, count_roots]
  · rw [if_neg hz, eq_comm, Multiset.count_eq_zero]
    intro hm
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hm
    exact hz (by simp)

/-- The number of real roots of a real polynomial has the parity of its degree. -/
theorem card_roots_add_two_mul_eq_natDegree (A : ℝ[X]) :
    ∃ u : ℕ, Multiset.card A.roots + 2 * u = A.natDegree := by
  refine ⟨(RiemannGaussian.realPolynomialUpperRootMultiset A).card, ?_⟩
  have h := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card A
  rwa [realPolynomialRealRootMultiset_eq_map_roots, Multiset.card_map] at h

theorem natDegree_sub_C_mul_derivative (p : ℝ[X]) (c : ℝ) :
    (p - C c * derivative p).natDegree = p.natDegree := by
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [derivative_of_natDegree_zero h0]; simp
  · exact natDegree_sub_eq_left_of_natDegree_lt
      ((natDegree_C_mul_le c _).trans_lt (natDegree_derivative_lt hpos.ne'))

theorem sub_C_mul_derivative_ne_zero {p : ℝ[X]} (hp : p ≠ 0) (c : ℝ) : p - C c * derivative p ≠ 0 := by
  intro h0
  rcases Nat.eq_zero_or_pos p.natDegree with h | hpos
  · rw [derivative_of_natDegree_zero h, mul_zero, sub_zero] at h0
    exact hp h0
  · have := natDegree_sub_C_mul_derivative p c
    rw [h0, natDegree_zero] at this
    omega

/-- **Hermite–Poulain, counting form.** For `c ≠ 0`, `p − c p′` has at least as many
real roots as `p`, with multiplicity. -/
theorem card_roots_le_sub_C_mul_derivative (p : ℝ[X]) {c : ℝ} (hc : c ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p - C c * derivative p).roots := by
  have h1 := card_roots_le_sub_C_mul_derivative_succ p hc
  obtain ⟨u, hu⟩ := card_roots_add_two_mul_eq_natDegree p
  obtain ⟨v, hv⟩ := card_roots_add_two_mul_eq_natDegree (p - C c * derivative p)
  rw [natDegree_sub_C_mul_derivative] at hv
  omega

/-- **The heat step loses no real root.** For `a > 0`, `p − a p″` has at least as many
real roots as `p`. -/
theorem card_roots_le_heatStep (p : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    Multiset.card p.roots ≤ Multiset.card (p - C a * derivative (derivative p)).roots := by
  set b := Real.sqrt a with hb
  have hb0 : b ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hbb : b * b = a := Real.mul_self_sqrt ha.le
  set q := p - C (-b) * derivative p with hq
  have h1 := card_roots_le_sub_C_mul_derivative p (neg_ne_zero.mpr hb0)
  have h2 := card_roots_le_sub_C_mul_derivative q hb0
  have e : q - C b * derivative q = p - C a * derivative (derivative p) := by
    rw [hq, derivative_sub, derivative_C_mul, ← hbb, C_mul]
    simp only [C_neg]
    ring
  rw [e] at h2
  exact h1.trans h2

/-- The heat step does not increase the number of nonreal roots `natDegree − #real roots`. -/
theorem nonrealCount_heatStep_le (p : ℝ[X]) {a : ℝ} (ha : 0 < a) :
    (p - C a * derivative (derivative p)).natDegree -
        Multiset.card (p - C a * derivative (derivative p)).roots ≤
      p.natDegree - Multiset.card p.roots := by
  have hdeg : (p - C a * derivative (derivative p)).natDegree = p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
    · rw [derivative_of_natDegree_zero h0]; simp
    · refine natDegree_sub_eq_left_of_natDegree_lt ((natDegree_C_mul_le a _).trans_lt ?_)
      have h1 := natDegree_derivative_le p
      have h2 := natDegree_derivative_le (derivative p)
      omega
  rw [hdeg]
  have := card_roots_le_heatStep p ha
  omega

end

end GaloisForLFunctions.HTGeometry
