import GaloisForLFunctions.SurfaceOfSpecZ.TheTwoHalfProducts

/-!
# The archimedean place of the surface is not the archimedean fibre of `ℙ¹_ℤ`

`TheTwoHalfProducts` writes the intersection of distinct Frobenius graphs of `Spec ℤ` as an
archimedean term `min/(1 − (min/max)²)` plus the gcd-twisted torsion intersection `G(m, n) I(m, n)` on
`ℙ¹_ℤ`. This file shows that the archimedean term cannot be moved to `ℙ¹_ℤ` as well.

On the archimedean fibre of `ℙ¹_ℤ` with a rotation-invariant (toric) Green function `g`, two torsion
orbits pair by `P_g(m, n) = Σ_{ζ ∈ O_m} Σ_{η ∈ O_n} g(ζ η⁻¹)` (`torsionPairing`). For coprime orders the
Chinese remainder theorem identifies `O_m × O_n` with `O_{mn}` through `(ζ, η) ↦ ζ η⁻¹`, so
`P_g(m, n) = P_g(1, mn)` (`torsionPairing_of_coprime`): **toric pairings of coprime orbits depend only on
the product of the orders.** Weil's pairings depend on the ratio: `Γ_2 · Γ_3 = 18/5` but
`Γ_1 · Γ_6 = 36/35` (`frobeniusIntersection_two_three`, `frobeniusIntersection_one_six`), with no prime
contribution in either. Hence no toric Green function makes the whole Frobenius intersection a
gcd-twisted torsion pairing (`not_exists_toric_frobeniusIntersection`).

With `TheFrobeniusZonotopeSurface`: the cusp channel `min(m, n)` is integral and toric, the prime
channel is a torsion intersection on `ℙ¹_ℤ`, and the jets of the trivial zeros are neither. Already
`Γ_1 · Γ_2 = 4/3 + log 2` (`frobeniusIntersection_one_two`): one cusp, a jet tower of total weight
`1/3`, and the point of `ℙ¹_ℤ` over `2`.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory

/-- The pairing of the torsion orbits `O_m, O_n` by a rotation-invariant Green function `g`. -/
def torsionPairing (g : ℂ → ℝ) (m n : ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, g (ζ * η⁻¹)

/-- The sum of `g` over one orbit. -/
def orbitSum (g : ℂ → ℝ) (k : ℕ) : ℝ := ∑ ω ∈ primitiveRoots k ℂ, g ω

/-- Pairing with the orbit `O_1 = {1}` is the orbit sum: inversion permutes `O_k`. -/
theorem torsionPairing_one (g : ℂ → ℝ) {k : ℕ} (hk : 0 < k) :
    torsionPairing g 1 k = orbitSum g k := by
  have h1 : primitiveRoots 1 ℂ = {1} := by
    ext x; simp
  rw [torsionPairing, h1, sum_singleton, orbitSum]
  refine sum_nbij' (fun η => η⁻¹) (fun η => η⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro η hη
    exact (mem_primitiveRoots hk).mpr ((mem_primitiveRoots hk).mp hη).inv
  · intro η hη
    exact (mem_primitiveRoots hk).mpr ((mem_primitiveRoots hk).mp hη).inv
  · intro η _; exact inv_inv η
  · intro η _; exact inv_inv η
  · intro η _; simp

/-- **Coprime orbits pair through their product.** -/
theorem torsionPairing_of_coprime (g : ℂ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) : torsionPairing g m n = orbitSum g (m * n) := by
  have hmn0 : 0 < m * n := Nat.mul_pos hm hn
  rw [torsionPairing, ← sum_product', orbitSum]
  have hprim : ∀ x ∈ primitiveRoots m ℂ ×ˢ primitiveRoots n ℂ,
      IsPrimitiveRoot (x.1 * x.2⁻¹) (m * n) := by
    intro x hx
    rw [mem_product] at hx
    have h1 := (mem_primitiveRoots hm).mp hx.1
    have h2 := ((mem_primitiveRoots hn).mp hx.2).inv
    rw [h1.eq_orderOf, h2.eq_orderOf, ← Commute.orderOf_mul_eq_mul_orderOf_of_coprime
      (Commute.all _ _) (by rw [← h1.eq_orderOf, ← h2.eq_orderOf]; exact hmn)]
    exact IsPrimitiveRoot.orderOf _
  have hinj : ∀ x ∈ primitiveRoots m ℂ ×ˢ primitiveRoots n ℂ,
      ∀ y ∈ primitiveRoots m ℂ ×ˢ primitiveRoots n ℂ,
      x.1 * x.2⁻¹ = y.1 * y.2⁻¹ → x = y := by
    intro x hx y hy hxy
    rw [mem_product] at hx hy
    have hx1 := (mem_primitiveRoots hm).mp hx.1
    have hx2 := (mem_primitiveRoots hn).mp hx.2
    have hy1 := (mem_primitiveRoots hm).mp hy.1
    have hy2 := (mem_primitiveRoots hn).mp hy.2
    have hne1 : x.1 ≠ 0 := hx1.ne_zero hm.ne'
    have hne2 : x.2 ≠ 0 := hx2.ne_zero hn.ne'
    have hne3 : y.1 ≠ 0 := hy1.ne_zero hm.ne'
    have hne4 : y.2 ≠ 0 := hy2.ne_zero hn.ne'
    set w := x.1 * y.1⁻¹ with hw
    have hw2 : w = x.2 * y.2⁻¹ := by
      rw [hw]; field_simp; field_simp at hxy; linear_combination hxy
    have hwm : w ^ m = 1 := by rw [hw, mul_pow, inv_pow, hx1.pow_eq_one, hy1.pow_eq_one]; simp
    have hwn : w ^ n = 1 := by rw [hw2, mul_pow, inv_pow, hx2.pow_eq_one, hy2.pow_eq_one]; simp
    have hw1 : w = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hwm, hwn⟩
      rwa [Nat.Coprime.gcd_eq_one hmn, pow_one] at this
    have e1 : x.1 = y.1 := by
      rw [hw] at hw1; field_simp at hw1; exact hw1
    have e2 : x.2 = y.2 := by
      rw [hw2] at hw1; field_simp at hw1; exact hw1
    exact Prod.ext e1 e2
  refine sum_bij (fun x _ => x.1 * x.2⁻¹) (fun x hx => (mem_primitiveRoots hmn0).mpr (hprim x hx))
    (fun x hx y hy h => hinj x hx y hy h) ?_ (fun _ _ => rfl)
  have hcard : (primitiveRoots (m * n) ℂ).card ≤
      (primitiveRoots m ℂ ×ˢ primitiveRoots n ℂ).card := by
    rw [card_product, (Complex.isPrimitiveRoot_exp _ hmn0.ne').card_primitiveRoots,
      (Complex.isPrimitiveRoot_exp _ hm.ne').card_primitiveRoots,
      (Complex.isPrimitiveRoot_exp _ hn.ne').card_primitiveRoots, Nat.totient_mul hmn]
  intro b hb
  obtain ⟨a, ha, hab⟩ := surj_on_of_inj_on_of_card_le (fun x _ => x.1 * x.2⁻¹)
    (fun x hx => (mem_primitiveRoots hmn0).mpr (hprim x hx))
    (fun x y hx hy h => hinj x hx y hy h) hcard b hb
  exact ⟨a, ha, hab.symm⟩

/-- **Toric pairings of coprime orbits depend only on the product of the orders.** -/
theorem torsionPairing_eq_of_coprime (g : ℂ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) : torsionPairing g m n = torsionPairing g 1 (m * n) := by
  rw [torsionPairing_of_coprime g hm hn hmn, torsionPairing_one g (Nat.mul_pos hm hn)]

/-! ### Weil's pairings depend on the ratio -/

theorem gcdTwist_of_coprime {m n : ℕ} (h : Nat.Coprime m n) : gcdTwist m n = 1 := by
  rw [gcdTwist_eq, Nat.Coprime.gcd_eq_one h]; simp

theorem frobeniusIntersection_two_three : frobeniusIntersection 2 3 = 18 / 5 := by
  rw [frobeniusIntersection_eq (by norm_num) (by norm_num) (by norm_num),
    orbitIntersection_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem frobeniusIntersection_one_six : frobeniusIntersection 1 6 = 36 / 35 := by
  rw [frobeniusIntersection_eq (by norm_num) (by norm_num) (by norm_num),
    orbitIntersection_eq (by norm_num) (by norm_num) (by norm_num)]
  have h6 : Λ 6 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg (by decide)]
  norm_num [h6]

theorem frobeniusIntersection_one_two : frobeniusIntersection 1 2 = 4 / 3 + Real.log 2 := by
  rw [frobeniusIntersection_eq (by norm_num) (by norm_num) (by norm_num),
    orbitIntersection_eq (by norm_num) (by norm_num) (by norm_num), gcdTwist_of_coprime (by norm_num)]
  norm_num [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]

/-- **The archimedean place is not toric.** No rotation-invariant Green function on the archimedean
fibre of `ℙ¹_ℤ` turns the Frobenius intersection of `Spec ℤ` into a gcd-twisted torsion pairing. -/
theorem not_exists_toric_frobeniusIntersection :
    ¬ ∃ g : ℂ → ℝ, ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      frobeniusIntersection m n = gcdTwist m n * torsionPairing g m n := by
  rintro ⟨g, hg⟩
  have h23 := hg 2 3 (by norm_num) (by norm_num) (by norm_num)
  have h16 := hg 1 6 (by norm_num) (by norm_num) (by norm_num)
  rw [frobeniusIntersection_two_three, gcdTwist_of_coprime (by norm_num), one_mul,
    torsionPairing_eq_of_coprime g (by norm_num) (by norm_num) (by norm_num)] at h23
  rw [frobeniusIntersection_one_six, gcdTwist_of_coprime (by norm_num), one_mul] at h16
  norm_num at h23
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
