import GaloisForLFunctions.HTGeometry.RittTowerDescentStep
import GaloisForLFunctions.HTGeometry.RittSecondJetAffineConnection

/-!
# A power of the chain-rule factor is constant only in the trivial exponent

The scalars produced by the tower descent are monomials `q^i · ρ^k` in the multiplier and the
chain-rule factor.  The multiplier is a derivation constant; the chain-rule factor is not, as soon as
the map is not affine.  So the base derivation separates the two: if `ρ^k` equals a power of `q`,
then differentiating gives `k · ρ^{k−1} · dK ρ = 0`, and in characteristic zero with `dK ρ ≠ 0` that
forces `k = 0`.

This is what pins the exponents in the degenerate branch of the descent: a monomial element at the
last scaling level can be degenerate only if the accumulated `ρ`-exponent already vanished.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

theorem dK_one : Fr.dK 1 = 0 := by
  have h := Fr.dK_mul 1 1
  simp only [one_mul, mul_one] at h
  linear_combination -h

theorem dK_pow_succ (a : K) : ∀ n : ℕ, Fr.dK (a ^ (n + 1)) = ((n : K) + 1) * a ^ n * Fr.dK a
  | 0 => by simp
  | (n + 1) => by
      have ha : a ^ (n + 2) = a * a ^ (n + 1) := by ring
      rw [ha, Fr.dK_mul, dK_pow_succ a n]
      push_cast
      ring

theorem dK_inv {a : K} (ha : a ≠ 0) : Fr.dK a⁻¹ = -(Fr.dK a) / a ^ 2 := by
  have h := Fr.dK_mul a a⁻¹
  rw [mul_inv_cancel₀ ha, Fr.dK_one] at h
  have ha2 : (a : K) ^ 2 ≠ 0 := pow_ne_zero _ ha
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  rw [eq_div_iff ha2]
  linear_combination (-a) * h - (Fr.dK a) * hinv

/-- The base derivation kills every integer power of a constant. -/
theorem dK_zpow_eq_zero {a : K} (ha : a ≠ 0) (h : Fr.dK a = 0) (k : ℤ) : Fr.dK (a ^ k) = 0 := by
  have hnat : ∀ n : ℕ, Fr.dK (a ^ n) = 0 := by
    intro n
    cases n with
    | zero => simpa using Fr.dK_one
    | succ n => rw [Fr.dK_pow_succ, h, mul_zero]
  rcases lt_or_ge k 0 with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hn, zpow_neg, zpow_natCast, Fr.dK_inv (pow_ne_zero _ ha), hnat n]
    simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    rw [hn, zpow_natCast, hnat n]

/-- **A power of a non-constant is never a power of a constant, except trivially.** -/
theorem zpow_exponent_eq_zero_of_eq_zpow_const [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hbconst : Fr.dK b = 0) (haconst : Fr.dK a ≠ 0) {k j : ℤ} (h : a ^ k = b ^ j) : k = 0 := by
  by_contra hk
  have key : ∀ (n : ℕ) (jj : ℤ), a ^ ((n : ℤ) + 1) = b ^ jj → False := by
    intro n jj hn
    have hd := congrArg Fr.dK hn
    rw [Fr.dK_zpow_eq_zero hb hbconst] at hd
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      Fr.dK_pow_succ] at hd
    have hn1 : ((n : K) + 1) ≠ 0 := by
      rw [show ((n : K) + 1) = ((n + 1 : ℕ) : K) by push_cast; ring]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rcases mul_eq_zero.mp hd with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hn1 h2
      · exact (pow_ne_zero n ha) h2
    · exact haconst h1
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · refine key (-k - 1).toNat (-j) ?_
    rw [Int.toNat_of_nonneg (by omega), show (-k - 1 + 1 : ℤ) = -k by ring, zpow_neg, zpow_neg, h]
  · refine key (k - 1).toNat j ?_
    rw [Int.toNat_of_nonneg (by omega), show (k - 1 + 1 : ℤ) = k by ring, h]

/-- **The chain rule on the base.**  The frame's chain rule restricts to the coefficient field. -/
theorem dK_psi (a : K) : Fr.dK (Fr.ψ a) = Fr.ρ * Fr.ψ (Fr.dK a) := by
  refine (algebraMap K L).injective ?_
  have h := Fr.chain (algebraMap K L a)
  rw [Fr.comp, Fr.d_base, Fr.d_base, Fr.comp] at h
  rw [map_mul]
  exact h

/-- **A `ψ`-fixed base element carries an invariant vector field.**  If `ψ(u) = u` with `u ≠ 0`, its
logarithmic derivative `v = dK(u)/u` satisfies `ρ·ψ(v) = v`.  So the degenerate branch of the tower
descent either produces an invariant rational vector field, or says that `u` is a derivation
constant. -/
theorem invariantVectorField_of_psi_fixed {u : K} (hu : u ≠ 0) (h : Fr.ψ u = u) :
    Fr.ρ * Fr.ψ (Fr.dK u / u) = Fr.dK u / u := by
  have hd := Fr.dK_psi u
  rw [h] at hd
  have hψu : Fr.ψ u ≠ 0 := by
    rw [h]; exact hu
  rw [map_div₀, h]
  field_simp
  linear_combination -hd

end RittFrame

end GaloisForLFunctions.HTGeometry
