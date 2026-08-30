import GaloisForLFunctions.HTGeometry.RittBaseExponent

/-!
# The logarithmic derivative turns an eigen-relation into a named obstruction

The scalars the tower descent produces are monomials `q^i·ρ^k`, and the `q`-exponent is invisible to
the logarithmic derivative because the multiplier is a derivation constant.  So passing an
eigen-relation

`ψ(u) = c·u`,  `u ≠ 0`,  `c ≠ 0`

to logarithmic derivatives collapses it: with `v = dK u / u` and the base chain rule
`dK ∘ ψ = ρ · (ψ ∘ dK)`,

`ρ · ψ(v) = v + dK c / c`,

and for `c = q^i·ρ^k` the right-hand inhomogeneity is exactly `k · dK ρ / ρ`.  Hence

* `k ≠ 0` gives, after scaling by `−k`, the **rational affine-connection equation**
  `ρ·ψ(a) = a − dK ρ / ρ`;
* `k = 0` gives `ρ·ψ(v) = v`, an **invariant rational vector field**.

Both are obstructions the corpus already studies, and neither sees the `q`-exponent — so the
exponent cancellations that make the raw eigen-relation degenerate are harmless here.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-- The logarithmic derivative on the base. -/
def dKLog (a : K) : K := Fr.dK a / a

theorem dKLog_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Fr.dKLog (a * b) = Fr.dKLog a + Fr.dKLog b := by
  rw [dKLog, dKLog, dKLog, Fr.dK_mul]
  field_simp

theorem dKLog_one : Fr.dKLog 1 = 0 := by
  rw [dKLog, Fr.dK_one, zero_div]

theorem dKLog_inv {a : K} (ha : a ≠ 0) : Fr.dKLog a⁻¹ = -Fr.dKLog a := by
  have h := Fr.dKLog_mul ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, Fr.dKLog_one] at h
  linear_combination -h

theorem dKLog_zpow {a : K} (ha : a ≠ 0) (k : ℤ) : Fr.dKLog (a ^ k) = (k : K) * Fr.dKLog a := by
  have hnat : ∀ n : ℕ, Fr.dKLog (a ^ n) = (n : K) * Fr.dKLog a := by
    intro n
    induction n with
    | zero => simpa using Fr.dKLog_one
    | succ n ih =>
        rw [pow_succ, Fr.dKLog_mul (pow_ne_zero n ha) ha, ih]
        push_cast
        ring
  rcases lt_or_ge k 0 with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hn, zpow_neg, zpow_natCast, Fr.dKLog_inv (pow_ne_zero n ha), hnat n]
    push_cast
    ring
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    rw [hn, zpow_natCast, hnat n]
    push_cast
    ring

/-- **The logarithmic form of an eigen-relation.** -/
theorem dKLog_relation_of_eigen {u c : K} (hu : u ≠ 0) (hc : c ≠ 0) (h : Fr.ψ u = c * u) :
    Fr.ρ * Fr.ψ (Fr.dKLog u) = Fr.dKLog u + Fr.dKLog c := by
  have hψu : Fr.ψ u ≠ 0 := by
    rw [h]
    exact mul_ne_zero hc hu
  have hchain := Fr.dK_psi u
  rw [h, Fr.dK_mul] at hchain
  have hψinv : Fr.ψ (Fr.dKLog u) = Fr.ψ (Fr.dK u) / (c * u) := by
    rw [dKLog, map_div₀, h]
  rw [hψinv, dKLog, dKLog]
  field_simp
  linear_combination -hchain

/-- **The two named obstructions.**  A monomial eigenvalue `q^i·ρ^k` with `q` a derivation constant
turns the logarithmic relation into the affine-connection equation when `k ≠ 0`, and into the
invariant-vector-field equation when `k = 0`. -/
theorem dKLog_relation_of_monomial_eigen [CharZero K] {u q : K} {i k : ℤ}
    (hu : u ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (h : Fr.ψ u = q ^ i * Fr.ρ ^ k * u) :
    Fr.ρ * Fr.ψ (Fr.dKLog u) = Fr.dKLog u + (k : K) * Fr.dKLog Fr.ρ := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hc0 : q ^ i * Fr.ρ ^ k ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq) (zpow_ne_zero _ hρ0)
  have hlog : Fr.dKLog (q ^ i * Fr.ρ ^ k) = (k : K) * Fr.dKLog Fr.ρ := by
    rw [Fr.dKLog_mul (zpow_ne_zero _ hq) (zpow_ne_zero _ hρ0), Fr.dKLog_zpow hq,
      Fr.dKLog_zpow hρ0]
    have : Fr.dKLog q = 0 := by rw [dKLog, hqconst, zero_div]
    rw [this, mul_zero, zero_add]
  rw [← hlog]
  exact Fr.dKLog_relation_of_eigen hu hc0 h

/-- **The affine connection from a nonzero weight.** -/
theorem exists_affineConnection_of_monomial_eigen [CharZero K] {u q : K} {i k : ℤ}
    (hu : u ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0) (hk : k ≠ 0)
    (h : Fr.ψ u = q ^ i * Fr.ρ ^ k * u) :
    ∃ a : K, Fr.ρ * Fr.ψ a = a - Fr.dKLog Fr.ρ := by
  have hkK : ((k : K)) ≠ 0 := Int.cast_ne_zero.mpr hk
  refine ⟨-(Fr.dKLog u) / (k : K), ?_⟩
  have hrel := Fr.dKLog_relation_of_monomial_eigen hu hq hqconst h
  rw [map_div₀, map_neg, map_intCast]
  field_simp
  linear_combination -hrel

end RittFrame

end GaloisForLFunctions.HTGeometry
