import GaloisForLFunctions.HTGeometry.RittBaseExponent

/-!
# Logarithmic derivatives of eigenvectors

The chain rule turns the logarithmic derivative of an eigenvector into a solution of an *affine*
transport equation whose inhomogeneity is the logarithmic derivative of the eigenvalue, divided by
the chain-rule factor.  Two consequences are recorded.

Over the big field: an eigenvector `σ v = c·v` has `σ(dv/v) = ρ^{−1}·(dv/v) + (dc)/(ρ·c)`, so an
eigenvalue that is not a derivation constant produces an affine datum with a base inhomogeneity and
no coupling.  For a monomial eigenvalue `q^i·ρ^k` with `q` constant the inhomogeneity is exactly
`k·(dρ)/ρ²`, nonzero precisely when the chain-rule exponent is.

Over the base: a shift-fixed element is either a derivation constant, or its logarithmic derivative
is an eigenvector of the base map with eigenvalue `ρ^{−1}` — a nontrivial exponent pair, hence
Ritt's order-one form.  So the monomial branch of the level classifications, whose coefficient is
only known to be shift-fixed, is not free: the coefficient must be a derivation constant.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The logarithmic derivative of an eigenvector solves an affine transport equation.** -/
theorem sigma_logDeriv_of_eigen (Fr : RittFrame K L) {v : L} (hv0 : v ≠ 0) {c : K} (hc : c ≠ 0)
    (hrel : Fr.σ v = algebraMap K L c * v) :
    Fr.σ (Fr.d v / v) = algebraMap K L Fr.ρ⁻¹ * (Fr.d v / v)
      + algebraMap K L (Fr.dK c / (Fr.ρ * c)) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hρL : algebraMap K L Fr.ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hcL : algebraMap K L c ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hc
  have hchain := Fr.chain v
  have hd : Fr.d (Fr.σ v) = algebraMap K L (Fr.dK c) * v + algebraMap K L c * Fr.d v := by
    rw [hrel, Fr.d_mul, Fr.d_base]
  have hσdv : algebraMap K L Fr.ρ * Fr.σ (Fr.d v)
      = algebraMap K L (Fr.dK c) * v + algebraMap K L c * Fr.d v := by
    rw [← hd]
    linear_combination -hchain
  have hσv0 : Fr.σ v ≠ 0 := by
    rw [hrel]
    exact mul_ne_zero hcL hv0
  have hmapinv : algebraMap K L Fr.ρ⁻¹ = (algebraMap K L Fr.ρ)⁻¹ := map_inv₀ _ _
  have hmapdiv : algebraMap K L (Fr.dK c / (Fr.ρ * c))
      = algebraMap K L (Fr.dK c) / (algebraMap K L Fr.ρ * algebraMap K L c) := by
    rw [map_div₀, map_mul]
  rw [map_div₀, hrel, hmapinv, hmapdiv]
  field_simp
  linear_combination hσdv

/-- The power rule for the base derivation, at an integer exponent. -/
theorem dK_zpow (Fr : RittFrame K L) {a : K} (ha : a ≠ 0) (k : ℤ) :
    Fr.dK (a ^ k) = (k : K) * a ^ (k - 1) * Fr.dK a := by
  have hnat : ∀ n : ℕ, Fr.dK (a ^ n) = (n : K) * a ^ ((n : ℤ) - 1) * Fr.dK a := by
    intro n
    cases n with
    | zero => simp [Fr.dK_one]
    | succ n =>
        rw [Fr.dK_pow_succ]
        push_cast
        rw [show ((n : ℤ) + 1 - 1) = (n : ℤ) by ring, zpow_natCast]
  rcases lt_or_ge k 0 with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    have han : (a : K) ^ n ≠ 0 := pow_ne_zero _ ha
    have hz1 : (a : K) ^ ((n : ℤ) - 1) = a ^ n / a := by
      rw [zpow_sub₀ ha, zpow_natCast, zpow_one]
    have hz2 : (a : K) ^ (-(n : ℤ) - 1) = 1 / (a ^ n * a) := by
      rw [zpow_sub₀ ha, zpow_neg, zpow_natCast, zpow_one, one_div, mul_inv, div_eq_mul_inv]
    rw [zpow_neg, zpow_natCast, Fr.dK_inv han, hnat n, hz1, hz2]
    push_cast
    field_simp
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    subst hn
    rw [zpow_natCast, hnat n]
    norm_cast

/-- For a monomial eigenvalue with constant linearizing multiplier the inhomogeneity is
`k·(dρ)/ρ²`. -/
theorem logDeriv_inhom_of_monomial (Fr : RittFrame K L) {q c : K} (hq : q ≠ 0)
    (hqconst : Fr.dK q = 0) {i k : ℤ} (hcik : c = q ^ i * Fr.ρ ^ k) :
    Fr.dK c / (Fr.ρ * c) = (k : K) * Fr.dK Fr.ρ / Fr.ρ ^ 2 := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hqi : Fr.dK (q ^ i) = 0 := Fr.dK_zpow_eq_zero hq hqconst i
  have hrk : Fr.dK (Fr.ρ ^ k) = (k : K) * Fr.ρ ^ (k - 1) * Fr.dK Fr.ρ := dK_zpow Fr hρ0 k
  have hqi0 : (q : K) ^ i ≠ 0 := zpow_ne_zero _ hq
  have hrk0 : (Fr.ρ : K) ^ k ≠ 0 := zpow_ne_zero _ hρ0
  rw [hcik, Fr.dK_mul, hqi, hrk, zero_mul, zero_add]
  rw [zpow_sub₀ hρ0, zpow_one]
  field_simp

/-- **A shift-fixed base element is a derivation constant, or it yields Ritt's form.** -/
theorem psi_fixed_dichotomy (Fr : RittFrame K L) {q : K} {κ : K} (hκ0 : κ ≠ 0)
    (hfix : Fr.ψ κ = κ) :
    Fr.dK κ = 0 ∨
    ∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u := by
  by_cases hd : Fr.dK κ = 0
  · exact Or.inl hd
  refine Or.inr ⟨Fr.dK κ / κ, 0, -1, div_ne_zero hd hκ0, by rintro ⟨-, h⟩; omega, ?_⟩
  have h := Fr.invariantVectorField_of_psi_fixed hκ0 hfix
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  rw [zpow_zero, one_mul, zpow_neg_one, inv_mul_eq_div, eq_div_iff hρ0]
  linear_combination h

end GaloisForLFunctions.HTGeometry
