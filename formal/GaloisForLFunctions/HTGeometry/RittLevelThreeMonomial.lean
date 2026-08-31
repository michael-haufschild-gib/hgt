import GaloisForLFunctions.HTGeometry.RittLevelThreeSeed

/-!
# A homogeneous-looking relation at jet order three with a monomial inhomogeneity

The companion produced by the degree-one branch of a descent is a relation

`σ V = c·V + g·τ^{p₀}·(dτ)^{p₁}`

at jet order three with no linear term in the top jet.  Four of the five branches of the level
dichotomy at jet order two close it outright; the fifth pins the whole configuration.

There the leading coefficient is a monomial `κ·τ^{e₀}(dτ)^{e₁}` with `κ` shift-fixed and a
derivation constant, and the companion's inhomogeneity is
`((q/ρ²)·g/(c·κ))·τ^{p₀−e₀}(dτ)^{p₁−e₁} − λ₂·dτ`.  Unless the two monomials coincide *and* their
coefficients cancel, the relation closes — if the companion vanishes the two monomials give a
monomial relation between the linearizer and its first jet, which is a nontrivial base relation, and
otherwise the two-monomial form applies.

What is left is one arithmetic configuration: the exponent pair is forced to be
`i₀ = p₀ + p₁`, `k₀ = −p₁ − 1`, and the coefficients satisfy `(q/ρ²)·g = c·κ·λ₂` for a shift-fixed
derivation constant `κ`.  That is a closed condition on the data of the relation, not an existence
statement about a solution.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **A level-three relation with a monomial inhomogeneity and no top linear term.** -/
theorem level_three_monomial (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (htr0 : Transcendental K τ)
    (htr0' : Transcendental ↥(Fr.jetPrefixField τ 0) τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    (htr2 : Transcendental ↥(Fr.jetPrefixField τ 2) (Fr.d^[2] τ))
    {V : L} (hV0 : V ≠ 0) (hVmem : V ∈ Fr.jetPrefixField τ 3)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {g : K} (hg0 : g ≠ 0) (hPg : P g) {p₀ p₁ : ℤ}
    (hrel : Fr.σ V = algebraMap K L c * V
      + algebraMap K L g * τ ^ p₀ * (Fr.d τ) ^ p₁) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) ∨
    (∃ κ : K, κ ≠ 0 ∧ Fr.ψ κ = κ ∧ Fr.dK κ = 0 ∧ i₀ = p₀ + p₁ ∧ k₀ = -p₁ - 1 ∧
      q / Fr.ρ ^ 2 * g = c * κ * -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3)) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hτ0 : τ ≠ 0 := fun h => htr0 (by rw [h]; exact isAlgebraic_zero)
  have hκL : ∀ x : K, x ≠ 0 → algebraMap K L x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hx
  set lam2 : K := -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3) with hlam2def
  have hlam20 : lam2 ≠ 0 := by
    rw [hlam2def, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero hq hdρ) (pow_ne_zero _ hρ0)
  have hPlam2 : P lam2 := by
    have hz3 : (Fr.ρ : K) ^ (-3 : ℤ) = (Fr.ρ ^ (3 : ℕ))⁻¹ := by rw [zpow_neg]; norm_cast
    have hrw : lam2 = -(q * Fr.dK Fr.ρ * Fr.ρ ^ (-3 : ℤ)) := by
      rw [hlam2def, hz3, div_eq_mul_inv]
    rw [hrw]
    exact hPreg.neg (hPreg.mul (hPreg.mul hPreg.q_mem (hPreg.deriv hPreg.rho_mem))
      (hPreg.rzpow _))
  have ha20 : q / Fr.ρ ^ 2 ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
  have hPa2 : P (q / Fr.ρ ^ 2) := by
    have hz2 : (Fr.ρ : K) ^ (-2 : ℤ) = (Fr.ρ ^ (2 : ℕ))⁻¹ := by rw [zpow_neg]; norm_cast
    have hrw : q / Fr.ρ ^ 2 = q * Fr.ρ ^ (-2 : ℤ) := by rw [hz2, div_eq_mul_inv]
    rw [hrw]
    exact hPreg.mul hPreg.q_mem (hPreg.rzpow _)
  have hcik2 : q / Fr.ρ ^ 2 = q ^ (1 : ℤ) * Fr.ρ ^ (-(2 : ℤ)) := by
    rw [zpow_one, zpow_neg, div_eq_mul_inv]; norm_cast
  have hdef2 : Fr.σ (Fr.d^[2] τ) = algebraMap K L (q / Fr.ρ ^ 2) * Fr.d^[2] τ
      + algebraMap K L lam2 * Fr.d τ := sigma_jet_two Fr hqconst hshift
  have hδ2 : Fr.σ (Fr.d^[2] τ) - algebraMap K L (q / Fr.ρ ^ 2) * Fr.d^[2] τ
      = algebraMap K L lam2 * Fr.d τ := by rw [hdef2]; ring
  clear_value lam2
  have hjetind : ∀ j, j < 2 → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ) := by
    intro j hj
    interval_cases j
    · exact htr0'
    · exact htr1
  have hτmem : τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 2) (by omega)
    simpa using h
  have hdτmem : Fr.d τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 1) (n := 2) (by omega)
    simpa using h
  have hβmem : algebraMap K L g * τ ^ p₀ * (Fr.d τ) ^ p₁ ∈ Fr.jetPrefixField τ 2 :=
    mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) (zpow_mem hτmem _))
      (zpow_mem hdτmem _)
  have hrel' : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L (0 : K) * Fr.d^[2] τ
        + algebraMap K L g * τ ^ p₀ * (Fr.d τ) ^ p₁) := by
    rw [map_zero, zero_mul, zero_add]
    exact hrel
  rcases affine_descent_dichotomy_gen Fr hqconst hshift hq htr2 hV0 hVmem hc hβmem hrel' with
      ⟨-, hmem2⟩ | hdiag | ⟨w', N, A', hw'0, hw'mem, hN, hAsh, hconn⟩ |
      ⟨-, -, -, -, -, -, -, hαne, -, -, -⟩ | ⟨v, hv0, hvmem, hveq, hlin⟩
  · -- the relation is already at jet order two
    rcases level_two_win_of_zmonomial_inhom Fr hPreg hqconst hshift hq hτ0 hdτ htr0 htr1
        hV0 hmem2 hc hcik hg0 hPg p₀ p₁ hrel with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exfalso
    rw [hdef2] at hdiag
    have hz : algebraMap K L lam2 * Fr.d τ = 0 := by linear_combination hdiag
    rcases mul_eq_zero.mp hz with hh | hh
    · exact hlam20 ((map_eq_zero_iff _ (algebraMap K L).injective).mp hh)
    · exact hdτ hh
  · -- the affine connection of the second jet
    have hcoef : A' 0 = 0 ∧ A' 1 = lam2 := by
      have hbase : algebraMap K L (A' 0) * τ + algebraMap K L (A' 1) * Fr.d τ
          = algebraMap K L lam2 * Fr.d τ := by
        have h2 : ∑ j ∈ Finset.range 2, algebraMap K L (A' j) * Fr.d^[j] τ
            = algebraMap K L lam2 * Fr.d τ := by
          rw [hdef2] at hAsh
          linear_combination -hAsh
        rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
        simpa using h2
      have hzero : ∑ j ∈ Finset.range 2,
          algebraMap K L ((fun j : ℕ => if j = 0 then A' 0 else A' 1 - lam2) j) * Fr.d^[j] τ
          = 0 := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        simp only [if_neg (by omega : ¬ (1 : ℕ) = 0), map_sub, if_true,
          Function.iterate_zero_apply, Function.iterate_one, sub_mul]
        linear_combination hbase
      have hc0 := jet_coeffs_eq_zero_of_sum_eq_zero Fr 2 hjetind
        (fun j : ℕ => if j = 0 then A' 0 else A' 1 - lam2) hzero 0 (by omega)
      have hc1 := jet_coeffs_eq_zero_of_sum_eq_zero Fr 2 hjetind
        (fun j : ℕ => if j = 0 then A' 0 else A' 1 - lam2) hzero 1 (by omega)
      simp only [if_true] at hc0
      simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)] at hc1
      exact ⟨hc0, by linear_combination hc1⟩
    have hw'rel : Fr.σ w' = algebraMap K L (q / Fr.ρ ^ 2) * w'
        + algebraMap K L (-(N : K) * lam2) * τ ^ (0 : ℕ) * (Fr.d τ) ^ (1 : ℕ) := by
      rw [hconn, Finset.sum_range_succ, Finset.sum_range_one, hcoef.1, hcoef.2]
      simp only [Function.iterate_zero_apply, Function.iterate_one, mul_zero, map_zero,
        zero_mul, zero_add, pow_zero, pow_one, mul_one]
    have hNlam : (-(N : K) * lam2) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hlam20
    rcases level_two_win_of_monomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hw'0 hw'mem
        ha20 hcik2 hNlam (hPreg.mul (hPreg.neg (hPreg.natCast N)) hPlam2) 0 1 hw'rel with
        h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact absurd rfl hαne
  · -- the degree-one branch
    obtain ⟨y, hymem, hyeq⟩ := hlin rfl
    have hcikv : c / (q / Fr.ρ ^ 2) = q ^ (i₀ - 1) * Fr.ρ ^ (k₀ + 2) := by
      rw [hcik, zpow_sub₀ hq, zpow_add₀ hρ0, zpow_one]
      have h2 : (Fr.ρ : K) ^ (2 : ℤ) = Fr.ρ ^ (2 : ℕ) := by norm_cast
      rw [h2]
      field_simp
    have hcv0 : c / (q / Fr.ρ ^ 2) ≠ 0 := div_ne_zero hc ha20
    have hvrel : Fr.σ v = algebraMap K L (c / (q / Fr.ρ ^ 2)) * v
        + (algebraMap K L (0 : K) * Fr.d τ
          + (algebraMap K L (0 : K) * τ + algebraMap K L (0 : K))) := by
      rw [map_zero, zero_mul, zero_mul, add_zero, add_zero, add_zero, hveq, zero_div, map_zero,
        add_zero]
    rcases level_two_classification_const Fr hqconst hshift hq htr0 htr1 hv0 hvmem hcv0 hcikv
        hvrel with hritt | ⟨hne, -⟩ | ⟨κ, e₀, e₁, hκ0, hψκ, hdκ, -, -, -, hvform, hi, hk⟩
    · exact Or.inl hritt
    · exact absurd ⟨rfl, rfl, rfl⟩ hne
    -- the companion's inhomogeneity
    set μ : K := q / Fr.ρ ^ 2 * g / (c * κ) with hμdef
    have hμ0 : μ ≠ 0 := div_ne_zero (mul_ne_zero ha20 hg0) (mul_ne_zero hc hκ0)
    have hPμ : P μ := by
      have hrw : μ = q / Fr.ρ ^ 2 * g * (c⁻¹ * κ⁻¹) := by rw [hμdef]; field_simp
      rw [hrw]
      refine hPreg.mul (hPreg.mul hPa2 hPg) (hPreg.mul ?_ (hPreg.fixed_inv κ hκ0 hψκ))
      have hcinv : c⁻¹ = q ^ (-i₀) * Fr.ρ ^ (-k₀) := by
        rw [hcik, mul_inv, ← zpow_neg, ← zpow_neg]
      rw [hcinv]
      exact hPreg.mul (hPreg.qzpow _) (hPreg.rzpow _)
    have hvL : v = algebraMap K L κ * τ ^ e₀ * (Fr.d τ) ^ e₁ := hvform
    have hquot : algebraMap K L (q / Fr.ρ ^ 2)
        * (algebraMap K L g * τ ^ p₀ * (Fr.d τ) ^ p₁) / (algebraMap K L c * v)
        = algebraMap K L μ * τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁) := by
      have h1 : algebraMap K L κ ≠ 0 := hκL κ hκ0
      have h2 : algebraMap K L c ≠ 0 := hκL c hc
      have h3 : (τ : L) ^ e₀ ≠ 0 := zpow_ne_zero _ hτ0
      have h4 : (Fr.d τ : L) ^ e₁ ≠ 0 := zpow_ne_zero _ hdτ
      rw [hvL, hμdef, zpow_sub₀ hτ0, zpow_sub₀ hdτ]
      simp only [map_div₀, map_mul, map_pow]
      field_simp
    have hyrel : Fr.σ y = algebraMap K L (q / Fr.ρ ^ 2) * y
        + (algebraMap K L μ * τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁)
          + algebraMap K L (-lam2) * τ ^ (0 : ℤ) * (Fr.d τ) ^ (1 : ℤ)) := by
      rw [hyeq, hquot, hδ2, map_neg, zpow_zero, zpow_one]
      ring
    by_cases hcase : p₀ - e₀ = 0 ∧ p₁ - e₁ = 1
    · -- the two monomials coincide
      obtain ⟨hA, hB⟩ := hcase
      by_cases hμl : μ = lam2
      · refine Or.inr (Or.inr ⟨κ, hκ0, hψκ, hdκ, by omega, by omega, ?_⟩)
        rw [← hμl, hμdef]
        field_simp
      · have hyrel2 : Fr.σ y = algebraMap K L (q / Fr.ρ ^ 2) * y
            + algebraMap K L (μ - lam2) * τ ^ (0 : ℤ) * (Fr.d τ) ^ (1 : ℤ) := by
          rw [hyrel, hA, hB, map_sub, map_neg, zpow_zero, zpow_one]
          ring
        have hml0 : μ - lam2 ≠ 0 := sub_ne_zero.mpr hμl
        have hy0 : y ≠ 0 := by
          intro h
          rw [h, map_zero, mul_zero, zero_add, zpow_zero, mul_one, zpow_one] at hyrel2
          rcases mul_eq_zero.mp hyrel2.symm with hh | hh
          · exact hml0 ((map_eq_zero_iff _ (algebraMap K L).injective).mp hh)
          · exact hdτ hh
        rcases level_two_win_of_zmonomial_inhom Fr hPreg hqconst hshift hq hτ0 hdτ htr0 htr1
            hy0 hymem ha20 hcik2 hml0 (hPreg.sub hPμ hPlam2) 0 1 hyrel2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · -- the two monomials are distinct
      by_cases hy0 : y = 0
      · -- the two monomials cancel, giving a monomial relation over the base
        rw [hy0, map_zero, mul_zero, zero_add] at hyrel
        rw [map_neg, zpow_zero, zpow_one, mul_one] at hyrel
        have hB : (Fr.d τ : L) ^ (p₁ - e₁ - 1) * Fr.d τ = (Fr.d τ) ^ (p₁ - e₁) := by
          rw [zpow_sub₀ hdτ, zpow_one]
          field_simp
        have hkey : algebraMap K L μ * (τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁ - 1)) * Fr.d τ
            = algebraMap K L lam2 * Fr.d τ := by
          calc algebraMap K L μ * (τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁ - 1)) * Fr.d τ
              = algebraMap K L μ * τ ^ (p₀ - e₀)
                * ((Fr.d τ) ^ (p₁ - e₁ - 1) * Fr.d τ) := by ring
            _ = algebraMap K L μ * τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁) := by rw [hB]
            _ = algebraMap K L lam2 * Fr.d τ := by linear_combination -hyrel
        have hkey2 : algebraMap K L μ * (τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁ - 1))
            = algebraMap K L lam2 := mul_right_cancel₀ hdτ hkey
        have hmono : τ ^ (p₀ - e₀) * (Fr.d τ) ^ (p₁ - e₁ - 1) = algebraMap K L (lam2 / μ) := by
          rw [map_div₀, eq_div_iff (hκL μ hμ0)]
          linear_combination hkey2
        exact Or.inl (base_relation_of_monomial Fr hqconst hshift hq
          (by rintro ⟨h1, h2⟩; exact hcase ⟨h1, by omega⟩)
          (div_ne_zero hlam20 hμ0) hmono)
      · rcases level_two_win_of_zbinomial_inhom Fr hPreg hqconst hshift hq hτ0 hdτ htr0 htr1
            hy0 hymem ha20 hcik2 hμ0 hPμ (hPreg.neg hPlam2)
            (by rintro ⟨h1, h2⟩; exact hcase ⟨by omega, by omega⟩) hyrel with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

end GaloisForLFunctions.HTGeometry
