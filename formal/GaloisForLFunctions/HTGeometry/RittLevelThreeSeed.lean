import GaloisForLFunctions.HTGeometry.RittLevelTwoWin
import GaloisForLFunctions.HTGeometry.RittMonomialConstant
import GaloisForLFunctions.HTGeometry.RittAffineTowerDichotomy
import GaloisForLFunctions.HTGeometry.RittSchwarzian
import GaloisForLFunctions.HTGeometry.RittJetIndependence

/-!
# A seeded relation at jet order three

A relation of the shape

`σ w = (q/ρ³)·w + α·d²τ + β₁·dτ`,   `α ≠ 0`,

at jet order three is what the affine connection of the third jet produces, and what the companion
of the Schwarzian's degree-one branch produces.  One level of the descent reduces it to jet order
two in every branch.

The quadratic branch is the delicate one, and it is exactly where the descent's third coefficient
equation is needed.  Its leading coefficient is a monomial `κ_v/(dτ)`; the middle equation either
leaves a nonzero multiple of `dτ`, or pins `κ_v` outright; and in the pinned case the constant-term
equation leaves the inhomogeneity `λ₂·(2·(q/ρ²)·β₁ − λ₂·α)/α·(dτ)²`, together with a
`τ^{-1}(dτ)³` term whose coefficient vanishes only when the middle coefficient does.  Clearing the
pole in `τ` by one multiplication turns it into a polynomial inhomogeneity.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **A seeded relation at jet order three reduces to the base.** -/
theorem level_three_seed (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (htr0 : Transcendental K τ)
    (htr0' : Transcendental ↥(Fr.jetPrefixField τ 0) τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    (htr2 : Transcendental ↥(Fr.jetPrefixField τ 2) (Fr.d^[2] τ))
    {w : L} (hw0 : w ≠ 0) (hwmem : w ∈ Fr.jetPrefixField τ 3)
    {α β₁ γ : K} (hα : α ≠ 0) (hPα : P α) (hPβ : P β₁) (hPγ : P γ)
    (hc2ne : 2 * (q / Fr.ρ ^ 2) * β₁ ≠ -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3) * α)
    (hrel : Fr.σ w = algebraMap K L (q / Fr.ρ ^ 3) * w
      + (algebraMap K L α * Fr.d^[2] τ
        + (algebraMap K L β₁ * Fr.d τ
          + algebraMap K L γ * τ ^ (-1 : ℤ) * (Fr.d τ) ^ (2 : ℤ)))) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hτ0 : τ ≠ 0 := fun h => htr0 (by rw [h]; exact isAlgebraic_zero)
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
  have ha30 : q / Fr.ρ ^ 3 ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
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
  have hdτmem : Fr.d τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 1) (n := 2) (by omega)
    simpa using h
  have hτmem : τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 2) (by omega)
    simpa using h
  have hβmem : algebraMap K L β₁ * Fr.d τ
      + algebraMap K L γ * τ ^ (-1 : ℤ) * (Fr.d τ) ^ (2 : ℤ) ∈ Fr.jetPrefixField τ 2 :=
    add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hdτmem)
      (mul_mem (mul_mem (IntermediateField.algebraMap_mem _ _) (zpow_mem hτmem _))
        (zpow_mem hdτmem _))
  rcases affine_descent_dichotomy_gen Fr hqconst hshift hq htr2 hw0 hwmem ha30 hβmem hrel with
      ⟨hα0, -⟩ | hdiag | ⟨w', N, A', hw'0, hw'mem, hN, hAsh, hconn⟩ |
      ⟨v, z, y, hv0, hvmem, hzmem, hymem, -, hveq, hzeq, hyeq⟩ |
      ⟨v, hv0, hvmem, hveq, -⟩
  · exact absurd hα0 hα
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
    exact level_two_win_of_monomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hw'0 hw'mem
      ha20 hcik2 hNlam (hPreg.mul (hPreg.neg (hPreg.natCast N)) hPlam2) 0 1 hw'rel
  · -- the quadratic branch
    have hκL : ∀ x : K, x ≠ 0 → algebraMap K L x ≠ 0 := fun x hx =>
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hx
    have hscv : q / Fr.ρ ^ 3 / (q / Fr.ρ ^ 2) ^ 2 = Fr.ρ / q := by field_simp
    have hcikv : (Fr.ρ : K) / q = q ^ (-1 : ℤ) * Fr.ρ ^ (1 : ℤ) := by
      rw [zpow_neg_one, zpow_one]
      field_simp
    have hvrel2 : Fr.σ v = algebraMap K L (Fr.ρ / q) * v
        + (algebraMap K L (0 : K) * Fr.d τ
          + (algebraMap K L (0 : K) * τ + algebraMap K L (0 : K))) := by
      rw [map_zero, zero_mul, zero_mul, add_zero, add_zero, add_zero, ← hscv]
      exact hveq
    rcases level_two_classification_const Fr hqconst hshift hq htr0 htr1 hv0 hvmem
        (div_ne_zero hρ0 hq) hcikv hvrel2 with hritt | ⟨hne, -⟩ |
        ⟨κv, e₀, e₁, hκv0, hψκv, -, -, -, -, hvform, hi, hk⟩
    · exact Or.inl hritt
    · exact absurd ⟨rfl, rfl, rfl⟩ hne
    have he₁ : e₁ = -1 := by omega
    have he₀ : e₀ = 0 := by omega
    rw [he₀, he₁, zpow_zero, mul_one] at hvform
    have hvdτ : v * Fr.d τ = algebraMap K L κv := by
      rw [hvform, zpow_neg_one]
      field_simp
    have hPκvinv : P κv⁻¹ := hPreg.fixed_inv κv hκv0 hψκv
    have hPκv : P κv := hPreg.fixed κv hψκv
    have hquot : ∀ x : K, algebraMap K L x / v = algebraMap K L (x / κv) * Fr.d τ := by
      intro x
      have h1 : algebraMap K L (x / κv) * Fr.d τ
          = algebraMap K L x * Fr.d τ / algebraMap K L κv := by
        rw [map_div₀]; ring
      rw [h1, div_eq_div_iff hv0 (hκL κv hκv0)]
      linear_combination (-(algebraMap K L x)) * hvdτ
    -- the middle coefficient equation
    set μz : K := Fr.ρ * α / κv - 2 * lam2 with hμzdef
    have hzrel : Fr.σ z = algebraMap K L (q / Fr.ρ ^ 2) * z
        + algebraMap K L μz * τ ^ (0 : ℕ) * (Fr.d τ) ^ (1 : ℕ) := by
      have hcoef : q / Fr.ρ ^ 2 * α / (q / Fr.ρ ^ 3) = Fr.ρ * α := by field_simp
      rw [hzeq, hcoef, hquot, hδ2, hμzdef, pow_zero, pow_one, mul_one, map_sub, map_mul,
        map_div₀, map_ofNat]
      ring
    have hP2 : P (2 : K) := by
      have h := hPreg.natCast 2
      norm_num at h
      exact h
    have hPμz : P μz := by
      have hrw : μz = Fr.ρ * α * κv⁻¹ - 2 * lam2 := by rw [hμzdef, div_eq_mul_inv]
      rw [hrw]
      exact hPreg.sub (hPreg.mul (hPreg.mul hPreg.rho_mem hPα) hPκvinv)
        (hPreg.mul hP2 hPlam2)
    by_cases hμz : μz = 0
    · -- the leading coefficient is pinned
      have hκvrel : Fr.ρ * α = 2 * lam2 * κv := by
        rw [hμzdef, sub_eq_zero] at hμz
        field_simp at hμz
        linear_combination hμz
      set c2 : K := lam2 ^ 2 + Fr.ρ * (q / Fr.ρ ^ 2 * β₁ - α * lam2) / κv with hc2def
      have hexp : c2 * κv = lam2 ^ 2 * κv + Fr.ρ * (q / Fr.ρ ^ 2 * β₁ - α * lam2) := by
        rw [hc2def]
        field_simp
      have hc2α : c2 * α = lam2 * (2 * (q / Fr.ρ ^ 2) * β₁ - lam2 * α) := by
        refine mul_right_cancel₀ hκv0 ?_
        calc c2 * α * κv = c2 * κv * α := by ring
        _ = (lam2 ^ 2 * κv + Fr.ρ * (q / Fr.ρ ^ 2 * β₁ - α * lam2)) * α := by rw [hexp]
        _ = lam2 ^ 2 * κv * α + (Fr.ρ * α) * (q / Fr.ρ ^ 2 * β₁ - α * lam2) := by ring
        _ = lam2 ^ 2 * κv * α + (2 * lam2 * κv) * (q / Fr.ρ ^ 2 * β₁ - α * lam2) := by
              rw [hκvrel]
        _ = lam2 * (2 * (q / Fr.ρ ^ 2) * β₁ - lam2 * α) * κv := by ring
      have hc20 : c2 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hc2α
        rcases mul_eq_zero.mp hc2α.symm with h | h
        · exact hlam20 h
        · exact hc2ne (by linear_combination h)
      have hPc2 : P c2 := by
        have hrw : c2 = lam2 * lam2 + Fr.ρ * (q / Fr.ρ ^ 2 * β₁ - α * lam2) * κv⁻¹ := by
          rw [hc2def, pow_two, div_eq_mul_inv]
        rw [hrw]
        exact hPreg.add (hPreg.mul hPlam2 hPlam2)
          (hPreg.mul (hPreg.mul hPreg.rho_mem
            (hPreg.sub (hPreg.mul hPa2 hPβ) (hPreg.mul hPα hPlam2))) hPκvinv)
      have hvinv : v = algebraMap K L κv / Fr.d τ := by
        rw [eq_div_iff hdτ]; exact hvdτ
      have hqL : algebraMap K L q ≠ 0 := hκL q hq
      have hρL : algebraMap K L Fr.ρ ≠ 0 := hκL Fr.ρ hρ0
      have hκvL : algebraMap K L κv ≠ 0 := hκL κv hκv0
      have hyrel0 : Fr.σ y = algebraMap K L ((q / Fr.ρ ^ 2) ^ 2) * y
          - algebraMap K L (q / Fr.ρ ^ 2 * lam2) * Fr.d τ * z
          + algebraMap K L c2 * (Fr.d τ) ^ 2 := by
        rw [hyeq, hδ2, hvinv, hc2def]
        simp only [map_add, map_sub, map_mul, map_div₀, map_pow]
        field_simp
        ring
      have hcik4 : ((q / Fr.ρ ^ 2) ^ 2 : K) = q ^ (2 : ℤ) * Fr.ρ ^ (-(4 : ℤ)) := by
        have h1 : (q : K) ^ (2 : ℤ) = q ^ (2 : ℕ) := by norm_cast
        have h2 : (Fr.ρ : K) ^ (-(4 : ℤ)) = (Fr.ρ ^ (4 : ℕ))⁻¹ := by rw [zpow_neg]; norm_cast
        rw [h1, h2, div_pow, ← pow_mul]
        norm_num [div_eq_mul_inv]
      by_cases hz0 : z = 0
      · -- the middle coefficient vanishes: the constant-term equation carries the whole datum
        have hyrel : Fr.σ y = algebraMap K L ((q / Fr.ρ ^ 2) ^ 2) * y
            + algebraMap K L c2 * τ ^ (0 : ℕ) * (Fr.d τ) ^ (2 : ℕ) := by
          rw [hyrel0, hz0, pow_zero]
          ring
        have hy0 : y ≠ 0 := by
          intro h
          rw [h, map_zero, mul_zero, zero_add, pow_zero, mul_one] at hyrel
          rcases mul_eq_zero.mp hyrel.symm with hh | hh
          · exact hc20 ((map_eq_zero_iff _ (algebraMap K L).injective).mp hh)
          · exact (pow_ne_zero 2 hdτ) hh
        exact level_two_win_of_monomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hy0 hymem
          (pow_ne_zero 2 ha20) hcik4 hc20 hPc2 0 2 hyrel
      · -- the middle coefficient is a monomial: clearing its pole gives a polynomial datum
        have hzhom : Fr.σ z = algebraMap K L (q / Fr.ρ ^ 2) * z
            + (algebraMap K L (0 : K) * Fr.d τ
              + (algebraMap K L (0 : K) * τ + algebraMap K L (0 : K))) := by
          rw [map_zero, zero_mul, zero_mul, add_zero, add_zero, add_zero, hzrel, hμz, map_zero]
          ring
        rcases level_two_classification_const Fr hqconst hshift hq htr0 htr1 hz0 hzmem
            ha20 hcik2 hzhom with hritt | ⟨hne, -⟩ |
            ⟨κz, f₀, f₁, hκz0, hψκz, -, -, -, -, hzform, hj, hl⟩
        · exact Or.inl hritt
        · exact absurd ⟨rfl, rfl, rfl⟩ hne
        have hf₁ : f₁ = 2 := by omega
        have hf₀ : f₀ = -1 := by omega
        rw [hf₀, hf₁] at hzform
        have hzτ : z * τ = algebraMap K L κz * (Fr.d τ) ^ (2 : ℕ) := by
          rw [hzform, zpow_neg_one]
          field_simp
        set μ3 : K := -(q * (q / Fr.ρ ^ 2) * lam2 * κz) with hμ3def
        set ν2 : K := q * c2 with hν2def
        have hμ30 : μ3 ≠ 0 := by
          rw [hμ3def, neg_ne_zero]
          exact mul_ne_zero (mul_ne_zero (mul_ne_zero hq ha20) hlam20) hκz0
        have hPμ3 : P μ3 := by
          rw [hμ3def]
          exact hPreg.neg (hPreg.mul (hPreg.mul (hPreg.mul hPreg.q_mem hPa2) hPlam2)
            (hPreg.fixed κz hψκz))
        have hPν2 : P ν2 := by rw [hν2def]; exact hPreg.mul hPreg.q_mem hPc2
        have hτmem : τ ∈ Fr.jetPrefixField τ 2 := by
          have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 2) (by omega)
          simpa using h
        have hYmem : τ * y ∈ Fr.jetPrefixField τ 2 := mul_mem hτmem hymem
        have hYrel : Fr.σ (τ * y) = algebraMap K L (q * (q / Fr.ρ ^ 2) ^ 2) * (τ * y)
            + (algebraMap K L μ3 * τ ^ (0 : ℕ) * (Fr.d τ) ^ (3 : ℕ)
              + algebraMap K L ν2 * τ ^ (1 : ℕ) * (Fr.d τ) ^ (2 : ℕ)) := by
          have hστ : Fr.σ τ = algebraMap K L q * τ := hshift
          rw [map_mul, hστ, hyrel0, hμ3def, hν2def]
          have hzv : z = algebraMap K L κz * (Fr.d τ) ^ (2 : ℕ) / τ := by
            rw [eq_div_iff hτ0]; exact hzτ
          rw [hzv]
          simp only [map_mul, map_neg, map_pow, map_div₀, pow_zero, pow_one, mul_one]
          field_simp
          ring
        have hY0 : τ * y ≠ 0 := by
          intro h
          rw [h, map_zero, mul_zero, zero_add, pow_zero, pow_one, mul_one] at hYrel
          have hfac : (Fr.d τ) ^ (2 : ℕ)
              * (algebraMap K L μ3 * Fr.d τ + algebraMap K L ν2 * τ) = 0 := by
            linear_combination -hYrel
          have hbr : algebraMap K L μ3 * Fr.d τ + algebraMap K L ν2 * τ = 0 :=
            (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hdτ)
          have hsum : ∑ j ∈ Finset.range 2,
              algebraMap K L ((fun j : ℕ => if j = 0 then ν2 else μ3) j) * Fr.d^[j] τ = 0 := by
            rw [Finset.sum_range_succ, Finset.sum_range_one]
            simp only [if_true, if_neg (by omega : ¬ (1 : ℕ) = 0),
              Function.iterate_zero_apply, Function.iterate_one]
            linear_combination hbr
          have hc := jet_coeffs_eq_zero_of_sum_eq_zero Fr 2 hjetind
            (fun j : ℕ => if j = 0 then ν2 else μ3) hsum 1 (by omega)
          simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)] at hc
          exact hμ30 hc
        have hcik34 : q * (q / Fr.ρ ^ 2) ^ 2 = q ^ (3 : ℤ) * Fr.ρ ^ (-(4 : ℤ)) := by
          have h3 : (q : K) ^ (3 : ℤ) = q * q ^ (2 : ℤ) := by
            rw [show (3 : ℤ) = 1 + 2 by norm_num, zpow_add₀ hq, zpow_one]
          rw [hcik4, h3]
          ring
        exact level_two_win_of_two_monomials Fr hPreg hqconst hshift hq htr0 htr1 hY0 hYmem
          (mul_ne_zero hq (pow_ne_zero 2 ha20)) hcik34 hμ30 hPμ3 hPν2
          (by omega : (2 : ℕ) ≠ 3) hYrel
    · -- the middle equation leaves a nonzero multiple of the first jet
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, map_zero, mul_zero, zero_add, pow_zero, pow_one, mul_one] at hzrel
        rcases mul_eq_zero.mp hzrel.symm with h | h
        · exact hμz ((map_eq_zero_iff _ (algebraMap K L).injective).mp h)
        · exact hdτ h
      exact level_two_win_of_monomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hz0 hzmem
        ha20 hcik2 hμz hPμz 0 1 hzrel
  · -- the degree-one branch: the inhomogeneity is a nonzero base constant
    have hsc : q / Fr.ρ ^ 3 / (q / Fr.ρ ^ 2) = Fr.ρ⁻¹ := by field_simp
    have hcikv : (Fr.ρ : K)⁻¹ = q ^ (0 : ℤ) * Fr.ρ ^ (-(1 : ℤ)) := by
      rw [zpow_zero, one_mul, zpow_neg_one]
    have hμ0 : α / (q / Fr.ρ ^ 2) ≠ 0 := div_ne_zero hα ha20
    have hPμ : P (α / (q / Fr.ρ ^ 2)) := by
      have hrw : α / (q / Fr.ρ ^ 2) = α * q ^ (-1 : ℤ) * Fr.ρ ^ (2 : ℤ) := by
        rw [zpow_neg_one]
        field_simp
      rw [hrw]
      exact hPreg.mul_monomial hPα _ _
    have hvrel : Fr.σ v = algebraMap K L (Fr.ρ⁻¹) * v
        + algebraMap K L (α / (q / Fr.ρ ^ 2)) * τ ^ (0 : ℕ) * (Fr.d τ) ^ (0 : ℕ) := by
      rw [hveq, hsc]
      ring
    exact level_two_win_of_monomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hv0 hvmem
      (inv_ne_zero hρ0) hcikv hμ0 hPμ 0 0 hvrel

end GaloisForLFunctions.HTGeometry
