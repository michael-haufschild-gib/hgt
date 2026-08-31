import GaloisForLFunctions.HTGeometry.RittRegularLevelTwo

/-!
# Level-two relations with monomial inhomogeneities

The general level-two statement takes its inhomogeneity as a polynomial in the linearizer with
coefficients read off degree by degree in the first jet.  The descent produces it in a much more
restricted shape — one or two base monomials `μ·τ^a·(dτ)^b` — so it is worth packaging the two
cases that occur, with the regularity of the coefficients passed straight through.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

omit [Algebra K L] in
private theorem coeff_C_mul_X_pow_mem {P : K → Prop} {μ : K} (hPμ : P μ) (hP0 : P 0)
    (a k : ℕ) : P ((C μ * X ^ a).coeff k) := by
  classical
  rw [coeff_C_mul, coeff_X_pow]
  split
  · rwa [mul_one]
  · rwa [mul_zero]


/-- **A single base monomial as inhomogeneity at jet order two.** -/
theorem level_two_win_of_monomial_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {μ : K} (hμ : μ ≠ 0) (hPμ : P μ) (a b : ℕ)
    (hrel : Fr.σ V = algebraMap K L c * V
      + algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  set G : ℕ → K[X] := fun j => if j = b then C μ * X ^ a else 0 with hG
  have hGb : G b = C μ * X ^ a := by rw [hG]; simp
  have hGne : G b ≠ 0 := by
    rw [hGb]
    exact mul_ne_zero (fun hz => hμ (C_eq_zero.mp hz)) (pow_ne_zero _ X_ne_zero)
  have hsum : ∑ j ∈ Finset.range (b + 1), aeval τ (G j) * (Fr.d τ) ^ j
      = algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b := by
    rw [Finset.sum_eq_single b]
    · rw [hGb, map_mul, aeval_C, map_pow, aeval_X]
    · intro j _ hj
      rw [hG]
      simp only [if_neg hj, map_zero, zero_mul]
    · intro hb
      exact absurd (Finset.self_mem_range_succ b) hb
  refine level_two_regular_inhom Fr hPreg hqconst hshift hq htr0 htr1 hV0 hV hc hcik
    (G := G) (n := b + 1) ⟨b, by omega, hGne⟩ ?_ (by rw [hrel, hsum])
  intro j k
  rw [hG]
  by_cases hj : j = b
  · simp only [hj, if_true]
    exact coeff_C_mul_X_pow_mem hPμ hPreg.zero a k
  · simp only [if_neg hj, coeff_zero]
    exact hPreg.zero

/-- **Two base monomials of distinct jet degree as inhomogeneity at jet order two.** -/
theorem level_two_win_of_two_monomials (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {μ ν : K} (hμ : μ ≠ 0) (hPμ : P μ) (hPν : P ν) {a b a' b' : ℕ} (hbb : b' ≠ b)
    (hrel : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b
        + algebraMap K L ν * τ ^ a' * (Fr.d τ) ^ b')) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  set G : ℕ → K[X] :=
    fun j => if j = b then C μ * X ^ a else if j = b' then C ν * X ^ a' else 0 with hG
  have hGb : G b = C μ * X ^ a := by rw [hG]; simp
  have hGb' : G b' = C ν * X ^ a' := by rw [hG]; simp [hbb]
  have hGne : G b ≠ 0 := by
    rw [hGb]
    exact mul_ne_zero (fun hz => hμ (C_eq_zero.mp hz)) (pow_ne_zero _ X_ne_zero)
  set N : ℕ := max b b' + 1 with hN
  have hsum : ∑ j ∈ Finset.range N, aeval τ (G j) * (Fr.d τ) ^ j
      = algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b
        + algebraMap K L ν * τ ^ a' * (Fr.d τ) ^ b' := by
    have hsub : ({b, b'} : Finset ℕ) ⊆ Finset.range N := by
      intro j hj
      rw [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [hN, Finset.mem_range]
      rcases hj with rfl | rfl <;> omega
    have hzero : ∀ j ∈ Finset.range N, j ∉ ({b, b'} : Finset ℕ) →
        aeval τ (G j) * (Fr.d τ) ^ j = 0 := by
      intro j _ hj
      rw [Finset.mem_insert, Finset.mem_singleton] at hj
      push Not at hj
      rw [hG]
      simp only [if_neg hj.1, if_neg hj.2, map_zero, zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (Ne.symm hbb), hGb, hGb',
      map_mul, aeval_C, map_pow, aeval_X, map_mul, aeval_C, map_pow, aeval_X]
  refine level_two_regular_inhom Fr hPreg hqconst hshift hq htr0 htr1 hV0 hV hc hcik
    (G := G) (n := N) ⟨b, by rw [hN]; omega, hGne⟩ ?_ (by rw [hrel, hsum])
  intro j k
  rw [hG]
  by_cases hj : j = b
  · simp only [hj, if_true]
    exact coeff_C_mul_X_pow_mem hPμ hPreg.zero a k
  · simp only [if_neg hj]
    by_cases hj' : j = b'
    · simp only [hj', if_true]
      exact coeff_C_mul_X_pow_mem hPν hPreg.zero a' k
    · simp only [if_neg hj', coeff_zero]
      exact hPreg.zero

/-- **Two base monomials as inhomogeneity at jet order two.**  Only the two exponent pairs need to
be distinct, and only the first coefficient needs to be nonzero. -/
theorem level_two_win_of_binomial_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {μ ν : K} (hμ : μ ≠ 0) (hPμ : P μ) (hPν : P ν) {a b a' b' : ℕ}
    (hne : ¬(a = a' ∧ b = b'))
    (hrel : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b
        + algebraMap K L ν * τ ^ a' * (Fr.d τ) ^ b')) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  set G : ℕ → K[X] :=
    fun j => (if j = b then C μ * X ^ a else 0) + (if j = b' then C ν * X ^ a' else 0) with hG
  have hGba : (G b).coeff a = μ := by
    have h2 : ((if (b : ℕ) = b' then C ν * X ^ a' else 0) : K[X]).coeff a = 0 := by
      by_cases hbb : b = b'
      · rw [if_pos hbb, coeff_C_mul, coeff_X_pow, if_neg (by tauto : ¬ a = a'), mul_zero]
      · rw [if_neg hbb, coeff_zero]
    rw [hG]
    simp only [coeff_add, h2, add_zero, if_true, coeff_C_mul, coeff_X_pow, mul_one]
  have hGne : G b ≠ 0 := fun h0 => hμ (by rw [← hGba, h0, coeff_zero])
  set N : ℕ := max b b' + 1 with hN
  have hsum : ∑ j ∈ Finset.range N, aeval τ (G j) * (Fr.d τ) ^ j
      = algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b
        + algebraMap K L ν * τ ^ a' * (Fr.d τ) ^ b' := by
    have hsplit : ∀ j : ℕ, aeval τ (G j) * (Fr.d τ) ^ j
        = aeval τ (if j = b then C μ * X ^ a else 0) * (Fr.d τ) ^ j
          + aeval τ (if j = b' then C ν * X ^ a' else 0) * (Fr.d τ) ^ j := by
      intro j
      rw [hG, map_add]
      ring
    simp only [hsplit]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single b]
      · rw [if_pos rfl, map_mul, aeval_C, map_pow, aeval_X]
      · intro j _ hj
        rw [if_neg hj, map_zero, zero_mul]
      · intro hb
        exact absurd (by rw [hN, Finset.mem_range]; omega) hb
    · rw [Finset.sum_eq_single b']
      · rw [if_pos rfl, map_mul, aeval_C, map_pow, aeval_X]
      · intro j _ hj
        rw [if_neg hj, map_zero, zero_mul]
      · intro hb
        exact absurd (by rw [hN, Finset.mem_range]; omega) hb
  refine level_two_regular_inhom Fr hPreg hqconst hshift hq htr0 htr1 hV0 hV hc hcik
    (G := G) (n := N) ⟨b, by rw [hN]; omega, hGne⟩ ?_ (by rw [hrel, hsum])
  intro j k
  rw [hG, coeff_add]
  refine hPreg.add ?_ ?_
  · split_ifs
    · exact coeff_C_mul_X_pow_mem hPμ hPreg.zero a k
    · rw [coeff_zero]
      exact hPreg.zero
  · split_ifs
    · exact coeff_C_mul_X_pow_mem hPν hPreg.zero a' k
    · rw [coeff_zero]
      exact hPreg.zero

/-- **Two base monomials with integer exponents.**  Multiplying by a power of the linearizer and of
its first jet clears the poles without leaving the second prefix field, and only changes the
multiplier by a monomial. -/
theorem level_two_win_of_zbinomial_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hτ0 : τ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {μ ν : K} (hμ : μ ≠ 0) (hPμ : P μ) (hPν : P ν) {a b a' b' : ℤ}
    (hne : ¬(a = a' ∧ b = b'))
    (hrel : Fr.σ V = algebraMap K L c * V
      + (algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b
        + algebraMap K L ν * τ ^ a' * (Fr.d τ) ^ b')) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set m : ℕ := (max (-a) (-a')).toNat with hmdef
  set n : ℕ := (max (-b) (-b')).toNat with hndef
  have hma : 0 ≤ a + (m : ℤ) := by rw [hmdef]; omega
  have hma' : 0 ≤ a' + (m : ℤ) := by rw [hmdef]; omega
  have hnb : 0 ≤ b + (n : ℤ) := by rw [hndef]; omega
  have hnb' : 0 ≤ b' + (n : ℤ) := by rw [hndef]; omega
  set A : ℕ := (a + (m : ℤ)).toNat with hAdef
  set A' : ℕ := (a' + (m : ℤ)).toNat with hA'def
  set B : ℕ := (b + (n : ℤ)).toNat with hBdef
  set B' : ℕ := (b' + (n : ℤ)).toNat with hB'def
  have hAeq : ((A : ℕ) : ℤ) = a + (m : ℤ) := by rw [hAdef]; omega
  have hA'eq : ((A' : ℕ) : ℤ) = a' + (m : ℤ) := by rw [hA'def]; omega
  have hBeq : ((B : ℕ) : ℤ) = b + (n : ℤ) := by rw [hBdef]; omega
  have hB'eq : ((B' : ℕ) : ℤ) = b' + (n : ℤ) := by rw [hB'def]; omega
  have hshiftPow : ∀ (x : L) (hx : x ≠ 0) (e : ℤ) (E N : ℕ), ((E : ℤ) = e + (N : ℤ)) →
      x ^ (N : ℕ) * x ^ e = x ^ (E : ℕ) := by
    intro x hx e E N hE
    rw [← zpow_natCast x N, ← zpow_add₀ hx, ← zpow_natCast x E, hE, add_comm]
  have hτmem : τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 2) (by omega)
    simpa using h
  have hdτmem : Fr.d τ ∈ Fr.jetPrefixField τ 2 := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 1) (n := 2) (by omega)
    simpa using h
  set s : K := q ^ m * (q / Fr.ρ) ^ n with hsdef
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ (div_ne_zero hq hρ0))
  have hPs : P s := by
    have hrw : s = q ^ (m : ℤ) * (q ^ (n : ℤ) * Fr.ρ ^ (-(n : ℤ))) := by
      rw [hsdef, div_pow, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    rw [hrw]
    exact hPreg.mul (hPreg.qzpow _) (hPreg.mul (hPreg.qzpow _) (hPreg.rzpow _))
  have hcikS : s * c = q ^ (i₀ + (m : ℤ) + (n : ℤ)) * Fr.ρ ^ (k₀ - (n : ℤ)) := by
    rw [hsdef, hcik, div_pow, zpow_add₀ hq, zpow_add₀ hq, zpow_sub₀ hρ0, zpow_natCast,
      zpow_natCast, zpow_natCast]
    field_simp
  set V' : L := τ ^ (m : ℕ) * (Fr.d τ) ^ (n : ℕ) * V with hV'def
  have hV'0 : V' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hτ0) (pow_ne_zero _ hdτ)) hV0
  have hV'mem : V' ∈ Fr.jetPrefixField τ 2 :=
    mul_mem (mul_mem (pow_mem hτmem _) (pow_mem hdτmem _)) hV
  have hσV' : Fr.σ V' = algebraMap K L (s * c) * V'
      + (algebraMap K L (s * μ) * τ ^ (A : ℕ) * (Fr.d τ) ^ (B : ℕ)
        + algebraMap K L (s * ν) * τ ^ (A' : ℕ) * (Fr.d τ) ^ (B' : ℕ)) := by
    have hστ : Fr.σ (τ ^ (m : ℕ)) = (algebraMap K L q) ^ m * τ ^ (m : ℕ) := by
      rw [map_pow, hshift, mul_pow]
    have hσd : Fr.σ ((Fr.d τ) ^ (n : ℕ))
        = (algebraMap K L (q / Fr.ρ)) ^ n * (Fr.d τ) ^ (n : ℕ) := by
      rw [map_pow, Fr.sigma_d_eq_of_shift hqconst hshift, mul_pow]
    have e1 : τ ^ (m : ℕ) * τ ^ a = τ ^ (A : ℕ) := hshiftPow τ hτ0 a A m hAeq
    have e2 : (Fr.d τ) ^ (n : ℕ) * (Fr.d τ) ^ b = (Fr.d τ) ^ (B : ℕ) :=
      hshiftPow (Fr.d τ) hdτ b B n hBeq
    have e3 : τ ^ (m : ℕ) * τ ^ a' = τ ^ (A' : ℕ) := hshiftPow τ hτ0 a' A' m hA'eq
    have e4 : (Fr.d τ) ^ (n : ℕ) * (Fr.d τ) ^ b' = (Fr.d τ) ^ (B' : ℕ) :=
      hshiftPow (Fr.d τ) hdτ b' B' n hB'eq
    rw [hV'def, map_mul, map_mul, hστ, hσd, hrel, ← e1, ← e2, ← e3, ← e4]
    simp only [hsdef, map_mul, map_pow]
    ring
  refine level_two_win_of_binomial_inhom Fr hPreg hqconst hshift hq htr0 htr1 hV'0 hV'mem
    (mul_ne_zero hs0 hc) hcikS (mul_ne_zero hs0 hμ) (hPreg.mul hPs hPμ) (hPreg.mul hPs hPν)
    (a := A) (b := B) (a' := A') (b' := B') ?_ hσV'
  rintro ⟨hAA, hBB⟩
  exact hne ⟨by omega, by omega⟩

/-- **A monomial relation between the linearizer and its first jet is a nontrivial base
relation.**  Applying the shift to `τ^{e₀}(dτ)^{e₁} = u` reads off `ψ u = q^{e₀+e₁}ρ^{−e₁}·u`. -/
theorem base_relation_of_monomial (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    {e₀ e₁ : ℤ} (hne : ¬(e₀ = 0 ∧ e₁ = 0)) {u : K} (hu0 : u ≠ 0)
    (heq : τ ^ e₀ * (Fr.d τ) ^ e₁ = algebraMap K L u) :
    ∃ (w : K) (I J : ℤ), w ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ w = q ^ I * Fr.ρ ^ J * w := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  refine ⟨u, e₀ + e₁, -e₁, hu0, by rintro ⟨h1, h2⟩; exact hne ⟨by omega, by omega⟩, ?_⟩
  have hσ := congrArg Fr.σ heq
  rw [map_mul, map_zpow₀, map_zpow₀, hshift, Fr.sigma_d_eq_of_shift hqconst hshift, Fr.comp,
    mul_zpow, mul_zpow] at hσ
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hcoef : algebraMap K L (q ^ (e₀ + e₁) * Fr.ρ ^ (-e₁))
      = (algebraMap K L q) ^ e₀ * (algebraMap K L (q / Fr.ρ)) ^ e₁ := by
    rw [map_mul, map_zpow₀, map_zpow₀, map_div₀, div_zpow, zpow_add₀ hqL, zpow_neg]
    field_simp
  refine (algebraMap K L).injective ?_
  rw [map_mul, hcoef, ← heq]
  linear_combination -hσ

/-- **A single base monomial with integer exponents.** -/
theorem level_two_win_of_zmonomial_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hτ0 : τ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {μ : K} (hμ : μ ≠ 0) (hPμ : P μ) (a b : ℤ)
    (hrel : Fr.σ V = algebraMap K L c * V
      + algebraMap K L μ * τ ^ a * (Fr.d τ) ^ b) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  refine level_two_win_of_zbinomial_inhom Fr hPreg hqconst hshift hq hτ0 hdτ htr0 htr1 hV0 hV
    hc hcik hμ hPμ hPreg.zero (a := a) (b := b) (a' := a) (b' := b + 1)
    (by rintro ⟨-, h⟩; omega) ?_
  rw [hrel, map_zero]
  ring

end GaloisForLFunctions.HTGeometry
