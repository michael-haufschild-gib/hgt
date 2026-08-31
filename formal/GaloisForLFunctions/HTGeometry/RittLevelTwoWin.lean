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

variable [CharZero K] [CharZero L]

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
      push_neg at hj
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

end GaloisForLFunctions.HTGeometry
