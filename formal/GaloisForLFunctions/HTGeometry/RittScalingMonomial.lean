import GaloisForLFunctions.HTGeometry.RittDiagonalToolkit

/-!
# The scaling classification: a solution is a monomial unless a relation splits off

When the shift scales the coordinate, `σ t = a·t`, the coprime split becomes a family of scalar
equations, one per coefficient, all with the same scalar.  Three things follow at once.

* A denominator coefficient below the top gives `Φ(w) = a^{e−k}·w`: a **pure power** relation, with
  no eigenvalue in it at all.  A denominator without one is `t^{deg Q}`.
* A nonzero constant part `β` of the inhomogeneity forces the equation at degree `deg Q` to read
  `Φ(P_e) = c·P_e + β`, and `P_e = 0` would make `β = 0`; so `β ≠ 0` yields an **affine** relation
  with nonzero inhomogeneity.  A nonzero linear part `α` does the same one degree higher.
* With the inhomogeneity gone every coefficient satisfies the same equation, so two nonzero
  coefficients have a ratio obeying a pure power relation.  A numerator without two is a monomial.

So either a pure power relation or an affine relation with nonzero inhomogeneity splits off, or the
solution is `u·t^{k₁ − deg Q}` with the inhomogeneity identically zero.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- The coefficients of an affine polynomial times a power of the coordinate. -/
theorem coeff_affine_mul_X_pow (α β : K) (e k : ℕ) :
    ((C α * X + C β) * X ^ e).coeff k
      = α * (if k = e + 1 then 1 else 0) + β * (if k = e then 1 else 0) := by
  have hsplit : (C α * X + C β) * X ^ e = C α * X ^ (e + 1) + C β * X ^ e := by
    rw [add_mul, mul_assoc, ← pow_succ']
  rw [hsplit, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow]

/-- A polynomial with at most one nonzero coefficient is a monomial. -/
theorem eq_C_mul_X_pow_of_unique_coeff {P : K[X]} (hP0 : P ≠ 0)
    (hone : ∀ k k' : ℕ, k ≠ k' → P.coeff k = 0 ∨ P.coeff k' = 0) :
    P = C P.leadingCoeff * X ^ P.natDegree := by
  refine Polynomial.ext fun k => ?_
  rw [coeff_C_mul, coeff_X_pow]
  rcases eq_or_ne k P.natDegree with rfl | hne
  · rw [if_pos rfl, mul_one, leadingCoeff]
  · rw [if_neg (by omega), mul_zero]
    rcases hone k P.natDegree hne with h | h
    · exact h
    · exact absurd h (leadingCoeff_ne_zero.mpr hP0)

/-- **The scaling classification.** -/
theorem scaling_monomial_dichotomy (Φ : K →+* K) {a c α β : K} (ha : a ≠ 0) (hc : c ≠ 0)
    {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q) (hP0 : P ≠ 0)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + (C α * X + C β) * Q)) :
    (∃ (w : K) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ Φ w = a ^ s * w) ∨
    (∃ (w : K) (s : ℤ) (h : K), w ≠ 0 ∧ h ≠ 0 ∧ (h = β ∨ h = α / a) ∧
      Φ w = a ^ s * c * w + h) ∨
    (∃ (u : K) (k₁ : ℕ), u ≠ 0 ∧ P = C u * X ^ k₁ ∧ Q = X ^ Q.natDegree ∧ α = 0 ∧ β = 0 ∧
      Φ u * a ^ k₁ = a ^ Q.natDegree * c * u) := by
  classical
  set e : ℕ := Q.natDegree with he
  have hden := denominator_coeff_eigen Φ ha hc hQ hcop hcross
  have hnum := numerator_coeff_eigen Φ ha hc hQ hcop hcross
  -- the denominator is a pure power unless a pure power relation splits off
  by_cases hlow : ∃ k, k < e ∧ Q.coeff k ≠ 0
  · obtain ⟨k, hke, hk0⟩ := hlow
    refine Or.inl ⟨Q.coeff k, (e : ℤ) - (k : ℤ), hk0, by omega, ?_⟩
    have h := hden k
    rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
    field_simp
    linear_combination h
  push Not at hlow
  have hQpow : Q = X ^ e := monic_eq_X_pow_of_coeff_vanishing hQ (fun k hk => hlow k hk)
  have hcoeff : ∀ k : ℕ, Φ (P.coeff k) * a ^ k
      = a ^ e * (c * P.coeff k
        + (α * (if k = e + 1 then 1 else 0) + β * (if k = e then 1 else 0))) := by
    intro k
    have h := hnum k
    rw [hQpow, coeff_affine_mul_X_pow, natDegree_X_pow] at h
    exact h
  have hae : (a : K) ^ e ≠ 0 := pow_ne_zero _ ha
  -- a nonzero constant part of the inhomogeneity splits off an affine relation
  by_cases hβ : β = 0
  · by_cases hα : α = 0
    · -- the homogeneous case: every coefficient obeys the same equation
      subst hα
      subst hβ
      have hclean : ∀ k : ℕ, Φ (P.coeff k) * a ^ k = (a ^ e * c) * P.coeff k := by
        intro k
        have h := hcoeff k
        simp only [zero_mul, add_zero] at h
        linear_combination h
      by_cases htwo : ∃ k k' : ℕ, k ≠ k' ∧ P.coeff k ≠ 0 ∧ P.coeff k' ≠ 0
      · obtain ⟨k, k', hne, h0, h0'⟩ := htwo
        have hs : ((k' : ℤ) - (k : ℤ)) ≠ 0 := by
          intro hh
          exact hne (by omega)
        exact Or.inl ⟨P.coeff k / P.coeff k', (k' : ℤ) - (k : ℤ), div_ne_zero h0 h0', hs,
          ratio_eigen_of_two_coeffs Φ ha (hclean k) (hclean k') h0'⟩
      · push Not at htwo
        have hmono : P = C P.leadingCoeff * X ^ P.natDegree :=
          eq_C_mul_X_pow_of_unique_coeff hP0 (fun k k' hne => by
            by_cases h : P.coeff k = 0
            · exact Or.inl h
            · exact Or.inr (htwo k k' hne h))
        refine Or.inr (Or.inr ⟨P.leadingCoeff, P.natDegree, leadingCoeff_ne_zero.mpr hP0, hmono,
          hQpow, rfl, rfl, ?_⟩)
        have h := hclean P.natDegree
        rw [← leadingCoeff] at h
        linear_combination h
    · -- a nonzero linear part
      have h := hcoeff (e + 1)
      rw [if_pos rfl, if_neg (by omega : ¬ e + 1 = e), mul_one, mul_zero, add_zero] at h
      by_cases hPe : P.coeff (e + 1) = 0
      · exfalso
        rw [hPe, map_zero, zero_mul, mul_zero, zero_add] at h
        exact hα ((mul_eq_zero.mp h.symm).resolve_left hae)
      · refine Or.inr (Or.inl ⟨P.coeff (e + 1), -1, α / a, hPe, div_ne_zero hα ha,
          Or.inr rfl, ?_⟩)
        have hapow : (a : K) ^ (e + 1) = a ^ e * a := pow_succ a e
        rw [hapow] at h
        have h' : Φ (P.coeff (e + 1)) * a = c * P.coeff (e + 1) + α := by
          refine mul_left_cancel₀ hae ?_
          linear_combination h
        rw [zpow_neg, zpow_one]
        field_simp
        linear_combination h'
  · -- a nonzero constant part
    have h := hcoeff e
    rw [if_neg (by omega : ¬ e = e + 1), if_pos rfl, mul_one, mul_zero, zero_add] at h
    by_cases hPe : P.coeff e = 0
    · exfalso
      rw [hPe, map_zero, zero_mul, mul_zero, zero_add] at h
      exact hβ ((mul_eq_zero.mp h.symm).resolve_left hae)
    · refine Or.inr (Or.inl ⟨P.coeff e, 0, β, hPe, hβ, Or.inl rfl, ?_⟩)
      rw [zpow_zero, one_mul]
      refine mul_left_cancel₀ hae ?_
      linear_combination h

section Ambient

variable {E L : Type*} [Field E] [CharZero E] [Field L] [Algebra E L]

omit [CharZero E] in
/-- **The scaling classification inside an ambient field.**  Over a coordinate the shift merely
scales, a solution of `σ V = c·V + (α·t + β)` either splits off a pure power relation or an affine
relation with nonzero inhomogeneity, or is a monomial `u·t^j` with the inhomogeneity zero. -/
theorem scaling_dichotomy_of_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a c α β : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t)
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ V = algebraMap E L c * V + (algebraMap E L α * t + algebraMap E L β)) :
    (∃ (w : E) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ φ w = a ^ s * w) ∨
    (∃ (w : E) (s : ℤ) (h : E), w ≠ 0 ∧ h ≠ 0 ∧ (h = β ∨ h = α / a) ∧
      φ w = a ^ s * c * w + h) ∨
    (∃ (u : E) (j : ℤ), u ≠ 0 ∧ α = 0 ∧ β = 0 ∧ V = algebraMap E L u * t ^ j ∧
      φ u = a ^ (-j) * c * u) := by
  classical
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by rw [h]; exact isAlgebraic_zero)
  have hσt' : σ t = algebraMap E L a * t + algebraMap E L 0 := by rw [map_zero, add_zero, hσt]
  obtain ⟨A, B, hB, hcop, hA0, hVeq, hcross, -⟩ :=
    exists_denominator_relation_of_affine_mem_adjoin σ φ hcomp ht ha hc hσt' hV0 hV hrel
  rcases scaling_monomial_dichotomy φ ha hc hB hcop hA0 hcross with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  obtain ⟨u, k₁, hu0, hAeq, hBeq, hα, hβ, hueq⟩ := h3
  obtain ⟨e, he⟩ : ∃ e, B.natDegree = e := ⟨_, rfl⟩
  rw [he] at hBeq hueq
  refine Or.inr (Or.inr ⟨u, (k₁ : ℤ) - (e : ℤ), hu0, hα, hβ, ?_, ?_⟩)
  · have hAval : (aeval t) A = algebraMap E L u * t ^ k₁ := by rw [hAeq]; simp
    have hBval : (aeval t) B = t ^ e := by rw [hBeq]; simp
    rw [hVeq, hAval, hBval, zpow_sub₀ ht0, zpow_natCast, zpow_natCast]
    field_simp
  · have hae : (a : E) ^ e ≠ 0 := pow_ne_zero _ ha
    have hak : (a : E) ^ k₁ ≠ 0 := pow_ne_zero _ ha
    rw [neg_sub, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
    field_simp
    linear_combination hueq

end Ambient

end GaloisForLFunctions.HTGeometry
