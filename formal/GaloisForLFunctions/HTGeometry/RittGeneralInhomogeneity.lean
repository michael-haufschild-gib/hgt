import GaloisForLFunctions.HTGeometry.RittScalingMonomial
import GaloisForLFunctions.HTGeometry.RittLevelOneClassification
import GaloisForLFunctions.HTGeometry.RittTowerDescentStep

/-!
# The coprime split for an arbitrary polynomial inhomogeneity

Nothing in the coprime split uses the inhomogeneity being affine in the coordinate.  For any
`G` in the coefficient ring's polynomial ring, a solution of `σ W = c·W + G(t)` written as a coprime
fraction `P/Q` with `Q` monic satisfies

`Q^Φ(aX + b) = a^{deg Q}·Q`,   `P^Φ(aX + b) = a^{deg Q}·(c·P + G·Q)`,

because `Q` is coprime to `c·P + G·Q` exactly as it is to `c·P + (αX + β)·Q`.

Under a pure scaling the second identity reads, coefficient by coefficient,
`Φ(P_k)·a^k = a^{e}·(c·P_k + G_{k−e})`.  A nonzero coefficient of `G` therefore forces an affine
relation at the matching degree — the corresponding numerator coefficient cannot vanish, since that
would make the coefficient of `G` vanish too — and if `G` is zero every coefficient obeys the same
homogeneous equation, so two nonzero ones have a ratio satisfying a pure power relation.

So the trichotomy holds for any polynomial inhomogeneity: a pure power relation, an affine relation
with a nonzero inhomogeneity that is an explicit multiple of a coefficient of `G`, or a monomial
solution with `G = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The denominator identity, for an arbitrary polynomial inhomogeneity.** -/
theorem twistComp_denominator_eq_gen (Φ : K →+* K) {a b c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + G * Q)) :
    twistComp Φ (C a * X + C b) Q = C (a ^ Q.natDegree) * Q := by
  classical
  set T : K[X] := C a * X + C b with hT
  have hTdeg : T.natDegree = 1 := natDegree_linear ha
  have hTlead : T.leadingCoeff = a := leadingCoeff_linear ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcopQ : IsCoprime Q (C c * P + G * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right G
    have heq : C c * P + Q * G = C c * P + G * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ T Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ T P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hde : d = a ^ Q.natDegree := by
    have hlead := leadingCoeff_twistComp Φ hTdeg Q
    rw [hd, hQ.leadingCoeff, map_one, hTlead, one_mul] at hlead
    rw [leadingCoeff_mul, leadingCoeff_C, hQ.leadingCoeff, mul_one] at hlead
    exact hlead
  rw [hd, hde]

/-- **The numerator identity, for an arbitrary polynomial inhomogeneity.** -/
theorem twistComp_numerator_eq_gen (Φ : K →+* K) {a b c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + G * Q)) :
    twistComp Φ (C a * X + C b) P = C (a ^ Q.natDegree) * (C c * P + G * Q) := by
  refine mul_right_cancel₀ hQ.ne_zero ?_
  rw [hcross, twistComp_denominator_eq_gen Φ ha hc hQ hcop hcross]
  ring

/-- Coefficients of the denominator under a scaling twist, for an arbitrary inhomogeneity. -/
theorem denominator_coeff_eigen_gen (Φ : K →+* K) {a c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + G * Q)) (k : ℕ) :
    Φ (Q.coeff k) * a ^ k = a ^ Q.natDegree * Q.coeff k := by
  have hden := twistComp_denominator_eq_gen Φ ha hc hQ hcop hcross
  have h := congrArg (fun R : K[X] => R.coeff k) hden
  rw [coeff_twistComp_scaling, coeff_C_mul] at h
  exact h

/-- Coefficients of the numerator under a scaling twist, for an arbitrary inhomogeneity. -/
theorem numerator_coeff_eigen_gen (Φ : K →+* K) {a c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + G * Q)) (k : ℕ) :
    Φ (P.coeff k) * a ^ k = a ^ Q.natDegree * (c * P.coeff k + (G * Q).coeff k) := by
  have hnum := twistComp_numerator_eq_gen Φ ha hc hQ hcop hcross
  have h := congrArg (fun R : K[X] => R.coeff k) hnum
  rw [coeff_twistComp_scaling, coeff_C_mul, coeff_add, coeff_C_mul] at h
  exact h

/-- **The scaling classification, for an arbitrary polynomial inhomogeneity.** -/
theorem scaling_monomial_dichotomy_gen (Φ : K →+* K) {a c : K} (ha : a ≠ 0) (hc : c ≠ 0)
    {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q) (hP0 : P ≠ 0)
    (hcross : twistComp Φ (C a * X + C 0) P * Q
      = twistComp Φ (C a * X + C 0) Q * (C c * P + G * Q)) :
    (∃ (w : K) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ Φ w = a ^ s * w) ∨
    (∃ (w : K) (s : ℤ) (h : K) (j : ℕ), w ≠ 0 ∧ h ≠ 0 ∧ h = G.coeff j / a ^ j ∧
      Φ w = a ^ s * c * w + h) ∨
    (∃ (u : K) (k₁ : ℕ), u ≠ 0 ∧ P = C u * X ^ k₁ ∧ Q = X ^ Q.natDegree ∧ G = 0 ∧
      Φ u * a ^ k₁ = a ^ Q.natDegree * c * u) := by
  classical
  set e : ℕ := Q.natDegree with he
  have hden := denominator_coeff_eigen_gen Φ ha hc hQ hcop hcross
  have hnum := numerator_coeff_eigen_gen Φ ha hc hQ hcop hcross
  have hae : (a : K) ^ e ≠ 0 := pow_ne_zero _ ha
  by_cases hlow : ∃ k, k < e ∧ Q.coeff k ≠ 0
  · obtain ⟨k, hke, hk0⟩ := hlow
    refine Or.inl ⟨Q.coeff k, (e : ℤ) - (k : ℤ), hk0, by omega, ?_⟩
    have h := hden k
    rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]
    field_simp
    linear_combination h
  push Not at hlow
  have hQpow : Q = X ^ e := monic_eq_X_pow_of_coeff_vanishing hQ (fun k hk => hlow k hk)
  have hGQ : ∀ k : ℕ, (G * Q).coeff k = if e ≤ k then G.coeff (k - e) else 0 := by
    intro k
    rw [hQpow, mul_comm, coeff_X_pow_mul']
  by_cases hG : G = 0
  · -- homogeneous: every coefficient obeys the same equation
    subst hG
    have hclean : ∀ k : ℕ, Φ (P.coeff k) * a ^ k = (a ^ e * c) * P.coeff k := by
      intro k
      have h := hnum k
      rw [zero_mul, coeff_zero, add_zero] at h
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
        hQpow, rfl, ?_⟩)
      have h := hclean P.natDegree
      rw [← leadingCoeff] at h
      linear_combination h
  · -- a nonzero coefficient of the inhomogeneity splits off an affine relation
    obtain ⟨j, hj⟩ : ∃ j, G.coeff j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hG (Polynomial.ext fun k => by rw [hcon k, coeff_zero])
    have h := hnum (e + j)
    rw [hGQ (e + j), if_pos (by omega), show e + j - e = j by omega] at h
    have hapow : (a : K) ^ (e + j) = a ^ e * a ^ j := pow_add a e j
    rw [hapow] at h
    by_cases hPe : P.coeff (e + j) = 0
    · exfalso
      rw [hPe, map_zero, zero_mul, mul_zero, zero_add] at h
      exact hj ((mul_eq_zero.mp h.symm).resolve_left hae)
    · refine Or.inr (Or.inl ⟨P.coeff (e + j), -(j : ℤ), G.coeff j / a ^ j, j, hPe,
        div_ne_zero hj (pow_ne_zero _ ha), rfl, ?_⟩)
      have haj : (a : K) ^ j ≠ 0 := pow_ne_zero _ ha
      have h' : Φ (P.coeff (e + j)) * a ^ j = c * P.coeff (e + j) + G.coeff j := by
        refine mul_left_cancel₀ hae ?_
        linear_combination h
      rw [zpow_neg, zpow_natCast]
      field_simp
      linear_combination h'

section Ambient

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- The coprime cross relation, for an arbitrary polynomial inhomogeneity. -/
theorem exists_coprime_cross_gen (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    {G : E[X]} (hrel : σ W = algebraMap E L c * W + aeval t G) :
    ∃ A B : E[X], B.Monic ∧ IsCoprime A B ∧ A ≠ 0 ∧ W = aeval t A / aeval t B ∧
      twistComp φ (C a * X + C b) A * B
        = twistComp φ (C a * X + C b) B * (C c * A + G * B) := by
  classical
  obtain ⟨A, B, hB, hcop, hAB⟩ := exists_coprime_monic_repr ht hW
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  have hB0 : B ≠ 0 := hB.ne_zero
  have hBt : aeval t B ≠ 0 := fun h => hB0 (hinj (by simpa using h))
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hAB
    exact hW0 ((mul_eq_zero.mp hAB).resolve_right hBt)
  have hWeq : W = aeval t A / aeval t B := by
    field_simp
    exact hAB
  set T : E[X] := C a * X + C b with hT
  have hTval : aeval t T = σ t := by rw [hT, hσt]; simp
  have htwB : aeval t (twistComp φ T B) ≠ 0 := fun h =>
    (twistComp_ne_zero φ (natDegree_linear ha) hB0) (hinj (by simpa using h))
  refine ⟨A, B, hB, hcop, hA0, hWeq, ?_⟩
  refine hinj ?_
  have hσA := aeval_twistComp_of_aeval_eq σ φ hcomp hTval A
  have hσB := aeval_twistComp_of_aeval_eq σ φ hcomp hTval B
  rw [hWeq, map_div₀, ← hσA, ← hσB] at hrel
  simp only [map_mul, map_add, aeval_C]
  rw [div_eq_iff htwB] at hrel
  field_simp at hrel
  linear_combination hrel

/-- **The scaling classification inside an ambient field, for an arbitrary polynomial
inhomogeneity.** -/
theorem scaling_dichotomy_gen (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a c : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    {G : E[X]} (hrel : σ W = algebraMap E L c * W + aeval t G) :
    (∃ (w : E) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ φ w = a ^ s * w) ∨
    (∃ (w : E) (s : ℤ) (h : E) (j : ℕ), w ≠ 0 ∧ h ≠ 0 ∧ h = G.coeff j / a ^ j ∧
      φ w = a ^ s * c * w + h) ∨
    (∃ (u : E) (j : ℤ), u ≠ 0 ∧ G = 0 ∧ W = algebraMap E L u * t ^ j ∧
      φ u = a ^ (-j) * c * u) := by
  classical
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by rw [h]; exact isAlgebraic_zero)
  have hσt' : σ t = algebraMap E L a * t + algebraMap E L 0 := by rw [map_zero, add_zero, hσt]
  obtain ⟨A, B, hB, hcop, hA0, hWeq, hcross⟩ :=
    exists_coprime_cross_gen σ φ hcomp ht ha hc hσt' hW0 hW hrel
  rcases scaling_monomial_dichotomy_gen φ ha hc hB hcop hA0 hcross with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  obtain ⟨u, k₁, hu0, hAeq, hBeq, hG0, hueq⟩ := h3
  obtain ⟨e, he⟩ : ∃ e, B.natDegree = e := ⟨_, rfl⟩
  rw [he] at hBeq hueq
  refine Or.inr (Or.inr ⟨u, (k₁ : ℤ) - (e : ℤ), hu0, hG0, ?_, ?_⟩)
  · have hAval : (aeval t) A = algebraMap E L u * t ^ k₁ := by rw [hAeq]; simp
    have hBval : (aeval t) B = t ^ e := by rw [hBeq]; simp
    rw [hWeq, hAval, hBval, zpow_sub₀ ht0, zpow_natCast, zpow_natCast]
    field_simp
  · have hae : (a : E) ^ e ≠ 0 := pow_ne_zero _ ha
    have hak : (a : E) ^ k₁ ≠ 0 := pow_ne_zero _ ha
    rw [neg_sub, zpow_sub₀ ha, zpow_natCast, zpow_natCast]
    field_simp
    linear_combination hueq

end Ambient

section Frame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The classification at jet order one, for an arbitrary polynomial inhomogeneity.** -/
theorem level_one_classification_gen (Fr : RittFrame K L) {τ : L} {q : K} (hq : q ≠ 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) (htr : Transcendental K τ)
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 1)
    {c : K} (hc : c ≠ 0) {G : K[X]}
    (hrel : Fr.σ V = algebraMap K L c * V + aeval τ G) :
    (∃ (w : K) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ Fr.ψ w = q ^ s * w) ∨
    (∃ (w : K) (s : ℤ) (h : K) (j : ℕ), w ≠ 0 ∧ h ≠ 0 ∧ h = G.coeff j / q ^ j ∧
      Fr.ψ w = q ^ s * c * w + h) ∨
    (∃ (u : K) (j : ℤ), u ≠ 0 ∧ G = 0 ∧ V = algebraMap K L u * τ ^ j ∧
      Fr.ψ u = q ^ (-j) * c * u) := by
  have hVadj : V ∈ IntermediateField.adjoin K ({τ} : Set L) := by
    rwa [jetPrefixField_one Fr τ] at hV
  exact scaling_dichotomy_gen (E := K) Fr.σ Fr.ψ Fr.comp htr hq hc hshift hV0 hVadj hrel

/-- **The classification at jet order one, for a Laurent inhomogeneity.**  Multiplying the relation
by a power of the coordinate clears the denominator and scales the eigenvalue by the same power of
the multiplier. -/
theorem level_one_classification_laurent (Fr : RittFrame K L) {τ : L} {q : K} (hq : q ≠ 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) (htr : Transcendental K τ)
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 1)
    {c : K} (hc : c ≠ 0) {G : K[X]} {N : ℕ}
    (hrel : Fr.σ V = algebraMap K L c * V + aeval τ G / τ ^ N) :
    (∃ (w : K) (s : ℤ), w ≠ 0 ∧ s ≠ 0 ∧ Fr.ψ w = q ^ s * w) ∨
    (∃ (w : K) (s : ℤ) (h : K), w ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ w = q ^ s * c * w + h) ∨
    (∃ (u : K) (j : ℤ), u ≠ 0 ∧ G = 0 ∧ V = algebraMap K L u * τ ^ j ∧
      Fr.ψ u = q ^ (-j) * c * u) := by
  classical
  have hτ0 : τ ≠ 0 := by
    intro h
    exact htr (by rw [h]; exact isAlgebraic_zero)
  have hτN : (τ : L) ^ N ≠ 0 := pow_ne_zero _ hτ0
  have hτmem : τ ∈ Fr.jetPrefixField τ 1 := by
    have h0 := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 1) (by omega)
    simpa using h0
  have hqN : (q : K) ^ N ≠ 0 := pow_ne_zero _ hq
  have hcq : c * q ^ N ≠ 0 := mul_ne_zero hc hqN
  have hV'0 : V * τ ^ N ≠ 0 := mul_ne_zero hV0 hτN
  have hV' : V * τ ^ N ∈ Fr.jetPrefixField τ 1 := mul_mem hV (pow_mem hτmem N)
  have hστ : Fr.σ (τ ^ N) = algebraMap K L (q ^ N) * τ ^ N := by
    rw [map_pow, hshift, mul_pow, map_pow]
  have hGval : aeval τ (C (q ^ N) * G) = algebraMap K L (q ^ N) * aeval τ G := by
    rw [map_mul, aeval_C]
  have hrel' : Fr.σ (V * τ ^ N) = algebraMap K L (c * q ^ N) * (V * τ ^ N)
      + aeval τ (C (q ^ N) * G) := by
    rw [map_mul, hστ, hrel, hGval, map_mul]
    field_simp
  rcases level_one_classification_gen Fr hq hshift htr hV'0 hV' hcq hrel' with
      h1 | ⟨w, s, h, jj, hw0, hh0, -, hweq⟩ | ⟨u, j, hu0, hG0, hVeq, hueq⟩
  · exact Or.inl h1
  · refine Or.inr (Or.inl ⟨w, s + (N : ℤ), h, hw0, hh0, ?_⟩)
    rw [hweq, zpow_add₀ hq, zpow_natCast]
    ring
  · have hGzero : G = 0 := by
      rcases mul_eq_zero.mp hG0 with hh | hh
      · exact absurd (C_eq_zero.mp hh) hqN
      · exact hh
    refine Or.inr (Or.inr ⟨u, (j : ℤ) - (N : ℤ), hu0, hGzero, ?_, ?_⟩)
    · have hτz : (τ : L) ^ ((j : ℤ) - (N : ℤ)) = τ ^ j / τ ^ (N : ℤ) := zpow_sub₀ hτ0 _ _
      rw [hτz, zpow_natCast]
      refine mul_right_cancel₀ hτN ?_
      rw [hVeq]
      field_simp
    · rw [hueq, neg_sub, zpow_sub₀ hq, zpow_natCast]
      field_simp
      rw [← zpow_add₀ hq]
      simp

/-- The image of the base polynomial ring inside the first jet prefix field. -/
theorem aeval_mem_jetPrefixField_one (Fr : RittFrame K L) (τ : L) (p : K[X]) :
    aeval τ p ∈ Fr.jetPrefixField τ 1 := by
  have hτmem : τ ∈ Fr.jetPrefixField τ 1 := by
    have h0 := Fr.jet_mem_jetPrefixField (τ := τ) (j := 0) (n := 1) (by omega)
    simpa using h0
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hτmem n)

/-- **A relation at jet order two with a nonzero polynomial inhomogeneity forces Ritt's form or an
affine transport equation.**  The monomial alternative of the classification needs the inhomogeneity
to vanish, so it is excluded outright. -/
theorem level_two_nonzero_inhom (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {V : L} (hV0 : V ≠ 0) (hV : V ∈ Fr.jetPrefixField τ 2)
    {c : K} (hc : c ≠ 0) {i₀ k₀ : ℤ} (hcik : c = q ^ i₀ * Fr.ρ ^ k₀)
    {G : ℕ → K[X]} {n : ℕ}
    (hG : ∃ j, j < n ∧ G j ≠ 0)
    (hrel : Fr.σ V = algebraMap K L c * V
      + ∑ j ∈ Finset.range n, aeval τ (G j) * (Fr.d τ) ^ j) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ) (j k : ℕ), u ≠ 0 ∧ h ≠ 0 ∧
      h = (G j).coeff k / ((q / Fr.ρ) ^ j * q ^ k) ∧
      Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set E : IntermediateField K L := Fr.jetPrefixField τ 1 with hEdef
  have hEσ : ∀ x ∈ E, Fr.σ x ∈ E := Fr.sigma_mem_jetPrefixField hqconst hshift 1
  set φ : ↥E →+* ↥E :=
    { toFun := fun x => ⟨Fr.σ (x : L), hEσ (x : L) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ
  have hcompE : ∀ x : ↥E, Fr.σ (algebraMap ↥E L x) = algebraMap ↥E L (φ x) := fun _ => rfl
  set aK : K := q / Fr.ρ with haKdef
  have haK0 : aK ≠ 0 := div_ne_zero hq hρ0
  set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
  have haE0 : aE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
  set cE : ↥E := ⟨algebraMap K L c, IntermediateField.algebraMap_mem _ _⟩ with hcE
  have hcE0 : cE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc) (congrArg Subtype.val h)
  have hσt : Fr.σ (Fr.d τ) = algebraMap ↥E L aE * Fr.d τ :=
    Fr.sigma_d_eq_of_shift hqconst hshift
  have hVadj : V ∈ IntermediateField.adjoin ↥E ({Fr.d τ} : Set L) := by
    have hV2 : V ∈ Fr.jetPrefixField τ (1 + 1) := hV
    have := (jetPrefixField_succ_eq Fr τ 1) ▸ hV2
    exact this
  set ι : K[X] → ↥E := fun p => ⟨aeval τ p, aeval_mem_jetPrefixField_one Fr τ p⟩ with hι
  set GG : (↥E)[X] := ∑ j ∈ Finset.range n, C (ι (G j)) * X ^ j with hGG
  have hGGcoeff : ∀ k, k < n → GG.coeff k = ι (G k) := by
    intro k hk
    rw [hGG, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hk) hmem
  have hGGval : aeval (Fr.d τ) GG
      = ∑ j ∈ Finset.range n, aeval τ (G j) * (Fr.d τ) ^ j := by
    rw [hGG, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, aeval_C, aeval_X]
    rfl
  have hrelE : Fr.σ V = algebraMap ↥E L cE * V + aeval (Fr.d τ) GG := by
    rw [hGGval]
    exact hrel
  have hGG0 : GG ≠ 0 := by
    obtain ⟨j, hjn, hj0⟩ := hG
    intro hzero
    have h := hGGcoeff j hjn
    rw [hzero, coeff_zero] at h
    refine hj0 ?_
    have hinj : Function.Injective (aeval τ : K[X] →ₐ[K] L) :=
      transcendental_iff_injective.mp htr0
    refine hinj ?_
    have : ((ι (G j) : ↥E) : L) = ((0 : ↥E) : L) := congrArg Subtype.val h.symm
    simpa [hι] using this
  have hcoez : ∀ (x : ↥E) (m : ℤ), ((x ^ m : ↥E) : L) = ((x : L)) ^ m :=
    fun x m => map_zpow₀ (algebraMap ↥E L) x m
  rcases scaling_dichotomy_gen (E := ↥E) Fr.σ φ hcompE htr1 haE0 hcE0 hσt hV0 hVadj hrelE with
      ⟨w, s, hw0, hs0, hweq⟩ | ⟨w, s, h, jj, hw0, hh0, hhval, hweq⟩ | ⟨-, -, -, hG0, -, -⟩
  · -- a pure power relation over `K⟮τ⟯`
    have hwL : (w : L) ≠ 0 := fun hh => hw0 (Subtype.ext (by simpa using hh))
    have hcast := congrArg (fun z : ↥E => (z : L)) hweq
    simp only [hφ] at hcast
    push_cast [hcoez] at hcast
    simp only [haE] at hcast
    have e1 : algebraMap K L (aK ^ s) = (algebraMap K L aK) ^ s := map_zpow₀ _ _ _
    have hak0 : aK ^ s ≠ 0 := zpow_ne_zero _ haK0
    have hrel1 : Fr.σ (w : L) = algebraMap K L (aK ^ s) * (w : L) + aeval τ (0 : K[X]) := by
      rw [e1, map_zero, add_zero]
      linear_combination hcast
    rcases level_one_classification_gen Fr hq hshift htr0 hwL w.2 hak0 hrel1 with
        ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', kk, hw'0, hh'0, hh'val, hw'eq⟩ |
        ⟨u', j', hu'0, -, -, hu'eq⟩
    · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
    · exact absurd hh'val (by
        rw [coeff_zero, zero_div]
        exact hh'0)
    · refine Or.inl ⟨u', -j' + s, -s, hu'0, ?_, ?_⟩
      · rintro ⟨-, hh⟩
        exact hs0 (by omega)
      · have hmul : q ^ (-j') * aK ^ s = q ^ (-j' + s) * Fr.ρ ^ (-s) := by
          rw [haKdef, div_zpow, zpow_add₀ hq, zpow_neg Fr.ρ s, div_eq_mul_inv]
          ring
        rw [hu'eq, hmul]
  · -- an affine relation over `K⟮τ⟯` with nonzero inhomogeneity
    have hwL : (w : L) ≠ 0 := fun hh => hw0 (Subtype.ext (by simpa using hh))
    have hc1 : aK ^ s * c ≠ 0 := mul_ne_zero (zpow_ne_zero _ haK0) hc
    have hjjn : jj < n := by
      by_contra hge
      push Not at hge
      refine hh0 ?_
      have hzero : GG.coeff jj = 0 := by
        rw [hGG, Polynomial.finsetSum_coeff]
        refine Finset.sum_eq_zero fun b hb => ?_
        rw [Finset.mem_range] at hb
        rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
      rw [hhval, hzero, zero_div]
    set Gj : K[X] := C ((aK ^ jj)⁻¹) * G jj with hGj
    have hhL : ((h : ↥E) : L) = aeval τ Gj := by
      have hstep : ((h : ↥E) : L) = aeval τ (G jj) / (algebraMap K L aK) ^ jj := by
        rw [hhval, hGGcoeff jj hjjn]
        push_cast
        rfl
      rw [hstep, hGj, map_mul, aeval_C, map_inv₀, map_pow, div_eq_mul_inv]
      ring
    have hGj0 : Gj ≠ 0 := by
      intro hzero
      refine hh0 (Subtype.ext ?_)
      rw [hhL, hzero, map_zero]
      rfl
    have hcast := congrArg (fun z : ↥E => (z : L)) hweq
    simp only [hφ] at hcast
    push_cast [hcoez] at hcast
    simp only [haE, hcE] at hcast
    have e1 : algebraMap K L (aK ^ s * c)
        = (algebraMap K L aK) ^ s * algebraMap K L c := by rw [map_mul, map_zpow₀]
    have hrel1 : Fr.σ (w : L) = algebraMap K L (aK ^ s * c) * (w : L) + aeval τ Gj := by
      rw [e1, ← hhL]
      linear_combination hcast
    rcases level_one_classification_gen Fr hq hshift htr0 hwL w.2 hc1 hrel1 with
        ⟨w', s', hw'0, hs'0, hw'eq⟩ | ⟨w', s', h', kk, hw'0, hh'0, hh'val, hw'eq⟩ |
        ⟨u', j', hu'0, hGjzero, -, -⟩
    · exact Or.inl ⟨w', s', 0, hw'0, by rintro ⟨hh, -⟩; exact hs'0 hh, by rw [hw'eq]; simp⟩
    · refine Or.inr ⟨w', h', s' + s + i₀, -s + k₀, jj, kk, hw'0, hh'0, ?_, ?_⟩
      · rw [hh'val, hGj, coeff_C_mul, haKdef]
        have haj : (aK : K) ^ jj ≠ 0 := pow_ne_zero _ haK0
        have hqk : (q : K) ^ kk ≠ 0 := pow_ne_zero _ hq
        rw [haKdef] at haj
        field_simp
      · have hmon : q ^ s' * (aK ^ s * c) = q ^ (s' + s + i₀) * Fr.ρ ^ (-s + k₀) := by
          rw [haKdef, hcik, div_zpow, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hρ0, zpow_neg]
          have h1 : (Fr.ρ : K) ^ s ≠ 0 := zpow_ne_zero _ hρ0
          field_simp
        rw [hw'eq, hmon]
    · exact absurd hGjzero hGj0
  · exact absurd hG0 hGG0

/-- **The affine exceptional datum at jet order two is refuted.**  Its inhomogeneity is a nonzero
constant, so the monomial alternative of the classification cannot occur. -/
theorem ritt_or_affine_of_excAff_two (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    {v : L} {h : K} (hv0 : v ≠ 0) (hh0 : h ≠ 0) (hvmem : v ∈ Fr.jetPrefixField τ 2)
    (hrel : Fr.σ v = algebraMap K L (Fr.ρ)⁻¹ * v + algebraMap K L h) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hGne : (fun j : ℕ => if j = 0 then C h else 0) 0 ≠ 0 := by
    simp only [if_pos rfl]
    exact fun hzero => hh0 (C_eq_zero.mp hzero)
  have hrel2 : Fr.σ v = algebraMap K L (Fr.ρ)⁻¹ * v
      + ∑ j ∈ Finset.range 1,
        aeval τ ((fun j : ℕ => if j = 0 then C h else 0) j) * (Fr.d τ) ^ j := by
    rw [hrel, Finset.sum_range_one]
    simp
  have hcik : (Fr.ρ)⁻¹ = q ^ (0 : ℤ) * Fr.ρ ^ (-1 : ℤ) := by
    rw [zpow_zero, one_mul, zpow_neg_one]
  rcases level_two_nonzero_inhom Fr hqconst hshift hq htr0 htr1 hv0 hvmem (inv_ne_zero hρ0)
      hcik ⟨0, by omega, hGne⟩ hrel2 with
      hritt | ⟨u, h', I, J, j, k, hu0, hh'0, hh'val, hbase⟩
  · exact Or.inl hritt
  · refine Or.inr ⟨u, I, J, hu0, ?_⟩
    have hjk : j = 0 ∧ k = 0 := by
      by_contra hcon
      refine hh'0 ?_
      rw [hh'val]
      rcases not_and_or.mp hcon with hj | hk
      · rw [if_neg hj, coeff_zero, zero_div]
      · by_cases hj0 : j = 0
        · rw [if_pos hj0, coeff_C, if_neg hk, zero_div]
        · rw [if_neg hj0, coeff_zero, zero_div]
    rw [hbase, hh'val, hjk.1, hjk.2, if_pos rfl, coeff_C, if_pos rfl, pow_zero, pow_zero,
      mul_one, div_one]

end Frame

end GaloisForLFunctions.HTGeometry
