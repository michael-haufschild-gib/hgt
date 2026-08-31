import GaloisForLFunctions.HTGeometry.RittAffineSliceResidue
import GaloisForLFunctions.HTGeometry.TwistedScalingDescent

/-!
# The subleading coefficient of a linear twist

Comparing leading coefficients across the shift relation identifies the residue but says nothing
once the numerator has been normalised to be monic.  The next coefficient does say something, and
what it says involves the constant term of the affine action on the top jet.

The computation rests on one identity: the coefficient of `X^n` in `(aX + b)^{n+1}` is
`(n+1)·a^n·b`.  So in the twist of a polynomial by `X ↦ aX + b`, the subleading coefficient picks up
a term proportional to `b` times the leading coefficient — which is exactly where the affine part of
the shift, and with it the derivation, enters the descent.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- The leading coefficient of a power of a linear polynomial. -/
theorem coeff_linear_pow_self {a b : K} (ha : a ≠ 0) (n : ℕ) :
    ((C a * X + C b) ^ n).coeff n = a ^ n := by
  have hdeg : ((C a * X + C b : K[X]) ^ n).natDegree = n := by
    rw [natDegree_pow, natDegree_linear ha, mul_one]
  have hlead : ((C a * X + C b : K[X]) ^ n).leadingCoeff = a ^ n := by
    rw [leadingCoeff_pow, leadingCoeff_linear ha]
  have h := Polynomial.coeff_natDegree (p := ((C a * X + C b : K[X]) ^ n))
  rw [hdeg] at h
  rw [h, hlead]

/-- **The subleading coefficient of a power of a linear polynomial.** -/
theorem coeff_linear_pow_sub_one {a b : K} (ha : a ≠ 0) :
    ∀ n : ℕ, ((C a * X + C b) ^ (n + 1)).coeff n = ((n : K) + 1) * a ^ n * b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : ((C a * X + C b : K[X]) ^ (n + 2))
          = C a * (((C a * X + C b : K[X]) ^ (n + 1)) * X)
            + C b * ((C a * X + C b : K[X]) ^ (n + 1)) := by
        rw [pow_succ]
        ring
      rw [hsplit, coeff_add, coeff_C_mul, coeff_C_mul, coeff_mul_X,
        coeff_linear_pow_self ha (n + 1), ih]
      push_cast
      ring

/-- The top coefficient of a composition with a linear polynomial. -/
theorem coeff_comp_linear_of_natDegree_le {a b : K} (ha : a ≠ 0) {R : K[X]} {n : ℕ}
    (hR : R.natDegree ≤ n) :
    (R.comp (C a * X + C b)).coeff n = R.coeff n * a ^ n := by
  have hT : (C a * X + C b : K[X]).natDegree = 1 := natDegree_linear ha
  rcases eq_or_lt_of_le hR with heq | hlt
  · have hcomp : (R.comp (C a * X + C b)).natDegree = n := by
      rw [natDegree_comp, hT, mul_one, heq]
    have hlead : (R.comp (C a * X + C b)).leadingCoeff = R.leadingCoeff * a ^ R.natDegree := by
      rw [leadingCoeff_comp (by rw [hT]; norm_num), leadingCoeff_linear ha]
    have h := Polynomial.coeff_natDegree (p := R.comp (C a * X + C b))
    rw [hcomp, hlead] at h
    rw [h, leadingCoeff, heq]
  · have hRc : R.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hlt
    have hcomp : (R.comp (C a * X + C b)).natDegree < n := by
      rw [natDegree_comp, hT, mul_one]
      exact hlt
    rw [coeff_eq_zero_of_natDegree_lt hcomp, hRc, zero_mul]

/-- **The subleading coefficient of a composition with a linear polynomial.** -/
theorem coeff_comp_linear_sub_one {a b : K} (ha : a ≠ 0) {R : K[X]} {n : ℕ}
    (hR : R.natDegree ≤ n + 1) :
    (R.comp (C a * X + C b)).coeff n
      = R.coeff n * a ^ n + R.coeff (n + 1) * ((n : K) + 1) * a ^ n * b := by
  set u : K := R.coeff (n + 1) with hu
  set R₁ : K[X] := R - C u * X ^ (n + 1) with hR₁
  have hR₁deg : R₁.natDegree ≤ n := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro m hm
    rw [hR₁, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases eq_or_ne m (n + 1) with rfl | hne
    · rw [if_pos rfl, mul_one, hu, sub_self]
    · rw [if_neg hne, mul_zero, sub_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hsplit : R = C u * X ^ (n + 1) + R₁ := by rw [hR₁]; ring
  have hcomp : R.comp (C a * X + C b)
      = C u * (C a * X + C b) ^ (n + 1) + R₁.comp (C a * X + C b) := by
    conv_lhs => rw [hsplit]
    rw [add_comp, mul_comp, C_comp, pow_comp, X_comp]
  have hR₁n : R₁.coeff n = R.coeff n := by
    rw [hR₁, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega : ¬ n = n + 1), mul_zero,
      sub_zero]
  rw [hcomp, coeff_add, coeff_C_mul, coeff_linear_pow_sub_one ha n,
    coeff_comp_linear_of_natDegree_le ha hR₁deg, hR₁n]
  ring

/-- **The subleading slice of an affine cross relation.**  Comparing the two sides one degree below
the top produces an affine relation for the subleading coefficient whose inhomogeneity carries the
constant term `b` of the affine action. -/
theorem subleading_relation_of_affine_cross (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hPdeg : 1 ≤ P.natDegree)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    ∃ d : K, d ≠ 0 ∧
      Φ (P.coeff (P.natDegree - 1)) * a ^ (P.natDegree - 1)
        + Φ P.leadingCoeff * (P.natDegree : K) * a ^ (P.natDegree - 1) * b
      = d * (c * P.coeff (P.natDegree - 1)
          + ((C α * X + C β) * Q).coeff (P.natDegree - 1)) := by
  classical
  set T : K[X] := C a * X + C b with hT
  have hTdeg : T.natDegree = 1 := natDegree_linear ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcopQ : IsCoprime Q (C c * P + (C α * X + C β) * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right (C α * X + C β)
    have heq : C c * P + Q * (C α * X + C β) = C c * P + (C α * X + C β) * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ T Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ T P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hnum : twistComp Φ T P = C d * (C c * P + (C α * X + C β) * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hd]
    ring
  refine ⟨d, hd0, ?_⟩
  have hmapdeg : (P.map Φ).natDegree ≤ (P.natDegree - 1) + 1 := by
    have := natDegree_map_le (f := Φ) (p := P)
    omega
  have hcoeff := congrArg (fun R : K[X] => R.coeff (P.natDegree - 1)) hnum
  simp only [twistComp] at hcoeff
  rw [coeff_comp_linear_sub_one ha hmapdeg] at hcoeff
  have hidx : (P.natDegree - 1) + 1 = P.natDegree := by omega
  have hcast : ((P.natDegree - 1 : ℕ) : K) + 1 = (P.natDegree : K) := by
    have h1 : (P.natDegree - 1) + 1 = P.natDegree := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → K) h1
  rw [coeff_map, coeff_map, hidx] at hcoeff
  simp only [coeff_add, coeff_C_mul, mul_add] at hcoeff
  simp only [Polynomial.leadingCoeff] at hcoeff ⊢
  linear_combination hcoeff - (Φ (P.coeff P.natDegree) * a ^ (P.natDegree - 1) * b) * hcast

section Ambient

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- **The subleading slice for an element of a simple transcendental adjunction.** -/
theorem exists_subleading_relation_of_affine_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c α β : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = algebraMap E L c * W + (algebraMap E L α * t + algebraMap E L β)) :
    ∃ A B : E[X], B.Monic ∧ IsCoprime A B ∧ A ≠ 0 ∧
      (1 ≤ A.natDegree → ∃ d : E, d ≠ 0 ∧
        φ (A.coeff (A.natDegree - 1)) * a ^ (A.natDegree - 1)
          + φ A.leadingCoeff * (A.natDegree : E) * a ^ (A.natDegree - 1) * b
        = d * (c * A.coeff (A.natDegree - 1)
            + ((C α * X + C β) * B).coeff (A.natDegree - 1))) := by
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
  have hcross : twistComp φ T A * B = twistComp φ T B * (C c * A + (C α * X + C β) * B) := by
    refine hinj ?_
    have hσA := aeval_twistComp_of_aeval_eq σ φ hcomp hTval A
    have hσB := aeval_twistComp_of_aeval_eq σ φ hcomp hTval B
    rw [hWeq, map_div₀, ← hσA, ← hσB] at hrel
    rw [map_mul, map_mul, map_add, map_mul, map_mul, map_add, map_mul, aeval_C, aeval_C,
      aeval_C, aeval_X]
    rw [div_eq_iff htwB] at hrel
    field_simp at hrel
    linear_combination hrel
  refine ⟨A, B, hB, hcop, hA0, ?_⟩
  intro hAdeg
  exact subleading_relation_of_affine_cross φ ha hc hB hcop hAdeg hcross

end Ambient

end GaloisForLFunctions.HTGeometry
