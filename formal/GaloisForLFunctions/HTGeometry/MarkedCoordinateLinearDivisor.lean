import GaloisForLFunctions.HTGeometry.LinearDivisorResidueField

/-!
# A hypersurface linear in one coordinate is birational to its base

Splitting a polynomial ring at a marked coordinate presents it as a univariate polynomial ring over
the polynomial ring in the remaining coordinates.  Under that presentation a polynomial of degree
one in the marked coordinate is literally linear, `C a * X + C b` with `a ≠ 0`, so the divisor it
cuts out has a residue ring that embeds in the field of rational functions in the remaining
coordinates, compatibly with those coordinates.

That is residue degree one: the divisor maps birationally onto its base.

## Main results

* `natDegree_markedSplit` — the split degree is the degree in the marked coordinate.
* `markedSplit_eq_linear` — degree one in the marked coordinate means linear in it.
* `isPrimitive_of_irreducible` — an irreducible polynomial of positive degree is primitive.
* `exists_injective_ringHom_quotient_span_of_degreeOf_eq_one` — **birationality.**
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

/-- Splitting a polynomial ring at a marked coordinate: polynomials in all the coordinates are
polynomials in the marked one with coefficients polynomial in the others. -/
def markedSplit (K : Type*) [CommRing K] {σ : Type*} [DecidableEq σ] (a : σ) :
    MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {b : σ // b ≠ a} K) :=
  (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe a).symm).trans
    (MvPolynomial.optionEquivLeft K _)

theorem markedSplit_apply (K : Type*) [CommRing K] {σ : Type*} [DecidableEq σ] (a : σ)
    (p : MvPolynomial σ K) :
    markedSplit K a p
      = MvPolynomial.optionEquivLeft K _
          (MvPolynomial.rename (Equiv.optionSubtypeNe a).symm p) :=
  rfl

/-- The degree of the split polynomial in the marked variable is the degree of the original in the
marked coordinate. -/
theorem natDegree_markedSplit (K : Type*) [CommRing K] {σ : Type*} [DecidableEq σ] (a : σ)
    (p : MvPolynomial σ K) :
    (markedSplit K a p).natDegree = MvPolynomial.degreeOf a p :=
  (MvPolynomial.degreeOf_eq_natDegree a p).symm

/-- **An irreducible polynomial of positive degree is primitive.**  A common divisor of all the
coefficients is a constant factor, and the cofactor has positive degree, so it is not a unit. -/
theorem isPrimitive_of_irreducible {S : Type*} [CommRing S] {p : Polynomial S}
    [NoZeroDivisors S] (hirr : Irreducible p) (hd : 0 < p.natDegree) : p.IsPrimitive := by
  intro r hr
  obtain ⟨q, hq⟩ := hr
  rcases hirr.isUnit_or_isUnit hq with h1 | h1
  · exact Polynomial.isUnit_C.mp h1
  · exfalso
    have hqd : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h1
    have hle : p.natDegree ≤ 0 := by
      calc p.natDegree = (Polynomial.C r * q).natDegree := by rw [hq]
        _ ≤ (Polynomial.C r).natDegree + q.natDegree := Polynomial.natDegree_mul_le
        _ = 0 := by simp [hqd]
    omega

section Field

variable {K : Type*} [Field K] {σ : Type*} [DecidableEq σ] {a : σ}

/-- **Degree one in the marked coordinate means linear in it.** -/
theorem markedSplit_eq_linear {g : MvPolynomial σ K} (h : MvPolynomial.degreeOf a g = 1) :
    markedSplit K a g
      = Polynomial.C ((markedSplit K a g).coeff 1) * Polynomial.X
        + Polynomial.C ((markedSplit K a g).coeff 0) := by
  refine Polynomial.eq_X_add_C_of_degree_le_one ?_
  have hnd : (markedSplit K a g).natDegree = 1 := by
    rw [natDegree_markedSplit, h]
  calc (markedSplit K a g).degree ≤ ((markedSplit K a g).natDegree : WithBot ℕ) :=
        Polynomial.degree_le_natDegree
    _ = 1 := by rw [hnd]; rfl

/-- The leading coefficient of the split of a polynomial of degree one in the marked coordinate is
nonzero. -/
theorem markedSplit_coeff_one_ne_zero {g : MvPolynomial σ K}
    (h : MvPolynomial.degreeOf a g = 1) : (markedSplit K a g).coeff 1 ≠ 0 := by
  have hnd : (markedSplit K a g).natDegree = 1 := by
    rw [natDegree_markedSplit, h]
  have hne : markedSplit K a g ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hnd
    exact one_ne_zero hnd.symm
  have hlc := Polynomial.leadingCoeff_ne_zero.mpr hne
  rwa [Polynomial.leadingCoeff, hnd] at hlc

variable (F : Type*) [Field F] [Algebra (MvPolynomial {b : σ // b ≠ a} K) F]
  [IsFractionRing (MvPolynomial {b : σ // b ≠ a} K) F]

/-- **A hypersurface linear in a marked coordinate is birational to its base.**  If `g` is
irreducible and has degree one in the coordinate `a`, the residue ring of the divisor `g = 0`
embeds in the field of rational functions in the remaining coordinates, the embedding restricts to
the canonical map on those coordinates, and every rational function in them is a ratio of residues.

Consequently the residue field of the divisor is the rational function field of the base: the
residue degree is one. -/
theorem exists_injective_ringHom_quotient_span_of_degreeOf_eq_one
    {g : MvPolynomial σ K} (hirr : Irreducible g) (h : MvPolynomial.degreeOf a g = 1) :
    ∃ φ : (MvPolynomial σ K ⧸ Ideal.span {g}) →+* F,
      Function.Injective φ ∧
      (∀ s : MvPolynomial {b : σ // b ≠ a} K,
        φ (Ideal.Quotient.mk _ ((markedSplit K a).symm (Polynomial.C s)))
          = algebraMap (MvPolynomial {b : σ // b ≠ a} K) F s) ∧
      (∀ z : F, ∃ x y : MvPolynomial σ K ⧸ Ideal.span {g},
        φ y ≠ 0 ∧ z * φ y = φ x) := by
  classical
  set S := MvPolynomial {b : σ // b ≠ a} K with hS
  set P : Polynomial S := markedSplit K a g with hP
  set α : S := P.coeff 1 with hα
  set β : S := P.coeff 0 with hβ
  have hlin : P = Polynomial.C α * Polynomial.X + Polynomial.C β := markedSplit_eq_linear h
  have hαne : α ≠ 0 := markedSplit_coeff_one_ne_zero h
  have hirrP : Irreducible P := (MulEquiv.irreducible_iff (markedSplit K a)).mpr hirr
  have hndP : P.natDegree = 1 := by rw [hP, natDegree_markedSplit, h]
  have hprim : P.IsPrimitive := isPrimitive_of_irreducible hirrP (by rw [hndP]; norm_num)
  have hprim' : (Polynomial.C α * Polynomial.X + Polynomial.C β).IsPrimitive := hlin ▸ hprim
  -- the ideal transported across the split
  set J : Ideal (Polynomial S) :=
    Ideal.span {Polynomial.C α * Polynomial.X + Polynomial.C β} with hJdef
  have hJ : J = Ideal.map ((markedSplit K a).toRingEquiv : MvPolynomial σ K →+* Polynomial S)
      (Ideal.span {g}) := by
    rw [Ideal.map_span, Set.image_singleton, hJdef, ← hlin]
    rfl
  set eq := Ideal.quotientEquiv (Ideal.span {g}) J (markedSplit K a).toRingEquiv hJ with heq
  have hker : ∀ p ∈ J, ((Polynomial.aeval (linearRoot F α β) :
      Polynomial S →ₐ[S] F) : Polynomial S →+* F) p = 0 := by
    intro p hp
    rw [← RingHom.mem_ker, ker_aeval_linearRoot F hαne hprim']
    exact hp
  set lift := Ideal.Quotient.lift J
      ((Polynomial.aeval (linearRoot F α β) : Polynomial S →ₐ[S] F) : Polynomial S →+* F)
      hker with hlift
  have hliftinj : Function.Injective lift :=
    injective_quotient_lift_aeval_linearRoot F hαne hprim'
  refine ⟨lift.comp (eq : _ ≃+* _).toRingHom, hliftinj.comp eq.injective, ?_, ?_⟩
  · intro s
    have h1 : eq (Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C s)))
        = Ideal.Quotient.mk J (Polynomial.C s) := by
      rw [heq, Ideal.quotientEquiv_mk]
      congr 1
      exact (markedSplit K a).apply_symm_apply _
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, h1, hlift, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
      Polynomial.aeval_C]
    rfl
  · intro z
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := S) (K := F) z
    have hvne : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
    have hvF : algebraMap S F v ≠ 0 := by
      simpa using (IsFractionRing.to_map_eq_zero_iff (R := S) (K := F) (x := v)).not.mpr hvne
    refine ⟨Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C u)),
      Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C v)), ?_, ?_⟩
    · have h1 : eq (Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C v)))
          = Ideal.Quotient.mk J (Polynomial.C v) := by
        rw [heq, Ideal.quotientEquiv_mk]
        congr 1
        exact (markedSplit K a).apply_symm_apply _
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, h1, hlift, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
        Polynomial.aeval_C]
      exact hvF
    · have h1 : ∀ w : S,
          (lift.comp (eq : _ ≃+* _).toRingHom)
            (Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C w)))
            = algebraMap S F w := by
        intro w
        have h2 : eq (Ideal.Quotient.mk (Ideal.span {g}) ((markedSplit K a).symm (Polynomial.C w)))
            = Ideal.Quotient.mk J (Polynomial.C w) := by
          rw [heq, Ideal.quotientEquiv_mk]
          congr 1
          exact (markedSplit K a).apply_symm_apply _
        simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, h2, hlift, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
          Polynomial.aeval_C]
      rw [h1, h1, ← huv]
      field_simp

end Field

end

end GaloisForLFunctions.HTGeometry
