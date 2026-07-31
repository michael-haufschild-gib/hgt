import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# The common kernel of all coordinate derivations is the constants

A rational function of free coordinates all of whose partial derivatives vanish is a constant.

The proof needs no factorisation.  Take a denominator of least total degree.  Differentiating the
denominator relation shows that the derivative of the denominator is again a denominator, of
strictly smaller degree unless it vanishes; so the denominator has vanishing derivatives, hence in
characteristic zero no variables, and then the numerator has vanishing derivatives too.

This is the endpoint of every argument that annihilation by a large enough family of currents
forces constancy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {C σ : Type*} [Field C]

/-- A polynomial with no variables is a constant. -/
theorem exists_C_of_vars_eq_empty {p : MvPolynomial σ C} (h : p.vars = ∅) :
    ∃ c : C, p = MvPolynomial.C c := by
  have hmem := MvPolynomial.mem_supported (R := C) (s := (∅ : Set σ)) (p := p)
  rw [MvPolynomial.supported_empty] at hmem
  have hp : p ∈ (⊥ : Subalgebra C (MvPolynomial σ C)) := hmem.2 (by rw [h]; simp)
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hp
  exact ⟨c, by rw [← hc]; rfl⟩

/-- A polynomial all of whose partial derivatives vanish is a constant. -/
theorem exists_C_of_forall_pderiv_eq_zero [CharZero C] {p : MvPolynomial σ C}
    (h : ∀ i, MvPolynomial.pderiv i p = 0) : ∃ c : C, p = MvPolynomial.C c :=
  exists_C_of_vars_eq_empty
    (Finset.eq_empty_iff_forall_notMem.2 fun i hi =>
      mvPolynomial_pderiv_ne_zero_of_mem_vars hi (h i))

/-- Every element of the free rational coordinate field has a polynomial denominator. -/
theorem exists_denominator (f : FreeCoordinateRationalField C σ) :
    ∃ B A : MvPolynomial σ C, B ≠ 0 ∧
      algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ) A =
        algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ) B * f := by
  obtain ⟨A, B, hB, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ C) f
  have hB0 : B ≠ 0 := nonZeroDivisors.ne_zero hB
  have hBne : algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ) B ≠ 0 := fun hcon =>
    hB0 ((map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial σ C)
      (FreeCoordinateRationalField C σ))).1 hcon)
  refine ⟨B, A, hB0, ?_⟩
  field_simp

/-- **The constant-kernel theorem.**  In characteristic zero a rational function of free
coordinates whose every partial derivative vanishes is a constant. -/
theorem exists_algebraMap_of_forall_freeCoordinateDerivation_eq_zero [CharZero C]
    {f : FreeCoordinateRationalField C σ}
    (hf : ∀ i, freeCoordinateDerivation C σ i f = 0) :
    ∃ c : C, f = algebraMap C (FreeCoordinateRationalField C σ) c := by
  classical
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ)) :=
    IsFractionRing.injective _ _
  have hex : ∃ d : ℕ, ∃ B A : MvPolynomial σ C, B ≠ 0 ∧
      algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ) A =
        algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ) B * f ∧
      B.totalDegree = d := by
    obtain ⟨B, A, hB, hBA⟩ := exists_denominator f
    exact ⟨B.totalDegree, B, A, hB, hBA, rfl⟩
  obtain ⟨B, A, hB0, hBA, hBd⟩ := Nat.find_spec hex
  -- differentiating the denominator relation
  have hstep : ∀ i : σ,
      algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ)
          (MvPolynomial.pderiv i A) =
        algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ)
          (MvPolynomial.pderiv i B) * f := by
    intro i
    have h := congrArg (freeCoordinateDerivation C σ i) hBA
    rw [freeCoordinateDerivation_algebraMap, Derivation.leibniz,
      freeCoordinateDerivation_algebraMap, hf i, smul_zero, zero_add, smul_eq_mul] at h
    rw [h, mul_comm]
  -- the denominator has vanishing derivatives
  have hBpd : ∀ i : σ, MvPolynomial.pderiv i B = 0 := by
    intro i
    by_contra hne
    refine Nat.find_min hex (m := (MvPolynomial.pderiv i B).totalDegree) ?_
      ⟨MvPolynomial.pderiv i B, MvPolynomial.pderiv i A, hne, hstep i, rfl⟩
    rw [← hBd]
    exact GaloisForLFunctions.totalDegree_pderiv_lt B i hne
  -- hence so does the numerator
  have hApd : ∀ i : σ, MvPolynomial.pderiv i A = 0 := by
    intro i
    refine hinj ?_
    rw [map_zero, hstep i, hBpd i, map_zero, zero_mul]
  obtain ⟨b, rfl⟩ := exists_C_of_forall_pderiv_eq_zero hBpd
  obtain ⟨a, rfl⟩ := exists_C_of_forall_pderiv_eq_zero hApd
  have hbne : (b : C) ≠ 0 := by
    intro hcon
    exact hB0 (by rw [hcon, map_zero])
  refine ⟨a / b, ?_⟩
  have hCa : algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ)
      (MvPolynomial.C a) = algebraMap C (FreeCoordinateRationalField C σ) a := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have hCb : algebraMap (MvPolynomial σ C) (FreeCoordinateRationalField C σ)
      (MvPolynomial.C b) = algebraMap C (FreeCoordinateRationalField C σ) b := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [hCa, hCb] at hBA
  have hbF : algebraMap C (FreeCoordinateRationalField C σ) b ≠ 0 := fun hcon =>
    hbne ((map_eq_zero_iff _ (algebraMap C (FreeCoordinateRationalField C σ)).injective).1 hcon)
  rw [map_div₀, eq_div_iff hbF, mul_comm]
  exact hBA.symm

/-- The common kernel of all coordinate derivations is the constant subfield. -/
theorem freeCoordinateCommonKernelField_empty [CharZero C] :
    freeCoordinateCommonKernelField C σ (∅ : Set σ) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  obtain ⟨c, rfl⟩ := exists_algebraMap_of_forall_freeCoordinateDerivation_eq_zero
    fun i => hf i (Set.notMem_empty i)
  exact IntermediateField.mem_bot.2 ⟨c, rfl⟩

end

end GaloisForLFunctions.HTGeometry
