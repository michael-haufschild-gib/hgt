import GaloisForLFunctions.HTGeometry.JetShiftTopCoefficient

/-!
# The weighted torus action on the free jet field

Scaling the jet coordinate of order `j` by `λ^j` is an automorphism of the free jet field, and it
interacts with the ambient derivation by a single factor:

`w_λ(δ v) = λ · δ(w_λ v)`.

The identity is checked on the polynomial ring, where both sides are computed on a monomial by the
Leibniz rule, and then transported through the quotient rule to the fraction field.

This is the grading that organizes the orbifold descent: every jet of the substituted value is
isobaric of its own order, so the equation a normalizing shift solves is isobaric.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C]

/-- The derivation of the jet polynomial ring advancing every coordinate. -/
def weightPolyDeriv : Derivation C (JetPoly C Unit) (JetPoly C Unit) :=
  MvPolynomial.mkDerivation C fun p : Unit × ℕ => (MvPolynomial.X (p.1, p.2 + 1) : JetPoly C Unit)

@[simp]
theorem weightPolyDeriv_X (p : Unit × ℕ) :
    weightPolyDeriv (MvPolynomial.X p : JetPoly C Unit)
      = MvPolynomial.X (p.1, p.2 + 1) := by
  rw [weightPolyDeriv, MvPolynomial.mkDerivation_X]

theorem jetDerivation_algebraMap (a : JetPoly C Unit) :
    JetField.jetDerivation (algebraMap (JetPoly C Unit) (JetField C Unit) a)
      = algebraMap (JetPoly C Unit) (JetField C Unit) (weightPolyDeriv a) := by
  rw [JetField.jetDerivation, fractionRingDerivation_algebraMap]
  rfl

/-! ## The scaling automorphism -/

/-- Scale the jet coordinate of order `j` by `λ^j`, on the polynomial ring. -/
def weightScaleAlgHom (lam : C) :
    JetPoly C Unit →ₐ[C] JetPoly C Unit :=
  MvPolynomial.aeval fun p : Unit × ℕ => MvPolynomial.C (lam ^ p.2) * MvPolynomial.X p

@[simp]
theorem weightScaleAlgHom_X (lam : C) (p : Unit × ℕ) :
    weightScaleAlgHom lam (MvPolynomial.X p : JetPoly C Unit)
      = MvPolynomial.C (lam ^ p.2) * MvPolynomial.X p := by
  simp [weightScaleAlgHom]

@[simp]
theorem weightScaleAlgHom_C (lam c : C) :
    weightScaleAlgHom lam (MvPolynomial.C c : JetPoly C Unit) = MvPolynomial.C c := by
  simp [weightScaleAlgHom]

/-- The scaling is an automorphism of the polynomial ring. -/
def weightScaleAlgEquiv {lam : C} (h : lam ≠ 0) :
    JetPoly C Unit ≃ₐ[C] JetPoly C Unit :=
  AlgEquiv.ofAlgHom (weightScaleAlgHom lam) (weightScaleAlgHom lam⁻¹)
    (by
      refine MvPolynomial.algHom_ext fun p => ?_
      show weightScaleAlgHom lam (weightScaleAlgHom lam⁻¹ (MvPolynomial.X p))
        = MvPolynomial.X p
      rw [weightScaleAlgHom_X, map_mul, weightScaleAlgHom_C, weightScaleAlgHom_X, ← mul_assoc,
        ← map_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ h), map_one, one_mul])
    (by
      refine MvPolynomial.algHom_ext fun p => ?_
      show weightScaleAlgHom lam⁻¹ (weightScaleAlgHom lam (MvPolynomial.X p))
        = MvPolynomial.X p
      rw [weightScaleAlgHom_X, map_mul, weightScaleAlgHom_C, weightScaleAlgHom_X, ← mul_assoc,
        ← map_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ h), map_one, one_mul])

@[simp]
theorem weightScaleAlgEquiv_X {lam : C} (h : lam ≠ 0) (p : Unit × ℕ) :
    weightScaleAlgEquiv h (MvPolynomial.X p : JetPoly C Unit)
      = MvPolynomial.C (lam ^ p.2) * MvPolynomial.X p :=
  weightScaleAlgHom_X lam p

/-- **The scaling automorphism of the free jet field.** -/
def weightScale {lam : C} (h : lam ≠ 0) : JetField C Unit ≃ₐ[C] JetField C Unit :=
  IsFractionRing.fieldEquivOfAlgEquiv C (JetField C Unit) (JetField C Unit)
    (weightScaleAlgEquiv h)

theorem weightScale_algebraMap {lam : C} (h : lam ≠ 0) (a : JetPoly C Unit) :
    weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a)
      = algebraMap (JetPoly C Unit) (JetField C Unit) (weightScaleAlgEquiv h a) :=
  IsFractionRing.fieldEquivOfAlgEquiv_algebraMap C (JetField C Unit) (JetField C Unit)
    (weightScaleAlgEquiv h) a

@[simp]
theorem weightScale_jet {lam : C} (h : lam ≠ 0) (p : Unit × ℕ) :
    weightScale h (JetField.jet p : JetField C Unit)
      = algebraMap C (JetField C Unit) (lam ^ p.2) * JetField.jet p := by
  rw [JetField.jet, weightScale_algebraMap, weightScaleAlgEquiv_X, map_mul]
  rfl

/-! ## The interaction with the ambient derivation -/

theorem weightScaleAlgEquiv_weightPolyDeriv {lam : C} (h : lam ≠ 0) (a : JetPoly C Unit) :
    weightScaleAlgEquiv h (weightPolyDeriv a)
      = MvPolynomial.C lam * weightPolyDeriv (weightScaleAlgEquiv h a) := by
  induction a using MvPolynomial.induction_on with
  | C c =>
      have h1 : weightPolyDeriv (MvPolynomial.C c : JetPoly C Unit) = 0 :=
        Derivation.map_algebraMap _ c
      have h2 : weightScaleAlgEquiv h (MvPolynomial.C c : JetPoly C Unit) = MvPolynomial.C c :=
        weightScaleAlgHom_C lam c
      rw [h1, h2, map_zero, h1, mul_zero]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
      ring
  | mul_X p n hp =>
      have hleib := weightPolyDeriv.leibniz p (MvPolynomial.X n)
      simp only [smul_eq_mul] at hleib
      have hCd : weightPolyDeriv (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n
          : JetPoly C Unit)
          = MvPolynomial.C (lam ^ n.2) * MvPolynomial.X (n.1, n.2 + 1) := by
        have hl := weightPolyDeriv.leibniz
          (MvPolynomial.C (lam ^ n.2) : JetPoly C Unit) (MvPolynomial.X n)
        simp only [smul_eq_mul] at hl
        have hC0 : weightPolyDeriv (MvPolynomial.C (lam ^ n.2) : JetPoly C Unit) = 0 := by
          simp [weightPolyDeriv]
        rw [hl, weightPolyDeriv_X, hC0, mul_zero, add_zero]
      have hleib2 := weightPolyDeriv.leibniz (weightScaleAlgEquiv h p)
        (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n)
      simp only [smul_eq_mul] at hleib2
      have hpow : (MvPolynomial.C (lam ^ (n.2 + 1)) : JetPoly C Unit)
          = MvPolynomial.C lam * MvPolynomial.C (lam ^ n.2) := by
        rw [← map_mul, pow_succ]
        ring_nf
      have hLHS : weightScaleAlgEquiv h (weightPolyDeriv (p * MvPolynomial.X n))
          = weightScaleAlgEquiv h p
              * (MvPolynomial.C (lam ^ (n.2 + 1)) * MvPolynomial.X (n.1, n.2 + 1))
            + MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n
              * (MvPolynomial.C lam * weightPolyDeriv (weightScaleAlgEquiv h p)) := by
        rw [hleib, weightPolyDeriv_X, map_add, map_mul, map_mul, weightScaleAlgEquiv_X,
          weightScaleAlgEquiv_X, hp]
      have hRHS : MvPolynomial.C lam
            * weightPolyDeriv (weightScaleAlgEquiv h (p * MvPolynomial.X n))
          = MvPolynomial.C lam * (weightScaleAlgEquiv h p
              * (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X (n.1, n.2 + 1))
            + MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n
              * weightPolyDeriv (weightScaleAlgEquiv h p)) := by
        rw [map_mul, weightScaleAlgEquiv_X, hleib2, hCd]
      rw [hLHS, hRHS, hpow]
      ring

/-- **The scaling twists the ambient derivation by a single factor.** -/
theorem weightScale_jetDerivation {lam : C} (h : lam ≠ 0) (v : JetField C Unit) :
    weightScale h (JetField.jetDerivation v)
      = algebraMap C (JetField C Unit) lam * JetField.jetDerivation (weightScale h v) := by
  have hquot : ∀ x y : JetField C Unit, y ≠ 0 →
      JetField.jetDerivation (x / y)
        = (JetField.jetDerivation x * y - x * JetField.jetDerivation y) / y ^ 2 := by
    intro x y hy
    have hl := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz (x / y) y
    simp only [smul_eq_mul] at hl
    rw [div_mul_cancel₀ x hy] at hl
    have h3 : JetField.jetDerivation (x / y)
        = (JetField.jetDerivation x - (x / y) * JetField.jetDerivation y) / y := by
      rw [eq_div_iff hy, hl]
      ring
    rw [h3]
    field_simp
  have hpoly : ∀ a : JetPoly C Unit,
      weightScale h (JetField.jetDerivation
          (algebraMap (JetPoly C Unit) (JetField C Unit) a))
        = algebraMap C (JetField C Unit) lam
          * JetField.jetDerivation (weightScale h
            (algebraMap (JetPoly C Unit) (JetField C Unit) a)) := by
    intro a
    rw [jetDerivation_algebraMap, weightScale_algebraMap, weightScale_algebraMap,
      jetDerivation_algebraMap, weightScaleAlgEquiv_weightPolyDeriv, map_mul]
    rfl
  obtain ⟨a, b, hbmem, hab⟩ := IsFractionRing.div_surjective (A := JetPoly C Unit) v
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbne : algebraMap (JetPoly C Unit) (JetField C Unit) b ≠ 0 := fun hh =>
    hb ((IsFractionRing.injective (JetPoly C Unit) (JetField C Unit)) (by rw [hh, map_zero]))
  have hwb : weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b) ≠ 0 := by
    intro hh
    refine hbne ?_
    have := (weightScale h).injective
      (a₁ := algebraMap (JetPoly C Unit) (JetField C Unit) b) (a₂ := 0) (by rw [hh, map_zero])
    exact this
  have hLHS : weightScale h (JetField.jetDerivation
      (algebraMap (JetPoly C Unit) (JetField C Unit) a
        / algebraMap (JetPoly C Unit) (JetField C Unit) b))
      = (weightScale h (JetField.jetDerivation
            (algebraMap (JetPoly C Unit) (JetField C Unit) a))
          * weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)
        - weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a)
          * weightScale h (JetField.jetDerivation
            (algebraMap (JetPoly C Unit) (JetField C Unit) b)))
        / (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)) ^ 2 := by
    rw [hquot _ _ hbne, map_div₀, map_sub, map_mul, map_mul, map_pow]
  have hRHS : JetField.jetDerivation (weightScale h
      (algebraMap (JetPoly C Unit) (JetField C Unit) a
        / algebraMap (JetPoly C Unit) (JetField C Unit) b))
      = (JetField.jetDerivation (weightScale h
            (algebraMap (JetPoly C Unit) (JetField C Unit) a))
          * weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)
        - weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a)
          * JetField.jetDerivation (weightScale h
            (algebraMap (JetPoly C Unit) (JetField C Unit) b)))
        / (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)) ^ 2 := by
    rw [map_div₀]
    exact hquot _ _ hwb
  rw [← hab, hLHS, hRHS, hpoly a, hpoly b]
  field_simp

/-! ## Extensionality on the jet coordinates -/

/-- Two algebra endomorphisms of the free jet field agreeing on the jet coordinates are equal. -/
theorem algHom_ext_jet {f g : JetField C Unit →ₐ[C] JetField C Unit}
    (h : ∀ p : Unit × ℕ, f (JetField.jet p) = g (JetField.jet p)) (v : JetField C Unit) :
    f v = g v := by
  have hpoly : ∀ a : JetPoly C Unit,
      f (algebraMap (JetPoly C Unit) (JetField C Unit) a)
        = g (algebraMap (JetPoly C Unit) (JetField C Unit) a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
        have hc : algebraMap (JetPoly C Unit) (JetField C Unit) (MvPolynomial.C c)
            = algebraMap C (JetField C Unit) c :=
          (IsScalarTower.algebraMap_apply C (JetPoly C Unit) (JetField C Unit) c).symm
        rw [hc, AlgHom.commutes, AlgHom.commutes]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp =>
        have hX : algebraMap (JetPoly C Unit) (JetField C Unit) (MvPolynomial.X n)
            = JetField.jet n := rfl
        rw [map_mul, map_mul, hp, hX, h n]
        exact (map_mul g _ _).symm
  obtain ⟨a, b, hbmem, hab⟩ := IsFractionRing.div_surjective (A := JetPoly C Unit) v
  rw [← hab, map_div₀, map_div₀, hpoly a, hpoly b]

/-! ## Isobarity of the substituted jets -/

variable {R : RatFunc C}

theorem weightScale_jet_zero {lam : C} (h : lam ≠ 0) :
    (weightScale h).toAlgHom (JetField.jet ((), 0) : JetField C Unit)
      = (JetField.jet ((), 0) : JetField C Unit) := by
  show weightScale h (JetField.jet ((), 0) : JetField C Unit) = _
  rw [weightScale_jet]
  simp

theorem weightScale_ratFuncEval {lam : C} (h : lam ≠ 0) (Q : RatFunc C) :
    weightScale h (ratFuncEval (JetField.jet ((), 0) : JetField C Unit)
        transcendental_freeGen Q)
      = ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen Q := by
  show (weightScale h).toAlgHom (ratFuncEval (JetField.jet ((), 0) : JetField C Unit)
      transcendental_freeGen Q) = _
  rw [← ratFuncEval_algHom (weightScale h).toAlgHom transcendental_freeGen Q]
  exact ratFuncEval_congr _ _ (weightScale_jet_zero h) Q

theorem weightScale_substitutionValue {lam : C} (h : lam ≠ 0) (R : RatFunc C) :
    weightScale h (substitutionValue R) = substitutionValue R :=
  weightScale_ratFuncEval h R

theorem weightScale_substitutionDeriv [CharZero C] {lam : C} (h : lam ≠ 0) (R : RatFunc C) :
    weightScale h (substitutionDeriv R) = substitutionDeriv R := by
  rw [← ratFuncEval_ratFuncDeriv R]
  exact weightScale_ratFuncEval h (ratFuncDeriv R)

/-- **Every jet of the substituted value is isobaric of its own order.** -/
theorem weightScale_substitutionJet {lam : C} (h : lam ≠ 0) (R : RatFunc C) : ∀ l : ℕ,
    weightScale h (substitutionJet R l)
      = algebraMap C (JetField C Unit) (lam ^ l) * substitutionJet R l := by
  intro l
  induction l with
  | zero =>
      rw [substitutionJet, differentialJet_zero, weightScale_substitutionValue, pow_zero,
        map_one, one_mul]
  | succ l ih =>
      have hstep : substitutionJet R (l + 1)
          = JetField.jetDerivation (substitutionJet R l) := by
        rw [substitutionJet, substitutionJet, differentialJet_succ, JetField.deriv_eq]
      have hconst : JetField.jetDerivation (algebraMap C (JetField C Unit) (lam ^ l)
            * substitutionJet R l)
          = algebraMap C (JetField C Unit) (lam ^ l)
            * JetField.jetDerivation (substitutionJet R l) := by
        have hl := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
          (algebraMap C (JetField C Unit) (lam ^ l)) (substitutionJet R l)
        simp only [smul_eq_mul] at hl
        rw [hl, Derivation.map_algebraMap, mul_zero, add_zero]
      rw [hstep, weightScale_jetDerivation, ih, hconst, ← mul_assoc, ← map_mul, ← pow_succ']

/-- **The shift term is isobaric of its level.** -/
theorem weightScale_substitutionShift {lam : C} (h : lam ≠ 0) (R : RatFunc C) [CharZero C]
    (M : ℕ) :
    weightScale h (substitutionShift R M)
      = algebraMap C (JetField C Unit) (lam ^ M) * substitutionShift R M := by
  have hdef : substitutionShift R M
      = substitutionJet R M - substitutionDeriv R * (JetField.jet ((), M) : JetField C Unit) :=
    rfl
  rw [hdef, map_sub, map_mul, weightScale_substitutionJet, weightScale_substitutionDeriv,
    weightScale_jet]
  ring

/-- **The scaling commutes with the substitution endomorphism.** -/
theorem weightScale_jetSubstitution [CharZero C] {lam : C} (h : lam ≠ 0) (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (v : JetField C Unit) :
    weightScale h (jetSubstitution R hR v) = jetSubstitution R hR (weightScale h v) := by
  refine algHom_ext_jet (f := (weightScale h).toAlgHom.comp (jetSubstitution R hR))
    (g := (jetSubstitution R hR).comp (weightScale h).toAlgHom) (fun p => ?_) v
  show weightScale h (jetSubstitution R hR (JetField.jet p))
    = jetSubstitution R hR (weightScale h (JetField.jet p))
  rw [jetSubstitution_jet, weightScale_jet, map_mul, jetSubstitution_jet,
    weightScale_substitutionJet]
  congr 1
  exact (AlgHom.commutes _ _).symm

/-! ## The action preserves the prefix fields -/

theorem weightScale_mem_jetPrefixField [CharZero C] {lam : C} (h : lam ≠ 0) (M : ℕ)
    {v : JetField C Unit} (hv : v ∈ jetPrefixField C M) :
    weightScale h v ∈ jetPrefixField C M := by
  have hle : jetPrefixField C M
      ≤ IntermediateField.comap (weightScale h).toAlgHom (jetPrefixField C M) := by
    rw [jetPrefixField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨u, j⟩, hj, rfl⟩
    show weightScale h (JetField.jet (u, j)) ∈ jetPrefixField C M
    rw [weightScale_jet]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (jet_mem_jetPrefixField hj)
  exact hle hv

end

end GaloisForLFunctions.HTGeometry
