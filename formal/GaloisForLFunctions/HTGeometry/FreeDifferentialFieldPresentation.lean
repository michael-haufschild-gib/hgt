import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingCovariance
import GaloisForLFunctions.HTGeometry.JetHypertranscendence

/-!
# A singly and freely differentially generated field is the free differential rational field

If `y` generates a differential field `E` over a base field `F` of constants and the jets of `y`
are algebraically independent, then evaluation of jet polynomials at the jets of `y` is a
differential `F`-isomorphism from the free differential rational field `JetField F Unit` onto `E`.

The isomorphism is built from the evaluation `X_{(*,n)} ↦ y^{(n)}`, which is injective exactly by
differential independence and therefore extends to the fraction field.  Compatibility with the two
derivations is proved on the polynomial ring and propagated to fractions by the quotient rule, so
no derivation object is transported between the two presentations of the fraction field.

Consequently every nonconstant element of such a field is hypertranscendental over the base.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

open JetField

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Differential E] [Algebra F E]

/-! ### The jet derivation on the polynomial ring -/

/-- The derivation of the jet polynomial ring advancing every jet coordinate. -/
def jetDeriv (F ι : Type*) [Field F] : Derivation F (JetPoly F ι) (JetPoly F ι) :=
  MvPolynomial.mkDerivation F fun p : ι × ℕ => (MvPolynomial.X (p.1, p.2 + 1) : JetPoly F ι)

@[simp] theorem jetDeriv_X {ι : Type*} (p : ι × ℕ) :
    jetDeriv F ι (MvPolynomial.X p) = MvPolynomial.X (p.1, p.2 + 1) :=
  MvPolynomial.mkDerivation_X _ _ _

/-- The formal jet derivation of the free differential rational field restricts on the polynomial
ring to the coordinate advance. -/
theorem deriv_algebraMap_jetPoly {ι : Type*} (p : JetPoly F ι) :
    ((algebraMap (JetPoly F ι) (JetField F ι)) p)′ =
      algebraMap (JetPoly F ι) (JetField F ι) (jetDeriv F ι p) := by
  rw [deriv_eq, jetDerivation, fractionRingDerivation_algebraMap]
  rfl

/-! ### Evaluation at the jets of a differentially independent generator -/

variable (F) in
/-- Evaluation of a jet polynomial at the jets of an element. -/
def differentialJetEval (y : E) : JetPoly F Unit →ₐ[F] E :=
  MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 y

@[simp] theorem jetPolyEval_X (y : E) (p : Unit × ℕ) :
    differentialJetEval F y (MvPolynomial.X p) = differentialJet p.2 y := by
  simp [differentialJetEval]

@[simp] theorem jetPolyEval_C (y : E) (a : F) :
    differentialJetEval F y (MvPolynomial.C a) = algebraMap F E a := by
  simp [differentialJetEval]

/-- Differential independence of `y` is exactly injectivity of jet evaluation at `y`. -/
theorem jetPolyEval_injective {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    Function.Injective (differentialJetEval F y) := hy

/-- **Jet evaluation intertwines the coordinate advance with the derivation.** -/
theorem jetPolyEval_jetDeriv {y : E} (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (p : JetPoly F Unit) :
    differentialJetEval F y (jetDeriv F Unit p) = (differentialJetEval F y p)′ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [jetPolyEval_C, hF a]
    have hzero : jetDeriv F Unit (MvPolynomial.C a) = 0 := by
      simp
    rw [hzero, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p q hp =>
    have hleib := (jetDeriv F Unit).leibniz p (MvPolynomial.X q)
    have hmul := Differential.deriv.leibniz (differentialJetEval F y p)
      (differentialJetEval F y (MvPolynomial.X q))
    simp only [smul_eq_mul] at hleib hmul
    have hjet : (differentialJet q.2 y)′ = differentialJet (q.2 + 1) y :=
      (differentialJet_succ q.2 y).symm
    rw [hleib, map_add, map_mul, map_mul, map_mul, hmul, hp, jetDeriv_X, jetPolyEval_X,
      jetPolyEval_X]
    rw [hjet]

/-! ### The induced map on the free differential rational field -/

variable (F) in
/-- Evaluation at the jets of a differentially independent element, extended to the free
differential rational field. -/
def differentialJetFieldEval {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    JetField F Unit →ₐ[F] E :=
  IsFractionRing.liftAlgHom (A := JetPoly F Unit) (K := JetField F Unit)
    (jetPolyEval_injective hy)

@[simp] theorem jetFieldEval_algebraMap {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) (p : JetPoly F Unit) :
    differentialJetFieldEval F hy (algebraMap (JetPoly F Unit) (JetField F Unit) p) =
      differentialJetEval F y p := by
  rw [differentialJetFieldEval, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem jetFieldEval_injective {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    Function.Injective (differentialJetFieldEval F hy) :=
  (differentialJetFieldEval F hy).toRingHom.injective

/-- **The extended evaluation is a differential homomorphism.** -/
theorem jetFieldEval_deriv {y : E} (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) (x : JetField F Unit) :
    differentialJetFieldEval F hy (x′) = (differentialJetFieldEval F hy x)′ := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := JetPoly F Unit) x
  set A : JetField F Unit := algebraMap (JetPoly F Unit) (JetField F Unit) a with hA
  set B : JetField F Unit := algebraMap (JetPoly F Unit) (JetField F Unit) b with hB
  have hB0 : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hxB : x * B = A := by rw [← hx, div_mul_cancel₀ _ hB0]
  have hEA : differentialJetFieldEval F hy (A′) = (differentialJetFieldEval F hy A)′ := by
    rw [hA, deriv_algebraMap_jetPoly, jetFieldEval_algebraMap, jetFieldEval_algebraMap,
      jetPolyEval_jetDeriv hF]
  have hEB : differentialJetFieldEval F hy (B′) = (differentialJetFieldEval F hy B)′ := by
    rw [hB, deriv_algebraMap_jetPoly, jetFieldEval_algebraMap, jetFieldEval_algebraMap,
      jetPolyEval_jetDeriv hF]
  have hleib := Differential.deriv.leibniz x B
  simp only [smul_eq_mul] at hleib
  have hup : x * B′ + B * x′ = A′ := by rw [← hleib, hxB]
  have hEup : differentialJetFieldEval F hy x * (differentialJetFieldEval F hy B)′
      + differentialJetFieldEval F hy B * differentialJetFieldEval F hy (x′)
      = (differentialJetFieldEval F hy A)′ := by
    have := congrArg (differentialJetFieldEval F hy) hup
    rw [map_add, map_mul, map_mul, hEA, hEB] at this
    exact this
  have hleib' := Differential.deriv.leibniz (differentialJetFieldEval F hy x)
    (differentialJetFieldEval F hy B)
  simp only [smul_eq_mul] at hleib'
  have hdown : differentialJetFieldEval F hy x * (differentialJetFieldEval F hy B)′
      + differentialJetFieldEval F hy B * (differentialJetFieldEval F hy x)′
      = (differentialJetFieldEval F hy A)′ := by
    rw [← hleib', ← map_mul, hxB]
  have hEB0 : differentialJetFieldEval F hy B ≠ 0 := by
    intro h
    exact hB0 (jetFieldEval_injective hy (by rw [h, map_zero]))
  refine mul_left_cancel₀ hEB0 ?_
  have hcancel := hEup.trans hdown.symm
  exact add_left_cancel hcancel

/-! ### Surjectivity -/

/-- The image of the extended evaluation is derivation closed. -/
theorem derivationClosed_jetFieldEval_fieldRange {y : E}
    (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    DerivationClosed (differentialJetFieldEval F hy).fieldRange := by
  rintro z ⟨w, rfl⟩
  exact ⟨w′, jetFieldEval_deriv hF hy w⟩

/-- The generator is in the image. -/
theorem mem_jetFieldEval_fieldRange {y : E}
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y)) :
    y ∈ (differentialJetFieldEval F hy).fieldRange := by
  have hval : differentialJetFieldEval F hy
      (algebraMap (JetPoly F Unit) (JetField F Unit) (MvPolynomial.X ((), 0))) = y := by
    rw [jetFieldEval_algebraMap, jetPolyEval_X, differentialJet_zero]
  exact ⟨_, hval⟩

/-- **Evaluation at the jets of a free differential generator is onto.** -/
theorem jetFieldEval_surjective {y : E} (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤) :
    Function.Surjective (differentialJetFieldEval F hy) := by
  have hle : differentialAdjoin F ({y} : Set E) ≤ (differentialJetFieldEval F hy).fieldRange :=
    differentialAdjoin_le F (by simpa using mem_jetFieldEval_fieldRange hy)
      (derivationClosed_jetFieldEval_fieldRange hF hy)
  rw [hytop, top_le_iff] at hle
  intro u
  have hu : u ∈ (differentialJetFieldEval F hy).fieldRange := by rw [hle]; trivial
  exact hu

/-! ### Hypertranscendence of every nonconstant element -/

/-- **Every nonconstant element of a singly and freely differentially generated field is
hypertranscendental over the base.**  The base is a field of constants, the generator is
differentially independent, and its jets generate the whole field. -/
theorem hypertranscendentalOver_of_notMem_bot_of_free [CharZero F]
    (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {y : E} (hy : DifferentialIndependent F (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin F ({y} : Set E) = ⊤)
    {u : E} (hu : u ∉ (⊥ : IntermediateField F E)) :
    HypertranscendentalOver F u := by
  obtain ⟨x, rfl⟩ := jetFieldEval_surjective hF hy hytop u
  rw [hypertranscendentalOver_algHom_iff (differentialJetFieldEval F hy)
    (jetFieldEval_deriv hF hy) x]
  refine hypertranscendentalOver_of_notMem_bot ?_
  intro hx
  refine hu ?_
  rw [IntermediateField.mem_bot] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, by rw [← hc, AlgHom.commutes]⟩

end

end GaloisForLFunctions.HTGeometry
