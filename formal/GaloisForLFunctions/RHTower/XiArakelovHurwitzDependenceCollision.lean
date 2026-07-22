import GaloisForLFunctions.RHTower.XiArakelovHurwitzAlgebraicityCollision
import GaloisForLFunctions.Hurwitz.IntegerTranslationDifferentialMatroid

/-!
# Hurwitz value relations feed the Arakelov algebraicity collision

For two nonintegral exponents, the intrinsic continued-Hurwitz differential matroid says that the
two functions are differentially dependent exactly when their monodromy characters agree.

Consequently, differential dependence of the Xi-indexed Hurwitz function with any nonintegral
anchor carrying an algebraic monodromy character transfers algebraicity to the Xi character.  If
the same hypothetical right-half Xi zero has algebraic Arakelov coordinate, the already formalized
Arakelov--Hurwitz Gelfond--Schneider collision forces RH.

The anchor may vary with the divisor point and need not lie on the critical line.  This module thus
isolates an actual function-value relation as a producer for one arithmetic input, rather than
assuming the Xi character algebraic without a mechanism.
-/

open Complex Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- The two-exponent family used by the intrinsic continued-Hurwitz differential matroid. -/
def continuedHurwitzPairExponent (s t : ℂ) : Bool → ℂ :=
  fun b => if b then t else s

/-- A genuine algebraic differential relation between the two analytically continued Hurwitz
functions in the shift variable. -/
def ContinuedHurwitzPairDifferentiallyDependent (s t : ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  ¬ DifferentialIndependent (RatFunc ℂ)
    (fun b : Bool => continuedHzetaUpperEndMero (continuedHurwitzPairExponent s t b))

/-- Differential dependence of two nonintegral continued-Hurwitz functions forces equality of
their monodromy characters. -/
theorem monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent
    {s t : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (ht : ∀ m : ℤ, t ≠ (m : ℂ))
    (hdep : ContinuedHurwitzPairDifferentiallyDependent s t) :
    monoScalar s = monoScalar t := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  by_contra hne
  apply hdep
  apply (continued_hurwitz_intrinsic_residue_differentialMatroid_law
    (continuedHurwitzPairExponent s t) ?_).mpr
  · intro b₁ b₂ hq
    cases b₁ <;> cases b₂ <;> simp_all [continuedHurwitzPairExponent]
  · intro b m
    cases b <;> simp [continuedHurwitzPairExponent, hs, ht]

/-- Exact two-point value law: continued-Hurwitz differential dependence is equality of the two
monodromy-character values. -/
theorem continuedHurwitzPairDifferentiallyDependent_iff_monoScalar_eq
    {s t : ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (ht : ∀ m : ℤ, t ≠ (m : ℂ)) :
    ContinuedHurwitzPairDifferentiallyDependent s t ↔
      monoScalar s = monoScalar t := by
  constructor
  · exact monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent hs ht
  · intro hq
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
    letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    intro hDI
    have hinj := (continued_hurwitz_intrinsic_residue_differentialMatroid_law
      (continuedHurwitzPairExponent s t) (by
        intro b m
        cases b <;> simp [continuedHurwitzPairExponent, hs, ht])).mp hDI
    have hfalseTrue : (false : Bool) = true := by
      apply hinj
      simpa [continuedHurwitzPairExponent] using hq
    simp at hfalseTrue

/-! ## Rank-two functional-equation character -/

/-- Trace of the determinant-one rank-two character obtained by pairing a Hurwitz monodromy
eigencharacter with its inverse. -/
def hurwitzFECharacterTrace (s : ℂ) : ℂ :=
  monoScalar s + (monoScalar s)⁻¹

/-- Determinant of the same paired character. -/
def hurwitzFECharacterDet (s : ℂ) : ℂ :=
  monoScalar s * (monoScalar s)⁻¹

/-- The paired character has determinant one at every exponent. -/
theorem hurwitzFECharacterDet_eq_one (s : ℂ) :
    hurwitzFECharacterDet s = 1 := by
  rw [hurwitzFECharacterDet, mul_inv_cancel₀]
  dsimp [monoScalar]
  exact Complex.exp_ne_zero _

/-- Algebraicity of the determinant-one rank-two trace already forces algebraicity of each
monodromy eigencharacter.  The converse follows by closure of algebraic numbers under inversion
and addition. -/
theorem hurwitzFECharacterTrace_isAlgebraic_iff_monoScalar_isAlgebraic (s : ℂ) :
    IsAlgebraic ℚ (hurwitzFECharacterTrace s) ↔
      IsAlgebraic ℚ (monoScalar s) := by
  constructor
  · intro htrace
    let q : ℂ := monoScalar s
    let T : ℂ := q + q⁻¹
    have hq0 : q ≠ 0 := by
      dsimp [q, monoScalar]
      exact Complex.exp_ne_zero _
    change IsAlgebraic ℚ T at htrace
    have hfour : IsAlgebraic ℚ (4 : ℂ) := by
      simpa using
        (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (4 : ℚ))).isAlgebraic
    have hdisc : IsAlgebraic ℚ (T ^ 2 - 4) := htrace.pow 2 |>.sub hfour
    have hid : (2 * q - T) ^ 2 = T ^ 2 - 4 := by
      dsimp [T]
      field_simp [hq0]
      ring
    have hrpow : IsAlgebraic ℚ ((2 * q - T) ^ 2) := by
      rw [hid]
      exact hdisc
    have hr : IsAlgebraic ℚ (2 * q - T) :=
      IsAlgebraic.of_pow (by norm_num) hrpow
    have hhalf : IsAlgebraic ℚ (1 / 2 : ℂ) := by
      simpa using
        (isIntegral_algebraMap : IsIntegral ℚ
          (algebraMap ℚ ℂ (1 / 2 : ℚ))).isAlgebraic
    have hqeq : q = ((2 * q - T) + T) * (1 / 2 : ℂ) := by ring
    change IsAlgebraic ℚ q
    rw [hqeq]
    exact (hr.add htrace).mul hhalf
  · intro hq
    exact hq.add hq.inv

/-- Positive obstruction: at a nonreal algebraic Arakelov coordinate, even the unlabelled
determinant-one rank-two trace is transcendental. -/
theorem hurwitzFECharacterTrace_transcendental_of_arakelovW_algebraic_of_im_ne_zero
    {s : ℂ} (hw : IsAlgebraic ℚ (arakelovW s)) (him : s.im ≠ 0) :
    Transcendental ℚ (hurwitzFECharacterTrace s) := by
  intro htrace
  exact monoScalar_transcendental_of_arakelovW_algebraic_of_im_ne_zero hw him
    ((hurwitzFECharacterTrace_isAlgebraic_iff_monoScalar_isAlgebraic s).mp htrace)

/-- Source-value hypothesis: every hypothetical right-half Xi zero has algebraic Arakelov
coordinate and its continued-Hurwitz function is differentially dependent with some nonintegral
anchor whose monodromy character is algebraic. -/
def XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      ∃ tau : ℂ,
        (∀ m : ℤ, tau ≠ (m : ℂ)) ∧
        IsAlgebraic ℚ (monoScalar tau) ∧
        ContinuedHurwitzPairDifferentiallyDependent (rho : ℂ) tau

/-- The Hurwitz value relation transfers the anchor's algebraic character to the Xi divisor
point, discharging the character-algebraicity input of the arithmetic collision. -/
theorem xiRightArakelovHurwitzAlgebraic_of_dependentOnAlgebraicCharacter
    (h : XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter) :
    XiRightArakelovHurwitzAlgebraic := by
  intro rho hrho
  obtain ⟨hw, tau, htau, hqtau, hdep⟩ := h rho hrho
  refine ⟨hw, ?_⟩
  have hqrho : monoScalar (rho : ℂ) = monoScalar tau :=
    monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent
      (fun m => openCriticalStrip_point_ne_int
        (xi_divisor_support_re_mem_open_unit rho) m)
      htau hdep
  rw [xiHurwitzMonodromyCharacter, hqrho]
  exact hqtau

/-- **Value-relation chain to RH.** Algebraic Arakelov coordinates plus differential dependence
with algebraic-character Hurwitz anchors force RH. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter
    (h : XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic
    (xiRightArakelovHurwitzAlgebraic_of_dependentOnAlgebraicCharacter h)

/-- Under RH the right-half source predicate holds vacuously: divisor support contains no point in
`Re s > 1/2`.  This identifies the predicate as an RH certificate, not a source construction. -/
theorem xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter := by
  intro rho hrho
  exact False.elim ((rh_iff_xi_ne_zero_right.mp hRH)
    (rho : ℂ) (mem_rightHalf.mpr hrho)
    (xi_eq_zero_of_mem_divisor_support rho))

/-- **Exact classification of the algebraic-character dependence interface.**  Its forward
direction is the Arakelov--Hurwitz transcendence collision; its reverse direction is right-half
vacuity under RH. -/
theorem xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_iff_riemannHypothesis :
    XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter,
    xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_of_riemannHypothesis⟩

/-- Rank-two trace version of the source-value hypothesis.  This asks a source object to expose an
algebraic characteristic-polynomial coefficient, rather than a chosen monodromy eigenvalue. -/
def XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      ∃ tau : ℂ,
        (∀ m : ℤ, tau ≠ (m : ℂ)) ∧
        IsAlgebraic ℚ (hurwitzFECharacterTrace tau) ∧
        ContinuedHurwitzPairDifferentiallyDependent (rho : ℂ) tau

/-- The determinant-one trace hypothesis is exactly the original algebraic-eigencharacter
hypothesis. -/
theorem xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_character :
    XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace ↔
      XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter := by
  constructor
  · intro h rho hrho
    obtain ⟨hw, tau, htau, htrace, hdep⟩ := h rho hrho
    exact ⟨hw, tau, htau,
      (hurwitzFECharacterTrace_isAlgebraic_iff_monoScalar_isAlgebraic tau).mp htrace,
      hdep⟩
  · intro h rho hrho
    obtain ⟨hw, tau, htau, hq, hdep⟩ := h rho hrho
    exact ⟨hw, tau, htau,
      (hurwitzFECharacterTrace_isAlgebraic_iff_monoScalar_isAlgebraic tau).mpr hq,
      hdep⟩

/-- Rank-two algebraic-character trace chain to RH. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace
    (h : XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter
    (xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_character.mp h)

/-- Exact classification of the determinant-one rank-two trace interface. -/
theorem xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_riemannHypothesis :
    XiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace ↔ RiemannHypothesis := by
  rw [xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicFETrace_iff_character,
    xiRightArakelovAlgebraicHurwitzDependentOnAlgebraicCharacter_iff_riemannHypothesis]

/-- Add one exponent to a finite Hurwitz anchor family. -/
def continuedHurwitzAugmentedExponent {I : Type*}
    (s : ℂ) (anchor : I → ℂ) : Option I → ℂ
  | none => s
  | some i => anchor i

/-- The Hurwitz function at `s` lies in the differential-matroid closure of an anchor
family when adjoining it destroys differential independence. -/
def ContinuedHurwitzDifferentiallyDependentOverAnchors
    {I : Type*}
    (s : ℂ) (anchor : I → ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  ¬ DifferentialIndependent (RatFunc ℂ)
    (fun o : Option I =>
      continuedHzetaUpperEndMero (continuedHurwitzAugmentedExponent s anchor o))

/-- If a nonintegral Hurwitz exponent lies in the differential-matroid closure of a finite
monodromy-separated anchor family, its character equals one of the anchor characters. -/
theorem exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (hdep : ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor) :
    ∃ i, monoScalar s = monoScalar (anchor i) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  by_contra hnone
  simp only [not_exists] at hnone
  apply hdep
  apply (continued_hurwitz_intrinsic_residue_differentialMatroid_law
    (continuedHurwitzAugmentedExponent s anchor) ?_).mpr
  · intro o₁ o₂ heq
    cases o₁ with
    | none =>
        cases o₂ with
        | none => rfl
        | some j => exact (hnone j heq).elim
    | some i =>
        cases o₂ with
        | none => exact (hnone i heq.symm).elim
        | some j => exact congrArg some (hinj heq)
  · intro o m
    cases o with
    | none => exact hs m
    | some i => exact hanchor i m

/-- Exact finite-closure classification: over a nonintegral monodromy-separated anchor family,
adjoining one continued-Hurwitz exponent destroys differential independence exactly when its
monodromy character repeats an anchor character. -/
theorem continuedHurwitzDifferentiallyDependentOverAnchors_iff_exists_monoScalar_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i))) :
    ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor ↔
      ∃ i, monoScalar s = monoScalar (anchor i) := by
  constructor
  · exact exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors
      hs hanchor hinj
  · rintro ⟨i, hi⟩ hDI
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
    letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    have hAugInj := (continued_hurwitz_intrinsic_residue_differentialMatroid_law
      (continuedHurwitzAugmentedExponent s anchor) (by
        intro o m
        cases o with
        | none => exact hs m
        | some j => exact hanchor j m)).mp hDI
    have hnoneSome : (none : Option I) = some i := by
      apply hAugInj
      simpa [continuedHurwitzAugmentedExponent] using hi
    simp at hnoneSome

/-- A finite differential-matroid closure relation over algebraic-character anchors transfers
algebraicity to the captured monodromy character. -/
theorem monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (halg : ∀ i, IsAlgebraic ℚ (monoScalar (anchor i)))
    (hdep : ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor) :
    IsAlgebraic ℚ (monoScalar s) := by
  obtain ⟨i, hi⟩ :=
    exists_anchor_monoScalar_eq_of_continuedHurwitzDependentOverAnchors
      hs hanchor hinj hdep
  rw [hi]
  exact halg i

/-- A nonreal point with algebraic Arakelov coordinate cannot lie in the differential closure of
any finite nonintegral monodromy-separated algebraic-character anchor atlas. -/
theorem not_continuedHurwitzDependentOverAlgebraicAnchors_of_arakelovW_algebraic_of_im_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {s : ℂ} {anchor : I → ℂ}
    (hw : IsAlgebraic ℚ (arakelovW s))
    (him : s.im ≠ 0)
    (hs : ∀ m : ℤ, s ≠ (m : ℂ))
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (halg : ∀ i, IsAlgebraic ℚ (monoScalar (anchor i))) :
    ¬ ContinuedHurwitzDifferentiallyDependentOverAnchors s anchor := by
  intro hdep
  exact monoScalar_transcendental_of_arakelovW_algebraic_of_im_ne_zero hw him
    (monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors
      hs hanchor hinj halg hdep)

/-- **Finite-anchor value-relation chain to RH.** If every hypothetical right-half Xi-indexed
Hurwitz function lies in the differential-matroid closure of one finite algebraic-character anchor
family, and its Arakelov coordinate is algebraic, then RH follows. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraic_of_finiteHurwitzAnchorCapture
    {I : Type*} [Fintype I] [DecidableEq I]
    (anchor : I → ℂ)
    (hanchor : ∀ i m, anchor i ≠ (m : ℂ))
    (hinj : Function.Injective (fun i => monoScalar (anchor i)))
    (halg : ∀ i, IsAlgebraic ℚ (monoScalar (anchor i)))
    (hcapture : ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
      IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
        ContinuedHurwitzDifferentiallyDependentOverAnchors (rho : ℂ) anchor) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic
  intro rho hrho
  obtain ⟨hw, hdep⟩ := hcapture rho hrho
  refine ⟨hw, ?_⟩
  rw [xiHurwitzMonodromyCharacter]
  exact monoScalar_isAlgebraic_of_continuedHurwitzDependentOverAlgebraicAnchors
    (fun m => openCriticalStrip_point_ne_int
      (xi_divisor_support_re_mem_open_unit rho) m)
    hanchor hinj halg hdep

end

end RHTower
