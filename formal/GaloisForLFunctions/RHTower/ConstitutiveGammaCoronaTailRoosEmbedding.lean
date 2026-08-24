import GaloisForLFunctions.RHTower.RouteRSummableHadamardTailRoosEmbedding
import GaloisForLFunctions.RHTower.RouteRCompletionMigrationDefect
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDeterminantTransgression
import GaloisForLFunctions.HTGeometry.CausalCollisionRecurrenceLaw

/-!
# The full constitutive Gamma corona inside fixed-tail Roos homology

Prime enumeration identifies the all-prime constitutive quotient and the enumerated coefficient
quotient: both erase exactly absolutely summable changes.  Composing enumeration with the
canonical diagonal mismatch therefore gives a coefficient-faithful linear map from the full
constitutive Gamma corona to fixed-tail `lim¹` homology.

This extends the bounded Hadamard-corona bridge.  It sends the undamped cofinal Gamma Bockstein
exactly to Route R's undamped diagonal tail class, and it sends the constitutive critical response
exactly to the critically damped first-wall class.  Thus undamped completion escape and first-wall
normalization are connected by the already constructed Gamma response semigroup; the remaining
problem is preservation of the fixed source marker, not existence of coefficient transport.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

universe u

open GaloisForLFunctions.HTGeometry.BoundaryMigration

/-- Enumerate an all-prime coefficient sequence in canonical increasing-prime coordinates. -/
def primeTraceToRouteRTraceSequence :
    PrimeTraceSequence →ₗ[ℂ] RouteRTraceSequence where
  toFun a n := a (nthPrimeEquiv n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Raw quotient map from the full constitutive Gamma corona to fixed-tail Roos homology. -/
private def constitutiveGammaCoronaToTailRoosFun
    (x : ConstitutiveGammaCorona) :
    DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
      routeRTailRoosRestrictedBond :=
  Quotient.map
    (fun a => routeRDiagonalMismatchLinear (primeTraceToRouteRTraceSequence a))
    (by
      intro a b hab
      apply Quotient.exact
      apply (routeRDiagonalTailRoosClass_eq_iff_summable_sub _ _).2
      have hquot :
          (Submodule.Quotient.mk a : ConstitutiveGammaCorona) =
            Submodule.Quotient.mk b :=
        Quotient.sound' hab
      have hmem : a - b ∈ primeFirstTraceSummableIdeal :=
        (Submodule.Quotient.eq primeFirstTraceSummableIdeal).1 hquot
      change Summable (a - b) at hmem
      change Summable ((a - b) ∘ nthPrimeEquiv)
      exact nthPrimeEquiv.summable_iff.mpr hmem) x

/-- Coefficient-faithful linear realization of the full constitutive Gamma corona in diagonal
fixed-tail derived homology. -/
def constitutiveGammaCoronaToTailRoos :
    ConstitutiveGammaCorona →ₗ[ℂ]
      DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond where
  toFun := constitutiveGammaCoronaToTailRoosFun
  map_add' x y := by
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      induction y using Submodule.Quotient.induction_on with
      | _ b =>
        exact routeRDiagonalTailRoosClass_add _ _
  map_smul' c x := by
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      exact routeRDiagonalTailRoosClass_smul c _

@[simp]
theorem constitutiveGammaCoronaToTailRoos_mk
    (a : PrimeTraceSequence) :
    constitutiveGammaCoronaToTailRoos
        (Submodule.Quotient.mk a : ConstitutiveGammaCorona) =
      routeRDiagonalTailRoosClass (primeTraceToRouteRTraceSequence a) := by
  rfl

/-- Prime enumeration and the diagonal Roos class lose no constitutive coefficient class. -/
theorem constitutiveGammaCoronaToTailRoos_injective :
    Function.Injective constitutiveGammaCoronaToTailRoos := by
  have hker : ∀ x : ConstitutiveGammaCorona,
      constitutiveGammaCoronaToTailRoos x = 0 → x = 0 := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
      intro hzero
      rw [constitutiveGammaCoronaToTailRoos_mk] at hzero
      have henum : Summable (primeTraceToRouteRTraceSequence a) :=
        (routeRDiagonalTailRoosClass_eq_zero_iff_summable _).1 hzero
      rw [Submodule.Quotient.mk_eq_zero]
      change Summable a
      exact nthPrimeEquiv.summable_iff.mp henum
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  rw [map_sub, hxy, sub_self]

/-- The bounded Hadamard-corona bridge factors through the full constitutive Gamma corona. -/
theorem constitutiveGammaCoronaToTailRoos_comp_summableHadamard
    (x : RouteRSummableHadamardCorona) :
    constitutiveGammaCoronaToTailRoos
        (routeRSummableHadamardToConstitutiveCorona x) =
      routeRSummableHadamardToTailRoos x := by
  induction x using Quotient.inductionOn' with
  | _ a =>
    rw [routeRSummableHadamardToConstitutiveCorona_mk,
      constitutiveGammaCoronaToTailRoos_mk,
      routeRSummableHadamardToTailRoos_mk]
    apply congrArg routeRDiagonalTailRoosClass
    funext n
    simp [primeTraceToRouteRTraceSequence, routeRBoundedTraceToPrimeTrace,
      routeRBoundedTraceToTraceSequence]

/-- The full quotient map sends the undamped cofinal Gamma Bockstein coefficient-for-coefficient
to Route R's undamped diagonal completion obstruction. -/
theorem constitutiveGammaCoronaToTailRoos_bockstein (t : ℝ) :
    constitutiveGammaCoronaToTailRoos (primeGammaCofinalBockstein t) =
      routeRDiagonalTailRoosClass (routeRPrimeGammaBocksteinSequence t) := by
  rw [primeGammaCofinalBockstein, primeFixedPhysicalFisherClass,
    primeFixedPhysicalFisherClass, ← Submodule.Quotient.mk_sub,
    constitutiveGammaCoronaToTailRoos_mk]
  rfl

/-- Generic inclusion of a relative escape defect into the ambient target quotient. -/
private def escapeDefectToAmbientQuotient
    {V W : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (Jsource : Submodule ℂ V) (Jtarget : Submodule ℂ W) :
    EscapeDefect f Jsource Jtarget →ₗ[ℂ] W ⧸ Jtarget :=
  (Jtarget.comap (Jsource.map f).subtype).mapQ Jtarget
    (Jsource.map f).subtype (by
      intro x hx
      exact hx)

/-- A relative escape defect embeds faithfully in the ambient target quotient.  Passing from the
source-marked numerator to the ambient quotient changes the carrier but does not identify two
distinct escape classes. -/
private theorem escapeDefectToAmbientQuotient_injective
    {V W : Type u} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (Jsource : Submodule ℂ V) (Jtarget : Submodule ℂ W) :
    Function.Injective (escapeDefectToAmbientQuotient f Jsource Jtarget) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  change escapeDefectToAmbientQuotient f Jsource Jtarget q = 0 at hq
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      change (Submodule.Quotient.mk (x : W) : W ⧸ Jtarget) = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
      exact hq

/-- Inclusion-induced realization of the source-marked Fisher escape defect in the full ambient
tail--Roos quotient.  This forgets no coefficient of the represented escape class; it only forgets
that the numerator was presented as the image of the source boundary subspace. -/
def routeRPrimeGammaFisherEscapeToTailRoos (t : ℝ) :
    EscapeDefect (routeRPrimeGammaFixedGradeTailLanding t)
        routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary →ₗ[ℂ]
      DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
        routeRTailRoosRestrictedBond :=
  escapeDefectToAmbientQuotient (routeRPrimeGammaFixedGradeTailLanding t)
    routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary

/-- The ambient tail--Roos realization retains the complete source-marked Fisher escape class. -/
theorem routeRPrimeGammaFisherEscapeToTailRoos_injective (t : ℝ) :
    Function.Injective (routeRPrimeGammaFisherEscapeToTailRoos t) :=
  escapeDefectToAmbientQuotient_injective
    (routeRPrimeGammaFixedGradeTailLanding t)
    routeRPrimeGammaVariableGradeBoundarySpace routeRTailRoosBoundary

@[simp]
theorem routeRPrimeGammaFisherEscapeToTailRoos_mk
    (t : ℝ)
    (x : routeRPrimeGammaVariableGradeBoundarySpace.map
      (routeRPrimeGammaFixedGradeTailLanding t)) :
    routeRPrimeGammaFisherEscapeToTailRoos t (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (x : RouteRTailRoosAmbient) :
        DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
          routeRTailRoosRestrictedBond) := by
  rfl

/-- The literal source-marked Fisher completion escape maps to exactly the undamped diagonal Roos
class, strengthening the previous equivalence of their zero loci to coefficient equality in the
ambient derived quotient. -/
theorem routeRPrimeGammaFisherEscapeToTailRoos_escapeClass (t : ℝ) :
    routeRPrimeGammaFisherEscapeToTailRoos t
        (routeRPrimeGammaFisherCompletionEscapeClass t) =
      routeRDiagonalTailRoosClass (routeRPrimeGammaBocksteinSequence t) := by
  rw [routeRPrimeGammaFisherCompletionEscapeClass, boundaryEscapeClass,
    routeRPrimeGammaFisherEscapeToTailRoos_mk]
  change Submodule.Quotient.mk
      (routeRPrimeGammaFixedGradeTailLanding t
        routeRPrimeGammaFisherSourceBoundary) = _
  rw [routeRPrimeGammaFixedGradeTailLanding_fisherBoundary]
  rfl

/-- The constitutive all-prime Bockstein and the source-marked completion escape have the same
coefficient-faithful image in fixed-tail homology. -/
theorem constitutiveBockstein_eq_sourceMarkedEscape_in_tailRoos (t : ℝ) :
    constitutiveGammaCoronaToTailRoos (primeGammaCofinalBockstein t) =
      routeRPrimeGammaFisherEscapeToTailRoos t
        (routeRPrimeGammaFisherCompletionEscapeClass t) := by
  rw [constitutiveGammaCoronaToTailRoos_bockstein,
    routeRPrimeGammaFisherEscapeToTailRoos_escapeClass]

/-- Critical Gamma response and first-wall damping commute with the full constitutive-to-Roos
coefficient bridge. -/
theorem constitutiveGammaCoronaToTailRoos_criticalResponse (t : ℝ) :
    constitutiveGammaCoronaToTailRoos (constitutiveGammaCriticalWallClass t) =
      routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) := by
  rw [← routeRSummableHadamardToConstitutiveCorona_criticalWall]
  exact (constitutiveGammaCoronaToTailRoos_comp_summableHadamard
    (routeRPrimeGammaCriticalWallSummableHadamardClass t)).trans
      (routeRSummableHadamardToTailRoos_criticalWall t)

/-- Explicit commutative handoff from the undamped physical Bockstein through its critical
response time to the first-wall Roos class. -/
theorem constitutiveGammaCoronaToTailRoos_criticalResponse_bockstein (t : ℝ) :
    constitutiveGammaCoronaToTailRoos
        (constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩
          (primeGammaCofinalBockstein t)) =
      routeRDiagonalTailRoosClass (routeRPrimeGammaCriticalWallSequence t) := by
  exact constitutiveGammaCoronaToTailRoos_criticalResponse t

/-- Critical response is not a provenance-faithful operation.  At every nonneutral physical-strip
grade `t`, response at the lifetime of `t` already erases the distinct nonzero Bockstein at grade
`t / 2`.  Thus the exact undamped-to-first-wall transport cannot itself justify preservation of
the fixed Fisher source marker. -/
theorem constitutiveGammaCoronaResponse_critical_not_injective
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    ¬ Function.Injective
      (constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩) := by
  intro hinj
  have hu0 : t / 2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  have hust : |t / 2| < 1 := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg t]
  have hsource : primeGammaCofinalBockstein (t / 2) ≠ 0 :=
    (primeGammaCofinalBockstein_ne_zero_iff hust).2 hu0
  have hkill :
      constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩
          (primeGammaCofinalBockstein (t / 2)) = 0 := by
    apply (constitutiveGammaBockstein_death_iff _ hu0).2
    change |t / 2| / 2 < |t| / 2
    have hhalf : |t / 2| = |t| / 2 := by
      rw [abs_div]
      norm_num
    rw [hhalf]
    have habs : 0 < |t| := abs_pos.mpr ht0
    exact div_lt_self (div_pos habs (by norm_num)) (by norm_num)
  apply hsource
  apply hinj
  rw [hkill, map_zero]

/-! ## Exact provenance-marker obligation -/

/-- Gamma response together with an independent provenance marker.  The second coordinate is
recorded in parallel with response, rather than computed downstream from its already-collapsed
value. -/
def constitutiveGammaMarkedResponse
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    (s : NNReal) (marker : ConstitutiveGammaCorona →ₗ[ℂ] T) :
    ConstitutiveGammaCorona →ₗ[ℂ] ConstitutiveGammaCorona × T :=
  (constitutiveGammaCoronaResponse s).prod marker

/-- The exact part of a provenance marker relevant at response time `s`: its restriction to the
classes erased by that response. -/
def constitutiveGammaProvenanceMarkerRestriction
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    (s : NNReal) (marker : ConstitutiveGammaCorona →ₗ[ℂ] T) :
    constitutiveGammaResponseKernel s →ₗ[ℂ] T :=
  marker.comp (constitutiveGammaResponseKernel s).subtype

/-- **Minimal provenance criterion.**  A parallel marker repairs a lossy Gamma response exactly
when it separates the response kernel.  Thus no full source copy is logically required; only the
classes actually erased at that response time must remain distinguishable. -/
theorem constitutiveGammaMarkedResponse_injective_iff_markerRestriction
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    (s : NNReal) (marker : ConstitutiveGammaCorona →ₗ[ℂ] T) :
    Function.Injective (constitutiveGammaMarkedResponse s marker) ↔
      Function.Injective (constitutiveGammaProvenanceMarkerRestriction s marker) := by
  constructor
  · intro hjoint x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    let z : constitutiveGammaResponseKernel s := ⟨(x : ConstitutiveGammaCorona) - y, by
      change constitutiveGammaCoronaResponse s
        ((x : ConstitutiveGammaCorona) - y) = 0
      rw [map_sub,
        LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_self]⟩
    have hzMarker : constitutiveGammaProvenanceMarkerRestriction s marker z = 0 := by
      change marker ((x : ConstitutiveGammaCorona) - y) = 0
      change marker (x : ConstitutiveGammaCorona) =
        marker (y : ConstitutiveGammaCorona) at hxy
      rw [map_sub, hxy, sub_self]
    have hzJoint :
        constitutiveGammaMarkedResponse s marker (z : ConstitutiveGammaCorona) = 0 := by
      apply Prod.ext
      · exact LinearMap.mem_ker.mp z.2
      · exact hzMarker
    have hz0 : (z : ConstitutiveGammaCorona) = 0 :=
      hjoint (by simpa using hzJoint)
    exact hz0
  · intro hkernel x y hxy
    have hresponse : constitutiveGammaCoronaResponse s (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
    let z : constitutiveGammaResponseKernel s := ⟨x - y, hresponse⟩
    have hmarker : constitutiveGammaProvenanceMarkerRestriction s marker z = 0 := by
      change marker (x - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
    have hz0 : z = 0 := hkernel (by simpa using hmarker)
    exact sub_eq_zero.mp (congrArg Subtype.val hz0)

/-- Tail--Roos homology is a faithful, though generally nonminimal, provenance marker for every
Gamma response time. -/
def constitutiveGammaTailRoosMarkedResponse (s : NNReal) :
    ConstitutiveGammaCorona →ₗ[ℂ]
      ConstitutiveGammaCorona ×
        DerivedLimitOne (fun _ : ℕ => routeRSummableSequenceIdeal)
          routeRTailRoosRestrictedBond :=
  constitutiveGammaMarkedResponse s constitutiveGammaCoronaToTailRoos

theorem constitutiveGammaTailRoosMarkedResponse_injective (s : NNReal) :
    Function.Injective (constitutiveGammaTailRoosMarkedResponse s) := by
  intro x y hxy
  exact constitutiveGammaCoronaToTailRoos_injective (congrArg Prod.snd hxy)

/-- Every faithful parallel provenance marker must detect each nonzero class erased by response. -/
theorem constitutiveGammaProvenanceMarker_ne_zero_of_response_death
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    (s : NNReal) (marker : ConstitutiveGammaCorona →ₗ[ℂ] T)
    (hfaithful : Function.Injective (constitutiveGammaMarkedResponse s marker))
    {x : ConstitutiveGammaCorona} (hx : x ≠ 0)
    (hdeath : constitutiveGammaCoronaResponse s x = 0) :
    marker x ≠ 0 := by
  intro hmarker
  apply hx
  apply hfaithful
  apply Prod.ext
  · simpa [constitutiveGammaMarkedResponse] using hdeath
  · simpa [constitutiveGammaMarkedResponse] using hmarker

/-- At critical time, every faithful marker detects the explicit lower-grade Bockstein erased by
that response.  This is a concrete source-boundary proof obligation, not a generic request for an
extra invariant. -/
theorem constitutiveGammaProvenanceMarker_detects_subcriticalBockstein
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0)
    (marker : ConstitutiveGammaCorona →ₗ[ℂ] T)
    (hfaithful : Function.Injective
      (constitutiveGammaMarkedResponse ⟨|t| / 2, by positivity⟩ marker)) :
    marker (primeGammaCofinalBockstein (t / 2)) ≠ 0 := by
  have hu0 : t / 2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  have hust : |t / 2| < 1 := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg t]
  apply constitutiveGammaProvenanceMarker_ne_zero_of_response_death
    ⟨|t| / 2, by positivity⟩ marker hfaithful
  · exact (primeGammaCofinalBockstein_ne_zero_iff hust).2 hu0
  · apply (constitutiveGammaBockstein_death_iff _ hu0).2
    rw [abs_div]
    norm_num
    have habs : 0 < |t| := abs_pos.mpr ht0
    exact div_lt_self (div_pos habs (by norm_num)) (by norm_num)

/-- A marker computed only after Gamma response cannot restore any distinction that response
erased.  In particular, no serial conservation law or downstream invariant repairs critical-time
provenance loss. -/
theorem constitutiveGammaPostprocessedMarker_not_injective_at_critical
    {T : Type u} [AddCommGroup T] [Module ℂ T]
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0)
    (downstream : ConstitutiveGammaCorona →ₗ[ℂ] T) :
    ¬ Function.Injective
      (constitutiveGammaMarkedResponse ⟨|t| / 2, by positivity⟩
        (downstream.comp
          (constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩))) := by
  intro hjoint
  apply constitutiveGammaCoronaResponse_critical_not_injective ht ht0
  intro x y hxy
  apply hjoint
  apply Prod.ext
  · exact hxy
  · change downstream (constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩ x) =
      downstream (constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩ y)
    exact congrArg downstream hxy

/-! ## Recurrent provenance-cobordism obstruction -/

/-- A recurrent exact-action history cannot retain a nonzero erased Gamma class when its
transverse reporter is a faithful provenance marker.  The recurrence law annihilates only the
reported transverse charge; internal collision data in any larger reporter kernel remains
unconstrained. -/
theorem constitutiveGammaResponseKernel_eq_zero_of_recurrentProvenance
    {T : Type u} [NormedAddCommGroup T] [NormedSpace ℂ T]
    (s : NNReal) (marker : ConstitutiveGammaCorona →ₗ[ℂ] T)
    (hfaithful : Function.Injective (constitutiveGammaMarkedResponse s marker))
    (x : constitutiveGammaResponseKernel s)
    (potential : ConstitutiveGammaCorona × ConstitutiveGammaCorona → ℝ)
    (history : ℕ → ConstitutiveGammaCorona × ConstitutiveGammaCorona)
    (hzero : history 0 = ((x : ConstitutiveGammaCorona), 0))
    (hledger : IsCausalCollisionActionLedger marker.toAddMonoidHom potential history)
    (hrecurrent : IsCofinalCollisionPotentialRecurrent potential history) :
    x = 0 := by
  have hcharge := collisionTransverseCharge_eq_zero_of_actionLedger_of_recurrent
    marker.toAddMonoidHom potential history hledger hrecurrent 0
  have hmarker : marker (x : ConstitutiveGammaCorona) = 0 := by
    rw [hzero] at hcharge
    simpa [collisionTransverseCharge] using hcharge
  have hrestriction :
      constitutiveGammaProvenanceMarkerRestriction s marker x = 0 := by
    exact hmarker
  have hinjective :=
    (constitutiveGammaMarkedResponse_injective_iff_markerRestriction s marker).1
      hfaithful
  exact hinjective (by simpa using hrestriction)

/-- The explicit shorter-lived Bockstein killed at critical response time cannot be the initial
collision of a recurrent exact nonnegative-action history with a faithful provenance marker.
This is the source-specific incompatibility needed by a recurrent provenance law: off-wall
completion error cannot be placed on a finite-action recurrent loop, while reporter-kernel
solitons are not ruled out. -/
theorem no_constitutiveGammaCriticalBockstein_recurrentProvenance
    {T : Type u} [NormedAddCommGroup T] [NormedSpace ℂ T]
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0)
    (marker : ConstitutiveGammaCorona →ₗ[ℂ] T)
    (hfaithful : Function.Injective
      (constitutiveGammaMarkedResponse ⟨|t| / 2, by positivity⟩ marker))
    (potential : ConstitutiveGammaCorona × ConstitutiveGammaCorona → ℝ)
    (history : ℕ → ConstitutiveGammaCorona × ConstitutiveGammaCorona)
    (hzero : history 0 = (primeGammaCofinalBockstein (t / 2), 0))
    (hledger : IsCausalCollisionActionLedger marker.toAddMonoidHom potential history)
    (hrecurrent : IsCofinalCollisionPotentialRecurrent potential history) :
    False := by
  have hu0 : t / 2 ≠ 0 := div_ne_zero ht0 (by norm_num)
  have hust : |t / 2| < 1 := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg t]
  have hkill :
      constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩
          (primeGammaCofinalBockstein (t / 2)) = 0 := by
    apply (constitutiveGammaBockstein_death_iff _ hu0).2
    rw [abs_div]
    norm_num
    have habs : 0 < |t| := abs_pos.mpr ht0
    exact div_lt_self (div_pos habs (by norm_num)) (by norm_num)
  let x : constitutiveGammaResponseKernel ⟨|t| / 2, by positivity⟩ :=
    ⟨primeGammaCofinalBockstein (t / 2), hkill⟩
  have hx0 : x = 0 :=
    constitutiveGammaResponseKernel_eq_zero_of_recurrentProvenance
      ⟨|t| / 2, by positivity⟩ marker hfaithful x potential history (by
        simpa [x] using hzero) hledger hrecurrent
  have hsource : primeGammaCofinalBockstein (t / 2) ≠ 0 :=
    (primeGammaCofinalBockstein_ne_zero_iff hust).2 hu0
  exact hsource (by
    have := congrArg Subtype.val hx0
    simpa [x] using this)

/-! ## Upstream Euler--Fisher coordinate replay -/

/-- One ordinary-prime coefficient, read on the canonical prequotient source sequence.  This
normed reporter lives upstream of singular completion; no norm on Tail--Roos homology is needed. -/
def routeRTraceCoordinateMarker (n : ℕ) : RouteRTraceSequence →ₗ[ℂ] ℂ where
  toFun a := a n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem routeRTraceCoordinateMarker_apply
    (n : ℕ) (a : RouteRTraceSequence) :
    routeRTraceCoordinateMarker n a = a n := rfl

/-- The upstream coordinate reporter reads exactly the literal signed Gamma Bockstein
coefficient at the corresponding ordinary prime. -/
theorem routeRTraceCoordinateMarker_bocksteinSequence
    (n : ℕ) (t : ℝ) :
    routeRTraceCoordinateMarker n (routeRPrimeGammaBocksteinSequence t) =
      (primeGammaCofinalBocksteinCoefficient t (nthPrimeEquiv n) : ℂ) := by
  simp [routeRPrimeGammaBocksteinSequence,
    primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherComplexTwist]

/-- Every ordinary-prime Euler--Fisher coordinate detects every nonneutral Gamma grade before
completion.  The reporter is therefore source-native and coefficient-faithful on the explicit
Bockstein without copying the whole source. -/
theorem routeRTraceCoordinateMarker_bocksteinSequence_ne_zero
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    routeRTraceCoordinateMarker n (routeRPrimeGammaBocksteinSequence t) ≠ 0 := by
  rw [routeRTraceCoordinateMarker_bocksteinSequence]
  exact_mod_cast
    ((primeGammaCofinalBocksteinCoefficient_eq_zero_iff
      t (nthPrimeEquiv n)).not.mpr ht)

/-- **Source-native finite-action replay obstruction.**  At any single ordinary-prime
Euler--Fisher coordinate, a nonneutral Gamma Bockstein cannot recur cofinally through a history
with summable total transverse action.  This removes the need for a normed full-corona or
Tail--Roos marker: the remaining global obligation is to construct the arithmetic history and
prove its finite action and coefficient-faithful Xi landing. -/
theorem no_routeRPrimeGammaBockstein_summableCoordinateReplay
    (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (history : ℕ → RouteRTraceSequence × RouteRTraceSequence)
    (hsummable : Summable (fun j => collisionTransverseAction
      (routeRTraceCoordinateMarker n).toAddMonoidHom (history j)))
    (hrecurrent : IsCofinalCollisionChargeRecurrent
      (routeRTraceCoordinateMarker n).toAddMonoidHom history
      (routeRPrimeGammaBocksteinSequence t, 0)) :
    False := by
  have hzero := collisionTransverseCharge_eq_zero_of_summableAction_of_cofinallyRecurrent
    (routeRTraceCoordinateMarker n).toAddMonoidHom history
    (routeRPrimeGammaBocksteinSequence t, 0) hsummable hrecurrent
  apply routeRTraceCoordinateMarker_bocksteinSequence_ne_zero n ht
  simpa [collisionTransverseCharge] using hzero

end

end RHTower
