import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw

/-!
# Involutive projective-wedge transport

The alternating two-point first-jet determinant, a contracted Koszul
differential, and the connection correction of a moving two-frame are three
forms of one elementary exterior-square law.

No analytic or Riemann-hypothesis assumption enters this file.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Alternating projective defect of a two-component field across an
involution candidate `tau`. -/
def involutiveProjectiveWedge {Q : Type*} (tau : Q -> Q)
    (j0 j1 : Q -> ℂ) (q : Q) : ℂ :=
  j1 q * j0 (tau q) - j0 q * j1 (tau q)

/-- Zeroth component of a point-dependent two-frame transport. -/
def projectiveJetTransportZero {Q : Type*}
    (a b : Q -> ℂ) (j0 j1 : Q -> ℂ) (q : Q) : ℂ :=
  a q * j0 q + b q * j1 q

/-- First component of a point-dependent two-frame transport. -/
def projectiveJetTransportOne {Q : Type*}
    (c d : Q -> ℂ) (j0 j1 : Q -> ℂ) (q : Q) : ℂ :=
  c q * j0 q + d q * j1 q

/-- The projective wedge is odd under an involution. -/
theorem involutiveProjectiveWedge_apply_involution
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (j0 j1 : Q -> ℂ) (q : Q) :
    involutiveProjectiveWedge tau j0 j1 (tau q) =
      -involutiveProjectiveWedge tau j0 j1 q := by
  rw [involutiveProjectiveWedge, involutiveProjectiveWedge, htau q]
  ring

/-- Nonvanishing scalar gauges multiply the wedge by their reflected norm
factor and therefore preserve its zero locus. -/
theorem involutiveProjectiveWedge_gauge_covariant
    {Q : Type*} (tau : Q -> Q) (g j0 j1 : Q -> ℂ) (q : Q) :
    involutiveProjectiveWedge tau
        (fun p => g p * j0 p) (fun p => g p * j1 p) q =
      g q * g (tau q) * involutiveProjectiveWedge tau j0 j1 q := by
  rw [involutiveProjectiveWedge, involutiveProjectiveWedge]
  ring

theorem involutiveProjectiveWedge_gauge_eq_zero_iff
    {Q : Type*} (tau : Q -> Q) {g j0 j1 : Q -> ℂ} (q : Q)
    (hg : g q ≠ 0) (hgtau : g (tau q) ≠ 0) :
    involutiveProjectiveWedge tau
        (fun p => g p * j0 p) (fun p => g p * j1 p) q = 0 <->
      involutiveProjectiveWedge tau j0 j1 q = 0 := by
  rw [involutiveProjectiveWedge_gauge_covariant]
  simp [hg, hgtau]

/-- Exact covariant-selection law.  A moving two-frame transports the old
wedge by its determinant and adds exactly one term: the mismatch of the
frame between the two involutive endpoints. -/
theorem involutiveProjectiveWedge_transport_eq_det_mul_add_connection
    {Q : Type*} (tau : Q -> Q) (a b c d j0 j1 : Q -> ℂ) (q : Q) :
    involutiveProjectiveWedge tau
        (projectiveJetTransportZero a b j0 j1)
        (projectiveJetTransportOne c d j0 j1) q =
      (a q * d q - b q * c q) *
          involutiveProjectiveWedge tau j0 j1 q +
        projectiveJetTransportOne c d j0 j1 q *
          ((a (tau q) - a q) * j0 (tau q) +
            (b (tau q) - b q) * j1 (tau q)) -
        projectiveJetTransportZero a b j0 j1 q *
          ((c (tau q) - c q) * j0 (tau q) +
            (d (tau q) - d q) * j1 (tau q)) := by
  rw [involutiveProjectiveWedge, involutiveProjectiveWedge,
    projectiveJetTransportZero, projectiveJetTransportOne,
    projectiveJetTransportZero, projectiveJetTransportOne]
  ring

/-- A frame that is constant on one involutive pair has no connection term:
the exterior defect obeys pure determinant covariance. -/
theorem involutiveProjectiveWedge_transport_of_pair_invariant
    {Q : Type*} (tau : Q -> Q) (a b c d j0 j1 : Q -> ℂ) (q : Q)
    (ha : a (tau q) = a q) (hb : b (tau q) = b q)
    (hc : c (tau q) = c q) (hd : d (tau q) = d q) :
    involutiveProjectiveWedge tau
        (projectiveJetTransportZero a b j0 j1)
        (projectiveJetTransportOne c d j0 j1) q =
      (a q * d q - b q * c q) *
        involutiveProjectiveWedge tau j0 j1 q := by
  rw [involutiveProjectiveWedge_transport_eq_det_mul_add_connection]
  simp [ha, hb, hc, hd]

/-- An invertible pair-invariant frame preserves the exact selection locus. -/
theorem involutiveProjectiveWedge_transport_eq_zero_iff
    {Q : Type*} (tau : Q -> Q) (a b c d j0 j1 : Q -> ℂ) (q : Q)
    (ha : a (tau q) = a q) (hb : b (tau q) = b q)
    (hc : c (tau q) = c q) (hd : d (tau q) = d q)
    (hdet : a q * d q - b q * c q ≠ 0) :
    involutiveProjectiveWedge tau
        (projectiveJetTransportZero a b j0 j1)
        (projectiveJetTransportOne c d j0 j1) q = 0 <->
      involutiveProjectiveWedge tau j0 j1 q = 0 := by
  rw [involutiveProjectiveWedge_transport_of_pair_invariant
    tau a b c d j0 j1 q ha hb hc hd]
  exact mul_eq_zero_iff_left hdet

/-- When the zeroth component is nonzero at both endpoints, the wedge is
exactly the obstruction to descent of the logarithmic first jet. -/
theorem involutiveProjectiveWedge_eq_zero_iff_logJet_descends
    {Q : Type*} (tau : Q -> Q) {j0 j1 : Q -> ℂ} (q : Q)
    (h0 : j0 q ≠ 0) (h0tau : j0 (tau q) ≠ 0) :
    involutiveProjectiveWedge tau j0 j1 q = 0 <->
      j1 q / j0 q = j1 (tau q) / j0 (tau q) := by
  rw [involutiveProjectiveWedge, sub_eq_zero]
  constructor
  · intro h
    apply (div_eq_div_iff h0 h0tau).2
    simpa [mul_comm] using h
  · intro h
    have hcross := (div_eq_div_iff h0 h0tau).1 h
    simpa [mul_comm] using hcross

/-- Projective-line descent form.  If the logarithmic first jet is a
downstream observable of a coordinate that identifies the two endpoints,
then its exterior obstruction vanishes. -/
theorem involutiveProjectiveWedge_eq_zero_of_logJet_factorsThrough
    {Q R : Type*} (tau : Q -> Q) {j0 j1 : Q -> ℂ} (pi : Q -> R)
    (h0 : forall q, j0 q ≠ 0)
    (hpi : InvariantUnder tau pi)
    (hfactor : FactorsThrough pi (fun q => j1 q / j0 q))
    (q : Q) :
    involutiveProjectiveWedge tau j0 j1 q = 0 := by
  rw [involutiveProjectiveWedge_eq_zero_iff_logJet_descends
    tau q (h0 q) (h0 (tau q))]
  exact mapKernelPair_mono_of_factorsThrough hfactor (hpi q).symm

/-- Equivalence relation generated by one involution.  Every class has at
most the two points `q` and `tau q`. -/
def involutionOrbitSetoid {Q : Type*} (tau : Q -> Q)
    (htau : Involutive tau) : Setoid Q where
  r q r := r = q ∨ r = tau q
  iseqv := by
    constructor
    · intro q
      exact Or.inl rfl
    · intro q r hqr
      rcases hqr with rfl | hqr
      · exact Or.inl rfl
      · exact Or.inr (by rw [hqr, htau q])
    · intro q r s hqr hrs
      rcases hqr with rfl | hqr
      · exact hrs
      · rcases hrs with hrs | hrs
        · exact Or.inr (hrs.trans hqr)
        · exact Or.inl (by rw [hrs, hqr, htau q])

/-- Finest observation that identifies every involutive pair. -/
def involutionOrbitObservation {Q : Type*} (tau : Q -> Q)
    (htau : Involutive tau) : Q -> Quotient (involutionOrbitSetoid tau htau) :=
  Quotient.mk _

theorem invariantUnder_involutionOrbitObservation
    {Q : Type*} (tau : Q -> Q) (htau : Involutive tau) :
    InvariantUnder tau (involutionOrbitObservation tau htau) := by
  intro q
  apply Quotient.sound
  exact Or.inr (htau q).symm

/-- **Complete projective descent classification.**  For a nowhere-zero
zeroth component, the logarithmic first jet factors through the finest
reflection-invariant observation exactly when the exterior obstruction
vanishes on every orbit.  Hence no coarser invariant observation can evade
the wedge obstruction. -/
theorem logJet_factorsThrough_involutionOrbit_iff
    {Q : Type*} (tau : Q -> Q) (htau : Involutive tau)
    {j0 j1 : Q -> ℂ} (h0 : forall q, j0 q ≠ 0) :
    FactorsThrough (involutionOrbitObservation tau htau)
        (fun q => j1 q / j0 q) <->
      forall q, involutiveProjectiveWedge tau j0 j1 q = 0 := by
  constructor
  · intro hfactor q
    exact involutiveProjectiveWedge_eq_zero_of_logJet_factorsThrough
      tau (involutionOrbitObservation tau htau) h0
      (invariantUnder_involutionOrbitObservation tau htau) hfactor q
  · intro hzero
    let logJet : Q -> ℂ := fun q => j1 q / j0 q
    let descend : Quotient (involutionOrbitSetoid tau htau) -> ℂ :=
      Quotient.lift logJet (by
        intro q r hqr
        rcases hqr with rfl | hqr
        · rfl
        · rw [hqr]
          exact
            (involutiveProjectiveWedge_eq_zero_iff_logJet_descends
              tau q (h0 q) (h0 (tau q))).mp (hzero q))
    refine ⟨descend, ?_⟩
    funext q
    rfl

/-- Odd projective curvature cannot factor through a quotient that identifies
the two involutive endpoints unless it vanishes. -/
theorem involutiveProjectiveWedge_eq_zero_of_orbit_factorization
    {Q R : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (j0 j1 : Q -> ℂ) (pi : Q -> R) (value : R -> ℂ)
    (hpi : forall q, pi (tau q) = pi q)
    (hfactor : forall q,
      involutiveProjectiveWedge tau j0 j1 q = value (pi q))
    (q : Q) :
    involutiveProjectiveWedge tau j0 j1 q = 0 := by
  have heven : involutiveProjectiveWedge tau j0 j1 (tau q) =
      involutiveProjectiveWedge tau j0 j1 q := by
    rw [hfactor, hfactor, hpi]
  rw [involutiveProjectiveWedge_apply_involution htau] at heven
  have htwo : (2 : ℂ) * involutiveProjectiveWedge tau j0 j1 q = 0 := by
    calc
      (2 : ℂ) * involutiveProjectiveWedge tau j0 j1 q =
          involutiveProjectiveWedge tau j0 j1 q -
            (-involutiveProjectiveWedge tau j0 j1 q) := by ring
      _ = 0 := by rw [heven]; ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Observation-order form of the same theorem.  The projective wedge is the
canonical reflection-odd transverse channel of a two-component jet, so it
cannot be recovered downstream of an invariant observation unless it is
zero. -/
theorem involutiveProjectiveWedge_eq_zero_of_factorsThrough_invariantObservation
    {Q R : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (j0 j1 : Q -> ℂ) (pi : Q -> R)
    (hpi : InvariantUnder tau pi)
    (hfactor : FactorsThrough pi (involutiveProjectiveWedge tau j0 j1))
    (q : Q) :
    involutiveProjectiveWedge tau j0 j1 q = 0 := by
  have heven : involutiveProjectiveWedge tau j0 j1 q =
      involutiveProjectiveWedge tau j0 j1 (tau q) :=
    mapKernelPair_mono_of_factorsThrough hfactor (hpi q).symm
  have hodd := involutiveProjectiveWedge_apply_involution htau j0 j1 q
  have htwo : (2 : ℂ) * involutiveProjectiveWedge tau j0 j1 q = 0 := by
    calc
      (2 : ℂ) * involutiveProjectiveWedge tau j0 j1 q =
          involutiveProjectiveWedge tau j0 j1 q -
            (-involutiveProjectiveWedge tau j0 j1 q) := by ring
      _ = 0 := by rw [← hodd, heven]; ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Contracted projective Koszul differential. -/
def contractedProjectiveKoszul {I : Type*} (i0 : I)
    (eta z : I -> ℂ) (i : I) : ℂ :=
  eta i0 * z i - z i0 * eta i

/-- Packet on one projective ray. -/
def projectiveRayPacket {I : Type*} (eta : I -> ℂ)
    (scalar : ℂ) (i : I) : ℂ :=
  scalar * eta i

/-- Pointed scalar remaining after vertical projective resolution. -/
def contractedProjectiveKoszulResidual {I : Type*} (i0 : I)
    (eta z : I -> ℂ) : ℂ :=
  z i0 / eta i0

@[simp]
theorem contractedProjectiveKoszul_projectiveRayPacket
    {I : Type*} (i0 : I) (eta : I -> ℂ) (scalar : ℂ) :
    contractedProjectiveKoszul i0 eta
        (projectiveRayPacket eta scalar) = 0 := by
  funext i
  simp only [contractedProjectiveKoszul, projectiveRayPacket, Pi.zero_apply]
  ring

@[simp]
theorem contractedProjectiveKoszulResidual_projectiveRayPacket
    {I : Type*} (i0 : I) (eta : I -> ℂ) (scalar : ℂ)
    (heta : eta i0 ≠ 0) :
    contractedProjectiveKoszulResidual i0 eta
        (projectiveRayPacket eta scalar) = scalar := by
  rw [contractedProjectiveKoszulResidual, projectiveRayPacket]
  exact mul_div_cancel_right₀ scalar heta

/-- Exact projective kernel law: if the pointed horizon coordinate is
nonzero, the Koszul differential kills precisely its scalar ray. -/
theorem contractedProjectiveKoszul_eq_zero_iff
    {I : Type*} (i0 : I) {eta z : I -> ℂ} (heta : eta i0 ≠ 0) :
    contractedProjectiveKoszul i0 eta z = 0 <->
      exists scalar : ℂ, z = fun i => scalar * eta i := by
  constructor
  · intro hz
    refine ⟨z i0 / eta i0, ?_⟩
    funext i
    have hi := congrFun hz i
    simp only [Pi.zero_apply] at hi
    rw [contractedProjectiveKoszul, sub_eq_zero] at hi
    change z i = (z i0 / eta i0) * eta i
    calc
      z i = (z i0 * eta i) / eta i0 := by
        apply (eq_div_iff heta).2
        simpa [mul_comm] using hi
      _ = (z i0 / eta i0) * eta i := by field_simp
  · rintro ⟨scalar, rfl⟩
    funext i
    simp only [contractedProjectiveKoszul, Pi.zero_apply]
    ring

/-- **Vertical/horizontal separation law.**  Exact vertical Koszul
compatibility leaves an arbitrary scalar field on the residual ray.  Its
horizontal involutive wedge is therefore unchanged and completely
unconstrained by vertical exactness. -/
theorem verticalProjectiveResolution_preserves_arbitraryHorizontalWedge
    {Q I : Type*} (tau : Q -> Q) (i0 : I) (eta : I -> ℂ)
    (heta : eta i0 ≠ 0) (j0 j1 : Q -> ℂ) :
    (forall q,
      contractedProjectiveKoszul i0 eta
        (projectiveRayPacket eta (j0 q)) = 0) ∧
    (forall q,
      contractedProjectiveKoszul i0 eta
        (projectiveRayPacket eta (j1 q)) = 0) ∧
    (forall q,
      involutiveProjectiveWedge tau
          (fun p => contractedProjectiveKoszulResidual i0 eta
            (projectiveRayPacket eta (j0 p)))
          (fun p => contractedProjectiveKoszulResidual i0 eta
            (projectiveRayPacket eta (j1 p))) q =
        involutiveProjectiveWedge tau j0 j1 q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact contractedProjectiveKoszul_projectiveRayPacket i0 eta (j0 q)
  · intro q
    exact contractedProjectiveKoszul_projectiveRayPacket i0 eta (j1 q)
  · intro q
    rw [involutiveProjectiveWedge, involutiveProjectiveWedge]
    simp only [contractedProjectiveKoszulResidual_projectiveRayPacket
      i0 eta _ heta]

/-- The universal law in one package: oddness, exact moving-frame
decomposition, and exact projective-ray kernel. -/
theorem involutiveProjectiveWedgeTransportLaw
    {Q I : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (a b c d j0 j1 : Q -> ℂ) (q : Q)
    (i0 : I) (eta z : I -> ℂ) (heta : eta i0 ≠ 0) :
    involutiveProjectiveWedge tau j0 j1 (tau q) =
        -involutiveProjectiveWedge tau j0 j1 q ∧
    involutiveProjectiveWedge tau
        (projectiveJetTransportZero a b j0 j1)
        (projectiveJetTransportOne c d j0 j1) q =
      (a q * d q - b q * c q) *
          involutiveProjectiveWedge tau j0 j1 q +
        projectiveJetTransportOne c d j0 j1 q *
          ((a (tau q) - a q) * j0 (tau q) +
            (b (tau q) - b q) * j1 (tau q)) -
        projectiveJetTransportZero a b j0 j1 q *
          ((c (tau q) - c q) * j0 (tau q) +
            (d (tau q) - d q) * j1 (tau q)) ∧
    (contractedProjectiveKoszul i0 eta z = 0 <->
      exists scalar : ℂ, z = fun i => scalar * eta i) := by
  exact ⟨
    involutiveProjectiveWedge_apply_involution htau j0 j1 q,
    involutiveProjectiveWedge_transport_eq_det_mul_add_connection
      tau a b c d j0 j1 q,
    contractedProjectiveKoszul_eq_zero_iff i0 heta⟩

end

end GaloisForLFunctions.HTGeometry
