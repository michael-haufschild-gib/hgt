import GaloisForLFunctions.HTGeometry.GraphSaturationCore
import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusCrossPairSingularOneLegTrace

/-!
# Singular graph completion of the Big-Witt cross-pair one-leg trace

The algebraic right-leg trace has no continuous extension to the ambient
Calderón--Witt edge `ℓ²` space.  This module constructs its exact graph
completion.  Finite labelled edge packets are dense in the full Hilbert
product of ambient packet and trace, and normalized finite averages converge
to the nonzero vertical trace generator.

The genuinely coherent Frobenius right-leg packets obey a stronger law: every
one has trace zero, so even their closure in the graph completion stays in the
closed trace kernel and cannot contain the vertical generator.  Thus arbitrary
singular averaging cannot be substituted for the arithmetic Frobenius source.
Any successful Xi/Green descent must select an incomplete or renormalized
right-leg incidence before coherent fibre summation.  No RH, zero-location,
positivity, spectral-synthesis, or computation premise occurs.
-/

open Complex Filter Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

local instance : Infinite DeningerCalderonWittCrossPrimePacketIndex :=
  Infinite.of_injective deningerBigWittCrossPairPacketNatEmbedding
    deningerBigWittCrossPairPacketNatEmbedding.injective

/-- Graph completion of ambient Calderón--Witt edge packets plus algebraic
one-leg trace. -/
abbrev DeningerBigWittCrossPairSingularOneLegGraph :=
  WithLp 2 (DeningerCalderonWittCrossPrimePacketHilbert × ℂ)

/-- Finite labelled graph before completion. -/
def deningerBigWittCrossPairFiniteOneLegGraph :
    Submodule ℂ DeningerBigWittCrossPairSingularOneLegGraph :=
  GaloisForLFunctions.HTGeometry.linearGraphSubmodule
    deningerBigWittCrossPairFinitePacketAdmission
    deningerBigWittCrossPairAlgebraicOneLegTrace

/-- The ambient packet and algebraic trace have trivial joint annihilator. -/
theorem deningerBigWittCrossPairFiniteOneLegGraph_jointAnnihilator
    (x : DeningerCalderonWittCrossPrimePacketHilbert) (y : ℂ)
    (h : ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
      inner ℂ (deningerBigWittCrossPairFinitePacketAdmission c) x +
        inner ℂ (deningerBigWittCrossPairAlgebraicOneLegTrace c) y = 0) :
    x = 0 ∧ y = 0 := by
  have hcoord : ∀ i : DeningerCalderonWittCrossPrimePacketIndex, x i = -y := by
    intro i
    have hi := h (Finsupp.single i 1)
    have hi' : x i + y = 0 := by
      simpa [lp.inner_single_left] using hi
    exact eq_neg_of_add_eq_zero_left hi'
  have hy : y = 0 := by
    by_contra hy
    have hs := (lp.memℓp x).summable (by norm_num)
    change Summable
      (fun i : DeningerCalderonWittCrossPrimePacketIndex => ‖x i‖ ^ (2 : ℝ)) at hs
    have hsconst : Summable
        (fun _i : DeningerCalderonWittCrossPrimePacketIndex => ‖y‖ ^ (2 : ℝ)) := by
      exact hs.congr (fun i => by rw [hcoord i, norm_neg])
    have hpos : 0 < ‖y‖ ^ (2 : ℝ) := by positivity
    exact Set.infinite_univ (Set.Finite.of_summable_const hpos hsconst)
  refine ⟨?_, hy⟩
  apply lp.ext
  funext i
  simp [hcoord i, hy]

/-- Completion of the full finite one-leg graph is the entire Hilbert
packet--trace product. -/
theorem deningerBigWittCrossPairFiniteOneLegGraph_closure_eq_top :
    deningerBigWittCrossPairFiniteOneLegGraph.topologicalClosure = ⊤ := by
  apply GaloisForLFunctions.HTGeometry.linearGraphSubmodule_closure_eq_top_of_annihilator
  exact deningerBigWittCrossPairFiniteOneLegGraph_jointAnnihilator

/-- Literal finite packet admission into the one-leg graph. -/
def deningerBigWittCrossPairFiniteOneLegGraphAdmission :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ]
      DeningerBigWittCrossPairSingularOneLegGraph :=
  (WithLp.linearEquiv 2 ℂ
      (DeningerCalderonWittCrossPrimePacketHilbert × ℂ)).symm.toLinearMap.comp
    (deningerBigWittCrossPairFinitePacketAdmission.prod
      deningerBigWittCrossPairAlgebraicOneLegTrace)

@[simp] theorem deningerBigWittCrossPairFiniteOneLegGraphAdmission_ofLp
    (c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    (deningerBigWittCrossPairFiniteOneLegGraphAdmission c).ofLp =
      (deningerBigWittCrossPairFinitePacketAdmission c,
        deningerBigWittCrossPairAlgebraicOneLegTrace c) := rfl

/-- Finite labelled one-leg packets are dense in the exact graph completion. -/
theorem deningerBigWittCrossPairFiniteOneLegGraphAdmission_dense :
    DenseRange deningerBigWittCrossPairFiniteOneLegGraphAdmission := by
  change Dense
    (deningerBigWittCrossPairFiniteOneLegGraph :
      Set DeningerBigWittCrossPairSingularOneLegGraph)
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    deningerBigWittCrossPairFiniteOneLegGraph_closure_eq_top

/-- Forgetful continuous projection to the ambient Calderón--Witt edge
completion. -/
def deningerBigWittCrossPairOneLegGraphAmbientProjection :
    DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  WithLp.fstL 2 ℂ DeningerCalderonWittCrossPrimePacketHilbert ℂ

/-- Continuous trace retained by the singular graph completion. -/
def deningerBigWittCrossPairOneLegGraphTrace :
    DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ :=
  WithLp.sndL 2 ℂ DeningerCalderonWittCrossPrimePacketHilbert ℂ

/-- Nonzero vertical trace generator lost by ambient `ℓ²` projection. -/
def deningerBigWittCrossPairOneLegGraphSingularVector :
    DeningerBigWittCrossPairSingularOneLegGraph :=
  WithLp.toLp 2 ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))

@[simp] theorem deningerBigWittCrossPairOneLegGraphAmbientProjection_singularVector :
    deningerBigWittCrossPairOneLegGraphAmbientProjection
      deningerBigWittCrossPairOneLegGraphSingularVector = 0 := by
  rfl

@[simp] theorem deningerBigWittCrossPairOneLegGraphTrace_singularVector :
    deningerBigWittCrossPairOneLegGraphTrace
      deningerBigWittCrossPairOneLegGraphSingularVector = 1 := by
  rfl

@[simp] theorem deningerBigWittCrossPairOneLegGraphTrace_finiteAdmission
    (c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    deningerBigWittCrossPairOneLegGraphTrace
      (deningerBigWittCrossPairFiniteOneLegGraphAdmission c) =
        deningerBigWittCrossPairAlgebraicOneLegTrace c := by
  rfl

theorem deningerBigWittCrossPairOneLegGraphSingularVector_ne_zero :
    deningerBigWittCrossPairOneLegGraphSingularVector ≠ 0 := by
  intro h
  have ht := congrArg deningerBigWittCrossPairOneLegGraphTrace h
  rw [deningerBigWittCrossPairOneLegGraphTrace_singularVector, map_zero] at ht
  exact one_ne_zero ht

/-- Explicit algebraic averages converge to the vertical trace generator
while their ambient edge packets disappear. -/
theorem tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_averagingPacket :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairPacketAveragingPacket n))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have hpair : Tendsto
      (fun n =>
        (deningerBigWittCrossPairFinitePacketAdmission
            (deningerBigWittCrossPairPacketAveragingPacket n),
          deningerBigWittCrossPairAlgebraicOneLegTrace
            (deningerBigWittCrossPairPacketAveragingPacket n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using
      tendsto_deningerBigWittCrossPairFinitePacketAdmission_averagingPacket.prodMk
        tendsto_deningerBigWittCrossPairAlgebraicOneLegTrace_averagingPacket
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

/-- Every genuinely coherent finite Frobenius right-leg fibre lies in the
horizontal trace kernel. -/
@[simp] theorem deningerBigWittCrossPairOneLegGraphTrace_finiteRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittCrossPairOneLegGraphTrace
      (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairFiniteRightLegPacket a s)) = 0 := by
  rw [deningerBigWittCrossPairOneLegGraphTrace_finiteAdmission,
    deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket]

/-- Set of graph vectors arising from coherent complete finite right-leg
Frobenius fibres. -/
def deningerBigWittCrossPairCoherentRightLegGraphSet :
    Set DeningerBigWittCrossPairSingularOneLegGraph :=
  {z | ∃ (a : Nat.Primes → ℂ) (s : Finset Nat.Primes),
    z = deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittCrossPairFiniteRightLegPacket a s)}

/-- The graph closure of coherent right-leg fibres remains trapped in the
closed trace kernel. -/
theorem deningerBigWittCrossPairCoherentRightLegGraphSet_closure_le_traceKernel :
    closure deningerBigWittCrossPairCoherentRightLegGraphSet ⊆
      {z | deningerBigWittCrossPairOneLegGraphTrace z = 0} := by
  apply closure_minimal
  · rintro z ⟨a, s, rfl⟩
    exact deningerBigWittCrossPairOneLegGraphTrace_finiteRightLegPacket a s
  · exact isClosed_eq deningerBigWittCrossPairOneLegGraphTrace.continuous continuous_const

/-- **Coherent-source exclusion.**  Although arbitrary finite graph packets
are dense in the full singular graph, coherent complete Frobenius right-leg
fibres cannot approximate its vertical generator. -/
theorem deningerBigWittCrossPairOneLegGraphSingularVector_not_mem_coherent_closure :
    deningerBigWittCrossPairOneLegGraphSingularVector ∉
      closure deningerBigWittCrossPairCoherentRightLegGraphSet := by
  intro h
  have hz := deningerBigWittCrossPairCoherentRightLegGraphSet_closure_le_traceKernel h
  change (1 : ℂ) = 0 at hz
  exact one_ne_zero hz

/-- Continuous fixed-left-leg fibre readout on the singular graph. -/
def deningerBigWittCrossPairOneLegGraphFiberReadout
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ :=
  deningerBigWittCrossPairOneLegGraphTrace.smulRight
    (-2 * deningerBigWittCrossPairLeftLeg a p q)

/-- The finite coherent Frobenius fibre coefficient factors exactly through
the singular graph readout. -/
theorem deningerBigWittCrossPairFrobeniusFiberCoefficient_eq_graphReadout
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes) :
    deningerBigWittCrossPairFrobeniusFiberCoefficient a s p q =
      deningerBigWittCrossPairOneLegGraphFiberReadout a p q
        (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittCrossPairFiniteRightLegPacket a s)) := by
  rw [deningerBigWittCrossPairFrobeniusFiberCoefficient_eq_singularOneLegContraction]
  change (-2 * deningerBigWittCrossPairLeftLeg a p q) *
      deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittCrossPairFiniteRightLegPacket a s) =
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittCrossPairFiniteRightLegPacket a s) *
      (-2 * deningerBigWittCrossPairLeftLeg a p q)
  exact mul_comm _ _

/-- Vertical singular trace recovers the unsummed fixed-left-leg coefficient. -/
@[simp] theorem deningerBigWittCrossPairOneLegGraphFiberReadout_singularVector
    (a : Nat.Primes → ℂ) (p q : Nat.Primes) :
    deningerBigWittCrossPairOneLegGraphFiberReadout a p q
      deningerBigWittCrossPairOneLegGraphSingularVector =
        -2 * deningerBigWittCrossPairLeftLeg a p q := by
  simp [deningerBigWittCrossPairOneLegGraphFiberReadout]

/-! ## Selected incomplete source before coherent fibre summation -/

/-- Coherent finite right-leg fibre with one labelled ordered edge removed.
This is the minimal source-level operation that escapes the coherent trace
kernel without erasing its four-prime provenance. -/
def deningerBigWittCrossPairSelectedPuncturedRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittCrossPairFiniteRightLegPacket a s -
    Finsupp.single i (deningerBigWittCrossPairRightLeg a i.1.1 i.1.2)

/-- Puncturing one selected edge leaves exactly its negative one-leg trace. -/
@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_selectedPuncturedRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
      (deningerBigWittCrossPairSelectedPuncturedRightLegPacket a s i) =
        -deningerBigWittCrossPairRightLeg a i.1.1 i.1.2 := by
  rw [deningerBigWittCrossPairSelectedPuncturedRightLegPacket, map_sub,
    deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket,
    deningerBigWittCrossPairAlgebraicOneLegTrace_single, zero_sub]

/-- Selected edge plus its punctured complement reconstructs the complete
coherent right-leg fibre before completion. -/
theorem deningerBigWittCrossPairSelectedEdge_add_punctured_eq_coherent
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    Finsupp.single i (deningerBigWittCrossPairRightLeg a i.1.1 i.1.2) +
        deningerBigWittCrossPairSelectedPuncturedRightLegPacket a s i =
      deningerBigWittCrossPairFiniteRightLegPacket a s := by
  rw [deningerBigWittCrossPairSelectedPuncturedRightLegPacket]
  abel

/-- Source reconstruction persists exactly after singular graph admission. -/
theorem deningerBigWittCrossPairSelectedEdgeGraph_add_puncturedGraph_eq_coherentGraph
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (Finsupp.single i (deningerBigWittCrossPairRightLeg a i.1.1 i.1.2)) +
      deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairSelectedPuncturedRightLegPacket a s i) =
      deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairFiniteRightLegPacket a s) := by
  rw [← map_add,
    deningerBigWittCrossPairSelectedEdge_add_punctured_eq_coherent]

/-- **Exact selected-source compensator.**  Puncturing right edge `(r,t)`
before coherent summation makes the continuous graph readout equal the
negative four-label Frobenius coefficient `(p,q;r,t)`. -/
theorem deningerBigWittCrossPairOneLegGraphFiberReadout_selectedPuncturedRightLegPacket
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairOneLegGraphFiberReadout a p q
        (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittCrossPairSelectedPuncturedRightLegPacket a s i)) =
      -deningerBigWittCrossPairFrobeniusCoefficient a p q i.1.1 i.1.2 := by
  rw [deningerBigWittCrossPairFrobeniusCoefficient_eq]
  change deningerBigWittCrossPairOneLegGraphTrace
      (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairSelectedPuncturedRightLegPacket a s i)) *
      (-2 * deningerBigWittCrossPairLeftLeg a p q) =
    -(-2 * deningerBigWittCrossPairLeftLeg a p q *
      deningerBigWittCrossPairRightLeg a i.1.1 i.1.2)
  rw [deningerBigWittCrossPairOneLegGraphTrace_finiteAdmission,
    deningerBigWittCrossPairAlgebraicOneLegTrace_selectedPuncturedRightLegPacket]
  ring

end

end RHTower
