import GaloisForLFunctions.HTGeometry.SubsystemPairCurvature
import GaloisForLFunctions.HTGeometry.SubsystemAtlasProjectiveGenericityLaw

/-!
# Infinite networks: the exhaustion law

A countably infinite locally finite interaction network carries a countable
family of real local coefficients.  Each finite volume of an exhaustion reads
a finite subfamily of them, and its own genericity set is dense, residual and
of full Lebesgue measure in its own finite-dimensional coefficient space.

Residuality transports backwards along the coordinate restriction, which is a
continuous open map, and residual sets are closed under countable
intersection; so all finite volumes are simultaneously generic on a residual
— hence dense — subset of the whole coefficient product.  Absolute continuity
of the finite-dimensional restriction marginals turns each finite-volume bad
cylinder into a null set, and a countable union of null sets is null.

Consequently, residually and almost surely, the temporal rank of every finite
volume of a connected exhaustion is the full tensor dimension minus the global
phase, `∏_{v ∈ W_k} q_v − 1`, and this diverges.  No fixed finite-dimensional
temporal carrier absorbs all finite-volume completed dynamics.  This is an
exhaustion statement: nothing here asserts an infinite-volume rank.
-/

open Set Topology MeasureTheory Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### A countable atlas of good sets inside one countable coefficient product -/

section Atlas

variable {ι : Type*} {Λ : Type*} {n : Λ → ℕ}

/-- Ambient parameters, in a possibly infinite coefficient product, whose
restriction to each member of a supplied atlas lands in that member's own
good set. -/
def ambientRestrictedGoodSet (Good : ∀ a : Λ, Set (Fin (n a) → ℝ))
    (e : ∀ a : Λ, Fin (n a) → ι) : Set (ι → ℝ) :=
  {p | ∀ a, coefficientRestrict (e a) p ∈ Good a}

theorem ambientRestrictedGoodSet_eq_iInter (Good : ∀ a : Λ, Set (Fin (n a) → ℝ))
    (e : ∀ a : Λ, Fin (n a) → ι) :
    ambientRestrictedGoodSet Good e =
      ⋂ a, coefficientRestrict (e a) ⁻¹' Good a := by
  ext p
  simp [ambientRestrictedGoodSet]

/-- **Residual atlas over a countable coefficient product.**  A countable
atlas of residual finite-dimensional good sets, each read through an injective
selector of the ambient coordinates, has residual — hence dense —
simultaneous intersection. -/
theorem ambientRestrictedGoodSet_residual [Countable ι] [Countable Λ]
    (Good : ∀ a : Λ, Set (Fin (n a) → ℝ)) (e : ∀ a : Λ, Fin (n a) → ι)
    (he : ∀ a, Function.Injective (e a))
    (hres : ∀ a, Good a ∈ residual (Fin (n a) → ℝ)) :
    ambientRestrictedGoodSet Good e ∈ residual (ι → ℝ) ∧
      Dense (ambientRestrictedGoodSet Good e) := by
  have hmem : ambientRestrictedGoodSet Good e ∈ residual (ι → ℝ) := by
    rw [ambientRestrictedGoodSet_eq_iInter]
    refine countable_iInter_mem.2 fun a => ?_
    exact preimage_mem_residual_of_isOpenMap
      (continuous_coefficientRestrict (e a))
      (isOpenMap_coefficientRestrict (he a)) (hres a)
  exact ⟨hmem, dense_of_mem_residual hmem⟩

/-- **Almost-sure atlas over a countable coefficient product.**  If every
finite-dimensional good set has full Lebesgue measure and every restriction
marginal of a law on the coefficient product is absolutely continuous with
respect to Lebesgue measure, then the simultaneous event has full
probability. -/
theorem measure_compl_ambientRestrictedGoodSet_eq_zero [Countable Λ]
    (Good : ∀ a : Λ, Set (Fin (n a) → ℝ)) (e : ∀ a : Λ, Fin (n a) → ι)
    (hnull : ∀ a, volume (Good a)ᶜ = 0) (μ : Measure (ι → ℝ))
    (hac : ∀ a, (Measure.map (coefficientRestrict (e a)) μ).AbsolutelyContinuous
      (volume : Measure (Fin (n a) → ℝ))) :
    μ (ambientRestrictedGoodSet Good e)ᶜ = 0 := by
  rw [ambientRestrictedGoodSet_eq_iInter, Set.compl_iInter]
  refine measure_iUnion_null fun a => ?_
  rw [← Set.preimage_compl]
  have hmarg : (Measure.map (coefficientRestrict (e a)) μ) (Good a)ᶜ = 0 :=
    hac a (hnull a)
  obtain ⟨T, hsub, hmeas, hTnull⟩ := exists_measurable_superset_of_null hmarg
  have hT : μ (coefficientRestrict (e a) ⁻¹' T) = 0 := by
    rw [← Measure.map_apply (measurable_coefficientRestrict (e a)) hmeas]
    exact hTnull
  exact measure_mono_null (Set.preimage_mono hsub) hT

end Atlas

/-! ### Divergence of the finite-volume tensor dimension -/

/-- A strictly increasing sequence of finite sets has at least `k` elements at
stage `k`. -/
theorem card_le_of_strictMono {V : Type*} {W : ℕ → Finset V} (hW : StrictMono W)
    (k : ℕ) : k ≤ (W k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hlt : (W k).card < (W (k + 1)).card :=
        Finset.card_lt_card (hW (Nat.lt_succ_self k))
      omega

/-- **Divergence of the finite-volume temporal rank.**  If every local
dimension is at least two and the volumes exhaust, the tensor dimension minus
the global phase diverges. -/
theorem tendsto_atTop_prod_sub_one {V : Type*} (q : V → ℕ) (h2 : ∀ v, 2 ≤ q v)
    (W : ℕ → Finset V)
    (hcard : Tendsto (fun k => (W k).card) atTop atTop) :
    Tendsto (fun k => (∏ v ∈ W k, q v) - 1) atTop atTop := by
  refine tendsto_atTop_mono (f := fun k => (W k).card) (fun k => ?_) hcard
  have hpow : 2 ^ (W k).card ≤ ∏ v ∈ W k, q v := by
    calc 2 ^ (W k).card = ∏ _v ∈ W k, 2 := (Finset.prod_const 2).symm
      _ ≤ ∏ v ∈ W k, q v := Finset.prod_le_prod' fun v _ => h2 v
  have hself : (W k).card < 2 ^ (W k).card := Nat.lt_two_pow_self
  omega

/-- **Divergence along a strictly increasing exhaustion.** -/
theorem tendsto_atTop_prod_sub_one_of_strictMono {V : Type*} (q : V → ℕ)
    (h2 : ∀ v, 2 ≤ q v) {W : ℕ → Finset V} (hW : StrictMono W) :
    Tendsto (fun k => (∏ v ∈ W k, q v) - 1) atTop atTop :=
  tendsto_atTop_prod_sub_one q h2 W
    (tendsto_atTop_mono (fun k => card_le_of_strictMono hW k) tendsto_id)

/-! ### The temporal rank of a connected finite volume -/

/-- A connected finite interaction graph reads its full tensor dimension minus
the global phase. -/
theorem finiteInducedGraphTemporalRank_univ {X : Type*} [Fintype X]
    [DecidableEq X] [Nonempty X] (G : SimpleGraph X) (q : X → ℕ)
    (hG : G.Connected) :
    finiteInducedGraphTemporalRank G q Finset.univ = (∏ v, q v) - 1 := by
  classical
  letI : Nonempty ((Finset.univ : Finset X) : Type _) :=
    ⟨⟨Classical.arbitrary X, Finset.mem_univ _⟩⟩
  unfold finiteInducedGraphTemporalRank
  rw [finiteGraphTemporalRank_of_connected]
  · congr 1
    exact Finset.prod_attach _ _
  · exact (SimpleGraph.Iso.comap
      (Equiv.subtypeUnivEquiv (fun x : X => Finset.mem_univ x)) G).connected_iff.mpr hG

/-! ### Finite volumes of an infinite network -/

variable {V : Type} [DecidableEq V]

/-- The site type of a finite volume. -/
abbrev VolumeSite (W : Finset V) : Type := {v : V // v ∈ W}

/-- Local state spaces of a finite volume. -/
abbrev volumeLocal (A : V → Type) (W : Finset V) : VolumeSite W → Type :=
  fun v => A v.1

/-- Interaction graph induced on a finite volume. -/
abbrev volumeGraph (G : SimpleGraph V) (W : Finset V) :
    SimpleGraph (VolumeSite W) :=
  G.comap (fun v : VolumeSite W => v.1)

variable (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of real interaction coordinates of a finite volume. -/
abbrev volumeCoordinateCount (W : Finset V) : ℕ :=
  interactionCoordinateCount (volumeLocal A W) (volumeGraph G W)

variable {ι : Type*}

/-- Ambient coefficients of an infinite network at which every finite volume
of an exhaustion is simultaneously spectrally generic. -/
def networkExhaustionGoodSet (W : ℕ → Finset V)
    (e : ∀ k, Fin (volumeCoordinateCount A G (W k)) → ι) : Set (ι → ℝ) :=
  ambientRestrictedGoodSet
    (fun k => allSubsystemGenericSet (volumeLocal A (W k)) (volumeGraph G (W k))) e

variable [∀ v, Nonempty (A v)]

/-- **Simultaneous genericity of all finite volumes.**  For a countable
coefficient product and injective coordinate selectors, the ambient parameters
at which every finite volume of the exhaustion is spectrally generic are
residual and dense. -/
theorem networkExhaustionGoodSet_residual [Countable ι]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) (W : ℕ → Finset V)
    (e : ∀ k, Fin (volumeCoordinateCount A G (W k)) → ι)
    (he : ∀ k, Function.Injective (e k)) :
    networkExhaustionGoodSet A G W e ∈ residual (ι → ℝ) ∧
      Dense (networkExhaustionGoodSet A G W e) :=
  ambientRestrictedGoodSet_residual _ e he fun k =>
    (allSubsystemGenericSet_dense_residual_fullMeasure
      (volumeLocal A (W k)) (volumeGraph G (W k)) fun v => h2 v.1).2.1

/-- **Almost-sure genericity of all finite volumes.**  Every law on the
coefficient product whose finite-volume restriction marginals are absolutely
continuous with respect to Lebesgue measure gives the simultaneous genericity
event full probability. -/
theorem measure_compl_networkExhaustionGoodSet_eq_zero
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) (W : ℕ → Finset V)
    (e : ∀ k, Fin (volumeCoordinateCount A G (W k)) → ι)
    (μ : Measure (ι → ℝ))
    (hac : ∀ k, (Measure.map (coefficientRestrict (e k)) μ).AbsolutelyContinuous
      (volume : Measure (Fin (volumeCoordinateCount A G (W k)) → ℝ))) :
    μ (networkExhaustionGoodSet A G W e)ᶜ = 0 :=
  measure_compl_ambientRestrictedGoodSet_eq_zero _ e
    (fun k => (allSubsystemGenericSet_dense_residual_fullMeasure
      (volumeLocal A (W k)) (volumeGraph G (W k)) fun v => h2 v.1).2.2) μ hac

/-- **The temporal rank of a connected finite volume.**  At an ambient
parameter of the simultaneous genericity set, the temporal rank read by the
whole of a connected finite volume is its tensor dimension minus the global
phase. -/
theorem anchoredTemporalRank_volume_eq (W : ℕ → Finset V)
    (e : ∀ k, Fin (volumeCoordinateCount A G (W k)) → ι)
    {p : ι → ℝ} (hp : p ∈ networkExhaustionGoodSet A G W e) (k : ℕ)
    (hconn : (volumeGraph G (W k)).Connected)
    (r : ∀ v : VolumeSite (W k), A v.1) :
    anchoredTemporalRank
        (subsystemHamiltonian_isHermitian (volumeLocal A (W k))
          (volumeGraph G (W k)) Finset.univ
          (coefficientRestrict (e k) p)).eigenvalues r =
      (∏ v ∈ W k, Fintype.card (A v)) - 1 := by
  classical
  haveI : Nonempty (VolumeSite (W k)) := hconn.nonempty
  rw [anchoredTemporalRank_eq_finiteInducedGraphTemporalRank
    (volumeLocal A (W k)) (volumeGraph G (W k)) (hp k) Finset.univ r,
    finiteInducedGraphTemporalRank_univ _ _ hconn]
  congr 1
  exact Finset.prod_attach (W k) (fun v => Fintype.card (A v))

/-- **Infinite-network completion.**  Fix a countably infinite interaction
network with all local dimensions at least two, an exhaustion by connected
finite volumes, and an injective selector of each finite volume's real
interaction coordinates inside one countable ambient coefficient product.
Then, on a residual — hence dense — set of ambient coefficients, and with full
probability under every law whose finite-volume restriction marginals are
absolutely continuous with respect to Lebesgue measure, every finite volume
reads exactly its tensor dimension minus the global phase, and those ranks
diverge.

No fixed finite-dimensional temporal carrier therefore absorbs all
finite-volume completed dynamics.  This is a statement about the exhaustion:
no infinite-volume rank is asserted. -/
theorem infiniteNetworkExhaustion_temporalRank_tendsto_atTop [Countable ι]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v)) {W : ℕ → Finset V} (hW : StrictMono W)
    (hconn : ∀ k, (volumeGraph G (W k)).Connected)
    (e : ∀ k, Fin (volumeCoordinateCount A G (W k)) → ι)
    (he : ∀ k, Function.Injective (e k)) :
    (networkExhaustionGoodSet A G W e ∈ residual (ι → ℝ) ∧
        Dense (networkExhaustionGoodSet A G W e)) ∧
      (∀ μ : Measure (ι → ℝ),
        (∀ k, (Measure.map (coefficientRestrict (e k)) μ).AbsolutelyContinuous
          (volume : Measure (Fin (volumeCoordinateCount A G (W k)) → ℝ))) →
        μ (networkExhaustionGoodSet A G W e)ᶜ = 0) ∧
      (∀ p ∈ networkExhaustionGoodSet A G W e, ∀ k : ℕ,
        ∀ r : ∀ v : VolumeSite (W k), A v.1,
          anchoredTemporalRank
              (subsystemHamiltonian_isHermitian (volumeLocal A (W k))
                (volumeGraph G (W k)) Finset.univ
                (coefficientRestrict (e k) p)).eigenvalues r =
            (∏ v ∈ W k, Fintype.card (A v)) - 1) ∧
      Tendsto (fun k => (∏ v ∈ W k, Fintype.card (A v)) - 1) atTop atTop := by
  refine ⟨networkExhaustionGoodSet_residual A G h2 W e he,
    fun μ hac => measure_compl_networkExhaustionGoodSet_eq_zero A G h2 W e μ hac,
    fun p hp k r =>
      anchoredTemporalRank_volume_eq A G W e hp k (hconn k) r, ?_⟩
  exact tendsto_atTop_prod_sub_one_of_strictMono
    (fun v => Fintype.card (A v)) (fun v => h2 v) hW

end

end GaloisForLFunctions.HTGeometry
