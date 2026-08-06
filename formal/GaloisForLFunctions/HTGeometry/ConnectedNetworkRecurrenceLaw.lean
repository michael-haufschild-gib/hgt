import GaloisForLFunctions.HTGeometry.InfiniteNetworkExhaustion
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw

/-!
# Generic spectra and recurrence of a connected finite network

A connected interaction graph has exactly one component packet, so the
transversality set of its subsystem atlas already forces the spectrum of the
whole network Hamiltonian to be maximally projective.  Its temporal rank is
therefore the full tensor dimension minus the global phase, and the recurrence
geometry of a maximally projective spectrum applies verbatim: the phase orbit
has the exact anchored return frequency, and no nonzero exact projective
return exists.

Interaction multiplication and recurrence scarcity are the same rank law.
-/

open scoped Matrix BigOperators
open Set Topology MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Root packets across different index types -/

/-- **Cross-type relabelling of root packets.**  Two real energy packets on
different index types with the same complex multiset of values are
relabellings of each other, so maximal projective independence transfers. -/
theorem maximallyProjectiveEnergy_of_multiset_eq {I J : Type*} [Fintype I]
    [DecidableEq I] [Fintype J] [DecidableEq J] {e : I → ℝ}
    (hmax : MaximallyProjectiveEnergy e) (f : J → ℝ)
    (heq : Finset.univ.val.map (fun j => ((f j : ℝ) : ℂ)) =
      Finset.univ.val.map (fun i => ((e i : ℝ) : ℂ))) :
    MaximallyProjectiveEnergy f := by
  classical
  have hinjE : Function.Injective e := MaximallyProjectiveEnergy.injective hmax
  have hnodup : (Finset.univ.val.map (fun j => ((f j : ℝ) : ℂ))).Nodup := by
    rw [heq]
    refine Finset.univ.nodup.map ?_
    intro a b hab
    exact hinjE (Complex.ofReal_injective hab)
  have hinjF : Function.Injective f := by
    intro a b hab
    refine Multiset.inj_on_of_nodup_map hnodup a (Finset.mem_univ a) b
      (Finset.mem_univ b) ?_
    exact_mod_cast hab
  have hmemE : ∀ y : ℝ,
      ((y : ℝ) : ℂ) ∈ Finset.univ.val.map (fun i => ((e i : ℝ) : ℂ)) ↔
        y ∈ Set.range e := by
    intro y
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_range]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, Complex.ofReal_injective hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  have hmemF : ∀ y : ℝ,
      ((y : ℝ) : ℂ) ∈ Finset.univ.val.map (fun j => ((f j : ℝ) : ℂ)) ↔
        y ∈ Set.range f := by
    intro y
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_range]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, Complex.ofReal_injective hj⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  have hrange : Set.range f = Set.range e := by
    ext x
    rw [← hmemF x, ← hmemE x, heq]
  let σ : J ≃ I :=
    (Equiv.ofInjective f hinjF).trans
      ((Equiv.setCongr hrange).trans (Equiv.ofInjective e hinjE).symm)
  have hcomp : ∀ j, e (σ j) = f j := by
    intro j
    show e ((Equiv.ofInjective e hinjE).symm
      ((Equiv.setCongr hrange) ((Equiv.ofInjective f hinjF) j))) = f j
    rw [Equiv.apply_ofInjective_symm hinjE]
    rfl
  have htransfer := maximallyProjectiveEnergy_equiv σ hmax
  rwa [funext hcomp] at htransfer

/-! ### The single component packet of a connected network -/

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The subsystem induced on the whole vertex set is the network itself. -/
theorem connected_inducedSubsystemGraph_univ (G : SimpleGraph V)
    (hG : G.Connected) : (inducedSubsystemGraph G Finset.univ).Connected :=
  (SimpleGraph.Iso.comap
    (Equiv.subtypeUnivEquiv (fun x : V => Finset.mem_univ x)) G).connected_iff.mpr hG

/-- A connected network has one site packet: the whole vertex set. -/
theorem sitePacketOf_univ (G : SimpleGraph V) (hG : G.Connected)
    (v : {x : V // x ∈ (Finset.univ : Finset V)}) :
    sitePacketOf G Finset.univ v = Finset.univ := by
  classical
  haveI : Subsingleton (inducedSubsystemGraph G Finset.univ).ConnectedComponent :=
    (connected_inducedSubsystemGraph_univ G hG).preconnected.subsingleton_connectedComponent
  ext x
  simp only [Finset.mem_univ, iff_true]
  rw [mem_sitePacketOf_iff]
  exact ⟨⟨x, Finset.mem_univ x⟩, Subsingleton.elim _ _, rfl⟩

/-- A connected network has exactly one component packet. -/
theorem componentPackets_univ_of_connected (G : SimpleGraph V) [Nonempty V]
    (hG : G.Connected) :
    componentPackets G Finset.univ = {(Finset.univ : Finset V)} := by
  classical
  unfold componentPackets
  rw [Finset.image_congr
    (g := fun _ : {x : V // x ∈ (Finset.univ : Finset V)} =>
      (Finset.univ : Finset V)) (fun v _ => sitePacketOf_univ G hG v)]
  exact Finset.image_const
    ⟨⟨Classical.arbitrary V, Finset.mem_univ _⟩, Finset.mem_attach _ _⟩ _

theorem univ_mem_componentPackets_univ (G : SimpleGraph V) [Nonempty V]
    (hG : G.Connected) :
    (Finset.univ : Finset V) ∈ componentPackets G Finset.univ := by
  rw [componentPackets_univ_of_connected G hG]
  exact Finset.mem_singleton_self _

/-- The component packets of a connected network form a one-element index. -/
@[reducible] def uniqueComponentPacketUniv (G : SimpleGraph V) [Nonempty V]
    (hG : G.Connected) :
    Unique {P : Finset V // P ∈ componentPackets G Finset.univ} where
  default := ⟨Finset.univ, univ_mem_componentPackets_univ G hG⟩
  uniq := by
    intro a
    refine Subtype.ext ?_
    exact Finset.mem_singleton.1
      ((Finset.ext_iff.1 (componentPackets_univ_of_connected G hG)
        (a : Finset V)).1 a.2)

/-! ### The generic spectrum of a connected network -/

variable (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- **The generic Hamiltonian of a connected network is maximally
projective.**  A connected graph has one component packet, so the subsystem
transversality set of the whole vertex set already says that the network
spectrum admits no nonzero balanced integer relation. -/
theorem maximallyProjective_subsystemBlock_univ_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ subsystemComponentGenericSet A G Finset.univ) :
    MaximallyProjectiveEnergy
      (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues := by
  classical
  letI := uniqueComponentPacketUniv G hG
  set M := componentPolynomialFamily A G Finset.univ with hM
  have hmapEq := blockDiagonal'_map M p
  have hherm : ∀ c, ((M c).map (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun t => (p t : ℂ)))).IsHermitian :=
    fun c => componentPolynomialFamily_isHermitian A G Finset.univ c p
  have hHermBD : ((Matrix.blockDiagonal' M).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun t => (p t : ℂ)))).IsHermitian := by
    rw [hmapEq]
    exact isHermitian_blockDiagonal' hherm
  have hmax := maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
    (Matrix.blockDiagonal' M) p hp hHermBD
  refine maximallyProjectiveEnergy_of_multiset_eq hmax _ ?_
  rw [hermitianEigenvalues_rootMultiset (subsystemBlock_isHermitian A G Finset.univ p),
    hermitianEigenvalues_rootMultiset hHermBD, hmapEq, charpoly_blockDiagonal',
    Fintype.prod_unique]
  exact congrArg Polynomial.roots
    (congrArg Matrix.charpoly
      (componentPolynomialFamily_eval A G Finset.univ default p).symm)

/-- **Equation `(3)`: interaction multiplication.**  At a generic interaction
parameter, a connected network reads its full tensor dimension minus the
global phase. -/
theorem anchoredTemporalRank_subsystemBlock_univ_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ subsystemComponentGenericSet A G Finset.univ)
    (r : LocalConfiguration A (Finset.univ : Finset V)) :
    anchoredTemporalRank
        (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues r =
      (∏ v, Fintype.card (A v)) - 1 := by
  rw [anchoredTemporalRank_eq_card_sub_one_of_maximallyProjective _
    (maximallyProjective_subsystemBlock_univ_of_connected A G hG hp) r,
    card_localConfiguration]

/-- Interaction multiplication in product form: temporal rank plus the global
phase is the total tensor dimension. -/
theorem anchoredTemporalRank_add_one_subsystemBlock_univ_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ subsystemComponentGenericSet A G Finset.univ)
    (r : LocalConfiguration A (Finset.univ : Finset V)) :
    anchoredTemporalRank
          (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues r + 1 =
      ∏ v, Fintype.card (A v) := by
  rw [anchoredTemporalRank_subsystemBlock_univ_of_connected A G hG hp r]
  refine Nat.sub_add_cancel (Finset.one_le_prod fun v _ => ?_)
  haveI : Nonempty (A v) := ⟨r ⟨v, Finset.mem_univ v⟩⟩
  exact Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero

/-! ### Recurrence of a connected network -/

/-- **Equation `(9)`: the exact anchored projective return frequency.**  At a
generic interaction parameter of a connected network, the asymptotic time
frequency with which the completed phase orbit returns to within chordal
tolerance `ε` of its start, modulo the global phase, is
`(2 arcsin(ε/2) / π)` raised to the temporal rank. -/
theorem anchoredProjectiveReturnFrequency_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ subsystemComponentGenericSet A G Finset.univ)
    (r : LocalConfiguration A (Finset.univ : Finset V))
    {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    Tendsto
      (fun T =>
        (finiteTorusPhaseProbabilityMeasure
          (projectiveFrequency
            (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues r) T :
          Measure (UnitAddTorus
            {i : LocalConfiguration A (Finset.univ : Finset V) // i ≠ r}))
            (anchoredProjectiveReturnTarget ε))
      atTop
      (𝓝 (ENNReal.ofReal (2 * Real.arcsin (ε / 2) / Real.pi) ^
        ((∏ v, Fintype.card (A v)) - 1))) := by
  have h := maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency
    (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues
    (maximallyProjective_subsystemBlock_univ_of_connected A G hG hp) r hε0 hε2
  rwa [card_localConfiguration] at h

/-- **No exact projective return.**  At a generic interaction parameter of a
connected network of total tensor dimension at least three, the only time at
which the completed phase orbit returns exactly to its start, modulo the
global phase, is time zero. -/
theorem no_nonzeroExactAnchoredReturn_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hG : G.Connected)
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ subsystemComponentGenericSet A G Finset.univ)
    (r : LocalConfiguration A (Finset.univ : Finset V))
    (hdim : 3 ≤ ∏ v, Fintype.card (A v)) :
    ∀ t : ℝ,
      screwPhase
        (projectiveFrequency
          (subsystemBlock_isHermitian A G Finset.univ p).eigenvalues r) t = 0 →
      t = 0 := by
  refine MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn
    (maximallyProjective_subsystemBlock_univ_of_connected A G hG hp) r ?_
  rwa [card_localConfiguration]

end

end GaloisForLFunctions.HTGeometry
