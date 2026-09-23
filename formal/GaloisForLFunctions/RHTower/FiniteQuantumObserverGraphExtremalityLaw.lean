import GaloisForLFunctions.HTGeometry.LinearSpectralGapRatioExtremality
import GaloisForLFunctions.HTGeometry.SpectralRecurrenceExponentLaw
import GaloisForLFunctions.RHTower.FiniteQuantumObserverFirstReturnExponentLaw

/-!
# Simultaneous arithmetic extremality of every finite observer graph

For a coherence graph, orient one gap from the chosen root of each component to every nonroot
vertex.  These rows form a forest incidence frame and are linearly independent.  General linear
gap-frame extremality therefore makes their normalized relative-frequency vector non-VWA for
almost every Hamiltonian in any escaping simple-spectrum chart.

Only finitely many labelled simple graphs exist at fixed Hilbert-space dimension.  A finite
intersection consequently produces one conull Hamiltonian set on which this arithmetic conclusion
holds for every observer graph chosen after the Hamiltonian.
-/

open scoped BigOperators
open MeasureTheory
open Filter Topology

namespace RHTower

noncomputable section

/-- Tail of each component-root gap. -/
def graphRootGapTail {d : ℕ} (G : SimpleGraph (Fin d)) : graphNonRoot G → Fin d :=
  fun v => graphComponentRoot G (G.connectedComponentMk v.1)

/-- Head of each component-root gap. -/
def graphRootGapHead {d : ℕ} (G : SimpleGraph (Fin d)) : graphNonRoot G → Fin d :=
  fun v => v.1

theorem graphRootGapTail_ne_head {d : ℕ} (G : SimpleGraph (Fin d))
    (v : graphNonRoot G) :
    graphRootGapHead G v ≠ graphRootGapTail G v := by
  intro h
  apply v.2
  rw [IsGraphComponentRoot]
  exact h

/-- Component-root gaps form a linearly independent balanced incidence frame. -/
theorem graphRootGapIncidence_linearIndependent {d : ℕ} (G : SimpleGraph (Fin d)) :
    LinearIndependent ℝ
      (GaloisForLFunctions.HTGeometry.edgeIncidenceRow
        (graphRootGapTail G) (graphRootGapHead G)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro weight hsum v
  have hcoord := congrArg (fun z : Fin d → ℝ => z v.1) hsum
  have hroot_ne (u : graphNonRoot G) :
      graphRootGapTail G u ≠ v.1 := by
    intro h
    apply v.2
    rw [IsGraphComponentRoot, ← h]
    simp [graphRootGapTail, connectedComponentMk_graphComponentRoot]
  have hrow (u : graphNonRoot G) :
      GaloisForLFunctions.HTGeometry.edgeIncidenceRow
          (graphRootGapTail G) (graphRootGapHead G) u v.1 =
        if u = v then 1 else 0 := by
    by_cases huv : u = v
    · subst u
      simp [GaloisForLFunctions.HTGeometry.edgeIncidenceRow,
        graphRootGapHead, hroot_ne]
    · have hhead : graphRootGapHead G u ≠ v.1 := by
        intro h
        exact huv (Subtype.ext h)
      simp [GaloisForLFunctions.HTGeometry.edgeIncidenceRow,
        hroot_ne, hhead, huv]
  simpa [hrow] using hcoord

def observerGraphGapTail {d r : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin r ≃ graphNonRoot G) : Fin r → Fin d :=
  fun k => graphRootGapTail G (q k)

def observerGraphGapHead {d r : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin r ≃ graphNonRoot G) : Fin r → Fin d :=
  fun k => graphRootGapHead G (q k)

theorem observerGraphGapIncidence_linearIndependent
    {d r : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin r ≃ graphNonRoot G) :
    LinearIndependent ℝ
      (GaloisForLFunctions.HTGeometry.edgeIncidenceRow
        (observerGraphGapTail G q) (observerGraphGapHead G q)) := by
  have hfamily :
      GaloisForLFunctions.HTGeometry.edgeIncidenceRow
          (observerGraphGapTail G q) (observerGraphGapHead G q) =
        fun k => GaloisForLFunctions.HTGeometry.edgeIncidenceRow
          (graphRootGapTail G) (graphRootGapHead G) (q k) := by
    funext k i
    rfl
  rw [hfamily]
  exact (graphRootGapIncidence_linearIndependent G).comp q q.injective

theorem observerGraphGapClock_ne
    {d r : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin (r + 1) ≃ graphNonRoot G) :
    observerGraphGapHead G q 0 ≠ observerGraphGapTail G q 0 :=
  graphRootGapTail_ne_head G (q 0)

/-- Graph gap ratios are exactly the virtual-spectrum ratios used by the observer return theorem;
the common orientation sign cancels. -/
theorem observerGraphGapRatioMap_eq_virtual
    {d e : ℕ} (G : SimpleGraph (Fin d)) (energy : Fin d → ℝ)
    (q : Fin (e + 2) ≃ graphNonRoot G) (sigma : ℝ) (hsigma : sigma ≠ 0) :
    GaloisForLFunctions.HTGeometry.edgeGapRatioMap energy
        (observerGraphGapTail G q) (observerGraphGapHead G q) =
      GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
        (observerVirtualEnergy G energy q sigma) 0 1 (fun k => k.succ.succ) := by
  funext k
  simp only [GaloisForLFunctions.HTGeometry.edgeGapRatioMap,
    observerGraphGapHead, observerGraphGapTail, graphRootGapHead, graphRootGapTail,
    GaloisForLFunctions.HTGeometry.anchoredGapRatioMap,
    observerVirtualEnergy, graphRelativeEnergy]
  simp only [Fin.cases_succ, Fin.cases_zero]
  change
    (energy (q k.succ).1 -
      energy (graphComponentRoot G (G.connectedComponentMk (q k.succ).1))) /
        (energy (q 0).1 -
          energy (graphComponentRoot G (G.connectedComponentMk (q 0).1))) =
      (sigma * (energy (q k.succ).1 -
          energy (graphComponentRoot G (G.connectedComponentMk (q k.succ).1))) - 0) /
        (sigma * (energy (q 0).1 -
          energy (graphComponentRoot G (G.connectedComponentMk (q 0).1))) - 0)
  rw [sub_zero, sub_zero]
  exact (mul_div_mul_left
    (energy (q k.succ).1 -
      energy (graphComponentRoot G (G.connectedComponentMk (q k.succ).1)))
    (energy (q 0).1 -
      energy (graphComponentRoot G (G.connectedComponentMk (q 0).1))) hsigma).symm

/-- Each fixed labelled observer graph has a null exceptional set. -/
theorem volume_vwa_observerGraphGapRatio_eq_zero
    {N d e : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P)))
    (G : SimpleGraph (Fin d)) (q : Fin (e + 2) ≃ graphNonRoot G)
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty)
    (hUsimple : U ⊆ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP) :
    volume {x ∈ U |
      GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma)
          0 1 (fun k => k.succ.succ))} = 0 := by
  have hraw := GaloisForLFunctions.HTGeometry.theoremA_sortedEdgeGapRatio
    (n := e + 1) (Nat.succ_pos e) hP hS
    (observerGraphGapTail G q) (observerGraphGapHead G q)
    (observerGraphGapIncidence_linearIndependent G q)
    (observerGraphGapClock_ne G q) hU hUc hUne hUsimple
  rw [show
    {x ∈ U |
      GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma)
          0 1 (fun k => k.succ.succ))} =
      {x ∈ U |
        GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA fun k =>
          GaloisForLFunctions.HTGeometry.edgeGapRatioMap
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x)
            (observerGraphGapTail G q) (observerGraphGapHead G q) k} by
    ext x
    constructor
    · rintro ⟨hx, hvwa⟩
      refine ⟨hx, ?_⟩
      rw [observerGraphGapRatioMap_eq_virtual G
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma hsigma]
      exact hvwa
    · rintro ⟨hx, hvwa⟩
      refine ⟨hx, ?_⟩
      rw [← observerGraphGapRatioMap_eq_virtual G
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma hsigma]
      exact hvwa]
  exact hraw

/-- Each fixed observer graph has a null exceptional set on the entire simple-spectrum locus, not
merely on one chosen chart. -/
theorem volume_vwa_observerGraphGapRatio_simpleLocus_eq_zero
    {N d e : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P)))
    (G : SimpleGraph (Fin d)) (q : Fin (e + 2) ≃ graphNonRoot G)
    (sigma : ℝ) (hsigma : sigma ≠ 0) :
    volume {x ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP |
      GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma)
          0 1 (fun k => k.succ.succ))} = 0 := by
  have hraw :=
    GaloisForLFunctions.HTGeometry.volume_vwa_sortedEdgeGapRatio_eq_zero
      (n := e + 1) (Nat.succ_pos e) hP hS
      (observerGraphGapTail G q) (observerGraphGapHead G q)
      (observerGraphGapIncidence_linearIndependent G q)
      (observerGraphGapClock_ne G q)
  rw [show
    {x ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP |
      GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma)
          0 1 (fun k => k.succ.succ))} =
      {x ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP |
        GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA fun k =>
          GaloisForLFunctions.HTGeometry.edgeGapRatioMap
            (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x)
            (observerGraphGapTail G q) (observerGraphGapHead G q) k} by
    ext x
    constructor
    · rintro ⟨hx, hvwa⟩
      refine ⟨hx, ?_⟩
      rw [observerGraphGapRatioMap_eq_virtual G
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma hsigma]
      exact hvwa
    · rintro ⟨hx, hvwa⟩
      refine ⟨hx, ?_⟩
      rw [← observerGraphGapRatioMap_eq_virtual G
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP x) q sigma hsigma]
      exact hvwa]
  exact hraw

/-- Canonical enumeration of every observer graph's nonroot vertices when visible capacity is at
least two. -/
def canonicalObserverGraphEquiv {d : ℕ} (G : SimpleGraph (Fin d))
    (hcap : 2 ≤ Fintype.card (graphNonRoot G)) :
    Fin ((Fintype.card (graphNonRoot G) - 2) + 2) ≃ graphNonRoot G := by
  have hcard : Fintype.card (graphNonRoot G) =
      (Fintype.card (graphNonRoot G) - 2) + 2 := by omega
  exact (Equiv.cast (congrArg Fin hcard.symm)).trans
    (Fintype.equivFin (graphNonRoot G)).symm

/-- **One conull Hamiltonian set is extremal for every observer coherence graph.** -/
theorem ae_all_observerGraphGapRatio_not_vwa
    {N d : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty)
    (hUsimple : U ⊆ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP) :
    ∀ᵐ theta, theta ∈ U →
      ∀ (G : SimpleGraph (Fin d))
        (hcap : 2 ≤ Fintype.card (graphNonRoot G)),
        ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
          (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
            (observerVirtualEnergy G
              (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
              (canonicalObserverGraphEquiv G hcap) 1)
            0 1 (fun k => k.succ.succ)) := by
  suffices hall : ∀ᵐ theta,
      ∀ G : SimpleGraph (Fin d), theta ∈ U →
        ∀ hcap : 2 ≤ Fintype.card (graphNonRoot G),
          ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
            (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
              (observerVirtualEnergy G
                (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
                (canonicalObserverGraphEquiv G hcap) 1)
              0 1 (fun k => k.succ.succ)) by
    filter_upwards [hall] with theta htheta hthetaU
    exact fun G => htheta G hthetaU
  rw [Filter.eventually_all]
  intro G
  by_cases hcap : 2 ≤ Fintype.card (graphNonRoot G)
  · have hnull := volume_vwa_observerGraphGapRatio_eq_zero
      hP hS G (canonicalObserverGraphEquiv G hcap) 1 one_ne_zero
      hU hUc hUne hUsimple
    have hae := GaloisForLFunctions.HTGeometry.ae_not_vwa_of_volume_eq_zero hnull
    filter_upwards [hae] with theta htheta hthetaU
    intro hcap'
    have : hcap' = hcap := Subsingleton.elim _ _
    subst hcap'
    exact htheta hthetaU
  · filter_upwards with theta
    intro _ hcap'
    exact (hcap hcap').elim

/-- One conull subset of the full simple-spectrum locus is extremal for every observer graph. -/
theorem ae_all_observerGraphGapRatio_not_vwa_simpleLocus
    {N d : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P))) :
    ∀ᵐ theta, theta ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP →
      ∀ (G : SimpleGraph (Fin d))
        (hcap : 2 ≤ Fintype.card (graphNonRoot G)),
        ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
          (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
            (observerVirtualEnergy G
              (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
              (canonicalObserverGraphEquiv G hcap) 1)
            0 1 (fun k => k.succ.succ)) := by
  suffices hall : ∀ᵐ theta,
      ∀ G : SimpleGraph (Fin d),
        theta ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP →
        ∀ hcap : 2 ≤ Fintype.card (graphNonRoot G),
          ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
            (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
              (observerVirtualEnergy G
                (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
                (canonicalObserverGraphEquiv G hcap) 1)
              0 1 (fun k => k.succ.succ)) by
    filter_upwards [hall] with theta htheta hthetaSimple
    exact fun G => htheta G hthetaSimple
  rw [Filter.eventually_all]
  intro G
  by_cases hcap : 2 ≤ Fintype.card (graphNonRoot G)
  · have hnull := volume_vwa_observerGraphGapRatio_simpleLocus_eq_zero
      hP hS G (canonicalObserverGraphEquiv G hcap) 1 one_ne_zero
    have hae := GaloisForLFunctions.HTGeometry.ae_not_vwa_of_volume_eq_zero hnull
    filter_upwards [hae] with theta htheta hthetaSimple
    intro hcap'
    have : hcap' = hcap := Subsingleton.elim _ _
    subst hcap'
    exact htheta hthetaSimple
  · filter_upwards with theta
    intro _ hcap'
    exact (hcap hcap').elim

/-- Orientation making the canonical observer clock gap positive for a strictly increasing
spectrum. -/
def observerGraphClockSign {d e : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin (e + 2) ≃ graphNonRoot G) : ℝ :=
  if graphRootGapTail G (q 0) < graphRootGapHead G (q 0) then 1 else -1

theorem observerGraphClockSign_eq_one_or_neg_one
    {d e : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin (e + 2) ≃ graphNonRoot G) :
    observerGraphClockSign G q = 1 ∨ observerGraphClockSign G q = -1 := by
  unfold observerGraphClockSign
  split_ifs <;> simp

theorem observerGraphClockSign_ne_zero
    {d e : ℕ} (G : SimpleGraph (Fin d))
    (q : Fin (e + 2) ≃ graphNonRoot G) :
    observerGraphClockSign G q ≠ 0 := by
  rcases observerGraphClockSign_eq_one_or_neg_one G q with h | h <;> rw [h] <;> norm_num

theorem observerVirtualEnergy_clockGap_pos_of_strictMono
    {d e : ℕ} (G : SimpleGraph (Fin d)) (energy : Fin d → ℝ)
    (henergy : StrictMono energy)
    (q : Fin (e + 2) ≃ graphNonRoot G) :
    0 < observerVirtualEnergy G energy q (observerGraphClockSign G q) 1 -
      observerVirtualEnergy G energy q (observerGraphClockSign G q) 0 := by
  let tail := graphRootGapTail G (q 0)
  let head := graphRootGapHead G (q 0)
  have hne : head ≠ tail := graphRootGapTail_ne_head G (q 0)
  rw [show (1 : Fin (e + 3)) = Fin.succ 0 by rfl]
  simp only [observerVirtualEnergy, Fin.cases_succ, Fin.cases_zero,
    graphRelativeEnergy, observerGraphClockSign, graphRootGapTail, graphRootGapHead]
  split_ifs with hlt
  · simpa only [one_mul, sub_zero] using sub_pos.mpr (henergy hlt)
  · have hrev : head < tail := lt_of_le_of_ne (Fin.not_lt.mp hlt) hne
    have hs := henergy hrev
    rw [sub_zero, neg_one_mul]
    change 0 < -(energy head - energy tail)
    rw [neg_sub]
    exact sub_pos.mpr hs

theorem graphRootChordEnergy_eq_zero_of_card_eq_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V) (z : V → ℂ)
    (hcard : Fintype.card (graphNonRoot G) = 0) :
    graphRootChordEnergy G z = 0 := by
  classical
  haveI : IsEmpty (graphNonRoot G) := Fintype.card_eq_zero_iff.mp hcard
  simp [graphRootChordEnergy]

theorem observerPhaseEnergy_eq_zero_of_rootChordEnergy_eq_zero
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (z : Fin d → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1)
    (hroot : graphRootChordEnergy
      (finiteObserverCoherenceGraph lam block) z = 0) :
    finiteQuantumObserverPhaseEnergy lam z block = 0 := by
  obtain ⟨a, b, ha, hb, hmetric⟩ :=
    observerPhaseEnergy_rootChordEnergy_comparable lam block hlam
  have hupper := (hmetric z hunit).2
  rw [hroot, mul_zero] at hupper
  exact le_antisymm hupper
    (finiteQuantumObserverPhaseEnergy_nonneg lam z block hlam)

/-- An observer with no visible relative phase is exactly recurrent at every time. -/
theorem tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_zero
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (energy : Fin d → ℝ)
    (hcap : Fintype.card
      (graphNonRoot (finiteObserverCoherenceGraph lam block)) = 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (finiteQuantumObserverReturnTime lam block energy t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hzero : finiteQuantumObserverPhaseEnergy lam
      (finiteObserverHamiltonianVertexPhase t₀ energy) block = 0 := by
    apply observerPhaseEnergy_eq_zero_of_rootChordEnergy_eq_zero
      lam block hlam
    · exact finiteObserverHamiltonianVertexPhase_norm t₀ energy
    · exact graphRootChordEnergy_eq_zero_of_card_eq_zero _ _ hcap
  simpa only [finiteQuantumObserverReturnTime] using
    GaloisForLFunctions.HTGeometry.tendsto_log_scalarSignalReturnTime_zero_of_exact_zero
      (fun t => finiteQuantumObserverPhaseEnergy lam
        (finiteObserverHamiltonianVertexPhase t energy) block)
      ht₀ (le_refl t₀) hzero

def canonicalObserverGraphEquivOne {d : ℕ} (G : SimpleGraph (Fin d))
    (hcap : Fintype.card (graphNonRoot G) = 1) :
    Fin 1 ≃ graphNonRoot G :=
  (Equiv.cast (congrArg Fin hcap.symm)).trans
    (Fintype.equivFin (graphNonRoot G)).symm

/-- One visible relative phase is an exact periodic clock, so it has an exact return after every
positive cutoff. -/
theorem exists_observerPhaseEnergy_exact_zero_of_capacity_one
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (energy : Fin d → ℝ)
    (hcap : Fintype.card
      (graphNonRoot (finiteObserverCoherenceGraph lam block)) = 1)
    {t₀ : ℝ} (_ht₀ : 0 < t₀) :
    ∃ tau : ℝ, t₀ ≤ tau ∧
      finiteQuantumObserverPhaseEnergy lam
        (finiteObserverHamiltonianVertexPhase tau energy) block = 0 := by
  let G := finiteObserverCoherenceGraph lam block
  let q : Fin 1 ≃ graphNonRoot G := canonicalObserverGraphEquivOne G hcap
  let v : Fin d := (q 0).1
  let r : Fin d := graphComponentRoot G (G.connectedComponentMk v)
  let omega : ℝ := energy v - energy r
  have hroot_of_phase (tau : ℝ)
      (hphase : finiteQuantumObserverPhase
        (finiteObserverHamiltonianVertexPhase tau energy) v r = 1) :
      graphRootChordEnergy G
        (finiteObserverHamiltonianVertexPhase tau energy) = 0 := by
    let z := finiteObserverHamiltonianVertexPhase tau energy
    have hz : z v = z r := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      rw [← norm_mul_star_sub_one_eq_norm_sub _ _
        (finiteObserverHamiltonianVertexPhase_norm tau energy r)]
      change ‖finiteQuantumObserverPhase z v r - 1‖ = 0
      rw [show finiteQuantumObserverPhase z v r = 1 by exact hphase,
        sub_self, norm_zero]
    rw [graphRootChordEnergy]
    have hsum := Equiv.sum_comp q
      (fun u : graphNonRoot G =>
        ‖z u.1 - z (graphComponentRoot G
          (G.connectedComponentMk u.1))‖ ^ (2 : ℕ))
    rw [Fin.sum_univ_one] at hsum
    simpa only [z, v, r, hz, sub_self, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using hsum.symm
  by_cases homega : omega = 0
  · refine ⟨t₀, le_rfl, ?_⟩
    apply observerPhaseEnergy_eq_zero_of_rootChordEnergy_eq_zero
      lam block hlam
    · exact finiteObserverHamiltonianVertexPhase_norm t₀ energy
    · apply hroot_of_phase
      rw [finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase_real]
      simp [omega, homega]
  · obtain ⟨T, hT, m, hperiod⟩ :
        ∃ T : ℝ, 0 < T ∧ ∃ m : ℤ,
          omega * T = (m : ℝ) * (2 * Real.pi) := by
      rcases lt_or_gt_of_ne homega with hneg | hpos
      · refine ⟨-(2 * Real.pi / omega), ?_, -1, ?_⟩
        · have hdiv : 2 * Real.pi / omega < 0 :=
            div_neg_of_pos_of_neg (by positivity) hneg
          linarith
        push_cast
        field_simp
      · refine ⟨2 * Real.pi / omega, by positivity, 1, ?_⟩
        push_cast
        field_simp
    obtain ⟨n, hn⟩ := exists_nat_gt (t₀ / T)
    let tau : ℝ := (n : ℝ) * T
    have ht₀tau : t₀ ≤ tau := by
      exact le_of_lt ((div_lt_iff₀ hT).mp hn)
    have hturn : tau * omega = (((n : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
      dsimp only [tau]
      calc
        (n : ℝ) * T * omega = (n : ℝ) * (omega * T) := by ring
        _ = (n : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by rw [hperiod]
        _ = (((n : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
          push_cast
          ring
    refine ⟨tau, ht₀tau, ?_⟩
    apply observerPhaseEnergy_eq_zero_of_rootChordEnergy_eq_zero
      lam block hlam
    · exact finiteObserverHamiltonianVertexPhase_norm tau energy
    · apply hroot_of_phase
      rw [finiteObserverHamiltonianVertexPhase_pair_eq_gapPhase_real]
      apply Complex.exp_eq_one_iff.mpr
      refine ⟨(n : ℤ) * m, ?_⟩
      rw [show energy v - energy r = omega by rfl, hturn]
      push_cast
      ring

theorem tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_one
    {d : ℕ} {J : Type*} [Fintype J]
    (lam : J → ℝ) (block : J → Fin d → Fin d → ℂ)
    (hlam : ∀ a, 0 ≤ lam a) (energy : Fin d → ℝ)
    (hcap : Fintype.card
      (graphNonRoot (finiteObserverCoherenceGraph lam block)) = 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto
      (fun delta : ℝ => Real.log
          (finiteQuantumObserverReturnTime lam block energy t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨tau, htau, hzero⟩ :=
    exists_observerPhaseEnergy_exact_zero_of_capacity_one
      lam block hlam energy hcap ht₀
  simpa only [finiteQuantumObserverReturnTime] using
    GaloisForLFunctions.HTGeometry.tendsto_log_scalarSignalReturnTime_zero_of_exact_zero
      (fun t => finiteQuantumObserverPhaseEnergy lam
        (finiteObserverHamiltonianVertexPhase t energy) block)
      ht₀ htau hzero

/-- Exact physical first-return law for every finite observer whose visible phase capacity is at
least two. -/
def HasExactFiniteObserverFirstReturnLaw {d : ℕ} (energy : Fin d → ℝ) : Prop :=
  ∀ (j : ℕ) (lam : Fin j → ℝ) (block : Fin j → Fin d → Fin d → ℂ),
    (∀ a, 0 ≤ lam a) →
    ∀ (_hcap : 2 ≤ Fintype.card
      (graphNonRoot (finiteObserverCoherenceGraph lam block)))
      {t₀ : ℝ}, 0 < t₀ →
      Tendsto
        (fun delta : ℝ => Real.log
            (finiteQuantumObserverReturnTime lam block energy t₀ delta) /
          Real.log (1 / delta))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((Fintype.card
          (graphNonRoot (finiteObserverCoherenceGraph lam block)) - 1 : ℕ) : ℝ) / 2))

theorem hasExactFiniteObserverFirstReturnLaw_of_allGraphExtremal
    {d : ℕ} (energy : Fin d → ℝ) (henergy : StrictMono energy)
    (hgood : ∀ (G : SimpleGraph (Fin d))
      (hcap : 2 ≤ Fintype.card (graphNonRoot G)),
      ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G energy (canonicalObserverGraphEquiv G hcap) 1)
          0 1 (fun k => k.succ.succ))) :
    HasExactFiniteObserverFirstReturnLaw energy := by
  intro j lam block hlam hcap t₀ ht₀
  let G := finiteObserverCoherenceGraph lam block
  let e := Fintype.card (graphNonRoot G) - 2
  let q : Fin (e + 2) ≃ graphNonRoot G := canonicalObserverGraphEquiv G hcap
  let sigma := observerGraphClockSign G q
  have hsigma : sigma = 1 ∨ sigma = -1 :=
    observerGraphClockSign_eq_one_or_neg_one G q
  have hsigmane : sigma ≠ 0 := observerGraphClockSign_ne_zero G q
  have hgap : 0 < observerVirtualEnergy G energy q sigma 1 -
      observerVirtualEnergy G energy q sigma 0 :=
    observerVirtualEnergy_clockGap_pos_of_strictMono G energy henergy q
  have hnvOne := hgood G hcap
  have hnv :
      ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G energy q sigma) 0 1 (fun k => k.succ.succ)) := by
    rw [← observerGraphGapRatioMap_eq_virtual G energy q sigma hsigmane,
      observerGraphGapRatioMap_eq_virtual G energy q 1 one_ne_zero]
    exact hnvOne
  have hmain := tendsto_log_finiteQuantumObserverReturnTime_of_graphNonVWA
    lam block hlam energy q sigma hsigma hgap hnv ht₀
  have hexponent : e + 1 = Fintype.card (graphNonRoot G) - 1 := by
    have hcapG : 2 ≤ Fintype.card (graphNonRoot G) := by
      simpa only [G] using hcap
    dsimp [e]
    omega
  rw [hexponent] at hmain
  simpa only [G] using hmain

/-- Universal observer law, including the zero- and one-dimensional phase boundaries.  Visible
capacity `r` has exact logarithmic first-return exponent `(r - 1) / 2`, where natural subtraction
makes both boundary exponents zero. -/
def HasUniversalFiniteObserverFirstReturnLaw {d : ℕ} (energy : Fin d → ℝ) : Prop :=
  ∀ (j : ℕ) (lam : Fin j → ℝ) (block : Fin j → Fin d → Fin d → ℂ),
    (∀ a, 0 ≤ lam a) →
    ∀ {t₀ : ℝ}, 0 < t₀ →
      Tendsto
        (fun delta : ℝ => Real.log
            (finiteQuantumObserverReturnTime lam block energy t₀ delta) /
          Real.log (1 / delta))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((Fintype.card
          (graphNonRoot (finiteObserverCoherenceGraph lam block)) - 1 : ℕ) : ℝ) / 2))

theorem hasUniversalFiniteObserverFirstReturnLaw_of_allGraphExtremal
    {d : ℕ} (energy : Fin d → ℝ) (henergy : StrictMono energy)
    (hgood : ∀ (G : SimpleGraph (Fin d))
      (hcap : 2 ≤ Fintype.card (graphNonRoot G)),
      ¬ GaloisForLFunctions.HTGeometry.KleinbockMargulis.VWA
        (GaloisForLFunctions.HTGeometry.anchoredGapRatioMap
          (observerVirtualEnergy G energy (canonicalObserverGraphEquiv G hcap) 1)
          0 1 (fun k => k.succ.succ))) :
    HasUniversalFiniteObserverFirstReturnLaw energy := by
  have hlarge := hasExactFiniteObserverFirstReturnLaw_of_allGraphExtremal
    energy henergy hgood
  intro j lam block hlam t₀ ht₀
  let r := Fintype.card
    (graphNonRoot (finiteObserverCoherenceGraph lam block))
  by_cases hzero : r = 0
  · have hmain := tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_zero
      lam block hlam energy (by simpa only [r] using hzero) ht₀
    simpa only [r, hzero, Nat.zero_sub, Nat.cast_zero, zero_div] using hmain
  · by_cases hone : r = 1
    · have hmain := tendsto_log_finiteQuantumObserverReturnTime_zero_of_capacity_one
        lam block hlam energy (by simpa only [r] using hone) ht₀
      simpa only [r, hone, Nat.reduceSub, Nat.cast_zero, zero_div] using hmain
    · have htwo : 2 ≤ Fintype.card
          (graphNonRoot (finiteObserverCoherenceGraph lam block)) := by
        change 2 ≤ r
        omega
      exact hlarge j lam block hlam htwo ht₀

/-- **Almost every escaping simple-spectrum Hamiltonian obeys the exact first-return exponent for
every finite observer chosen after the Hamiltonian.** -/
theorem ae_hasExactFiniteObserverFirstReturnLaw
    {N d : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty)
    (hUsimple : U ⊆ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP) :
    ∀ᵐ theta, theta ∈ U →
      HasExactFiniteObserverFirstReturnLaw
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) := by
  have hgood := ae_all_observerGraphGapRatio_not_vwa
    hP hS hU hUc hUne hUsimple
  filter_upwards [hgood] with theta htheta hthetaU
  have hmono : Monotone
      (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) := by
    exact GaloisForLFunctions.HTGeometry.monotone_sortedTuple _
  have hinj := GaloisForLFunctions.HTGeometry.injective_sortedEnsembleSpectrum
    hP (hUsimple hthetaU)
  exact hasExactFiniteObserverFirstReturnLaw_of_allGraphExtremal
    (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
    (hmono.strictMono_of_injective hinj)
    (htheta hthetaU)

/-- Almost every Hamiltonian in an escaping simple-spectrum chart obeys the universal observer
law simultaneously for every finite observer, including both zero-exponent boundary ranks. -/
theorem ae_hasUniversalFiniteObserverFirstReturnLaw
    {N d : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P)))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty)
    (hUsimple : U ⊆ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP) :
    ∀ᵐ theta, theta ∈ U →
      HasUniversalFiniteObserverFirstReturnLaw
        (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) := by
  have hgood := ae_all_observerGraphGapRatio_not_vwa
    hP hS hU hUc hUne hUsimple
  filter_upwards [hgood] with theta htheta hthetaU
  have hmono : Monotone
      (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) :=
    GaloisForLFunctions.HTGeometry.monotone_sortedTuple _
  have hinj := GaloisForLFunctions.HTGeometry.injective_sortedEnsembleSpectrum
    hP (hUsimple hthetaU)
  exact hasUniversalFiniteObserverFirstReturnLaw_of_allGraphExtremal
    (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
    (hmono.strictMono_of_injective hinj)
    (htheta hthetaU)

/-- On the full simple-spectrum locus, failure of the simultaneous universal observer law is
Lebesgue-null. -/
theorem ae_hasUniversalFiniteObserverFirstReturnLaw_simpleLocus
    {N d : ℕ} {P : Fin N → Matrix (Fin d) (Fin d) ℂ} [NeZero N]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : GaloisForLFunctions.HTGeometry.SpectrumEscapesRealRelations
      (Set.range (GaloisForLFunctions.HTGeometry.spectralEnsembleMatrix P))) :
    ∀ᵐ theta,
      theta ∈ GaloisForLFunctions.HTGeometry.simpleEnsembleLocus hP →
        HasUniversalFiniteObserverFirstReturnLaw
          (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) := by
  have hgood := ae_all_observerGraphGapRatio_not_vwa_simpleLocus hP hS
  filter_upwards [hgood] with theta htheta hthetaSimple
  have hmono : Monotone
      (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta) :=
    GaloisForLFunctions.HTGeometry.monotone_sortedTuple _
  have hinj := GaloisForLFunctions.HTGeometry.injective_sortedEnsembleSpectrum
    hP hthetaSimple
  exact hasUniversalFiniteObserverFirstReturnLaw_of_allGraphExtremal
    (GaloisForLFunctions.HTGeometry.sortedEnsembleSpectrum hP theta)
    (hmono.strictMono_of_injective hinj)
    (htheta hthetaSimple)

end

end RHTower
