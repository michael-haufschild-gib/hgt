import GaloisForLFunctions.HTGeometry.QuditPathChainEscape
import GaloisForLFunctions.HTGeometry.SpectralRecurrenceExponentLaw

/-!
# The sharp discrete recurrence exponent of a generic local qudit chain

The escape property of the chain's exact onsite-plus-nearest-neighbour Hamiltonian space, written in
canonical real coordinates on the levels of the chain, makes the anchored gap map nondegenerate, and
the first-hit exponent law then pins the discrete recurrence exponent of almost every chain
Hamiltonian to the projective dimension `q^n - 1`.

## Main results

* `exists_ne_zero_of_spectrumEscapes` — an escaping family contains a nonzero matrix.
* `exists_quditPathChain_discreteRecurrenceExponent` — **the discrete exponent law**.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A family escaping real relations on a carrier with at least two states contains a nonzero
matrix: the zero matrix has an entirely degenerate characteristic root. -/
theorem exists_ne_zero_of_spectrumEscapes {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : 2 ≤ Fintype.card I) {S : Set (Matrix I I ℂ)}
    (hS : SpectrumEscapesAffineRelations S) :
    ∃ H ∈ S, H ≠ 0 := by
  classical
  obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (α := I) (by omega)
  set c : I → ℝ := fun i => (if i = i₀ then 1 else 0) - (if i = i₁ then 1 else 0) with hc
  have hbalanced : ∑ i, c i = 0 := by
    rw [hc]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i₀,
      Finset.sum_ite_eq' Finset.univ i₁]
    simp
  have hcne : c ≠ 0 := by
    intro h
    have hval := congrFun h i₀
    rw [hc] at hval
    simp [if_neg hne] at hval
  obtain ⟨H, hHS, E, hEinj, hEroot, -⟩ := hS c hbalanced hcne 0
  refine ⟨H, hHS, ?_⟩
  intro hzero
  have hE : ∀ i, E i = 0 := by
    intro i
    have hroot := hEroot i
    rw [hzero] at hroot
    have hpow : matrixCharpolyRelation ((0 : Matrix I I ℂ), ((E i : ℝ) : ℂ))
        = ((E i : ℝ) : ℂ) ^ Fintype.card I := by
      show (Matrix.scalar I ((E i : ℝ) : ℂ) - 0).det = _
      rw [sub_zero, Matrix.scalar_apply, Matrix.det_diagonal]
      simp
    rw [hpow] at hroot
    have hzero' : ((E i : ℝ) : ℂ) = 0 := pow_eq_zero_iff (by omega) |>.mp hroot
    exact_mod_cast hzero'
  exact hne (hEinj ((hE i₀).trans (hE i₁).symm))

/-- A simple real characteristic-root packet makes the canonical eigenvalue enumeration
injective. -/
theorem hermitianEigenvalues_injective_of_rootPacket {I : Type*} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (E : I → ℝ) (hEinj : Function.Injective E)
    (hroot : ∀ i, matrixCharpolyRelation (H, ((E i : ℝ) : ℂ)) = 0) :
    Function.Injective hH.eigenvalues := by
  classical
  set packet : Multiset ℂ := Finset.univ.val.map (fun i => ((E i : ℝ) : ℂ)) with hpacket
  have hnodup : packet.Nodup :=
    Finset.univ.nodup.map (fun a b h => hEinj (Complex.ofReal_injective h))
  have hcharNe : H.charpoly ≠ 0 := H.charpoly_monic.ne_zero
  have hle : packet ≤ H.charpoly.roots := by
    rw [Multiset.le_iff_subset hnodup]
    intro z hz
    rcases Multiset.mem_map.mp hz with ⟨i, -, rfl⟩
    rw [Polynomial.mem_roots hcharNe]
    change H.charpoly.eval ((E i : ℝ) : ℂ) = 0
    rw [Matrix.eval_charpoly]
    exact hroot i
  have hrootsCard : H.charpoly.roots.card = Fintype.card I := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits H.charpoly)]
    exact H.charpoly_natDegree_eq_dim
  have hpacketCard : packet.card = Fintype.card I := by simp [hpacket]
  have heq : packet = H.charpoly.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hrootsCard, hpacketCard])
  have heig : Finset.univ.val.map (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) = H.charpoly.roots :=
    hermitianEigenvalues_rootMultiset hH
  have hnodupEig : (Finset.univ.val.map (fun i => ((hH.eigenvalues i : ℝ) : ℂ))).Nodup := by
    rw [heig, ← heq]
    exact hnodup
  intro a b hab
  refine Multiset.inj_on_of_nodup_map hnodupEig a (Finset.mem_univ a) b (Finset.mem_univ b) ?_
  exact_mod_cast hab

/-- **A family escaping real relations has a simple-spectrum chart.**  The escape witness has a
simple spectrum, and the simple locus is open, so it contains a ball. -/
theorem exists_chart_of_spectrumEscapes {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hD : 2 ≤ D) (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P))) :
    ∃ U : Set (Fin N → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP := by
  classical
  obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card (α := Fin D) (by rw [Fintype.card_fin]; omega)
  set c : Fin D → ℝ := fun i => (if i = i₀ then 1 else 0) - (if i = i₁ then 1 else 0) with hc
  have hbalanced : ∑ i, c i = 0 := by
    rw [hc]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i₀,
      Finset.sum_ite_eq' Finset.univ i₁]
    simp
  have hcne : c ≠ 0 := by
    intro h
    have hval := congrFun h i₀
    rw [hc] at hval
    simp [if_neg hne] at hval
  obtain ⟨M, ⟨θ, rfl⟩, E, hEinj, hEroot, -⟩ := hS c hbalanced hcne 0
  have hθ : θ ∈ simpleEnsembleLocus hP := by
    exact hermitianEigenvalues_injective_of_rootPacket
      (isHermitian_spectralEnsembleMatrix hP θ) E hEinj hEroot
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_simpleEnsembleLocus hP) θ hθ
  exact ⟨Metric.ball θ r, Metric.isOpen_ball, Metric.isPreconnected_ball,
    ⟨θ, Metric.mem_ball_self hr⟩, hball⟩

/-- **The open qudit chain in canonical coordinates.**  Its exact onsite-plus-nearest-neighbour
Hamiltonian space, relabelled by the levels of the chain, is a nonzero real-affine Hermitian family
escaping every constant real relation among the energies. -/
theorem exists_quditPathChain_coordinateFamily (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ D : ℕ, q ^ n = D ∧ 4 ≤ D ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical) (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin D)
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin D) (Fin D) ℂ) (_hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a =
          Matrix.reindex eSt eSt
            (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)) := by
  classical
  obtain ⟨Physical, Observer, instP, instPd, T, eObs, hgraph, hcard, hescape⟩ :=
    exists_quditPathChain_spectrumEscapes n q hn hq
  letI := instP
  letI := instPd
  have hq4 : 4 ≤ q ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  refine ⟨q ^ n, rfl, hq4, Physical, Observer, instP, instPd, T, eObs, hgraph, ?_⟩
  set L := T.hermitianLocalHamiltonianSubmodule with hL
  have hLself : L ≤ selfAdjoint.submodule ℝ (Matrix Physical Physical ℂ) :=
    T.hermitianLocalHamiltonianSubmodule_le_selfAdjoint
  set eSt : Physical ≃ Fin (q ^ n) := Fintype.equivFinOfCardEq hcard with heSt
  set gen := realMatrixSubmoduleGenerator L with hgen
  set P : Fin (Module.finrank ℝ L) → Matrix (Fin (q ^ n)) (Fin (q ^ n)) ℂ :=
    fun a => Matrix.reindex eSt eSt (gen a) with hP
  have hPHermitian : ∀ a, (P a).IsHermitian := by
    intro a
    rw [hP]
    exact (Matrix.isHermitian_reindex_iff eSt).mpr
      (realMatrixSubmoduleGenerator_isHermitian L hLself a)
  have hNeZero : NeZero (Module.finrank ℝ L) := by
    refine ⟨?_⟩
    obtain ⟨H, hHmem, hHne⟩ :=
      exists_ne_zero_of_spectrumEscapes (I := Physical) (by omega) (hL ▸ hescape)
    have hpos : 0 < Module.finrank ℝ L :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨H, hHmem⟩, fun h0 => hHne (congrArg Subtype.val h0)⟩
    omega
  have hfamily : SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)) := by
    refine (hescape.ofSubmodule (L := L)).reindex eSt ?_
    rintro M ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    ext i j
    simp [spectralEnsembleMatrix, realAffineMatrix, Matrix.reindex, hP, hgen,
      Matrix.sum_apply, Matrix.smul_apply]
  exact ⟨eSt, hNeZero, P, hPHermitian, fun a => rfl, hfamily⟩

/-- **The sharp discrete recurrence exponent of a generic local qudit chain.**  For an open chain of
`n ≥ 2` sites with `q ≥ 2` levels each, on every preconnected open chart of simple-spectrum
Hamiltonians in the exact onsite-plus-nearest-neighbour coefficient space, almost every Hamiltonian
has first-return exponent exactly `q^n - 1` for its projective gap phases. -/
theorem exists_quditPathChain_discreteRecurrenceExponent (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ d : ℕ, q ^ n = d + 1 ∧ 0 < d ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical) (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin (d + 1))
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a =
          Matrix.reindex eSt eSt
            (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        (∃ U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
          IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP) ∧
        ∀ {U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ)},
          IsOpen U → IsPreconnected U → U.Nonempty →
          U ⊆ simpleEnsembleLocus hP →
          ∀ᵐ x, x ∈ U →
            Tendsto
              (fun r : ℝ =>
                Real.log
                    (firstHit
                      (anchoredGapMap (2 * Real.pi) (sortedEnsembleSpectrum hP x) 0 Fin.succ) r)
                  / Real.log (1 / r))
              (𝓝[>] (0 : ℝ)) (𝓝 (d : ℝ)) := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily n q hn hq
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  letI := instP
  letI := instPd
  haveI := hNeZero
  refine ⟨d, hD, by omega, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hPHermitian, hprov,
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily, ?_⟩
  intro U hU hUc hUne hUsimple
  exact ae_tendsto_log_firstHit_sortedGap (by omega) hPHermitian hfamily
    (Fin.succ_injective _) (fun k => Fin.succ_ne_zero k) (by positivity) hU hUc hUne hUsimple

/-- **The sharp winding recurrence exponent.**  Anchoring the projective phases at the lowest level
and using the first gap as the clock loses exactly one dimension: almost every Hamiltonian of the
chart has winding first-return exponent `q^n - 2`. -/
theorem exists_quditPathChain_windingRecurrenceExponent (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ e : ℕ, q ^ n = e + 3 ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical) (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      ∃ (eSt : Physical ≃ Fin (e + 3))
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin (e + 3)) (Fin (e + 3)) ℂ) (hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a =
          Matrix.reindex eSt eSt
            (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        (∃ U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ),
          IsOpen U ∧ IsPreconnected U ∧ U.Nonempty ∧ U ⊆ simpleEnsembleLocus hP) ∧
        ∀ {U : Set (Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) → ℝ)},
          IsOpen U → IsPreconnected U → U.Nonempty →
          U ⊆ simpleEnsembleLocus hP →
          ∀ᵐ x, x ∈ U →
            Tendsto
              (fun r : ℝ =>
                Real.log
                    (firstHit
                      (anchoredGapRatioMap (sortedEnsembleSpectrum hP x) 0 1
                        (fun k => k.succ.succ)) r)
                  / Real.log (1 / r))
              (𝓝[>] (0 : ℝ)) (𝓝 ((e + 1 : ℕ) : ℝ)) := by
  obtain ⟨D, hD, hD4, Physical, Observer, instP, instPd, T, eObs, hgraph,
      eSt, hNeZero, P, hPHermitian, hprov, hfamily⟩ :=
    exists_quditPathChain_coordinateFamily n q hn hq
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 3 := ⟨D - 3, by omega⟩
  letI := instP
  letI := instPd
  haveI := hNeZero
  refine ⟨e, hD, Physical, Observer, instP, instPd, T, eObs, hgraph,
    eSt, hNeZero, P, hPHermitian, hprov,
    exists_chart_of_spectrumEscapes (by omega) hPHermitian hfamily, ?_⟩
  intro U hU hUc hUne hUsimple
  refine ae_tendsto_log_firstHit_sortedGapRatio (n := e + 1) (by omega) hPHermitian
    hfamily.toRealRelations ?_ ?_ ?_ ?_ hU hUc hUne hUsimple
  · intro a b hab
    exact Fin.succ_injective _ (Fin.succ_injective _ hab)
  · intro k
    exact Fin.succ_ne_zero _
  · intro k
    have h1 : (1 : Fin (e + 3)) = Fin.succ (0 : Fin (e + 2)) := rfl
    rw [h1]
    intro hk
    exact Fin.succ_ne_zero k (Fin.succ_injective _ hk)
  · intro h01
    exact zero_ne_one h01

end

end GaloisForLFunctions.HTGeometry
