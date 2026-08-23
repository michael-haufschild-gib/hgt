/-
# Complexity onset and quantum-recurrence dimension are independent

The incubation law already produces, at every prescribed delay, one exactly cubic-phase-preparable
seed and a shell set of definite measure carrying arbitrary finite-time incubation, a maximally
independent projective spectrum, optimal spectral capacity, a full later plateau, later
low-complexity recurrence, and no weak spatial bond.  Removing two further null sets of directions
-- the Diophantine-exceptional ones and those for which the seed is not cyclic -- adds the maximal
continuous recurrence dimension `(D-2)/2` without changing the measure bound, and the two-local
Pauli support of the shell Hamiltonian adds the permanent local separator from Haar randomness.

Since the recurrence exponent, the capacity, the plateau and the locality witness do not involve the
delay, none of them bounds the onset.

Main results:
* `chainAnchor`, `chainClock`, `chainLevelIndex` — the level indexing of the sorted chain spectrum.
* `tendsto_log_orbitFidelityReturnTime_patch` — **equation `(6)` for the patch family**.
* `hasPauliWeightAtMost_pathHamiltonian`, `productStabilizerTwoQuery_patch_gt_haarBenchmark` —
  **clause 7**.
* `onsetGoodSet`, `toSphere_restrict_onsetGoodSet` — the extra exclusions are free.
* `exists_onsetRecurrence_dimension_independence` — **the theorem**.
-/
import GaloisForLFunctions.HTGeometry.OrbitFidelityRecurrenceExponent
import GaloisForLFunctions.HTGeometry.ChainVwaSphereNull
import GaloisForLFunctions.HTGeometry.ChainCyclicSeedGenericity
import GaloisForLFunctions.HTGeometry.CubicSeedPhaseCompiler
import GaloisForLFunctions.HTGeometry.PauliWeightWitnesses
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw

open Matrix Finset Metric MeasureTheory Filter Topology _root_.HTGeometry
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedVariables false

noncomputable section

set_option linter.unusedSectionVars false

/-! ## The level indexing of the sorted chain spectrum -/

variable {k : ℕ}

/-- The anchor level of the sorted chain spectrum. -/
def chainAnchor (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) : Fin (2 ^ (k + 3)) :=
  (finCongr h).symm 0

/-- The clock level of the sorted chain spectrum. -/
def chainClock (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) : Fin (2 ^ (k + 3)) :=
  (finCongr h).symm 1

/-- The remaining levels of the sorted chain spectrum. -/
def chainLevelIndex (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) :
    Fin ((2 ^ (k + 3) - 3) + 1) → Fin (2 ^ (k + 3)) :=
  fun m => (finCongr h).symm m.succ.succ

theorem chainLevelIndex_injective (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) :
    Function.Injective (chainLevelIndex h) := fun a b hab =>
  Fin.succ_injective _ (Fin.succ_injective _ ((finCongr h).symm.injective hab))

theorem chainLevelIndex_ne_anchor (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3)
    (m : Fin ((2 ^ (k + 3) - 3) + 1)) : chainLevelIndex h m ≠ chainAnchor h := by
  intro hcon
  have hval := (finCongr h).symm.injective hcon
  exact Fin.succ_ne_zero _ hval

theorem chainLevelIndex_ne_clock (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3)
    (m : Fin ((2 ^ (k + 3) - 3) + 1)) : chainLevelIndex h m ≠ chainClock h := by
  intro hcon
  have hval := (finCongr h).symm.injective hcon
  have hv := congrArg Fin.val hval
  rw [Fin.val_succ, Fin.val_succ, Fin.val_one] at hv
  omega

theorem chainAnchor_ne_chainClock (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) :
    chainAnchor h ≠ chainClock h := by
  intro hcon
  have hval := (finCongr h).symm.injective hcon
  have hv := congrArg Fin.val hval
  rw [Fin.val_zero, Fin.val_one] at hv
  omega

theorem chainAnchor_le_chainClock (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) :
    chainAnchor h ≤ chainClock h := by
  rw [chainAnchor, chainClock, Fin.le_def]
  simp only [finCongr_symm_apply, Fin.val_cast]
  rw [Fin.val_zero, Fin.val_one]
  omega

/-! ## Equation `(6)` for the patch family -/

/-- **The maximal continuous recurrence dimension of a good patch direction.**  Outside the
degenerate, the Diophantine-exceptional and the non-cyclic directions, the first fidelity return of
the cubic seed after a positive cutoff has logarithmic exponent exactly `(D-2)/2`. -/
theorem tendsto_log_orbitFidelityReturnTime_patch (k : ℕ)
    (h : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3)
    (c : MonLe (Fin (k + 3)) 3 → ZMod 8) {ω : PatchSphere k}
    (hbad : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k)
    (hvwa : ω ∉ patchToCoeff k ⁻¹' chainVwaSphere k (chainAnchor h) (chainClock h)
      (chainLevelIndex h))
    (hkry : ω ∉ patchToCoeff k ⁻¹'
      krylovDegenerateSphere (chainPauliFin (k + 3)) (cubicSeed (k + 3) c))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun δ : ℝ => Real.log (orbitFidelityReturnTime
        (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
        (registerCubicSeed k c) t₀ δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 2 : ℕ) : ℝ) / 2)) := by
  classical
  set S : Fin (2 ^ (k + 3)) → ℝ :=
    sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
      (sphereCoeff (patchToCoeff k ω)) with hSdef
  set ρ : FiniteQubitConfiguration (Fin (k + 3)) ≃ Fin ((2 ^ (k + 3) - 3) + 3) :=
    (qubitConfigFin (k + 3)).trans (finCongr h) with hρdef
  have hlam : ∀ i : Fin ((2 ^ (k + 3) - 3) + 3),
      patchEigenValues k ω (ρ.symm i) = S ((finCongr h).symm i) := by
    intro i
    rw [patchEigenValues, hSdef, hρdef]
    show spectralTuple (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))
        ((qubitConfigFin (k + 3)) (((qubitConfigFin (k + 3)).trans (finCongr h)).symm i)) = _
    rw [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    rfl
  have hsimple : Function.Injective S := by
    have hinj := mem_simpleLocus_of_notMem_chainBadSphere hbad
    exact injective_sortedTuple hinj
  have hgap : patchEigenValues k ω (ρ.symm 0) < patchEigenValues k ω (ρ.symm 1) := by
    rw [hlam 0, hlam 1]
    refine lt_of_le_of_ne ?_ ?_
    · exact monotone_sortedTuple _ (chainAnchor_le_chainClock h)
    · intro hcon
      exact chainAnchor_ne_chainClock h (hsimple hcon)
  have hkry' : (ensembleKrylov (chainPauliFin (k + 3)) (cubicSeed (k + 3) c)
      (sphereCoeff (patchToCoeff k ω))).det ≠ 0 := hkry
  have hcyc : ∀ j, finiteComplexInner (patchEigenBasis k ω j) (registerCubicSeed k c) ≠ 0 :=
    finiteComplexInner_patchEigenBasis_ne_zero k c hkry'
  have hnv : ¬ KleinbockMargulis.VWA
      (anchoredGapRatioMap (fun i => patchEigenValues k ω (ρ.symm i)) 0 1
        (fun m => m.succ.succ)) := by
    have hmapeq : (anchoredGapRatioMap (fun i => patchEigenValues k ω (ρ.symm i)) 0 1
        (fun m => m.succ.succ))
        = anchoredGapRatioMap S (chainAnchor h) (chainClock h) (chainLevelIndex h) := by
      funext m
      rw [anchoredGapRatioMap, anchoredGapRatioMap, hlam, hlam, hlam]
      rfl
    rw [hmapeq]
    exact hvwa
  have hmain := tendsto_log_orbitFidelityReturnTime ρ (isOrthoEigenBasis_patchEigenBasis ω)
    (finiteComplexInner_registerCubicSeed c) hcyc hgap hnv ht₀
  have hval : (((2 ^ (k + 3) - 3) + 1 : ℕ) : ℝ) = ((2 ^ (k + 3) - 2 : ℕ) : ℝ) := by
    have h8 : 8 ≤ 2 ^ (k + 3) := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    congr 1
    omega
  rw [hval] at hmain
  exact hmain

/-! ## Equation for clause 7: permanent non-Haar locality -/

theorem finitePauliWeight_pathWord_le (n : ℕ) (l : PathLabel n) :
    finitePauliWeight (pathWord l) ≤ 2 := by
  classical
  rcases l with sq | eab
  · refine le_trans (Finset.card_le_card
      (t := ({sq.1} : Finset (Fin (n + 2)))) ?_) ?_
    · show (Finset.univ.filter fun t => pathWord (Sum.inl sq) t ≠ none)
        ⊆ ({sq.1} : Finset (Fin (n + 2)))
      intro t ht
      rw [Finset.mem_filter] at ht
      have hval : (if t = sq.1 then some sq.2 else none) ≠ none := ht.2
      by_cases hts : t = sq.1
      · simp [hts]
      · rw [if_neg hts] at hval
        exact absurd rfl hval
    · simp
  · refine le_trans (Finset.card_le_card
      (t := ({eab.1.castSucc, eab.1.succ} : Finset (Fin (n + 2)))) ?_) ?_
    · show (Finset.univ.filter fun t => pathWord (Sum.inr eab) t ≠ none)
        ⊆ ({eab.1.castSucc, eab.1.succ} : Finset (Fin (n + 2)))
      intro t ht
      rw [Finset.mem_filter] at ht
      have hval : (if t = eab.1.castSucc then some eab.2.1
        else if t = eab.1.succ then some eab.2.2 else none) ≠ none := ht.2
      by_cases h1 : t = eab.1.castSucc
      · simp [h1]
      · rw [if_neg h1] at hval
        by_cases h2 : t = eab.1.succ
        · simp [h2]
        · rw [if_neg h2] at hval
          exact absurd rfl hval
    · exact le_trans (Finset.card_insert_le _ _) (by simp)

/-- **The path-local Hamiltonian is two-local in Pauli support.** -/
theorem hasPauliWeightAtMost_pathHamiltonian {n : ℕ} (u : PathShell n)
    (hsa : IsSelfAdjoint (pathHamiltonian u)) :
    HasPauliWeightAtMost (Fin (n + 2)) 2 ⟨pathHamiltonian u, hsa⟩ := by
  classical
  intro P hP
  have hsum : (⟨pathHamiltonian u, hsa⟩ :
      selfAdjoint (Matrix (FiniteQubitConfiguration (Fin (n + 2)))
        (FiniteQubitConfiguration (Fin (n + 2))) ℂ))
      = ∑ l : PathLabel n, (u l) • finitePauliSelfAdjoint (pathWord l) := by
    apply Subtype.ext
    show pathHamiltonian u
        = ((∑ l : PathLabel n, (u l) • finitePauliSelfAdjoint (pathWord l) :
            selfAdjoint (Matrix (FiniteQubitConfiguration (Fin (n + 2)))
              (FiniteQubitConfiguration (Fin (n + 2))) ℂ)) :
          Matrix (FiniteQubitConfiguration (Fin (n + 2)))
            (FiniteQubitConfiguration (Fin (n + 2))) ℂ)
    rw [pathHamiltonian_eq_sum u, AddSubgroup.val_finsetSum]
    exact Finset.sum_congr rfl fun l _ => rfl
  rw [hsum, map_sum]
  rw [Finsupp.coe_finsetSum]
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_smul, ← finitePauliSelfAdjointBasis_apply,
    (finitePauliSelfAdjointBasis (Fin (n + 2))).repr_self]
  have hne : pathWord l ≠ P := by
    intro hcon
    have hle := finitePauliWeight_pathWord_le n l
    rw [hcon] at hle
    omega
  simp [hne]

/-- The path-local Hamiltonian of a simple-spectrum direction is nonzero. -/
theorem patchHamLM_ne_zero (k : ℕ) {ω : PatchSphere k}
    (hbad : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k) :
    (⟨patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)),
      isSelfAdjoint_patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))⟩ :
      selfAdjoint (Matrix (FiniteQubitConfiguration (Fin (k + 3)))
        (FiniteQubitConfiguration (Fin (k + 3))) ℂ)) ≠ 0 := by
  intro hzero
  have hmat : patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) = 0 :=
    congrArg Subtype.val hzero
  have heb := isOrthoEigenBasis_patchEigenBasis ω
  have hlamzero : ∀ j, patchEigenValues k ω j = 0 := by
    intro j
    have heigen := heb.eigen j
    rw [show pathHamiltonian (pathPatchIsometry (k + 1)
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
        = patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) from rfl,
      hmat, Matrix.zero_mulVec] at heigen
    have hnorm := heb.orth j j
    rw [if_pos rfl] at hnorm
    by_contra hne
    have hej : patchEigenBasis k ω j = 0 := by
      funext x
      have := congrFun heigen.symm x
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hne
      · exact h
    rw [hej] at hnorm
    simp [finiteComplexInner] at hnorm
  have hinj := (maximallyProjectiveEnergy_patchEigenValues hbad).injective
  have hx : (fun _ : Fin (k + 3) => false) ≠ (fun _ : Fin (k + 3) => true) := by
    intro hcon
    have := congrFun hcon ⟨0, by omega⟩
    simp at this
  exact hx (hinj (by rw [hlamzero, hlamzero]))

/-- **Clause 7 for the patch family.**  The fixed product-stabilizer two-query protocol separates
the propagator of a good patch direction from the exact Haar benchmark at every real time. -/
theorem productStabilizerTwoQuery_patch_gt_haarBenchmark (k : ℕ)
    {ω : PatchSphere k} (hbad : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k)
    (hsep : Fintype.card (FiniteQLocalPauliLabel (Fin (k + 3)) 2) * 3 ^ 2
      < 2 ^ Fintype.card (Fin (k + 3)) + 1) (t : ℝ) :
    1 / (((2 ^ Fintype.card (Fin (k + 3)) + 1 : ℕ) : ℝ))
      < productStabilizerTwoQueryProtocolSignal
        (fun P : FiniteQLocalPauliLabel (Fin (k + 3)) 2 => P.1)
        (finiteQLocalPauliTransferMatrix (Fin (k + 3)) 2
          ⟨patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)),
            isSelfAdjoint_patchHamLM k
              (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))⟩ t) :=
  finiteQLocalAutonomousTransferSignal_gt_haarBenchmark (Fin (k + 3)) 2 _
    (patchHamLM_ne_zero k hbad)
    (hasPauliWeightAtMost_pathHamiltonian (pathPatchIsometry (k + 1)
      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) _) t hsep

/-! ## The capstone -/

theorem measure_inter_compl_of_null {β : Type*} [MeasurableSpace β] {μ : Measure β}
    {A B : Set β} (hB : μ B = 0) : μ (A ∩ Bᶜ) = μ A := by
  rw [← Set.sdiff_eq]
  exact measure_sdiff_null hB

/-- The good directions of the onset–recurrence law: collision-good, nondegenerate, Diophantine
generic, and cyclic for the seed. -/
def onsetGoodSet (k : ℕ) (hD : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3) (kap : ℝ)
    (c : MonLe (Fin (k + 3)) 3 → ZMod 8) : Set (PatchSphere k) :=
  patchGood k kap c ∩ (patchToCoeff k ⁻¹' chainBadSphere k)ᶜ
    ∩ (patchToCoeff k ⁻¹' chainVwaSphere k (chainAnchor hD) (chainClock hD)
        (chainLevelIndex hD))ᶜ
    ∩ (patchToCoeff k ⁻¹' krylovDegenerateSphere (chainPauliFin (k + 3)) (cubicSeed (k + 3) c))ᶜ

theorem toSphere_restrict_onsetGoodSet (k : ℕ) (hD : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3)
    (kap : ℝ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    (T : Set (PatchSphere k)) :
    (((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).restrict
        T).real (onsetGoodSet k hD kap c)
      = (((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).restrict
        T).real (patchGood k kap c ∩ (patchToCoeff k ⁻¹' chainBadSphere k)ᶜ) := by
  classical
  set μ := ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).restrict
    T with hμ
  have hvwa0 : (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
      (patchToCoeff k ⁻¹' chainVwaSphere k (chainAnchor hD) (chainClock hD)
        (chainLevelIndex hD)) = 0 :=
    toSphere_preimage_chainVwaSphere_eq_zero k (by omega) (chainLevelIndex_injective hD)
      (chainLevelIndex_ne_anchor hD) (chainLevelIndex_ne_clock hD) (chainAnchor_ne_chainClock hD)
  have hkry0 : (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
      (patchToCoeff k ⁻¹' krylovDegenerateSphere (chainPauliFin (k + 3))
        (cubicSeed (k + 3) c)) = 0 := by
    rw [toSphere_preimage_patchToCoeff k
      (measurableSet_krylovDegenerateSphere (chainPauliFin (k + 3)) (cubicSeed (k + 3) c))]
    exact toSphere_krylovDegenerateSphere_eq_zero (chainPauliFin (k + 3)) (cubicSeed (k + 3) c)
      (exists_chainKrylov_witness k (cubicSeed_ne_zero (k + 3) c))
  have hvwaμ : μ (patchToCoeff k ⁻¹' chainVwaSphere k (chainAnchor hD) (chainClock hD)
      (chainLevelIndex hD)) = 0 :=
    le_antisymm (le_trans (Measure.restrict_apply_le _ _) (le_of_eq hvwa0)) (by positivity)
  have hkryμ : μ (patchToCoeff k ⁻¹' krylovDegenerateSphere (chainPauliFin (k + 3))
      (cubicSeed (k + 3) c)) = 0 :=
    le_antisymm (le_trans (Measure.restrict_apply_le _ _) (le_of_eq hkry0)) (by positivity)
  rw [Measure.real, Measure.real, onsetGoodSet, measure_inter_compl_of_null hkryμ,
    measure_inter_compl_of_null hvwaμ]

/-- **Complexity onset and quantum-recurrence dimension are independent.**  For every prescribed
delay there is one exactly cubic-phase-preparable seed and a shell set of definite measure on which
the orbit stays easy through the whole delay, while its projective spectrum is maximally
independent, its spectral capacity is optimal, its later complexity plateaus, its continuous
fidelity recurrence exponent is exactly `(D-2)/2`, it returns arbitrarily close to the seed, the
fixed local two-query protocol separates it from Haar randomness at every time, and no spatial bond
is weak. -/
theorem exists_onsetRecurrence_dimension_independence (k : ℕ)
    (hD : 2 ^ (k + 3) = (2 ^ (k + 3) - 3) + 3)
    {ρ r L eta epsMinus : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L) (heta : 0 < eta)
    (hgap : L * (Real.sqrt (Fintype.card (PathLabel (k + 1))) * r) ≤ epsMinus - eta)
    {kap : ℝ} (hkap : 0 < kap)
    {epsn epsw : ℝ} (hepsn : 0 ≤ epsn) (hegap : epsn < epsw) (hepsw : epsw < 1)
    {rr : ℕ} (hrr : 1 ≤ rr)
    (hscale : 16 * ((2 + kap) / regDim k) / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * rr))
    {C : Type} [Fintype C] [Nonempty C]
    (Z : C → (FiniteQubitConfiguration (Fin (k + 3)) → ℂ))
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {M : ℝ} (hM : 1 < M) {sc : ℕ} (hcardC : (Fintype.card C : ℝ) ≤ M ^ (sc + 1))
    (hs : ((sc : ℝ) + 1) * Real.log M ≤ ((rr : ℝ) / 2) * Real.log 2)
    (W : ℝ)
    (hW : ((plateauGridCount W ((epsw - epsn) /
        Real.sqrt (Fintype.card (PathLabel (k + 1)))) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((rr : ℝ) / 2)) < 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hsep : Fintype.card (FiniteQLocalPauliLabel (Fin (k + 3)) 2) * 3 ^ 2
      < 2 ^ Fintype.card (Fin (k + 3)) + 1) :
    ∃ m : ℕ, 0 < m ∧
      ∃ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        (1 - 96 / (kap ^ 2 * regDim k)) *
            ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).real
              (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)
          ≤ (((volume : Measure (PatchSpace (2 * (k + 1) + 3)
              (10 * (k + 1) + 12))).toSphere).restrict
              (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)).real
              (onsetGoodSet k hD kap c)
        ∧ ∀ ω ∈ patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r,
            ω ∈ onsetGoodSet k hD kap c →
            (∀ t : ℝ, 0 ≤ t → t ≤ L →
                approxComplexity (cubicDiagAct (k + 1) m) (eucVec (uniformSeed (k + 3))) epsMinus
                  (orbitState (patchHamLM k
                      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                    (eucVec (registerCubicSeed k c)) t)
                ≤ Fintype.card (MonLe (Fin (k + 3)) 3) + (2 * (k + 1) + 3))
            ∧ MaximallyProjectiveEnergy (patchEigenValues k ω)
            ∧ phaseCollision (patchEigenBasis k ω) (eighthPhase (polyEval 3 c))
                ≤ (2 + kap) / regDim k
            ∧ (∀ A : ℝ, ∃ t₁, A < t₁ ∧ ∀ u ∈ Set.Icc t₁ (t₁ + W),
                u ∉ metricEasySet
                  (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                  (registerCubicSeed k c) epsn Z)
            ∧ Tendsto (fun δ : ℝ => Real.log (orbitFidelityReturnTime
                  (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                  (registerCubicSeed k c) t₀ δ) / Real.log (1 / δ))
                (𝓝[>] (0 : ℝ)) (𝓝 (((2 ^ (k + 3) - 2 : ℕ) : ℝ) / 2))
            ∧ (∀ ρ' : ℝ, 0 < ρ' → ∀ A : ℝ, ∃ s' : ℝ, A < s' ∧ 1 - ρ' ≤ ‖finiteComplexInner
                (unitaryEvolution
                    (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) s' *ᵥ
                  registerCubicSeed k c) (registerCubicSeed k c)‖)
            ∧ (∀ t : ℝ, 1 / (((2 ^ Fintype.card (Fin (k + 3)) + 1 : ℕ) : ℝ))
                < productStabilizerTwoQueryProtocolSignal
                  (fun P : FiniteQLocalPauliLabel (Fin (k + 3)) 2 => P.1)
                  (finiteQLocalPauliTransferMatrix (Fin (k + 3)) 2
                    ⟨patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)),
                      isSelfAdjoint_patchHamLM k
                        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))⟩ t))
            ∧ (∀ e : Fin (k + 2),
                (Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ))⁻¹ - ρ - r
                  ≤ ‖edgePart (pathPatchIsometry (k + 1)
                      (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) e‖) := by
  classical
  obtain ⟨m, hmpos, c, hmeas, hall⟩ :=
    exists_incubating_cubicSeed_compiled k hρ hL heta hgap hkap hepsn hegap hepsw hrr hscale
      Z hZ hM hcardC hs W hW
  refine ⟨m, hmpos, c, ?_, ?_⟩
  · rw [toSphere_restrict_onsetGoodSet k hD kap c]
    exact hmeas
  · intro ω hωT hωgood
    obtain ⟨⟨⟨hgood, hbad⟩, hvwa⟩, hkry⟩ := hωgood
    obtain ⟨h1, h2, h3, h4, h6, h8⟩ := hall ω hωT hgood hbad
    exact ⟨h1, h2, h3, h4,
      tendsto_log_orbitFidelityReturnTime_patch k hD c hbad hvwa hkry ht₀,
      h6, fun t => productStabilizerTwoQuery_patch_gt_haarBenchmark k hbad hsep t, h8⟩

end

end GaloisForLFunctions.HTGeometry
