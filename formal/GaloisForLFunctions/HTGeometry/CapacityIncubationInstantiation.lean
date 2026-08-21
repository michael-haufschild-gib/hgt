/-
# The fully coupled sleeping-chaos family

Theorem A of the incubation law is abstract: a carrier patch, a uniform compiler, a density of
capacity seeds, a conull generic completion, and a completed-phase plateau.  All five certificates
are available for the nearest-neighbour Pauli shell read on the patch space of its diagonal
splitting, so the incubation law instantiates: one cubic-phase seed serves all but a `96/(κ²D)`
fraction of the tube over the diagonal cap, and every nondegenerate direction of that part is easy
through the whole prescribed delay while retaining full later capacity, recurrence and edge
coupling.

Main results:
* `patchHamLM`, `norm_patchHamLM_sub_le`, `norm_patchHam_le` — the shell map on the patch space.
* `registerCubicSeed`, `phaseCollision_le_of_good` — the seed and its collision.
* `toSphere_patchThickening_cap_ge`, `volume_patchAnnulus_cap_pos` — **`(9)`**.
* `exists_incubating_cubicSeed` — **Theorem B**.
-/
import GaloisForLFunctions.HTGeometry.PatchChainPullback
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow
import GaloisForLFunctions.HTGeometry.SeedOrbitRecurrence

open MeasureTheory Metric Set Matrix Filter
open scoped ENNReal
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

variable (k : ℕ)

/-- The shell Hamiltonian read on the patch space, as a real-linear map. -/
def patchHamLM (k : ℕ) :
    PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12) →ₗ[ℝ]
      Matrix (FiniteQubitConfiguration (Fin (k + 3))) (FiniteQubitConfiguration (Fin (k + 3))) ℂ :=
  (pathHamiltonianLM (k + 1)).comp (pathPatchIsometry (k + 1)).toLinearEquiv.toLinearMap

theorem patchHamLM_apply (p : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) :
    patchHamLM k p = pathHamiltonian (pathPatchIsometry (k + 1) p) := rfl

theorem isSelfAdjoint_patchHamLM (p : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) :
    IsSelfAdjoint (patchHamLM k p) := isSelfAdjoint_pathHamiltonian _

theorem norm_patchHamLM_sub_le (a b : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) :
    ‖patchHamLM k a - patchHamLM k b‖
      ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) * ‖a - b‖ := by
  have h := norm_pathHamiltonianLM_sub_le (pathPatchIsometry (k + 1) a)
    (pathPatchIsometry (k + 1) b)
  have hiso : ‖pathPatchIsometry (k + 1) a - pathPatchIsometry (k + 1) b‖ = ‖a - b‖ := by
    rw [← (pathPatchIsometry (k + 1)).map_sub, LinearIsometryEquiv.norm_map]
  rw [hiso] at h
  exact h

instance isFiniteMeasure_patchToSphere :
    IsFiniteMeasure ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere)
    := by
  constructor
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top


theorem sqrt_card_pathLabel_pos' {k : ℕ} :
    0 < Real.sqrt (Fintype.card (PathLabel (k + 1))) := by
  refine Real.sqrt_pos.mpr ?_
  have : 0 < Fintype.card (PathLabel (k + 1)) := Fintype.card_pos
  exact_mod_cast this

theorem norm_patchHam_le {k : ℕ} (ω : PatchSphere k) :
    ‖patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))‖
      ≤ Real.sqrt (Fintype.card (PathLabel (k + 1))) := by
  have hnorm : ‖(ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))‖ = 1 := by
    have h := ω.2
    rw [mem_sphere_iff_norm, sub_zero] at h
    exact h
  have h := norm_patchHamLM_sub_le k (ω : PatchSpace _ _) 0
  rw [map_zero, sub_zero, sub_zero, hnorm, mul_one] at h
  exact h

/-- The cubic phase seed on the register. -/
def registerCubicSeed (k : ℕ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    FiniteQubitConfiguration (Fin (k + 3)) → ℂ :=
  uniformPhaseSeed (eighthPhase (polyEval 3 c))

theorem finiteComplexInner_registerCubicSeed {k : ℕ} (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    finiteComplexInner (registerCubicSeed k c) (registerCubicSeed k c) = 1 := by
  have hs := sum_normSq_uniformPhaseSeed
    (α := FiniteQubitConfiguration (Fin (k + 3))) Fintype.card_pos
    (eighthPhase (polyEval 3 c))
  have hcast : finiteComplexInner (registerCubicSeed k c) (registerCubicSeed k c)
      = ((∑ x, ‖registerCubicSeed k c x‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [hcast, show (∑ x, ‖registerCubicSeed k c x‖ ^ 2 : ℝ) = 1 from hs]
  norm_num

theorem occupationCollision_eq_phaseCollision {k : ℕ} (c : MonLe (Fin (k + 3)) 3 → ZMod 8)
    (ω : PatchSphere k) :
    occupationCollision (fun j => ‖eigenCoords (patchEigenBasis k ω)
        (registerCubicSeed k c) j‖ ^ 2)
      = phaseCollision (patchEigenBasis k ω) (eighthPhase (polyEval 3 c)) := by
  rw [occupationCollision, phaseCollision]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eigenCoords, finitePureStateFidelity_comm, finitePureStateFidelity, ← pow_mul,
    registerCubicSeed, pow_mul]

/-- **`(5)` at the selected direction.**  A good, nondegenerate patch direction has small seed
collision. -/
theorem phaseCollision_le_of_good {k : ℕ} {kap : ℝ} {c : MonLe (Fin (k + 3)) 3 → ZMod 8}
    {ω : PatchSphere k} (hωg : ω ∈ patchGood k kap c)
    (hωb : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k) :
    phaseCollision (patchEigenBasis k ω) (eighthPhase (polyEval 3 c))
      ≤ (2 + kap) / regDim k := by
  have hsimple := mem_simpleLocus_of_notMem_chainBadSphere hωb
  have hmem : patchToCoeff k ω ∈
      goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
        ((2 + kap) / regDim k) ∪
      (simpleLocus (chainPauliFin_isHermitian (k + 3)))ᶜ := hωg
  rcases hmem with hgood | hbad
  · have hcc := crossCollision_cubicSeed k c hsimple
    have hle : crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
        (patchToCoeff k ω) ≤ (2 + kap) / regDim k := hgood.2
    rw [hcc] at hle
    exact hle
  · exact absurd hsimple hbad



/-- **`(9)` at the constructed patch.**  The thickening of the diagonal cap has surface measure at
least the carrier factor times `r^d`. -/
theorem toSphere_patchThickening_cap_ge (k : ℕ) {ρ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((Module.finrank ℝ (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) : ℝ≥0∞) *
        (volume (patchAnnulus (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ)) *
          (ENNReal.ofReal ((r / 8) ^ (10 * (k + 1) + 12)) *
            volume (ball (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12))) 1))))
      ≤ (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
          (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r) :=
  toSphere_patchThickening_ge (measurableSet_sphericalCap _ _) hr0 hr1

/-- The carrier factor of the diagonal cap is positive. -/
theorem volume_patchAnnulus_cap_pos (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < volume (patchAnnulus (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ)) :=
  volume_patchAnnulus_sphericalCap_pos (norm_uniformDir (by omega)) hρ

set_option maxHeartbeats 1000000 in
/-- **Theorem B: the fully coupled sleeping-chaos family.**  One cubic-phase seed serves all but a
`96/(κ²D)` fraction of the tube over the diagonal cap, and every nondegenerate direction of that
part is easy through the whole prescribed delay, has maximally projective spectrum and small seed
collision, is hard at every instant of arbitrarily late windows, recurs to the seed, and keeps every
spatial edge coupled. -/
theorem exists_incubating_cubicSeed (k : ℕ) {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    (chi : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (k + 3))))
    {ρ r L eta epsMinus : ℝ} {B : ℕ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hcert : ∀ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      ∀ y ∈ embedPatch (d := 10 * (k + 1) + 12)
        (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ),
      ∀ s : ℝ, ∃ w : List Γ, w.length ≤ B ∧
        dist (orbitState (patchHamLM k y) (eucVec (registerCubicSeed k c)) s)
          (wordAct act w chi) ≤ eta)
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
      (2 : ℝ) ^ (-((rr : ℝ) / 2)) < 1) :
    ∃ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      (1 - 96 / (kap ^ 2 * regDim k)) *
          ((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).real
            (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)
        ≤ (((volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere).restrict
            (patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r)).real
            (patchGood k kap c ∩ (patchToCoeff k ⁻¹' chainBadSphere k)ᶜ)
      ∧ ∀ ω ∈ patchThickening (sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ) r,
          ω ∈ patchGood k kap c → ω ∉ patchToCoeff k ⁻¹' chainBadSphere k →
          (∀ t : ℝ, 0 ≤ t → t ≤ L → approxComplexity act chi epsMinus
              (orbitState (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                (eucVec (registerCubicSeed k c)) t) ≤ B)
          ∧ MaximallyProjectiveEnergy (patchEigenValues k ω)
          ∧ phaseCollision (patchEigenBasis k ω) (eighthPhase (polyEval 3 c))
              ≤ (2 + kap) / regDim k
          ∧ (∀ A : ℝ, ∃ t₀, A < t₀ ∧ ∀ u ∈ Set.Icc t₀ (t₀ + W),
              u ∉ metricEasySet
                (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))
                (registerCubicSeed k c) epsn Z)
          ∧ (∀ ρ' : ℝ, 0 < ρ' → ∀ A : ℝ, ∃ s' : ℝ, A < s' ∧ 1 - ρ' ≤ ‖finiteComplexInner
              (unitaryEvolution
                  (patchHamLM k (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) s' *ᵥ
                registerCubicSeed k c) (registerCubicSeed k c)‖)
          ∧ (∀ e : Fin (k + 2),
              (Real.sqrt ((2 * (k + 1) + 3 : ℕ) : ℝ))⁻¹ - ρ - r
                ≤ ‖edgePart (pathPatchIsometry (k + 1)
                    (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))) e‖) := by
  classical
  obtain ⟨PU, hPUdef⟩ : ∃ PU, PU = sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := exists_seed_measureReal_ge
    (μ := (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere)
    (patchThickening PU r) (patchGood k kap)
    (fun q => measurableSet_patchGood kap q) (fun x => density_patchGood hkap x)
  refine ⟨c, ?_, ?_⟩
  · have hnull : (((volume : Measure (PatchSpace (2 * (k + 1) + 3)
        (10 * (k + 1) + 12))).toSphere).restrict (patchThickening PU r))
        ((patchToCoeff k ⁻¹' chainBadSphere k)ᶜ)ᶜ = 0 := by
      rw [compl_compl]
      have h1 := Measure.restrict_apply_le (μ := (volume : Measure (PatchSpace
        (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere) (patchThickening PU r)
        (patchToCoeff k ⁻¹' chainBadSphere k)
      rw [toSphere_preimage_chainBadSphere_eq_zero k] at h1
      exact le_antisymm h1 zero_le
    rw [← hPUdef, measureReal_inter_conull _ _ _ hnull]
    exact hc
  · intro ω hωt hωg hωb
    have hψunit : finiteComplexInner (registerCubicSeed k c) (registerCubicSeed k c) = 1 :=
      finiteComplexInner_registerCubicSeed c
    have hψnorm : ‖eucVec (registerCubicSeed k c)‖ = 1 := norm_eucVec_eq_one hψunit
    have hcoll := phaseCollision_le_of_good hωg hωb
    have heb := isOrthoEigenBasis_patchEigenBasis ω
    have hmax := maximallyProjectiveEnergy_patchEigenValues hωb
    refine ⟨?_, hmax, hcoll, ?_, ?_, ?_⟩
    · intro t ht0 htL
      refine approxComplexity_le_of_mem_patchThickening act chi hψnorm (patchHamLM k)
        (isSelfAdjoint_patchHamLM k) (Real.sqrt_nonneg _) (norm_patchHamLM_sub_le k)
        (hPUdef ▸ isCompact_embedPatch_sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ)
        (hPUdef ▸ nonempty_embedPatch_sphericalCap (norm_uniformDir (by omega)) hρ.le)
        (hPUdef ▸ hcert c) hL hgap hωt ht0 htL
    · intro A
      have hcoll' : occupationCollision (fun j => ‖eigenCoords (patchEigenBasis k ω)
          (registerCubicSeed k c) j‖ ^ 2) ≤ (2 + kap) / regDim k := by
        rw [occupationCollision_eq_phaseCollision]
        exact hcoll
      exact exists_late_hardWindow heb hmax (fun _ => false)
        (isSelfAdjoint_patchHamLM k _) hψunit hZ hepsn hegap hepsw
        sqrt_card_pathLabel_pos' (norm_patchHam_le ω) hrr hcoll' hscale hM hcardC hs W hW A
    · intro ρ' hρ' A
      exact exists_late_seed_recurrence heb hmax.injective hmax (fun _ => false)
        (registerCubicSeed k c) hψunit hρ' A
    · intro e
      have hcpt : IsCompact (embedPatch (d := 10 * (k + 1) + 12) PU) :=
        hPUdef ▸ isCompact_embedPatch_sphericalCap (uniformDir (2 * (k + 1) + 3)) ρ
      have hne : (embedPatch (d := 10 * (k + 1) + 12) PU).Nonempty :=
        hPUdef ▸ nonempty_embedPatch_sphericalCap (norm_uniformDir (by omega)) hρ.le
      obtain ⟨y, hy, hdisty⟩ := hcpt.exists_infDist_eq_dist hne
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
      obtain ⟨w, hw, hwy⟩ : ∃ w ∈ PU, WithLp.toLp 2
          (w, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))) = y := hy
      have hωt' : Metric.infDist (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))
          (embedPatch (d := 10 * (k + 1) + 12) PU) ≤ r := by
        rw [hPUdef]
        exact hωt
      have hle : ‖(ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) - y‖ ≤ r := by
        rw [← dist_eq_norm, ← hdisty]
        exact hωt'
      have hdist : ‖pathPatchIsometry (k + 1)
            (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) -
          pathPatchIsometry (k + 1)
            (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * (k + 1) + 12)))))‖ ≤ r := by
        rw [← (pathPatchIsometry (k + 1)).map_sub, LinearIsometryEquiv.norm_map, hwy]
        exact hle
      exact edgeCoupling_lower (by rw [← hPUdef]; exact hw) hdist e

end GaloisForLFunctions.HTGeometry

end
