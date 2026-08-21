import GaloisForLFunctions.RHTower.ReturnExcisedGaussianFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ArithmeticWindowHardCell
import GaloisForLFunctions.HTGeometry.UniformPhaseRayTransport

/-!
# Static Choi return-excised Gaussian first-return law

For a finite-dimensional static Hamiltonian, the Choi orbit is Lipschitz.  Hence every coordinate
of every finite replica incidence subspace is continuous, bounded by one, measurable, and square
integrable against a restricted Gaussian measure.  This discharges all analytic regularity inputs
in the return-excised coarea first-return theorem.

The resulting theorem has one substantive input: an explicit upper bound on the return-excised,
incidence-normalized coarea action.  No minimum spectral gap, target label count, or global mixing
premise appears.
-/

open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem continuous_finitePureTensorPowerEuclidean_comp
    {α : Type*} [Fintype α] {r : ℕ}
    (psi : ℝ → EuclideanSpace ℂ α) (hpsi : Continuous psi) :
    Continuous (fun x => finitePureTensorPowerEuclidean r (psi x)) := by
  unfold finitePureTensorPowerEuclidean finitePureTensorPower
  fun_prop

theorem continuous_replicaSubspaceCoordinate_comp
    {α : Type*} [Fintype α] {r : ℕ}
    (psi : ℝ → EuclideanSpace ℂ α) (hpsi : Continuous psi)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (i : Fin (Module.finrank ℂ S)) :
    Continuous (fun x => replicaSubspaceCoordinate r S (psi x) i) := by
  unfold replicaSubspaceCoordinate
  apply Continuous.inner continuous_const
  exact continuous_finitePureTensorPowerEuclidean_comp psi hpsi

theorem norm_replicaSubspaceCoordinate_le_one
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (psi : α → ℂ) (hpsi : finiteComplexInner psi psi = 1)
    (i : Fin (Module.finrank ℂ S)) :
    ‖replicaSubspaceCoordinate r S psi i‖ ≤ 1 := by
  unfold replicaSubspaceCoordinate
  calc
    ‖inner ℂ
      (((replicaSubspaceOrthonormalBasis r S i : S) :
        EuclideanSpace ℂ (Fin r → α)))
      (finitePureTensorPowerEuclidean r psi)‖ ≤
        ‖(((replicaSubspaceOrthonormalBasis r S i : S) :
          EuclideanSpace ℂ (Fin r → α)))‖ *
          ‖finitePureTensorPowerEuclidean r psi‖ := norm_inner_le_norm _ _
    _ = 1 := by
      rw [norm_finitePureTensorPowerEuclidean_eq_one r psi hpsi, mul_one]
      exact (replicaSubspaceOrthonormalBasis r S).orthonormal.norm_eq_one i

theorem finiteComplexInner_staticSpectralChoiVector_self
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t : ℝ) :
    finiteComplexInner (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d t energy) = 1 := by
  rw [← inner_toLp_eq_finiteComplexInner]
  simp only [WithLp.toLp_ofLp]
  rw [inner_self_eq_norm_sq_to_K, staticSpectralChoiVector_norm hd]
  norm_num

theorem continuous_staticSpectralChoiVector_scaled
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ) :
    Continuous (fun x : ℝ => staticSpectralChoiVector d (T * x) energy) := by
  let K : NNReal := ⟨staticChoiSpeed energy, (staticChoiSpeed_pos energy).le⟩
  have hK : (K : ℝ) = staticChoiSpeed energy := rfl
  have horbitLip : LipschitzWith K
      (fun t => staticSpectralChoiVector d t energy) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [hK, dist_eq_norm, Real.dist_eq]
    exact norm_staticSpectralChoiVector_time_sub_le hd energy t u
  exact horbitLip.continuous.comp (continuous_const.mul continuous_id)

theorem integrable_sq_replicaSubspaceCoordinate_staticSpectralChoiVector
    {d r : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → (Fin d × Fin d))))
    (i : Fin (Module.finrank ℂ S)) (R : Set ℝ) :
    Integrable
      (fun x => ‖replicaSubspaceCoordinate r S
        (staticSpectralChoiVector d (T * x) energy) i‖ ^ 2)
      ((gaussianReal 0 1).restrict R) := by
  have hc := continuous_replicaSubspaceCoordinate_comp
    (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
    (continuous_staticSpectralChoiVector_scaled hd energy T) S i
  apply Integrable.of_bound (hc.norm.pow 2).aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖replicaSubspaceCoordinate r S
    (staticSpectralChoiVector d (T * x) energy) i‖ ^ 2 ≤ 1
  have hcoord := norm_replicaSubspaceCoordinate_le_one r S
    (staticSpectralChoiVector d (T * x) energy)
    (finiteComplexInner_staticSpectralChoiVector_self hd energy (T * x)) i
  simpa only [one_pow] using
    (sq_le_sq₀ (norm_nonneg (replicaSubspaceCoordinate r S
      (staticSpectralChoiVector d (T * x) energy) i)) zero_le_one).2 hcoord

/-- **Static Choi first-return law from the exact return-excised incidence action.**  For every
finite target family, a bound on the occupied-image action below the displayed threshold excludes
all later narrow captures through `T`.  Continuity, measurability, and integrability are automatic;
the action estimate is the only remaining scientific input. -/
theorem no_forward_pureChoiCircuitReturn_of_returnExcisedGaussianIncidenceAction_lt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (energy : Fin d → ℝ)
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    {r : ℕ} (hr : 0 < r)
    {T epsn epsw : ℝ}
    (hTpos : 0 < T) (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (haction :
      (returnExcisedReplicaIncidenceNumber r (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) : ℝ) *
        returnExcisedReplicaIncidenceAction (gaussianReal 0 1) r
          (fun c => (target c).ofLp)
          (fun x => (staticSpectralChoiVector d (T * x) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)) <
      (gaussianFloorTwo *
        ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r) ^ 2) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ≤ epsn := by
  have hepsw : 0 ≤ epsw := hepsn.trans (le_of_lt hgap)
  have htargetInner : ∀ c,
      finiteComplexInner (target c).ofLp (target c).ofLp = 1 := by
    intro c
    rw [finiteComplexInner_eq_inner]
    simp only [WithLp.toLp_ofLp]
    rw [inner_self_eq_norm_sq_to_K, htarget c]
    norm_num
  have hthreshold : 0 < 1 - epsw ^ 2 := by
    nlinarith [sq_nonneg epsw]
  have htriangle : ∀ t u c,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (target c).ofLp) ≤
        pureStateTraceDistance
            (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
              EuclideanSpace ℂ (Fin d × Fin d))
            (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp) +
          pureStateTraceDistance
            (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp :
              EuclideanSpace ℂ (Fin d × Fin d))
            (WithLp.toLp 2 (target c).ofLp) := by
    intro t u c
    simpa only [WithLp.toLp_ofLp] using
      pureStateTraceDistance_triangle
        (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d u energy)
        (target c)
        (staticSpectralChoiVector_norm hd t energy)
        (staticSpectralChoiVector_norm hd u energy)
        (htarget c)
  have hLip : ∀ t u,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (staticSpectralChoiVector d u energy).ofLp) ≤
        staticChoiSpeed energy * |t - u| := by
    intro t u
    simpa only [WithLp.toLp_ofLp] using
      pureStateTraceDistance_staticSpectralChoiVector_time_le hd energy t u
  have hfidelity : ∀ t c,
      pureStateTraceDistance
          (WithLp.toLp 2 (staticSpectralChoiVector d t energy).ofLp :
            EuclideanSpace ℂ (Fin d × Fin d))
          (WithLp.toLp 2 (target c).ofLp) ≤ epsw →
        1 - epsw ^ 2 ≤ finitePureStateFidelity
          (staticSpectralChoiVector d t energy).ofLp (target c).ofLp := by
    intro t c hdist
    rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    rw [norm_inner_symm]
    have hsq := sq_pureStateTraceDistance
      (staticSpectralChoiVector d t energy) (target c)
      (by rw [staticSpectralChoiVector_norm hd])
      (by rw [htarget c])
    have hdistSq : pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (target c) ^ 2 ≤ epsw ^ 2 :=
      (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) hepsw).2 hdist
    nlinarith
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          (fun y => (staticSpectralChoiVector d (T * y) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)))
        (staticSpectralChoiVector d (T * x) energy).ofLp i)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro i
    exact (continuous_replicaSubspaceCoordinate_comp
      (fun x : ℝ => staticSpectralChoiVector d (T * x) energy)
      (continuous_staticSpectralChoiVector_scaled hd energy T) _ i).aestronglyMeasurable
  have hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r (fun c => (target c).ofLp)
          (fun y => (staticSpectralChoiVector d (T * y) energy).ofLp)
          (Icc (-(epsw / staticChoiSpeed energy / T))
            (epsw / staticChoiSpeed energy / T)))
        (staticSpectralChoiVector d (T * x) energy).ofLp i‖ ^ 2)
      ((gaussianReal 0 1).restrict
        (Icc (-(epsw / staticChoiSpeed energy / T))
          (epsw / staticChoiSpeed energy / T))ᶜ) := by
    intro i
    exact integrable_sq_replicaSubspaceCoordinate_staticSpectralChoiVector
      hd energy T _ i _
  simpa only [WithLp.toLp_ofLp] using
    (no_second_capture_of_returnExcised_gaussianIncidenceAction_lt
      (fun u v => pureStateTraceDistance
        (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin d × Fin d))
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d × Fin d)))
      (fun t => (staticSpectralChoiVector d t energy).ofLp)
      (fun c => (target c).ofLp) hr htargetInner
      (staticChoiSpeed_pos energy) hTpos hepsn hgap hT hthreshold
      htriangle hLip hfidelity hmeas hcoord haction)

end RHTower
