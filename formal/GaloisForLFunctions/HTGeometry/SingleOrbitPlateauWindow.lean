/-
# A continuous hard window along one orbit

The shell-averaged plateau laws bound the measure of the Hamiltonians that are easy at a given late
time.  A single Hamiltonian with maximally projective spectrum carries its own equidistribution: the
one-sided Kronecker--Weyl law turns the Haar measure of the capture target into the long-time
density of the capture times.  Translating the target along a mesh of the window turns that into a
density bound for the times whose forward window meets the target, and a density below one leaves
times arbitrarily late whose whole window is hard.

Main results:
* `shiftTarget`, `gridTarget` — the capture target translated along a time grid.
* `metricEasySet`, `metricEasySet_subset_physicalCaptureSet`, `metricEasySet_mesh` — the metric
  parametrization of the easy times and its mesh transfer.
* `limsup_windowProb_badWindowSet_le` — the density of the times whose window meets the target.
* `exists_notMem_of_limsup_windowProb_lt_one` — a density below one leaves late times outside.
* `exists_late_hardWindow` — **the single-orbit continuous plateau**.
-/
import GaloisForLFunctions.HTGeometry.PhysicalTimeCircuitCapture
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.ProjectiveCaptureHaarBound

open MeasureTheory Complex UnitAddTorus Set Filter Topology Matrix
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Phase

variable {d : Type} [Fintype d]

theorem finiteClockPhasePoint_add (omega : d → ℝ) (t s : ℝ) :
    finiteClockPhasePoint omega (t + s)
      = finiteClockPhasePoint omega t + finiteClockPhasePoint omega s := by
  funext i
  show ((((t + s) * omega i / (2 * Real.pi) : ℝ)) : UnitAddCircle) = _
  rw [add_mul, add_div]
  rfl

end Phase

section Unitary

variable {I : Type} [Fintype I] [DecidableEq I]

/-- A unitary evolution preserves the inner product of a state with itself. -/
theorem finiteComplexInner_unitaryEvolution_self {H : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    (psi : I → ℂ) (t : ℝ) :
    finiteComplexInner (unitaryEvolution H t *ᵥ psi) (unitaryEvolution H t *ᵥ psi)
      = finiteComplexInner psi psi := by
  classical
  obtain ⟨U, hUdef⟩ : ∃ U, U = unitaryEvolution H t := ⟨_, rfl⟩
  have hU : Uᴴ * U = (1 : Matrix I I ℂ) := by
    rw [hUdef]
    have h := unitaryEvolution_mem_unitary hH t
    exact (Matrix.mem_unitaryGroup_iff'.mp h)
  rw [← hUdef]
  have hdot : ∀ x y : I → ℂ, finiteComplexInner x y = (star x) ⬝ᵥ y := fun x y => rfl
  rw [hdot, hdot, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one]

end Unitary


section ShiftTarget

variable {d : Type} [Fintype d]

/-- A closed capture target translated by a fixed phase. -/
def shiftTarget (p : UnitAddTorus d) (A : Set (UnitAddTorus d)) : Set (UnitAddTorus d) :=
  (fun y => y + p) ⁻¹' A

theorem isClosed_shiftTarget {A : Set (UnitAddTorus d)} (hA : IsClosed A)
    (p : UnitAddTorus d) : IsClosed (shiftTarget p A) :=
  hA.preimage (continuous_id.add continuous_const)

theorem volume_shiftTarget (p : UnitAddTorus d) (A : Set (UnitAddTorus d)) :
    (volume : Measure (UnitAddTorus d)) (shiftTarget p A) = volume A :=
  measure_preimage_add_right volume p A

/-- The union of the translates of a target along a time grid. -/
def gridTarget (omega : d → ℝ) (mesh : ℝ) (N : ℕ) (A : Set (UnitAddTorus d)) :
    Set (UnitAddTorus d) :=
  ⋃ j ∈ Finset.range N,
    shiftTarget (finiteClockPhasePoint omega (plateauGridPoint 0 mesh j)) A

theorem isClosed_gridTarget {A : Set (UnitAddTorus d)} (hA : IsClosed A)
    (omega : d → ℝ) (mesh : ℝ) (N : ℕ) : IsClosed (gridTarget omega mesh N A) := by
  refine Set.Finite.isClosed_biUnion (Finset.range N).finite_toSet fun j _ => ?_
  exact isClosed_shiftTarget hA _

theorem volume_gridTarget_le (omega : d → ℝ) (mesh : ℝ) (N : ℕ)
    (A : Set (UnitAddTorus d)) :
    (volume : Measure (UnitAddTorus d)) (gridTarget omega mesh N A)
      ≤ (N : ENNReal) * volume A := by
  refine le_trans (measure_biUnion_finset_le (Finset.range N) _) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => le_of_eq (volume_shiftTarget _ A))) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end ShiftTarget


section MetricOrbit

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

theorem sum_normSq_eq_one_of_inner {u : I → ℂ} (h : finiteComplexInner u u = 1) :
    (∑ i, ‖u i‖ ^ 2 : ℝ) = 1 := by
  have hcast : ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = finiteComplexInner u u := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
  rw [h] at hcast
  exact_mod_cast hcast

/-- The register state read as a Euclidean vector. -/
def eucVec (v : I → ℂ) : EuclideanSpace ℂ I := (EuclideanSpace.equiv I ℂ).symm v

theorem norm_eucVec (v : I → ℂ) : ‖eucVec v‖ = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  rw [eucVec, EuclideanSpace.norm_eq]
  rfl

theorem dist_eucVec (u v : I → ℂ) :
    dist (eucVec u) (eucVec v) = Real.sqrt (∑ i, ‖u i - v i‖ ^ 2) := by
  rw [dist_eq_norm, ← norm_eucVec]
  congr 1

theorem norm_eucVec_eq_one {v : I → ℂ} (h : finiteComplexInner v v = 1) : ‖eucVec v‖ = 1 := by
  rw [norm_eucVec, sum_normSq_eq_one_of_inner h, Real.sqrt_one]

/-- The Schrödinger orbit of a register state. -/
def orbitVec (H : Matrix I I ℂ) (psi : I → ℂ) (t : ℝ) : EuclideanSpace ℂ I :=
  eucVec (unitaryEvolution H t *ᵥ psi)

/-- The set of times at which the orbit is within `eps` of some target. -/
def metricEasySet (H : Matrix I I ℂ) (psi : I → ℂ) (eps : ℝ) (Z : C → (I → ℂ)) : Set ℝ :=
  {t | ∃ κ, dist (orbitVec H psi t) (eucVec (Z κ)) ≤ eps}

/-- **A distance approximation is a fidelity capture.** -/
theorem metricEasySet_subset_physicalCaptureSet {H : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {eps : ℝ} (heps : 0 ≤ eps) {Z : C → (I → ℂ)}
    (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1) :
    metricEasySet H psi eps Z ⊆ physicalCaptureSet H psi (1 - eps ^ 2) Z := by
  rintro t ⟨κ, hκ⟩
  refine ⟨κ, ?_⟩
  have hu : finiteComplexInner (unitaryEvolution H t *ᵥ psi) (unitaryEvolution H t *ᵥ psi) = 1 := by
    rw [finiteComplexInner_unitaryEvolution_self hH psi t, hpsi]
  have hd : Real.sqrt (∑ i, ‖(unitaryEvolution H t *ᵥ psi) i - Z κ i‖ ^ 2) ≤ eps := by
    rw [← dist_eucVec]
    exact hκ
  have hsq : (∑ i, ‖(unitaryEvolution H t *ᵥ psi) i - Z κ i‖ ^ 2 : ℝ) ≤ eps ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ i, ‖(unitaryEvolution H t *ᵥ psi) i - Z κ i‖ ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg
      (∑ i, ‖(unitaryEvolution H t *ᵥ psi) i - Z κ i‖ ^ 2), hd, heps]
  exact le_finitePureStateFidelity_of_dist_le hu (hZ κ) hsq

/-- **Orbit speed.**  The Schrödinger orbit of a unit state is `‖H‖`-Lipschitz in time. -/
theorem dist_orbitVec_le {H : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {speed : ℝ} (hspeed : ‖H‖ ≤ speed) (t u : ℝ) :
    dist (orbitVec H psi t) (orbitVec H psi u) ≤ speed * |t - u| :=
  dist_unitaryOrbit_le (fun _ : Unit => H) (fun _ => hH) (fun _ => eucVec psi)
    (fun _ => le_of_eq (norm_eucVec_eq_one hpsi)) (fun _ => hspeed) () t u

/-- **Mesh transfer in the metric parametrization.** -/
theorem metricEasySet_mesh {H : Matrix I I ℂ} (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {speed : ℝ} (hspeed : ‖H‖ ≤ speed) {Z : C → (I → ℂ)}
    {epsn epsw mesh : ℝ} (hgap : speed * mesh ≤ epsw - epsn)
    {t u : ℝ} (htu : |t - u| ≤ mesh) (hspeed0 : 0 ≤ speed)
    (ht : t ∈ metricEasySet H psi epsn Z) : u ∈ metricEasySet H psi epsw Z := by
  obtain ⟨κ, hκ⟩ := ht
  refine ⟨κ, ?_⟩
  have hut : |u - t| ≤ mesh := by rwa [abs_sub_comm]
  calc dist (orbitVec H psi u) (eucVec (Z κ))
      ≤ dist (orbitVec H psi u) (orbitVec H psi t) + dist (orbitVec H psi t) (eucVec (Z κ)) :=
        dist_triangle _ _ _
    _ ≤ speed * |u - t| + epsn := add_le_add (dist_orbitVec_le hH hpsi hspeed u t) hκ
    _ ≤ speed * mesh + epsn := by nlinarith
    _ ≤ epsw := by linarith

end MetricOrbit


section BadWindow

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

/-- The times whose forward window contains a grid point at which the dictionary captures the
orbit. -/
def badWindowSet (H : Matrix I I ℂ) (psi : I → ℂ) (a : ℝ) (Z : C → (I → ℂ))
    (mesh : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ j ∈ Finset.range N,
    {t | t + plateauGridPoint 0 mesh j ∈ physicalCaptureSet H psi a Z}

theorem badWindowSet_eq_preimage {H : Matrix I I ℂ} {e : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (ref : I) (psi : I → ℂ) (a : ℝ) (Z : C → (I → ℂ))
    (mesh : ℝ) (N : ℕ) :
    badWindowSet H psi a Z mesh N
      = finiteClockPhasePoint (projectiveFrequency (fun i => -lam i) ref) ⁻¹'
          gridTarget (projectiveFrequency (fun i => -lam i) ref) mesh N
            (projectiveAmpCaptureTarget ref (eigenCoords e psi) a
              (fun κ => eigenCoords e (Z κ))) := by
  ext t
  simp only [badWindowSet, gridTarget, Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq,
    shiftTarget, exists_prop]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  rw [physicalCaptureSet_eq_preimage heb ref psi a Z]
  rw [Set.mem_preimage, finiteClockPhasePoint_add]

theorem limsup_windowProb_badWindowSet_le {H : Matrix I I ℂ} {e : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (psi : I → ℂ) (hpsi : finiteComplexInner psi psi = 1)
    (Z : C → (I → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖eigenCoords e psi j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (mesh : ℝ) (N : ℕ) :
    atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ)
        (badWindowSet H psi a Z mesh N))
      ≤ (N : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
  classical
  obtain ⟨omega, homega⟩ : ∃ omega, omega = projectiveFrequency (fun i => -lam i) ref := ⟨_, rfl⟩
  obtain ⟨Tgt, hTgt⟩ : ∃ Tgt, Tgt = projectiveAmpCaptureTarget ref (eigenCoords e psi) a
    (fun κ => eigenCoords e (Z κ)) := ⟨_, rfl⟩
  have hclosed : IsClosed Tgt := by
    rw [hTgt]
    exact isClosed_projectiveAmpCaptureTarget ref (eigenCoords e psi) a
      (fun κ => eigenCoords e (Z κ))
  have hind : RationallyIndependentFrequency omega := by
    rw [homega]
    exact maximallyProjectiveEnergy_projectiveFrequency_independent (fun i => -lam i)
      (maximallyProjectiveEnergy_neg hmax) ref
  have hcsum : ∑ j, ‖eigenCoords e psi j‖ ^ 2 ≤ 1 :=
    le_of_eq (sum_normSq_eigenCoords heb psi hpsi)
  have hznorm : ∀ κ, ∑ j, ‖eigenCoords e (Z κ) j‖ ^ 2 ≤ 1 :=
    fun κ => le_of_eq (sum_normSq_eigenCoords heb (Z κ) (hZ κ))
  have hzunit : ∀ κ, finiteComplexInner (eigenCoords e (Z κ)) (eigenCoords e (Z κ)) = 1 :=
    fun κ => (finiteComplexInner_eigenCoords heb (Z κ) (Z κ)).trans (hZ κ)
  have hvolTgt : (volume : Measure (UnitAddTorus {i : I // i ≠ ref})) Tgt
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
    rw [hTgt]
    exact measure_projectiveAmpCaptureTarget_le_two_rpow ref (eigenCoords e psi) hcsum ha
      (fun κ => eigenCoords e (Z κ)) hzunit hznorm hr hcoll hscale hM hcard hs
  have hset : ∀ T : ℝ, (windowProbabilityMeasure T : Measure ℝ)
      (badWindowSet H psi a Z mesh N)
      = (clockPhaseWindowLaw omega T : Measure (UnitAddTorus {i : I // i ≠ ref}))
        (gridTarget omega mesh N Tgt) := by
    intro T
    rw [clockPhaseWindowLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (finiteClockPhasePoint_continuous _).measurable
        (isClosed_gridTarget hclosed omega mesh N).measurableSet]
    rw [badWindowSet_eq_preimage heb ref psi a Z mesh N, homega, hTgt]
  rw [Filter.limsup_congr (Filter.Eventually.of_forall hset)]
  refine le_trans (oneSided_closedTarget_limsup_le_volume omega hind
    (isClosed_gridTarget hclosed omega mesh N)) ?_
  exact le_trans (volume_gridTarget_le omega mesh N Tgt) (mul_le_mul' le_rfl hvolTgt)

end BadWindow


section Unbounded

theorem windowProb_apply (T : ℝ) (S : Set ℝ) :
    (windowProbabilityMeasure T : Measure ℝ) S
      = (ENNReal.ofReal (windowLength T))⁻¹ *
        (volume.restrict (Set.Ioc 0 (windowLength T))) S := by
  show ((ENNReal.ofReal (windowLength T))⁻¹ •
    (volume.restrict (Set.Ioc 0 (windowLength T)))) S = _
  rw [Measure.smul_apply, smul_eq_mul]

theorem windowProb_Ioc {A T : ℝ} (hA : 0 ≤ A) (hT : 0 < T) :
    (windowProbabilityMeasure T : Measure ℝ) (Set.Ioc A T)
      = ENNReal.ofReal ((T - A) / T) := by
  have hlen : windowLength T = T := by rw [windowLength, if_pos hT]
  rw [windowProb_apply, hlen, Measure.restrict_apply measurableSet_Ioc]
  have hinter : Set.Ioc A T ∩ Set.Ioc 0 T = Set.Ioc A T := by
    rw [Set.inter_eq_left]
    exact fun t ht => ⟨lt_of_le_of_lt hA ht.1, ht.2⟩
  rw [hinter, Real.volume_Ioc, ← ENNReal.ofReal_inv_of_pos hT,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hT))]
  congr 1
  rw [div_eq_inv_mul]

/-- **A time density below one leaves times arbitrarily late outside the set.** -/
theorem exists_notMem_of_limsup_windowProb_lt_one {B : Set ℝ}
    (hB : atTop.limsup (fun T => (windowProbabilityMeasure T : Measure ℝ) B) < 1) (A : ℝ) :
    ∃ t, A < t ∧ t ∉ B := by
  by_contra hcon
  have hall : ∀ t : ℝ, A < t → t ∈ B :=
    fun t ht => not_not.mp (fun hnb => hcon ⟨t, ht, hnb⟩)
  obtain ⟨ρ, hρ0, hlt, hρ1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hB
  have hρone : ρ < 1 := by
    by_contra hge
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal ρ := by
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (not_lt.mp hge)
    exact absurd hρ1 (not_lt.mpr h1)
  obtain ⟨A', hA'def⟩ : ∃ A' : ℝ, A' = max A 0 := ⟨_, rfl⟩
  have hA'0 : 0 ≤ A' := by rw [hA'def]; exact le_max_right _ _
  have hAA' : A ≤ A' := by rw [hA'def]; exact le_max_left _ _
  have hev := Filter.eventually_lt_of_limsup_lt hlt
  obtain ⟨T, hTlt, hTgt⟩ := (hev.and (Filter.eventually_gt_atTop
    (max (A' + 1) (A' / (1 - ρ) + 1)))).exists
  have hT1 : A' + 1 ≤ max (A' + 1) (A' / (1 - ρ) + 1) := le_max_left _ _
  have hT2 : A' / (1 - ρ) + 1 ≤ max (A' + 1) (A' / (1 - ρ) + 1) := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hsub : Set.Ioc A' T ⊆ B := fun t ht => hall t (lt_of_le_of_lt hAA' ht.1)
  have hmono := measure_mono (μ := (windowProbabilityMeasure T : Measure ℝ)) hsub
  rw [windowProb_Ioc hA'0 hTpos] at hmono
  have hden : (0 : ℝ) < 1 - ρ := by linarith
  have hTbig : A' / (1 - ρ) < T := by linarith
  have hbig : ρ < (T - A') / T := by
    rw [lt_div_iff₀ hTpos, div_lt_iff₀ hden] at *
    linarith
  have hcmp : ENNReal.ofReal ρ < ENNReal.ofReal ((T - A') / T) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρ0).mpr hbig
  exact absurd (lt_of_le_of_lt hmono hTlt) (not_lt.mpr (le_of_lt hcmp))

end Unbounded


section Plateau

variable {I : Type} [Fintype I] [DecidableEq I]
variable {C : Type} [Fintype C] [Nonempty C]

/-- **The single-orbit continuous plateau.**  For one Hamiltonian with maximally projective
spectrum and one unit seed whose collision in its eigenbasis is small enough, there are windows of
length `W` arbitrarily late on which *no* time admits an `εₙ`-approximation from the dictionary,
as soon as the number of mesh points of the window times `2^{-r/2}` is below one. -/
theorem exists_late_hardWindow {H : Matrix I I ℂ} {e : I → I → ℂ} {lam : I → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hmax : MaximallyProjectiveEnergy lam) (ref : I)
    (hH : IsSelfAdjoint H)
    {psi : I → ℂ} (hpsi : finiteComplexInner psi psi = 1)
    {Z : C → (I → ℂ)} (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {epsn epsw : ℝ} (hepsn : 0 ≤ epsn) (hgap : epsn < epsw) (hepsw : epsw < 1)
    {speed : ℝ} (hspeed0 : 0 < speed) (hspeed : ‖H‖ ≤ speed)
    {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hcoll : occupationCollision (fun j => ‖eigenCoords e psi j‖ ^ 2) ≤ c₀)
    (hscale : 16 * c₀ / (1 - epsw ^ 2) ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    (W : ℝ)
    (hW : ((plateauGridCount W ((epsw - epsn) / speed) : ℕ) : ℝ) *
      (2 : ℝ) ^ (-((r : ℝ) / 2)) < 1)
    (A : ℝ) :
    ∃ t₀, A < t₀ ∧ ∀ u ∈ Set.Icc t₀ (t₀ + W), u ∉ metricEasySet H psi epsn Z := by
  classical
  obtain ⟨mesh, hmeshdef⟩ : ∃ mesh, mesh = (epsw - epsn) / speed := ⟨_, rfl⟩
  have hmesh : 0 < mesh := by rw [hmeshdef]; exact div_pos (by linarith) hspeed0
  have hspeedmesh : speed * mesh = epsw - epsn := by
    rw [hmeshdef, mul_div_cancel₀ _ (ne_of_gt hspeed0)]
  obtain ⟨N, hNdef⟩ : ∃ N, N = plateauGridCount W mesh := ⟨_, rfl⟩
  have hapos : 0 < 1 - epsw ^ 2 := by nlinarith
  have hdens := limsup_windowProb_badWindowSet_le heb hmax ref psi hpsi Z hZ hapos hr hcoll
    hscale hM hcard hs mesh N
  have hlt1 : (N : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) < 1 := by
    rw [show ((N : ENNReal)) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (by positivity),
      show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr ?_
    rw [hNdef, hmeshdef]
    exact hW
  obtain ⟨t₀, ht₀A, ht₀⟩ := exists_notMem_of_limsup_windowProb_lt_one
    (lt_of_le_of_lt hdens hlt1) A
  refine ⟨t₀, ht₀A, ?_⟩
  intro u hu hmem
  obtain ⟨j, hj⟩ := exists_plateauGrid_near (W := W) hmesh 0
    (t := u - t₀) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine ht₀ (Set.mem_biUnion (Finset.mem_range.mpr (by rw [hNdef]; exact j.2)) ?_)
  show t₀ + plateauGridPoint 0 mesh (j : ℕ) ∈ physicalCaptureSet H psi (1 - epsw ^ 2) Z
  refine metricEasySet_subset_physicalCaptureSet hH hpsi
    (le_of_lt (lt_of_le_of_lt hepsn hgap)) hZ ?_
  refine metricEasySet_mesh hH hpsi hspeed (epsn := epsn) (epsw := epsw) (mesh := mesh)
    (le_of_eq hspeedmesh) ?_ hspeed0.le hmem
  rw [show u - (t₀ + plateauGridPoint 0 mesh (j : ℕ))
    = (u - t₀) - plateauGridPoint 0 mesh (j : ℕ) by ring]
  exact hj

end Plateau

end GaloisForLFunctions.HTGeometry

end
