import GaloisForLFunctions.RHTower.PrimeTorsionCircuitRayPolygon
import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw
import GaloisForLFunctions.RHTower.StaticChoiSyndeticComplexityLaw

/-!
# Autonomous shadowing of complete hard prime-torsion polygons

A strict finite hard polygon is a stable open target in the projective phase
torus.  Maximal projective spectral rank makes one fixed autonomous phase
flow hit this entire target syndetically.  One hit simultaneously shadows all
nonidentity polygon vertices at the corresponding integer multiples and
returns near the identity at the prime multiple.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The finite cyclic phase lift is an additive homomorphism. -/
def zmodUnitAddCirclePhaseHom (M : ℕ) [NeZero M] : ZMod M →+ UnitAddCircle where
  toFun := zmodUnitAddCirclePhase M
  map_zero' := by
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    simp [zmodUnitAddCirclePhase, AddCircle.homeomorphCircle_apply]
  map_add' x y := by
    apply (AddCircle.homeomorphCircle one_ne_zero).injective
    rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_add]
    simp [zmodUnitAddCirclePhase, AddChar.map_add_eq_mul]
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero,
      ← AddCircle.homeomorphCircle_apply one_ne_zero,
      ← AddCircle.homeomorphCircle_apply one_ne_zero]
    simp

theorem zmodUnitAddCirclePhaseHom_self_nsmul
    (M : ℕ) [NeZero M] (x : ZMod M) :
    M • zmodUnitAddCirclePhaseHom M x = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod M)]
  simp

/-- Remove the zeroth global cyclic phase from a full grid point. -/
def finiteGridProjectivePhase
    (M d : ℕ) [NeZero M] (q : Fin (d + 1) → ZMod M) :
    Fin d → UnitAddCircle :=
  fun i => zmodUnitAddCirclePhaseHom M (q i.succ - q 0)

theorem finiteGridProjectivePhase_self_nsmul
    (M d : ℕ) [NeZero M] (q : Fin (d + 1) → ZMod M) :
    M • finiteGridProjectivePhase M d q = 0 := by
  funext i
  exact zmodUnitAddCirclePhaseHom_self_nsmul M (q i.succ - q 0)

/-- A common phase cancels from the full pure Choi density. -/
theorem fullUniformPhaseChoiDensity_add_common
    (d : ℕ) (x : Fin d → UnitAddCircle) (c : UnitAddCircle) :
    fullUniformPhaseChoiDensity d (fun i => x i + c) =
      fullUniformPhaseChoiDensity d x := by
  ext pq
  simp only [fullUniformPhaseChoiDensity]
  by_cases h1 : pq.1.1 = pq.1.2 <;>
    by_cases h2 : pq.2.1 = pq.2.2
  · simp only [h1, h2, and_self, if_pos]
    rw [fourier_one, fourier_one, fourier_one, fourier_one,
      AddCircle.toCircle_add, AddCircle.toCircle_add, Circle.coe_mul,
      Circle.coe_mul, map_mul]
    have hc : (AddCircle.toCircle c : ℂ) *
        starRingEnd ℂ (AddCircle.toCircle c : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp
    rw [show
        ((d : ℝ)⁻¹ : ℂ) *
              ((AddCircle.toCircle (x pq.1.2) : ℂ) *
                (AddCircle.toCircle c : ℂ)) *
              (starRingEnd ℂ (AddCircle.toCircle (x pq.2.2) : ℂ) *
                starRingEnd ℂ (AddCircle.toCircle c : ℂ)) =
            (((d : ℝ)⁻¹ : ℂ) *
              (AddCircle.toCircle (x pq.1.2) : ℂ) *
              starRingEnd ℂ (AddCircle.toCircle (x pq.2.2) : ℂ)) *
              ((AddCircle.toCircle c : ℂ) *
                starRingEnd ℂ (AddCircle.toCircle c : ℂ)) by ring,
      hc, mul_one]
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- Full Choi density depends only on phases relative to coordinate zero. -/
theorem fullUniformPhaseChoiDensity_eq_zeroAnchored
    (d : ℕ) (x : Fin (d + 1) → UnitAddCircle) :
    fullUniformPhaseChoiDensity (d + 1) x =
      fullUniformPhaseChoiDensity (d + 1)
        (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2) := by
  calc
    _ = fullUniformPhaseChoiDensity (d + 1)
        ((zeroRelativePhaseEquiv d).symm (zeroRelativePhaseEquiv d x)) := by
      rw [(zeroRelativePhaseEquiv d).symm_apply_apply]
    _ = fullUniformPhaseChoiDensity (d + 1)
        (fun i => zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2 i +
          (zeroRelativePhaseEquiv d x).1) := by
      rw [zeroRelativePhaseEquiv_symm_eq_anchored_add]
    _ = _ := fullUniformPhaseChoiDensity_add_common _ _ _

theorem zeroRelativePhase_finiteGrid_scalar
    (M d : ℕ) [NeZero M] (a : ZMod M)
    (q : Fin (d + 1) → ZMod M) :
    (zeroRelativePhaseEquiv d
      (fun i => zmodUnitAddCirclePhaseHom M (a * q i))).2 =
        a.val • finiteGridProjectivePhase M d q := by
  funext i
  change zmodUnitAddCirclePhaseHom M (a * q i.succ) -
      zmodUnitAddCirclePhaseHom M (a * q 0) =
    a.val • zmodUnitAddCirclePhaseHom M (q i.succ - q 0)
  rw [← map_sub, ← map_nsmul]
  congr 1
  rw [← ZMod.natCast_zmod_val a]
  simp [nsmul_eq_mul, mul_sub]

/-- The density of a full scalar grid point is exactly the density of its
zero-anchored projective representative. -/
theorem fullUniformPhaseChoiDensity_finiteGrid_scalar_eq_projective
    (M d : ℕ) [NeZero M] (a : ZMod M)
    (q : Fin (d + 1) → ZMod M) :
    fullUniformPhaseChoiDensity (d + 1)
        (fun i => zmodUnitAddCirclePhaseHom M (a * q i)) =
      fullUniformPhaseChoiDensity (d + 1)
        (zeroAnchoredPhase d
          (a.val • finiteGridProjectivePhase M d q)) := by
  rw [fullUniformPhaseChoiDensity_eq_zeroAnchored,
    zeroRelativePhase_finiteGrid_scalar]

/-- Projective normalized Choi vector of a relative phase packet. -/
def projectivePhaseChoiVector
    (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) :=
  fullUniformPhaseChoiVector (d + 1) (zeroAnchoredPhase d x)

/-- Projective full pure Choi density. -/
def projectivePhaseChoiDensity
    (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ
      ((Fin (d + 1) × Fin (d + 1)) × (Fin (d + 1) × Fin (d + 1))) :=
  fullUniformPhaseChoiDensity (d + 1) (zeroAnchoredPhase d x)

theorem projectivePhaseChoiVector_norm
    (d : ℕ) (x : Fin d → UnitAddCircle) :
    ‖projectivePhaseChoiVector d x‖ = 1 :=
  fullUniformPhaseChoiVector_norm (Nat.succ_pos d) _

theorem pureStateDensity_projectivePhaseChoiVector
    (d : ℕ) (x : Fin d → UnitAddCircle) :
    pureStateDensity (projectivePhaseChoiVector d x) =
      projectivePhaseChoiDensity d x :=
  pureStateDensity_fullUniformPhaseChoiVector (Nat.succ_pos d) _

theorem continuous_projectivePhaseChoiDensity (d : ℕ) :
    Continuous (projectivePhaseChoiDensity d) := by
  exact (continuous_fullUniformPhaseChoiDensity (d + 1)).comp (by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const
    · exact continuous_apply j)

/-- Open phase target encoding every hard nonidentity polygon vertex and a
near-return at the prime multiple. -/
def projectivePrimeCircuitPolygonTarget
    {Y : Type*} [Fintype Y]
    (p d : ℕ) (target : Y → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (epsilon rho : ℝ) : Set (Fin d → UnitAddCircle) :=
  (⋂ a : ZMod p, ⋂ (_ha : a ≠ 0), ⋂ y : Y,
    {x | Real.sqrt 2 * epsilon <
      dist (projectivePhaseChoiDensity d (a.val • x))
        (pureStateDensity (target y))}) ∩
  {x | dist (projectivePhaseChoiDensity d (p • x))
      (projectivePhaseChoiDensity d 0) < Real.sqrt 2 * rho}

theorem isOpen_projectivePrimeCircuitPolygonTarget
    {Y : Type*} [Fintype Y]
    (p d : ℕ) [NeZero p]
    (target : Y → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (epsilon rho : ℝ) :
    IsOpen (projectivePrimeCircuitPolygonTarget p d target epsilon rho) := by
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro a
    apply isOpen_iInter_of_finite
    intro ha
    apply isOpen_iInter_of_finite
    intro y
    apply isOpen_lt continuous_const
    exact ((continuous_projectivePhaseChoiDensity d).comp (by fun_prop)).dist
      continuous_const
  · apply isOpen_lt
    · exact ((continuous_projectivePhaseChoiDensity d).comp (by fun_prop)).dist
        continuous_const
    · exact continuous_const

/-- A complete hard finite-grid polygon supplies a point of the stable open
projective polygon target. -/
theorem finiteGridProjectivePhase_mem_polygonTarget
    {Y : Type*} [Fintype Y]
    (p d : ℕ) [Fact p.Prime]
    (target : Y → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon rho : ℝ} (hrho : 0 < rho)
    (q : Fin (d + 1) → ZMod p)
    (hq : ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
      epsilon < pureStateTraceDistance
        (finiteGridChoiVector p (d + 1) fun i => a * q i) (target y)) :
    finiteGridProjectivePhase p d q ∈
      projectivePrimeCircuitPolygonTarget p d target epsilon rho := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · apply Set.mem_iInter.mpr
    intro a
    apply Set.mem_iInter.mpr
    intro ha
    apply Set.mem_iInter.mpr
    intro y
    have hgridNorm : ‖finiteGridChoiVector p (d + 1)
        (fun i => a * q i)‖ = 1 :=
      finiteGridChoiVector_norm (Nat.succ_pos d) _
    have hdensity : Real.sqrt 2 * epsilon <
        dist (pureStateDensity
          (finiteGridChoiVector p (d + 1) fun i => a * q i))
          (pureStateDensity (target y)) := by
      rw [dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance _ _
        hgridNorm (htarget y)]
      exact mul_lt_mul_of_pos_left (hq a ha y) (Real.sqrt_pos.2 (by norm_num))
    rw [show pureStateDensity
        (finiteGridChoiVector p (d + 1) fun i => a * q i) =
          fullUniformPhaseChoiDensity (d + 1)
            (fun i => zmodUnitAddCirclePhaseHom p (a * q i)) by
          exact pureStateDensity_fullUniformPhaseChoiVector
            (Nat.succ_pos d) _] at hdensity
    rw [fullUniformPhaseChoiDensity_finiteGrid_scalar_eq_projective] at hdensity
    exact hdensity
  · change dist (projectivePhaseChoiDensity d
        (p • finiteGridProjectivePhase p d q))
      (projectivePhaseChoiDensity d 0) < Real.sqrt 2 * rho
    rw [finiteGridProjectivePhase_self_nsmul]
    simpa using mul_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) hrho

/-- **Autonomous complete-polygon shadowing law.** One fixed maximally
projective Hamiltonian shadows every nonidentity vertex of a supplied strict
prime-torsion hard polygon and returns near the identity at the prime multiple.
Such base times occur with one uniform finite gap after every starting time. -/
theorem maximallyProjective_complete_circuitPolygon_shadow_syndetic
    {Y : Type*} [Fintype Y]
    (p d : ℕ) [Fact p.Prime]
    (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (target : Y → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon rho : ℝ} (hrho : 0 < rho)
    (q : Fin (d + 1) → ZMod p)
    (hq : ∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
      epsilon < pureStateTraceDistance
        (finiteGridChoiVector p (d + 1) fun i => a * q i) (target y)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ A : ℝ, ∃ tau ∈ Set.Icc A (A + L),
      (∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        epsilon < pureStateTraceDistance
          (projectivePhaseChoiVector d
            (projectivePhysicalPhaseFlow energy ((a.val : ℝ) * tau)))
          (target y)) ∧
      pureStateTraceDistance
        (projectivePhaseChoiVector d
          (projectivePhysicalPhaseFlow energy ((p : ℝ) * tau)))
        (projectivePhaseChoiVector d 0) < rho := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let U := projectivePrimeCircuitPolygonTarget p d target epsilon rho
  have hUopen : IsOpen U :=
    isOpen_projectivePrimeCircuitPolygonTarget p d target epsilon rho
  have hUne : U.Nonempty :=
    ⟨finiteGridProjectivePhase p d q,
      finiteGridProjectivePhase_mem_polygonTarget p d target htarget hrho q hq⟩
  obtain ⟨L, hL, hhits⟩ := denseAddOrbit_open_hits_syndetically
    (projectivePhysicalPhaseFlowHom energy)
    (denseRange_projectivePhysicalPhaseFlowHom energy hmax) hUopen hUne
  refine ⟨L, hL, fun A => ?_⟩
  obtain ⟨tau, htau, htauU⟩ := hhits A
  refine ⟨tau, htau, ?_, ?_⟩
  · intro a ha y
    have hhard : Real.sqrt 2 * epsilon <
        dist (projectivePhaseChoiDensity d
          (a.val • projectivePhysicalPhaseFlow energy tau))
          (pureStateDensity (target y)) :=
      Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp htauU.1 a) ha) y
    have hflow : projectivePhysicalPhaseFlow energy ((a.val : ℝ) * tau) =
        a.val • projectivePhysicalPhaseFlow energy tau := by
      change projectivePhysicalPhaseFlowHom energy ((a.val : ℝ) * tau) =
        a.val • projectivePhysicalPhaseFlowHom energy tau
      simpa [nsmul_eq_mul] using
        map_nsmul (projectivePhysicalPhaseFlowHom energy) a.val tau
    rw [← hflow, ← pureStateDensity_projectivePhaseChoiVector,
      dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance _ _
        (projectivePhaseChoiVector_norm d _) (htarget y)] at hhard
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  · have hreturn : dist
        (projectivePhaseChoiDensity d
          (p • projectivePhysicalPhaseFlow energy tau))
        (projectivePhaseChoiDensity d 0) < Real.sqrt 2 * rho := htauU.2
    have hflow : projectivePhysicalPhaseFlow energy ((p : ℝ) * tau) =
        p • projectivePhysicalPhaseFlow energy tau := by
      change projectivePhysicalPhaseFlowHom energy ((p : ℝ) * tau) =
        p • projectivePhysicalPhaseFlowHom energy tau
      simpa [nsmul_eq_mul] using
        map_nsmul (projectivePhysicalPhaseFlowHom energy) p tau
    rw [← hflow, ← pureStateDensity_projectivePhaseChoiVector,
      ← pureStateDensity_projectivePhaseChoiVector,
      dist_pureStateDensity_eq_sqrtTwo_mul_traceDistance _ _
        (projectivePhaseChoiVector_norm d _)
        (projectivePhaseChoiVector_norm d 0)] at hreturn
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]

/-- **Replica-budget autonomous hard-polygon law.** The factorial
growing-replica budget alone constructs the strict polygon; maximal
projective rank then makes one ordinary fixed spectrum shadow all its hard
vertices and return endpoint syndetically. -/
theorem maximallyProjective_exists_complete_circuitPolygon_of_replicaBudget
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p d : ℕ) [Fact p.Prime]
    (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (target : Y → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ y, ‖target y‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon < 1 / 2)
    {rho : ℝ} (hrho : 0 < rho)
    (n : ℕ) (hreplica : 2 * n < p)
    (hbudget :
      (((p - 1) * Fintype.card Y : ℕ) : ℝ) * (n.factorial : ℝ) *
          (((d + 1 : ℕ) : ℝ)⁻¹) ^ n <
        (Real.sqrt (1 - 4 * epsilon ^ 2)) ^ (2 * n)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ A : ℝ, ∃ tau ∈ Set.Icc A (A + L),
      (∀ a : ZMod p, a ≠ 0 → ∀ y : Y,
        epsilon < pureStateTraceDistance
          (projectivePhaseChoiVector d
            (projectivePhysicalPhaseFlow energy ((a.val : ℝ) * tau)))
          (target y)) ∧
      pureStateTraceDistance
        (projectivePhaseChoiVector d
          (projectivePhysicalPhaseFlow energy ((p : ℝ) * tau)))
        (projectivePhaseChoiVector d 0) < rho := by
  obtain ⟨q, hq⟩ :=
    exists_primeTorsion_complete_circuitRay_avoidance_of_replicaBudget
      p (d + 1) (Nat.succ_pos d) target htarget hepsilon hepsilonHalf n hreplica
      (by simpa using hbudget)
  exact maximallyProjective_complete_circuitPolygon_shadow_syndetic
    p d energy hmax target htarget hrho q hq

end RHTower
