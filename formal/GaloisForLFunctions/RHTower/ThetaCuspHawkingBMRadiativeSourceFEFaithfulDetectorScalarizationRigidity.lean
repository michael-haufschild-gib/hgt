import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFEHorizonBoundaryRelativeCocycleRigidity

/-!
# Faithful horizon/boundary detector scalarization rigidity

HC92 proves that common diagonal phase gauge cannot erase the relative source-FE holonomy between
the physical horizon and normalizable AdS-boundary readouts. This module closes the much larger
linear-detector loophole, including arbitrary nonscalar and singular compression.

The two-channel detector cocycle is diagonal with the actual HC89 horizon cocycle and HC92 boundary
cocycle. Any complex-linear detector map seeing one scalar FE gain on a tilted Xi fibre must kill
the horizon basis axis or the boundary basis axis. Conversely either axis deletion scalarizes the
surviving eigenchannel, so this is an exact classification, not merely a non-injectivity result.

Hence every faithful detector scalarization is possible exactly on the critical line. Even allowing
a different faithful detector map at every Xi copy, global scalarization is equivalent to RH.
Off-line singular escape exists only by discarding one complete physical readout.

[NEW] [FAITHFUL DETECTOR] [SINGULAR CLASSIFICATION] [AXIS LOSS] [RH EQUIVALENCE]
-/

open Complex Real

namespace RHTower

noncomputable section

abbrev HBXiRadiativeDetectorCarrier := ℂ × ℂ

def hbXiRadiativeHorizonDetectorBasis : HBXiRadiativeDetectorCarrier := (1, 0)

def hbXiRadiativeBoundaryDetectorBasis : HBXiRadiativeDetectorCarrier := (0, 1)

def hbXiRadiativeHorizonBoundaryDetectorCocycle (q : XiZeroCopy) :
    HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier where
  toFun x :=
    (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q * x.1,
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q * x.2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' c x := by ext <;> simp <;> ring

def HBXiRadiativeDetectorScalarizes
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (c : ℂ) (q : XiZeroCopy) : Prop :=
  ∀ x : HBXiRadiativeDetectorCarrier, L (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) = c • L x

theorem hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
        hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  simpa [hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryDiagonalGaugedCocycle,
    hbXiPhaseSensitiveUnitRadiativeSourceFEDiagonalGaugedCocycle] using
    (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryHorizonGaugedCocycle_eq_iff_re_eq_half
      (fun _ => 1) (fun _ => one_ne_zero) q)

theorem hbXiRadiativeDetectorCocycle_horizonBasis (q : XiZeroCopy) :
    hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeHorizonDetectorBasis =
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q • hbXiRadiativeHorizonDetectorBasis := by
  ext <;> simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, hbXiRadiativeHorizonDetectorBasis]

theorem hbXiRadiativeDetectorCocycle_boundaryBasis (q : XiZeroCopy) :
    hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeBoundaryDetectorBasis =
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q •
        hbXiRadiativeBoundaryDetectorBasis := by
  ext <;> simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, hbXiRadiativeBoundaryDetectorBasis]

theorem hbXiRadiativeDetectorScalarizes_horizonBasis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeDetectorScalarizes L c q) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q • L hbXiRadiativeHorizonDetectorBasis =
      c • L hbXiRadiativeHorizonDetectorBasis := by
  calc
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q • L hbXiRadiativeHorizonDetectorBasis =
        L (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q •
          hbXiRadiativeHorizonDetectorBasis) := (L.map_smul _ _).symm
    _ = L (hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeHorizonDetectorBasis) := by
      rw [hbXiRadiativeDetectorCocycle_horizonBasis]
    _ = c • L hbXiRadiativeHorizonDetectorBasis := hscalar hbXiRadiativeHorizonDetectorBasis

theorem hbXiRadiativeDetectorScalarizes_boundaryBasis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeDetectorScalarizes L c q) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q •
        L hbXiRadiativeBoundaryDetectorBasis = c • L hbXiRadiativeBoundaryDetectorBasis := by
  calc
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q •
        L hbXiRadiativeBoundaryDetectorBasis =
      L (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q •
        hbXiRadiativeBoundaryDetectorBasis) := (L.map_smul _ _).symm
    _ = L (hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeBoundaryDetectorBasis) := by
      rw [hbXiRadiativeDetectorCocycle_boundaryBasis]
    _ = c • L hbXiRadiativeBoundaryDetectorBasis := hscalar hbXiRadiativeBoundaryDetectorBasis

theorem hbXiRadiativeFaithfulDetectorScalarization_forces_cocycles_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (hL : Function.Injective L)
    (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeDetectorScalarizes L c q) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q =
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q := by
  have hH :
      hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeHorizonDetectorBasis =
        c • hbXiRadiativeHorizonDetectorBasis := by
    apply hL
    rw [L.map_smul]
    exact hscalar hbXiRadiativeHorizonDetectorBasis
  have hB :
      hbXiRadiativeHorizonBoundaryDetectorCocycle q hbXiRadiativeBoundaryDetectorBasis =
        c • hbXiRadiativeBoundaryDetectorBasis := by
    apply hL
    rw [L.map_smul]
    exact hscalar hbXiRadiativeBoundaryDetectorBasis
  have hcH : hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q = c := by
    simpa [hbXiRadiativeHorizonBoundaryDetectorCocycle, hbXiRadiativeHorizonDetectorBasis] using
      congrArg Prod.fst hH
  have hcB :
      hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q = c := by
    simpa [hbXiRadiativeHorizonBoundaryDetectorCocycle, hbXiRadiativeBoundaryDetectorBasis] using
      congrArg Prod.snd hB
  exact hcH.trans hcB.symm

theorem hbXiRadiativeFaithfulDetectorScalarization_forces_re_eq_half
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (hL : Function.Injective L)
    (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeDetectorScalarizes L c q) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mp
  exact (hbXiRadiativeFaithfulDetectorScalarization_forces_cocycles_eq L hL c q hscalar).symm

theorem hbXiRadiativeDetectorScalarization_kills_axis_of_offLine
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (c : ℂ) (q : XiZeroCopy)
    (hscalar : HBXiRadiativeDetectorScalarizes L c q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    L hbXiRadiativeHorizonDetectorBasis = 0 ∨ L hbXiRadiativeBoundaryDetectorBasis = 0 := by
  by_cases hH0 : L hbXiRadiativeHorizonDetectorBasis = 0
  · exact Or.inl hH0
  by_cases hB0 : L hbXiRadiativeBoundaryDetectorBasis = 0
  · exact Or.inr hB0
  exfalso
  have hH := hbXiRadiativeDetectorScalarizes_horizonBasis L c q hscalar
  have hB := hbXiRadiativeDetectorScalarizes_boundaryBasis L c q hscalar
  have hzH :
      (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q - c) •
          L hbXiRadiativeHorizonDetectorBasis = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hH
  have hzB :
      (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q - c) •
          L hbXiRadiativeBoundaryDetectorBasis = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hB
  have hcH : hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q = c :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzH).resolve_right hH0)
  have hcB : hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q = c :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzB).resolve_right hB0)
  apply hoff
  apply (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mp
  exact hcB.trans hcH.symm

theorem hbXiRadiativeDetectorCarrier_decomposition (x : HBXiRadiativeDetectorCarrier) :
    x = x.1 • hbXiRadiativeHorizonDetectorBasis + x.2 • hbXiRadiativeBoundaryDetectorBasis := by
  apply Prod.ext <;> simp [hbXiRadiativeHorizonDetectorBasis, hbXiRadiativeBoundaryDetectorBasis]

theorem hbXiRadiativeDetectorMap_eq_boundary_smul_of_horizonBasis_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (hH0 : L hbXiRadiativeHorizonDetectorBasis = 0)
    (x : HBXiRadiativeDetectorCarrier) :
    L x = x.2 • L hbXiRadiativeBoundaryDetectorBasis := by
  conv_lhs => rw [hbXiRadiativeDetectorCarrier_decomposition x]
  rw [map_add, map_smul, map_smul, hH0, smul_zero, zero_add]

theorem hbXiRadiativeDetectorMap_eq_horizon_smul_of_boundaryBasis_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (hB0 : L hbXiRadiativeBoundaryDetectorBasis = 0)
    (x : HBXiRadiativeDetectorCarrier) :
    L x = x.1 • L hbXiRadiativeHorizonDetectorBasis := by
  conv_lhs => rw [hbXiRadiativeDetectorCarrier_decomposition x]
  rw [map_add, map_smul, map_smul, hB0, smul_zero, add_zero]

theorem hbXiRadiativeDetectorScalarizes_boundaryGain_of_horizonBasis_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (hH0 : L hbXiRadiativeHorizonDetectorBasis = 0) (q : XiZeroCopy) :
    HBXiRadiativeDetectorScalarizes L
      (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q) q := by
  intro x
  calc
    L (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) =
        (hbXiRadiativeHorizonBoundaryDetectorCocycle q x).2 • L hbXiRadiativeBoundaryDetectorBasis :=
      hbXiRadiativeDetectorMap_eq_boundary_smul_of_horizonBasis_eq_zero L hH0 _
    _ = (hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q * x.2) •
        L hbXiRadiativeBoundaryDetectorBasis := rfl
    _ = hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q •
        (x.2 • L hbXiRadiativeBoundaryDetectorBasis) := by rw [mul_smul]
    _ = hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q • L x := by
      exact congrArg
        (fun y => hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q • y)
        (hbXiRadiativeDetectorMap_eq_boundary_smul_of_horizonBasis_eq_zero L hH0 x).symm

theorem hbXiRadiativeDetectorScalarizes_horizonGain_of_boundaryBasis_eq_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V)
    (hB0 : L hbXiRadiativeBoundaryDetectorBasis = 0) (q : XiZeroCopy) :
    HBXiRadiativeDetectorScalarizes L
      (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) q := by
  intro x
  calc
    L (hbXiRadiativeHorizonBoundaryDetectorCocycle q x) =
        (hbXiRadiativeHorizonBoundaryDetectorCocycle q x).1 • L hbXiRadiativeHorizonDetectorBasis :=
      hbXiRadiativeDetectorMap_eq_horizon_smul_of_boundaryBasis_eq_zero L hB0 _
    _ = (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q * x.1) •
        L hbXiRadiativeHorizonDetectorBasis := rfl
    _ = hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q •
        (x.1 • L hbXiRadiativeHorizonDetectorBasis) := by rw [mul_smul]
    _ = hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q • L x := by
      exact congrArg
        (fun y => hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q • y)
        (hbXiRadiativeDetectorMap_eq_horizon_smul_of_boundaryBasis_eq_zero L hB0 x).symm

theorem hbXiRadiativeDetectorScalarizable_iff_axisLoss_of_offLine
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] V) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (∃ c : ℂ, HBXiRadiativeDetectorScalarizes L c q) ↔
      L hbXiRadiativeHorizonDetectorBasis = 0 ∨ L hbXiRadiativeBoundaryDetectorBasis = 0 := by
  constructor
  · rintro ⟨c, hscalar⟩
    exact hbXiRadiativeDetectorScalarization_kills_axis_of_offLine L c q hscalar hoff
  · rintro (hH0 | hB0)
    · exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q,
        hbXiRadiativeDetectorScalarizes_boundaryGain_of_horizonBasis_eq_zero L hH0 q⟩
    · exact ⟨hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q,
        hbXiRadiativeDetectorScalarizes_horizonGain_of_boundaryBasis_eq_zero L hB0 q⟩

def HBXiRadiativeFaithfulDetectorScalarizationAt (q : XiZeroCopy) : Prop :=
  ∃ L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier,
    Function.Injective L ∧
      ∃ c : ℂ, HBXiRadiativeDetectorScalarizes L c q

theorem hbXiRadiativeFaithfulDetectorScalarizationAt_iff_re_eq_half (q : XiZeroCopy) :
    HBXiRadiativeFaithfulDetectorScalarizationAt q ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨L, hL, c, hscalar⟩
    exact hbXiRadiativeFaithfulDetectorScalarization_forces_re_eq_half L hL c q hscalar
  · intro hline
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    refine ⟨LinearMap.id, Function.injective_id,
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q, ?_⟩
    intro x
    apply Prod.ext <;> simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

def HBXiRadiativeGlobalFaithfulDetectorScalarization : Prop :=
  ∃ L : XiZeroCopy →
      (HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier),
    (∀ q : XiZeroCopy, Function.Injective (L q)) ∧
      ∃ c : XiZeroCopy → ℂ,
        ∀ q : XiZeroCopy, HBXiRadiativeDetectorScalarizes (L q) (c q) q

theorem hbXiRadiativeGlobalFaithfulDetectorScalarization_iff_rh :
    HBXiRadiativeGlobalFaithfulDetectorScalarization ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨L, hL, c, hscalar⟩
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact hbXiRadiativeFaithfulDetectorScalarization_forces_re_eq_half (L q) (hL q) (c q) q
      (hscalar q)
  · intro hRH
    refine ⟨fun _ => LinearMap.id, fun _ => Function.injective_id,
      fun q => hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q, ?_⟩
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp
        ((forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr
          hRH q)
    have heq :
        hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
          hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q :=
      (hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half q).mpr hline
    intro x
    apply Prod.ext <;> simp [hbXiRadiativeHorizonBoundaryDetectorCocycle, heq]

def HBXiRadiativeFaithfulDetectorScalarizationRigidity : Prop :=
  (∀ q : XiZeroCopy,
    hbXiPhaseSensitiveUnitRadiativeSourceFEBoundaryCocycle q =
        hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier)
      (c : ℂ) (q : XiZeroCopy),
    Function.Injective L → HBXiRadiativeDetectorScalarizes L c q →
      (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (L : HBXiRadiativeDetectorCarrier →ₗ[ℂ] HBXiRadiativeDetectorCarrier)
      (q : XiZeroCopy),
    (q.1 : ℂ).re ≠ 1 / 2 →
      ((∃ c : ℂ, HBXiRadiativeDetectorScalarizes L c q) ↔
        L hbXiRadiativeHorizonDetectorBasis = 0 ∨ L hbXiRadiativeBoundaryDetectorBasis = 0)) ∧
  (∀ q : XiZeroCopy,
    HBXiRadiativeFaithfulDetectorScalarizationAt q ↔ (q.1 : ℂ).re = 1 / 2) ∧
  (HBXiRadiativeGlobalFaithfulDetectorScalarization ↔ RiemannHypothesis)

theorem hbXiRadiativeFaithfulDetectorScalarizationRigidity :
    HBXiRadiativeFaithfulDetectorScalarizationRigidity := by
  refine ⟨hbXiRadiativeBoundaryCocycle_eq_horizonCocycle_iff_re_eq_half,
    ?_, ?_, hbXiRadiativeFaithfulDetectorScalarizationAt_iff_re_eq_half,
    hbXiRadiativeGlobalFaithfulDetectorScalarization_iff_rh⟩
  · intro L c q hL hscalar
    exact hbXiRadiativeFaithfulDetectorScalarization_forces_re_eq_half L hL c q hscalar
  · intro L q hoff
    exact hbXiRadiativeDetectorScalarizable_iff_axisLoss_of_offLine L q hoff

end
end RHTower

