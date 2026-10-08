import GaloisForLFunctions.RHTower.WeilPaperEnergyPreservingHomotopy
import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of native laws and every attained full-energy level

Intrinsic convex interpolation contracts all native laws to any chosen native
base. The same interpolation contracts an exact energy fiber while preserving
its defining equality. Applying the realification retraction gives the analogous
contraction inside the symmetric real-test fiber.
-/

open Filter Set Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- Every native law space contracts to any chosen native base law. -/
def paperNativeContraction (a : Set.range spectralRepresentingMeasure) :
    ContinuousMap.Homotopy (ContinuousMap.id (Set.range spectralRepresentingMeasure))
      (ContinuousMap.const _ a) where
  toFun p := paperNativeConvexCombination p.2 a p.1
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact tendsto_paperNativeConvexCombination
      (continuous_snd.tendsto p) tendsto_const_nhds (continuous_fst.tendsto p)
  map_zero_left μ := paperNativeConvexCombination_zero μ a
  map_one_left μ := paperNativeConvexCombination_one μ a

/-- The actual native spectral-law space is contractible. -/
theorem contractibleSpace_nativeSpectralLaws :
    ContractibleSpace (Set.range spectralRepresentingMeasure) := by
  obtain ⟨c, _⟩ := exists_complexNullMixture_energy_gt 0
  let a : Set.range spectralRepresentingMeasure :=
    ⟨spectralRepresentingMeasure c, Set.mem_range_self c⟩
  exact (contractible_iff_id_nullhomotopic _).mpr ⟨a, ⟨paperNativeContraction a⟩⟩

/-- The exact full-energy level through an actual native law. -/
abbrev PaperNativeEnergyFiber (a : Set.range spectralRepresentingMeasure) :=
  {μ : Set.range spectralRepresentingMeasure | paperNativeSpectralEnergy μ = paperNativeSpectralEnergy a}

def paperNativeEnergyBasepoint (a : Set.range spectralRepresentingMeasure) :
    PaperNativeEnergyFiber a := ⟨a, rfl⟩

/-- Convex interpolation contracts an exact energy fiber without leaving that fiber. -/
def paperNativeEnergyContraction (a : Set.range spectralRepresentingMeasure) :
    ContinuousMap.Homotopy (ContinuousMap.id (PaperNativeEnergyFiber a))
      (ContinuousMap.const _ (paperNativeEnergyBasepoint a)) where
  toFun p := ⟨paperNativeConvexCombination p.2.1 a p.1, by
    change paperNativeSpectralEnergy (paperNativeConvexCombination p.2.1 a p.1) =
      paperNativeSpectralEnergy a
    rw [paperNativeSpectralEnergy_convexCombination, p.2.2]
    ring⟩
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_subtype_rng.mpr
    exact tendsto_paperNativeConvexCombination
      ((continuous_subtype_val.comp continuous_snd).tendsto p)
      tendsto_const_nhds (continuous_fst.tendsto p)
  map_zero_left μ := Subtype.ext (paperNativeConvexCombination_zero μ.1 a)
  map_one_left μ := Subtype.ext (paperNativeConvexCombination_one μ.1 a)

/-- The contraction fixes its basepoint at every time. -/
theorem paperNativeEnergyContraction_fixed (a : Set.range spectralRepresentingMeasure)
    (t : Set.Icc (0 : ℝ) 1) :
    paperNativeEnergyContraction a (t, paperNativeEnergyBasepoint a) =
      paperNativeEnergyBasepoint a :=
  Subtype.ext (paperNativeConvexCombination_self a t)

/-- Every full-energy value already attained by a native law has a contractible exact level. -/
theorem contractibleSpace_paperNativeEnergyFiber (a : Set.range spectralRepresentingMeasure) :
    ContractibleSpace (PaperNativeEnergyFiber a) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨paperNativeEnergyBasepoint a, ⟨paperNativeEnergyContraction a⟩⟩

/-- An exact energy level within the real-test, inversion-symmetric native image. -/
abbrev PaperSymmetricNativeEnergyFiber (a : Set.range paperNativeRealification) :=
  {μ : Set.range paperNativeRealification |
    paperNativeSpectralEnergy μ.1 = paperNativeSpectralEnergy a.1}

def paperSymmetricEnergyBasepoint (a : Set.range paperNativeRealification) :
    PaperSymmetricNativeEnergyFiber a := ⟨a, rfl⟩

/-- Convex interpolation followed by realification contracts the exact symmetric energy level. -/
def paperSymmetricEnergyContraction (a : Set.range paperNativeRealification) :
    ContinuousMap.Homotopy (ContinuousMap.id (PaperSymmetricNativeEnergyFiber a))
      (ContinuousMap.const _ (paperSymmetricEnergyBasepoint a)) where
  toFun p := ⟨paperNativeRealificationRetraction
    (paperNativeConvexCombination p.2.1.1 a.1 p.1), by
      change paperNativeSpectralEnergy (paperNativeRealification
        (paperNativeConvexCombination p.2.1.1 a.1 p.1)) = _
      rw [paperNativeSpectralEnergy_realification,
        paperNativeSpectralEnergy_convexCombination, p.2.2]
      ring⟩
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply tendsto_subtype_rng.mpr
    apply (paperNativeRealificationRetraction.continuous.tendsto _).comp
    exact tendsto_paperNativeConvexCombination
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).tendsto p)
      tendsto_const_nhds (continuous_fst.tendsto p)
  map_zero_left μ := by
    apply Subtype.ext
    change paperNativeRealificationRetraction (paperNativeConvexCombination μ.1.1 a.1 0) = μ.1
    rw [paperNativeConvexCombination_zero, paperNativeRealificationRetraction_coe]
  map_one_left μ := by
    apply Subtype.ext
    change paperNativeRealificationRetraction (paperNativeConvexCombination μ.1.1 a.1 1) = a
    rw [paperNativeConvexCombination_one, paperNativeRealificationRetraction_coe]

/-- The symmetric energy contraction also fixes its chosen base law. -/
theorem paperSymmetricEnergyContraction_fixed (a : Set.range paperNativeRealification)
    (t : Set.Icc (0 : ℝ) 1) :
    paperSymmetricEnergyContraction a (t, paperSymmetricEnergyBasepoint a) =
      paperSymmetricEnergyBasepoint a := by
  apply Subtype.ext
  change paperNativeRealificationRetraction (paperNativeConvexCombination a.1 a.1 t) = a
  rw [paperNativeConvexCombination_self, paperNativeRealificationRetraction_coe]

/-- Every attained symmetric real-test energy level is contractible in its own weak topology. -/
theorem contractibleSpace_paperSymmetricNativeEnergyFiber (a : Set.range paperNativeRealification) :
    ContractibleSpace (PaperSymmetricNativeEnergyFiber a) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨paperSymmetricEnergyBasepoint a, ⟨paperSymmetricEnergyContraction a⟩⟩

end RHTower.WeilWorkPBAP
