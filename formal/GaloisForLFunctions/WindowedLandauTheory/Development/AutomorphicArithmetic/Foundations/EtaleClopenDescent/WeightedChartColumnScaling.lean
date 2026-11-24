import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! Unscaling a column identifies its weighted differential with the
Koszul differential for the normalized affine coefficients. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ]
  {d : ℕ} (T : WeightedChartSystem k d S E)

/-- Restrict the system's scalar action to the ring of a chart pair. -/
abbrev chartModule (I J : Finset (Fin (d + 1))) : Module (T.R I J) E :=
  Module.compHom E (T.act.comp (T.R I J).val).toRingHom

/-- The action of the chart ring extends the base-field action. -/
theorem chartScalarTower {I J : Finset (Fin (d + 1))} :
    letI := T.chartModule I J
    IsScalarTower k (T.R I J) E := by
  letI := T.chartModule I J
  refine IsScalarTower.of_algebraMap_smul (fun c a => ?_)
  change T.act (algebraMap k S c) a = c • a
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]

/-- The product of the units used to normalize the selected weights. -/
def normalizationProduct (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (L : Finset κ) : Sˣ :=
  ∏ l ∈ L, T.weightUnit n i j l

/-- Multiply each Koszul component by the product of its normalization
units. The inverse divides by the same product. -/
def scaleColumn (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) :
    (Finset κ → E) ≃ₗ[k] (Finset κ → E) where
  toFun a L := T.act (T.normalizationProduct n i j L : S) (a L)
  invFun a L := T.act ((T.normalizationProduct n i j L)⁻¹ : Sˣ) (a L)
  left_inv a := funext fun L => by
    change T.act ((T.normalizationProduct n i j L)⁻¹ : Sˣ)
      (T.act (T.normalizationProduct n i j L : S) (a L)) = a L
    rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
  right_inv a := funext fun L => by
    change T.act (T.normalizationProduct n i j L : S)
      (T.act ((T.normalizationProduct n i j L)⁻¹ : Sˣ) (a L)) = a L
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
  map_add' a b := funext fun L => map_add _ (a L) (b L)
  map_smul' c a := funext fun L => map_smul _ c (a L)

theorem scaleColumn_wd (n : κ → ℕ × ℕ) (z : κ → S) (i j : Fin (d + 1)) (a : Finset κ → E) :
    T.scaleColumn n i j (wd (fun l => T.act (T.normalizedWeight n z i j l)) a) =
      wd (fun l => T.act (z l)) (T.scaleColumn n i j a) := by
  funext L
  change T.act (T.normalizationProduct n i j L : S)
      (wd (fun l => T.act (T.normalizedWeight n z i j l)) a L) = _
  rw [wd_apply, wd_apply, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_zsmul]
  change _ • T.act _ (T.act _ (a (L.erase l))) =
    _ • T.act _ (T.act _ (a (L.erase l)))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  have hprod : T.normalizationProduct n i j L =
      T.weightUnit n i j l * T.normalizationProduct n i j (L.erase l) :=
    (Finset.mul_prod_erase L _ hl).symm
  let b := T.weightUnit n i j l
  let u := T.normalizationProduct n i j (L.erase l)
  have hcoef : (T.normalizationProduct n i j L : S) * T.normalizedWeight n z i j l =
      z l * (u : S) := by
    rw [hprod, Units.val_mul]
    change (b : S) * (u : S) * (z l * (b⁻¹ : Sˣ)) = _
    calc
      _ = ((b : S) * (b⁻¹ : Sˣ)) * (z l * (u : S)) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, one_mul]
  rw [hcoef]

theorem scaleColumn_mem_terms_iff (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (p : ℤ) (a : Finset κ → E) :
    T.scaleColumn n i j a ∈ (T.columnComplex n z I J).C p ↔
      a ∈ (acx (fun _ => T.M I J) fun l => T.act (T.normalizedWeight n z i j l)).C p := by
  rw [T.columnComplex_eq hT n z hi hj, acx_mem_terms_iff, acx_mem_terms_iff]
  refine forall_congr' fun L => ?_
  let f := T.act (T.normalizationProduct n i j L : S)
  change f (a L) ∈ (if (L.card : ℤ) = p then (T.M I J).map f else ⊥) ↔
    a L ∈ (if (L.card : ℤ) = p then T.M I J else ⊥)
  have hf : Function.Injective f := by
    intro v w h
    let g := T.act ((T.normalizationProduct n i j L)⁻¹ : Sˣ)
    have h' (u : E) : g (f u) = u := by
      change T.act _ (T.act _ u) = _
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one]
      rfl
    exact (h' v).symm.trans ((congrArg g h).trans (h' w))
  by_cases hL : (L.card : ℤ) = p
  · rw [if_pos hL, if_pos hL]
    exact ⟨fun ⟨u, hu, h⟩ => hf h ▸ hu, fun h => ⟨a L, h, rfl⟩⟩
  · rw [if_neg hL, if_neg hL]
    simp only [Submodule.mem_bot]
    exact ⟨fun h => hf (h.trans (map_zero f).symm), fun h => by rw [h, map_zero]⟩

/-- Scaling identifies the cocycles for the normalized and homogeneous
weights on the same chart pair. -/
theorem scaleColumn_mem_cycles_iff (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (p : ℤ) (a : Finset κ → E) :
    T.scaleColumn n i j a ∈ (T.columnComplex n z I J).Z p ↔
      a ∈ (acx (fun _ => T.M I J) fun l => T.act (T.normalizedWeight n z i j l)).Z p := by
  let f := T.scaleColumn n i j
  have hD (v : Finset κ → E) :
      wd (fun l => T.act (z l)) (f v) = 0 ↔
        wd (fun l => T.act (T.normalizedWeight n z i j l)) v = 0 := by
    rw [← T.scaleColumn_wd]
    exact ⟨fun h => f.injective (h.trans (map_zero f).symm),
      fun h => by rw [h, map_zero]⟩
  exact ⟨fun ha => ⟨(T.scaleColumn_mem_terms_iff hT n z hi hj p a).mp ha.1, (hD a).mp ha.2⟩,
    fun ha => ⟨(T.scaleColumn_mem_terms_iff hT n z hi hj p a).mpr ha.1, (hD a).mpr ha.2⟩⟩

/-- The same scaling identifies boundaries and their primitives. -/
theorem scaleColumn_mem_boundaries_iff (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (p : ℤ) (a : Finset κ → E) :
    T.scaleColumn n i j a ∈ (T.columnComplex n z I J).B p ↔
      a ∈ (acx (fun _ => T.M I J) fun l => T.act (T.normalizedWeight n z i j l)).B p := by
  let f := T.scaleColumn n i j
  constructor
  · rintro ⟨b, hb, hbd⟩
    let u := f.symm b
    have hu : f u = b := f.apply_symm_apply b
    refine ⟨u, (T.scaleColumn_mem_terms_iff hT n z hi hj (p - 1) u).mp (hu.symm ▸ hb), ?_⟩
    apply f.injective
    change T.scaleColumn n i j (wd _ u) = f a
    rw [T.scaleColumn_wd, hu]
    exact hbd
  · rintro ⟨u, hu, hud⟩
    refine ⟨f u, (T.scaleColumn_mem_terms_iff hT n z hi hj (p - 1) u).mpr hu, ?_⟩
    change wd (fun l => T.act (z l)) (f u) = f a
    rw [← T.scaleColumn_wd]
    exact congrArg f hud

/-- Column exactness for the normalized affine sequence transfers to
the original weighted column. -/
theorem columnExact_of_normalized (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (p : ℤ)
    (h : let C := acx (fun _ => T.M I J) (fun l => T.act (T.normalizedWeight n z i j l))
      C.Z p ≤ C.B p) :
    (T.columnComplex n z I J).Z p ≤ (T.columnComplex n z I J).B p := by
  let f := T.scaleColumn n i j
  intro a ha
  let b := f.symm a
  have hb : f b = a := f.apply_symm_apply a
  have hbZ := (T.scaleColumn_mem_cycles_iff hT n z hi hj p b).mp (hb.symm ▸ ha)
  exact hb ▸ (T.scaleColumn_mem_boundaries_iff hT n z hi hj p b).mpr (h hbZ)

end GlobalTheory.WH.WeightedChartSystem
