import GaloisForLFunctions.HTGeometry.ProperFiniteFiberIntervalExtension
import GaloisForLFunctions.HTGeometry.OrderedCriticalValueCovering
import GaloisForLFunctions.HTGeometry.OrderedCriticalValueFiniteFibers
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Set Filter Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- An actual critical-value path, regular before its final time, lifts uniquely through
the terminal collision from any specified initial realization. -/
theorem existsUnique_valuesWithConstant_collision_path_lift {n : ℕ}
    (b : C(I, Fin (n + 1) → ℂ))
    (hb : ∀ t : I, (t : ℝ) < 1 → Function.Injective (b t))
    (v₀ : Parameter n) (hv₀ : valuesWithConstant v₀ = b 0) :
    ∃! v : C(I, Parameter n), v 0 = v₀ ∧ ∀ t, valuesWithConstant (v t) = b t := by
  classical
  let J := Ico (0 : ℝ) 1
  let j₀ : J := ⟨0, le_rfl, zero_lt_one⟩
  let e : J → I := fun t => ⟨t, t.property.1, t.property.2.le⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  let γ : C(J, Configuration n) := ⟨fun t => ⟨b (e t), hb (e t) t.property.2⟩,
    (b.continuous.comp he).subtype_mk (fun t => hb (e t) t.property.2)⟩
  let p₀ : RegularParameter n := ⟨v₀, by rw [hv₀]; exact hb 0 zero_lt_one⟩
  letI : ContractibleSpace J :=
    (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_lt_one⟩
  letI : LocallyPathConnectedSpace J :=
    (convex_Ico (0 : ℝ) 1).locallyPathConnectedSpace
  have hp₀ : regularMap n p₀ = γ j₀ := Subtype.ext hv₀
  obtain ⟨L, ⟨hL₀, hL⟩, huniq⟩ :=
    (isCoveringMap_regularMap n).existsUnique_continuousMap_lifts γ j₀ p₀ hp₀
  have hLval (t : J) : valuesWithConstant (L t).val = b (e t) :=
    congrArg Subtype.val (congr_fun hL t)
  let vr : ℝ → Parameter n := fun t => if ht : t ∈ J then (L ⟨t, ht⟩).val else v₀
  have hvr (t : J) : vr t = (L t).val := dif_pos t.property
  have hcvr : ContinuousOn vr J := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact (continuous_subtype_val.comp L.continuous).congr (fun t => (hvr t).symm)
  let br : C(ℝ, Fin (n + 1) → ℂ) := b.IccExtend (by norm_num)
  have hbr (t : I) : br t = b t := Set.IccExtend_of_mem _ b t.property
  have hvrb (t : ℝ) (ht : t ∈ J) : valuesWithConstant (vr t) = br t := by
    let ht' : J := ⟨t, ht⟩
    calc
      valuesWithConstant (vr t) = valuesWithConstant (L ht').val := congrArg _ (hvr ht')
      _ = b (e ht') := hLval ht'
      _ = br t := (hbr (e ht')).symm
  obtain ⟨V, hV₀, hVB, hVhalf⟩ :=
    exists_closed_interval_extension_of_proper_finite_fiber
      (isProperMap_valuesWithConstant n) hcvr br hvrb (finite_valuesWithConstant_fiber (br 1))
  have hVstart : V 0 = v₀ := hV₀.trans ((hvr j₀).trans (congrArg Subtype.val hL₀))
  have hVb (t : I) : valuesWithConstant (V t) = b t := (hVB t).trans (hbr t)
  refine ⟨V, ⟨hVstart, hVb⟩, ?_⟩
  intro W hW
  have hWreg (t : J) : Function.Injective (valuesWithConstant (W (e t))) := by
    rw [hW.2]
    exact hb (e t) t.property.2
  let WL : C(J, RegularParameter n) := ⟨fun t => ⟨W (e t), hWreg t⟩,
    (W.continuous.comp he).subtype_mk hWreg⟩
  have hWL₀ : WL j₀ = p₀ := Subtype.ext hW.1
  have hWL : regularMap n ∘ WL = γ := by
    funext t
    exact Subtype.ext (hW.2 (e t))
  have hWLeq : WL = L := huniq WL ⟨hWL₀, hWL⟩
  have hWeq (t : J) : W (e t) = V (e t) := by
    calc
      W (e t) = (L t).val := congrArg (fun F : C(J, RegularParameter n) => (F t).val) hWLeq
      _ = vr t := (hvr t).symm
      _ = V (e t) := (hVhalf (e t) t.property.2).symm
  let Wr := W.IccExtend (by norm_num : (0 : ℝ) ≤ 1)
  let Vr := V.IccExtend (by norm_num : (0 : ℝ) ≤ 1)
  have hreal : EqOn Wr Vr J := by
    intro t ht
    let tt : J := ⟨t, ht⟩
    calc
      Wr t = W (e tt) := Set.IccExtend_of_mem _ W (e tt).property
      _ = V (e tt) := hWeq tt
      _ = Vr t := (Set.IccExtend_of_mem _ V (e tt).property).symm
  have hclosed := hreal.closure Wr.continuous Vr.continuous
  apply ContinuousMap.ext
  intro t
  have ht : (t : ℝ) ∈ closure J := by
    change (t : ℝ) ∈ closure (Ico (0 : ℝ) 1)
    rw [closure_Ico (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact t.property
  exact (Set.IccExtend_of_mem _ W t.property).symm.trans
    ((hclosed ht).trans (Set.IccExtend_of_mem _ V t.property))

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
