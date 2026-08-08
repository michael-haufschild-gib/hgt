import GaloisForLFunctions.RHTower.DeningerStructureSheafMaps

/-!
# Extending a function from a coordinate divisor

A holomorphic function on the divisor of the last coordinate extends to a neighbourhood in the
ambient domain: forget the last coordinate.  That map is complex linear and constant in the
direction of the divisor, so the extension is again holomorphic, and it restricts back to the given
function.  Away from the divisor there is nothing to extend, so restriction to the divisor is a
locally surjective morphism of sheaves — an epimorphism.

* `RHTower.deningerChopMap` : forgetting the last coordinate.
* `RHTower.deningerDivisorRestrict_locallySurjective` : restriction is locally surjective.
* `RHTower.deningerDivisorRestrict_epi` : restriction is an epimorphism.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section ChopMap

variable {n : ℕ}

/-- **Forgetting the last coordinate.** -/
def deningerChopMap (z : Fin (n + 1) → ℂ) : Fin n → ℂ := fun j => z j.castSucc

@[simp] theorem deningerChopMap_apply (z : Fin (n + 1) → ℂ) (j : Fin n) :
    deningerChopMap z j = z j.castSucc := rfl

@[simp] theorem deningerChopMap_divisorMap (w : Fin n → ℂ) :
    deningerChopMap (deningerDivisorMap w) = w := by
  funext j
  rw [deningerChopMap_apply, deningerDivisorMap_castSucc]

theorem deningerDivisorMap_chopMap {z : Fin (n + 1) → ℂ} (hz : z (Fin.last n) = 0) :
    deningerDivisorMap (deningerChopMap z) = z := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [deningerDivisorMap_last, hz]
  · intro j
    rw [deningerDivisorMap_castSucc, deningerChopMap_apply]

theorem continuous_deningerChopMap : Continuous (deningerChopMap (n := n)) :=
  continuous_pi fun j => continuous_apply j.castSucc

theorem contDiff_deningerChopMap :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deningerChopMap (n := n)) :=
  contDiff_pi.2 fun j => contDiff_coord j.castSucc

/-- Forgetting the last coordinate commutes with updating an earlier one. -/
theorem deningerChopMap_update_castSucc (z : Fin (n + 1) → ℂ) (j : Fin n) (t : ℂ) :
    deningerChopMap (Function.update z j.castSucc t)
      = Function.update (deningerChopMap z) j t := by
  funext k
  by_cases hjk : k = j
  · subst hjk
    rw [deningerChopMap_apply, Function.update_self, Function.update_self]
  · rw [deningerChopMap_apply,
      Function.update_of_ne (fun h => hjk (Fin.castSucc_injective n h)),
      Function.update_of_ne hjk, deningerChopMap_apply]

/-- Forgetting the last coordinate ignores an update of the last one. -/
theorem deningerChopMap_update_last (z : Fin (n + 1) → ℂ) (t : ℂ) :
    deningerChopMap (Function.update z (Fin.last n) t) = deningerChopMap z := by
  funext k
  rw [deningerChopMap_apply,
    Function.update_of_ne (Fin.castSucc_lt_last k).ne, deningerChopMap_apply]

/-- **The antiholomorphic derivatives of a function pulled back from the divisor.**  In an earlier
direction it is the derivative of the function; in the last direction it vanishes, because the
pullback does not use that coordinate. -/
theorem dzbarAt_comp_chopMap_castSucc (G : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin (n + 1) → ℂ) :
    dzbarAt (fun x => G (deningerChopMap x)) j.castSucc z
      = dzbarAt G j (deningerChopMap z) := by
  have hslice : dbarSlice (fun x => G (deningerChopMap x)) j.castSucc z
      = dbarSlice G j (deningerChopMap z) := by
    funext t
    show G (deningerChopMap (Function.update z j.castSucc t))
      = G (Function.update (deningerChopMap z) j t)
    rw [deningerChopMap_update_castSucc]
  show dzbar (dbarSlice (fun x => G (deningerChopMap x)) j.castSucc z) (z j.castSucc) = _
  rw [hslice]
  rfl

theorem dzbarAt_comp_chopMap_last (G : (Fin n → ℂ) → ℂ) (z : Fin (n + 1) → ℂ) :
    dzbarAt (fun x => G (deningerChopMap x)) (Fin.last n) z = 0 := by
  have hslice : dbarSlice (fun x => G (deningerChopMap x)) (Fin.last n) z
      = fun _ => G (deningerChopMap z) := by
    funext t
    show G (deningerChopMap (Function.update z (Fin.last n) t)) = G (deningerChopMap z)
    rw [deningerChopMap_update_last]
  show dzbar (dbarSlice (fun x => G (deningerChopMap x)) (Fin.last n) z) (z (Fin.last n)) = 0
  rw [hslice]
  exact (dzbar_eq_zero_of_differentiableAt (differentiableAt_const _)).1

/-- A form on the divisor pulled back to the ambient domain, constant in the last coordinate. -/
noncomputable def deningerChopPullback (g : SetForm n) : SetForm (n + 1) :=
  fun S z => if S = ∅ then g ∅ (deningerChopMap z) else 0

@[simp] theorem deningerChopPullback_empty (g : SetForm n) (z : Fin (n + 1) → ℂ) :
    deningerChopPullback g ∅ z = g ∅ (deningerChopMap z) := if_pos rfl

@[simp] theorem deningerChopPullback_ne (g : SetForm n) {S : Finset (Fin (n + 1))}
    (hS : S ≠ ∅) (z : Fin (n + 1) → ℂ) : deningerChopPullback g S z = 0 := if_neg hS

theorem deningerChopPullback_smooth {g : SetForm n} (hg : SmoothSetForm g) :
    SmoothSetForm (deningerChopPullback g) := by
  intro S
  by_cases hS : S = ∅
  · subst hS
    exact (hg ∅).comp contDiff_deningerChopMap
  · simpa only [show deningerChopPullback g S = fun _ => (0 : ℂ) from
      funext fun z => deningerChopPullback_ne g hS z] using contDiff_const

theorem deningerChopPullback_deg (g : SetForm n) : SetFormDeg 0 (deningerChopPullback g) := by
  intro S hS z
  exact deningerChopPullback_ne g (fun h => hS (by rw [h]; rfl)) z

/-- **The pullback of a closed form from the divisor is closed.**  Only singleton indices
contribute, the last direction contributes nothing, and each earlier direction reads the
corresponding derivative on the divisor. -/
theorem setDbar_deningerChopPullback_eq_zero {g : SetForm n} {z : Fin (n + 1) → ℂ}
    (hg : ∀ j : Fin n, dzbarAt (g ∅) j (deningerChopMap z) = 0) (S : Finset (Fin (n + 1))) :
    setDbar (deningerChopPullback g) S z = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  refine mul_eq_zero_of_right _ ?_
  by_cases hk : S.erase k = ∅
  · rw [hk, show deningerChopPullback g ∅ = fun x => g ∅ (deningerChopMap x) from
      funext fun x => deningerChopPullback_empty g x]
    refine Fin.lastCases ?_ ?_ k
    · exact dzbarAt_comp_chopMap_last (g ∅) z
    · intro j
      rw [dzbarAt_comp_chopMap_castSucc, hg j]
  · rw [show deningerChopPullback g (S.erase k) = fun _ => (0 : ℂ) from
      funext fun x => deningerChopPullback_ne g hk x]
    exact dzbarAt_zero k z

end ChopMap

end RHTower

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section Surjectivity

variable {n : ℕ} {Ω : Opens (Fin (n + 1) → ℂ)} {Ω' : Opens (Fin n → ℂ)}
  (hmap : ∀ w ∈ Ω', deningerDivisorMap w ∈ Ω)

/-- The complement of the divisor is open. -/
theorem deningerOffDivisor_isOpen :
    IsOpen {z : Fin (n + 1) → ℂ | z (Fin.last n) ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_apply (Fin.last n))

/-- A closed form on the divisor has vanishing antiholomorphic derivatives where its model is
valid. -/
theorem deningerDivisorModel_dzbar_eq_zero {U' : Opens (deningerSpace Ω')}
    {h : ↥U' → DeningerFormVal n} (hh : DeningerClosedFormPred 0 h) {g : SetForm n}
    {N : Set (Fin n → ℂ)} (hNopen : IsOpen N)
    (hNeq : ∀ z ∈ N, ∀ S, deningerExtend h z S = g S z)
    {w : Fin n → ℂ} (hwN : w ∈ N) (hwU : w ∈ deningerAmb U') (j : Fin n) :
    dzbarAt (g ∅) j w = 0 := by
  have hloc : setDbar (deningerFlip (deningerExtend h)) {j} w = setDbar g {j} w :=
    setDbar_congr_on_isOpen hNopen (fun T y hy => hNeq y hy T) hwN {j}
  have hzero : setDbar (deningerFlip (deningerExtend h)) {j} w = 0 := by
    have := hh.2 (deningerPt hwU) {j}
    rwa [deningerPt_val hwU] at this
  have hsum : setDbar g {j} w = dzbarAt (g ∅) j w := by
    show (∑ k ∈ ({j} : Finset (Fin n)), insertSign k (({j} : Finset (Fin n)).erase k)
      * dzbarAt (g (({j} : Finset (Fin n)).erase k)) k w) = _
    rw [Finset.sum_singleton, Finset.erase_singleton]
    show insertSign j (∅ : Finset (Fin n)) * _ = _
    rw [show insertSign j (∅ : Finset (Fin n)) = 1 from by
      show ((-1 : ℂ)) ^ ((∅ : Finset (Fin n)).filter (fun k => k < j)).card = 1
      rw [Finset.filter_empty, Finset.card_empty, pow_zero], one_mul]
  rw [← hsum, ← hloc, hzero]

set_option maxHeartbeats 1000000 in
/-- **Restriction to the divisor is locally surjective.**  Off the divisor the trace of a small
neighbourhood is empty, so the zero section works; on the divisor a local model of the given
function, read through the map forgetting the last coordinate, is a holomorphic extension. -/
theorem deningerDivisorRestrict_locallySurjective
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    TopCat.Presheaf.IsLocallySurjective (deningerDivisorRestrict hmap).1 := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).2 ?_
  intro U h x hx
  by_cases hlast : (x.1 : Fin (n + 1) → ℂ) (Fin.last n) = 0
  · -- on the divisor
    set U' : Opens (deningerSpace Ω') := (Opens.map (deningerDivisorInclusion hmap)).obj U with hU'
    have hxΩ' : deningerChopMap (x.1 : Fin (n + 1) → ℂ) ∈ Ω' :=
      hfull _ (by rw [deningerDivisorMap_chopMap hlast]; exact x.2)
    have hxpt : (deningerDivisorInclusion hmap)
        (⟨deningerChopMap (x.1 : Fin (n + 1) → ℂ), hxΩ'⟩ : deningerSpace Ω') = x :=
      Subtype.ext (deningerDivisorMap_chopMap hlast)
    have hxU' : (⟨deningerChopMap (x.1 : Fin (n + 1) → ℂ), hxΩ'⟩ : deningerSpace Ω') ∈ U' := by
      show (deningerDivisorInclusion hmap)
        (⟨deningerChopMap (x.1 : Fin (n + 1) → ℂ), hxΩ'⟩ : deningerSpace Ω') ∈ U
      rw [hxpt]
      exact hx
    obtain ⟨g, N, hg, hgd, hNopen, hxN, hNeq⟩ :=
      h.2.1.exists_model_open ⟨⟨deningerChopMap (x.1 : Fin (n + 1) → ℂ), hxΩ'⟩, hxU'⟩
    set W : Opens (Fin (n + 1) → ℂ) :=
      ⟨deningerChopMap ⁻¹' (N ∩ (deningerAmb U' : Set (Fin n → ℂ))),
        (hNopen.inter (deningerAmb U').2).preimage continuous_deningerChopMap⟩ with hW
    set V : Opens (deningerSpace Ω) := deningerRestrictOpen Ω W ⊓ U with hV
    have hxV : x ∈ V := ⟨⟨hxN, deningerAmb_mem_of_mem
      (⟨⟨deningerChopMap (x.1 : Fin (n + 1) → ℂ), hxΩ'⟩, hxU'⟩ : ↥U')⟩, hx⟩
    have hmemW : ∀ y : ↥V, deningerChopMap (y.1.1 : Fin (n + 1) → ℂ)
        ∈ N ∩ (deningerAmb U' : Set (Fin n → ℂ)) := fun y => y.2.1
    refine ⟨V, inf_le_right, ⟨⟨fun y => fun S => deningerChopPullback g S (y.1.1 : Fin (n+1) → ℂ),
      ?_⟩, ?_⟩, hxV⟩
    · refine ⟨⟨fun y S hS => deningerChopPullback_deg g S hS _, fun y => ?_⟩, fun y S => ?_⟩
      · refine ⟨deningerChopPullback g, deningerChopPullback_smooth hg,
          deningerChopPullback_deg g, ?_⟩
        filter_upwards [(deningerAmb V).2.mem_nhds (deningerAmb_mem_of_mem y)] with z hz
        intro S
        rw [deningerExtend_of_mem _ hz]
        rfl
      · have hmodel : ∀ᶠ z in nhds ((y.1.1 : Fin (n + 1) → ℂ)), ∀ S,
            deningerExtend (fun w : ↥V => fun S => deningerChopPullback g S
              (w.1.1 : Fin (n + 1) → ℂ)) z S = deningerChopPullback g S z := by
          filter_upwards [(deningerAmb V).2.mem_nhds (deningerAmb_mem_of_mem y)] with z hz
          intro S
          rw [deningerExtend_of_mem _ hz]
          rfl
        rw [deningerSetDbar_model hmodel S]
        exact setDbar_deningerChopPullback_eq_zero
          (fun j => deningerDivisorModel_dzbar_eq_zero h.2 hNopen hNeq
            (hmemW y).1 (hmemW y).2 j) S
    · refine Subtype.ext (funext fun y => funext fun S => ?_)
      have hyV : (deningerDivisorInclusion hmap) y.1 ∈ V := y.2
      have hy' : y.1 ∈ U' := hyV.2
      have hchop : deningerChopMap
          (deningerDivisorMap (y.1.1 : Fin n → ℂ)) = (y.1.1 : Fin n → ℂ) :=
        deningerChopMap_divisorMap _
      have hyN : (y.1.1 : Fin n → ℂ) ∈ N := by
        have hmem : deningerChopMap (deningerDivisorMap (y.1.1 : Fin n → ℂ))
            ∈ N ∩ (deningerAmb U' : Set (Fin n → ℂ)) := hyV.1
        rw [hchop] at hmem
        exact hmem.1
      by_cases hS : S = ∅
      · subst hS
        show deningerRestrictVal
            (fun T => deningerChopPullback g T (deningerDivisorMap (y.1.1 : Fin n → ℂ))) ∅
          = h.1 ⟨y.1, hy'⟩ ∅
        rw [deningerRestrictVal_empty, deningerChopPullback_empty, hchop]
        exact (hNeq _ hyN ∅).symm.trans
          (congrFun (deningerExtend_apply h.1 (⟨y.1, hy'⟩ : ↥U')) ∅)
      · show deningerRestrictVal
            (fun T => deningerChopPullback g T (deningerDivisorMap (y.1.1 : Fin n → ℂ))) S
          = h.1 ⟨y.1, hy'⟩ S
        rw [deningerRestrictVal_ne _ hS]
        exact (h.2.1.1 ⟨y.1, hy'⟩ S (fun hcard => hS (Finset.card_eq_zero.1 hcard))).symm
  · -- off the divisor
    set W : Opens (Fin (n + 1) → ℂ) :=
      ⟨{z : Fin (n + 1) → ℂ | z (Fin.last n) ≠ 0}, deningerOffDivisor_isOpen⟩ with hW
    set V : Opens (deningerSpace Ω) := deningerRestrictOpen Ω W ⊓ U with hV
    have hxV : x ∈ V := ⟨hlast, hx⟩
    refine ⟨V, inf_le_right, ⟨0, ?_⟩, hxV⟩
    refine Subtype.ext (funext fun y => ?_)
    exact absurd (deningerDivisorMap_last (y.1.1 : Fin n → ℂ)) y.2.1

/-- **Restriction to the divisor is an epimorphism of sheaves.** -/
theorem deningerDivisorRestrict_epi
    (hfull : ∀ w : Fin n → ℂ, deningerDivisorMap w ∈ Ω → w ∈ Ω') :
    Epi (deningerDivisorRestrict hmap) :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
    (deningerDivisorRestrict_locallySurjective hmap hfull)

end Surjectivity

end RHTower
