import GaloisForLFunctions.HTGeometry.FriedrichsClosedSum
import GaloisForLFunctions.HTGeometry.OrthogonalCodimensionOne
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Removing one direction from each of two transverse summands drops the sum by exactly two

Let `A`, `B` be closed transverse subspaces of a Hilbert space whose sum is closed, and let
`u ∈ A`, `v ∈ B` be nonzero.  Put `A' = A ⊖ 𝕜u` and `B' = B ⊖ 𝕜v`.  Then `A' + B'` is again
closed and the orthogonal complement of `A' + B'` inside `A + B` has dimension exactly `2`.

This is the mechanism of Burnol's second proof of Prop. 4.5 (arXiv:math/0203120): the extended
Sonine space `L_a` is the perpendicular of `(L²(0,a) ∩ 1⊥) + F₊(L²(0,a) ∩ 1⊥)` while the Sonine
space `K_a` is the perpendicular of `L²(0,a) + F₊(L²(0,a))`, so `dim(L_a/K_a) = 2`.

## Main results

* `friedrichsCosine_mono_of_inf_eq_bot`
* `isClosed_sup_of_le_of_inf_eq_bot`
* `finrank_inf_orthogonal_sub_sup_eq_two`
-/

namespace GaloisForLFunctions.HTGeometry

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- For transverse pairs the Friedrichs cosine is monotone in both arguments. -/
theorem friedrichsCosine_mono_of_inf_eq_bot {A B U V : Submodule 𝕜 H}
    (hAB : A ⊓ B = ⊥) (_hUV : U ⊓ V = ⊥) (hUA : U ≤ A) (hVB : V ≤ B) :
    friedrichsCosine U V ≤ friedrichsCosine A B := by
  refine Real.sSup_le ?_ (friedrichsCosine_nonneg A B)
  rintro r ⟨x, hx, y, hy, hxn, hyn, rfl⟩
  refine le_csSup (friedrichsCosineSet_bddAbove A B) ?_
  refine ⟨x, ⟨hUA hx.1, ?_⟩, y, ⟨hVB hy.1, ?_⟩, hxn, hyn, rfl⟩
  · rw [hAB, Submodule.bot_orthogonal_eq_top]
    trivial
  · rw [hAB, Submodule.bot_orthogonal_eq_top]
    trivial

/-- Shrinking both summands of a closed transverse sum keeps the sum closed. -/
theorem isClosed_sup_of_le_of_inf_eq_bot {A B U V : Submodule 𝕜 H}
    (hAB : A ⊓ B = ⊥) (hUV : U ⊓ V = ⊥) (hUA : U ≤ A) (hVB : V ≤ B)
    (hA : IsClosed (A : Set H)) (hB : IsClosed (B : Set H))
    (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (hsup : IsClosed ((A ⊔ B : Submodule 𝕜 H) : Set H)) :
    IsClosed ((U ⊔ V : Submodule 𝕜 H) : Set H) := by
  refine (friedrichsCosine_lt_one_iff_isClosed_sup hU hV).1 ?_
  refine lt_of_le_of_lt (friedrichsCosine_mono_of_inf_eq_bot hAB hUV hUA hVB) ?_
  exact (friedrichsCosine_lt_one_iff_isClosed_sup hA hB).2 hsup

/-- **The codimension-two law.**  Removing one direction from each transverse summand leaves an
exactly two-dimensional orthogonal complement inside the sum. -/
theorem finrank_inf_orthogonal_sub_sup_eq_two {A B : Submodule 𝕜 H}
    (hAB : A ⊓ B = ⊥)
    (hA : IsClosed (A : Set H)) (hB : IsClosed (B : Set H))
    (hsup : IsClosed ((A ⊔ B : Submodule 𝕜 H) : Set H))
    {u v : H} (hu : u ∈ A) (hu0 : u ≠ 0) (hv : v ∈ B) (hv0 : v ≠ 0) :
    Module.finrank 𝕜
        (((A ⊔ B) ⊓ ((A ⊓ (𝕜 ∙ u)ᗮ) ⊔ (B ⊓ (𝕜 ∙ v)ᗮ))ᗮ : Submodule 𝕜 H)) = 2 := by
  classical
  set A' : Submodule 𝕜 H := A ⊓ (𝕜 ∙ u)ᗮ with hA'
  set B' : Submodule 𝕜 H := B ⊓ (𝕜 ∙ v)ᗮ with hB'
  set S : Submodule 𝕜 H := A' ⊔ B' with hS
  set T : Submodule 𝕜 H := A ⊔ B with hT
  have hA'A : A' ≤ A := inf_le_left
  have hB'B : B' ≤ B := inf_le_left
  have hA'B' : A' ⊓ B' = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine le_trans (inf_le_inf hA'A hB'B) ?_
    exact le_of_eq hAB
  have hA'closed : IsClosed ((A' : Submodule 𝕜 H) : Set H) := by
    rw [hA']
    exact hA.inter (Submodule.isClosed_orthogonal _)
  have hB'closed : IsClosed ((B' : Submodule 𝕜 H) : Set H) := by
    rw [hB']
    exact hB.inter (Submodule.isClosed_orthogonal _)
  have hSclosed : IsClosed ((S : Submodule 𝕜 H) : Set H) :=
    isClosed_sup_of_le_of_inf_eq_bot hAB hA'B' hA'A hB'B hA hB hA'closed hB'closed hsup
  haveI : CompleteSpace S := hSclosed.completeSpace_coe
  haveI : S.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace S
  -- the two representatives
  set w₁ : H := u - S.starProjection u with hw₁
  set w₂ : H := v - S.starProjection v with hw₂
  have hST : S ≤ T := by
    refine sup_le (le_trans hA'A le_sup_left) (le_trans hB'B le_sup_right)
  have hdecompT : T = S ⊔ (𝕜 ∙ u) ⊔ (𝕜 ∙ v) := by
    have hAu : (𝕜 ∙ u) ⊔ A' = A := sup_span_singleton_inf_orthogonal A hu
    have hBv : (𝕜 ∙ v) ⊔ B' = B := sup_span_singleton_inf_orthogonal B hv
    rw [hT, ← hAu, ← hBv, hS]
    ac_rfl
  have hw₁mem : w₁ ∈ T ⊓ Sᗮ := by
    refine ⟨?_, S.sub_starProjection_mem_orthogonal u⟩
    exact Submodule.sub_mem _ ((le_sup_left : A ≤ A ⊔ B) hu) (hST (S.starProjection_apply_mem u))
  have hw₂mem : w₂ ∈ T ⊓ Sᗮ := by
    refine ⟨?_, S.sub_starProjection_mem_orthogonal v⟩
    exact Submodule.sub_mem _ ((le_sup_right : B ≤ A ⊔ B) hv) (hST (S.starProjection_apply_mem v))
  -- the complement is spanned by the two representatives
  have hspan : (T ⊓ Sᗮ : Submodule 𝕜 H) = Submodule.span 𝕜 {w₁, w₂} := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨hxT, hxS⟩
      rw [hdecompT] at hxT
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hxT
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨lu, rfl⟩ := Submodule.mem_span_singleton.1 hq
      obtain ⟨lv, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have hproj : S.starProjection (p + lu • u + lv • v) = 0 := by
        have := Submodule.starProjection_apply_eq_zero_iff (K := S) |>.2 hxS
        exact this
      have hp0 : S.starProjection p = p := Submodule.starProjection_eq_self_iff.2 hp
      have hkey : p + lu • u + lv • v = lu • w₁ + lv • w₂ := by
        have hexp : S.starProjection (p + lu • u + lv • v)
            = p + lu • S.starProjection u + lv • S.starProjection v := by
          rw [map_add, map_add, map_smul, map_smul, hp0]
        rw [hexp] at hproj
        rw [hw₁, hw₂, smul_sub, smul_sub]
        have : p = -(lu • S.starProjection u) - lv • S.starProjection v := by
          linear_combination (norm := module) hproj
        rw [this]
        module
      rw [hkey]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro x hx
      rcases hx with rfl | rfl
      · exact hw₁mem
      · exact hw₂mem
  -- independence
  have hindep : LinearIndependent 𝕜 ![w₁, w₂] := by
    rw [LinearIndependent.pair_iff]
    intro lu lv hzero
    have hmemS : lu • u + lv • v ∈ S := by
      have hrw : lu • w₁ + lv • w₂ = (lu • u + lv • v)
          - S.starProjection (lu • u + lv • v) := by
        rw [hw₁, hw₂, map_add, map_smul, map_smul, smul_sub, smul_sub]
        module
      rw [hrw, sub_eq_zero] at hzero
      rw [hzero]
      exact S.starProjection_apply_mem _
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmemS
    have hsplit : lu • u - p = q - lv • v := by
      rw [sub_eq_sub_iff_add_eq_add]
      rw [← hpq]
      module
    have hinA : lu • u - p ∈ A := Submodule.sub_mem _ (Submodule.smul_mem _ _ hu) (hA'A hp)
    have hinB : lu • u - p ∈ B := by
      rw [hsplit]
      exact Submodule.sub_mem _ (hB'B hq) (Submodule.smul_mem _ _ hv)
    have hzero2 : lu • u - p = 0 := by
      have : lu • u - p ∈ A ⊓ B := ⟨hinA, hinB⟩
      rw [hAB, Submodule.mem_bot] at this
      exact this
    have hup : lu • u = p := sub_eq_zero.1 hzero2
    have hlu : lu = 0 := by
      have hperp : ⟪u, p⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hp.2
      rw [← hup, inner_smul_right, inner_self_eq_norm_sq_to_K] at hperp
      have hun : ((‖u‖ : 𝕜)) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hu0)
      exact (mul_eq_zero.1 hperp).resolve_right hun
    have hvq : lv • v = q := by
      have : q - lv • v = 0 := by rw [← hsplit, hzero2]
      exact (sub_eq_zero.1 this).symm
    have hlv : lv = 0 := by
      have hperp : ⟪v, q⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hq.2
      rw [← hvq, inner_smul_right, inner_self_eq_norm_sq_to_K] at hperp
      have hvn : ((‖v‖ : 𝕜)) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hv0)
      exact (mul_eq_zero.1 hperp).resolve_right hvn
    exact ⟨hlu, hlv⟩
  have hrange : Set.range ![w₁, w₂] = {w₁, w₂} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hspan, ← hrange, finrank_span_eq_card hindep]
  simp

end GaloisForLFunctions.HTGeometry
