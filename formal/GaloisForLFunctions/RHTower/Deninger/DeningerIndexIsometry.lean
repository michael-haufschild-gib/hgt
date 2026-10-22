import GaloisForLFunctions.RHTower.Deninger.DeningerAbsGenerator

/-!
# The isometry induced by an injective index map

Transporting coefficients along an injective map of indices, extending by zero off the image, is an
isometry of the square-summable coefficient space: the coefficient sums agree because the map is
injective and the extension vanishes off its range.

The power correspondence on Kummer characters is of this form — it sends the character of `a` to the
character of `q a` — so it is an isometric embedding, unitary exactly when multiplication by `q` is
bijective on the index.

* `deningerIndexPush` : the transported coefficient family.
* `deningerIndexIsometry` : the isometry it defines.
* `deningerIndexIsometry_diagonal` : it intertwines the diagonal operators.
-/

namespace RHTower

open scoped ENNReal
open scoped Classical

noncomputable section

universe u

variable {ι : Type u}

/-- The coefficients transported along an injective index map, extended by zero off the image. -/
def deningerIndexPush (m : ι → ι) (x : lp (fun _ : ι => ℂ) 2) (j : ι) : ℂ :=
  if h : ∃ i, m i = j then (x : ι → ℂ) h.choose else 0

theorem deningerIndexPush_apply_map {m : ι → ι} (hm : Function.Injective m)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) : deningerIndexPush m x (m i) = (x : ι → ℂ) i := by
  have hex : ∃ k, m k = m i := ⟨i, rfl⟩
  have hchoose : hex.choose = i := hm hex.choose_spec
  rw [deningerIndexPush, dif_pos hex, hchoose]

theorem deningerIndexPush_apply_notMem {m : ι → ι} (x : lp (fun _ : ι => ℂ) 2) {j : ι}
    (hj : j ∉ Set.range m) : deningerIndexPush m x j = 0 := by
  rw [deningerIndexPush, dif_neg]
  intro h
  exact hj h

theorem deningerIndexPush_vanish {m : ι → ι} (x : lp (fun _ : ι => ℂ) 2) :
    ∀ j ∉ Set.range m, ‖deningerIndexPush m x j‖ ^ (2 : ℝ≥0∞).toReal = 0 := by
  intro j hj
  rw [deningerIndexPush_apply_notMem x hj, norm_zero]
  simp

theorem deningerIndexPush_support {m : ι → ι} (x : lp (fun _ : ι => ℂ) 2) :
    Function.support (fun j => ‖deningerIndexPush m x j‖ ^ (2 : ℝ≥0∞).toReal) ⊆ Set.range m := by
  intro j hj
  by_contra hcon
  exact hj (deningerIndexPush_vanish x j hcon)

theorem deningerIndexPush_memℓp {m : ι → ι} (hm : Function.Injective m)
    (x : lp (fun _ : ι => ℂ) 2) : Memℓp (deningerIndexPush m x) 2 := by
  have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen ?_
  refine (hm.summable_iff (deningerIndexPush_vanish x)).mp ?_
  refine (x.2.summable htwo).congr fun i => ?_
  rw [Function.comp_apply, deningerIndexPush_apply_map hm x i]

/-- **The isometry induced by an injective index map.** -/
def deningerIndexIsometry {m : ι → ι} (hm : Function.Injective m) :
    lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun x := ⟨deningerIndexPush m x, deningerIndexPush_memℓp hm x⟩
  map_add' x y := by
    refine lp.ext ?_
    funext j
    show deningerIndexPush m (x + y) j
      = deningerIndexPush m x j + deningerIndexPush m y j
    by_cases hj : ∃ i, m i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [deningerIndexPush_apply_map hm, deningerIndexPush_apply_map hm,
        deningerIndexPush_apply_map hm]
      rfl
    · rw [deningerIndexPush_apply_notMem _ hj, deningerIndexPush_apply_notMem _ hj,
        deningerIndexPush_apply_notMem _ hj, add_zero]
  map_smul' c x := by
    refine lp.ext ?_
    funext j
    show deningerIndexPush m (c • x) j = c * deningerIndexPush m x j
    by_cases hj : ∃ i, m i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [deningerIndexPush_apply_map hm, deningerIndexPush_apply_map hm]
      rfl
    · rw [deningerIndexPush_apply_notMem _ hj, deningerIndexPush_apply_notMem _ hj, mul_zero]
  norm_map' x := by
    have htwo : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
    congr 1
    refine ((hm.tsum_eq (deningerIndexPush_support x)).symm).trans ?_
    refine tsum_congr fun i => ?_
    show ‖deningerIndexPush m x (m i)‖ ^ (2 : ℝ≥0∞).toReal
      = ‖(x : ι → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
    rw [deningerIndexPush_apply_map hm]

@[simp] theorem deningerIndexIsometry_apply_map {m : ι → ι} (hm : Function.Injective m)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    ((deningerIndexIsometry hm x : lp (fun _ : ι => ℂ) 2) : ι → ℂ) (m i) = (x : ι → ℂ) i :=
  deningerIndexPush_apply_map hm x i

/-- **The index isometry intertwines the diagonal multipliers.**  Pulling back and then multiplying
by a symbol is multiplying by the pulled-back symbol and then pulling back. -/
theorem deningerIndexIsometry_diagonal {m : ι → ι} (hm : Function.Injective m) {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ ≤ 1) (hgm : ∀ i, ‖g (m i)‖ ≤ 1) (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    ((deningerMultiplier hg (deningerIndexIsometry hm x) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) (m i)
      = ((deningerIndexIsometry hm (deningerMultiplier hgm x) : lp (fun _ : ι => ℂ) 2) : ι → ℂ)
          (m i) := by
  rw [deningerMultiplier_apply, deningerIndexIsometry_apply_map hm,
    deningerIndexIsometry_apply_map hm, deningerMultiplier_apply]

end

end RHTower
