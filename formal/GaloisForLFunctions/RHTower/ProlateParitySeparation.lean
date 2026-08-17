import GaloisForLFunctions.RHTower.ProlateFullLadderConsequences

/-!
# The parity separation of the constrained ground eigenvalues

The two sector ground eigenvalues are normalized by their own dominant leakages, and the quotient of
those normalizations is the Hermite constant `13/11`.  The step-one ladder supplies the missing
factor: the two normalizing leakages are adjacent corpus indices, so their quotient vanishes.  Hence

```text
mu_+(lam) / mu_-(lam)  →  (13/11) · 0  =  0 ,
```

so the positive-sector ground is eventually strictly below the negative-sector one and the gap
between them is asymptotically the whole of the negative-sector ground.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The negative-sector ground eigenvalue is eventually positive: it lies strictly above the first
leakage of its own ladder, which is nonnegative. -/
theorem eventually_negativeSector_root_pos :
    let Dn : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓn : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    ∀ᶠ lam : ℝ in atTop, 0 < infiniteSecularRoot (Dn lam) (ℓn lam) := by
  intro Dn ℓn
  have ha0 : constrainedProlateNegativeCoordinate 0 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 0).ne'
  have ha1 : constrainedProlateNegativeCoordinate 1 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 1).ne'
  have h0 : ∀ᶠ lam : ℝ in atTop, ℓn lam 0 ≠ 0 :=
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 0).eventually_ne ha0
  have h1 : ∀ᶠ lam : ℝ in atTop, ℓn lam 1 ≠ 0 :=
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1).eventually_ne ha1
  filter_upwards [ladderEnvelope_evenProlateSignedLeakage_negative.first_struct,
    negativeSector_sum, h0, h1] with lam hst hsm hl0 hl1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec (d := Dn lam) (ℓ := ℓn lam)
    h01 h12 hd2 hsm hl0 hl1
  have hnn : 0 ≤ Dn lam 0 := evenProlateSignedLeakage_nonneg lam 1
  exact lt_of_le_of_lt hnn hrmem.1

/-- **Equation `(9)`, the vanishing of the parity quotient.**  The positive-sector constrained
ground eigenvalue is negligible against the negative-sector one. -/
theorem tendsto_constrainedProlateParity_ratio_zero :
    let Dp : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓp : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    let Dn : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓn : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    Tendsto (fun lam : ℝ =>
        infiniteSecularRoot (Dp lam) (ℓp lam) / infiniteSecularRoot (Dn lam) (ℓn lam))
      atTop (𝓝 0) := by
  intro Dp ℓp Dn ℓn
  have hnorm := constrainedProlateParity_normalized_ratio_tendsto
  have hleak := tendsto_signedLeakage_succ_ratio 2
  have hprod := hnorm.mul hleak
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_evenProlateSignedLeakage_pos 2 (by omega),
    eventually_evenProlateSignedLeakage_pos 3 (by omega),
    eventually_negativeSector_root_pos] with lam h2 h3 hroot
  have h2' : Dp lam 1 ≠ 0 := by
    show evenProlateSignedLeakage lam 2 ≠ 0
    exact h2.ne'
  have h3' : Dn lam 1 ≠ 0 := by
    show evenProlateSignedLeakage lam 3 ≠ 0
    exact h3.ne'
  have hr : infiniteSecularRoot (Dn lam) (ℓn lam) ≠ 0 := hroot.ne'
  show infiniteSecularRoot (Dp lam) (ℓp lam) / Dp lam 1
      / (infiniteSecularRoot (Dn lam) (ℓn lam) / Dn lam 1)
      * (evenProlateSignedLeakage lam 2 / evenProlateSignedLeakage lam 3)
    = infiniteSecularRoot (Dp lam) (ℓp lam) / infiniteSecularRoot (Dn lam) (ℓn lam)
  have hDp : Dp lam 1 = evenProlateSignedLeakage lam 2 := rfl
  have hDn : Dn lam 1 = evenProlateSignedLeakage lam 3 := rfl
  rw [hDp, hDn] at *
  field_simp

/-- **Equation `(9)`.**  Eventually the positive-sector ground is strictly below the negative-sector
one, and the gap between them is asymptotically the whole negative-sector ground. -/
theorem constrainedProlateParity_separation :
    let Dp : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓp : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    let Dn : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓn : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    (∀ᶠ lam : ℝ in atTop,
        infiniteSecularRoot (Dp lam) (ℓp lam) < infiniteSecularRoot (Dn lam) (ℓn lam)) ∧
      Tendsto (fun lam : ℝ =>
          (infiniteSecularRoot (Dn lam) (ℓn lam) - infiniteSecularRoot (Dp lam) (ℓp lam))
            / infiniteSecularRoot (Dn lam) (ℓn lam))
        atTop (𝓝 1) := by
  intro Dp ℓp Dn ℓn
  have hzero := tendsto_constrainedProlateParity_ratio_zero
  constructor
  · have hlt : ∀ᶠ lam : ℝ in atTop,
        infiniteSecularRoot (Dp lam) (ℓp lam) / infiniteSecularRoot (Dn lam) (ℓn lam) < 1 :=
      hzero.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hlt, eventually_negativeSector_root_pos] with lam h hroot
    rw [div_lt_one hroot] at h
    exact h
  · have hone : Tendsto (fun lam : ℝ =>
        1 - infiniteSecularRoot (Dp lam) (ℓp lam) / infiniteSecularRoot (Dn lam) (ℓn lam))
        atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hzero
    rw [sub_zero] at hone
    refine hone.congr' ?_
    filter_upwards [eventually_negativeSector_root_pos] with lam hroot
    have hne : infiniteSecularRoot (Dn lam) (ℓn lam) ≠ 0 := ne_of_gt hroot
    field_simp

end RHTower

end
