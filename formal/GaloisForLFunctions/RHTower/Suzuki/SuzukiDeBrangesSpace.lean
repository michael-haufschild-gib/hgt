import GaloisForLFunctions.RHTower.Suzuki.SuzukiModelSpaceConjugation
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPropOneTwo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHalfInnerHalfPlane

noncomputable section

/-!
# The de Branges space `H(E)` and its identification with the model space

Suzuki defines `H(E)` as the entire functions `F` with `F/E` and `F^♯/E` both in `H²`, normed by
`‖F‖_{H(E)} = ‖F/E‖_{L²(ℝ)}`.  On the real axis `F^♯ = conj F` and `E^♯ = conj E`, so

```text
F^♯/E = (E^♯/E) · conj(F/E) = Θ · conj(F/E),
```

which turns the second membership condition into `Θ · conj G ∈ H²` for `G = F/E`.  That is exactly
membership of `G` in `(Θ H²)^⊥`, so

```text
F ∈ H(E)  ⟺  F/E ∈ H² ∩ (Θ H²)^⊥ = K(Θ).
```

This is the boundary form of the second half of Lemma 5.1, and it exhibits `F ↦ F/E` as the map
identifying `H(E)` with the model space.  No analytic continuation is needed: the whole argument is
the unimodularity of `Θ` together with `conj H² = (H²)^⊥`.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

theorem mem_thetaHardyL2_orthogonal_iff (G : L2R) :
    G ∈ thetaHardyL2ᗮ ↔ thetaMul (star G) ∈ hardyL2 := by
  have hmap : thetaHardyL2ᗮ
      = Submodule.map (thetaUnitary.toLinearEquiv.toLinearMap) hardyL2ᗮ := by
    rw [thetaHardyL2, Submodule.map_orthogonal_equiv hardyL2 thetaUnitary]
    rfl
  rw [hmap, ← map_star_hardyL2]
  constructor
  · rintro ⟨z, ⟨h, hh, rfl⟩, rfl⟩
    show thetaMul (star (thetaMul (star h))) ∈ hardyL2
    rw [thetaMul_star_thetaMul_star]
    exact hh
  · intro hG
    exact ⟨star (thetaMul (star G)), ⟨thetaMul (star G), hG, rfl⟩,
      thetaMul_star_thetaMul_star G⟩

/-- **The model space in conjugation form.**  `G ∈ K(Θ)` exactly when `G` and `Θ · conj G` both
lie in the Hardy space. -/
theorem mem_suzukiModelSpace_iff_conj (G : L2R) :
    G ∈ suzukiModelSpace ↔ G ∈ hardyL2 ∧ thetaMul (star G) ∈ hardyL2 := by
  rw [suzukiModelSpace, Submodule.mem_inf, mem_thetaHardyL2_orthogonal_iff]

/-! ## The de Branges space -/

theorem ae_xiHedenmalmDeBrangesE_ofReal_ne_zero :
    ∀ᵐ x : ℝ, xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) ≠ 0 := by
  filter_upwards [ae_ne_zero_and_XiC_ne_zero] with x hx hE
  exact hx.2 (XiC_eq_zero_of_xiHedenmalmDeBrangesE_ofReal_eq_zero hE)

/-- **The de Branges space of the Hedenmalm pair.**  An entire `F` belongs to `H(E)` when both
`F/E` and `F^♯/E` have square-integrable boundary values lying in the Hardy space. -/
structure MemDeBranges (F : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ F
  memLp : MemLp (fun x : ℝ =>
    F ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
  memLpSharp : MemLp (fun x : ℝ =>
    (starRingEnd ℂ) (F ((x : ℝ) : ℂ)) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      2 (volume : Measure ℝ)
  hardy : memLp.toLp _ ∈ hardyL2
  hardySharp : memLpSharp.toLp _ ∈ hardyL2

theorem sharpQuotient_eq_thetaMul_star {F : ℂ → ℂ}
    (h1 : MemLp (fun x : ℝ =>
      F ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ))
    (h2 : MemLp (fun x : ℝ =>
      (starRingEnd ℂ) (F ((x : ℝ) : ℂ)) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
        2 (volume : Measure ℝ)) :
    h2.toLp _ = thetaMul (star (h1.toLp _)) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [h2.coeFn_toLp, thetaMul_coeFn (star (h1.toLp _)),
    MeasureTheory.Lp.coeFn_star (h1.toLp _), h1.coeFn_toLp,
    ae_xiHedenmalmDeBrangesE_ofReal_ne_zero] with x k1 k2 k3 k4 hE
  rw [k1, k2, k3, Pi.star_apply, k4]
  rw [suzukiThetaSymbol, if_neg hE, xiHedenmalmDeBrangesESharp_ofReal_eq_conj]
  rw [show star (F ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      = (starRingEnd ℂ) (F ((x : ℝ) : ℂ))
        / (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) by
    rw [← map_div₀ (starRingEnd ℂ)]
    rfl]
  have hEc : (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) ≠ 0 := by simpa using hE
  field_simp

/-- **The de Branges space is the model space, through division by `E`.**  This is the boundary
form of the second half of Suzuki's Lemma 5.1. -/
theorem memDeBranges_iff_mem_suzukiModelSpace {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (h1 : MemLp (fun x : ℝ =>
      F ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ))
    (h2 : MemLp (fun x : ℝ =>
      (starRingEnd ℂ) (F ((x : ℝ) : ℂ)) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
        2 (volume : Measure ℝ)) :
    MemDeBranges F ↔ h1.toLp _ ∈ suzukiModelSpace := by
  rw [mem_suzukiModelSpace_iff_conj, ← sharpQuotient_eq_thetaMul_star h1 h2]
  constructor
  · intro hmem
    exact ⟨hmem.hardy, hmem.hardySharp⟩
  · rintro ⟨ha, hb⟩
    exact ⟨hF, h1, h2, ha, hb⟩

end RHTower
