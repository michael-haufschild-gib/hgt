/-
# Böttcher tower — the Green's function determines the parameter (E2 closure)

`greenFunctionDyn c₁ = greenFunctionDyn c₂ ⟹ c₁ = c₂`. Combined with E1
(`greenFunctionDyn_eq_of_filledJulia_eq`), this gives **`K_{c₁} = K_{c₂} ⟹ c₁ = c₂`** — the Julia-set
rigidity at the heart of brick E.

Proof chain: equal Green's functions ⟹ `Re(bottcherLog c₁) = Re(bottcherLog c₂)` on a germ ball ⟹
(`eq_const_of_re_eq_const`) `bottcherLog c₁ − bottcherLog c₂` is an imaginary constant `a`, so
`φ_{c₁} = exp(a)·φ_{c₂}` there ⟹ (identity theorem) on the whole deep exterior ⟹ (the normalization
`φ_c(z) − z → 0` forces `z(exp a − 1) → 0`, impossible unless) `exp a = 1` ⟹ `φ_{c₁} = φ_{c₂}` ⟹
(`c_eq_of_bottcherCoord_eqOn`) `c₁ = c₂`.

New file (hRigid connected lane).
-/
import GaloisForLFunctions.Bottcher.BottcherAsymptotic
import GaloisForLFunctions.Bottcher.GreenContinuity
import GaloisForLFunctions.Bottcher.BottcherBasin
import GaloisForLFunctions.Bottcher.GreenUnique
import GaloisForLFunctions.Bottcher.BasinConnected
import GaloisForLFunctions.Bottcher.SquareFree
import Mathlib.Analysis.Complex.OpenMapping

open Filter Topology Metric Complex Set Bornology

namespace Bottcher

/-- **The Green's function determines `c`** (E2). -/
theorem c_eq_of_greenFunctionDyn_eq {c₁ c₂ : ℂ}
    (hG : greenFunctionDyn c₁ = greenFunctionDyn c₂) : c₁ = c₂ := by
  set R : ℝ := max 2 (max ‖c₁‖ ‖c₂‖) with hRdef
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) ≤ R := le_trans (by norm_num) hR2
  set W : Set ℂ := escapeOpen c₁ ∩ escapeOpen c₂ with hWdef
  have hWeq : W = {z : ℂ | R < ‖z‖} := by
    rw [hWdef]; ext z
    simp only [escapeOpen, Set.mem_inter_iff, Set.mem_setOf_eq, hRdef, max_lt_iff]
    tauto
  have hWconn : IsConnected W := by rw [hWeq]; exact isConnected_setOf_lt_norm hR0
  have hWopen : IsOpen W := (isOpen_escapeOpen c₁).inter (isOpen_escapeOpen c₂)
  -- greenLimit c₁ = greenLimit c₂ on W
  have hglEq : ∀ z ∈ W, greenLimit c₁ z = greenLimit c₂ z := by
    intro z hzW
    have hzK1 : z ∈ (filledJulia c₁)ᶜ :=
      (basin_eq_compl_filledJulia c₁) ▸ escapeOpen_subset_basin c₁ hzW.1
    have hzK2 : z ∈ (filledJulia c₂)ᶜ :=
      (basin_eq_compl_filledJulia c₂) ▸ escapeOpen_subset_basin c₂ hzW.2
    have e1 : greenFunctionDyn c₁ z = greenLimit c₁ z := by rw [greenFunctionDyn, if_neg hzK1]
    have e2 : greenFunctionDyn c₂ z = greenLimit c₂ z := by rw [greenFunctionDyn, if_neg hzK2]
    have h := congrFun hG z
    rw [e1, e2] at h; exact h
  -- germ ball deep on the positive real axis (inside escape ∩ slit for both)
  set z₀ : ℂ := ((R + 2 : ℝ) : ℂ) with hz0def
  have hz0norm : ‖z₀‖ = R + 2 := by
    rw [hz0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hBsub : ball z₀ 1 ⊆ escapeOpen c₁ ∩ escapeOpen c₂ ∩ slitPlane := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hwn : R < ‖w‖ := by
      have h := norm_sub_norm_le z₀ w
      rw [hz0norm, norm_sub_rev] at h
      linarith
    have hwre : 0 < w.re := by
      have hz0re : z₀.re = R + 2 := by rw [hz0def]; simp
      have hbound : |w.re - z₀.re| ≤ ‖w - z₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      rw [hz0re] at hbound
      have hlt := abs_lt.mp (lt_of_le_of_lt hbound hw)
      linarith [hlt.1]
    refine ⟨⟨?_, ?_⟩, Or.inl hwre⟩
    · rw [escapeOpen, Set.mem_setOf_eq]
      exact lt_of_le_of_lt (le_trans (max_le_max (le_refl 2) (le_max_left _ _)) hRdef.ge) hwn
    · rw [escapeOpen, Set.mem_setOf_eq]
      exact lt_of_le_of_lt (le_trans (max_le_max (le_refl 2) (le_max_right _ _)) hRdef.ge) hwn
  -- bottcherLog analytic on the ball (⊆ escape ∩ slit)
  have hBlog1 : AnalyticOnNhd ℂ (bottcherLog c₁) (ball z₀ 1) :=
    ((differentiableOn_bottcherLog c₁).analyticOnNhd
      ((isOpen_escapeOpen c₁).inter isOpen_slitPlane)).mono
      (fun w hw => ⟨(hBsub hw).1.1, (hBsub hw).2⟩)
  have hBlog2 : AnalyticOnNhd ℂ (bottcherLog c₂) (ball z₀ 1) :=
    ((differentiableOn_bottcherLog c₂).analyticOnNhd
      ((isOpen_escapeOpen c₂).inter isOpen_slitPlane)).mono
      (fun w hw => ⟨(hBsub hw).1.2, (hBsub hw).2⟩)
  have hre0 : ∀ w ∈ ball z₀ 1, (bottcherLog c₁ w - bottcherLog c₂ w).re = (0 : ℝ) := by
    intro w hw
    have hw1 : w ∈ escapeOpen c₁ := (hBsub hw).1.1
    have hw2 : w ∈ escapeOpen c₂ := (hBsub hw).1.2
    obtain ⟨hc1, hz1⟩ := mem_escapeOpen_regime hw1
    obtain ⟨hc2, hz2⟩ := mem_escapeOpen_regime hw2
    rw [Complex.sub_re, bottcherLog_re hc1 hz1, bottcherLog_re hc2 hz2,
      hglEq w (by rw [hWdef]; exact ⟨hw1, hw2⟩), sub_self]
  obtain ⟨a, ha⟩ := AnalyticOnNhd.eq_const_of_re_eq_const (hBlog1.sub hBlog2) hre0 isOpen_ball
    (isConnected_ball (by norm_num))
  -- φ_{c₁} = exp(a) · φ_{c₂} on the ball
  have hBcoord : ∀ w ∈ ball z₀ 1, bottcherCoord c₁ w = Complex.exp a * bottcherCoord c₂ w := by
    intro w hw
    have hd := ha w hw
    simp only [Pi.sub_apply] at hd
    rw [bottcherCoord, bottcherCoord, sub_eq_iff_eq_add.mp hd, Complex.exp_add]
  -- extend to W by the identity theorem
  have hz0B : z₀ ∈ ball z₀ 1 := mem_ball_self (by norm_num)
  have hz0W : z₀ ∈ W := by rw [hWdef]; exact ⟨(hBsub hz0B).1.1, (hBsub hz0B).1.2⟩
  have hWcoord1 : AnalyticOnNhd ℂ (bottcherCoord c₁) W :=
    (analyticOnNhd_bottcherCoord_full c₁).mono (hWdef ▸ inter_subset_left)
  have hWcoord2 : AnalyticOnNhd ℂ (fun w => Complex.exp a * bottcherCoord c₂ w) W :=
    analyticOnNhd_const.mul ((analyticOnNhd_bottcherCoord_full c₂).mono (hWdef ▸ inter_subset_right))
  have hevB : bottcherCoord c₁ =ᶠ[𝓝 z₀] (fun w => Complex.exp a * bottcherCoord c₂ w) := by
    filter_upwards [isOpen_ball.mem_nhds hz0B] with w hw using hBcoord w hw
  have hWfull : EqOn (bottcherCoord c₁) (fun w => Complex.exp a * bottcherCoord c₂ w) W :=
    hWcoord1.eqOn_of_preconnected_of_eventuallyEq hWcoord2 hWconn.isPreconnected hz0W hevB
  -- exp a = 1 (normalization)
  have hWcob : {z : ℂ | R < ‖z‖} ∈ cobounded ℂ :=
    tendsto_norm_cobounded_atTop.eventually_gt_atTop R
  have hexp1 : Complex.exp a = 1 := by
    by_contra hne1
    have hd : Complex.exp a - 1 ≠ 0 := sub_ne_zero.mpr hne1
    have hev0 : (fun z => z * (Complex.exp a - 1)) =ᶠ[cobounded ℂ]
        (fun z => (bottcherCoord c₁ z - z) - Complex.exp a * (bottcherCoord c₂ z - z)) := by
      filter_upwards [hWcob] with z hz
      have hzW : z ∈ W := by rw [hWeq]; exact hz
      rw [hWfull hzW]; ring
    have hT0 : Tendsto (fun z => z * (Complex.exp a - 1)) (cobounded ℂ) (𝓝 0) := by
      have h := (tendsto_bottcherCoord_sub_id c₁).sub
        ((tendsto_bottcherCoord_sub_id c₂).const_mul (Complex.exp a))
      have h0 : Tendsto (fun z => (bottcherCoord c₁ z - z) - Complex.exp a * (bottcherCoord c₂ z - z))
          (cobounded ℂ) (𝓝 0) := by simpa using h
      exact h0.congr' hev0.symm
    have hTinf : Tendsto (fun z : ℂ => ‖z * (Complex.exp a - 1)‖) (cobounded ℂ) atTop := by
      simp only [norm_mul]
      exact Tendsto.atTop_mul_const (norm_pos_iff.mpr hd) tendsto_norm_cobounded_atTop
    exact (not_tendsto_nhds_of_tendsto_atTop hTinf 0) (by simpa using hT0.norm)
  -- conclude
  apply c_eq_of_bottcherCoord_eqOn
  intro z hz
  have hzW : z ∈ W := by rw [hWeq]; exact hz
  have hfin := hWfull hzW
  simp only [hexp1, one_mul] at hfin
  exact hfin

end Bottcher

namespace Bottcher

/-- **The filled Julia set determines the parameter** (E1 ∘ E2): `K_{c₁} = K_{c₂} ⟹ c₁ = c₂`. The
full Julia-set rigidity feeding `compact_subset_of_full` in the connected-case independence. -/
theorem c_eq_of_filledJulia_eq {c₁ c₂ : ℂ}
    (hK : IsPreconnected (filledJulia c₁)ᶜ) (h : filledJulia c₁ = filledJulia c₂) : c₁ = c₂ :=
  c_eq_of_greenFunctionDyn_eq (greenFunctionDyn_eq_of_filledJulia_eq h hK)

end Bottcher

namespace Bottcher

/-- **The filled Julia set determines the parameter — UNCONDITIONAL** (E, fully closed):
`K_{c₁} = K_{c₂} ⟹ c₁ = c₂`, with basin-connectedness now discharged by
`isPreconnected_compl_filledJulia`. This is the Julia-set rigidity feeding `compact_subset_of_full`
in the connected-case independence, with no remaining hypotheses. -/
theorem c_eq_of_filledJulia_eq' {c₁ c₂ : ℂ} (h : filledJulia c₁ = filledJulia c₂) : c₁ = c₂ :=
  c_eq_of_filledJulia_eq (isPreconnected_compl_filledJulia c₁) h

end Bottcher
