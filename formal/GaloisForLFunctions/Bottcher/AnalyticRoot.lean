/-
# Analytic `N`-th roots on simply-connected regions

Toward the per-level Böttcher root (the connected Böttcher uniformization). Mathlib's
`Complex.exists_continuousOn_pow_eq` produces a CONTINUOUS branch of `ⁿ√g` on a simply-connected open
set where `g` is continuous and nonvanishing. Two utilities here:

* `analyticAt_of_continuousAt_pow_eq` — the **analyticity upgrade**: a continuous function `s` with
  `s^N = g` near `z₀` (for analytic nonvanishing `g`) is itself analytic at `z₀`. Mechanism: locally
  `g` has an analytic `N`-th root `r = a·exp(N⁻¹·log(g/g z₀))`, and `s/r` is a continuous
  root-of-unity-valued function, hence locally constant, so `s = ζ·r` is analytic.
* `exists_analyticOnNhd_pow_eq` — combining the two: on a simply-connected open `U`, an analytic
  nowhere-zero `g` has an **analytic** `N`-th root.

These are the simply-connected building block of the per-level `2ⁿ`-th-root branch `βlev n`
(`BasinColimit.exists_global_branch_of_level_roots`); the full (non-simply-connected) escape level
needs gluing such roots across a cut — the winding identification.

New file (hRigid / connected lane, analytic-root utilities — Mathlib-only deps).
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic

open Complex Filter Topology Set

namespace Bottcher

/-- **Analyticity upgrade for a continuous root.** If `s` is continuous at `z₀`, `g` is analytic at
`z₀` with `g z₀ ≠ 0`, and `s^N = g` near `z₀` (`N ≥ 1`), then `s` is analytic at `z₀`. Locally `g` has
an analytic `N`-th root `r = a·exp(N⁻¹·log(g/g z₀))` (with `a^N = g z₀`); `s/r` is a continuous
root-of-unity-valued function, hence locally constant, so `s = ζ·r` is analytic. -/
theorem analyticAt_of_continuousAt_pow_eq {s g : ℂ → ℂ} {z₀ : ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hsc : ContinuousAt s z₀) (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0)
    (hpow : ∀ᶠ z in 𝓝 z₀, s z ^ N = g z) :
    AnalyticAt ℂ s z₀ := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set a : ℂ := Complex.exp (Complex.log (g z₀) / (N : ℂ)) with hadef
  have ha : a ^ N = g z₀ := by
    rw [hadef, ← Complex.exp_nat_mul,
      show (N : ℂ) * (Complex.log (g z₀) / (N : ℂ)) = Complex.log (g z₀) from by field_simp]
    exact Complex.exp_log hg0
  have ha0 : a ≠ 0 := Complex.exp_ne_zero _
  have hgw : AnalyticAt ℂ (fun z => g z / g z₀) z₀ := hg.div analyticAt_const hg0
  have hmem : (fun z => g z / g z₀) z₀ ∈ slitPlane := by
    show g z₀ / g z₀ ∈ slitPlane; rw [div_self hg0]; exact one_mem_slitPlane
  have hL : AnalyticAt ℂ (fun z => Complex.log (g z / g z₀)) z₀ := hgw.clog hmem
  set r : ℂ → ℂ := fun z => a * Complex.exp (((N : ℂ)⁻¹) * Complex.log (g z / g z₀)) with hrdef
  have hra : AnalyticAt ℂ r z₀ := analyticAt_const.mul ((analyticAt_const.mul hL).cexp)
  have hr0 : r z₀ ≠ 0 := mul_ne_zero ha0 (Complex.exp_ne_zero _)
  have hgne : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hrpow : ∀ᶠ z in 𝓝 z₀, r z ^ N = g z := by
    filter_upwards [hgne] with z hz
    have hqne : g z / g z₀ ≠ 0 := div_ne_zero hz hg0
    rw [hrdef]; simp only
    rw [mul_pow, ha, ← Complex.exp_nat_mul,
      show (N : ℂ) * ((N : ℂ)⁻¹ * Complex.log (g z / g z₀)) = Complex.log (g z / g z₀) from by
        field_simp, Complex.exp_log hqne]
    field_simp
  have hrne : ∀ᶠ z in 𝓝 z₀, r z ≠ 0 := hra.continuousAt.eventually_ne hr0
  have hsr_pow : ∀ᶠ z in 𝓝 z₀, (s z / r z) ^ N = 1 := by
    filter_upwards [hpow, hrpow, hrne, hgne] with z hsz hrz hrnz hgz
    rw [div_pow, hsz, hrz, div_self hgz]
  have hTfin : {w : ℂ | w ^ N = 1}.Finite := by
    have hpne : (Polynomial.X ^ N - 1 : Polynomial ℂ) ≠ 0 := by
      have := Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < N) (1 : ℂ); simpa using this
    have heq : {w : ℂ | w ^ N = 1} = {w | (Polynomial.X ^ N - 1 : Polynomial ℂ).IsRoot w} := by
      ext w; simp [Polynomial.IsRoot, sub_eq_zero]
    rw [heq]; exact Polynomial.finite_setOf_isRoot hpne
  have hsrc : ContinuousAt (fun z => s z / r z) z₀ := hsc.div hra.continuousAt hr0
  set v₀ : ℂ := s z₀ / r z₀ with hv₀
  have hsr_const : ∀ᶠ z in 𝓝 z₀, s z / r z = v₀ := by
    have hfin' : ({w : ℂ | w ^ N = 1} \ {v₀}).Finite := hTfin.subset Set.diff_subset
    have hcompl : ({w : ℂ | w ^ N = 1} \ {v₀})ᶜ ∈ 𝓝 v₀ :=
      hfin'.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hsrc.eventually_mem hcompl, hsr_pow] with z hz hzpow
    by_contra hne
    exact hz ⟨hzpow, by simpa using hne⟩
  have hseq : s =ᶠ[𝓝 z₀] (fun z => v₀ * r z) := by
    filter_upwards [hsr_const, hrne] with z hz hrnz
    exact (div_eq_iff hrnz).mp hz
  exact (analyticAt_const.mul hra).congr hseq.symm

/-- **Analytic `N`-th root on a simply-connected region.** If `U` is open and simply connected and `g`
is analytic and nowhere-zero on `U`, then `g` has an analytic `N`-th root on `U` (`N ≥ 1`). Mathlib's
`exists_continuousOn_pow_eq` gives a CONTINUOUS branch on the simply-connected `U`; the analyticity
upgrade `analyticAt_of_continuousAt_pow_eq` makes it analytic pointwise. The simply-connected building
block of the per-level Böttcher root. -/
theorem exists_analyticOnNhd_pow_eq {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s U ∧ ∀ z ∈ U, s z ^ N = g z := by
  obtain ⟨f, hfc, hf⟩ := exists_continuousOn_pow_eq hUc hUo hg.continuousOn
    (by rintro ⟨z, hz, hz0⟩; exact hg0 z hz hz0) (by omega : N ≠ 0)
  refine ⟨f, fun z hz => ?_, fun z _ => hf z⟩
  exact analyticAt_of_continuousAt_pow_eq hN (hfc.continuousAt (hUo.mem_nhds hz))
    (hg z hz) (hg0 z hz) (Filter.Eventually.of_forall hf)

/-- **Two-chart analytic gluing.** Two analytic functions on open sets that agree on the overlap glue
to an analytic function on the union (restricting to each chart). The gluing mechanism of the per-level
root's cut-and-match: the content is producing the overlap-agreement (the winding identification); the
gluing itself is `V₁.piecewise`, analytic since locally it is one chart or the other. -/
theorem analyticOnNhd_glue_twoChart {V₁ V₂ : Set ℂ} {s₁ s₂ : ℂ → ℂ}
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂)
    (h₁ : AnalyticOnNhd ℂ s₁ V₁) (h₂ : AnalyticOnNhd ℂ s₂ V₂)
    (hagree : EqOn s₁ s₂ (V₁ ∩ V₂)) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s (V₁ ∪ V₂) ∧ EqOn s s₁ V₁ ∧ EqOn s s₂ V₂ := by
  classical
  refine ⟨V₁.piecewise s₁ s₂, ?_, ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · have hloc : V₁.piecewise s₁ s₂ =ᶠ[𝓝 z] s₁ := by
        filter_upwards [hV₁.mem_nhds hz] with w hw
        simp [Set.piecewise, hw]
      exact (h₁ z hz).congr hloc.symm
    · have hloc : V₁.piecewise s₁ s₂ =ᶠ[𝓝 z] s₂ := by
        filter_upwards [hV₂.mem_nhds hz] with w hw
        by_cases hw1 : w ∈ V₁
        · simp [Set.piecewise, hw1, hagree ⟨hw1, hw⟩]
        · simp [Set.piecewise, hw1]
      exact (h₂ z hz).congr hloc.symm
  · intro z hz; simp [Set.piecewise, hz]
  · intro z hz
    by_cases hz1 : z ∈ V₁
    · simp [Set.piecewise, hz1, hagree ⟨hz1, hz⟩]
    · simp [Set.piecewise, hz1]

/-- **An annular sector is simply connected.** `{z : R < ‖z‖ ∧ z ∈ slitPlane}` (the exterior of the disk
of radius `R`, minus the negative-real slit) is simply connected, for `R > 0`: it is the image of the
convex strip `{Real.log R < Re w, |Im w| < π}` under the open embedding `exp` (injective there since the
strip has height `< 2π`), and a convex set is contractible hence simply connected
(`Convex.contractibleSpace` → `SimplyConnectedSpace.ofContractible`, transported along the embedding by
`IsEmbedding.isSimplyConnected_image`). The slit cuts the loop around the disk, making the sector simply
connected. This is the building block of every escape-level chart of the connected Böttcher
uniformization. -/
theorem isSimplyConnected_sector {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} := by
  set S : Set ℂ := {w : ℂ | Real.log R < w.re ∧ -Real.pi < w.im ∧ w.im < Real.pi} with hSdef
  have hSo : IsOpen S := by
    have he : S = {w : ℂ | Real.log R < w.re} ∩ {w : ℂ | -Real.pi < w.im} ∩ {w : ℂ | w.im < Real.pi} := by
      ext w; simp only [hSdef, mem_setOf_eq, mem_inter_iff]; tauto
    rw [he]
    exact ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_const continuous_im)).inter (isOpen_lt continuous_im continuous_const)
  have hSconv : Convex ℝ S := by
    have he : S = ({w : ℂ | Real.log R < w.re} ∩ {w : ℂ | -Real.pi < w.im}) ∩ {w : ℂ | w.im < Real.pi} := by
      ext w; simp only [hSdef, mem_setOf_eq, mem_inter_iff]; tauto
    rw [he]
    exact ((convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)).inter (convex_halfSpace_im_lt _)
  have hSne : S.Nonempty := ⟨((Real.log R + 1 : ℝ) : ℂ), by
    refine ⟨by simp, ?_, ?_⟩ <;> simp [Real.pi_pos]⟩
  set e : S → ℂ := fun w => Complex.exp (w : ℂ) with hedef
  have hcont : Continuous e := Complex.continuous_exp.comp continuous_subtype_val
  have hinj : Function.Injective e := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [hedef] at h
    rw [exp_eq_exp_iff_exists_int] at h
    obtain ⟨n, hn⟩ := h
    have hd : a - b = (n:ℂ) * (2 * (Real.pi:ℂ) * I) := by rw [hn]; ring
    have him : a.im - b.im = (n:ℝ) * (2 * Real.pi) := by
      have := congrArg Complex.im hd
      simpa [Complex.sub_im, Complex.mul_im, Complex.mul_re] using this
    have hn0 : n = 0 := by
      have hd2 : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
        rw [← him, abs_lt]
        constructor <;> nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, Real.pi_pos]
      by_contra hne
      have h1 : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs (by exact_mod_cast hne)
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hd2
      nlinarith [Real.pi_pos]
    subst hn0; simp only [Int.cast_zero, zero_mul, add_zero] at hn
    exact Subtype.ext hn
  have hopen : IsOpenMap e := isOpenMap_exp.comp (hSo.isOpenMap_subtype_val)
  have hemb : IsEmbedding e :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isEmbedding
  have himg : e '' univ = {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} := by
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, -, rfl⟩
      refine ⟨?_, ?_⟩
      · show R < ‖Complex.exp w‖
        rw [Complex.norm_exp]
        calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
          _ < Real.exp w.re := Real.exp_lt_exp.mpr hw.1
      · show Complex.exp w ∈ slitPlane
        rw [Complex.mem_slitPlane_iff]
        by_cases hw0 : w.im = 0
        · left; rw [Complex.exp_re, hw0, Real.cos_zero, mul_one]; exact Real.exp_pos _
        · right; rw [Complex.exp_im]
          refine mul_ne_zero (Real.exp_ne_zero _) ?_
          intro hsin
          rw [Real.sin_eq_zero_iff] at hsin
          obtain ⟨k, hk⟩ := hsin
          rcases lt_trichotomy k 0 with hkneg | hk0 | hkpos
          · have hk1 : k ≤ -1 := by omega
            have : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
            nlinarith [hw.2.1, Real.pi_pos]
          · subst hk0; simp at hk; exact hw0 hk.symm
          · have hk1 : (1:ℤ) ≤ k := hkpos
            have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
            nlinarith [hw.2.2, Real.pi_pos]
    · rintro ⟨hz1, hz2⟩
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz1; linarith
      refine ⟨⟨Complex.log z, ?_, ?_, ?_⟩, mem_univ _, Complex.exp_log hz0⟩
      · rw [Complex.log_re]; exact Real.log_lt_log hR hz1
      · rw [Complex.log_im]; exact Complex.neg_pi_lt_arg z
      · rw [Complex.log_im]
        rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
        · exact h
        · exfalso
          obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp h
          rw [Complex.mem_slitPlane_iff] at hz2
          rcases hz2 with h' | h'
          · linarith
          · exact h' him
  rw [← himg, hemb.isSimplyConnected_image]
  haveI : ContractibleSpace S := hSconv.contractibleSpace hSne
  haveI : SimplyConnectedSpace S := SimplyConnectedSpace.ofContractible S
  exact ((Homeomorph.Set.univ S).toHomotopyEquiv).simplyConnectedSpace_iff.mpr ‹_›

end Bottcher
