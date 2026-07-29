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
    have hfin' : ({w : ℂ | w ^ N = 1} \ {v₀}).Finite := hTfin.subset Set.sdiff_subset
    have hcompl : ({w : ℂ | w ^ N = 1} \ {v₀})ᶜ ∈ 𝓝 v₀ :=
      hfin'.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hsrc.eventually_mem hcompl, hsr_pow] with z hz hzpow
    by_contra hne
    exact hz ⟨hzpow, by simpa using hne⟩
  have hseq : s =ᶠ[𝓝 z₀] (fun z => v₀ * r z) := by
    filter_upwards [hsr_const, hrne] with z hz hrnz
    exact (div_eq_iff hrnz).mp hz
  exact (analyticAt_const.mul hra).congr hseq.symm

/-- **A continuous `N`-th root of an analytic nowhere-zero function is analytic.** Globalisation of
`analyticAt_of_continuousAt_pow_eq` over an open set: if `s` is merely continuous on the open `U`,
`g` is analytic and nowhere-zero on `U`, and `s^N = g` on `U` (`N ≥ 1`), then `s` is analytic on `U`.
This is the final step of every root construction: the topology only has to supply a *continuous*
branch, and analyticity is then automatic. -/
theorem analyticOnNhd_of_continuousOn_pow_eq {U : Set ℂ} (hUo : IsOpen U) {s g : ℂ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (hsc : ContinuousOn s U) (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0)
    (hpow : ∀ z ∈ U, s z ^ N = g z) :
    AnalyticOnNhd ℂ s U := by
  intro z hz
  exact analyticAt_of_continuousAt_pow_eq hN (hsc.continuousAt (hUo.mem_nhds hz)) (hg z hz)
    (hg0 z hz) (Filter.eventually_of_mem (hUo.mem_nhds hz) (fun w hw => hpow w hw))

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

/-- **The negated slit-exterior sector is simply connected.** `{R < ‖z‖ ∧ -z ∈ slitPlane}` (the
exterior of the disk of radius `R`, minus the *positive*-real slit) is simply connected: it is the
image of the slit sector `isSimplyConnected_sector` under the homeomorphism `z ↦ -z`. This is the
second chart of the two-sector cover of the escape-level annulus. -/
theorem isSimplyConnected_sector_neg {R : ℝ} (hR : 0 < R) :
    IsSimplyConnected {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} := by
  have hemb : IsEmbedding (fun z : ℂ => -z) := (Homeomorph.neg ℂ).isEmbedding
  have himg : (fun z : ℂ => -z) '' {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane}
      = {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} := by
    ext w
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨by simpa using ha1, by simpa using ha2⟩
    · rintro ⟨hw1, hw2⟩
      exact ⟨-w, ⟨by simpa using hw1, by simpa using hw2⟩, by simp⟩
  rw [← himg, hemb.isSimplyConnected_image]
  exact isSimplyConnected_sector hR

/-- **Openness of the slit-exterior sectors.** -/
theorem isOpen_sector {R : ℝ} : IsOpen {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} :=
  (isOpen_lt continuous_const continuous_norm).inter Complex.isOpen_slitPlane

/-- **Openness of the negated slit-exterior sector.** -/
theorem isOpen_sector_neg {R : ℝ} : IsOpen {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} :=
  (isOpen_lt continuous_const continuous_norm).inter
    (Complex.isOpen_slitPlane.preimage continuous_neg)

/-- **Two-sector cover of the punctured exterior.** For `R > 0` the exterior `{R < ‖z‖}` is the union
of the two slit-exterior sectors (slits along the negative and the positive real axis): a point fails
to lie in `slitPlane` only on the nonpositive real axis, where its negation lies in `slitPlane`. The
two charts on which the per-level Böttcher root is built; they are each simply connected
(`isSimplyConnected_sector`, `isSimplyConnected_sector_neg`) and glue by `analyticOnNhd_glue_twoChart`
once the two sector roots are matched across the overlap (the winding identification). -/
theorem exterior_eq_sector_union {R : ℝ} (hR : 0 < R) :
    {z : ℂ | R < ‖z‖}
      = {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} ∪ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} := by
  ext z
  simp only [mem_setOf_eq, mem_union]
  constructor
  · intro hz
    by_cases hzs : z ∈ slitPlane
    · exact Or.inl ⟨hz, hzs⟩
    · refine Or.inr ⟨hz, ?_⟩
      rw [Complex.mem_slitPlane_iff] at hzs ⊢
      simp only [not_or, not_lt, not_not] at hzs
      obtain ⟨hre, him⟩ := hzs
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
      have hrelt : z.re < 0 := by
        rcases lt_or_eq_of_le hre with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hz0
      left; simp only [Complex.neg_re]; linarith
  · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz

/-- **Two `N`-th roots of the same function differ by a constant root of unity on a connected set.**
If `V` is preconnected, `s₁, s₂` are continuous on `V` with `s₂` nowhere zero and `s₁^N = s₂^N` on
`V` (`N ≥ 1`), then there is an `N`-th root of unity `ζ` with `s₁ = ζ · s₂` on `V`.  Mechanism:
`q = s₁/s₂` is continuous on `V` into the finite (hence separated) set of `N`-th roots of unity, so
by preconnectedness its image is a single point `ζ`.  This is the per-component discrepancy of two
sector roots in the escape-level cover: across each overlap component the two Böttcher root branches
differ by a fixed root of unity, and the winding identity forces that constant to be `1`. -/
theorem root_ratio_const_of_isPreconnected {V : Set ℂ} {s₁ s₂ : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hVc : IsPreconnected V)
    (h₁ : ContinuousOn s₁ V) (h₂ : ContinuousOn s₂ V)
    (h20 : ∀ z ∈ V, s₂ z ≠ 0)
    (hpow : ∀ z ∈ V, s₁ z ^ N = s₂ z ^ N) :
    ∃ ζ : ℂ, ζ ^ N = 1 ∧ ∀ z ∈ V, s₁ z = ζ * s₂ z := by
  rcases V.eq_empty_or_nonempty with hVe | ⟨z₀, hz₀⟩
  · exact ⟨1, one_pow N, fun z hz => by rw [hVe] at hz; exact absurd hz (Set.notMem_empty z)⟩
  set q : ℂ → ℂ := fun z => s₁ z / s₂ z with hqdef
  have hqc : ContinuousOn q V := h₁.div h₂ h20
  have hqpow : ∀ z ∈ V, q z ^ N = 1 := fun z hz => by
    rw [hqdef]; simp only [div_pow, hpow z hz, div_self (pow_ne_zero N (h20 z hz))]
  have hfactor : ∀ w ∈ V, s₁ w = q w * s₂ w := fun w hw => by
    have hne := h20 w hw; rw [hqdef]; field_simp
  set ζ : ℂ := q z₀ with hζdef
  refine ⟨ζ, hqpow z₀ hz₀, fun z hz => ?_⟩
  rw [hfactor z hz]
  -- It remains to show `q z = ζ`.
  have hTfin : {w : ℂ | w ^ N = 1}.Finite := by
    have hpne : (Polynomial.X ^ N - 1 : Polynomial ℂ) ≠ 0 := by
      have := Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < N) (1 : ℂ); simpa using this
    have heq : {w : ℂ | w ^ N = 1} = {w | (Polynomial.X ^ N - 1 : Polynomial ℂ).IsRoot w} := by
      ext w; simp [Polynomial.IsRoot, sub_eq_zero]
    rw [heq]; exact Polynomial.finite_setOf_isRoot hpne
  have hScl : IsClosed ({w : ℂ | w ^ N = 1} \ {ζ}) :=
    (hTfin.subset Set.sdiff_subset).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hScl.isOpen_compl ζ (by
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not]
    exact fun _ => trivial)
  -- `hball : Metric.ball ζ r ⊆ ({w | w^N=1} \ {ζ})ᶜ`; any root in `ball ζ r` equals `ζ`.
  have hroot_eq : ∀ w, dist w ζ < r → w ^ N = 1 → w = ζ := by
    intro w hwd hwr
    have : w ∈ ({u : ℂ | u ^ N = 1} \ {ζ})ᶜ := hball (by rw [Metric.mem_ball]; exact hwd)
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, not_and, not_not] at this
    exact this hwr
  -- Two opens separating `ζ` from the other roots.
  obtain ⟨O₁, hO₁o, hO₁⟩ := (continuousOn_iff'.mp hqc) (Metric.ball ζ r) Metric.isOpen_ball
  obtain ⟨O₂, hO₂o, hO₂⟩ := (continuousOn_iff'.mp hqc) {w : ℂ | r / 2 < dist w ζ}
    (isOpen_lt continuous_const (continuous_id.dist continuous_const))
  have hcover : V ⊆ O₁ ∪ O₂ := by
    intro w hw
    by_cases hd : dist (q w) ζ < r
    · left
      have : w ∈ q ⁻¹' Metric.ball ζ r ∩ V :=
        ⟨by rw [Set.mem_preimage, Metric.mem_ball]; exact hd, hw⟩
      rw [hO₁] at this; exact this.1
    · right
      have : w ∈ q ⁻¹' {w : ℂ | r / 2 < dist w ζ} ∩ V :=
        ⟨by rw [Set.mem_preimage, Set.mem_setOf_eq]; rw [not_lt] at hd; linarith, hw⟩
      rw [hO₂] at this; exact this.1
  have hz₀O₁ : z₀ ∈ O₁ := by
    have : z₀ ∈ q ⁻¹' Metric.ball ζ r ∩ V :=
      ⟨by rw [Set.mem_preimage, Metric.mem_ball, ← hζdef, dist_self]; exact hr, hz₀⟩
    rw [hO₁] at this; exact this.1
  have hVO₂ : V ∩ O₂ = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hne2
    have hkey := hVc O₁ O₂ hO₁o hO₂o hcover ⟨z₀, hz₀, hz₀O₁⟩ hne2
    obtain ⟨w, hwV, hwO₁, hwO₂⟩ := hkey
    have hw1 : w ∈ q ⁻¹' Metric.ball ζ r ∩ V := by rw [hO₁]; exact ⟨hwO₁, hwV⟩
    have hw2 : w ∈ q ⁻¹' {w : ℂ | r / 2 < dist w ζ} ∩ V := by rw [hO₂]; exact ⟨hwO₂, hwV⟩
    have hd1 : dist (q w) ζ < r := by
      have := hw1.1; rw [Set.mem_preimage, Metric.mem_ball] at this; exact this
    have hd2 : r / 2 < dist (q w) ζ := by
      have := hw2.1; rw [Set.mem_preimage, Set.mem_setOf_eq] at this; exact this
    have hqζ : q w = ζ := hroot_eq (q w) hd1 (hqpow w hwV)
    rw [hqζ, dist_self] at hd2; linarith
  have hzO₁ : z ∈ O₁ := by
    rcases hcover hz with h | h
    · exact h
    · exact absurd (Set.mem_inter hz h) (by rw [hVO₂]; exact Set.notMem_empty z)
  have hzpre : z ∈ q ⁻¹' Metric.ball ζ r ∩ V := by rw [hO₁]; exact ⟨hzO₁, hz⟩
  have hd : dist (q z) ζ < r := by
    have := hzpre.1; rw [Set.mem_preimage, Metric.mem_ball] at this; exact this
  rw [hroot_eq (q z) hd (hqpow z hz)]

/-- **Two `N`-th roots of the same nowhere-zero function that agree at one point of a connected set
agree on it.** Specialisation of `root_ratio_const_of_isPreconnected`: the per-component root-of-unity
discrepancy is `1` once the roots are pinned at a single point.  This is how the two sector roots are
matched across each overlap component of the escape-level cover. -/
theorem eqOn_of_pow_eq_of_isPreconnected {V : Set ℂ} {s₁ s₂ : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hVc : IsPreconnected V) (h₁ : ContinuousOn s₁ V) (h₂ : ContinuousOn s₂ V)
    (h20 : ∀ z ∈ V, s₂ z ≠ 0) (hpow : ∀ z ∈ V, s₁ z ^ N = s₂ z ^ N)
    {p : ℂ} (hp : p ∈ V) (hmatch : s₁ p = s₂ p) :
    Set.EqOn s₁ s₂ V := by
  obtain ⟨ζ, _hζ, heq⟩ := root_ratio_const_of_isPreconnected hN hVc h₁ h₂ h20 hpow
  have hζ1 : ζ = 1 := by
    have hpp := heq p hp
    rw [hmatch] at hpp
    have hcancel : ζ * s₂ p = 1 * s₂ p := by rw [one_mul]; exact hpp.symm
    exact mul_right_cancel₀ (h20 p hp) hcancel
  intro z hz; rw [heq z hz, hζ1, one_mul]

/-- **The two slit-exterior sectors overlap in the slit-free exterior.** Their intersection is exactly
`{R < ‖z‖ ∧ z.im ≠ 0}` (a point off the real axis lies in both slit planes; a real point lies in at
most one).  This overlap has two connected components — the upper and lower exterior half-planes — on
each of which the two sector roots are matched. -/
theorem sector_inter_sector_neg {R : ℝ} :
    {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} ∩ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane}
      = {z : ℂ | R < ‖z‖ ∧ z.im ≠ 0} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Complex.mem_slitPlane_iff, Complex.neg_re,
    Complex.neg_im, ne_eq, neg_eq_zero]
  constructor
  · rintro ⟨⟨hz, h1⟩, _, h2⟩
    refine ⟨hz, ?_⟩
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exfalso; linarith
      · exact h2
    · exact h1
  · rintro ⟨hz, him⟩
    exact ⟨⟨hz, Or.inr him⟩, hz, Or.inr him⟩

/-- **Analytic `N`-th root on the punctured exterior from two matched sector roots.** Writing the
exterior `{R < ‖z‖}` as the union of the two simply-connected slit sectors
(`exterior_eq_sector_union`), if `s₁, s₂` are analytic `N`-th roots of `g` on the two sectors that
agree on the overlap, they glue (`analyticOnNhd_glue_twoChart`) to an analytic `N`-th root of `g` on
the whole exterior.  Producing the agreeing roots is the winding step: the sector roots exist by
`exists_analyticOnNhd_pow_eq`, and agreement on the overlap reduces by
`eqOn_of_pow_eq_of_isPreconnected` to matching them at one point of each overlap component — which is
possible exactly when `N` divides the winding number of `g` around the disk. -/
theorem exists_pow_eq_exterior_of_sectorRoots
    {R : ℝ} (hR : 0 < R) {g s₁ s₂ : ℂ → ℂ} {N : ℕ}
    (hs₁ : AnalyticOnNhd ℂ s₁ {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane})
    (hs₂ : AnalyticOnNhd ℂ s₂ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane})
    (hs₁pow : ∀ z, R < ‖z‖ → z ∈ slitPlane → s₁ z ^ N = g z)
    (hs₂pow : ∀ z, R < ‖z‖ → -z ∈ slitPlane → s₂ z ^ N = g z)
    (hagree : Set.EqOn s₁ s₂
      ({z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} ∩ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane})) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s {z : ℂ | R < ‖z‖} ∧ ∀ z, R < ‖z‖ → s z ^ N = g z := by
  obtain ⟨s, hsan, hs1eq, hs2eq⟩ :=
    analyticOnNhd_glue_twoChart isOpen_sector isOpen_sector_neg hs₁ hs₂ hagree
  rw [← exterior_eq_sector_union hR] at hsan
  refine ⟨s, hsan, fun z hz => ?_⟩
  have hzU : z ∈ {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} ∪ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} := by
    rw [← exterior_eq_sector_union hR]; exact hz
  rcases hzU with h | h
  · rw [hs1eq h]; exact hs₁pow z h.1 h.2
  · rw [hs2eq h]; exact hs₂pow z h.1 h.2

/-- A point of the upper exterior half-plane lies in the (negative-real-)slit sector. -/
theorem mem_sector_of_upper {R : ℝ} {z : ℂ} (hzR : R < ‖z‖) (him : 0 < z.im) :
    z ∈ {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} :=
  ⟨hzR, Complex.mem_slitPlane_iff.mpr (Or.inr him.ne')⟩

/-- A point of the upper exterior half-plane lies in the positive-real-slit sector. -/
theorem mem_sector_neg_of_upper {R : ℝ} {z : ℂ} (hzR : R < ‖z‖) (him : 0 < z.im) :
    z ∈ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} :=
  ⟨hzR, Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using him.ne'))⟩

/-- A point of the lower exterior half-plane lies in the (negative-real-)slit sector. -/
theorem mem_sector_of_lower {R : ℝ} {z : ℂ} (hzR : R < ‖z‖) (him : z.im < 0) :
    z ∈ {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane} :=
  ⟨hzR, Complex.mem_slitPlane_iff.mpr (Or.inr him.ne)⟩

/-- A point of the lower exterior half-plane lies in the positive-real-slit sector. -/
theorem mem_sector_neg_of_lower {R : ℝ} {z : ℂ} (hzR : R < ‖z‖) (him : z.im < 0) :
    z ∈ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane} :=
  ⟨hzR, Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using him.ne))⟩

/-- **Exterior `N`-th root from sector roots matched at one point of each half-plane.** The full
reduction of the annulus root: given analytic `N`-th roots `s₁, s₂` of `g` on the two slit sectors
that coincide at a single point `pU` of the upper exterior half-plane and a single point `pL` of the
lower one, they glue to an analytic `N`-th root of `g` on the whole exterior `{R < ‖z‖}`.  Mechanism:
each overlap half-plane is preconnected, so by `eqOn_of_pow_eq_of_isPreconnected` the single matching
point forces agreement on that half; the two halves are the whole overlap (`sector_inter_sector_neg`),
so `exists_pow_eq_exterior_of_sectorRoots` glues.  The two matching points encode the
winding-divisibility condition (`N ∣ winding g`): they can be chosen exactly when the winding number
is divisible by `N`. -/
theorem exists_pow_eq_exterior_of_sectorRoots_match
    {R : ℝ} (hR : 0 < R) {g s₁ s₂ : ℂ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hs₁ : AnalyticOnNhd ℂ s₁ {z : ℂ | R < ‖z‖ ∧ z ∈ slitPlane})
    (hs₂ : AnalyticOnNhd ℂ s₂ {z : ℂ | R < ‖z‖ ∧ -z ∈ slitPlane})
    (hs₁pow : ∀ z, R < ‖z‖ → z ∈ slitPlane → s₁ z ^ N = g z)
    (hs₂pow : ∀ z, R < ‖z‖ → -z ∈ slitPlane → s₂ z ^ N = g z)
    (hg0 : ∀ z, R < ‖z‖ → g z ≠ 0)
    (hUpc : IsPreconnected {z : ℂ | R < ‖z‖ ∧ 0 < z.im})
    (hLpc : IsPreconnected {z : ℂ | R < ‖z‖ ∧ z.im < 0})
    {pU pL : ℂ} (hpUR : R < ‖pU‖) (hpUi : 0 < pU.im) (hpLR : R < ‖pL‖) (hpLi : pL.im < 0)
    (hmU : s₁ pU = s₂ pU) (hmL : s₁ pL = s₂ pL) :
    ∃ s : ℂ → ℂ, AnalyticOnNhd ℂ s {z : ℂ | R < ‖z‖} ∧ ∀ z, R < ‖z‖ → s z ^ N = g z := by
  -- continuity / nonvanishing / pow-agreement of the two roots on each half-plane
  have hcontU₁ : ContinuousOn s₁ {z : ℂ | R < ‖z‖ ∧ 0 < z.im} :=
    (hs₁.mono (fun z hz => mem_sector_of_upper hz.1 hz.2)).continuousOn
  have hcontU₂ : ContinuousOn s₂ {z : ℂ | R < ‖z‖ ∧ 0 < z.im} :=
    (hs₂.mono (fun z hz => mem_sector_neg_of_upper hz.1 hz.2)).continuousOn
  have hcontL₁ : ContinuousOn s₁ {z : ℂ | R < ‖z‖ ∧ z.im < 0} :=
    (hs₁.mono (fun z hz => mem_sector_of_lower hz.1 hz.2)).continuousOn
  have hcontL₂ : ContinuousOn s₂ {z : ℂ | R < ‖z‖ ∧ z.im < 0} :=
    (hs₂.mono (fun z hz => mem_sector_neg_of_lower hz.1 hz.2)).continuousOn
  have hne₂ : ∀ z, R < ‖z‖ → -z ∈ slitPlane → s₂ z ≠ 0 := by
    intro z hzR hzs h0
    exact hg0 z hzR (by rw [← hs₂pow z hzR hzs, h0, zero_pow (by omega : N ≠ 0)])
  have hUpow : ∀ z ∈ {z : ℂ | R < ‖z‖ ∧ 0 < z.im}, s₁ z ^ N = s₂ z ^ N := fun z hz =>
    (hs₁pow z hz.1 (mem_sector_of_upper hz.1 hz.2).2).trans
      (hs₂pow z hz.1 (mem_sector_neg_of_upper hz.1 hz.2).2).symm
  have hLpow : ∀ z ∈ {z : ℂ | R < ‖z‖ ∧ z.im < 0}, s₁ z ^ N = s₂ z ^ N := fun z hz =>
    (hs₁pow z hz.1 (mem_sector_of_lower hz.1 hz.2).2).trans
      (hs₂pow z hz.1 (mem_sector_neg_of_lower hz.1 hz.2).2).symm
  -- agreement on each half-plane from the single matching point
  have heqU : Set.EqOn s₁ s₂ {z : ℂ | R < ‖z‖ ∧ 0 < z.im} :=
    eqOn_of_pow_eq_of_isPreconnected hN hUpc hcontU₁ hcontU₂
      (fun z hz => hne₂ z hz.1 (mem_sector_neg_of_upper hz.1 hz.2).2) hUpow ⟨hpUR, hpUi⟩ hmU
  have heqL : Set.EqOn s₁ s₂ {z : ℂ | R < ‖z‖ ∧ z.im < 0} :=
    eqOn_of_pow_eq_of_isPreconnected hN hLpc hcontL₁ hcontL₂
      (fun z hz => hne₂ z hz.1 (mem_sector_neg_of_lower hz.1 hz.2).2) hLpow ⟨hpLR, hpLi⟩ hmL
  -- combine into agreement on the whole overlap
  refine exists_pow_eq_exterior_of_sectorRoots hR hs₁ hs₂ hs₁pow hs₂pow ?_
  rw [sector_inter_sector_neg]
  intro z hz
  rcases lt_or_gt_of_ne hz.2 with hlt | hgt
  · exact heqL ⟨hz.1, hlt⟩
  · exact heqU ⟨hz.1, hgt⟩

end Bottcher
