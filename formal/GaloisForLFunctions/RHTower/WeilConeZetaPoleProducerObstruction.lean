import GaloisForLFunctions.RHTower.ZetaLineResonatorLargeValues
import GaloisForLFunctions.RHTower.WeilConeBoundaryMobiusAveraging

/-!
# ζ-type poles never produce Weil positivity

Let `v : ℕ → ℝ` with `v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`, and let `β ∈ ℝ`. The weight system
`λ(n) = β · [n ≥ 2] + v(n)` has Dirichlet series `β(ζ(s) − 1) + V(s)`, with the pole of `ζ`.

**Theorem** (`not_weilPositiveFull_poleSystem`). `λ` is never full-cone Weil-positive.

**Proof.** If it were, its Herglotz continuation `Φ` would satisfy
`(s − 1) Φ(s) = (s − 1)(G(s) + β − V(s)) + 1 − β (s − 1) ζ(s)` on `Re s > ½`, by the identity
theorem from `Re s > 1`. At `s = 1` this forces `β = 1`. Hence
`Φ = G + 1/(s − 1) + 1 − ζ − V` off `s = 1`. This is continuous up to the critical line, so
`Re Φ ≥ 0` gives `Re ζ(½+it) ≤ θ′(t) + 1 − Re V(½+it) ≤ log t + C` for `t ≥ 1`. That contradicts
the resonance theorem `ZetaResonator.exists_log_add_lt_re_zeta`.

So every Weil-positive system whose Dirichlet series carries the pole of `ζ` itself, up to an
absolutely convergent correction on the critical line, is excluded. A producer must carry its pole
in a logarithmic derivative.
-/

noncomputable section

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation
open RHTower.WeilZetaSquare

namespace RHTower.WeilZetaPole

open RHTower.WeilBoundaryDilation (BoundaryRegular regSeries)

/-- The weight system `λ(n) = β · [n ≥ 2] + v(n)`. -/
def poleSystem (β : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ := β * (if 2 ≤ n then 1 else 0) + v n

variable {β : ℝ} {v : ℕ → ℝ}

theorem LSeries_poleSystem (hv : BoundaryRegular v) {s : ℂ} (hs : 1 < s.re) :
    LSeries (lamC (poleSystem β v)) s = β * (riemannZeta s - 1) + regSeries v s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hV : LSeriesSummable (fun n => (v n : ℂ)) s :=
    hv.summable.of_re_le_re (by norm_num; linarith)
  have hδ : Summable fun n : ℕ => (β : ℂ) * (if n = 1 then 1 else 0) :=
    summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
  have hpt : ∀ n, LSeries.term (lamC (poleSystem β v)) s n =
      (β : ℂ) * LSeries.term 1 s n + LSeries.term (fun n => (v n : ℂ)) s n -
        (β : ℂ) * (if n = 1 then 1 else 0) := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [LSeries.term]
      · simp [LSeries.term, lamC, hv.one]
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      simp only [LSeries.term, if_neg hn0, if_neg hn1, lamC, poleSystem, if_pos h, Pi.one_apply]
      push_cast
      ring
  rw [LSeries, tsum_congr hpt, Summable.tsum_sub ((h1.mul_left _).add hV) hδ,
    Summable.tsum_add (h1.mul_left _) hV, tsum_mul_left, tsum_mul_left, tsum_ite_eq,
    ← LSeries, LSeries_one_eq_riemannZeta hs]
  simp only [regSeries, LSeries, mul_one]
  ring

/-- **The master identity** for `β · [n ≥ 2] + v` on `Re s > ½`. -/
theorem mul_weilContinuation_eq (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (poleSystem β v)) {s : ℂ} (hs : 1 / 2 < s.re) :
    (s - 1) * weilContinuation hW s =
      (s - 1) * (zetaArchimedeanDatum s + β - regSeries v s) + 1 - β * zetaResidueUnit s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2U : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  have hL : AnalyticOnNhd ℂ (fun s => (s - 1) * weilContinuation hW s) {s : ℂ | 1 / 2 < s.re} :=
    DifferentiableOn.analyticOnNhd (((differentiableOn_id.sub_const 1).mul
      (differentiableOn_weilContinuation hW))) hU
  have hR : AnalyticOnNhd ℂ (fun s => (s - 1) * (zetaArchimedeanDatum s + β - regSeries v s) + 1 -
      β * zetaResidueUnit s) {s : ℂ | 1 / 2 < s.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz' : 1 / 2 < z.re := hz
    have hG := differentiableAt_zetaArchimedeanDatum (s := z) (by linarith)
    have hV : DifferentiableAt ℂ (regSeries v) z :=
      (WeilBoundaryDilation.differentiableOn_regSeries hv).differentiableAt (hU.mem_nhds hz)
    have hZ := (analyticAt_zetaResidueUnit z).differentiableAt
    exact (((differentiableAt_id.sub_const 1).mul ((hG.add_const _).sub hV)).add_const _ |>.sub
      (hZ.const_mul _)).differentiableWithinAt
  refine hL.eqOn_of_preconnected_of_eventuallyEq hR hpre h2U ?_ hs
  have hV1 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hV1] with z hz
  have hz : 1 < z.re := hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [weilContinuation_eq hW hz, weilFunction, LSeries_poleSystem hv hz,
    (zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
  unfold zetaArchimedeanDatum
  field_simp
  ring

theorem beta_eq_one (hv : BoundaryRegular v) (hW : WeilPositiveFull (poleSystem β v)) : β = 1 := by
  have h := mul_weilContinuation_eq hv hW (s := 1) (by norm_num)
  simp only [sub_self, zero_mul, zetaResidueUnit_one, zero_add, mul_one] at h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The boundary function `G + 1/(s − 1) + 1 − ζ − V`. -/
def poleBoundary (v : ℕ → ℝ) (s : ℂ) : ℂ :=
  zetaArchimedeanDatum s + 1 / (s - 1) + 1 - riemannZeta s - regSeries v s

theorem weilContinuation_eq_poleBoundary (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (poleSystem β v)) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    weilContinuation hW s = poleBoundary v s := by
  have hβ := beta_eq_one hv hW
  subst hβ
  have h := mul_weilContinuation_eq hv hW hs
  rw [(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold poleBoundary
  apply mul_left_cancel₀ hs1'
  rw [h]
  field_simp
  push_cast
  ring

theorem continuousWithinAt_poleBoundary (hv : BoundaryRegular v) (t : ℝ) :
    ContinuousWithinAt (poleBoundary v) {s : ℂ | 1 / 2 ≤ s.re} (linePt t) := by
  have hre := linePt_re t
  have hs1 : linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hmem : linePt t ∈ {s : ℂ | 1 / 2 ≤ s.re} := by
    show (1 / 2 : ℝ) ≤ (linePt t).re; rw [hre]
  have hG : ContinuousAt zetaArchimedeanDatum (linePt t) :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hre]; norm_num)).continuousAt
  have hinv : ContinuousAt (fun s : ℂ => 1 / (s - 1)) (linePt t) :=
    continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1)
  have hZ : ContinuousAt riemannZeta (linePt t) := (differentiableAt_riemannZeta hs1).continuousAt
  have hV := WeilBoundaryDilation.continuousOn_regSeries hv (linePt t) hmem
  unfold poleBoundary
  exact ((((hG.add hinv).add continuousAt_const).sub hZ).continuousWithinAt).sub hV

theorem re_poleBoundary_line_nonneg (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (poleSystem β v)) (t : ℝ) : 0 ≤ (poleBoundary v (linePt t)).re := by
  have hre := linePt_re t
  obtain ⟨path, hpath⟩ : ∃ path : ℝ → ℂ, path = fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hpre : ∀ σ, (path σ).re = σ := fun σ => by simp [hpath]
  have hpath0 : path (1 / 2) = linePt t := by simp [hpath, linePt]
  have hpc : Continuous path := by rw [hpath]; fun_prop
  have hlim : Tendsto path (𝓝[>] (1 / 2)) (𝓝[{s : ℂ | 1 / 2 ≤ s.re}] (linePt t)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · rw [← hpath0]; exact hpc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      show (1 / 2 : ℝ) ≤ (path σ).re
      rw [hpre]; exact le_of_lt hσ
  have hfun : ContinuousWithinAt (fun s => (poleBoundary v s).re) {s : ℂ | 1 / 2 ≤ s.re}
      (linePt t) :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_poleBoundary hv t)
  refine ge_of_tendsto (hfun.tendsto.comp hlim) ?_
  have hev : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), σ < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hσ1
  have hσ' : (1 / 2 : ℝ) < σ := hσ
  have hne : path σ ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hpre] at this; simp at this; linarith
  have hs : 1 / 2 < (path σ).re := by rw [hpre]; exact hσ'
  show 0 ≤ (poleBoundary v (path σ)).re
  rw [← weilContinuation_eq_poleBoundary hv hW hs hne]
  exact re_weilContinuation_nonneg hW hs

/-- **The pole bound on the line**: `Re ζ(½+it) ≤ θ′(t) + 1 + Σ |v(n)| n^{−½}`. -/
theorem re_zeta_line_le (hv : BoundaryRegular v) (hW : WeilPositiveFull (poleSystem β v))
    (t : ℝ) :
    (riemannZeta (linePt t)).re ≤
      gammaHardyPhaseRate t + 1 + ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ := by
  have h := re_poleBoundary_line_nonneg hv hW t
  have hd := re_datum_add_inv_line t
  have hV : -(regSeries v (linePt t)).re ≤
      ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (WeilBoundaryDilation.norm_LSeries_linePt_le hv.summable t))
  unfold poleBoundary at h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at h
  rw [← Complex.add_re] at h
  linarith

/-- **ζ-type poles never produce Weil positivity.** For every `β` and every `v` with
`v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`, the system `β · [n ≥ 2] + v` is not full-cone
Weil-positive. -/
theorem not_weilPositiveFull_poleSystem (β : ℝ) {v : ℕ → ℝ} (hv : BoundaryRegular v) :
    ¬ WeilPositiveFull (poleSystem β v) := by
  intro hW
  set S := ∑' n, ‖LSeries.term (fun n => (v n : ℂ)) (1 / 2) n‖
  obtain ⟨t, ht1, ht⟩ := ZetaResonator.exists_log_add_lt_re_zeta (5 + S) 1
  have hle := re_zeta_line_le hv hW t
  have ht0 : 0 < t := by linarith
  have hb := gammaHardyPhaseRate_sub_log_conductor_bound ht0
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog2 : Real.log (t / (2 * Real.pi)) ≤ Real.log t :=
    Real.log_le_log (by positivity) (div_le_self ht0.le (by nlinarith [Real.pi_gt_three]))
  have herr : 33 / (16 * t ^ 2) + Real.pi / (2 * t) ≤ 4 := by
    have h1 : 33 / (16 * t ^ 2) ≤ 33 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : Real.pi / (2 * t) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_pos]
    linarith [Real.pi_lt_d2]
  have hθ : gammaHardyPhaseRate t ≤ Real.log t + 4 := by
    linarith [(abs_le.mp hb).2]
  linarith

end RHTower.WeilZetaPole
