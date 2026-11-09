import GaloisForLFunctions.ExceptionalLayerTheory.ZeroFreeBoundsForDampingFilters
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane

/-!
# Positive-strip contours for finite divisor filters

Shifting the complete prime integral within the positive Mellin strip crosses
the exceptional zeta divisor without introducing a Gamma pole. The filter
retains its full spacing factor in the remaining vertical integral.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_logDeriv_line_abs (x v : ℝ) :
    ‖logDeriv riemannZeta ((x : ℂ) + v * I)‖ =
      ‖logDeriv riemannZeta ((x : ℂ) + ((|v| : ℝ) : ℂ) * I)‖ := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · have he : (x : ℂ) + v * I =
        (starRingEnd ℂ) ((x : ℂ) + ((|v| : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [abs_of_neg (lt_of_not_ge hv)]
    rw [he, logDeriv_riemannZeta_conj, Complex.norm_conj]

/-- Above a finite exceptional packet, a horizontal gap gives polynomial
control of the actual logarithmic derivative across the whole strip. -/
theorem finite_layer_high_strip_logDeriv_bounds (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 1 / 2 ≤ c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ H C : ℝ, 4 ≤ H ∧ 0 < C ∧ ∀ x v : ℝ,
      c ≤ x → x ≤ 2 → H ≤ |v| →
      riemannZeta ((x : ℂ) + v * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((x : ℂ) + v * I)‖ ≤ C * (1 + |v|) := by
  classical
  let δ := min (c - θ) 1
  let M := ∑ q ∈ F, |(xiZero q).im|
  let H := M + δ + 4
  have hδ : 0 < δ := lt_min (sub_pos.mpr hgap) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hH : 4 ≤ H := by dsimp only [H]; linarith only [hM, hδ]
  have hsep : ∀ x v : ℝ, c ≤ x → H ≤ |v| → ∀ q : XiZeroCopy,
      δ ≤ ‖((x : ℂ) + v * I) - xiZero q‖ := by
    intro x v hx hv q
    by_cases hq : q ∈ F
    · have hqi : |(xiZero q).im| ≤ M :=
        Finset.single_le_sum (fun p _ => abs_nonneg (xiZero p).im) hq
      have hn := Complex.abs_im_le_norm (((x : ℂ) + v * I) - xiZero q)
      have he : (((x : ℂ) + v * I) - xiZero q).im = v - (xiZero q).im := by simp
      rw [he] at hn
      have ha := abs_add_le (v - (xiZero q).im) (xiZero q).im
      rw [sub_add_cancel] at ha
      dsimp only [H] at hv
      linarith only [ha, hn, hv, hqi]
    · have hn := Complex.re_le_norm (((x : ℂ) + v * I) - xiZero q)
      have he : (((x : ℂ) + v * I) - xiZero q).re = x - (xiZero q).re := by simp
      rw [he] at hn
      have hd : δ ≤ c - θ := min_le_left _ _
      linarith only [hn, hd, hx, hrest q hq]
  let C := logDerivZetaConstant / δ + 1
  have hbase : 0 ≤ logDerivZetaConstant / δ := by
    unfold logDerivZetaConstant
    positivity
  have hC : 0 < C := by dsimp only [C]; linarith only [hbase]
  refine ⟨H, C, hH, hC, ?_⟩
  intro x v hx hx2 hv
  have hv4 : 4 ≤ |v| := hH.trans hv
  have hx0 : 0 < x := by linarith only [hc, hx]
  have hs1 : (x : ℂ) + v * I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add, Complex.one_im] at hi
    rw [hi, abs_zero] at hv4
    linarith only [hv4]
  have hs0 : (x : ℂ) + v * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hx0, hh]
  have hz : riemannZeta ((x : ℂ) + v * I) ≠ 0 := by
    intro hz
    have hxi : xi ((x : ℂ) + v * I) = 0 := by
      rw [xi_eq_xiUnit_mul_zeta hs0 hs1 (by simpa using hx0), hz, mul_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hh := hsep x v hx hv q
    change δ ≤ ‖((x : ℂ) + v * I) - (q.1 : ℂ)‖ at hh
    rw [hq, sub_self, norm_zero] at hh
    exact (not_le_of_gt hδ) hh
  refine ⟨hz, ?_⟩
  have hb := norm_logDeriv_zeta_le (hc.trans hx) hx2 hv4 hδ hδ1
    (fun q => by
      change δ ≤ ‖((x : ℂ) + (|v| : ℝ) * I) - xiZero q‖
      exact hsep x |v| hx (by simpa only [abs_abs] using hv) q)
  rw [norm_logDeriv_line_abs]
  calc
    _ ≤ (logDerivZetaConstant / δ) * Real.log |v| := by convert hb using 1; ring
    _ ≤ (logDerivZetaConstant / δ) * (1 + |v|) :=
      mul_le_mul_of_nonneg_left (by linarith only [Real.log_le_self (abs_nonneg v)]) hbase
    _ ≤ C * (1 + |v|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C]
      linarith

/-- A line between the complementary divisor and the exceptional abscissae
is globally zero-free, including its bounded-height segment. -/
theorem finite_layer_regular_line_zeta_ne_zero (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 0 < c) (hc1 : c < 1) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) (v : ℝ) :
    riemannZeta ((c : ℂ) + v * I) ≠ 0 := by
  have hs0 : (c : ℂ) + v * I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hc, hh]
  have hs1 : (c : ℂ) + v * I ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith only [hc1, hh]
  intro hz
  have hxi : xi ((c : ℂ) + v * I) = 0 := by
    rw [xi_eq_xiUnit_mul_zeta hs0 hs1 (by simpa using hc), hz, mul_zero]
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hre : (xiZero q).re = c := by
    change (q.1 : ℂ).re = c
    rw [hq]
    simp
  by_cases hqF : q ∈ F
  · exact havoid q hqF hre.symm
  · linarith only [hrest q hqF, hre, hgap]

/-- The actual logarithmic derivative has polynomial growth on a globally
regular line above the complementary divisor. -/
theorem exists_finite_layer_regular_line_logDeriv_bound (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) :
    ∃ E : ℝ, 0 < E ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((c : ℂ) + v * I)‖ ≤ E * (1 + |v|) := by
  obtain ⟨H, C, _, hC, hb⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  have hc0 : 0 < c := by linarith only [hc]
  have hnz := finite_layer_regular_line_zeta_ne_zero F hc0 hc1 hgap hrest havoid
  have hcont : Continuous (fun v : ℝ => logDeriv riemannZeta ((c : ℂ) + v * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hs1 : (c : ℂ) + v * I ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      linarith only [hc1, hh]
    have ha := analyticOn_riemannZeta ((c : ℂ) + v * I) hs1
    have hld : ContinuousAt (logDeriv riemannZeta) ((c : ℂ) + v * I) := by
      change ContinuousAt (fun z => deriv riemannZeta z / riemannZeta z) _
      exact ha.deriv.continuousAt.div ha.continuousAt (hnz v)
    exact hld.comp (f := fun v : ℝ => (c : ℂ) + v * I) (by fun_prop)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-H) H) hcont.continuousOn
  let E := |B| + C + 1
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨E, hE, fun v => ?_⟩
  by_cases hv : |v| ≤ H
  · have hvI : v ∈ Icc (-H) H := abs_le.mp hv
    calc
      _ ≤ B := hB v hvI
      _ ≤ E := by dsimp only [E]; linarith only [le_abs_self B, hC]
      _ ≤ E * (1 + |v|) := le_mul_of_one_le_right hE.le (by linarith only [abs_nonneg v])
  · have hv' : H ≤ |v| := (lt_of_not_ge hv).le
    refine (hb c v le_rfl (by linarith only [hc1]) hv').2.trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [E]
    linarith only [abs_nonneg B]

/-- The pole and every enclosed zero contribute their exact weighted residues.
The weight need only be analytic near the rectangle. -/
theorem rectIntegral_weighted_neg_logDeriv_zeta
    {g : ℂ → ℂ} {z₁ z₂ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hg : AnalyticOnNhd ℂ g U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hre1 : z₁.re < 1) (hre2 : 1 < z₂.re)
    (him1 : z₁.im < 0) (him2 : 0 < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + v * I) ≠ 0)
    (hleft : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + v * I) ≠ 0) :
    rectIntegral (fun z => g z * (-logDeriv riemannZeta z)) z₁ z₂ =
      2 * Real.pi * I * (g 1 -
        ∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) := by
  let S : Set ℂ := {z | z ∈ U ∧ z ≠ 1 ∧ zetaResidueUnit z ≠ 0}
  have hb : ∀ x ∈ uIcc z₁.re z₂.re, (x : ℂ) + z₁.im * I ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr ⟨by simpa using hx,
      by simp⟩), ?_, hbot x hx⟩
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith only [hi, him1]
  have ht : ∀ x ∈ uIcc z₁.re z₂.re, (x : ℂ) + z₂.im * I ∈ S := by
    intro x hx
    refine ⟨hsub (Complex.mem_reProdIm.mpr ⟨by simpa using hx,
      by simp⟩), ?_, htop x hx⟩
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith only [hi, him2]
  have hr : ∀ v ∈ uIcc z₁.im z₂.im, (z₂.re : ℂ) + v * I ∈ S := by
    intro v hv
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by simp,
        by simpa using hv⟩), ?_, hright v hv⟩
    intro he
    have hi := congrArg Complex.re he
    simp at hi
    linarith only [hi, hre2]
  have hl : ∀ v ∈ uIcc z₁.im z₂.im, (z₁.re : ℂ) + v * I ∈ S := by
    intro v hv
    refine ⟨hsub (Complex.mem_reProdIm.mpr
      ⟨by simp,
        by simpa using hv⟩), ?_, hleft v hv⟩
    intro he
    have hi := congrArg Complex.re he
    simp at hi
    linarith only [hi, hre1]
  have hid : ∀ z ∈ S, g z * (-logDeriv riemannZeta z) =
      g z * (z - 1)⁻¹ + g z * Sieve.zetaLogDerivReg z := by
    intro z hz
    rw [Sieve.neg_logDeriv_riemannZeta_eq hz.2.1 hz.2.2, mul_add]
  have IIp : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, pt u ∈ S) →
      IntervalIntegrable (fun u => g (pt u) * (pt u - 1)⁻¹) volume c d := by
    intro c d pt hpt hm
    exact ((hg.continuousOn.comp hpt.continuousOn (fun u hu => (hm u hu).1)).mul
      ((hpt.continuousOn.sub continuousOn_const).inv₀
        (fun u hu => sub_ne_zero.mpr (hm u hu).2.1))).intervalIntegrable
  have IIr : ∀ {c d : ℝ} (pt : ℝ → ℂ), Continuous pt →
      (∀ u ∈ uIcc c d, pt u ∈ S) →
      IntervalIntegrable (fun u => g (pt u) * Sieve.zetaLogDerivReg (pt u))
        volume c d := by
    intro c d pt hpt hm
    apply ContinuousOn.intervalIntegrable
    intro u hu
    exact (((hg (pt u) (hm u hu).1).continuousAt.mul
      (Sieve.differentiableAt_zetaLogDerivReg (hm u hu).2.2).continuousAt).comp
        (hpt.continuousAt)).continuousWithinAt
  rw [rectIntegral_congr hid hb ht hr hl,
    rectIntegral_add
      (IIp _ (by fun_prop) hb) (IIr _ (by fun_prop) hb)
      (IIp _ (by fun_prop) ht) (IIr _ (by fun_prop) ht)
      (IIp _ (by fun_prop) hr) (IIr _ (by fun_prop) hr)
      (IIp _ (by fun_prop) hl) (IIr _ (by fun_prop) hl),
    rectIntegral_cauchyFormula_of_analyticOnNhd hg hsub
      (by simpa using hre1) (by simpa using hre2)
      (by simpa using him1) (by simpa using him2),
    Sieve.rectIntegral_mul_zetaLogDerivReg_eq_neg_closedRectangleZeroSum
      hU hg hsub (hre1.trans hre2) (him1.trans him2) hbot htop hright hleft]
  ring

/-- The complete polynomial weight in the zeta variable. Its Mellin argument
stays right of all Gamma poles when `σ < z.re`. -/
def divisorFilteredMellinWeight (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y t : ℝ) (z : ℂ) : ℂ :=
  (divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (z - β))) *
    gaussianMBKernel y (z - ((σ : ℂ) + t * I))

theorem analyticOnNhd_divisorFilteredMellinWeight (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h t : ℝ) {y : ℝ} (hy : 0 < y) :
    AnalyticOnNhd ℂ (divisorFilteredMellinWeight F ρ σ β h y t)
      {z : ℂ | σ < z.re} := by
  have hd : DifferentiableOn ℂ (divisorFilteredMellinWeight F ρ σ β h y t)
      {z : ℂ | σ < z.re} := by
    intro z hz
    let w := z - ((σ : ℂ) + t * I)
    have hw : 0 < w.re := by
      change σ < z.re at hz
      dsimp only [w]
      simpa using sub_pos.mpr hz
    have hΓ : DifferentiableAt ℂ Complex.Gamma (w / 2) := by
      apply Complex.differentiableAt_Gamma
      intro m hm
      have he := congrArg Complex.re hm
      simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at he
      linarith only [hw, he, Nat.cast_nonneg (α := ℝ) m]
    have hK : DifferentiableAt ℂ (gaussianMBKernel y) w := by
      unfold gaussianMBKernel
      exact ((hΓ.comp w (differentiableAt_id.div_const 2)).const_mul (1 / 2)).mul
        ((differentiableAt_id.div_const 2).neg.const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne')))
    have hP : DifferentiableAt ℂ (fun z : ℂ =>
        (divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (z - β)))) z :=
      (divisorDampingFilter F ρ β h).differentiable.differentiableAt.comp z
        ((differentiableAt_id.sub_const (β : ℂ)).const_mul (h : ℂ)).cexp
    exact (hP.mul (hK.comp z (differentiableAt_id.sub_const _))).differentiableWithinAt
  intro z hz
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

/-- Every residue-unit zero right of the complementary divisor occurs in the
actual finite exceptional packet. -/
theorem finite_layer_residueUnit_zero_mem (F : Finset XiZeroCopy)
    {θ c : ℝ} (hc : 0 < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    {w : ℂ} (hw : c ≤ w.re) (hG : zetaResidueUnit w = 0) :
    ∃ q ∈ F, xiZero q = w := by
  have hwpos : 0 < w.re := hc.trans_le hw
  have hw0 : w ≠ 0 := by intro he; simp [he] at hwpos
  have hw1 : w ≠ 1 := by intro he; simp [he, zetaResidueUnit_one] at hG
  have hz : riemannZeta w = 0 := by
    by_contra hn
    exact ((Sieve.zetaResidueUnit_ne_zero_iff hw1).2 hn) hG
  have hxi : xi w = 0 := by
    rw [xi_eq_xiUnit_mul_zeta hw0 hw1 hwpos, hz, mul_zero]
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hqw : xiZero q = w := hq
  refine ⟨q, ?_, hqw⟩
  by_contra hqF
  have hh := hrest q hqF
  rw [hqw] at hh
  linarith only [hh, hw, hgap]

private theorem exists_filtered_regular_line_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β c : ℝ) (hc1 : c ≠ 1) (hσc : σ < c)
    (hnz : ∀ v : ℝ, riemannZeta ((c : ℂ) + v * I) ≠ 0)
    (hbound : ∃ E : ℝ, 0 < E ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((c : ℂ) + v * I)‖ ≤ E * (1 + |v|)) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h t : ℝ, 0 < y → 0 ≤ h → h ≤ 1 →
      let Q := fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          gaussianMBKernel y (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
      Integrable Q ∧ ‖∫ v : ℝ, Q v‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            y ^ (-(c - σ) / 2) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  let δ := c - σ
  have hδ : 0 < δ := sub_pos.mpr hσc
  obtain ⟨B, hB, hfilter⟩ := exists_divisorDampingFilter_euler_bound F ρ β c
  obtain ⟨E, hE, hlog⟩ := hbound
  let W : ℝ → ℝ := fun v =>
    ‖gaussianMBKernel 1 ((δ : ℂ) + v * I)‖ * (1 + |v|) ^ (d + 1)
  have hWi : Integrable W :=
    integrable_norm_gaussianMBKernel_mul_pow zero_lt_one hδ (d + 1)
  let J := ∫ v : ℝ, W v
  have hJ : 0 ≤ J := integral_nonneg fun v => by dsimp only [W]; positivity
  let C₀ := B ^ d * E * J
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro y h t hy hh hh1
  dsimp only
  let Q : ℝ → ℂ := fun v =>
    (divisorDampingFilter F ρ β h).eval
      (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
        gaussianMBKernel y ((δ : ℂ) + v * I) *
          (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
  let Z := h ^ d * (1 + |t|) ^ (d + 1) * y ^ (-δ / 2)
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hpoint (v : ℝ) : ‖Q v‖ ≤ (B ^ d * E * Z) * W v := by
    have hl : ‖logDeriv riemannZeta ((c : ℂ) + (t + v) * I)‖ ≤
        E * (1 + |t|) * (1 + |v|) := by
      have htv : 1 + |t + v| ≤ (1 + |t|) * (1 + |v|) := by
        nlinarith only [abs_add_le t v, mul_nonneg (abs_nonneg t) (abs_nonneg v)]
      have hhlog := hlog (t + v)
      push_cast at hhlog
      exact hhlog.trans (by nlinarith only [htv, hE])
    have hK : ‖gaussianMBKernel y ((δ : ℂ) + v * I)‖ =
        y ^ (-δ / 2) * ‖gaussianMBKernel 1 ((δ : ℂ) + v * I)‖ := by
      rw [norm_gaussianMBKernel_line hy, norm_gaussianMBKernel_line zero_lt_one,
        Real.one_rpow, mul_one]
      rw [show -(δ / 2) = -δ / 2 by ring]
      ring
    dsimp only [Q]
    rw [norm_mul, norm_mul, norm_neg]
    calc
      _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
          ‖gaussianMBKernel y ((δ : ℂ) + v * I)‖ *
            (E * (1 + |t|) * (1 + |v|)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (hfilter h t v hh hh1) (norm_nonneg _)
        · exact hl
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        rw [hK]
        dsimp only [W, Z]
        simp only [mul_pow, pow_succ]
        ring
  have hlogcont : Continuous (fun u : ℝ => logDeriv riemannZeta ((c : ℂ) + u * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hs1 : (c : ℂ) + u * I ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      exact hc1 hh
    have ha := analyticOn_riemannZeta ((c : ℂ) + u * I) hs1
    have hd : ContinuousAt (logDeriv riemannZeta) ((c : ℂ) + u * I) :=
      ha.deriv.continuousAt.div ha.continuousAt (hnz u)
    exact hd.comp (f := fun u : ℝ => (c : ℂ) + u * I) (by fun_prop)
  have hcont : Continuous Q := by
    have hp : Continuous (fun v : ℝ => (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β)))) := by
      simp_rw [Polynomial.eval_eq_sum_range]
      fun_prop
    have hl : Continuous (fun v : ℝ => -logDeriv riemannZeta ((c : ℂ) + (t + v) * I)) := by
      have hcc := (hlogcont.comp (show Continuous (fun v : ℝ => t + v) by fun_prop)).neg
      change Continuous (fun v : ℝ =>
        -logDeriv riemannZeta ((c : ℂ) + ((t + v : ℝ) : ℂ) * I)) at hcc
      simpa only [Complex.ofReal_add] using hcc
    exact (hp.mul (continuous_gaussianMBKernel_line hy hδ)).mul hl
  have hQi : Integrable Q :=
    (hWi.const_mul (B ^ d * E * Z)).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hpoint)
  refine ⟨hQi, ?_⟩
  have hnorm : ‖∫ v : ℝ, Q v‖ ≤ C₀ * Z := by
    calc
      _ ≤ ∫ v : ℝ, ‖Q v‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (B ^ d * E * Z) * W v :=
        integral_mono hQi.norm (hWi.const_mul _) hpoint
      _ = _ := by rw [integral_const_mul]; dsimp only [C₀, J]; ring
  refine hnorm.trans ?_
  have he : d + 1 = 2 + (F.filter (fun q => xiZero q ≠ ρ)).card := by dsimp only [d]; omega
  calc
    C₀ * Z ≤ (C₀ + 1) * Z :=
      mul_le_mul_of_nonneg_right (by linarith) hZ
    _ = _ := by dsimp only [Z, δ]; rw [he]; ring

/-- The shifted integral keeps every spacing factor, uniformly as the damping
spacing tends to zero. The logarithmic derivative costs one height power. -/
theorem exists_finite_layer_filtered_line_bound (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β : ℝ) {θ c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1)
    (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h t : ℝ, 0 < y → 0 ≤ h → h ≤ 1 →
      let Q := fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          gaussianMBKernel y (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
      Integrable Q ∧ ‖∫ v : ℝ, Q v‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            y ^ (-(c - σ) / 2) :=
  exists_filtered_regular_line_bound F ρ σ β c hc1.ne hσc
    (finite_layer_regular_line_zeta_ne_zero F (by linarith only [hc]) hc1 hgap hrest havoid)
    (exists_finite_layer_regular_line_logDeriv_bound F hc hc1 hgap hrest havoid)

/-- A sufficiently tall positive-strip rectangle extracts exactly the selected
zero. Pole cancellation and unwanted-zero cancellation are exact. -/
theorem finite_layer_divisorFilter_rectangle (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h t : ℝ) {θ c y : ℝ} (hy : 0 < y)
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ H : ℝ, 0 < H ∧ ∀ T : ℝ, H ≤ T →
      rectIntegral (fun z => divisorFilteredMellinWeight F ρ σ β h y t z *
        (-logDeriv riemannZeta z)) ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I) =
      -(2 * Real.pi * I * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h y t ρ) := by
  classical
  obtain ⟨H, C, hH, _, hb⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  have hc0 : 0 < c := by linarith only [hc]
  refine ⟨H + |ρ.im| + 1, by linarith only [hH, abs_nonneg ρ.im], ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith only [hH, abs_nonneg ρ.im, hT]
  have hTH : H ≤ T := by linarith only [hT, abs_nonneg ρ.im]
  have hρT : |ρ.im| < T := by linarith only [hT, hH]
  let z₁ : ℂ := (c : ℂ) + (-T : ℝ) * I
  let z₂ : ℂ := (2 : ℂ) + T * I
  let g := divisorFilteredMellinWeight F ρ σ β h y t
  let U : Set ℂ := {z | σ < z.re}
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro z hz
    have hh := (Complex.mem_reProdIm.mp hz).1
    have hc2 : c ≤ 2 := by linarith only [hc1]
    have hzI : z.re ∈ Icc c 2 := by simpa [z₁, z₂, uIcc_of_le hc2] using hh
    have hzre : c ≤ z.re := hzI.1
    exact hσc.trans_le hzre
  have hedge : ∀ x v : ℝ, c ≤ x → x ≤ 2 → H ≤ |v| → v ≠ 0 →
      zetaResidueUnit ((x : ℂ) + v * I) ≠ 0 := by
    intro x v hx hx2 hv hv0
    apply (Sieve.zetaResidueUnit_ne_zero_iff ?_).2 (hb x v hx hx2 hv).1
    intro he
    apply hv0
    simpa using congrArg Complex.im he
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c 2 := by
      simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hx
    simpa [z₁] using hedge x (-T) hx'.1 hx'.2
      (by simpa [abs_of_pos hT0] using hTH) (neg_ne_zero.mpr hT0.ne')
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c 2 := by
      simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hx
    simpa [z₂] using hedge x T hx'.1 hx'.2
      (by simpa [abs_of_pos hT0] using hTH) hT0.ne'
  have hright : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₂.re : ℂ) + v * I) ≠ 0 := by
    intro v _
    have hs1 : (2 : ℂ) + v * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      norm_num at hr
    simpa [z₂] using (Sieve.zetaResidueUnit_ne_zero_iff hs1).2
      (riemannZeta_ne_zero_of_one_lt_re (by simp))
  have hleft : ∀ v ∈ uIcc z₁.im z₂.im,
      zetaResidueUnit ((z₁.re : ℂ) + v * I) ≠ 0 := by
    intro v _
    have hs1 : (c : ℂ) + v * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith only [hr, hc1]
    simpa [z₁] using (Sieve.zetaResidueUnit_ne_zero_iff hs1).2
      (finite_layer_regular_line_zeta_ne_zero F hc0 hc1 hgap hrest havoid v)
  have hρG : zetaResidueUnit ρ = 0 := by
    have hz := (xi_zero_iff_zeta_zero_of_mem_strip (hc0.trans hρc) hρ1).1 hρ
    by_contra hn
    have hr1 : ρ ≠ 1 := by intro he; simp [he] at hρ1
    exact ((Sieve.zetaResidueUnit_ne_zero_iff hr1).1 hn) hz
  have hρmem : ρ ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂ := by
    apply Sieve.mem_zetaResidueUnitClosedRectangleZeros.mpr
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hρG⟩
    · simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using
        (show ρ.re ∈ Icc c 2 from ⟨hρc.le, by linarith only [hρ1]⟩)
    · simpa [z₁, z₂, uIcc_of_le (show -T ≤ T by linarith only [hT0])] using
        (show ρ.im ∈ Icc (-T) T from abs_le.mp hρT.le)
  have hsum : (∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) =
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) * g ρ := by
    apply Finset.sum_eq_single ρ
    · intro w hw hne
      obtain ⟨hwK, hwG⟩ := Sieve.mem_zetaResidueUnitClosedRectangleZeros.mp hw
      have hwre := (Complex.mem_reProdIm.mp hwK).1
      have hwc : c ≤ w.re := by
        have hwI : w.re ∈ Icc c 2 := by
          simpa [z₁, z₂, uIcc_of_le (show c ≤ 2 by linarith only [hc1])] using hwre
        exact hwI.1
      obtain ⟨q, hqF, hqw⟩ := finite_layer_residueUnit_zero_mem F hc0 hgap hrest hwc hwG
      have hkill := divisorDampingFilter_kills F ρ β h hqF (by simpa [hqw] using hne)
      rw [hqw] at hkill
      simp only [g, divisorFilteredMellinWeight, hkill, zero_mul, mul_zero]
    · exact fun hnot => (hnot hρmem).elim
  have hpole : g 1 = 0 := by
    dsimp only [g, divisorFilteredMellinWeight]
    rw [divisorDampingFilter_pole, zero_mul]
  have hid := rectIntegral_weighted_neg_logDeriv_zeta
    (isOpen_lt continuous_const Complex.continuous_re)
    (analyticOnNhd_divisorFilteredMellinWeight F ρ σ β h t hy) hsub
    (by simpa [z₁] using hc1) (by simp [z₂])
    (by simpa [z₁] using neg_neg_of_pos hT0) (by simpa [z₂] using hT0)
    hbot htop hright hleft
  change rectIntegral (fun z => g z * (-logDeriv riemannZeta z)) z₁ z₂ = _
  rw [hid]
  change 2 * Real.pi * I * (g 1 -
    ∑ w ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * g w) = _
  rw [hpole, hsum]
  ring

/-- Horizontal edges of the complete filtered contour vanish at both ends
of the finite exceptional packet. -/
theorem tendsto_finite_layer_divisorFilter_horizontal (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h t e : ℝ) {θ c y : ℝ} (hy : 0 < y)
    (hc : 1 / 2 ≤ c) (hc2 : c ≤ 2) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (he : |e| = 1) :
    Tendsto (fun T : ℝ => ∫ x in c..2,
      divisorFilteredMellinWeight F ρ σ β h y t ((x : ℂ) + (e * T) * I) *
        (-logDeriv riemannZeta ((x : ℂ) + (e * T) * I))) atTop (𝓝 0) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨H, E, hH, hE, hlog⟩ := finite_layer_high_strip_logDeriv_bounds F hc hgap hrest
  obtain ⟨A, hA, hkernel⟩ := exists_divisorFilter_kernel_strip_envelope
    F ρ σ β (c - σ) (2 - σ) (sub_pos.mpr hσc)
  let Y := Real.exp (|Real.log y| * ((2 - σ) / 2))
  let D := A * h ^ d * (1 + |t|) ^ d * Y * E * Real.exp (|t| / 2)
  have hD : 0 ≤ D := by dsimp only [D, Y]; positivity
  have hpt (x v : ℝ) (hx : c ≤ x) (hx2 : x ≤ 2) (hv : H ≤ |v|) :
      ‖divisorFilteredMellinWeight F ρ σ β h y t ((x : ℂ) + v * I) *
        (-logDeriv riemannZeta ((x : ℂ) + v * I))‖ ≤
        D * (1 + |v|) * Real.exp (-(|v| / 2)) := by
    have hxs : 0 < x - σ := sub_pos.mpr (hσc.trans_le hx)
    have hk := hkernel y h t (x - σ) (v - t) hy hh hh1
      (by linarith only [hx]) (by linarith only [hx2])
    have hsum : ((σ : ℂ) + t * I) + (((x - σ : ℝ) : ℂ) + ((v - t : ℝ) : ℂ) * I) =
        (x : ℂ) + v * I := by push_cast; ring
    have hdiff : (x : ℂ) + v * I - ((σ : ℂ) + t * I) =
        ((x - σ : ℝ) : ℂ) + ((v - t : ℝ) : ℂ) * I := by push_cast; ring
    have hk' : ‖divisorFilteredMellinWeight F ρ σ β h y t ((x : ℂ) + v * I)‖ ≤
        A * h ^ d * (1 + |t|) ^ d * y ^ (-((x - σ) / 2)) *
          Real.exp (-(|v - t| / 2)) := by
      simpa only [divisorFilteredMellinWeight, hsum, hdiff, d] using hk
    have hyb : y ^ (-((x - σ) / 2)) ≤ Y := by
      rw [Real.rpow_def_of_pos hy]
      apply Real.exp_le_exp.mpr
      have hn := neg_le_abs (Real.log y)
      have hnon := abs_nonneg (Real.log y)
      nlinarith only [hn, hnon, hxs, hx2]
    have hve : Real.exp (-(|v - t| / 2)) ≤
        Real.exp (|t| / 2) * Real.exp (-(|v| / 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hvabs := abs_add_le (v - t) t
      rw [sub_add_cancel] at hvabs
      linarith only [hvabs]
    rw [norm_mul, norm_neg]
    calc
      _ ≤ (A * h ^ d * (1 + |t|) ^ d * Y *
          (Real.exp (|t| / 2) * Real.exp (-(|v| / 2)))) * (E * (1 + |v|)) := by
        apply mul_le_mul
        · exact hk'.trans (by gcongr)
        · exact (hlog x v hx hx2 hv).2
        · exact norm_nonneg _
        · positivity
      _ = _ := by dsimp only [D]; ring
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := 2 * D * (2 - c)) (N := 1) (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [eventually_ge_atTop H] with T hT
  have hT1 : 1 ≤ T := by linarith only [hT, hH]
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  have heT : |e * T| = T := by rw [abs_mul, he, one_mul, abs_of_nonneg hT0]
  have hb : ∀ x ∈ uIoc c 2,
      ‖divisorFilteredMellinWeight F ρ σ β h y t ((x : ℂ) + (e * T) * I) *
        (-logDeriv riemannZeta ((x : ℂ) + (e * T) * I))‖ ≤
        D * (1 + T) * Real.exp (-(T / 2)) := by
    intro x hx
    rw [uIoc_of_le hc2] at hx
    have hv : H ≤ |e * T| := by rwa [heT]
    simpa only [Complex.ofReal_mul, heT] using hpt x (e * T) hx.1.le hx.2 hv
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr hc2)] at hi
  refine hi.trans ?_
  have ht : 1 + T ≤ 2 * T := by linarith only [hT1]
  calc
    D * (1 + T) * Real.exp (-(T / 2)) * (2 - c) ≤
        D * (2 * T) * Real.exp (-(T / 2)) * (2 - c) := by gcongr
    _ = _ := by
      rw [show -(T / 2) = -((1 / 2 : ℝ) * T) by ring]
      simp only [pow_one]
      ring

private theorem divisorFilteredMellinWeight_shift (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y t c v : ℝ) :
    divisorFilteredMellinWeight F ρ σ β h y t ((c : ℂ) + (t + v) * I) =
      (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          gaussianMBKernel y (((c - σ : ℝ) : ℂ) + v * I) := by
  unfold divisorFilteredMellinWeight
  congr 2
  push_cast
  ring

private theorem integrable_filtered_line_of_shifted (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h y t c : ℝ)
    (hi : Integrable (fun v : ℝ =>
      (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
          gaussianMBKernel y (((c - σ : ℝ) : ℂ) + v * I) *
            (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I)))) :
    Integrable (fun v : ℝ => divisorFilteredMellinWeight F ρ σ β h y t
      ((c : ℂ) + v * I) * (-logDeriv riemannZeta ((c : ℂ) + v * I))) := by
  have his : Integrable (fun v : ℝ => divisorFilteredMellinWeight F ρ σ β h y t
      ((c : ℂ) + (t + v) * I) * (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))) := by
    simpa only [divisorFilteredMellinWeight_shift] using hi
  convert his.comp_add_right (-t) using 1
  funext v
  simp only [Complex.ofReal_add, Complex.ofReal_neg]
  have he : (t : ℂ) + (v + -t) = v := by ring
  rw [he]

private theorem filtered_euler_line_integrable (F : Finset XiZeroCopy) (ρ : ℂ)
    (σ β h t : ℝ) {y : ℝ} (hy : 0 < y) (hσ : σ < 2)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    Integrable (fun v : ℝ => divisorFilteredMellinWeight F ρ σ β h y t
      ((2 : ℂ) + v * I) * (-logDeriv riemannZeta ((2 : ℂ) + v * I))) := by
  let E : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 : ℝ)
  have hE : 0 ≤ E := tsum_nonneg fun n => div_nonneg
    ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hb : ∃ B : ℝ, 0 < B ∧ ∀ v : ℝ,
      ‖logDeriv riemannZeta ((2 : ℂ) + v * I)‖ ≤ B * (1 + |v|) := by
    refine ⟨E + 1, by positivity, fun v => ?_⟩
    have hn := norm_LSeries_vonMangoldt_le (s := (2 : ℂ) + v * I) (by simp)
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp),
      neg_div, ← logDeriv_apply, norm_neg] at hn
    have hn' : ‖logDeriv riemannZeta ((2 : ℂ) + v * I)‖ ≤ E := by simpa [E] using hn
    exact hn'.trans (by nlinarith only [hE, abs_nonneg v, mul_nonneg hE (abs_nonneg v)])
  obtain ⟨C, _, hC⟩ := exists_filtered_regular_line_bound F ρ σ β 2 (by norm_num) hσ
    (fun v => riemannZeta_ne_zero_of_one_lt_re (by simp)) hb
  exact integrable_filtered_line_of_shifted F ρ σ β h y t 2 (hC y h t hy hh hh1).1

/-- Shifting the full positive-strip contour leaves one exact exceptional
residue. No Gamma pole lies between the two vertical lines. -/
theorem finite_layer_divisorFilter_line_shift (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h t : ℝ) {θ c y : ℝ} (hy : 0 < y)
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ v : ℝ, divisorFilteredMellinWeight F ρ σ β h y t ((2 : ℂ) + v * I) *
        (-logDeriv riemannZeta ((2 : ℂ) + v * I))) -
      (∫ v : ℝ, divisorFilteredMellinWeight F ρ σ β h y t ((c : ℂ) + v * I) *
        (-logDeriv riemannZeta ((c : ℂ) + v * I))) =
      -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h y t ρ) := by
  let G : ℂ → ℂ := fun z => divisorFilteredMellinWeight F ρ σ β h y t z *
    (-logDeriv riemannZeta z)
  have hc2 : c ≤ 2 := by linarith only [hc1]
  have hir := filtered_euler_line_integrable F ρ σ β h t hy (hσc.trans_le hc2) hh hh1
  obtain ⟨C, _, hb⟩ := exists_finite_layer_filtered_line_bound F ρ σ β hc hc1
    hσc hgap hrest havoid
  have hil := integrable_filtered_line_of_shifted F ρ σ β h y t c (hb y h t hy hh hh1).1
  have hright := intervalIntegral_tendsto_integral hir tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral hil tendsto_neg_atTop_atBot tendsto_id
  have hbottom := tendsto_finite_layer_divisorFilter_horizontal F ρ σ β h t (-1)
    hy hc hc2 hσc hgap hrest hh hh1 (by norm_num)
  have htop := tendsto_finite_layer_divisorFilter_horizontal F ρ σ β h t 1
    hy hc hc2 hσc hgap hrest hh hh1 (by norm_num)
  have hlimit := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hlimit' : Tendsto (fun T : ℝ => rectIntegral G
      ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I)) atTop
      (𝓝 (I • (∫ v : ℝ, G ((2 : ℂ) + v * I)) -
        I • (∫ v : ℝ, G ((c : ℂ) + v * I)))) := by
    simpa only [rectIntegral, G, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_neg, Complex.neg_re, Complex.neg_im, Complex.ofNat_re,
      Complex.ofNat_im, mul_zero, zero_mul, sub_zero, mul_one, add_zero, zero_add,
      neg_one_mul, one_mul, zero_sub, zero_smul] using hlimit
  obtain ⟨H, _, hrect⟩ := finite_layer_divisorFilter_rectangle F ρ σ β h t hy
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ
  have hevent : (fun T : ℝ => rectIntegral G
      ((c : ℂ) + (-T : ℝ) * I) ((2 : ℂ) + T * I)) =ᶠ[atTop]
      (fun _ => -(2 * Real.pi * I * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h y t ρ)) := by
    filter_upwards [eventually_ge_atTop H] with T hT
    exact hrect T hT
  have hid := tendsto_nhds_unique (hlimit'.congr' hevent) tendsto_const_nhds
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    I * ((∫ v : ℝ, G ((2 : ℂ) + v * I)) - ∫ v : ℝ, G ((c : ℂ) + v * I)) =
        I • (∫ v : ℝ, G ((2 : ℂ) + v * I)) -
          I • (∫ v : ℝ, G ((c : ℂ) + v * I)) := by rw [mul_sub]; rfl
    _ = _ := hid
    _ = _ := by ring

/-- The literal prime filter equals the selected exceptional mode plus the
complete vertical integral on any regular positive Mellin line below it. -/
theorem primeDampingFilter_eq_selected_mode_add_line (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β a h t : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t =
      -((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) t ρ +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, divisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) t
          ((c : ℂ) + v * I) * (-logDeriv riemannZeta ((c : ℂ) + v * I)) := by
  let y := Real.exp (-a * t)
  let G : ℂ → ℂ := fun z => divisorFilteredMellinWeight F ρ σ β h y t z *
    (-logDeriv riemannZeta z)
  let k : ℝ := 1 / (2 * Real.pi)
  have hσ2 : σ < 2 := by linarith only [hσc, hc1]
  have hp : primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t =
      (k : ℂ) * ∫ v : ℝ, G ((2 : ℂ) + v * I) := by
    rw [primeDampingFilter_eq_euler_integral _ σ β a h t (2 - σ)
      (sub_pos.mpr hσ2) (by linarith)]
    have hfun : (fun v : ℝ =>
        (divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) * (((σ : ℂ) + t * I +
            (((2 - σ : ℝ) : ℂ) + v * I)) - β))) *
          gaussianMBKernel y (((2 - σ : ℝ) : ℂ) + v * I) *
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              ((σ : ℂ) + t * I + (((2 - σ : ℝ) : ℂ) + v * I))) =
        (fun v : ℝ => G ((2 : ℂ) + ((v + t : ℝ) : ℂ) * I)) := by
      funext v
      have hz : (σ : ℂ) + t * I + (((2 - σ : ℝ) : ℂ) + v * I) =
          (2 : ℂ) + (t + v) * I := by push_cast; ring
      have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((2 : ℂ) + (t + v) * I) = -logDeriv riemannZeta ((2 : ℂ) + (t + v) * I) := by
        rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp),
          logDeriv_apply, neg_div]
      rw [hz, he]
      have hvt : ((v + t : ℝ) : ℂ) = (t : ℂ) + v := by push_cast; ring
      rw [hvt]
      dsimp only [G]
      rw [divisorFilteredMellinWeight_shift]
    change (k : ℂ) * ∫ v : ℝ, _ = _
    rw [hfun, integral_add_right_eq_self (fun v : ℝ => G ((2 : ℂ) + v * I)) t]
  have hs := finite_layer_divisorFilter_line_shift F ρ σ β h t (Real.exp_pos (-a * t))
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ hh hh1
  change (∫ v : ℝ, G ((2 : ℂ) + v * I)) - (∫ v : ℝ, G ((c : ℂ) + v * I)) =
    -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      divisorFilteredMellinWeight F ρ σ β h y t ρ) at hs
  have hk : (k : ℂ) * (2 * Real.pi : ℂ) = 1 := by
    dsimp only [k]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hhprod := congrArg (fun z : ℂ => (k : ℂ) * z) hs
  rw [mul_sub] at hhprod
  have hm : (k : ℂ) * -(2 * Real.pi * ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
      divisorFilteredMellinWeight F ρ σ β h y t ρ) =
      -((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h y t ρ := by
    calc
      _ = -((k : ℂ) * (2 * Real.pi)) *
          (((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
            divisorFilteredMellinWeight F ρ σ β h y t ρ) := by ring
      _ = _ := by rw [hk]; ring
  rw [hm] at hhprod
  rw [hp]
  linear_combination hhprod

/-- The complete filtered error retains the full spacing order. Its growth
rate can be placed arbitrarily close to zero by moving the regular contour
toward the observation line. -/
theorem exists_primeDampingFilter_spacing_preserving_error_bound
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β : ℝ) {θ c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) (hσc : σ < c) (hgap : θ < c)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (havoid : ∀ q ∈ F, c ≠ (xiZero q).re)
    (hρc : c < ρ.re) (hρ1 : ρ.re < 1) (hρ : xi ρ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a h t : ℝ, 0 ≤ h → h ≤ 1 →
      ‖primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t +
        ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
          divisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) t ρ‖ ≤
        C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          (1 + |t|) ^ (2 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
            Real.exp (a * t * (c - σ) / 2) := by
  obtain ⟨B, hB, hb⟩ := exists_finite_layer_filtered_line_bound F ρ σ β
    hc hc1 hσc hgap hrest havoid
  let k : ℝ := 1 / (2 * Real.pi)
  have hk : 0 < k := by dsimp only [k]; positivity
  refine ⟨k * B, by positivity, ?_⟩
  intro a h t hh hh1
  let y := Real.exp (-a * t)
  let G : ℂ → ℂ := fun z => divisorFilteredMellinWeight F ρ σ β h y t z *
    (-logDeriv riemannZeta z)
  let Q : ℝ → ℂ := fun v =>
    (divisorDampingFilter F ρ β h).eval
      (Complex.exp ((h : ℂ) * ((c : ℂ) + (t + v) * I - β))) *
        gaussianMBKernel y (((c - σ : ℝ) : ℂ) + v * I) *
          (-logDeriv riemannZeta ((c : ℂ) + (t + v) * I))
  have htran : (∫ v : ℝ, G ((c : ℂ) + v * I)) = ∫ v : ℝ, Q v := by
    calc
      _ = ∫ v : ℝ, G ((c : ℂ) + ((v + t : ℝ) : ℂ) * I) :=
        (integral_add_right_eq_self (fun v : ℝ => G ((c : ℂ) + v * I)) t).symm
      _ = _ := by
        apply integral_congr_ae
        refine Eventually.of_forall fun v => ?_
        have hvt : ((v + t : ℝ) : ℂ) = (t : ℂ) + v := by push_cast; ring
        rw [hvt]
        dsimp only [G, Q]
        rw [divisorFilteredMellinWeight_shift]
  have heq := primeDampingFilter_eq_selected_mode_add_line F ρ σ β a h t
    hc hc1 hσc hgap hrest havoid hρc hρ1 hρ hh hh1
  have heq' : primeDampingFilter (divisorDampingFilter F ρ β h) σ β a h t +
      ((analyticOrderAt zetaResidueUnit ρ).toNat : ℂ) *
        divisorFilteredMellinWeight F ρ σ β h y t ρ =
      (k : ℂ) * ∫ v : ℝ, G ((c : ℂ) + v * I) := by
    change _ = _ at heq
    linear_combination heq
  rw [heq', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, htran]
  have hnorm := (hb y h t (Real.exp_pos _) hh hh1).2
  have hyexp : y ^ (-(c - σ) / 2) = Real.exp (a * t * (c - σ) / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hyexp] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm hk.le).trans_eq (by ring)

end GaloisForLFunctions.ExceptionalLayerTheory
