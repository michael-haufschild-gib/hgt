import GaloisForLFunctions.RHTower.RiemannKernelTruncationWeilPositive
import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure
import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaFarTail

/-!
# The exact order of the Weil energy of the truncated Riemann kernel

Let `E(L) = e^{9L/2}e^{−πe^{2L}}` and `Y = 2πe^{2L}`. For the truncation `Φχ_L` of Riemann's kernel
with an edge of width `1/Y`, there is `K` such that for all large `L`

`E(L)²/Y ≤ Re W(Φχ_L, Φχ_L) ≤ K E(L)²`   (`exists_twoSided_truncKernel_energy`),

unconditionally. So `log W(Φχ_L) = −2πe^{2L} + O(L)`: the energy of the canonical near-null
direction is `e^{−T_N}` up to factors `e^{O(L)}`, where `T_N = 2πe^{2L}` is the Nyquist height of
level `L`. Since `∫(Φχ_L)² ≥ 400E(1)²`, the even Weil ground energy at half-width `L + 1` is at most
`K' e^{9L} e^{−2πe^{2L}}`, which sharpens the exponent `πe^{2L−1/2}` of `zeta_weil_margin_superexponential`.

**Upper bound** (`re_W_edgeTail_le`). By the radical identity, `W(Φχ_L) = lim_R W(T_R)` for the edge
tails `T_R = Φ(χ_R − χ_L) ≥ 0`. In the explicit formula the prime term of `T_R` is nonnegative, so
`Re W(T_R) ≤ pole + arch`.
- The pole term is at most `2(∫T e^{|u|/2})²` (`re_pole_le`).
- For the archimedean term, `|γ(r)| ≤ C + |r|`, `|r| ≤ s/2 + r²/(2s)`, Plancherel and `(f')^ = −ir f̂`
  give `arch ≤ (C + s/2)∫|f|² + (1/(2s))∫|f'|²` (`re_arch_le`).
- The tail and its derivative are dominated by `e^{−c(|u|−L)}` envelopes, using the sharp logarithmic
  derivative `|Φ'| ≤ 2π(e^{2u} + 2)Φ`.

**Lower bound.** This is the explicit form of the edge-tail positivity
(`re_W_edgeTail_ge_narrow`, `edgePrimeBound_le_decay`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

local notation "st" => Real.smoothTransition

/-! ## The archimedean term from above -/

theorem exists_abs_gammaBracket_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |EF.gammaBracket r| ≤ C + |r| := by
  refine ⟨_, ?_, fun r => WeilSpectral.abs_gammaBracket_le r⟩
  have h := WeilSpectral.abs_gammaBracket_le 0
  rw [abs_zero, add_zero] at h
  exact (abs_nonneg _).trans h

/-- **Archimedean upper bound.** For a `C³` compactly supported test and every `s > 0`,
`arch ≤ (C + s/2)∫|f|² + (1/(2s))∫|f'|²` whenever `|γ(r)| ≤ C + |r|`. -/
theorem re_arch_le {f : ℝ → ℂ} (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) {a : ℝ}
    (hfs : tsupport f ⊆ Icc (-a) a) {C : ℝ} (hC : ∀ r : ℝ, |EF.gammaBracket r| ≤ C + |r|)
    {s : ℝ} (hs : 0 < s) :
    ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re ≤
      (C + s / 2) * (∫ u, ‖f u‖ ^ 2) + 1 / (2 * s) * ∫ u, ‖deriv f u‖ ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hdc : HasCompactSupport (deriv f) := hfc.deriv
  have hds : tsupport (deriv f) ⊆ Icc (-a) a := tsupport_deriv_subset.trans hfs
  set F : ℝ → ℝ := fun r => ‖paperFT f r‖ ^ 2 with hF
  set G : ℝ → ℝ := fun r => ‖paperFT (deriv f) r‖ ^ 2 with hG
  have hFint : Integrable F := integrable_normSq_paperFT hf2 hfs
  have hGint : Integrable G := integrable_normSq_paperFT hd hds
  -- `(f')^ = −ir f̂`
  have hFG : ∀ r : ℝ, G r = r ^ 2 * F r := fun r => by
    have hsd := superExpDecay_of_continuous_hasCompactSupport hf.continuous hfc
    have hsd' := superExpDecay_of_continuous_hasCompactSupport hd.continuous hdc
    have hder : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
      ((hf.differentiable (by norm_num)) x).hasDerivAt
    have h := paperFT_deriv_of_superExpDecay hsd hsd' hder (r : ℂ)
    simp only [hF, hG]
    rw [h, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have hFγ : Integrable (fun r => F r * EF.gammaBracket r) := by
    have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf2 hfc hf2 hfc
    have h2 : Integrable (fun r : ℝ =>
        (paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re) := h.re
    refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hF]
    rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hcomplex : ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r *
      (EF.gammaBracket r : ℂ)).re = (1 / (2 * π)) * ∫ r, F r * EF.gammaBracket r := by
    have : ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ) =
        ((∫ r, F r * EF.gammaBracket r : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1; funext r
      rw [paperFT_weilTest_self_eq_normSq hf.continuous hfc, ← Complex.ofReal_mul]
    rw [this, show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hcomplex]
  have hpt : ∀ r, F r * EF.gammaBracket r ≤ (C + s / 2) * F r + 1 / (2 * s) * G r := fun r => by
    have hF0 : 0 ≤ F r := sq_nonneg _
    have hγ : EF.gammaBracket r ≤ C + |r| := (le_abs_self _).trans (hC r)
    have hr : |r| ≤ s / 2 + r ^ 2 / (2 * s) := by
      rw [show s / 2 + r ^ 2 / (2 * s) = (s ^ 2 + r ^ 2) / (2 * s) by field_simp,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (s - |r|), sq_abs r]
    rw [hFG r]
    calc F r * EF.gammaBracket r ≤ F r * (C + |r|) := mul_le_mul_of_nonneg_left hγ hF0
      _ ≤ F r * (C + (s / 2 + r ^ 2 / (2 * s))) := by gcongr
      _ = _ := by ring
  have hrhs : Integrable (fun r => (C + s / 2) * F r + 1 / (2 * s) * G r) :=
    (hFint.const_mul _).add (hGint.const_mul _)
  have hmono := integral_mono hFγ hrhs hpt
  rw [integral_add (hFint.const_mul _) (hGint.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hpF := LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf2 hfc
  have hpG := LebesgueAtomWeil.integral_norm_sq_paperFT_eq hd hdc
  have hπ := Real.pi_pos
  have e1 : ∫ r, F r = 2 * π * ∫ u, ‖f u‖ ^ 2 := by
    rw [← hpF]; simp only [hF]; field_simp
  have e2 : ∫ r, G r = 2 * π * ∫ u, ‖deriv f u‖ ^ 2 := by
    rw [← hpG]; simp only [hG]; field_simp
  rw [e1, e2] at hmono
  calc 1 / (2 * π) * ∫ r, F r * EF.gammaBracket r
      ≤ 1 / (2 * π) * ((C + s / 2) * (2 * π * ∫ u, ‖f u‖ ^ 2) +
          1 / (2 * s) * (2 * π * ∫ u, ‖deriv f u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = _ := by field_simp

/-! ## The pole term from above -/

/-- The pole term of a nonnegative test is at most `2(∫ f e^{|u|/2})²`. -/
theorem re_pole_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ u, 0 ≤ f u) :
    (paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (I / 2) +
      paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (-I / 2)).re ≤
      2 * (∫ u, f u * Real.exp (|u| / 2)) ^ 2 := by
  have hc : Continuous (fun u => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hcc : HasCompactSupport (fun u => (f u : ℂ)) :=
    hfc.comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero
  rw [EF.paperFT_weilTest hc hc hcc hcc, EF.paperFT_weilTest hc hc hcc hcc, conj_I_div_two,
    conj_neg_I_div_two, paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_neg_I_div_two]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hint : ∀ g : ℝ → ℝ, Continuous g → Integrable (fun u => f u * g u) := fun g hg =>
    (hf.mul hg).integrable_of_hasCompactSupport (hfc.mul_right)
  have hZ := hint (fun u => Real.exp (|u| / 2)) (by fun_prop)
  have h1 : ∫ u, f u * Real.exp (-u / 2) ≤ ∫ u, f u * Real.exp (|u| / 2) :=
    integral_mono (hint _ (by fun_prop)) hZ fun u =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have := neg_abs_le u; linarith)) (hf0 u)
  have h2 : ∫ u, f u * Real.exp (u / 2) ≤ ∫ u, f u * Real.exp (|u| / 2) :=
    integral_mono (hint _ (by fun_prop)) hZ fun u =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have := le_abs_self u; linarith)) (hf0 u)
  have h3 : 0 ≤ ∫ u, f u * Real.exp (-u / 2) :=
    integral_nonneg fun u => mul_nonneg (hf0 u) (Real.exp_pos _).le
  have h4 : 0 ≤ ∫ u, f u * Real.exp (u / 2) :=
    integral_nonneg fun u => mul_nonneg (hf0 u) (Real.exp_pos _).le
  nlinarith [mul_le_mul h1 h2 h4 (h3.trans h1), mul_le_mul h2 h1 h3 (h4.trans h2)]

/-! ## Envelopes of the edge tail and its derivative -/

/-- `edgeMajorant` squared is again an `edgeMajorant`. -/
theorem edgeMajorant_sq (A c L t : ℝ) :
    edgeMajorant A c L t ^ 2 = edgeMajorant (A ^ 2) (2 * c) L t := by
  unfold edgeMajorant
  by_cases ht : t ∈ Ioi L
  · rw [indicator_of_mem ht, indicator_of_mem ht, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]; ring

/-- `∫ T² ≤ A²/c` with `A = C₀E(L)`, `c = Y − 9/2`. -/
theorem integral_edgeTail_sq_le {L R : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) :
    ∫ u, edgeTail L R u ^ 2 ≤
      (riemannEnvelopeConst * kernelEnvelope L) ^ 2 / (edgeRate L - 9 / 2) := by
  set A := riemannEnvelopeConst * kernelEnvelope L with hA
  set c := edgeRate L - 9 / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hA0 : 0 ≤ A := mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  have hmaj : ∀ u, edgeTail L R u ^ 2 ≤ edgeMajorant (A ^ 2) (2 * c) L |u| := fun u => by
    rw [← edgeMajorant_sq]
    exact pow_le_pow_left₀ (edgeTail_nonneg (by linarith) hR u)
      (edgeTail_le_edgeMajorant hL (by linarith) u) 2
  calc ∫ u, edgeTail L R u ^ 2 ≤ ∫ u, edgeMajorant (A ^ 2) (2 * c) L |u| :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
          (integrable_edgeMajorant_abs (sq_nonneg A) (by linarith) L)
          (Eventually.of_forall hmaj)
    _ = 2 * (A ^ 2 / (2 * c)) := integral_edgeMajorant_abs (by linarith) (by linarith)
    _ = A ^ 2 / c := by field_simp

/-- `∫ T e^{|u|/2} ≤ 2A e^{L/2}/(c − ½)`. -/
theorem integral_edgeTail_mul_exp_le {L R : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) :
    ∫ u, edgeTail L R u * Real.exp (|u| / 2) ≤
      2 * (riemannEnvelopeConst * kernelEnvelope L * Real.exp (L / 2) /
        (edgeRate L - 9 / 2 - 1 / 2)) := by
  set A := riemannEnvelopeConst * kernelEnvelope L with hA
  set c := edgeRate L - 9 / 2 with hc
  have hc0 : 0 < c - 1 / 2 := by rw [hc]; linarith
  have hA0 : 0 ≤ A := mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  have hmaj : ∀ u, edgeTail L R u * Real.exp (|u| / 2) ≤
      edgeMajorant (A * Real.exp (L / 2)) (c - 1 / 2) L |u| := fun u => by
    have h1 := edgeTail_le_edgeMajorant (R := R) hL (by linarith) u
    rw [← hA, ← hc] at h1
    by_cases hu : L < |u|
    · rw [edgeMajorant_of_lt hu] at h1 ⊢
      calc edgeTail L R u * Real.exp (|u| / 2)
          ≤ A * Real.exp (-c * (|u| - L)) * Real.exp (|u| / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = A * Real.exp (L / 2) * Real.exp (-(c - 1 / 2) * (|u| - L)) := by
            have e : Real.exp (-c * (|u| - L)) * Real.exp (|u| / 2) =
                Real.exp (L / 2) * Real.exp (-(c - 1 / 2) * (|u| - L)) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            rw [mul_assoc, e, ← mul_assoc]
    · push Not at hu
      rw [edgeTail_eq_zero_of_le (by linarith) hu, zero_mul]
      exact edgeMajorant_nonneg (by positivity) _
  calc ∫ u, edgeTail L R u * Real.exp (|u| / 2)
      ≤ ∫ u, edgeMajorant (A * Real.exp (L / 2)) (c - 1 / 2) L |u| :=
        integral_mono_of_nonneg (Eventually.of_forall fun u =>
            mul_nonneg (edgeTail_nonneg (by linarith) hR u) (Real.exp_pos _).le)
          (integrable_edgeMajorant_abs (by positivity) hc0 L) (Eventually.of_forall hmaj)
    _ = _ := integral_edgeMajorant_abs hc0 (by linarith)

theorem edgeCutoffD1_eq_zero_inner {L η u : ℝ} (hη : 0 < η) (hu : |u| < L) :
    edgeCutoffD1 L η u = 0 := by
  unfold edgeCutoffD1
  have h1 : 1 < (L + η - u) / η := by rw [lt_div_iff₀ hη]; linarith [le_abs_self u]
  have h2 : 1 < (L + η + u) / η := by rw [lt_div_iff₀ hη]; linarith [neg_abs_le u]
  rw [deriv_smoothTransition_eq_zero (Or.inr h1), deriv_smoothTransition_eq_zero (Or.inr h2)]
  ring

/-- `|Φ'(u)| ≤ 2π(e^{2u} + 2) Φ(u)` for `e^{2u} ≥ 3`. -/
theorem abs_cuspDeriv_le {u : ℝ} (hu : Real.log 3 / 2 ≤ u) :
    |cuspSeries (cuspDeriv riemannCuspPoly) u| ≤
      2 * π * (Real.exp (2 * u) + 2) * riemannKernelReal u := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hle := cuspSeries_cuspDeriv_riemannCuspPoly_le_sharp hu
  have hge := cuspSeries_cuspDeriv_riemannCuspPoly_ge_sharp hu0
  rw [← riemannKernelReal_of_nonneg hu0] at hle hge
  have hΦ := riemannKernelReal_pos u
  have he := Real.exp_pos (2 * u)
  have hmul : (5 - 2 * π * Real.exp (2 * u)) * riemannKernelReal u ≤
      2 * π * (Real.exp (2 * u) + 2) * riemannKernelReal u :=
    mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_gt_three]) hΦ.le
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem deriv_edgeTail_eq_zero_inner {L R u : ℝ} (hR : L ≤ R) (hu : |u| < L) :
    deriv (edgeTail L R) u = 0 := by
  have h : edgeTail L R =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hu] with v hv
    exact edgeTail_eq_zero_of_le hR hv.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the edge tail on the positive half-line. -/
theorem hasDerivAt_edgeTail_of_pos {L R u : ℝ} (hu : 0 < u) :
    HasDerivAt (edgeTail L R)
      (cuspSeries (cuspDeriv riemannCuspPoly) u * (edgeCutoff R 1 u - edgeCutoff L (edgeWidth L) u) +
        riemannKernelReal u * (edgeCutoffD1 R 1 u - edgeCutoffD1 L (edgeWidth L) u)) u := by
  have h := (hasDerivAt_riemannKernelReal_of_pos hu).mul
    ((hasDerivAt_edgeCutoff R 1 u).sub (hasDerivAt_edgeCutoff L (edgeWidth L) u))
  exact h

/-- **Envelope of the derivative of the edge tail.** With `K = C₀(Y + 4π + 2S₁(1 + Y))`,
`|T'(u)| ≤ K E(L) e^{−(c−2)(|u| − L)}` for `|u| ≥ L`. -/
theorem abs_deriv_edgeTail_le {S₁ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : ∀ x, |deriv st x| ≤ S₁)
    {L R u : ℝ} (hL : 1 ≤ L) (hu : L ≤ |u|) :
    |deriv (edgeTail L R) u| ≤
      riemannEnvelopeConst * (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) * kernelEnvelope L *
        Real.exp (-(edgeRate L - 9 / 2 - 2) * (|u| - L)) := by
  -- reduce to `u > 0`
  have key : ∀ v : ℝ, L ≤ v → |deriv (edgeTail L R) v| ≤
      riemannEnvelopeConst * (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) * kernelEnvelope L *
        Real.exp (-(edgeRate L - 9 / 2 - 2) * (v - L)) := by
    intro v hv
    have hv0 : 0 < v := by linarith
    have hη := edgeWidth_pos L
    have hY0 := edgeRate_pos L
    have hηY : edgeWidth L * edgeRate L = 1 := by unfold edgeWidth; field_simp
    rw [(hasDerivAt_edgeTail_of_pos (L := L) (R := R) hv0).deriv]
    have hlog3 : Real.log 3 / 2 ≤ v := by
      have : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
      linarith
    have hd := abs_cuspDeriv_le hlog3
    have hΦ := riemannKernelReal_pos v
    have hcut := abs_edgeCutoff_sub_le R L (edgeWidth L) v
    have hD1R := abs_edgeCutoffD1_le hS₁ (L := R) one_pos v
    have hD1L := abs_edgeCutoffD1_le hS₁ (L := L) hη v
    have h2S : 2 * S₁ / edgeWidth L = 2 * S₁ * edgeRate L := by
      field_simp; nlinarith
    rw [h2S] at hD1L
    have hpt : |cuspSeries (cuspDeriv riemannCuspPoly) v * (edgeCutoff R 1 v -
        edgeCutoff L (edgeWidth L) v) + riemannKernelReal v * (edgeCutoffD1 R 1 v -
        edgeCutoffD1 L (edgeWidth L) v)| ≤
        (2 * π * (Real.exp (2 * v) + 2) + 2 * S₁ * (1 + edgeRate L)) * riemannKernelReal v := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hΦ]
      have h1 : |cuspSeries (cuspDeriv riemannCuspPoly) v| * |edgeCutoff R 1 v -
          edgeCutoff L (edgeWidth L) v| ≤ 2 * π * (Real.exp (2 * v) + 2) * riemannKernelReal v :=
        (mul_le_mul_of_nonneg_left hcut (abs_nonneg _)).trans (by rw [mul_one]; exact hd)
      have h2 : |edgeCutoffD1 R 1 v - edgeCutoffD1 L (edgeWidth L) v| ≤ 2 * S₁ * (1 + edgeRate L) := by
        refine (abs_sub _ _).trans ?_
        rw [div_one] at hD1R
        linarith
      nlinarith
    refine hpt.trans ?_
    -- envelope
    have henv : riemannKernelReal v ≤
        riemannEnvelopeConst * (kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * (v - L))) := by
      have h1 := riemannKernelReal_le_envelope (u := v) (three_le_exp_two_mul_abs (by
        rw [abs_of_pos hv0]; linarith))
      rw [abs_of_pos hv0] at h1
      have h2 := kernelEnvelope_add_le L (v - L)
      rw [show L + (v - L) = v by ring] at h2
      exact h1.trans (mul_le_mul_of_nonneg_left h2 riemannEnvelopeConst_pos.le)
    have hev : Real.exp (2 * v) = Real.exp (2 * L) * Real.exp (2 * (v - L)) := by
      rw [← Real.exp_add]; ring_nf
    have he1 : 1 ≤ Real.exp (2 * (v - L)) := Real.one_le_exp (by linarith)
    have hcoef : 2 * π * (Real.exp (2 * v) + 2) + 2 * S₁ * (1 + edgeRate L) ≤
        (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) * Real.exp (2 * (v - L)) := by
      rw [hev]
      have hY : edgeRate L = 2 * π * Real.exp (2 * L) := rfl
      have hpos : 0 ≤ 2 * S₁ * (1 + edgeRate L) := by positivity
      nlinarith [Real.pi_pos, Real.exp_pos (2 * L)]
    have hcoef0 : 0 ≤ 2 * π * (Real.exp (2 * v) + 2) + 2 * S₁ * (1 + edgeRate L) := by positivity
    calc (2 * π * (Real.exp (2 * v) + 2) + 2 * S₁ * (1 + edgeRate L)) * riemannKernelReal v
        ≤ ((edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) * Real.exp (2 * (v - L))) *
            (riemannEnvelopeConst * (kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * (v - L)))) :=
          mul_le_mul hcoef henv hΦ.le (by positivity)
      _ = _ := by
          rw [show ((edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) * Real.exp (2 * (v - L))) *
            (riemannEnvelopeConst * (kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * (v - L)))) =
            riemannEnvelopeConst * (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) *
              kernelEnvelope L * (Real.exp (2 * (v - L)) *
                Real.exp (-(edgeRate L - 9 / 2) * (v - L))) by ring, ← Real.exp_add]
          congr 2; ring
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu ⊢; exact key u hu
  · rw [abs_of_neg h0] at hu ⊢
    have hneg : deriv (edgeTail L R) u = -deriv (edgeTail L R) (-u) := by
      have h := deriv_comp_neg (edgeTail L R) u
      have e : (fun x => edgeTail L R (-x)) = edgeTail L R := funext fun x => edgeTail_neg L R x
      rw [e] at h; exact h
    rw [hneg, abs_neg]
    exact key (-u) hu

/-- `∫ (T')² ≤ (eK E)²/(c − 2)`. -/
theorem integral_deriv_edgeTail_sq_le {S₁ : ℝ} (hS₁0 : 0 ≤ S₁) (hS₁ : ∀ x, |deriv st x| ≤ S₁)
    {L R : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 12 ≤ edgeRate L) :
    ∫ u, deriv (edgeTail L R) u ^ 2 ≤
      (Real.exp 1 * (riemannEnvelopeConst * (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) *
        kernelEnvelope L)) ^ 2 / (edgeRate L - 9 / 2 - 2) := by
  set K := riemannEnvelopeConst * (edgeRate L + 4 * π + 2 * S₁ * (1 + edgeRate L)) *
    kernelEnvelope L with hK
  set c := edgeRate L - 9 / 2 - 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hK0 : 0 ≤ K := by
    rw [hK]; have := riemannEnvelopeConst_pos; have := kernelEnvelope_pos L
    have := edgeRate_pos L; positivity
  have hL' : 0 ≤ L - 1 / c := by
    have : 1 / c ≤ 1 := by rw [div_le_one hc0]; linarith
    linarith
  have hmaj : ∀ u, |deriv (edgeTail L R) u| ≤
      edgeMajorant (Real.exp 1 * K) c (L - 1 / c) |u| := fun u => by
    by_cases hu : L ≤ |u|
    · have h := abs_deriv_edgeTail_le (R := R) hS₁0 hS₁ hL hu
      rw [← hK, ← hc] at h
      have h0 : 0 < 1 / c := by positivity
      have hlt : L - 1 / c < |u| := by linarith
      rw [edgeMajorant_of_lt hlt]
      refine h.trans ?_
      rw [show Real.exp 1 * K * Real.exp (-c * (|u| - (L - 1 / c))) =
        K * (Real.exp 1 * Real.exp (-c * (|u| - (L - 1 / c)))) by ring, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hK0
      apply Real.exp_le_exp.mpr
      have : c * (1 / c) = 1 := by field_simp
      nlinarith
    · push Not at hu
      rw [deriv_edgeTail_eq_zero_inner (by linarith) hu, abs_zero]
      exact edgeMajorant_nonneg (by positivity) _
  have hsq : ∀ u, deriv (edgeTail L R) u ^ 2 ≤
      edgeMajorant ((Real.exp 1 * K) ^ 2) (2 * c) (L - 1 / c) |u| := fun u => by
    rw [← edgeMajorant_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hmaj u) 2
  calc ∫ u, deriv (edgeTail L R) u ^ 2
      ≤ ∫ u, edgeMajorant ((Real.exp 1 * K) ^ 2) (2 * c) (L - 1 / c) |u| :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
          (integrable_edgeMajorant_abs (sq_nonneg _) (by linarith) _) (Eventually.of_forall hsq)
    _ = 2 * ((Real.exp 1 * K) ^ 2 / (2 * c)) := integral_edgeMajorant_abs (by linarith) hL'
    _ = _ := by field_simp

/-! ## The edge tail from above -/

theorem contDiff_three_ofReal_edgeTail (L R : ℝ) : ContDiff ℝ 3 (fun u => (edgeTail L R u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_edgeTail L R).of_le (WithTop.coe_le_coe.2 le_top))

theorem deriv_ofReal_edgeTail (L R u : ℝ) :
    deriv (fun v => (edgeTail L R v : ℂ)) u = ((deriv (edgeTail L R) u : ℝ) : ℂ) :=
  (((contDiff_edgeTail L R).differentiable (by simp)) u).hasDerivAt.ofReal_comp.deriv

/-- **Explicit-formula upper bound for the tail.** The prime term of `T ≥ 0` is nonnegative, so
`Re W(T, T) ≤ pole + arch`. -/
theorem re_W_edgeTail_le {L R : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) {C : ℝ}
    (hC : ∀ r : ℝ, |EF.gammaBracket r| ≤ C + |r|) {s : ℝ} (hs : 0 < s) :
    (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re ≤
      2 * (∫ u, edgeTail L R u * Real.exp (|u| / 2)) ^ 2 +
        ((C + s / 2) * (∫ u, edgeTail L R u ^ 2) +
          1 / (2 * s) * ∫ u, deriv (edgeTail L R) u ^ 2) := by
  set Tc : ℝ → ℂ := fun u => (edgeTail L R u : ℂ) with hTc
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hd := contDiff_ofReal_edgeTail L R
  have hd3 := contDiff_three_ofReal_edgeTail L R
  have hsupp := tsupport_ofReal_edgeTail hL0 hR
  have hc : HasCompactSupport Tc :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
  rw [zeta_W_eq_weilFullFunctional hd hc]
  unfold weilFullFunctional
  have hkc : HasCompactSupport (EF.weilTest Tc Tc) := EF.weilTest_hasCompactSupport hc hc
  have hpole := re_pole_le (continuous_edgeTail L R) (hasCompactSupport_edgeTail hL0 hR)
    (edgeTail_nonneg hL0 hR)
  have harch := re_arch_le hd3 hc hsupp hC hs
  have e1 : ∫ u, ‖Tc u‖ ^ 2 = ∫ u, edgeTail L R u ^ 2 := by
    congr 1; funext u; rw [hTc]; simp only; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : ∫ u, ‖deriv Tc u‖ ^ 2 = ∫ u, deriv (edgeTail L R) u ^ 2 := by
    congr 1; funext u; rw [hTc, deriv_ofReal_edgeTail, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1, e2] at harch
  -- the prime term is nonnegative
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hkc
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Tc Tc (Real.log n) + EF.weilTest Tc Tc (-Real.log n)) =
      (((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) : ℝ) : ℂ) := fun n => by
    rw [hTc, weilTest_ofReal_edgeTail, weilTest_ofReal_edgeTail]; push_cast; ring
  have hsum : ∑' n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Tc Tc (Real.log n) + EF.weilTest Tc Tc (-Real.log n)) =
      ((∑ n ∈ Finset.range N, (if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => ?_)]
    · push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hterm]; push_cast; ring
    · rw [Finset.mem_range, not_lt] at hn
      rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]
  have hprime0 : 0 ≤ ∑ n ∈ Finset.range N,
      (if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0) *
        (edgeLag L R (Real.log n) + edgeLag L R (-Real.log n)) := by
    refine Finset.sum_nonneg fun n _ => mul_nonneg ?_ (add_nonneg (edgeLag_nonneg hL0 hR _)
      (edgeLag_nonneg hL0 hR _))
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_refl 0
  rw [hsum]
  rw [Complex.add_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  rw [Complex.add_re] at hpole
  linarith

/-- The arithmetic of the upper constant. -/
theorem edgeTail_upper_arith {Y E C₀ C S₁ eL I1 I2 I3 : ℝ} (hY : 40 ≤ Y) (hE : 0 ≤ E)
    (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hS₁ : 0 ≤ S₁) (heL : 8 * eL ≤ (Y / 2) ^ 2) (heL0 : 0 ≤ eL)
    (hI1 : I1 ≤ 2 * (C₀ * E * eL.sqrt / (Y - 9 / 2 - 1 / 2)))
    (hI10 : 0 ≤ I1)
    (hI2 : I2 ≤ (C₀ * E) ^ 2 / (Y - 9 / 2))
    (hI3 : I3 ≤ (Real.exp 1 * (C₀ * (Y + 4 * π + 2 * S₁ * (1 + Y)) * E)) ^ 2 / (Y - 9 / 2 - 2)) :
    2 * I1 ^ 2 + ((C + Y / 2) * I2 + 1 / (2 * Y) * I3) ≤
      C₀ ^ 2 * (2 + C + Real.exp 1 ^ 2 * (2 + 4 * S₁) ^ 2) * E ^ 2 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  have hY0 : 0 < Y := by linarith
  -- pole
  have hd1 : Y / 2 ≤ Y - 9 / 2 - 1 / 2 := by linarith
  have hsq : eL.sqrt ^ 2 = eL := Real.sq_sqrt heL0
  have hp : 2 * I1 ^ 2 ≤ C₀ ^ 2 * E ^ 2 := by
    have h1 : I1 ≤ 2 * (C₀ * E * eL.sqrt / (Y / 2)) := hI1.trans (by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hd1)
    have h2 : I1 ^ 2 ≤ (2 * (C₀ * E * eL.sqrt / (Y / 2))) ^ 2 := pow_le_pow_left₀ hI10 h1 2
    have h3 : (2 * (C₀ * E * eL.sqrt / (Y / 2))) ^ 2 = 4 * (C₀ * E) ^ 2 * eL / (Y / 2) ^ 2 := by
      have e : (2 * (C₀ * E * eL.sqrt / (Y / 2))) ^ 2 =
          4 * (C₀ * E) ^ 2 * eL.sqrt ^ 2 / (Y / 2) ^ 2 := by ring
      rw [e, hsq]
    rw [h3] at h2
    have h4 : 4 * (C₀ * E) ^ 2 * eL / (Y / 2) ^ 2 ≤ (C₀ * E) ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg (C₀ * E)]
    nlinarith
  -- first archimedean part
  have ha1 : (C + Y / 2) * I2 ≤ C₀ ^ 2 * E ^ 2 * (C + 1) := by
    have h1 : I2 ≤ (C₀ * E) ^ 2 / (Y / 2) := hI2.trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))
    have hI20 : (C + Y / 2) * I2 ≤ (C + Y / 2) * ((C₀ * E) ^ 2 / (Y / 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine hI20.trans ?_
    have e : (C + Y / 2) * ((C₀ * E) ^ 2 / (Y / 2)) = C₀ ^ 2 * E ^ 2 * (2 * C / Y + 1) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 2 * C / Y ≤ C := by
      rw [div_le_iff₀ hY0]; nlinarith
    linarith
  -- second archimedean part
  have ha2 : 1 / (2 * Y) * I3 ≤ C₀ ^ 2 * E ^ 2 * (Real.exp 1 ^ 2 * (2 + 4 * S₁) ^ 2) := by
    have hK : Y + 4 * π + 2 * S₁ * (1 + Y) ≤ (2 + 4 * S₁) * Y := by nlinarith
    have hK0 : 0 ≤ Y + 4 * π + 2 * S₁ * (1 + Y) := by positivity
    have h1 : (Real.exp 1 * (C₀ * (Y + 4 * π + 2 * S₁ * (1 + Y)) * E)) ^ 2 ≤
        (Real.exp 1 * (C₀ * ((2 + 4 * S₁) * Y) * E)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul_of_nonneg_left _ he0.le
      apply mul_le_mul_of_nonneg_right _ hE
      exact mul_le_mul_of_nonneg_left hK hC₀
    have h2 : I3 ≤ (Real.exp 1 * (C₀ * ((2 + 4 * S₁) * Y) * E)) ^ 2 / (Y / 2) := by
      refine hI3.trans ?_
      calc (Real.exp 1 * (C₀ * (Y + 4 * π + 2 * S₁ * (1 + Y)) * E)) ^ 2 / (Y - 9 / 2 - 2)
          ≤ (Real.exp 1 * (C₀ * ((2 + 4 * S₁) * Y) * E)) ^ 2 / (Y - 9 / 2 - 2) :=
            div_le_div_of_nonneg_right h1 (by linarith)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h3 : 1 / (2 * Y) * I3 ≤ 1 / (2 * Y) *
        ((Real.exp 1 * (C₀ * ((2 + 4 * S₁) * Y) * E)) ^ 2 / (Y / 2)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    refine h3.trans (le_of_eq ?_)
    field_simp
  nlinarith

/-! ## From the tails to the truncation -/

/-- `W(T_R) → W(Φχ_L)` as `R → ∞`. -/
theorem tendsto_re_W_edgeTail {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun R => (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ))
        (fun u => (edgeTail L R u : ℂ))).re) atTop
      (𝓝 (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ))
        (fun u => (riemannTruncKernel L u : ℂ))).re) := by
  obtain ⟨S₁, hS₁0, hS₁⟩ := exists_abs_deriv_smoothTransition_le
  obtain ⟨S₂, hS₂0, hS₂⟩ := exists_abs_deriv_deriv_smoothTransition_le
  obtain ⟨BT, hBT⟩ : ∃ BT, BT = 1 + 2 * (2 * S₁ / 1 + 2 * S₁ / edgeWidth L) +
      ((2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 + (2 * S₂ + 2 * S₁ ^ 2) / edgeWidth L ^ 2) := ⟨_, rfl⟩
  obtain ⟨BE, hBE⟩ : ∃ BE, BE = 1 + 2 * (2 * S₁ / 1) + (2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 := ⟨_, rfl⟩
  have hη := edgeWidth_pos L
  have hBT0 : 0 ≤ BT := by rw [hBT]; positivity
  have hBE0 : 0 ≤ BE := by rw [hBE]; positivity
  obtain ⟨NT, hNT⟩ : ∃ NT, NT = 4 * (2 * BT * kernelTailMass 0) := ⟨_, rfl⟩
  have hNT0 : 0 ≤ NT := by have := kernelTailMass_nonneg 0; rw [hNT]; positivity
  obtain ⟨S, hS⟩ : ∃ S, S = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3 := ⟨_, rfl⟩
  have hlim : Tendsto (fun R => (2 * NT * (4 * (2 * BE * kernelTailMass R)) +
      (4 * (2 * BE * kernelTailMass R)) ^ 2) * S) atTop (𝓝 0) := by
    have h := tendsto_kernelTailMass
    have h1 : Tendsto (fun R => 4 * (2 * BE * kernelTailMass R)) atTop (𝓝 0) := by
      simpa using (h.const_mul (2 * BE)).const_mul 4
    have h2 := ((h1.const_mul (2 * NT)).add (h1.pow 2)).mul_const S
    simpa using h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (L + 2)] with R hR
  have hNE0 : 0 ≤ 4 * (2 * BE * kernelTailMass R) := by
    have := kernelTailMass_nonneg R; positivity
  have hdiff := norm_W_truncKernel_sub_le (L := L) (R := R) (NT := NT)
    (NE := 4 * (2 * BE * kernelTailMass R)) hL hR hNT0 hNE0
    (fun z hz => by rw [hNT, hBT]; exact norm_paperFT_edgeTail_le hS₁0 hS₂0 hS₁ hS₂ L R hz)
    (fun z hz => by rw [hBE]; exact norm_paperFT_outerTail_le hS₁0 hS₂0 hS₁ hS₂ R hz)
  rw [← hS] at hdiff
  have h1 := Complex.abs_re_le_norm
    (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ)) (fun u => (riemannTruncKernel L u : ℂ)) -
      zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ)))
  rw [Complex.sub_re] at h1
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact h1.trans hdiff

/-- The arithmetic of the lower bound. -/
theorem edgeTail_lower_arith {ℓ I2 P E Y C₀ u W : ℝ} (hY : 0 < Y) (hu : u ≤ 1)
    (hℓ : 20 + (2 + 120 * C₀ ^ 2) * Real.exp 6 / 200 ≤ ℓ)
    (hI2 : 400 * Real.exp (-6) * E ^ 2 / Y ≤ I2) (hP : P ≤ E ^ 2 / Y * (120 * C₀ ^ 2 * u))
    (hW : (ℓ / 2 - 10) * I2 - P ≤ W) : E ^ 2 / Y ≤ W := by
  have he : Real.exp 6 * Real.exp (-6) = 1 := by rw [← Real.exp_add]; simp
  have hE2 : 0 ≤ E ^ 2 / Y := by positivity
  have hc : (2 + 120 * C₀ ^ 2) * Real.exp 6 / 400 ≤ ℓ / 2 - 10 := by linarith
  have hc0 : 0 ≤ (2 + 120 * C₀ ^ 2) * Real.exp 6 / 400 := by positivity
  have h1 : (2 + 120 * C₀ ^ 2) * Real.exp 6 / 400 * (400 * Real.exp (-6) * E ^ 2 / Y) ≤
      (ℓ / 2 - 10) * I2 :=
    mul_le_mul hc hI2 (by positivity) (hc0.trans hc)
  have h2 : (2 + 120 * C₀ ^ 2) * Real.exp 6 / 400 * (400 * Real.exp (-6) * E ^ 2 / Y) =
      (2 + 120 * C₀ ^ 2) * (E ^ 2 / Y) * (Real.exp 6 * Real.exp (-6)) := by ring
  rw [h2, he, mul_one] at h1
  have h3 : P ≤ 120 * C₀ ^ 2 * (E ^ 2 / Y) := by
    refine hP.trans ?_
    have : 120 * C₀ ^ 2 * u ≤ 120 * C₀ ^ 2 := by nlinarith [sq_nonneg C₀]
    nlinarith
  nlinarith

/-- **The exact order of the truncation energy.** There is `K` such that for all large `L`,
`E(L)²/Y ≤ Re W(Φχ_L, Φχ_L) ≤ K E(L)²`, unconditionally. -/
theorem exists_twoSided_truncKernel_energy :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      kernelEnvelope L ^ 2 / edgeRate L ≤
          (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ))
            (fun u => (riemannTruncKernel L u : ℂ))).re ∧
        (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ))
            (fun u => (riemannTruncKernel L u : ℂ))).re ≤ K * kernelEnvelope L ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_gammaBracket_le
  obtain ⟨S₁, hS₁0, hS₁⟩ := exists_abs_deriv_smoothTransition_le
  have hC₀ := riemannEnvelopeConst_pos
  refine ⟨riemannEnvelopeConst ^ 2 * (2 + C + Real.exp 1 ^ 2 * (2 + 4 * S₁) ^ 2), by positivity, ?_⟩
  have hband := eventually_log_edgeBand_ge
    (20 + (2 + 120 * riemannEnvelopeConst ^ 2) * Real.exp 6 / 200)
  have hdec := tendsto_edgeDecay.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (2 : ℝ), hband, hdec] with L hL hℓ hu
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hY12, -, -⟩ := edgeRate_ge hL1
  have hY50 : 40 ≤ edgeRate L := by
    unfold edgeRate
    have h1 : Real.exp 2 ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
    have h7 : 7 ≤ Real.exp 2 := by
      have he1 := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      nlinarith
    have h3 : 3 * 7 ≤ π * Real.exp (2 * L) :=
      mul_le_mul (le_of_lt Real.pi_gt_three) (h7.trans h1) (by norm_num) Real.pi_pos.le
    linarith
  have hYpos := edgeRate_pos L
  have hlim := tendsto_re_W_edgeTail hL0
  constructor
  · -- lower bound
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (L + 2)] with R hR
    have hW := re_W_edgeTail_ge_narrow hL1 hR (by linarith)
    have hI2 := integral_edgeTail_sq_ge hL1 hR (by linarith)
    have hP := edgePrimeBound_le_decay hL1 hR
    exact edgeTail_lower_arith hYpos hu hℓ hI2 hP hW
  · -- upper bound
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (L + 2)] with R hR
    have hW := re_W_edgeTail_le hL1 hR hC (s := edgeRate L) hYpos
    have hI1 := integral_edgeTail_mul_exp_le hL1 hR (by linarith)
    have hI2 := integral_edgeTail_sq_le hL1 hR (by linarith)
    have hI3 := integral_deriv_edgeTail_sq_le hS₁0 hS₁ hL1 hR hY12
    have hI10 : 0 ≤ ∫ u, edgeTail L R u * Real.exp (|u| / 2) :=
      integral_nonneg fun u => mul_nonneg (edgeTail_nonneg hL0 hR u) (Real.exp_pos _).le
    rw [Real.exp_half] at hI1
    have heL : 8 * Real.exp L ≤ (edgeRate L / 2) ^ 2 := by
      unfold edgeRate
      have h4 : Real.exp L ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
      have h5 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
      have hπ2 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have hsq : Real.exp (2 * L) ≤ Real.exp (2 * L) ^ 2 := by nlinarith
      have e : (2 * π * Real.exp (2 * L) / 2) ^ 2 = π ^ 2 * Real.exp (2 * L) ^ 2 := by ring
      rw [e]
      have h6 : 9 * Real.exp (2 * L) ^ 2 ≤ π ^ 2 * Real.exp (2 * L) ^ 2 :=
        mul_le_mul_of_nonneg_right hπ2 (sq_nonneg _)
      linarith
    refine hW.trans ?_
    exact edgeTail_upper_arith hY50 (kernelEnvelope_pos L).le hC₀.le hC0 hS₁0 heL
      (Real.exp_pos L).le hI1 hI10 hI2 hI3

/-! ## The Rayleigh quotient -/

theorem kernelEnvelope_ge_one {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    kernelEnvelope 1 ≤ kernelEnvelope u := by
  unfold kernelEnvelope
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : 1 + 2 * (1 - u) ≤ Real.exp (2 * (1 - u)) := by
    linarith [Real.add_one_le_exp (2 * (1 - u))]
  have h2 : Real.exp (2 * 1) = Real.exp (2 * u) * Real.exp (2 * (1 - u)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have h4 : 2 * (1 - u) ≤ Real.exp (2 * 1) - Real.exp (2 * u) := by
    rw [h2]; nlinarith
  have h7 : 3 * (Real.exp (2 * 1) - Real.exp (2 * u)) ≤
      π * (Real.exp (2 * 1) - Real.exp (2 * u)) :=
    mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith)
  rw [mul_sub, mul_sub] at h7
  simp only [neg_mul]
  generalize Real.exp (2 * 1) = a at h4 h7 ⊢
  generalize Real.exp (2 * u) = b at h4 h7 ⊢
  linarith

theorem continuous_riemannTruncKernel (L : ℝ) : Continuous (riemannTruncKernel L) :=
  continuous_riemannKernelReal.mul (contDiff_edgeCutoff L (edgeWidth L)).continuous

theorem hasCompactSupport_riemannTruncKernel (L : ℝ) : HasCompactSupport (riemannTruncKernel L) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -(|L| + edgeWidth L)) (b := |L| + edgeWidth L)) fun u hu => ?_
  have hu' : L + edgeWidth L ≤ |u| := by
    rw [Set.mem_Icc, not_and_or] at hu
    have := le_abs_self L
    rcases hu with h | h
    · push Not at h; linarith [le_abs.2 (Or.inr (show -u ≥ |L| + edgeWidth L by linarith))]
    · push Not at h; linarith [le_abs_self u]
  unfold riemannTruncKernel
  rw [edgeCutoff_eq_zero (edgeWidth_pos L) hu', mul_zero]

/-- `∫(Φχ_L)² ≥ 400 E(1)²` for `L ≥ 1`. -/
theorem integral_truncKernel_sq_ge {L : ℝ} (hL : 1 ≤ L) :
    400 * kernelEnvelope 1 ^ 2 ≤ ∫ u, riemannTruncKernel L u ^ 2 := by
  have hint : Integrable (fun u => riemannTruncKernel L u ^ 2) := by
    have h2 : HasCompactSupport (fun u => riemannTruncKernel L u ^ 2) := by
      simpa [Function.comp_def] using
        (hasCompactSupport_riemannTruncKernel L).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    exact ((continuous_riemannTruncKernel L).pow 2).integrable_of_hasCompactSupport h2
  have hlow : ∀ u ∈ Icc (0 : ℝ) 1, 400 * kernelEnvelope 1 ^ 2 ≤ riemannTruncKernel L u ^ 2 :=
    fun u hu => by
      have habs : |u| ≤ L := by rw [abs_of_nonneg hu.1]; linarith [hu.2]
      unfold riemannTruncKernel
      rw [edgeCutoff_eq_one (edgeWidth_pos L) habs, mul_one]
      have h1 := envelope_le_riemannKernelReal hu.1
      have h2 := kernelEnvelope_ge_one hu.1 hu.2
      have h3 := kernelEnvelope_pos 1
      have : 20 * kernelEnvelope 1 ≤ riemannKernelReal u := by linarith
      nlinarith
  calc 400 * kernelEnvelope 1 ^ 2 = ∫ _u in Icc (0 : ℝ) 1, 400 * kernelEnvelope 1 ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]; norm_num
    _ ≤ ∫ u in Icc (0 : ℝ) 1, riemannTruncKernel L u ^ 2 :=
        setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne) hint.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ u, riemannTruncKernel L u ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)

/-- **The canonical near-null Rayleigh quotient is `e^{−2πe^{2L} + O(L)}`.** There is `K'` such that
for all large `L`, `0 < Re W(Φχ_L) ≤ K' E(L)² ∫(Φχ_L)²`. -/
theorem exists_truncKernel_rayleigh_le :
    ∃ K' : ℝ, 0 < K' ∧ ∀ᶠ L : ℝ in atTop,
      0 < (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ))
          (fun u => (riemannTruncKernel L u : ℂ))).re ∧
        (zetaZeroConfig.W (fun u => (riemannTruncKernel L u : ℂ))
            (fun u => (riemannTruncKernel L u : ℂ))).re ≤
          K' * kernelEnvelope L ^ 2 * ∫ u, riemannTruncKernel L u ^ 2 := by
  obtain ⟨K, hK, hev⟩ := exists_twoSided_truncKernel_energy
  have hE1 := kernelEnvelope_pos 1
  refine ⟨K / (400 * kernelEnvelope 1 ^ 2), by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with L hL hL1
  obtain ⟨hlo, hhi⟩ := hL
  have hYpos := edgeRate_pos L
  have hEL := kernelEnvelope_pos L
  refine ⟨lt_of_lt_of_le (by positivity) hlo, hhi.trans ?_⟩
  have hI := integral_truncKernel_sq_ge hL1
  have h400 : 0 < 400 * kernelEnvelope 1 ^ 2 := by positivity
  calc K * kernelEnvelope L ^ 2
      = K / (400 * kernelEnvelope 1 ^ 2) * kernelEnvelope L ^ 2 * (400 * kernelEnvelope 1 ^ 2) := by
        field_simp
    _ ≤ _ := by gcongr

end

end RHTower
