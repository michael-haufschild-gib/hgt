import GaloisForLFunctions.ThetaCuspSections.VinogradovKorobovCriticalCollar
import GaloisForLFunctions.RHTower.XiHadamardSharpRegion
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.WeilLagFunctionOmega

/-!
# The finite-rank window criterion at every aperture

**Theorem** (`exists_signedHankel_posDef_of_current_nonneg`). There is `D` such that for every rank `N` and every
aperture `0 < a ≤ 3/4`, nonnegativity of the current on `|b| ≤ D (N+1)³` makes the signed section positive definite.

The current vanishes on the real line, because `Ξ` is real there. So its core and its tail are both proportional to
`a`, and the aperture cancels from the comparison:

* tail: `|current a b| ≤ C a e^{−π|b|/4}`, by the mean value theorem from `a = 0`;
* core: `current a b ≥ m a` for `|b| ≤ 1`. There `Re (ξ'/ξ) ≥ a/(8(|γ₀|+1)²)`: each line-conjugate pair at distance
  `X = (b−γ)²` contributes at least `a/(4X)`, and one pair suffices since all pairs are positive.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Matrix Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar
open _root_.RHTower CriticalCollar QuantitativeCollar

/-! ## The current is proportional to the aperture -/

/-- `Ξ` is real on the real line, so the current vanishes at aperture zero. -/
theorem current_zero (b : ℝ) : current 0 b = 0 := by
  have hconj : ∀ w : ℂ, XiC ((starRingEnd ℂ) w) = (starRingEnd ℂ) (XiC w) := XiC_conj
  have hu : (starRingEnd ℂ) (XiC (b : ℂ)) = XiC (b : ℂ) := by
    rw [← hconj, Complex.conj_ofReal]
  have hfun : ((starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ) : ℂ → ℂ) = XiC := by
    funext w
    simp only [Function.comp, hconj, Complex.conj_conj]
  have hv : (starRingEnd ℂ) (deriv XiC (b : ℂ)) = deriv XiC (b : ℂ) := by
    have h : deriv ((starRingEnd ℂ) ∘ XiC ∘ (starRingEnd ℂ)) (b : ℂ) =
        ((starRingEnd ℂ) ∘ deriv XiC ∘ (starRingEnd ℂ)) (b : ℂ) := congrFun deriv_conj_conj _
    rw [hfun] at h
    simp only [Function.comp, Complex.conj_ofReal] at h
    exact h.symm
  have hui := Complex.conj_eq_iff_im.mp hu
  have hvi := Complex.conj_eq_iff_im.mp hv
  have hz : ((b : ℂ) - ((0 : ℝ) : ℂ) * I) = (b : ℂ) := by simp
  rw [current, hz]
  simp only [mul_re, mul_im, conj_re, conj_im, neg_re, neg_im, I_re, I_im, hui, hvi]
  ring

/-- Mean value bound from the real line with the strip decay retained. -/
theorem norm_sub_real_line_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hbound : ∀ t a : ℝ, |a| ≤ 7 / 8 → ‖f ((t : ℂ) + (a : ℂ) * I)‖ ≤ C * Real.exp (-(δ * |t|)))
    (b a : ℝ) (ha : |a| ≤ 3 / 4) :
    ‖f ((b : ℂ) - (a : ℂ) * I) - f (b : ℂ)‖ ≤ 8 * C * Real.exp δ * Real.exp (-(δ * |b|)) * |a| := by
  let z : ℂ := (b : ℂ)
  let y : ℂ := (b : ℂ) - (a : ℂ) * I
  let B : ℝ := C * Real.exp δ * Real.exp (-(δ * |b|))
  have hlarge (u : ℂ) (hu : ‖u - z‖ ≤ 7 / 8) : ‖f u‖ ≤ B := by
    have him : |u.im| ≤ 7 / 8 := by
      have hi := (Complex.abs_im_le_norm (u - z)).trans hu
      simpa [z] using hi
    have hre : |b| - 7 / 8 ≤ |u.re| := by
      have hr := (Complex.abs_re_le_norm (u - z)).trans hu
      have hr' : |u.re - b| ≤ 7 / 8 := by simpa [z] using hr
      have habs := abs_sub_abs_le_abs_sub b u.re
      rw [abs_sub_comm b u.re] at habs
      linarith only [hr', habs]
    have hfu := hbound u.re u.im him
    rw [Complex.re_add_im] at hfu
    have hexp : -(δ * |u.re|) ≤ δ + -(δ * |b|) := by
      have h := mul_le_mul_of_nonneg_left hre hδ
      nlinarith only [h, hδ]
    calc
      ‖f u‖ ≤ C * Real.exp (-(δ * |u.re|)) := hfu
      _ ≤ C * Real.exp (δ + -(δ * |b|)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
      _ = B := by rw [Real.exp_add]; dsimp [B]; ring
  have hder (w : ℂ) (hw : w ∈ Metric.closedBall z (3 / 4)) : ‖deriv f w‖ ≤ 8 * B := by
    have hw' : ‖w - z‖ ≤ 3 / 4 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hsphere (u : ℂ) (hu : u ∈ Metric.sphere w (1 / 8)) : ‖f u‖ ≤ B := by
      apply hlarge
      have hu' : ‖u - w‖ = 1 / 8 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hu
      have h : ‖u - z‖ ≤ ‖u - w‖ + ‖w - z‖ := by
        rw [show u - z = (u - w) + (w - z) by ring]
        exact norm_add_le _ _
      rw [hu'] at h
      linarith only [h, hw']
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1 / 8) hf.diffContOnCl hsphere
    convert h using 1
    ring
  have hdist : ‖y - z‖ = |a| := by
    have he : y - z = -((a : ℂ) * I) := by dsimp [y, z]; ring
    rw [he, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hz : z ∈ Metric.closedBall z (3 / 4) := Metric.mem_closedBall_self (by norm_num)
  have hy : y ∈ Metric.closedBall z (3 / 4) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, hdist] using ha
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w _ => hf w) hder (convex_closedBall z (3 / 4)) hz hy
  rw [hdist] at h
  change ‖f y - f z‖ ≤ _
  calc
    ‖f y - f z‖ ≤ 8 * B * |a| := h
    _ = _ := by dsimp [B]; ring

/-- **The current is proportional to the aperture, with exponential decay.** -/
theorem abs_current_le : ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, |a| ≤ 3 / 4 → ∀ b : ℝ,
    |current a b| ≤ C * |a| * Real.exp (-((Real.pi / 4) * |b|)) := by
  let δ : ℝ := Real.pi / 8
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδpi : 2 * δ < Real.pi / 2 := by dsimp only [δ]; linarith only [Real.pi_pos]
  obtain ⟨C₀, hC₀, h₀⟩ := exists_norm_XiC_horizontal_le (A := 7 / 8) (δ := δ) (by norm_num) hδ hδpi
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_XiC_deriv_horizontal_le (A := 7 / 8) (δ := δ) (by norm_num) hδ hδpi
  have hd : Differentiable ℂ (deriv XiC) := fun z => ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  refine ⟨32 * C₀ * C₁ * Real.exp δ + 1, by positivity, fun a ha b => ?_⟩
  have ha78 : |a| ≤ 7 / 8 := ha.trans (by norm_num)
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hv : ‖deriv XiC z‖ ≤ C₁ * Real.exp (-(δ * |b|)) := by
    simpa only [z, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using
      h₁ b (-a) (by simpa only [abs_neg] using ha78)
  have hu₀ : ‖XiC (b : ℂ)‖ ≤ C₀ * Real.exp (-(δ * |b|)) := by
    simpa using h₀ b 0 (by norm_num)
  have hdu := norm_sub_real_line_le XiC_differentiable hC₀ hδ h₀ b a ha
  have hdv := norm_sub_real_line_le hd hC₁ hδ h₁ b a ha
  have hdiff := current_difference_le (XiC (b : ℂ)) (XiC z) (deriv XiC (b : ℂ)) (deriv XiC z)
  have hrew : current a b = 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re := rfl
  have hrew₀ : 2 * ((starRingEnd ℂ) (XiC (b : ℂ)) * (-I * deriv XiC (b : ℂ))).re = 0 := by
    have h := current_zero b
    have hz0 : ((b : ℂ) - ((0 : ℝ) : ℂ) * I) = (b : ℂ) := by simp
    rw [current, hz0] at h
    exact h
  rw [hrew₀, sub_zero, ← hrew] at hdiff
  have he2 : Real.exp (-(δ * |b|)) * Real.exp (-(δ * |b|)) = Real.exp (-((Real.pi / 4) * |b|)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δ]
    ring
  have hp₀ := mul_le_mul hdu hv (norm_nonneg _) (by positivity)
  have hp₁ := mul_le_mul hu₀ hdv (norm_nonneg _) (by positivity)
  have hsum : 2 * (‖XiC z - XiC (b : ℂ)‖ * ‖deriv XiC z‖ + ‖XiC (b : ℂ)‖ * ‖deriv XiC z - deriv XiC (b : ℂ)‖) ≤
      32 * C₀ * C₁ * Real.exp δ * |a| * (Real.exp (-(δ * |b|)) * Real.exp (-(δ * |b|))) := by
    nlinarith only [hp₀, hp₁]
  rw [he2] at hsum
  have hexp0 : 0 ≤ |a| * Real.exp (-((Real.pi / 4) * |b|)) := by positivity
  calc
    |current a b| ≤ _ := hdiff.trans hsum
    _ ≤ _ := by nlinarith only [hexp0]

/-- The tail moments are proportional to the aperture. -/
theorem tailMoment_le_aperture : ∃ M K : ℝ, 0 < M ∧ 1 ≤ K ∧
    ∀ a : ℝ, |a| ≤ 3 / 4 → ∀ T : ℝ, 0 ≤ T → ∀ k : ℕ,
      |tailMoment a T k| ≤ |a| * (M * K ^ k * (k.factorial : ℝ) * Real.exp (-((Real.pi / 8) * T))) := by
  obtain ⟨C, hC, hcurrent⟩ := abs_current_le
  let E : ℝ → ℝ := fun b => Real.exp (-((Real.pi / 16) * |b|))
  have hE : Integrable E := integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (by positivity)
  let I₀ : ℝ := ∫ b : ℝ, E b
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun b => (Real.exp_pos _).le
  let M : ℝ := C * (I₀ + 1)
  let K : ℝ := max 1 (16 / Real.pi)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, K, hM, le_max_left _ _, fun a ha T _hT k => ?_⟩
  let S : Set ℝ := {b : ℝ | T < |b|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hi : Integrable (S.indicator (fun b : ℝ => b ^ k * current a b)) :=
    (raw_integrable a (ha.trans_lt (by norm_num)) k).indicator hS
  let B : ℝ := C * |a| * Real.exp (-((Real.pi / 8) * T)) * (16 / Real.pi) ^ k * (k.factorial : ℝ)
  have hmajor (b : ℝ) : |S.indicator (fun b : ℝ => b ^ k * current a b) b| ≤ B * E b := by
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb, abs_mul, abs_pow]
      have hbT : T ≤ |b| := le_of_lt hb
      have hexp : Real.exp (-((Real.pi / 8) * |b|)) ≤ Real.exp (-((Real.pi / 8) * T)) :=
        Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hbT])
      have h := mul_le_mul_of_nonneg_left (hcurrent a ha b) (pow_nonneg (abs_nonneg b) k)
      have hpow := pow_abs_mul_exp_neg_le (by positivity : (0 : ℝ) < Real.pi / 8) k b
      calc
        |b| ^ k * |current a b| ≤ |b| ^ k * (C * |a| * Real.exp (-((Real.pi / 4) * |b|))) := h
        _ = C * |a| * Real.exp (-((Real.pi / 8) * |b|)) * (|b| ^ k * Real.exp (-((Real.pi / 8) * |b|))) := by
          rw [show -((Real.pi / 4) * |b|) = -((Real.pi / 8) * |b|) + -((Real.pi / 8) * |b|) by ring,
            Real.exp_add]
          ring
        _ ≤ (C * |a| * Real.exp (-((Real.pi / 8) * T))) *
            ((2 / (Real.pi / 8)) ^ k * (k.factorial : ℝ) * Real.exp (-(((Real.pi / 8) / 2) * |b|))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp (by positivity)) hpow (by positivity) (by positivity)
        _ = B * E b := by
          dsimp only [B, E]
          rw [show (2 : ℝ) / (Real.pi / 8) = 16 / Real.pi by ring, show (Real.pi / 8) / 2 = Real.pi / 16 by ring]
          ring
    · rw [Set.indicator_of_notMem hb, abs_zero]
      positivity
  have hnorm : Integrable (fun b : ℝ => |S.indicator (fun b : ℝ => b ^ k * current a b) b|) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hle := integral_mono hnorm (hE.const_mul B) hmajor
  rw [integral_const_mul] at hle
  have hn : |tailMoment a T k| ≤ B * I₀ := by
    change |∫ b : ℝ, S.indicator (fun b : ℝ => b ^ k * current a b) b| ≤ _
    exact abs_integral_le_integral_abs.trans hle
  have hK : (16 / Real.pi) ^ k ≤ K ^ k := pow_le_pow_left₀ (by positivity) (le_max_right _ _) k
  have hBnn : 0 ≤ B := by dsimp only [B]; positivity
  calc
    |tailMoment a T k| ≤ B * I₀ := hn
    _ ≤ |a| * (C * (I₀ + 1) * (16 / Real.pi) ^ k * (k.factorial : ℝ) * Real.exp (-((Real.pi / 8) * T))) := by
      have : B * I₀ ≤ B * (I₀ + 1) := mul_le_mul_of_nonneg_left (by linarith only) hBnn
      refine this.trans (le_of_eq ?_)
      dsimp only [B]
      ring
    _ ≤ _ := by
      dsimp only [M]
      gcongr

/-! ## The core: one pair of zeros gives a floor proportional to the aperture -/

/-- A line-conjugate pair at horizontal distance `X` contributes at least `a/(4X)`. -/
theorem pair_lower {a δ X : ℝ} (ha : 0 < a) (ha2 : a ≤ 3 / 4) (hδ : δ ^ 2 < 1 / 4) (hX : 2 ≤ X) :
    a / (4 * X) ≤ (a - δ) / ((a - δ) ^ 2 + X) + (a + δ) / ((a + δ) ^ 2 + X) := by
  have hX0 : 0 < X := by linarith only [hX]
  have hδ' : |δ| < 1 / 2 := by
    rw [← sq_lt_sq₀ (abs_nonneg _) (by norm_num), sq_abs]
    linarith only [hδ]
  obtain ⟨hδ1, hδ2⟩ := abs_lt.mp hδ'
  have h₁ : (a - δ) ^ 2 ≤ 25 / 16 := by nlinarith only [ha, ha2, hδ1, hδ2]
  have h₂ : (a + δ) ^ 2 ≤ 25 / 16 := by nlinarith only [ha, ha2, hδ1, hδ2]
  have hd₁ : 0 < (a - δ) ^ 2 + X := by positivity
  have hd₂ : 0 < (a + δ) ^ 2 + X := by positivity
  rw [div_add_div _ _ hd₁.ne' hd₂.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have hd₁' : (a - δ) ^ 2 + X ≤ 2 * X := by linarith only [h₁, hX]
  have hd₂' : (a + δ) ^ 2 + X ≤ 2 * X := by linarith only [h₂, hX]
  have hprod : ((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X) ≤ 4 * X ^ 2 := by nlinarith only [hd₁', hd₂', hd₁, hd₂]
  have hnum : (a - δ) * ((a + δ) ^ 2 + X) + ((a - δ) ^ 2 + X) * (a + δ) = 2 * a * (a ^ 2 - δ ^ 2 + X) := by ring
  rw [hnum]
  have hmid : X / 2 ≤ a ^ 2 - δ ^ 2 + X := by nlinarith only [hδ, hX, sq_nonneg a]
  have h3 : a * (((a - δ) ^ 2 + X) * ((a + δ) ^ 2 + X)) ≤ a * (4 * X ^ 2) :=
    mul_le_mul_of_nonneg_left hprod ha.le
  have h4 : 2 * a * (X / 2) * (4 * X) ≤ 2 * a * (a ^ 2 - δ ^ 2 + X) * (4 * X) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid (by positivity)) (by positivity)
  nlinarith only [h3, h4]

/-- One pair above the sum: nonnegative pairs plus one quantified pair bound the real part below. -/
theorem le_re_tsum_of_lineConj_pairs {f : XiZeroCopy → ℂ} (hsum : Summable f) {c : ℝ} (hc : 0 ≤ c)
    (q₀ : XiZeroCopy) (hpair : ∀ q, 0 ≤ (f q + f (xiZeroCopyLineConjEquiv q)).re)
    (hpair₀ : ∀ q, q = q₀ ∨ xiZeroCopyLineConjEquiv q = q₀ → 2 * c ≤ (f q + f (xiZeroCopyLineConjEquiv q)).re) :
    c ≤ (∑' q, f q).re := by
  classical
  let g : XiZeroCopy → ℂ := fun q => if q = q₀ then (c : ℂ) else 0
  have hg : HasSum g (c : ℂ) := by
    simpa only [g] using hasSum_ite_eq q₀ (c : ℂ)
  have hsum' : Summable fun q => f q - g q := hsum.sub hg.summable
  have hnn := centralPaired_tsum_re_nonneg_of_lineConj_pairs (fun q => f q - g q) hsum' (fun q => by
    have hgre (p : XiZeroCopy) : (g p).re = if p = q₀ then c else 0 := by
      by_cases hp : p = q₀ <;> simp [g, hp]
    simp only [Complex.add_re, Complex.sub_re, hgre]
    have hP := hpair q
    simp only [Complex.add_re] at hP
    by_cases h1 : q = q₀
    · have hQ := hpair₀ q (Or.inl h1)
      simp only [Complex.add_re] at hQ
      split_ifs <;> linarith only [hQ, hc]
    · by_cases h2 : xiZeroCopyLineConjEquiv q = q₀
      · have hQ := hpair₀ q (Or.inr h2)
        simp only [Complex.add_re] at hQ
        split_ifs <;> linarith only [hQ, hc]
      · simp only [if_neg h1, if_neg h2]
        linarith only [hP])
  rw [hsum.tsum_sub hg.summable, hg.tsum_eq, Complex.sub_re, Complex.ofReal_re] at hnn
  linarith only [hnn]

theorem nonempty_xiZeroCopy : Nonempty XiZeroCopy := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have hz : weilLagFunction 0 = 0 := by
    unfold weilLagFunction
    exact tsum_empty
  rw [weilLagFunction_zero] at hz
  have h0 : poleSharpConstant = 0 := Complex.ofReal_injective (hz.trans Complex.ofReal_zero.symm)
  exact poleSharpConstant_pos.ne' h0

/-- **The floor of the logarithmic derivative.** For `0 < a ≤ 3/4`, `|b| ≤ 1`, `Re (ξ'/ξ)(½ + a + ib) ≥ m₀ a`. -/
theorem exists_re_logDeriv_xi_floor : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ a b : ℝ, 0 < a → a ≤ 3 / 4 → |b| ≤ 1 →
    a * m₀ ≤ (logDeriv xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I)).re := by
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  set Y : ℝ := (|(q₀.1 : ℂ).im| + 1) ^ 2 with hY
  have hY0 : 0 < Y := by positivity
  refine ⟨1 / (8 * Y), by positivity, fun a b ha ha2 hb => ?_⟩
  set s : ℂ := 1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I with hs
  have hre : s.re = 1 / 2 + a := by norm_num [hs, Complex.mul_re, Complex.mul_im]
  have him : s.im = b := by norm_num [hs, Complex.mul_re, Complex.mul_im]
  have hxi : xi s ≠ 0 := xi_ne_zero_of_abs_im_le_nine_halves (by rw [him]; linarith only [hb])
  have hsum : Summable fun q : XiZeroCopy => ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ := by
    refine (XiAtlasFinitePart.summable_logDerivTerm hxi).congr fun q => ?_
    show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  -- The pair formula.
  have hpairval (q : XiZeroCopy) :
      (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ +
          (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹ + (s - ((xiZeroCopyLineConjEquiv q).1 : ℂ))⁻¹).re =
        (a - ((q.1 : ℂ).re - 1 / 2)) / ((a - ((q.1 : ℂ).re - 1 / 2)) ^ 2 + (b - (q.1 : ℂ).im) ^ 2) +
          (a + ((q.1 : ℂ).re - 1 / 2)) / ((a + ((q.1 : ℂ).re - 1 / 2)) ^ 2 + (b - (q.1 : ℂ).im) ^ 2) := by
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    have hρ' := xiZero_lineConj_eq q
    have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) = -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]
      ring
    have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re = -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    simp only [Complex.add_re]
    rw [hconst, hρ', re_inv_sub_eq s (q.1 : ℂ), re_inv_sub_lineConj_eq s (q.1 : ℂ), hre, him]
    have e : (1 / 2 + a - 1 / 2 : ℝ) = a := by ring
    rw [e]
    ring
  have hlow (q : XiZeroCopy) : 2 ≤ (b - (q.1 : ℂ).im) ^ 2 := by
    have hg := four_half_lt_abs_im_of_xiZeroCopy q
    have h1 : |(q.1 : ℂ).im| - |b| ≤ |b - (q.1 : ℂ).im| := by
      have := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) b
      rwa [abs_sub_comm ((q.1 : ℂ).im) b] at this
    rw [← sq_abs]
    have h2 : (2 : ℝ) ≤ |b - (q.1 : ℂ).im| := by linarith only [h1, hg, hb]
    nlinarith only [h2]
  have hδ (q : XiZeroCopy) : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hc : 0 ≤ a * (1 / (8 * Y)) := by positivity
  rw [logDeriv_xi_eq_partialFraction hxi]
  refine le_re_tsum_of_lineConj_pairs hsum hc q₀ (fun q => ?_) (fun q hq => ?_)
  · have h := pair_lower ha ha2 (hδ q) (hlow q)
    have hp : 0 < a / (4 * (b - (q.1 : ℂ).im) ^ 2) := by
      have := hlow q
      positivity
    have e := hpairval q
    rw [add_assoc (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)] at e
    rw [e]
    linarith only [h, hp]
  · have h := pair_lower ha ha2 (hδ q) (hlow q)
    have e := hpairval q
    rw [add_assoc (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)] at e
    rw [e]
    refine le_trans ?_ h
    have him_q : |(q.1 : ℂ).im| = |(q₀.1 : ℂ).im| := by
      rcases hq with rfl | hq
      · rfl
      · rw [← hq, xiZero_lineConj_eq q]
        simp
    have hXY : (b - (q.1 : ℂ).im) ^ 2 ≤ Y := by
      rw [hY, ← sq_abs (b - (q.1 : ℂ).im)]
      have h1 : |b - (q.1 : ℂ).im| ≤ |b| + |(q.1 : ℂ).im| := abs_sub _ _
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [← him_q]
      linarith only [h1, hb]
    have hX0 : 0 < (b - (q.1 : ℂ).im) ^ 2 := lt_of_lt_of_le (by norm_num) (hlow q)
    rw [show 2 * (a * (1 / (8 * Y))) = a / (4 * Y) by field_simp; ring]
    exact div_le_div_of_nonneg_left ha.le (by positivity) (by linarith only [hXY])

/-- `|Ξ|²` is bounded below on the low rectangle. -/
theorem exists_normSq_XiC_floor : ∃ f₀ : ℝ, 0 < f₀ ∧ ∀ a b : ℝ, a ∈ Icc (0 : ℝ) (3 / 4) → b ∈ Icc (0 : ℝ) 1 →
    f₀ ≤ Complex.normSq (XiC ((b : ℂ) - (a : ℂ) * I)) := by
  let F : ℝ × ℝ → ℝ := fun p => Complex.normSq (XiC ((p.2 : ℂ) - (p.1 : ℂ) * I))
  have hK : IsCompact (Icc (0 : ℝ) (3 / 4) ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0 : ℝ) (3 / 4) ×ˢ Icc (0 : ℝ) 1).Nonempty :=
    ⟨(0, 0), Set.mk_mem_prod (by norm_num) (by norm_num)⟩
  have hcont : Continuous F :=
    Complex.continuous_normSq.comp (XiC_differentiable.continuous.comp (by fun_prop))
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hne0 : XiC ((p.2 : ℂ) - (p.1 : ℂ) * I) ≠ 0 := by
    have him : (1 / 2 + ((p.2 : ℂ) - (p.1 : ℂ) * I) * I).im = p.2 := by
      norm_num [Complex.mul_re, Complex.mul_im]
    have hb : |(1 / 2 + ((p.2 : ℂ) - (p.1 : ℂ) * I) * I).im| ≤ 9 / 2 := by
      rw [him, abs_of_nonneg (Set.mem_prod.1 hp).2.1]
      linarith only [(Set.mem_prod.1 hp).2.2]
    exact xi_ne_zero_of_abs_im_le_nine_halves hb
  refine ⟨F p, Complex.normSq_pos.mpr hne0, fun a b ha hb => ?_⟩
  exact isMinOn_iff.1 hmin (a, b) (Set.mk_mem_prod ha hb)

/-- **The core.** On `b ∈ [0,1]` the current is at least `m a`, uniformly in `0 < a ≤ 3/4`. -/
theorem exists_current_floor : ∃ m : ℝ, 0 < m ∧ ∀ a b : ℝ, 0 < a → a ≤ 3 / 4 → b ∈ Icc (0 : ℝ) 1 →
    a * m ≤ current a b := by
  obtain ⟨m₀, hm₀, hfloor⟩ := exists_re_logDeriv_xi_floor
  obtain ⟨f₀, hf₀, hnorm⟩ := exists_normSq_XiC_floor
  refine ⟨2 * f₀ * m₀, by positivity, fun a b ha ha2 hb => ?_⟩
  set z : ℂ := (b : ℂ) - (a : ℂ) * I with hz
  have hN := hnorm a b ⟨ha.le, ha2⟩ hb
  have hne : XiC z ≠ 0 := by
    intro h
    rw [← hz, h, map_zero] at hN
    linarith only [hN, hf₀]
  have hlog := hfloor a b ha ha2 (by rw [abs_of_nonneg hb.1]; exact hb.2)
  rw [← hz] at hN hlog
  have him : a * m₀ ≤ (logDeriv XiC z).im := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi]
    simpa using hlog
  change _ ≤ 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re
  rw [kreinCurrent_eq_normSq_mul_logDeriv_im _ _ hne, ← logDeriv_apply]
  have h1 : f₀ * (a * m₀) ≤ Complex.normSq (XiC z) * (logDeriv XiC z).im :=
    mul_le_mul hN him (by positivity) (Complex.normSq_nonneg _)
  nlinarith only [h1]

/-! ## The criterion -/

/-- **The window criterion at every aperture.** There is `D` such that, at every rank `N` and aperture
`0 < a ≤ 3/4`, nonnegativity of the current on `|b| ≤ D (N+1)³` makes the signed section positive definite. -/
theorem exists_signedHankel_posDef_of_current_nonneg : ∃ D : ℝ, 4 ≤ D ∧
    ∀ N : ℕ, ∀ a : ℝ, 0 < a → a ≤ 3 / 4 →
      (∀ b : ℝ, |b| ≤ D * ((N : ℝ) + 1) ^ 3 → 0 ≤ current a b) →
        (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨m, hm, hcore⟩ := exists_current_floor
  obtain ⟨M, K, hM, hK, htail⟩ := tailMoment_le_aperture
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨D, hD, hpayment⟩ := exists_cubic_tail_payment hM hm (zero_lt_one : (0 : ℝ) < 1) hK
    (by positivity : (0 : ℝ) < Real.pi / 8)
  refine ⟨D, hD, fun N a ha0 ha2 hwindow => ?_⟩
  have habs : |a| ≤ 3 / 4 := by rw [abs_of_pos ha0]; exact ha2
  have ha1 : |a| < 1 := habs.trans_lt (by norm_num)
  apply signed_posDef_of_raw ha1 N
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨raw_hermitian a N, fun v hv => ?_⟩
  rw [star_trivial]
  cases N with
  | zero => exact False.elim (hv (Subsingleton.elim v 0))
  | succ n =>
    let T : ℝ := D * (((n + 1 : ℕ) : ℝ) + 1) ^ 3
    have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hD
    have hT : 4 ≤ T := by
      apply hD.trans
      apply le_mul_of_one_le_right hD0.le
      apply one_le_pow₀
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hT0 : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 4).trans hT
    have hrT : (1 : ℝ) ≤ T := (by norm_num : (1 : ℝ) ≤ 4).trans hT
    let B : ℝ := (Nat.factorial (n + 1) : ℝ) * (Nat.factorial (2 * (n + 1)) : ℝ) ^ (n + 1)
    let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := tailHankel a T (n + 1)
    let P : ℝ := (n + 1 : ℕ) * M * K ^ (2 * (n + 1)) * (Nat.factorial (2 * (n + 1)) : ℝ) *
      Real.exp (-((Real.pi / 8) * T))
    have hB : 0 < B := by dsimp only [B]; positivity
    have hpay : B * P ≤ m * 1 ^ (2 * (n + 1) + 1) / 2 := by
      simpa only [B, P, T, mul_assoc] using hpayment (n + 1)
    rw [one_pow, mul_one] at hpay
    have hentry (i j : Fin (n + 1)) :
        |E i j| ≤ a * (M * K ^ (2 * (n + 1)) * (Nat.factorial (2 * (n + 1)) : ℝ) * Real.exp (-((Real.pi / 8) * T))) := by
      have hij : i.val + j.val ≤ 2 * (n + 1) := by omega
      have hp := pow_le_pow_right₀ hK hij
      have hf : (Nat.factorial (i.val + j.val) : ℝ) ≤ (Nat.factorial (2 * (n + 1)) : ℝ) := by
        exact_mod_cast Nat.factorial_le hij
      have hprod := mul_le_mul hp hf (by positivity) (by positivity)
      have h := htail a habs T hT0 (i.val + j.val)
      rw [abs_of_pos ha0] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ ha0.le)
      have hbound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hM.le) (Real.exp_pos (-((Real.pi / 8) * T))).le
      simpa only [mul_assoc] using hbound
    have he := GaloisForLFunctions.HTGeometry.abs_dotProduct_mulVec_le E (by positivity) hentry v
    have he' : |v ⬝ᵥ E *ᵥ v| ≤ a * P * (v ⬝ᵥ v) := by
      convert he using 1
      dsimp only [P]
      ring
    have hnorm : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        (Ne.symm (fun h => hv ((dotProduct_self_eq_zero).mp h)))
    have hsplit : v ⬝ᵥ rawHankel a (n + 1) *ᵥ v =
        v ⬝ᵥ truncatedHankel a T (n + 1) *ᵥ v + v ⬝ᵥ E *ᵥ v := by
      rw [raw_eq_truncated_add_tail a T ha1, Matrix.add_mulVec, dotProduct_add]
    have hsplitB := congrArg (fun q : ℝ => B * q) hsplit
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp he').1 hB.le
    have hpaid := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpay ha0.le) hnorm.le
    have hzero := truncated_current_factorial_floor ha1 (mul_pos ha0 hm) (zero_lt_one : (0 : ℝ) < 1) le_rfl hrT
      (fun b hb => hwindow b hb) (fun b hb => hcore a b ha0 ha2 hb) n v
    rw [one_pow, mul_one] at hzero
    change (a * m) * (v ⬝ᵥ v) ≤ B * (v ⬝ᵥ truncatedHankel a T (n + 1) *ᵥ v) at hzero
    have hfinal : (a * (m / 2)) * (v ⬝ᵥ v) ≤ B * (v ⬝ᵥ rawHankel a (n + 1) *ᵥ v) := by
      nlinarith only [hzero, hlow, hpaid, hsplitB]
    have hpositive : 0 < (a * (m / 2)) * (v ⬝ᵥ v) := by positivity
    exact (mul_pos_iff_of_pos_left hB).mp (hpositive.trans_le hfinal)

end GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar

#print axioms GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar.exists_current_floor
#print axioms GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar.exists_signedHankel_posDef_of_current_nonneg
