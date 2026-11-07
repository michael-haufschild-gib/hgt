import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentTail
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact

/-!
# A sharp tail for the current

**Theorem** (`abs_current_le_sharp`). For `|a| ≤ ½`,

`|current a b| ≤ 3.6·10⁷ · |a| · e^{−(7/5)|b|}`.

The uniform bound `‖Φ(z)‖ ≤ 2770 e^{−2|Re z|}` on `|Im z| ≤ 7/10` is replaced by the exact integral
of the profile of each source term. On the line `Re z = u ≥ 0`, with `X = n² e^{2u}`,

`e^{3u/2} ‖Φₙ(z)‖ ≤ 2π e^{2u} (2πX² + 3X) e^{−0.53 X}`,

which is the `u`-derivative of `−(π/n²) Q(X) e^{−0.53 X}` for an explicit quadratic `Q`. So its
integral over `u > 0` is `(π/n²) Q(n²) e^{−0.53 n²} ≤ (π/n²) Q(1) e^{−0.53}`, and summing over `n`
gives `|Ξ(t + ia)| ≤ 1000 e^{−(7/10)|t|}` on the whole strip `|a| ≤ 3/2`. The wide strip lets
Cauchy's estimate use circles of radius `½`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ThetaCuspSections.ExplicitCollar

open _root_.RHTower CriticalCollar QuantitativeCollar LogarithmicCollar

/-! ## The profile of one term -/

/-- The scaled square `X = n² e^{2u}` of the argument of the Gaussian. -/
def lineX (n : ℕ) (u : ℝ) : ℝ := (n : ℝ) ^ 2 * Real.exp (2 * u)

/-- The profile of the `n`-th source term on the line `Re z = u`, weighted by `e^{3u/2}`. -/
def lineProfile (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (2 * u) * (2 * Real.pi * (2 * Real.pi * lineX n u ^ 2 + 3 * lineX n u) *
    Real.exp (-(0.53 * lineX n u)))

/-- The quadratic with `d/dY [−Q(Y) e^{−0.53 Y}] = (2πY² + 3Y) e^{−0.53 Y}`. -/
def profileQ (Y : ℝ) : ℝ :=
  2 * Real.pi * (Y ^ 2 / 0.53 + 2 * Y / 0.53 ^ 2 + 2 / 0.53 ^ 3) + 3 * (Y / 0.53 + 1 / 0.53 ^ 2)

/-- `Q(Y) e^{−0.53 Y}`, the tail integral of the profile in the variable `Y`. -/
def profileTail (Y : ℝ) : ℝ := profileQ Y * Real.exp (-(0.53 * Y))

theorem lineX_nonneg (n : ℕ) (u : ℝ) : 0 ≤ lineX n u := by
  unfold lineX
  positivity

theorem lineProfile_nonneg (n : ℕ) (u : ℝ) : 0 ≤ lineProfile n u := by
  have := lineX_nonneg n u
  unfold lineProfile
  positivity

theorem continuous_lineProfile (n : ℕ) : Continuous (lineProfile n) := by
  unfold lineProfile lineX
  fun_prop

theorem lineProfile_zero (u : ℝ) : lineProfile 0 u = 0 := by
  simp [lineProfile, lineX]

theorem hasDerivAt_profileTail (Y : ℝ) :
    HasDerivAt profileTail (-((2 * Real.pi * Y ^ 2 + 3 * Y) * Real.exp (-(0.53 * Y)))) Y := by
  have hQ : HasDerivAt profileQ (2 * Real.pi * (2 * Y / 0.53 + 2 / 0.53 ^ 2) + 3 * (1 / 0.53)) Y := by
    have h := ((((hasDerivAt_pow 2 Y).const_mul (2 * Real.pi / 0.53)).add
      ((hasDerivAt_id' Y).const_mul (2 * Real.pi * 2 / 0.53 ^ 2 + 3 / 0.53))).add_const
      (2 * Real.pi * (2 / 0.53 ^ 3) + 3 * (1 / 0.53 ^ 2)))
    have e : profileQ = fun y => 2 * Real.pi / 0.53 * y ^ 2 +
        (2 * Real.pi * 2 / 0.53 ^ 2 + 3 / 0.53) * y + (2 * Real.pi * (2 / 0.53 ^ 3) + 3 * (1 / 0.53 ^ 2)) := by
      funext y
      unfold profileQ
      ring
    rw [e]
    refine h.congr_deriv ?_
    push_cast
    ring
  have hE : HasDerivAt (fun Y : ℝ => Real.exp (-(0.53 * Y))) (Real.exp (-(0.53 * Y)) * -0.53) Y := by
    have := ((hasDerivAt_id Y).const_mul 0.53).neg.exp
    simpa using this
  have h := hQ.mul hE
  refine h.congr_deriv ?_
  unfold profileQ
  ring

theorem profileTail_antitoneOn : AntitoneOn profileTail (Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun Y _ => (hasDerivAt_profileTail Y).continuousAt.continuousWithinAt)
    (fun Y _ => (hasDerivAt_profileTail Y).hasDerivWithinAt) fun Y hY => ?_
  rw [interior_Ici] at hY
  have hY0 : 0 ≤ Y := le_of_lt hY
  have : 0 ≤ (2 * Real.pi * Y ^ 2 + 3 * Y) * Real.exp (-(0.53 * Y)) := by positivity
  linarith only [this]

/-- The antiderivative of the profile. -/
def lineAnti (n : ℕ) (u : ℝ) : ℝ := -(Real.pi / (n : ℝ) ^ 2) * profileTail (lineX n u)

theorem hasDerivAt_lineAnti {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    HasDerivAt (lineAnti n) (lineProfile n u) u := by
  have hn0 : (n : ℝ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hX : HasDerivAt (lineX n) ((n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)) u := by
    unfold lineX
    have := (((hasDerivAt_id u).const_mul 2).exp).const_mul ((n : ℝ) ^ 2)
    simpa using this
  have h := ((hasDerivAt_profileTail (lineX n u)).comp u hX).const_mul (-(Real.pi / (n : ℝ) ^ 2))
  refine h.congr_deriv ?_
  unfold lineProfile lineX
  field_simp
  ring

private theorem tendsto_pow_mul_exp_scaled (k : ℕ) :
    Tendsto (fun Y : ℝ => Y ^ k * Real.exp (-(0.53 * Y))) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) 0.53 (by norm_num)
  refine h.congr' (Eventually.of_forall fun Y => ?_)
  rw [Real.rpow_natCast]
  ring_nf

theorem tendsto_profileTail : Tendsto profileTail atTop (𝓝 0) := by
  have h2 := tendsto_pow_mul_exp_scaled 2
  have h1 := tendsto_pow_mul_exp_scaled 1
  have h0 := tendsto_pow_mul_exp_scaled 0
  have hsum := ((h2.const_mul (2 * Real.pi / 0.53 : ℝ)).add
    (h1.const_mul (2 * Real.pi * 2 / 0.53 ^ 2 + 3 / 0.53 : ℝ))).add
    (h0.const_mul (2 * Real.pi * 2 / 0.53 ^ 3 + 3 / 0.53 ^ 2 : ℝ))
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun Y => ?_)
  unfold profileTail profileQ
  ring

theorem tendsto_lineAnti {n : ℕ} (hn : 1 ≤ n) : Tendsto (lineAnti n) atTop (𝓝 0) := by
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hX : Tendsto (lineX n) atTop atTop := by
    unfold lineX
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul_atTop hn0
  have h := (tendsto_profileTail.comp hX).const_mul (-(Real.pi / (n : ℝ) ^ 2))
  rw [mul_zero] at h
  exact h

theorem integrableOn_lineProfile {n : ℕ} (hn : 1 ≤ n) : IntegrableOn (lineProfile n) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_lineAnti hn 0).continuousAt.continuousWithinAt
    (fun u _ => hasDerivAt_lineAnti hn u) (fun u _ => lineProfile_nonneg n u) (tendsto_lineAnti hn)

/-- The integral of the profile over `u > 0`. -/
theorem integral_lineProfile {n : ℕ} (hn : 1 ≤ n) :
    ∫ u in Ioi (0 : ℝ), lineProfile n u = Real.pi / (n : ℝ) ^ 2 * profileTail ((n : ℝ) ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hasDerivAt_lineAnti hn 0).continuousAt.continuousWithinAt
    (fun u _ => hasDerivAt_lineAnti hn u) (integrableOn_lineProfile hn) (tendsto_lineAnti hn)]
  simp [lineAnti, lineX]

theorem integral_lineProfile_le (n : ℕ) :
    ∫ u in Ioi (0 : ℝ), lineProfile n u ≤ profileTail 1 * (Real.pi * (1 / (n : ℝ) ^ 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lineProfile_zero]
  · rw [integral_lineProfile hn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith only [this]
    have hT := profileTail_antitoneOn (by norm_num : (1 : ℝ) ∈ Ici 0)
      (show (n : ℝ) ^ 2 ∈ Ici 0 from mem_Ici.mpr (by positivity)) h1
    have hc : 0 ≤ Real.pi / (n : ℝ) ^ 2 := by positivity
    calc Real.pi / (n : ℝ) ^ 2 * profileTail ((n : ℝ) ^ 2) ≤ Real.pi / (n : ℝ) ^ 2 * profileTail 1 :=
          mul_le_mul_of_nonneg_left hT hc
      _ = _ := by ring

/-! ## The source on the line `Im z = 7/10` -/

/-- One source term on a line `|Im z| ≤ 7/10`. -/
theorem norm_term_le_profile {z : ℂ} (him : |z.im| ≤ 7 / 10) (n : ℕ) :
    ‖thetaCuspComplexTerm z n‖ ≤ Real.exp (z.re / 2) *
      (2 * Real.pi * (2 * Real.pi * lineX n z.re ^ 2 + 3 * lineX n z.re) *
        Real.exp (-(0.53 * lineX n z.re))) := by
  have hπ := Real.pi_pos
  obtain ⟨X, hXdef⟩ : ∃ X, X = lineX n z.re := ⟨_, rfl⟩
  rw [← hXdef]
  have hX0 : 0 ≤ X := by rw [hXdef]; exact lineX_nonneg n z.re
  have hcos : (0.169 : ℝ) ≤ Real.cos (2 * z.im) := by
    refine cos_seven_fifths_ge.trans ?_
    have h1 := cos_le_cos_of_abs_le (δ := 7 / 10) (y := z.im)
      (by linarith only [Real.pi_gt_d2]) him
    norm_num at h1 ⊢
    exact h1
  have hgauss : ‖Complex.exp (-(Real.pi : ℂ) * ((n : ℂ) * Complex.exp z) ^ 2)‖ ≤
      Real.exp (-(0.53 * X)) := by
    rw [norm_exp_neg_pi_sq]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0.53 ≤ Real.pi * Real.cos (2 * z.im) := by
      have h2 := mul_le_mul Real.pi_gt_d2.le hcos (by norm_num) hπ.le
      norm_num at h2 ⊢
      linarith only [h2]
    have h3 := mul_le_mul_of_nonneg_right h1 hX0
    rw [hXdef, lineX] at h3 ⊢
    nlinarith only [h3]
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (n : ℂ) * Complex.exp z := ⟨_, rfl⟩
  have hnw : ‖w‖ ^ 2 = X := by
    rw [hw, norm_mul, Complex.norm_natCast, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul,
      hXdef, lineX]
    norm_num
  have hpoly : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ ≤
      2 * Real.pi * (2 * Real.pi * X ^ 2 + 3 * X) := by
    have h1 : ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ ≤ 2 * Real.pi * X ^ 2 + 3 * X := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
      have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have e3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [e2, e3, ← hnw]
      apply le_of_eq
      ring
    rw [norm_mul]
    have h2 : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hπ]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  unfold thetaCuspComplexTerm thetaCuspComplexSeed
  rw [norm_mul, norm_mul, ← hw]
  have he : ‖Complex.exp (z / 2)‖ = Real.exp (z.re / 2) := by
    rw [Complex.norm_exp]
    simp
  rw [he]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hg := hgauss
  rw [← hw] at hg
  exact mul_le_mul hpoly hg (norm_nonneg _) (by positivity)

theorem summable_lineProfile (u : ℝ) : Summable fun n : ℕ => lineProfile n u := by
  have hσ : 0 < 0.53 * Real.exp (2 * u) := by positivity
  have h4 := summable_pow_mul_exp_neg_nat_sq 4 hσ
  have h2 := summable_pow_mul_exp_neg_nat_sq 2 hσ
  refine ((h4.mul_left (Real.exp (2 * u) * (2 * Real.pi) * (2 * Real.pi) * Real.exp (2 * u) ^ 2)).add
    (h2.mul_left (Real.exp (2 * u) * (2 * Real.pi) * 3 * Real.exp (2 * u)))).congr fun n => ?_
  unfold lineProfile lineX
  have e : -(0.53 * Real.exp (2 * u)) * (n : ℝ) ^ 2 = -(0.53 * ((n : ℝ) ^ 2 * Real.exp (2 * u))) := by
    ring
  rw [e]
  ring

/-- The weighted source on the line `Im z = 7/10` is dominated by the summed profile at `|x|`. -/
theorem exp_mul_norm_source_line_le (x : ℝ) :
    Real.exp (3 / 2 * |x|) * ‖thetaCuspStripSource ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ ≤
      ∑' n : ℕ, lineProfile n |x| := by
  obtain ⟨z, hz, hzre, hzim⟩ : ∃ z : ℂ,
      thetaCuspStripSource ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I) = thetaCuspStripSource z ∧
        z.re = |x| ∧ |z.im| ≤ 7 / 10 := by
    rcases le_or_gt 0 x with hx | hx
    · refine ⟨(x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I, rfl, ?_, ?_⟩
      · simp [abs_of_nonneg hx]
      · simp; norm_num [abs_of_pos]
    · have hmem : (x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I ∈ thetaCuspStrip := by
        rw [thetaCuspStrip, Set.mem_setOf_eq]
        simp
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 10)]
        linarith only [Real.pi_gt_d2]
      refine ⟨-((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I), (thetaCuspStripSource_neg hmem).symm, ?_, ?_⟩
      · simp [abs_of_neg hx]
      · simp; norm_num [abs_of_pos]
  rw [hz]
  have hbd : ∀ n : ℕ, Real.exp (3 / 2 * |x|) * ‖thetaCuspComplexTerm z n‖ ≤ lineProfile n |x| := by
    intro n
    have h := norm_term_le_profile hzim n
    rw [hzre] at h
    have e : Real.exp (3 / 2 * |x|) * Real.exp (|x| / 2) = Real.exp (2 * |x|) := by
      rw [← Real.exp_add]
      ring_nf
    calc Real.exp (3 / 2 * |x|) * ‖thetaCuspComplexTerm z n‖
        ≤ Real.exp (3 / 2 * |x|) * (Real.exp (|x| / 2) *
            (2 * Real.pi * (2 * Real.pi * lineX n |x| ^ 2 + 3 * lineX n |x|) *
              Real.exp (-(0.53 * lineX n |x|)))) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = lineProfile n |x| := by
          rw [← mul_assoc, e]
          rfl
  have hE := Real.exp_pos (3 / 2 * |x|)
  have hnorm : Summable fun n : ℕ => ‖thetaCuspComplexTerm z n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_lineProfile |x|).mul_left (Real.exp (3 / 2 * |x|))⁻¹)
    rw [le_inv_mul_iff₀ hE]
    exact hbd n
  calc Real.exp (3 / 2 * |x|) * ‖thetaCuspStripSource z‖
      ≤ Real.exp (3 / 2 * |x|) * ∑' n : ℕ, ‖thetaCuspComplexTerm z n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hE.le
    _ = ∑' n : ℕ, Real.exp (3 / 2 * |x|) * ‖thetaCuspComplexTerm z n‖ := by rw [tsum_mul_left]
    _ ≤ _ := (hnorm.mul_left _).tsum_le_tsum hbd (summable_lineProfile |x|)

/-! ## The integral of the summed profile -/

private theorem integrable_comp_abs_of_Ioi {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable fun x : ℝ => f |x| := by
  have h1 : IntegrableOn (fun x : ℝ => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h1
  have h := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integrable_lineProfile_abs (n : ℕ) : Integrable fun x : ℝ => lineProfile n |x| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lineProfile_zero]
  · exact integrable_comp_abs_of_Ioi (integrableOn_lineProfile hn)

theorem integral_lineProfile_abs_le (n : ℕ) :
    ∫ x : ℝ, lineProfile n |x| ≤ 2 * profileTail 1 * (Real.pi * (1 / (n : ℝ) ^ 2)) := by
  rw [integral_comp_abs (f := lineProfile n)]
  have := integral_lineProfile_le n
  linarith only [this]

/-- `2π Q(1) e^{−0.53} · π²/6 ≤ 1000`. -/
private theorem profile_constant_le :
    2 * profileTail 1 * (Real.pi * (Real.pi ^ 2 / 6)) ≤ 1000 := by
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have he : Real.exp (-(0.53 * (1 : ℝ))) ≤ 1 / 1.67045 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.53)
    rw [mul_one, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h ⊢
    linarith only [h]
  have he0 := Real.exp_pos (-(0.53 * (1 : ℝ)))
  have hQ : profileQ 1 ≤ 2 * 3.1416 * 22.44068 + 16.34034 := by
    unfold profileQ
    norm_num
    nlinarith only [hπ, hπ0]
  have hQ0 : 0 ≤ profileQ 1 := by unfold profileQ; positivity
  unfold profileTail
  have h1 : profileQ 1 * Real.exp (-(0.53 * (1 : ℝ))) ≤
      (2 * 3.1416 * 22.44068 + 16.34034) * (1 / 1.67045) :=
    mul_le_mul hQ he he0.le (by norm_num)
  have h2 : Real.pi * (Real.pi ^ 2 / 6) ≤ 3.1416 * (3.1416 ^ 2 / 6) := by
    have := pow_le_pow_left₀ hπ0.le hπ.le 2
    nlinarith only [this, hπ, hπ0]
  have h3 := mul_le_mul h1 h2 (by positivity) (by norm_num)
  norm_num at h3 ⊢
  nlinarith only [h3]

/-- **The integral of the summed profile.** -/
theorem integrable_and_integral_sum_lineProfile_le :
    Integrable (fun x : ℝ => ∑' n : ℕ, lineProfile n |x|) ∧
      ∫ x : ℝ, ∑' n : ℕ, lineProfile n |x| ≤ 1000 := by
  have hnn (n : ℕ) (x : ℝ) : 0 ≤ lineProfile n |x| := lineProfile_nonneg n |x|
  have hint (n : ℕ) : ∫ x : ℝ, ‖lineProfile n |x|‖ = ∫ x : ℝ, lineProfile n |x| := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hnn n x)]
  have hmaj : Summable fun n : ℕ => 2 * profileTail 1 * (Real.pi * (1 / (n : ℝ) ^ 2)) :=
    (hasSum_zeta_two.summable.mul_left Real.pi).mul_left _
  have hI0 (n : ℕ) : 0 ≤ ∫ x : ℝ, lineProfile n |x| := integral_nonneg (hnn n)
  have hsum : Summable fun n : ℕ => ∫ x : ℝ, ‖lineProfile n |x|‖ := by
    simp_rw [hint]
    exact Summable.of_nonneg_of_le hI0 integral_lineProfile_abs_le hmaj
  have hHas := hasSum_integral_of_summable_integral_norm integrable_lineProfile_abs hsum
  have hval : ∫ x : ℝ, ∑' n : ℕ, lineProfile n |x| ≤ 1000 := by
    rw [← hHas.tsum_eq]
    refine (Summable.tsum_le_tsum integral_lineProfile_abs_le
      (Summable.of_nonneg_of_le hI0 integral_lineProfile_abs_le hmaj) hmaj).trans ?_
    rw [tsum_mul_left, tsum_mul_left, hasSum_zeta_two.tsum_eq]
    have := profile_constant_le
    linarith only [this]
  refine ⟨?_, hval⟩
  by_contra hni
  have h0 := hHas
  rw [integral_undef hni] at h0
  have hzero := (hasSum_zero_iff_of_nonneg hI0).mp h0
  have h1 := congrFun hzero 1
  have hpos : 0 < ∫ x : ℝ, lineProfile 1 |x| := by
    rw [integral_comp_abs (f := lineProfile 1), integral_lineProfile le_rfl]
    have hT : 0 < profileTail 1 := by
      unfold profileTail profileQ
      positivity
    have e : ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [e]
    have := Real.pi_pos
    positivity
  simp only [Pi.zero_apply] at h1
  linarith only [h1, hpos]

/-! ## `Ξ` on the wide strip -/

/-- `|Ξ(t + ia)| ≤ 1000 e^{−(7/10)|t|}` for `|a| ≤ 3/2`. -/
theorem norm_XiC_le_wide (t a : ℝ) (ha : |a| ≤ 3 / 2) :
    ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 1000 * Real.exp (-(7 / 10 * |t|)) := by
  obtain ⟨hGi, hGv⟩ := integrable_and_integral_sum_lineProfile_le
  have hcore : ∀ t a : ℝ, t ≤ 0 → |a| ≤ 3 / 2 →
      ‖XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 1000 * Real.exp (-(7 / 10 * |t|)) := by
    intro t a ht ha
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (t : ℂ) + (a : ℂ) * I := ⟨_, rfl⟩
    have hwre : w.re = t := by rw [hw]; simp
    have hwim : w.im = a := by rw [hw]; simp
    rw [← hw]
    have hax (y : ℝ) : a * y ≤ 3 / 2 * |y| :=
      calc a * y ≤ |a * y| := le_abs_self _
        _ = |a| * |y| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    -- The decay needed for the contour shift.
    have hbound : ∀ z : ℂ, |z.im| ≤ 7 / 10 →
        ‖thetaStripKernel w z‖ ≤ (2770 * Real.exp (|t| * (7 / 10))) *
          Real.exp (-(1 / 2 * |z.re|)) := by
      intro z hz
      rw [norm_thetaStripKernel, hwre, hwim]
      have hK := norm_source_le hz
      have htz : t * z.im ≤ |t| * (7 / 10) :=
        calc t * z.im ≤ |t * z.im| := le_abs_self _
          _ = |t| * |z.im| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg t)
      have hexp : Real.exp (t * z.im + a * z.re) ≤
          Real.exp (|t| * (7 / 10)) * Real.exp (3 / 2 * |z.re|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith only [htz, hax z.re])
      calc Real.exp (t * z.im + a * z.re) * ‖thetaCuspStripSource z‖
          ≤ (Real.exp (|t| * (7 / 10)) * Real.exp (3 / 2 * |z.re|)) *
              (2770 * Real.exp (-(2 * |z.re|))) := mul_le_mul hexp hK (norm_nonneg _) (by positivity)
        _ = (2770 * Real.exp (|t| * (7 / 10))) *
              (Real.exp (3 / 2 * |z.re|) * Real.exp (-(2 * |z.re|))) := by ring
        _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
    have hdiff : ∀ z : ℂ, |z.im| ≤ 7 / 10 → DifferentiableAt ℂ (thetaStripKernel w) z := by
      intro z hz
      refine differentiableAt_thetaStripKernel w ?_
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      linarith only [hz, Real.pi_gt_d2]
    have hshift := integral_horizontal_shift_of_decay (F := thetaStripKernel w) (c := 7 / 10)
      (C := 2770 * Real.exp (|t| * (7 / 10))) (r := 1 / 2) (by norm_num) (by norm_num) hdiff hbound
    have hFL : (∫ x : ℝ, thetaStripKernel w ((x : ℝ) : ℂ)) = XiC w := by
      rw [integral_thetaStripKernel_real, thetaCuspFourierLaplace_eq_XiC_all]
    rw [← hFL, ← hshift]
    -- The line bound.
    have hline : ∀ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ ≤
        Real.exp (t * (7 / 10)) * ∑' n : ℕ, lineProfile n |x| := by
      intro x
      have hre : ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).re = x := by simp
      have him : ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).im = 7 / 10 := by simp
      rw [norm_thetaStripKernel, hwre, hwim, hre, him]
      have hS := exp_mul_norm_source_line_le x
      have hexp : Real.exp (t * (7 / 10) + a * x) ≤
          Real.exp (t * (7 / 10)) * Real.exp (3 / 2 * |x|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith only [hax x])
      calc Real.exp (t * (7 / 10) + a * x) *
            ‖thetaCuspStripSource ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖
          ≤ (Real.exp (t * (7 / 10)) * Real.exp (3 / 2 * |x|)) *
              ‖thetaCuspStripSource ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ :=
            mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
        _ = Real.exp (t * (7 / 10)) * (Real.exp (3 / 2 * |x|) *
              ‖thetaCuspStripSource ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.exp_pos _).le
    have hcont : Continuous fun x : ℝ => thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I) := by
      refine continuous_iff_continuousAt.mpr fun x => ?_
      have hmem : |((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I).im| ≤ 7 / 10 := by
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add,
          add_zero]
        norm_num [abs_of_pos]
      have hcomp := ((hdiff _ hmem).continuousAt).comp (x := x)
        (f := fun y : ℝ => ((y : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)) (by fun_prop)
      simpa [Function.comp_def] using hcomp
    have hmaj : Integrable fun x : ℝ => Real.exp (t * (7 / 10)) * ∑' n : ℕ, lineProfile n |x| :=
      hGi.const_mul _
    calc ‖∫ x : ℝ, thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖
        ≤ ∫ x : ℝ, ‖thetaStripKernel w ((x : ℂ) + ((7 / 10 : ℝ) : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, Real.exp (t * (7 / 10)) * ∑' n : ℕ, lineProfile n |x| := by
          refine integral_mono ?_ hmaj hline
          exact hmaj.mono' hcont.norm.aestronglyMeasurable
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
              exact hline x)
      _ = Real.exp (t * (7 / 10)) * ∫ x : ℝ, ∑' n : ℕ, lineProfile n |x| := integral_const_mul _ _
      _ ≤ Real.exp (t * (7 / 10)) * 1000 := mul_le_mul_of_nonneg_left hGv (Real.exp_pos _).le
      _ = _ := by
          rw [abs_of_nonpos ht, mul_comm]
          congr 2
          ring
  rcases le_or_gt t 0 with ht | ht
  · exact hcore t a ht ha
  · have heven : XiC ((t : ℂ) + (a : ℂ) * I) = XiC (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I) := by
      rw [show (((-t : ℝ) : ℂ) + ((-a : ℝ) : ℂ) * I) = -((t : ℂ) + (a : ℂ) * I) by push_cast; ring,
        XiC_even]
    rw [heven]
    have h := hcore (-t) (-a) (by linarith only [ht]) (by rwa [abs_neg])
    rwa [abs_neg] at h

/-! ## Derivatives and the current -/

private theorem exp_seven_twentieths_le : Real.exp (7 / 10 * (1 / 2)) ≤ 1.48 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := 7 / 10 * (1 / 2)) (by norm_num [abs_of_pos])
  have h2 := (abs_le.mp h).2
  norm_num at h2 ⊢
  linarith only [h2]

/-- `Ξ'` on `|a| ≤ 1`. -/
theorem norm_deriv_XiC_le_wide (t a : ℝ) (ha : |a| ≤ 1) :
    ‖deriv XiC ((t : ℂ) + (a : ℂ) * I)‖ ≤ 2960 * Real.exp (-(7 / 10 * |t|)) := by
  have h := norm_deriv_le_of_strip XiC_differentiable (C := 1000) (δ := 7 / 10) (A := 3 / 2)
    (ρ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) norm_XiC_le_wide t a
    (by norm_num at ha ⊢; linarith only [ha])
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hs := exp_seven_twentieths_le
  rw [div_le_iff₀ (by norm_num)]
  nlinarith only [hs]

/-- `Ξ''` on `|a| ≤ ½`. -/
theorem norm_deriv_deriv_XiC_le_wide (t a : ℝ) (ha : |a| ≤ 1 / 2) :
    ‖deriv (deriv XiC) ((t : ℂ) + (a : ℂ) * I)‖ ≤ 8762 * Real.exp (-(7 / 10 * |t|)) := by
  have hd : Differentiable ℂ (deriv XiC) :=
    fun z => ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  have h := norm_deriv_le_of_strip hd (C := 2960) (δ := 7 / 10) (A := 1) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) norm_deriv_XiC_le_wide t a
    (by norm_num at ha ⊢; linarith only [ha])
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hs := exp_seven_twentieths_le
  rw [div_le_iff₀ (by norm_num)]
  nlinarith only [hs]

/-- **The sharp tail of the current.** -/
theorem abs_current_le_sharp {a : ℝ} (ha : |a| ≤ 1 / 2) (b : ℝ) :
    |current a b| ≤ 36000000 * |a| * Real.exp (-(7 / 5 * |b|)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Real.exp (-(7 / 10 * |b|)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.exp_pos _
  have hgg : Real.exp (-(7 / 5 * |b|)) = g * g := by
    rw [hg, ← Real.exp_add]
    congr 1
    ring
  have hd : Differentiable ℂ (deriv XiC) :=
    fun z => ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (b : ℂ) - (a : ℂ) * I := ⟨_, rfl⟩
  have hzform : z = (b : ℂ) + ((-a : ℝ) : ℂ) * I := by
    rw [hz]
    push_cast
    ring
  have hU : ‖XiC z - XiC (b : ℂ)‖ ≤ 2960 * g * |a| := by
    rw [hz]
    refine norm_sub_vertical_le XiC_differentiable fun a' ha' => ?_
    rw [hg]
    exact norm_deriv_XiC_le_wide b a' (ha'.trans (ha.trans (by norm_num)))
  have hV : ‖deriv XiC z - deriv XiC (b : ℂ)‖ ≤ 8762 * g * |a| := by
    rw [hz]
    refine norm_sub_vertical_le hd fun a' ha' => ?_
    rw [hg]
    exact norm_deriv_deriv_XiC_le_wide b a' (ha'.trans ha)
  have hv : ‖deriv XiC z‖ ≤ 2960 * g := by
    rw [hzform, hg]
    exact norm_deriv_XiC_le_wide b (-a) (by rw [abs_neg]; exact ha.trans (by norm_num))
  have hu₀ : ‖XiC (b : ℂ)‖ ≤ 1000 * g := by
    have h := norm_XiC_le_wide b 0 (by norm_num)
    simpa [hg] using h
  have hdiff := current_difference_le (XiC (b : ℂ)) (XiC z) (deriv XiC (b : ℂ)) (deriv XiC z)
  have hrew : current a b = 2 * ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z)).re := by
    rw [hz]
    rfl
  have hrew₀ : 2 * ((starRingEnd ℂ) (XiC (b : ℂ)) * (-I * deriv XiC (b : ℂ))).re = 0 := by
    have h := current_zero b
    have hz0 : ((b : ℂ) - ((0 : ℝ) : ℂ) * I) = (b : ℂ) := by simp
    rw [current, hz0] at h
    exact h
  rw [hrew₀, sub_zero, ← hrew] at hdiff
  have habs := abs_nonneg a
  have h1 := mul_le_mul hU hv (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul hu₀ hV (norm_nonneg _) (by positivity)
  rw [hgg]
  have hpos : 0 ≤ |a| * (g * g) := by positivity
  nlinarith only [hdiff, h1, h2, hpos]

end GaloisForLFunctions.ThetaCuspSections.ExplicitCollar
