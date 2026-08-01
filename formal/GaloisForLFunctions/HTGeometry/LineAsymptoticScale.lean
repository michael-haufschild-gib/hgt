import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational

/-!
# The asymptotic scale of a vertical line

Decay on a vertical line, measured against the powers of the point itself: `IsLineBigO σ k f` says
`‖f(t)‖ ≤ C‖σ+it‖^{-k}` for large `t`.  This is the scale in which the digamma jets have their
asymptotic expansions, and it is a graded ring: orders add under multiplication, the smaller order
absorbs the larger, and a positive order forces decay to zero.

The extraction lemma is the point of the scale: a function whose difference from `c·s^{-k}` is one
order smaller has `s^k f(s) → c`, so the coefficient of an expansion is exactly the residue in the
sense used by the projective boundary law, and is therefore unique.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- `f` decays at least like the `k`-th inverse power of the point of the vertical line. -/
def IsLineBigO (σ : ℝ) (k : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ C : ℝ, ∀ᶠ t : ℝ in atTop, ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k ≤ C

theorem eventually_one_le_norm_vertical (σ : ℝ) :
    ∀ᶠ t : ℝ in atTop, (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
  (tendsto_norm_vertical σ).eventually_ge_atTop 1

theorem isLineBigO_const (σ : ℝ) (c : ℂ) : IsLineBigO σ 0 (fun _ => c) :=
  ⟨‖c‖, Eventually.of_forall fun t => by simp⟩

theorem IsLineBigO.add {k : ℕ} {f g : ℝ → ℂ} (hf : IsLineBigO σ k f) (hg : IsLineBigO σ k g) :
    IsLineBigO σ k (fun t => f t + g t) := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  have hpow : (0 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k := by positivity
  calc ‖f t + g t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
      ≤ (‖f t‖ + ‖g t‖) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) hpow
    _ = ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
        + ‖g t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k := by ring
    _ ≤ C₁ + C₂ := add_le_add ht₁ ht₂

theorem IsLineBigO.neg {k : ℕ} {f : ℝ → ℂ} (hf : IsLineBigO σ k f) :
    IsLineBigO σ k (fun t => -f t) := by
  obtain ⟨C, h⟩ := hf
  exact ⟨C, by filter_upwards [h] with t ht using by simpa using ht⟩

theorem IsLineBigO.sub {k : ℕ} {f g : ℝ → ℂ} (hf : IsLineBigO σ k f) (hg : IsLineBigO σ k g) :
    IsLineBigO σ k (fun t => f t - g t) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem IsLineBigO.mul {k l : ℕ} {f g : ℝ → ℂ} (hf : IsLineBigO σ k f) (hg : IsLineBigO σ l g) :
    IsLineBigO σ (k + l) (fun t => f t * g t) := by
  obtain ⟨C₁, h₁⟩ := hf
  obtain ⟨C₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, ?_⟩
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  have hf0 : (0 : ℝ) ≤ ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k := by positivity
  have hg0 : (0 : ℝ) ≤ ‖g t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ l := by positivity
  calc ‖f t * g t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + l)
      = (‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k)
        * (‖g t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ l) := by
        rw [norm_mul, pow_add]; ring
    _ ≤ C₁ * C₂ := mul_le_mul ht₁ ht₂ hg0 (le_trans hf0 ht₁)

theorem IsLineBigO.const_mul {k : ℕ} {f : ℝ → ℂ} (c : ℂ) (hf : IsLineBigO σ k f) :
    IsLineBigO σ k (fun t => c * f t) := by
  have := (isLineBigO_const σ c).mul hf
  simpa using this

/-- A larger order absorbs a smaller one. -/
theorem IsLineBigO.mono {k l : ℕ} {f : ℝ → ℂ} (hkl : k ≤ l) (hf : IsLineBigO σ l f) :
    IsLineBigO σ k f := by
  obtain ⟨C, h⟩ := hf
  refine ⟨max C 0, ?_⟩
  filter_upwards [h, eventually_one_le_norm_vertical σ] with t ht h1
  have hmono : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ l :=
    pow_le_pow_right₀ h1 hkl
  have hnn : (0 : ℝ) ≤ ‖f t‖ := norm_nonneg _
  calc ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
      ≤ ‖f t‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ l := mul_le_mul_of_nonneg_left hmono hnn
    _ ≤ C := ht
    _ ≤ max C 0 := le_max_left _ _

/-- A positive order forces decay to zero along the line. -/
theorem IsLineBigO.tendsto_zero {k : ℕ} {f : ℝ → ℂ} (hf : IsLineBigO σ (k + 1) f) :
    Tendsto f atTop (nhds 0) := by
  obtain ⟨C, h⟩ := hf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
  · filter_upwards [h, eventually_one_le_norm_vertical σ, eventually_gt_atTop (0 : ℝ)]
      with t ht h1 ht0
    have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      calc t = |((σ : ℂ) + (t : ℂ) * Complex.I).im| := by rw [him, abs_of_nonneg ht0.le]
        _ ≤ _ := Complex.abs_im_le_norm _
    have hpow : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k * t
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    have hnn : (0 : ℝ) ≤ ‖f t‖ := norm_nonneg _
    have hstep : ‖f t‖ * t ≤ C := by
      have h1' : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k := one_le_pow₀ h1
      have hA : ‖f t‖ * t ≤ ‖f t‖ * (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k * t) := by
        nlinarith [mul_nonneg hnn ht0.le]
      have hB := mul_le_mul_of_nonneg_left hpow hnn
      linarith
    rw [le_div_iff₀ ht0]
    linarith

/-- **The extraction lemma.**  If `f` differs from `c·s^{-k}` by one order more, then `s^k f(s) → c`:
the coefficient of an expansion is the residue against the corresponding monomial. -/
theorem tendsto_pow_mul_of_isLineBigO {k : ℕ} {f : ℝ → ℂ} {c : ℂ}
    (h : IsLineBigO σ (k + 1)
      (fun t => f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k)) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t) atTop (nhds c) := by
  have hdiff : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k
      * (f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k)) atTop (nhds 0) := by
    obtain ⟨C, hC⟩ := h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      calc t = |((σ : ℂ) + (t : ℂ) * Complex.I).im| := by rw [him, abs_of_nonneg ht0.le]
        _ ≤ _ := Complex.abs_im_le_norm _
    have hnn : (0 : ℝ) ≤ ‖f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k‖ := norm_nonneg _
    rw [norm_mul, norm_pow, le_div_iff₀ ht0]
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
          * ‖f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k‖ * t
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k
          * ‖f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k‖
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
          refine mul_le_mul_of_nonneg_left hge ?_
          positivity
      _ = ‖f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k‖
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ C := ht
  have hconst : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k
      * (c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k)) atTop (nhds c) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_vertical_ne_zero σ] with t ht
    rw [← mul_assoc, mul_right_comm, ← mul_pow, mul_inv_cancel₀ ht, one_pow, one_mul]
  have hsum := hdiff.add hconst
  rw [zero_add] at hsum
  refine hsum.congr fun t => ?_
  ring

/-- The coefficient in the extraction lemma is unique. -/
theorem isLineBigO_coeff_unique {k : ℕ} {f : ℝ → ℂ} {c d : ℂ}
    (hc : IsLineBigO σ (k + 1) (fun t => f t - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k))
    (hd : IsLineBigO σ (k + 1) (fun t => f t - d * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ k)) :
    c = d :=
  tendsto_nhds_unique (tendsto_pow_mul_of_isLineBigO hc) (tendsto_pow_mul_of_isLineBigO hd)

/-- A convergent normalized limit gives the corresponding decay order. -/
theorem isLineBigO_of_tendsto {k : ℕ} {f : ℝ → ℂ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t) atTop (nhds c)) :
    IsLineBigO σ k f := by
  refine ⟨‖c‖ + 1, ?_⟩
  have hball := h.eventually (Metric.ball_mem_nhds c one_pos)
  filter_upwards [hball] with t ht
  have hnorm : ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t‖ < ‖c‖ + 1 := by
    have := mem_ball_iff_norm.mp ht
    calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t‖
        ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t - c‖ + ‖c‖ := by
          simpa using norm_add_le (((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * f t - c) c
      _ < 1 + ‖c‖ := by linarith
      _ = ‖c‖ + 1 := by ring
  rw [norm_mul, norm_pow] at hnorm
  linarith [hnorm, le_of_eq (mul_comm (‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k) ‖f t‖)]

/-- Powers of a decaying function decay at the multiplied order. -/
theorem IsLineBigO.pow {k : ℕ} {f : ℝ → ℂ} (hf : IsLineBigO σ k f) (n : ℕ) :
    IsLineBigO σ (k * n) (fun t => f t ^ n) := by
  induction n with
  | zero => simpa using isLineBigO_const σ 1
  | succ n ih =>
    have hmul := ih.mul hf
    have hfun : (fun t : ℝ => f t ^ n * f t) = fun t : ℝ => f t ^ (n + 1) := by
      funext t
      rw [pow_succ]
    rw [hfun] at hmul
    have hidx : k * n + k = k * (n + 1) := by ring
    rwa [hidx] at hmul

end GaloisForLFunctions
