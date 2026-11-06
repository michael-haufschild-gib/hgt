import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCrowdOfTheInnerField

/-!
# The arithmetic Carleson measure

The Carleson measure of `ζ` is `μ = Σ_ρ m_ρ b_ρ δ_ρ`, `b_ρ = Re ρ − ½`, on the right half-plane. The inner field controls it at every scale, with no loss in the depth.

* **Boxes** (`sum_depth_box_le`). On the box `b ≤ x`, `|γ − t| ≤ x`: `μ(box) ≤ (5/2) x I(½ + x + it)`. So the Carleson norm at scale `x` is the inner field at width `x`.
* **The kernel test** (`sum_carleson_test_le`). `Σ_ρ m_ρ 2xb_ρ/|ρ + w̄ − 1|² ≤ I(w)`.
* **Inner mass at infinity is the depth density** (`tendsto_innerField_iff_depthDensity`, `bounded_innerField_iff_depthDensity`).
  As `x → ∞`, `I(½ + x + it) → 0` iff `Σ_{|γ−t|≤T} m_ρ b_ρ = o(T)`, and `I` stays bounded iff this sum is `O(T)`. For an Euler column the limit is the Mahler measure; for `ζ` the vanishing is a statement between
  density theorems and RH. It does not depend on the height `t` (`tendsto_innerField_congr`).
* **The embedding at scale `x`** (`carleson_embedding`, `shiftedCrowd_le_innerField`). For an entire `A` of quadratic growth, shifting the zeros by `x`,

  `Σ_ρ m_ρ (b_ρ/(b_ρ + x)) |A(ρ + x)|² ≤ ∫ |A(½ + iτ)|² ν_x(τ) dτ`, with `ν_x(τ) ≤ I(½ + x + iτ)/(2πx)`.

  At the critical scale `x ≍ 1/log T` zeros of depth `≥ x` carry weight at least `½`, and all arithmetic is in the coefficients of `A`: this is a large sieve for zeros with the inner field as constant.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The centre at width `x` and height `t`. -/
def centre (x t : ℝ) : ℂ := ((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * I

theorem centre_re (x t : ℝ) : (centre x t).re = 1 / 2 + x := by simp [centre]

theorem centre_im (x t : ℝ) : (centre x t).im = t := by simp [centre]

/-- The depth of a zero. -/
def depth (ρ : ℂ) : ℝ := ρ.re - 1 / 2

/-- The Carleson box of width `x` at height `t`. -/
def InCarlesonBox (x t : ℝ) (ρ : ℂ) : Prop := ρ.re - 1 / 2 ≤ x ∧ |ρ.im - t| ≤ x

theorem zetaEntire_centre_ne_zero {x : ℝ} (hx : 1 / 2 ≤ x) (t : ℝ) : zetaEntire (centre x t) ≠ 0 := by
  rw [Ne, zetaEntire_eq_zero_iff]
  exact riemannZeta_ne_zero_of_one_le_re (by rw [centre_re]; linarith)

theorem depth_le_half (ρ : ZetaRightZero) : depth ρ ≤ 1 / 2 := by
  have h : (ρ : ℂ).re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) ρ.2.1
  simp only [depth]
  linarith

theorem depth_pos (ρ : ZetaRightZero) : 0 < depth ρ := by
  have := ρ.2.2
  simp only [depth]
  linarith

theorem ne_centre {x t : ℝ} (h0 : zetaEntire (centre x t) ≠ 0) (a : ZetaRightZero) :
    (a : ℂ) ≠ centre x t := fun h => by
  apply h0
  rw [← h, zetaEntire_eq_zero_iff]
  exact a.2.1

/-- `|ρ + w̄ − 1|² = (b + x)² + (γ − t)²` at the centre `w = ½ + x + it`. -/
theorem sq_norm_add_conj_centre (x t : ℝ) (ρ : ℂ) :
    ‖ρ + conj (centre x t) - 1‖ ^ 2 = (depth ρ + x) ^ 2 + (ρ.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.sub_im,
    Complex.add_im, Complex.conj_im, Complex.one_im, centre_re, centre_im, depth]
  ring

/-- The inner field dominates any finite part of its Green sum. -/
theorem sum_mul_greenKernel_le {x t : ℝ} (hx : 0 < x) (h0 : zetaEntire (centre x t) ≠ 0)
    (Z : Finset ZetaRightZero) :
    ∑ ρ ∈ Z, zeroMult ρ * greenKernel (centre x t) ρ ≤ innerField (centre x t) := by
  have hw : 1 / 2 < (centre x t).re := by rw [centre_re]; linarith
  have hsum := hasSum_innerField hw h0
  exact sum_le_hasSum Z (fun a _ => mul_nonneg (zeroMult_pos a).le
    (greenKernel_pos hw a.2.2 (ne_centre h0 a)).le) hsum

/-- **The kernel test of the Carleson measure.** -/
theorem sum_carleson_test_le {x t : ℝ} (hx : 0 < x) (h0 : zetaEntire (centre x t) ≠ 0)
    (Z : Finset ZetaRightZero) :
    ∑ ρ ∈ Z, zeroMult ρ * (2 * x * depth ρ / ((depth ρ + x) ^ 2 + ((ρ : ℂ).im - t) ^ 2)) ≤
      innerField (centre x t) := by
  have hw : 1 / 2 < (centre x t).re := by rw [centre_re]; linarith
  refine le_trans (Finset.sum_le_sum fun ρ _ => ?_) (sum_mul_greenKernel_le hx h0 Z)
  refine mul_le_mul_of_nonneg_left ?_ (zeroMult_pos ρ).le
  have h1 := greenKernel_ge hw ρ.2.2 (ne_centre h0 ρ)
  rw [sq_norm_add_conj_centre, centre_re] at h1
  have e : 1 / 2 + x - 1 / 2 = x := by ring
  rw [e] at h1
  exact h1

/-- **Boxes.** `μ(box) ≤ (5/2) x I(½ + x + it)`. -/
theorem sum_depth_box_le {x t : ℝ} (hx : 0 < x) (h0 : zetaEntire (centre x t) ≠ 0)
    (Z : Finset ZetaRightZero) (hZ : ∀ ρ ∈ Z, InCarlesonBox x t ρ) :
    ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ (5 / 2) * x * innerField (centre x t) := by
  have h := sum_carleson_test_le hx h0 Z
  have hle : ∑ ρ ∈ Z, zeroMult ρ * (2 / (5 * x) * depth ρ) ≤
      ∑ ρ ∈ Z, zeroMult ρ * (2 * x * depth ρ / ((depth ρ + x) ^ 2 + ((ρ : ℂ).im - t) ^ 2)) := by
    refine Finset.sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left ?_ (zeroMult_pos ρ).le
    obtain ⟨h1, h2⟩ := hZ ρ hρ
    have hb := depth_pos ρ
    have h1' : depth ρ ≤ x := h1
    have h3 : ((ρ : ℂ).im - t) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hden : (depth ρ + x) ^ 2 + ((ρ : ℂ).im - t) ^ 2 ≤ 5 * x ^ 2 := by nlinarith
    have hdpos : 0 < (depth ρ + x) ^ 2 + ((ρ : ℂ).im - t) ^ 2 := by positivity
    rw [le_div_iff₀ hdpos]
    have e : 2 / (5 * x) * depth ρ * (5 * x ^ 2) = 2 * x * depth ρ := by
      field_simp
    have h4 : 2 / (5 * x) * depth ρ * ((depth ρ + x) ^ 2 + ((ρ : ℂ).im - t) ^ 2) ≤
        2 / (5 * x) * depth ρ * (5 * x ^ 2) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    linarith
  have hsum : ∑ ρ ∈ Z, zeroMult ρ * (2 / (5 * x) * depth ρ) =
      2 / (5 * x) * ∑ ρ ∈ Z, zeroMult ρ * depth ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [hsum] at hle
  have h5 := hle.trans h
  have e : ∑ ρ ∈ Z, zeroMult ρ * depth ρ =
      (5 * x / 2) * (2 / (5 * x) * ∑ ρ ∈ Z, zeroMult ρ * depth ρ) := by
    field_simp
  rw [e]
  have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 5 * x / 2)
  refine h6.trans (le_of_eq ?_)
  ring

/-- **The lower side.** For `T ≥ 1`, the depth mass up to height `T` is at most `(5/2) T I(½ + T + it)`. -/
theorem sum_depth_height_le {T t : ℝ} (hT : 1 ≤ T) (Z : Finset ZetaRightZero)
    (hZ : ∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) :
    ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ (5 / 2) * T * innerField (centre T t) := by
  refine sum_depth_box_le (by linarith) (zetaEntire_centre_ne_zero (by linarith) t) Z fun ρ hρ => ⟨?_, hZ ρ hρ⟩
  have := depth_le_half ρ
  simp only [depth] at this
  linarith

/-- The Green kernel from above, far from the zeros. -/
theorem greenKernel_centre_le {x t : ℝ} (hx : 1 ≤ x) (ρ : ZetaRightZero) :
    greenKernel (centre x t) ρ ≤ 8 * x * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) := by
  have hb := depth_pos ρ
  have hb2 := depth_le_half ρ
  set w := centre x t with hw
  have hA : 0 < ‖(ρ : ℂ) + conj w - 1‖ :=
    norm_pos_iff.mpr (ne_zero_of_half_lt_re (by rw [hw, centre_re]; linarith) ρ.2.2)
  have hB2 : ‖(ρ : ℂ) - w‖ ^ 2 = (depth ρ - x) ^ 2 + ((ρ : ℂ).im - t) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, hw, centre_re, centre_im, depth]
    ring
  have hden : 0 < x ^ 2 + ((ρ : ℂ).im - t) ^ 2 := by positivity
  have hlow : (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) / 4 ≤ ‖(ρ : ℂ) - w‖ ^ 2 := by
    rw [hB2]
    have : x / 2 ≤ x - depth ρ := by linarith
    have h2 : (x / 2) ^ 2 ≤ (depth ρ - x) ^ 2 := by
      rw [show depth ρ - x = -(x - depth ρ) by ring, neg_sq]
      exact pow_le_pow_left₀ (by linarith) this 2
    nlinarith [sq_nonneg ((ρ : ℂ).im - t)]
  have hBpos : 0 < ‖(ρ : ℂ) - w‖ ^ 2 := lt_of_lt_of_le (by positivity) hlow
  have hB : 0 < ‖(ρ : ℂ) - w‖ := by
    by_contra h
    have h0 : ‖(ρ : ℂ) - w‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hBpos
    simp at hBpos
  have hpol := sq_norm_add_conj_eq w ρ
  have e4 : 4 * (w.re - 1 / 2) * ((ρ : ℂ).re - 1 / 2) = 4 * x * depth ρ := by
    rw [hw, centre_re]
    simp only [depth]
    ring
  rw [e4] at hpol
  set A := ‖(ρ : ℂ) + conj w - 1‖ with hAd
  set B := ‖(ρ : ℂ) - w‖ with hBd
  have hG : greenKernel w ρ = (1 / 2) * Real.log (A ^ 2 / B ^ 2) := by
    rw [greenKernel, ← hAd, ← hBd, ← div_pow, Real.log_pow]
    push_cast
    ring
  have hlog := Real.log_le_sub_one_of_pos (show 0 < A ^ 2 / B ^ 2 by positivity)
  have hfrac : A ^ 2 / B ^ 2 - 1 = 4 * x * depth ρ / B ^ 2 := by
    rw [hpol]
    field_simp
    ring
  rw [hG]
  have hmono : 4 * x * depth ρ / B ^ 2 ≤ 16 * x * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) := by
    rw [div_le_div_iff₀ hBpos hden]
    have hxb : 0 ≤ x * depth ρ := by positivity
    nlinarith
  have e8 : (1 / 2) * (16 * x * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2)) =
      8 * x * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) := by ring
  rw [← e8]
  linarith

/-- The dyadic estimate: a depth density at most `ε` gives `Σ m_ρ b_ρ/(x² + y²) ≤ 5ε/x`. -/
theorem sum_depth_div_le {x t ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hD : ∀ T : ℝ, x ≤ T → ∀ Z : Finset ZetaRightZero, (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) →
      ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ ε * T) (Z : Finset ZetaRightZero) :
    ∑ ρ ∈ Z, zeroMult ρ * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) ≤ 5 * ε / x := by
  classical
  have hxpos : 0 < x := by linarith
  set W : ℕ → Finset ZetaRightZero := fun K =>
    Z.filter fun ρ => |(ρ : ℂ).im - t| ≤ 2 ^ K * x with hW
  set f : ZetaRightZero → ℝ := fun ρ => zeroMult ρ * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2) with hf
  have hm : ∀ ρ : ZetaRightZero, 0 ≤ zeroMult ρ * depth ρ := fun ρ =>
    mul_nonneg (zeroMult_pos ρ).le (depth_pos ρ).le
  have hind : ∀ K : ℕ, ∑ ρ ∈ W K, f ρ ≤ (ε / x) * (5 - 4 * (1 / 2) ^ K) := by
    intro K
    induction K with
    | zero =>
      have hb : ∑ ρ ∈ W 0, f ρ ≤ ∑ ρ ∈ W 0, zeroMult ρ * depth ρ / x ^ 2 :=
        Finset.sum_le_sum fun ρ _ => div_le_div_of_nonneg_left (hm ρ) (by positivity)
          (by nlinarith [sq_nonneg ((ρ : ℂ).im - t)])
      rw [← Finset.sum_div] at hb
      have h1 := hD x le_rfl (W 0) fun ρ hρ => by
        simpa [hW] using (Finset.mem_filter.mp hρ).2
      have h2 : (∑ ρ ∈ W 0, zeroMult ρ * depth ρ) / x ^ 2 ≤ ε * x / x ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have e : ε * x / x ^ 2 = (ε / x) * (5 - 4 * (1 / 2) ^ 0) := by
        field_simp
        ring
      linarith
    | succ K ih =>
      have hsub : W K ⊆ W (K + 1) := fun ρ hρ => by
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hρ
        refine Finset.mem_filter.mpr ⟨h1, h2.trans ?_⟩
        have : (2 : ℝ) ^ K ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact mul_le_mul_of_nonneg_right this hxpos.le
      rw [← Finset.sum_sdiff hsub]
      have hshell : ∑ ρ ∈ W (K + 1) \ W K, f ρ ≤
          ∑ ρ ∈ W (K + 1), zeroMult ρ * depth ρ / ((2 ^ K * x) ^ 2) := by
        refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun ρ _ _ =>
            div_nonneg (hm ρ) (by positivity))
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hρ
        have h3 : 2 ^ K * x < |(ρ : ℂ).im - t| := by
          by_contra hc
          exact h2 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, not_lt.mp hc⟩)
        have h4 : (2 ^ K * x) ^ 2 ≤ ((ρ : ℂ).im - t) ^ 2 := by
          rw [← sq_abs ((ρ : ℂ).im - t)]
          exact pow_le_pow_left₀ (by positivity) h3.le 2
        exact div_le_div_of_nonneg_left (hm ρ) (by positivity) (by nlinarith [sq_nonneg x])
      rw [← Finset.sum_div] at hshell
      have hT : x ≤ 2 ^ (K + 1) * x := by
        have : (1 : ℝ) ≤ 2 ^ (K + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      have h1 := hD _ hT (W (K + 1)) fun ρ hρ => (Finset.mem_filter.mp hρ).2
      have h2 : (∑ ρ ∈ W (K + 1), zeroMult ρ * depth ρ) / (2 ^ K * x) ^ 2 ≤
          ε * (2 ^ (K + 1) * x) / (2 ^ K * x) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have e : ε * (2 ^ (K + 1) * x) / (2 ^ K * x) ^ 2 = (ε / x) * (2 * (1 / 2) ^ K) := by
        rw [one_div, inv_pow]
        field_simp
        ring
      have e2 : (ε / x) * (5 - 4 * (1 / 2) ^ (K + 1)) =
          (ε / x) * (5 - 4 * (1 / 2) ^ K) + (ε / x) * (2 * (1 / 2) ^ K) := by
        rw [pow_succ]
        ring
      rw [e2]
      linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ M := by
    refine ⟨∑ ρ ∈ Z, |(ρ : ℂ).im - t|, fun ρ hρ => ?_⟩
    exact Finset.single_le_sum (f := fun ρ : ZetaRightZero => |(ρ : ℂ).im - t|)
      (fun _ _ => abs_nonneg _) hρ
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (M / x) (by norm_num : (1 : ℝ) < 2)
  have hZK : W K = Z := by
    refine Finset.filter_true_of_mem fun ρ hρ => (hM ρ hρ).trans ?_
    rw [div_lt_iff₀ hxpos] at hK
    exact hK.le
  have h := hind K
  rw [hZK] at h
  refine h.trans ?_
  have hp : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  have hq : 0 ≤ ε / x := by positivity
  have e : 5 * ε / x = (ε / x) * 5 := by ring
  rw [e]
  nlinarith

/-- **The upper side.** A depth density at most `ε` above height `x` gives `I(½ + x + it) ≤ 40ε`. -/
theorem innerField_le_of_depthDensity {x t ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hD : ∀ T : ℝ, x ≤ T → ∀ Z : Finset ZetaRightZero, (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) →
      ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ ε * T) :
    innerField (centre x t) ≤ 40 * ε := by
  have hxpos : 0 < x := by linarith
  have h0 := zetaEntire_centre_ne_zero (x := x) (by linarith) t
  have hw : 1 / 2 < (centre x t).re := by rw [centre_re]; linarith
  refine hasSum_le_of_sum_le (hasSum_innerField hw h0) fun Z => ?_
  have h1 : ∑ ρ ∈ Z, zeroMult ρ * greenKernel (centre x t) ρ ≤
      ∑ ρ ∈ Z, 8 * x * (zeroMult ρ * depth ρ / (x ^ 2 + ((ρ : ℂ).im - t) ^ 2)) := by
    refine Finset.sum_le_sum fun ρ _ => ?_
    have h2 := mul_le_mul_of_nonneg_left (greenKernel_centre_le (t := t) hx ρ) (zeroMult_pos ρ).le
    refine h2.trans (le_of_eq ?_)
    ring
  rw [← Finset.mul_sum] at h1
  have h2 := sum_depth_div_le hx hε hD Z
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * x)
  have e : 8 * x * (5 * ε / x) = 40 * ε := by
    field_simp
    ring
  linarith

/-- **Inner mass at infinity is the depth density.** -/
theorem tendsto_innerField_iff_depthDensity (t : ℝ) :
    Tendsto (fun x : ℝ => innerField (centre x t)) atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Z : Finset ZetaRightZero,
        (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) → ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ ε * T := by
  constructor
  · intro h ε hε
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * ε / 5)))
    refine ⟨max x₀ 1, fun T hT Z hZ => ?_⟩
    have h1 := sum_depth_height_le ((le_max_right _ _).trans hT) Z hZ
    have h2 := hx₀ T ((le_max_left _ _).trans hT)
    have hTpos : 0 < T := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hT)
    have h3 := mul_le_mul_of_nonneg_left h2.le (by positivity : (0 : ℝ) ≤ (5 / 2) * T)
    refine h1.trans (h3.trans (le_of_eq ?_))
    ring
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := h (ε / 41) (by positivity)
    refine ⟨max T₀ 1, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hx2 : T₀ ≤ x := (le_max_left _ _).trans hx
    have h1 := innerField_le_of_depthDensity (t := t) hx1 (by positivity : 0 ≤ ε / 41)
      fun T hT Z hZ => hT₀ T (hx2.trans hT) Z hZ
    have h0 := zetaEntire_centre_ne_zero (x := x) (by linarith) t
    have hnn := innerField_nonneg (w := centre x t) (by rw [centre_re]; linarith) h0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    linarith

/-- **Bounded inner mass at infinity is an `O(T)` depth bound.** -/
theorem bounded_innerField_iff_depthDensity (t : ℝ) :
    (∃ B : ℝ, ∀ x : ℝ, 1 ≤ x → innerField (centre x t) ≤ B) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ Z : Finset ZetaRightZero,
        (∀ ρ ∈ Z, |(ρ : ℂ).im - t| ≤ T) → ∑ ρ ∈ Z, zeroMult ρ * depth ρ ≤ C * T := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨(5 / 2) * max B 0, by positivity, fun T hT Z hZ => ?_⟩
    have h1 := sum_depth_height_le hT Z hZ
    have h2 := (hB T hT).trans (le_max_left B 0)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (5 / 2) * T)
    refine h1.trans (h3.trans (le_of_eq ?_))
    ring
  · rintro ⟨C, hC, hD⟩
    exact ⟨40 * C, fun x hx => innerField_le_of_depthDensity hx hC fun T hT Z hZ =>
      hD T (hx.trans hT) Z hZ⟩

/-- **The inner mass at infinity does not depend on the height.** -/
theorem tendsto_innerField_congr (t t' : ℝ)
    (h : Tendsto (fun x : ℝ => innerField (centre x t)) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => innerField (centre x t')) atTop (𝓝 0) := by
  rw [tendsto_innerField_iff_depthDensity] at h ⊢
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h (ε / 2) (by positivity)
  refine ⟨max (max T₀ |t - t'|) 0, fun T hT Z hZ => ?_⟩
  have hT1 : T₀ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : |t - t'| ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT3 : 0 ≤ T := (le_max_right _ _).trans hT
  have h1 := hT₀ (2 * T) (by linarith) Z fun ρ hρ => by
    have h2 := hZ ρ hρ
    have h3 : |(ρ : ℂ).im - t| ≤ |(ρ : ℂ).im - t'| + |t - t'| := by
      calc |(ρ : ℂ).im - t| = |((ρ : ℂ).im - t') + (t' - t)| := by
            congr 1
            ring
        _ ≤ |(ρ : ℂ).im - t'| + |t' - t| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm t' t]
    linarith
  refine h1.trans (le_of_eq ?_)
  ring

/-! ### The embedding at scale `x` -/

/-- The shifted crowd: `ν_x(τ) = Σ_ρ (m_ρ/π) b_ρ/((b_ρ + x)² + (γ_ρ − τ)²)`. -/
def shiftedCrowd (Z : Finset ZetaRightZero) (x τ : ℝ) : ℝ :=
  ∑ ρ ∈ Z, zeroMult ρ * (depth ρ / (depth ρ + x)) * halfPlanePoissonKernel ((ρ : ℂ) + (x : ℂ)) τ

/-- **The shifted crowd is the inner field at width `x`.** -/
theorem shiftedCrowd_le_innerField {x τ : ℝ} (hx : 0 < x) (h0 : zetaEntire (centre x τ) ≠ 0)
    (Z : Finset ZetaRightZero) :
    shiftedCrowd Z x τ ≤ innerField (centre x τ) / (2 * π * x) := by
  have hπ := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  have h := sum_carleson_test_le hx h0 Z
  refine le_trans (le_of_eq ?_) h
  rw [shiftedCrowd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hb := depth_pos ρ
  have hre : ((ρ : ℂ) + (x : ℂ)).re - 1 / 2 = depth ρ + x := by
    simp [depth]
    ring
  have him : ((ρ : ℂ) + (x : ℂ)).im = (ρ : ℂ).im := by simp
  rw [halfPlanePoissonKernel, hre, him]
  have e : (τ - (ρ : ℂ).im) ^ 2 = ((ρ : ℂ).im - τ) ^ 2 := by ring
  rw [e]
  have hd : 0 < (depth ρ + x) ^ 2 + ((ρ : ℂ).im - τ) ^ 2 := by positivity
  have hs : 0 < depth ρ + x := by positivity
  field_simp

/-- **The Carleson embedding at scale `x`.** -/
theorem carleson_embedding {A : ℂ → ℂ} (hA : Differentiable ℂ A) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖A z‖ ≤ C * (‖z‖ + 2) ^ 2) {x : ℝ} (hx : 0 < x)
    (Z : Finset ZetaRightZero)
    (hi : ∀ ρ ∈ Z, Integrable fun τ : ℝ =>
      ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel ((ρ : ℂ) + (x : ℂ)) τ) :
    ∑ ρ ∈ Z, zeroMult ρ * (depth ρ / (depth ρ + x)) * ‖A ((ρ : ℂ) + (x : ℂ))‖ ^ 2 ≤
      ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * shiftedCrowd Z x τ := by
  have e : ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * shiftedCrowd Z x τ =
      ∑ ρ ∈ Z, zeroMult ρ * (depth ρ / (depth ρ + x)) *
        ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel ((ρ : ℂ) + (x : ℂ)) τ := by
    simp only [shiftedCrowd, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      ring
    · intro ρ hρ
      refine ((hi ρ hρ).const_mul (zeroMult ρ * (depth ρ / (depth ρ + x)))).congr (ae_of_all _ fun τ => ?_)
      ring
  rw [e]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hb := depth_pos ρ
  have hs : 1 / 2 < ((ρ : ℂ) + (x : ℂ)).re := by
    have : ((ρ : ℂ) + (x : ℂ)).re = (ρ : ℂ).re + x := by simp
    rw [this]
    have := ρ.2.2
    linarith
  exact mul_le_mul_of_nonneg_left (norm_sq_le_poisson hA hgrow hs (hi ρ hρ))
    (mul_nonneg (zeroMult_pos ρ).le (div_nonneg hb.le (by positivity)))

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
