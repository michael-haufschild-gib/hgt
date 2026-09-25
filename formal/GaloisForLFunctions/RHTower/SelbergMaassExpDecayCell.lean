import GaloisForLFunctions.RHTower.SarnakXueCuspTail
import GaloisForLFunctions.RHTower.SelbergMaassBesselRemainder
import GaloisForLFunctions.RHTower.PeriodicFourierDecay
import GaloisForLFunctions.RHTower.SelbergPoincareIntegrability
import GaloisForLFunctions.RHTower.MaassCongruenceL2
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainMeasure
import GaloisForLFunctions.RHTower.SarnakXuePretrace

open Set Filter Topology UpperHalfPlane

/-!
# Exponential cusp decay of exceptional Maass forms and integrability on the fundamental cell

For a decaying solution of `a'' = (k² - λ/y²) a` with `κ² ≤ k²` and `λ ≤ κ² t₀²/2`, `G = |a|²` has
`G'' ≥ κ² G` beyond `t₀`; then `H = G' + κG` satisfies `H' ≥ κH`, so `H > 0` somewhere would force linear growth
of `G` (`ge_of_deriv_ge`), hence `H ≤ 0` and `e^{κt}G` is nonincreasing (`normSq_le_exp`). For a `Γ(N+1)` Maass cusp
form with `0 < λ < 1/4` every nonconstant mode decays like `e^{-κ(t-t₀)/2}`, `κ = 2π/(N+1)` (`mode_decay`); the
coefficients at a fixed height are `O(n^{-2})` and the constant mode vanishes, so pointwise Fourier inversion gives
`|f(z)| ≤ C e^{-π Im z/(N+1)}` (`maass_decay`).

Consequently `(1 + y⁶)|f|` is integrable on `𝒟` (`integrableOn_fd`); heights under a fixed modular
transformation are polynomially controlled on `𝒟` (`im_smul_bound`), and every translate of `f` is again such a
form, so `(y^{-6} + y³)|f|` is integrable over the fundamental cell `cellP (N+1)` (`integrableOn_cellP`).
-/

namespace GaloisForLFunctions.RHTower.SelbergMaassExpDecayCell
open GaloisForLFunctions.RHTower.SarnakXueCuspTail

/-- If `H' ≥ κH` on `[t₀, ∞)` and `H(t₁) > 0`, then `H(t) ≥ H(t₁)` for all `t ≥ t₁`. -/
theorem ge_of_deriv_ge {H H' : ℝ → ℝ} {κ t₀ : ℝ} (hκ : 0 < κ)
    (hH : ∀ t, t₀ ≤ t → HasDerivAt H (H' t) t) (hH' : ∀ t, t₀ ≤ t → κ * H t ≤ H' t)
    {t₁ : ℝ} (ht₁ : t₀ ≤ t₁) (hpos : 0 < H t₁) : ∀ t, t₁ ≤ t → H t₁ ≤ H t := by
  -- `e^{-κt} H` is nondecreasing on `[t₀, ∞)`
  set φ : ℝ → ℝ := fun t => Real.exp (-κ * t) * H t
  have hφ : ∀ t, t₀ ≤ t → HasDerivAt φ (Real.exp (-κ * t) * (H' t - κ * H t)) t := by
    intro t ht
    have he : HasDerivAt (fun t => Real.exp (-κ * t)) (Real.exp (-κ * t) * -κ) t := by
      have := ((hasDerivAt_id t).const_mul (-κ)).exp
      simpa using this
    exact (he.mul (hH t ht)).congr_deriv (by ring)
  have hmono : MonotoneOn φ (Ici t₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t₀)
    · exact fun t ht => (hφ t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hφ t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hφ t ht.le).deriv]
      have := hH' t ht.le
      exact mul_nonneg (Real.exp_pos _).le (by linarith)
  intro t ht
  have h := hmono (show t₁ ∈ Ici t₀ from ht₁) (show t ∈ Ici t₀ from ht₁.trans ht) ht
  simp only [φ] at h
  -- `H t ≥ e^{κ(t - t₁)} H t₁ ≥ H t₁`
  have h1 : H t₁ * Real.exp (κ * (t - t₁)) ≤ H t := by
    have hpos' : 0 < Real.exp (-κ * t) := Real.exp_pos _
    have : Real.exp (-κ * t) * (H t₁ * Real.exp (κ * (t - t₁))) ≤ Real.exp (-κ * t) * H t := by
      calc Real.exp (-κ * t) * (H t₁ * Real.exp (κ * (t - t₁))) = Real.exp (-κ * t₁) * H t₁ := by
            rw [show Real.exp (-κ * t) * (H t₁ * Real.exp (κ * (t - t₁))) =
              H t₁ * (Real.exp (-κ * t) * Real.exp (κ * (t - t₁))) by ring, ← Real.exp_add]
            rw [show -κ * t + κ * (t - t₁) = -κ * t₁ by ring]; ring
        _ ≤ _ := h
    exact le_of_mul_le_mul_left this hpos'
  have h2 : 1 ≤ Real.exp (κ * (t - t₁)) := Real.one_le_exp (by nlinarith)
  nlinarith

/-- **Exponential decay of a decaying mode.** If `a'' = (k² - λ/y²) a` on `y > 0`, `a → 0`, `κ² ≤ k²`
and `λ ≤ κ² t₀²/2`, then `|a(t)|² ≤ |a(t₀)|² e^{-κ(t-t₀)}` for `t ≥ t₀`. -/
theorem normSq_le_exp {a : ℝ → ℂ} {k lam κ t₀ : ℝ} (hκ : 0 < κ) (ht₀ : 0 < t₀) (hk : κ ^ 2 ≤ k ^ 2)
    (hlam : lam ≤ κ ^ 2 * t₀ ^ 2 / 2)
    (h1 : ∀ y, 0 < y → HasDerivAt a (deriv a y) y)
    (h2 : ∀ y, 0 < y → HasDerivAt (deriv a) (deriv (deriv a) y) y)
    (hode : ∀ y, 0 < y → deriv (deriv a) y = ((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y)
    (hdec : Tendsto a atTop (𝓝 0)) :
    ∀ t, t₀ ≤ t → Complex.normSq (a t) ≤ Complex.normSq (a t₀) * Real.exp (-κ * (t - t₀)) := by
  set G : ℝ → ℝ := fun y => (a y).re ^ 2 + (a y).im ^ 2
  set G' : ℝ → ℝ := fun y => 2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im)
  set G'' : ℝ → ℝ := fun y => 2 * ((deriv a y).re ^ 2 + (a y).re * (deriv (deriv a) y).re +
    ((deriv a y).im ^ 2 + (a y).im * (deriv (deriv a) y).im))
  have hGd : ∀ y, 0 < y → HasDerivAt G (G' y) y := by
    intro y hy
    have hr := hasDerivAt_re (h1 y hy)
    have hi := hasDerivAt_im (h1 y hy)
    exact ((hr.pow 2).add (hi.pow 2)).congr_deriv (by simp only [G']; norm_num; ring)
  have hG'd : ∀ y, 0 < y → HasDerivAt G' (G'' y) y := by
    intro y hy
    have hr := hasDerivAt_re (h1 y hy)
    have hi := hasDerivAt_im (h1 y hy)
    have hr' := hasDerivAt_re (h2 y hy)
    have hi' := hasDerivAt_im (h2 y hy)
    exact (((hr.mul hr').add (hi.mul hi')).const_mul 2).congr_deriv (by simp only [G'']; ring)
  have hG''ge : ∀ y, t₀ ≤ y → κ ^ 2 * G y ≤ G'' y := by
    intro y hy
    have hy0 : 0 < y := ht₀.trans_le hy
    have hc : κ ^ 2 / 2 ≤ k ^ 2 - lam / y ^ 2 := by
      have : lam / y ^ 2 ≤ κ ^ 2 / 2 := by
        rcases le_or_gt lam 0 with hl | hl
        · have : lam / y ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hl (by positivity)
          have : 0 ≤ κ ^ 2 / 2 := by positivity
          linarith
        · rw [div_le_iff₀ (by positivity)]
          have hyy : t₀ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ ht₀.le hy 2
          nlinarith
      linarith
    simp only [G'', G]
    rw [hode y hy0]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    have hG0 : 0 ≤ (a y).re ^ 2 + (a y).im ^ 2 := by positivity
    nlinarith [sq_nonneg (deriv a y).re, sq_nonneg (deriv a y).im, mul_le_mul_of_nonneg_right hc hG0]
  set H : ℝ → ℝ := fun y => G' y + κ * G y
  have hH : ∀ y, t₀ ≤ y → HasDerivAt H (G'' y + κ * G' y) y :=
    fun y hy => (hG'd y (ht₀.trans_le hy)).add ((hGd y (ht₀.trans_le hy)).const_mul κ)
  have hH' : ∀ y, t₀ ≤ y → κ * H y ≤ G'' y + κ * G' y := by
    intro y hy; simp only [H]; nlinarith [hG''ge y hy]
  -- `H ≤ 0` on `[t₀, ∞)`
  have hHle : ∀ y, t₀ ≤ y → H y ≤ 0 := by
    intro t₁ ht₁
    by_contra hpos; push Not at hpos
    have hgrow := ge_of_deriv_ge hκ hH hH' ht₁ hpos
    have hGlim : Tendsto G atTop (𝓝 0) := by
      have : Tendsto (fun y => Complex.normSq (a y)) atTop (𝓝 (Complex.normSq 0)) :=
        (Complex.continuous_normSq.tendsto 0).comp hdec
      simpa [G, Complex.normSq_apply, pow_two] using this
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hGlim.eventually (gt_mem_nhds (show (0 : ℝ) < H t₁ / (2 * κ) by positivity)))
    set T' := max T t₁
    have hG'ge : ∀ y, T' ≤ y → H t₁ / 2 ≤ G' y := by
      intro y hy
      have h1 := hgrow y ((le_max_right _ _).trans hy)
      have h2 := hT y ((le_max_left _ _).trans hy)
      simp only [H] at h1
      have : κ * G y ≤ H t₁ / 2 := by
        rw [lt_div_iff₀ (by positivity)] at h2; linarith
      linarith
    -- `G` grows linearly beyond `T'`
    have hlin : ∀ y, T' ≤ y → G T' + H t₁ / 2 * (y - T') ≤ G y := by
      intro y hy
      have hm : MonotoneOn (fun t => G t - H t₁ / 2 * t) (Icc T' y) := by
        have hT'0 : t₀ ≤ T' := ht₁.trans (le_max_right _ _)
        apply monotoneOn_of_deriv_nonneg (convex_Icc T' y)
        · intro t ht
          exact ((hGd t (ht₀.trans_le (hT'0.trans ht.1))).continuousAt.sub
            (continuousAt_const.mul continuousAt_id)).continuousWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          exact ((hGd t (ht₀.trans_le (hT'0.trans ht.1.le))).sub
            ((hasDerivAt_id t).const_mul (H t₁ / 2))).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Icc] at ht
          have hd : HasDerivAt (fun t => G t - H t₁ / 2 * t) (G' t - H t₁ / 2 * 1) t :=
            (hGd t (ht₀.trans_le (hT'0.trans ht.1.le))).sub ((hasDerivAt_id' t).const_mul _)
          rw [hd.deriv]
          have := hG'ge t ht.1.le
          linarith
      have := hm (left_mem_Icc.mpr hy) (right_mem_Icc.mpr hy) hy
      simp only at this; linarith
    set y := T' + 2 * (H t₁ / (2 * κ)) / (H t₁ / 2) + 1
    have hy : T' ≤ y := by
      have : 0 ≤ 2 * (H t₁ / (2 * κ)) / (H t₁ / 2) := by positivity
      simp only [y]; linarith
    have hA := hlin y hy
    have hB := hT y ((le_max_left _ _).trans hy)
    have hGT : 0 ≤ G T' := by simp only [G]; positivity
    have : H t₁ / 2 * (y - T') = 2 * (H t₁ / (2 * κ)) + H t₁ / 2 := by
      simp only [y]; field_simp; ring
    have hX : 0 < H t₁ / (2 * κ) := by positivity
    linarith
  -- `e^{κt} G` is nonincreasing
  set ψ : ℝ → ℝ := fun t => Real.exp (κ * t) * G t
  have hψ : ∀ t, t₀ ≤ t → HasDerivAt ψ (Real.exp (κ * t) * H t) t := by
    intro t ht
    have he : HasDerivAt (fun t => Real.exp (κ * t)) (Real.exp (κ * t) * κ) t := by
      have := ((hasDerivAt_id t).const_mul κ).exp
      simpa using this
    exact (he.mul (hGd t (ht₀.trans_le ht))).congr_deriv (by simp only [H]; ring)
  have hanti : AntitoneOn ψ (Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
    · exact fun t ht => (hψ t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hψ t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hψ t ht.le).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hHle t ht.le)
  intro t ht
  have h := hanti Set.self_mem_Ici (show t ∈ Ici t₀ from ht) ht
  simp only [ψ] at h
  have hG : Complex.normSq (a t) = G t := by simp [G, Complex.normSq_apply, pow_two]
  have hG0 : Complex.normSq (a t₀) = G t₀ := by simp [G, Complex.normSq_apply, pow_two]
  rw [hG, hG0]
  have hpos : 0 < Real.exp (κ * t) := Real.exp_pos _
  have e : Real.exp (-κ * (t - t₀)) = Real.exp (κ * t₀) / Real.exp (κ * t) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [e, mul_div_assoc', le_div_iff₀ hpos]
  linarith [mul_comm (G t) (Real.exp (κ * t)), mul_comm (G t₀) (Real.exp (κ * t₀))]

theorem periodic_bounded (g : ℝ → ℂ) (hg : Continuous g) {c : ℝ} (hc : 0 < c) (hp : Function.Periodic g c) :
    ∃ C, ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := c)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ hc x
  rw [hxy]; exact hC y (Set.Ico_subset_Icc_self hy)

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.SelbergMaassFourier
  GaloisForLFunctions.RHTower.SelbergMaassMean GaloisForLFunctions.RHTower.SelbergMaassParseval
  GaloisForLFunctions.RHTower.SelbergMaassBessel

/-- **Pointwise Fourier bound**: `|f(x + it)| ≤ Σ_n |a_n(t)|` whenever the coefficients are dominated by a
summable sequence. -/
theorem norm_le_tsum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ)
    {b : ℤ → ℝ} (hb : Summable b) (hab : ∀ n, ‖maassCoefficient N f n z.im‖ ≤ b n) :
    ‖f.1.1 z‖ ≤ ∑' n, b n := by
  set w : ℝ := ((N + 1 : ℕ) : ℝ)
  have hw : 0 < w := by positivity
  set F := f.1.1 ∘ ofComplex
  set t := z.im
  have ht : 0 < t := z.im_pos
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hf1 : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} := hf.of_le (by simp)
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hdd := directional_contDiffOn hd (m := 0) (by simp) (1 : ℂ)
  set g : ℝ → ℂ := fun x => F (point x t)
  have hper : Function.Periodic g w := fun x => maass_periodic N f x ht
  have hper1 : Function.Periodic (fun x => directional 1 F (point x t)) w :=
    fun x => directional_periodic hf1 ht w (fun x => maass_periodic N f x ht) x
  have hper2 : Function.Periodic (fun x => directional 1 (directional 1 F) (point x t)) w :=
    fun x => directional_periodic hd ht w (fun x => directional_periodic hf1 ht w (fun x => maass_periodic N f x ht) x) x
  obtain ⟨C, hC⟩ := periodic_bounded _ (slice_continuous hdd.continuousOn ht) hw hper2
  have hsum : ∀ x ∈ Ioc 0 w, HasSum (fun n : ℤ => fourierCoeffOn hw g n * fourier n ((x : ℝ) : AddCircle (w - 0))) (g x) := by
    intro x hx
    have := hasSum_fourier_of_periodic_two (a := 0) (b := w) hw (f := g)
      (f' := fun x => directional 1 F (point x t)) (f'' := fun x => directional 1 (directional 1 F) (point x t))
      (fun x _ => slice_horizontal hf1 ht x) (fun x _ => slice_horizontal hd ht x)
      ((slice_continuous hd.continuousOn ht).intervalIntegrable _ _)
      ((slice_continuous hdd.continuousOn ht).intervalIntegrable _ _) hC
      (by simpa using hper 0) (by simpa using hper1 0) hx
    simpa using this
  -- reduce `z.re` to `Ioc 0 w`
  obtain ⟨x', hx', hxx'⟩ := hper.exists_mem_Ico₀ hw z.re
  have hmem : ∃ x'' ∈ Ioc 0 w, g z.re = g x'' := by
    rcases eq_or_lt_of_le hx'.1 with h0 | hpos
    · refine ⟨w, ⟨hw, le_rfl⟩, ?_⟩
      rw [hxx', ← h0]; simpa using (hper 0).symm
    · exact ⟨x', ⟨hpos, hx'.2.le⟩, hxx'⟩
  obtain ⟨x'', hx'', hg⟩ := hmem
  have hz : f.1.1 z = g z.re := by
    simp only [g, F, Function.comp_apply, point]
    rw [ofComplex_apply_of_im_pos (by simpa using ht)]
    apply congrArg
    apply UpperHalfPlane.ext
    simp only [t]
    exact (Complex.re_add_im (z : ℂ)).symm
  rw [hz, hg, ← (hsum x'' hx'').tsum_eq]
  have hcoef : ∀ n, ‖fourierCoeffOn hw g n * fourier n ((x'' : ℝ) : AddCircle (w - 0))‖ ≤ b n := by
    intro n
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one, ← coefficient_eq_fourierCoeffOn w hw F t n]
    exact hab n
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef hb)).trans
    (Summable.tsum_le_tsum hcoef (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoef hb) hb)

/-- Each nonconstant mode decays like `e^{-κ(t - t₀)/2}` beyond `t₀`, `κ = 2π/(N+1)`. -/
theorem mode_decay (N : ℕ) {lam : ℝ} (hlam0 : lam < 1 / 4)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) {n : ℤ} (hn : n ≠ 0)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hκt : 2 ≤ 2 * Real.pi / ((N + 1 : ℕ) : ℝ) * t₀) {t : ℝ} (ht : t₀ ≤ t) :
    ‖maassCoefficient N f n t‖ ≤ ‖maassCoefficient N f n t₀‖ *
      Real.exp (-(2 * Real.pi / ((N + 1 : ℕ) : ℝ)) / 2 * (t - t₀)) := by
  set w : ℝ := ((N + 1 : ℕ) : ℝ)
  set κ := 2 * Real.pi / w
  have hκ : 0 < κ := by positivity
  set a := maassCoefficient N f n
  set k := signedFrequency (N + 1 : ℕ) n
  have hk : κ ^ 2 ≤ k ^ 2 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      exact_mod_cast this
    have : k = κ * n := by simp only [k, κ, signedFrequency, w]; ring
    rw [this, mul_pow]; nlinarith [sq_nonneg κ]
  have hlam : lam ≤ κ ^ 2 * t₀ ^ 2 / 2 := by nlinarith
  have hode : ∀ y, 0 < y → deriv (deriv a) y = ((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y := by
    intro y hy
    have h := maassCoefficient_modal_equation N f n hy
    have hy2 : ((y : ℝ) : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hy 2).ne'
    have hm : deriv (deriv a) y * ((y : ℝ) : ℂ) ^ 2 = ((k : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ 2 - lam) * a y := by
      linear_combination (-1 : ℂ) * h
    rw [← eq_div_iff hy2] at hm
    rw [hm]
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
  have h := normSq_le_exp hκ ht₀ hk hlam (fun y hy => maassCoefficient_hasDerivAt N f n hy)
    (fun y hy => maassCoefficient_second_hasDerivAt N f n hy) hode (maassCoefficient_decay N f n) t ht
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  have he : Real.exp (-κ * (t - t₀)) = (Real.exp (-κ / 2 * (t - t₀))) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h

/-- **Exponential decay of `Γ(N+1)` Maass cusp forms** with `0 < λ < 1/4` at the cusp `∞`:
`|f(z)| ≤ C e^{-π Im z/(N+1)}` for `Im z ≥ t₀`. -/
theorem maass_decay (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ z : ℍ, t₀ ≤ z.im →
      ‖f.1.1 z‖ ≤ C * Real.exp (-(2 * Real.pi / ((N + 1 : ℕ) : ℝ)) / 2 * z.im) := by
  set w : ℝ := ((N + 1 : ℕ) : ℝ)
  set κ := 2 * Real.pi / w
  have hw : 0 < w := by positivity
  have hκ : 0 < κ := by positivity
  set t₀ := max 1 (2 / κ)
  have ht₀ : 0 < t₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hκt : 2 ≤ κ * t₀ := by
    have : 2 / κ ≤ t₀ := le_max_right _ _
    rw [div_le_iff₀ hκ] at this; linarith
  obtain ⟨M₀, hM₀0, hM₀⟩ := maassCoefficient_frequency_square_bound N f ht₀
  set S₂ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  set C := M₀ * (w / (2 * Real.pi)) ^ 2 * S₂ * Real.exp (κ / 2 * t₀)
  refine ⟨C, t₀, ht₀, fun z hz => ?_⟩
  set t := z.im
  set b : ℤ → ℝ := fun n => M₀ * (w / (2 * Real.pi)) ^ 2 * (1 / (n : ℝ) ^ 2) * Real.exp (-κ / 2 * (t - t₀))
  have hsumS : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  have hb : Summable b := by
    have := (hsumS.mul_left (M₀ * (w / (2 * Real.pi)) ^ 2)).mul_right (Real.exp (-κ / 2 * (t - t₀)))
    exact this
  have hab : ∀ n, ‖maassCoefficient N f n t‖ ≤ b n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [constant_mode_zero N lam f z.im_pos, norm_zero]
      simp [b]
    · have h1 := mode_decay N lam.2.2 f hn ht₀ hκt hz
      have hk : signedFrequency (N + 1 : ℕ) n ^ 2 = κ ^ 2 * (n : ℝ) ^ 2 := by
        simp only [signedFrequency, κ, w]; ring
      have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      have h2 : ‖maassCoefficient N f n t₀‖ ≤ M₀ * (w / (2 * Real.pi)) ^ 2 * (1 / (n : ℝ) ^ 2) := by
        have := hM₀ n
        rw [hk] at this
        have hwk : (w / (2 * Real.pi)) ^ 2 = 1 / κ ^ 2 := by
          simp only [κ]; field_simp
        rw [hwk, show M₀ * (1 / κ ^ 2) * (1 / (n : ℝ) ^ 2) = M₀ / (κ ^ 2 * (n : ℝ) ^ 2) by
          field_simp]
        rw [le_div_iff₀ (by positivity)]; linarith
      calc ‖maassCoefficient N f n t‖ ≤ ‖maassCoefficient N f n t₀‖ * Real.exp (-κ / 2 * (t - t₀)) := h1
        _ ≤ b n := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  refine (norm_le_tsum N f z hb hab).trans (le_of_eq ?_)
  have hsb : ∑' n, b n = M₀ * (w / (2 * Real.pi)) ^ 2 * S₂ * Real.exp (-κ / 2 * (t - t₀)) := by
    simp only [b]; rw [tsum_mul_right, tsum_mul_left]
  rw [hsb]
  simp only [C]
  rw [mul_assoc (M₀ * (w / (2 * Real.pi)) ^ 2 * S₂), ← Real.exp_add]
  congr 2; simp only [t, κ]; ring

open MeasureTheory ModularGroup GaloisForLFunctions.HTGeometry
open scoped Pointwise MatrixGroups

theorem continuous_source {Γ : Subgroup SL2R} {lam : ℝ} (f : MaassCuspEigenform Γ lam) : Continuous f.1.1 := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (f.2.2.1.1.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

theorem fd_subset : fd ⊆ modularStrip ∪ (ModularGroup.T ^ (-1 : ℤ)) • modularStrip := by
  intro w hw
  have hre := hw.2
  rcases le_or_gt 0 w.re with h0 | h0
  · left
    simp only [modularStrip, Set.mem_setOf_eq]
    constructor
    · exact h0
    · rw [abs_le] at hre; linarith
  · right
    refine ⟨ModularGroup.T • w, ?_, by simp [smul_smul]⟩
    simp only [modularStrip, Set.mem_setOf_eq]
    rw [show ModularGroup.T • w = ModularGroup.T ^ (1 : ℤ) • w by simp, re_T_zpow_smul]
    rw [abs_le] at hre
    push_cast
    constructor <;> linarith

theorem maj_integrableOn_fd {σ c : ℝ} (hσ : 1 < σ) (hc : 0 < c) :
    IntegrableOn (GaloisForLFunctions.RHTower.SelbergPoincareIntegrability.maj σ c) fd volume := by
  open GaloisForLFunctions.RHTower.SelbergPoincareIntegrability in
  have h1 := maj_integrableOn_strip hσ hc
  have h2 : IntegrableOn (maj σ c) ((ModularGroup.T ^ (-1 : ℤ)) • modularStrip) volume := by
    rw [IntegrableOn, ← Set.image_smul, ← ((measurePreserving_smul (ModularGroup.T ^ (-1 : ℤ)) volume).restrict_image_emb
      (measurableEmbedding_const_smul _) modularStrip).integrable_comp_emb
      (measurableEmbedding_const_smul _)]
    have : (maj σ c ∘ fun x => ModularGroup.T ^ (-1 : ℤ) • x) = maj σ c := by
      funext z; exact maj_T_zpow σ c (-1) z
    rw [this]
    exact h1
  exact (h1.union h2).mono_set fd_subset

theorem one_le_im_of_mem_fd {w : ℍ} (hw : w ∈ fd) : (1 : ℝ) / 2 ≤ w.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hw
  nlinarith [w.im_pos]

/-- **Weighted integrability on the fundamental domain**: `(1 + y^6)|f|` is integrable on `𝒟`. -/
theorem integrableOn_fd (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    IntegrableOn (fun w : ℍ => (1 + w.im ^ 6) * ‖f.1.1 w‖) fd volume := by
  open GaloisForLFunctions.RHTower.SelbergPoincareIntegrability in
  obtain ⟨B, hB⟩ := MaassCongruenceL2.source_bounded N f
  obtain ⟨C, t₀, ht₀, hdec⟩ := maass_decay N lam f
  set c := (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) / 2
  have hc : 0 < c := by positivity
  set t₁ := max t₀ 1
  set K := (1 + t₁ ^ 6) * max B 0
  have hmaj := maj_integrableOn_fd (σ := 6) (by norm_num) hc
  have hdom : IntegrableOn (fun w : ℍ => K + 2 * max C 0 * ‖maj 6 c w‖) fd volume :=
    (integrableOn_const volume_fd_ne_top).add (hmaj.norm.const_mul _)
  refine hdom.mono' ((by fun_prop : Continuous (fun w : ℍ => w.im)).pow 6 |>.const_add 1 |>.mul
    (continuous_source f).norm).aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem isClosed_fd.measurableSet (fun w hw => ?_)
  have ht := w.im_pos
  have hKn : 0 ≤ K := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmajw : ‖maj 6 c w‖ = w.im ^ (6 : ℝ) * Real.exp (-c * w.im) := by
    simp only [maj, Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_nonneg (by positivity)]
  rw [hmajw]
  have h6 : w.im ^ (6 : ℝ) = w.im ^ 6 := by norm_cast
  rw [h6]
  rcases le_or_gt w.im t₁ with hle | hgt
  · have h1 : 1 + w.im ^ 6 ≤ 1 + t₁ ^ 6 := by gcongr
    have h2 : ‖f.1.1 w‖ ≤ max B 0 := (hB w).trans (le_max_left _ _)
    have : (1 + w.im ^ 6) * ‖f.1.1 w‖ ≤ K := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have : 0 ≤ 2 * max C 0 * (w.im ^ 6 * Real.exp (-c * w.im)) := by positivity
    linarith
  · have ht0 : t₀ ≤ w.im := (le_max_left _ _).trans hgt.le
    have ht1 : 1 ≤ w.im := (le_max_right _ _).trans hgt.le
    have h1 : 1 + w.im ^ 6 ≤ 2 * w.im ^ 6 := by nlinarith [one_le_pow₀ ht1 (n := 6)]
    have h2 : ‖f.1.1 w‖ ≤ max C 0 * Real.exp (-c * w.im) := by
      refine (hdec w ht0).trans ?_
      have : -(2 * Real.pi / ((N + 1 : ℕ) : ℝ)) / 2 * w.im = -c * w.im := by simp only [c]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have : (1 + w.im ^ 6) * ‖f.1.1 w‖ ≤ 2 * w.im ^ 6 * (max C 0 * Real.exp (-c * w.im)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    nlinarith

theorem pow_six_le (t : ℝ) (ht : 0 ≤ t) : (2 + t) ^ 6 ≤ 729 * (1 + t ^ 6) := by
  rcases le_or_gt t 1 with h | h
  · have : (2 + t) ^ 6 ≤ 3 ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    nlinarith [pow_nonneg ht 6]
  · have : (2 + t) ^ 6 ≤ (3 * t) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    rw [mul_pow] at this; norm_num at this; nlinarith

/-- Heights under a fixed modular transformation are polynomially controlled on `𝒟`. -/
theorem im_smul_bound (A : SL(2, ℤ)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ w ∈ fd,
    (A • w).im ^ (-6 : ℝ) + (A • w).im ^ (3 : ℝ) ≤ K * (1 + w.im ^ 6) := by
  set c : ℝ := (A 1 0 : ℝ)
  set d : ℝ := (A 1 1 : ℝ)
  set E := (|c| + |d| + 1) ^ 2
  refine ⟨64 + 729 * E ^ 6, by positivity, fun w hw => ?_⟩
  have ht := w.im_pos
  have ht2 := one_le_im_of_mem_fd hw
  have hx : |w.re| ≤ 1 / 2 := hw.2
  set t := w.im
  set x := w.re
  set D := Complex.normSq (UpperHalfPlane.denom A w)
  have hD : D = (c * x + d) ^ 2 + (c * t) ^ 2 := by
    simp only [D, UpperHalfPlane.denom, Complex.normSq_apply]
    simp [c, d, x, t]; ring
  have him : (A • w).im = t / D := by rw [ModularGroup.im_smul_eq_div_normSq]
  -- lower bound `D ≥ 1/4`
  have hDlow : 1 / 4 ≤ D := by
    by_cases hc : (A 1 0 : ℤ) = 0
    · have hdet := A.2
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      have hd1 : (A 1 1 : ℤ) = 1 ∨ (A 1 1 : ℤ) = -1 :=
        Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet)
      have hc' : c = 0 := by simp [c, hc]
      have hd2 : d ^ 2 = 1 := by rcases hd1 with h | h <;> simp [d, h]
      rw [hD, hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (A 1 0) ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs (A 1 0)]
        simp only [c]; exact_mod_cast this
      have e1 : (c * t) ^ 2 = c ^ 2 * t ^ 2 := by ring
      have e2 : t ^ 2 ≤ c ^ 2 * t ^ 2 := by nlinarith [sq_nonneg t]
      have e3 : 1 / 4 ≤ t ^ 2 := by nlinarith
      rw [hD]; nlinarith [sq_nonneg (c * x + d)]
  have hDpos : 0 < D := by linarith
  -- upper bound `D ≤ E (1 + t²)`
  have hDup : D ≤ E * (1 + t ^ 2) := by
    rw [hD]
    have h1 : |c * x + d| ≤ |c| + |d| := by
      calc |c * x + d| ≤ |c * x| + |d| := abs_add_le _ _
        _ = |c| * |x| + |d| := by rw [abs_mul]
        _ ≤ |c| * 1 + |d| := by gcongr; linarith
        _ = |c| + |d| := by ring
    have h2 : (c * x + d) ^ 2 ≤ E := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg c]) 2
    have h3 : (c * t) ^ 2 ≤ E * t ^ 2 := by
      rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg d]) 2
    nlinarith
  have hq : 0 < (A • w).im := (A • w).im_pos
  -- the `3` power
  have h3 : (A • w).im ^ (3 : ℝ) ≤ 64 * (1 + t ^ 6) := by
    have hle : (A • w).im ≤ 4 * t := by
      rw [him, div_le_iff₀ hDpos]; nlinarith
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (A • w).im ^ 3 ≤ (4 * t) ^ 3 := pow_le_pow_left₀ hq.le hle 3
    have h' : t ^ 3 ≤ 1 + t ^ 6 := by nlinarith [sq_nonneg (t ^ 3 - 1), pow_nonneg ht.le 3]
    nlinarith
  -- the `-6` power
  have h6 : (A • w).im ^ (-6 : ℝ) ≤ 729 * E ^ 6 * (1 + t ^ 6) := by
    have hinv : ((A • w).im)⁻¹ ≤ E * (2 + t) := by
      rw [him, inv_div, div_le_iff₀ ht]
      have : E * (1 + t ^ 2) ≤ E * (2 + t) * t := by
        have hE : 0 ≤ E := by positivity
        have : 1 + t ^ 2 ≤ (2 + t) * t := by nlinarith
        nlinarith
      linarith
    rw [show ((-6 : ℝ)) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hq.le, Real.rpow_natCast, ← inv_pow]
    calc ((A • w).im)⁻¹ ^ 6 ≤ (E * (2 + t)) ^ 6 := pow_le_pow_left₀ (by positivity) hinv 6
      _ = E ^ 6 * (2 + t) ^ 6 := by rw [mul_pow]
      _ ≤ E ^ 6 * (729 * (1 + t ^ 6)) := mul_le_mul_of_nonneg_left (pow_six_le t ht.le) (by positivity)
      _ = _ := by ring
  nlinarith

open GaloisForLFunctions.RHTower.SarnakXuePretrace in
theorem finite_cosets (p : ℕ) [NeZero p] : Finite (Cosets p) := by
  have h1 : (CongruenceSubgroup.Gamma p).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h2 := Subgroup.index_map_dvd (CongruenceSubgroup.Gamma p)
    (QuotientGroup.mk'_surjective modularActionKernel)
  have h3 : (gammaBar p).index ≠ 0 := fun h => h1 (by
    unfold gammaBar at h; rw [h] at h2; exact Nat.eq_zero_of_zero_dvd h2)
  haveI : (gammaBar p).FiniteIndex := ⟨h3⟩
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel _).symm

theorem continuous_weight : Continuous (fun z : ℍ => z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) := by
  have hc : Continuous (fun z : ℍ => z.im) := by fun_prop
  exact (hc.rpow_const (fun z => Or.inl z.im_pos.ne')).add (hc.rpow_const (fun z => Or.inr (by norm_num)))

open GaloisForLFunctions.RHTower.SarnakXuePretrace in
/-- **Cusp integrability**: `(y^{-6} + y^3)|f|` is integrable over the fundamental cell of `Γ(N+1)`. -/
theorem integrableOn_cellP (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    IntegrableOn (fun z : ℍ => (z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) * ‖f.1.1 z‖) (cellP (N + 1)) volume := by
  haveI := finite_cosets (N + 1)
  unfold cellP
  refine integrableOn_finite_iUnion.mpr (fun q => ?_)
  set g : PSL2Z := Quotient.out q
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective g
  have hgA : ∀ z : ℍ, g • z = A • z := fun z => by rw [← hA]; exact PSL2Z_mk_smul A z
  rw [IntegrableOn, ← Set.image_smul, ← ((measurePreserving_smul g volume).restrict_image_emb
    (measurableEmbedding_const_smul _) fd).integrable_comp_emb (measurableEmbedding_const_smul _)]
  obtain ⟨K, hK0, hK⟩ := im_smul_bound A
  have hint := (integrableOn_fd N lam (SelbergMaassCuspTransport.translate (N + 1) A f)).const_mul K
  refine hint.mono' ?_ (ae_restrict_of_forall_mem isClosed_fd.measurableSet (fun w hw => ?_))
  · exact ((continuous_weight.mul (continuous_source f).norm).comp (continuous_const_smul g)).aestronglyMeasurable
  · simp only [Function.comp_apply, hgA, SelbergMaassCuspTransport.translate_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := (A • w).im_pos; positivity)]
    calc ((A • w).im ^ (-6 : ℝ) + (A • w).im ^ (3 : ℝ)) * ‖f.1.1 (A • w)‖
        ≤ K * (1 + w.im ^ 6) * ‖f.1.1 (A • w)‖ := mul_le_mul_of_nonneg_right (hK w hw) (norm_nonneg _)
      _ = K * ((1 + w.im ^ 6) * ‖f.1.1 (A • w)‖) := by ring

end GaloisForLFunctions.RHTower.SelbergMaassExpDecayCell
