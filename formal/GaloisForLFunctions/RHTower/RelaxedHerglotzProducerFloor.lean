import GaloisForLFunctions.RHTower.RelaxedHerglotzProducerCompactness
import GaloisForLFunctions.RHTower.CarlsonHalfPlaneProducerFloor
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRemainderFourierTransform
import GaloisForLFunctions.RHTower.WindingAmplitude
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope

/-!
# The producer floor at `Re s = ½` is sharp exactly under RH

Herglotz producers on `Re s > σ₀` (`IsHerglotzProducerOn`) with weights `|lam(n)| ≤ log n`:

* **Floor** (`not_isHerglotzProducerOn_of_lt_half`, unconditional).  There is none for `σ₀ < ½`.
  The archimedean function `½ψ(s/2) − ½ log π + 1/s + 1/(s − 1)` has logarithmic growth on
  vertical strips (`norm_archPart_le`), so Carlson's mean value theorem applies
  (`CarlsonFloor.not_isHalfPlaneProducer_of_lt_half`): a producer left of `½` would make the
  Dirichlet series of `lam` absolutely convergent at `s = 1`, against its pole.
* **Sharpness** (`riemannHypothesis_iff_forall_gt_half_herglotzProducerOn`).  There is one for
  every `σ₀ > ½` if and only if RH holds.
* **Right of the strip** (`herglotzProducerOn_one_vonMangoldt`).  `Λ` is a producer on `Re s > 1`,
  with continuation `ξ′/ξ`.
* **The producer abscissa** (`producerAbscissa`, the infimum of the producer levels) lies in
  `[½, 1]` and is attained (`producerAbscissa_mem_producerLevels`, via the closedness theorem
  `exists_herglotzProducerOn_of_forall_gt`).  RH holds iff it equals `½`
  (`riemannHypothesis_iff_producerAbscissa_eq_half`).

So the set of half-planes carrying a producer is `(½, ∞)` under RH, and under ¬RH it stops at a
level strictly above `½`.  The producers need not be `Λ`; the condition involves only the weights
and the Gamma function.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.RelaxedHerglotz

/-- **Logarithmic growth of the archimedean function** on `0 < Re s ≤ 3`, `Im s ≥ 4`. -/
theorem norm_archPart_le {s : ℂ} (h0 : 0 < s.re) (h3 : s.re ≤ 3) (hT : 4 ≤ s.im) :
    ‖archPart s‖ ≤ 6 * Real.log s.im := by
  have hnorm_ge : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
  have hs4 : 4 ≤ ‖s‖ := hT.trans hnorm_ge
  have hnorm_le : ‖s‖ ≤ 2 * s.im := (Complex.norm_le_abs_re_add_abs_im s).trans (by
    rw [abs_of_pos h0, abs_of_pos (by linarith)]; linarith)
  have hlogim : 1 ≤ Real.log s.im := by
    have he : Real.exp 1 ≤ s.im := by have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log s.im := Real.log_le_log (Real.exp_pos 1) he
  have hlog2 : Real.log 2 ≤ Real.log s.im := Real.log_le_log (by norm_num) (by linarith)
  have hlogs : Real.log ‖s‖ ≤ 2 * Real.log s.im := by
    calc Real.log ‖s‖ ≤ Real.log (2 * s.im) := Real.log_le_log (by linarith) hnorm_le
      _ = Real.log 2 + Real.log s.im := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log s.im := by linarith
  have hlogs0 : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the real part of `ψ(s/2)`
  have hre := abs_re_digamma_half_sub_log_le h0 hs4
  have hre' : |(Complex.digamma (s / 2)).re| ≤ Real.log ‖s‖ + 23 / 16 := by
    have h1 : (20 + s.re) / ‖s‖ ^ 2 ≤ 23 / 16 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 := abs_sub_abs_le_abs_sub (Complex.digamma (s / 2)).re (Real.log ‖s‖ - Real.log 2)
    have h3 : |Real.log ‖s‖ - Real.log 2| ≤ Real.log ‖s‖ := by
      rw [abs_of_nonneg (by linarith)]; linarith
    linarith
  -- the imaginary part of `ψ(s/2)`
  have hs2 : s / 2 = ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have him := im_digamma_vertical_bound (σ := s.re / 2) (t := s.im / 2) (by linarith)
    (by linarith)
  rw [← hs2] at him
  have him' : |(Complex.digamma (s / 2)).im| ≤ 1 / 2 + 2 := by
    rw [abs_of_nonneg him.1]
    have h1 : 1 / (s.im / 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith [Real.pi_le_four, him.2]
  have hψ : ‖Complex.digamma (s / 2)‖ ≤ 2 * Real.log s.im + 4 := by
    have := Complex.norm_le_abs_re_add_abs_im (Complex.digamma (s / 2)); linarith
  -- the remaining terms
  have hpi : Real.log Real.pi ≤ 3 :=
    (Real.log_le_sub_one_of_pos Real.pi_pos).trans (by linarith [Real.pi_le_four])
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hinv1 : ‖1 / s‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hs4
  have hinv2 : ‖1 / (s - 1)‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one]
    have h1 : s.im ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at this
      exact (le_abs_self _).trans this
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hmid : ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖ ≤
      ‖Complex.digamma (s / 2)‖ / 2 + Real.log Real.pi / 2 := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi0]
    norm_num
  unfold archPart
  calc ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1 / (s - 1)‖
      ≤ ‖Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖ + ‖1 / s‖ + ‖1 / (s - 1)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 6 * Real.log s.im := by linarith

/-- The archimedean function is holomorphic on `Re s > σ₀ > 0` away from `s = 1`. -/
theorem differentiableOn_archPart {σ₀ : ℝ} (hσ₀ : 0 < σ₀) :
    DifferentiableOn ℂ archPart ({s : ℂ | σ₀ < s.re} \ {1}) := by
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  simp only [mem_setOf_eq] at hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hsne : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs0; linarith
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) s :=
    (differentiableAt_digamma_of_re_pos (by simp; linarith)).comp s
      ((differentiableAt_id).div_const 2)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold archPart
  exact (((hdg.div_const 2).sub_const _).add ((differentiableAt_const _).div differentiableAt_id
    hsne)).add ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1')

/-- A Herglotz producer on `Re s > σ₀` (`0 < σ₀ < 1`) is a producer in the sense of Carlson's floor
for the archimedean function. -/
theorem isHalfPlaneProducer_of_isHerglotzProducerOn {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1)
    {lam : ℕ → ℝ} (h : IsHerglotzProducerOn σ₀ lam) :
    CarlsonFloor.IsHalfPlaneProducer archPart σ₀ (WeilHerglotz.lamC lam) := by
  obtain ⟨Φ, hΦd, hΦre, hΦ⟩ := h
  have hopen : {s : ℂ | σ₀ < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_halfPlane σ₀).mem_nhds (by simpa using hσ₁)
  refine ⟨fun s => archPart s - Φ s, (differentiableOn_archPart hσ₀).sub (hΦd.mono sdiff_subset),
    fun s hs => ?_, ?_, fun s hs _ => ?_⟩
  · show archPart s - Φ s = _
    rw [hΦ s (by linarith), weilFunction_eq_archPart_sub]; ring
  · set g : ℂ → ℂ := fun s => Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s - Φ s
      with hg
    have hgc : ContinuousAt g 1 := by
      have hdg : ContinuousAt (fun s : ℂ => Complex.digamma (s / 2)) 1 :=
        ((differentiableAt_digamma_of_re_pos (by norm_num)).comp (1 : ℂ)
          ((differentiableAt_id).div_const 2)).continuousAt
      exact (((hdg.div_const 2).sub continuousAt_const).add
        (continuousAt_const.div continuousAt_id one_ne_zero)).sub
        ((hΦd.differentiableAt hopen).continuousAt)
    have hlim : Tendsto (fun s : ℂ => (s - 1) * g s + 1) (𝓝[≠] 1) (𝓝 ((1 - 1) * g 1 + 1)) :=
      (((continuousAt_id.sub continuousAt_const).mul hgc).add continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds
    rw [sub_self, zero_mul, zero_add] at hlim
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    simp only [hg, archPart]
    field_simp
    ring
  · simp only [sub_sub_cancel]
    exact hΦre s hs

/-- `|lam(n)| ≤ log n ≤ 2 n^{1/2}`. -/
theorem norm_lamC_le {lam : ℕ → ℝ} (hlam : ∀ n, |lam n| ≤ Real.log n) (n : ℕ) :
    ‖WeilHerglotz.lamC lam n‖ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hlog : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [div_eq_mul_inv] at this
    linarith
  unfold WeilHerglotz.lamC
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · exact (hlam n).trans hlog
  · rw [abs_zero]; positivity

/-- **The producer floor.**  No weight sequence with `|lam(n)| ≤ log n` is a Herglotz producer on a
half-plane `Re s > σ₀` with `σ₀ < ½`. -/
theorem not_isHerglotzProducerOn_of_lt_half {σ₀ : ℝ} (hσ₀ : σ₀ < 1 / 2) {lam : ℕ → ℝ}
    (hlam : ∀ n, |lam n| ≤ Real.log n) : ¬ IsHerglotzProducerOn σ₀ lam := by
  intro h
  set σ₁ : ℝ := max σ₀ (1 / 4) with hσ₁
  have hσ₁0 : 0 < σ₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hσ₁h : σ₁ < 1 / 2 := max_lt hσ₀ (by norm_num)
  have h1 := h.mono (le_max_left σ₀ (1 / 4))
  refine CarlsonFloor.not_isHalfPlaneProducer_of_lt_half archPart hσ₁0 hσ₁h
    (differentiableOn_archPart hσ₁0) (K₀ := 6) (T₁ := 4) (by norm_num)
    (fun s hs h3 hT => norm_archPart_le (by linarith) h3 hT) (WeilHerglotz.lamC lam)
    (C := 2) (θ := 1 / 2) (by norm_num) (by norm_num) (norm_lamC_le hlam)
    (isHalfPlaneProducer_of_isHerglotzProducerOn hσ₁0 (by linarith) h1)

/-- **The floor is sharp exactly under RH.**  The Riemann hypothesis holds if and only if every
half-plane `Re s > σ₀` with `σ₀ > ½` carries a Herglotz producer with `|lam(n)| ≤ log n`. -/
theorem riemannHypothesis_iff_forall_gt_half_herglotzProducerOn :
    RiemannHypothesis ↔ ∀ σ₀ : ℝ, 1 / 2 < σ₀ → ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧
      IsHerglotzProducerOn σ₀ lam := by
  rw [riemannHypothesis_iff_forall_herglotzProducerOn]
  constructor
  · intro h σ₀ hσ₀
    obtain ⟨lam, hlam, hp⟩ := h (σ₀ - 1 / 2) (by linarith)
    exact ⟨lam, hlam, by simpa using hp⟩
  · intro h δ hδ
    exact h (1 / 2 + δ) (by linarith)

/-- The von Mangoldt weights pass through `lamC` unchanged. -/
theorem lamC_vonMangoldt :
    WeilHerglotz.lamC (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  unfold WeilHerglotz.lamC
  split_ifs with hn
  · rfl
  · interval_cases n <;> simp

/-- **The von Mangoldt weights are a producer on `Re s > 1`**, unconditionally: `ξ′/ξ` is the
continuation, with nonnegative real part right of the strip. -/
theorem herglotzProducerOn_one_vonMangoldt :
    IsHerglotzProducerOn 1 fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  refine ⟨logDeriv xi, fun s hs => ?_, fun s hs => re_logDeriv_xi_nonneg_of_one_le_re hs.le,
    fun s hs => ?_⟩
  · simp only [mem_setOf_eq] at hs
    have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re hs.le
    exact (((xi_differentiable.analyticAt s).deriv.differentiableAt).div
      (xi_differentiable s) hxi).differentiableWithinAt
  · rw [WeilSpectral.logDeriv_xi_eq_datum hs, weilFunction_eq_archPart_sub, lamC_vonMangoldt]
    unfold archPart zetaArchimedeanDatum
    ring

/-- **The producer abscissa lies in `[½, 1]`.**  Some log-bounded weight is a producer on
`Re s > 1`, and none is a producer left of `½`. -/
theorem exists_herglotzProducerOn_one_and_floor :
    (∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧ IsHerglotzProducerOn 1 lam) ∧
      ∀ σ₀ : ℝ, σ₀ < 1 / 2 → ∀ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) →
        ¬ IsHerglotzProducerOn σ₀ lam := by
  refine ⟨⟨fun n => ArithmeticFunction.vonMangoldt n, fun n => ?_,
    herglotzProducerOn_one_vonMangoldt⟩, fun σ₀ hσ₀ lam hlam =>
      not_isHerglotzProducerOn_of_lt_half hσ₀ hlam⟩
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log

/-- The levels `σ₀` whose half-plane `Re s > σ₀` carries a producer with `|lam(n)| ≤ log n`. -/
def producerLevels : Set ℝ :=
  {σ₀ | ∃ lam : ℕ → ℝ, (∀ n, |lam n| ≤ Real.log n) ∧ IsHerglotzProducerOn σ₀ lam}

/-- The **producer abscissa**: the infimum of the producer levels. -/
def producerAbscissa : ℝ := sInf producerLevels

theorem one_mem_producerLevels : (1 : ℝ) ∈ producerLevels :=
  exists_herglotzProducerOn_one_and_floor.1

theorem half_le_of_mem_producerLevels {σ₀ : ℝ} (h : σ₀ ∈ producerLevels) : 1 / 2 ≤ σ₀ := by
  by_contra hlt
  obtain ⟨lam, hlam, hp⟩ := h
  exact not_isHerglotzProducerOn_of_lt_half (not_le.mp hlt) hlam hp

theorem bddBelow_producerLevels : BddBelow producerLevels :=
  ⟨1 / 2, fun _ h => half_le_of_mem_producerLevels h⟩

theorem mem_producerLevels_of_le {σ₀ σ₁ : ℝ} (h : σ₀ ∈ producerLevels) (hσ : σ₀ ≤ σ₁) :
    σ₁ ∈ producerLevels := by
  obtain ⟨lam, hlam, hp⟩ := h
  exact ⟨lam, hlam, hp.mono hσ⟩

theorem half_le_producerAbscissa : 1 / 2 ≤ producerAbscissa :=
  le_csInf ⟨1, one_mem_producerLevels⟩ fun _ h => half_le_of_mem_producerLevels h

theorem producerAbscissa_le_one : producerAbscissa ≤ 1 :=
  csInf_le bddBelow_producerLevels one_mem_producerLevels

/-- **The producer abscissa is attained**: `Re s > producerAbscissa` carries a log-bounded
producer, and no half-plane further left does. -/
theorem producerAbscissa_mem_producerLevels : producerAbscissa ∈ producerLevels := by
  rcases eq_or_lt_of_le producerAbscissa_le_one with h1 | h1
  · rw [h1]; exact one_mem_producerLevels
  refine exists_herglotzProducerOn_of_forall_gt
    (by linarith [half_le_producerAbscissa]) h1 fun δ hδ => ?_
  obtain ⟨σ₀, hσ₀, hlt⟩ := exists_lt_of_csInf_lt ⟨1, one_mem_producerLevels⟩
    (by linarith : producerAbscissa < producerAbscissa + δ)
  exact mem_producerLevels_of_le hσ₀ hlt.le

theorem not_mem_producerLevels_of_lt {σ₀ : ℝ} (h : σ₀ < producerAbscissa) :
    σ₀ ∉ producerLevels := fun hm => not_le.mpr h (csInf_le bddBelow_producerLevels hm)

/-- **RH is the producer abscissa `½`.** -/
theorem riemannHypothesis_iff_producerAbscissa_eq_half :
    RiemannHypothesis ↔ producerAbscissa = 1 / 2 := by
  rw [riemannHypothesis_iff_forall_gt_half_herglotzProducerOn]
  constructor
  · intro h
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) half_le_producerAbscissa
    obtain ⟨lam, hlam, hp⟩ := h (1 / 2 + ε / 2) (by linarith)
    exact lt_of_le_of_lt (csInf_le bddBelow_producerLevels ⟨lam, hlam, hp⟩) (by linarith)
  · intro h σ₀ hσ₀
    have := mem_producerLevels_of_le producerAbscissa_mem_producerLevels
      (show producerAbscissa ≤ σ₀ by rw [h]; exact hσ₀.le)
    exact this

end RHTower.RelaxedHerglotz
