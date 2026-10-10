import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalMeanCriterion
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroHurwitz

/-!
# RH as a zero-free right half-plane of the zero heat trace

`ν(τ) = Σ_q e^{-τ w_q}` with `w_q = z_q²`.

**Theorem** (`riemannHypothesis_iff_xiGaussianHeatTraceC_zeroFree_halfPlane`).  RH holds iff `ν` has
no zeros in some right half-plane `Re τ > a₀`.  Equivalently
(`riemannHypothesis_iff_primeChirp_ne_arch_add_pole_halfPlane`), the prime chirp equation
`(π/τ)^{1/2} S(τ) = Arch(τ) + 2π e^{τ/4}` has no solution far to the right.

Under RH, `ν` is a Dirichlet series in `τ` with positive frequencies `γ²`, and its first term
dominates on `Re τ ≫ 1`.  Without RH, `ν` has zeros with arbitrarily large real part.

Mechanism of the converse (`exists_zero_xiGaussianHeatTraceC_of_balance`).  Choose `β ≥ 0` and the
minimal value `ℓ` of `κ_q = Re w_q − β Im w_q` so that two distinct frequencies attain it: the
conjugate pair `w, w̄` at the minimal real part, or else the minimal real frequency together with the
steepest off-line frequency.  Along `p_n = n(1 + iβ)` the normalized translates
`ν(p_n + ζ) e^{nℓ}` converge (on a subsequence fixing the phases) to the exponential sum
`F(ζ) = Σ_{κ_q = ℓ} θ_q e^{-ζ w_q}`, uniformly on disks, because every other term carries
`e^{-n(κ_q − ℓ)}`.  `F` has at least two distinct frequencies, so it has an isolated zero
(`exists_isolated_zero_of_finset_frequencies`), and Hurwitz's theorem
(`ne_zero_of_tendstoUniformlyOn_of_forall_ne_zero`) forbids this limit of zero-free translates.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-! ## Heat frequencies -/

/-- The heat frequency `w_q = z_q²` of a zero copy. -/
def xiHeatFrequency (q : XiZeroCopy) : ℂ := xiSpectralPoint q ^ (2 : ℕ)

theorem xiHeatFrequency_re (q : XiZeroCopy) :
    (xiHeatFrequency q).re = (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 := by
  rw [xiHeatFrequency, pow_two, Complex.mul_re]; ring

theorem xiHeatFrequency_im (q : XiZeroCopy) :
    (xiHeatFrequency q).im = 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
  rw [xiHeatFrequency, pow_two, Complex.mul_im]; ring

theorem norm_xiHeatFrequency_le (q : XiZeroCopy) :
    ‖xiHeatFrequency q‖ ≤ (xiSpectralPoint q).re ^ 2 + 1 / 4 := by
  rw [xiHeatFrequency, norm_pow, Complex.sq_norm, Complex.normSq_apply]
  nlinarith [xiSpectralPoint_im_sq_lt_quarter q]

theorem xiGaussianHeatTermC_eq_exp (τ : ℂ) (q : XiZeroCopy) :
    xiGaussianHeatTermC τ q = Complex.exp (-τ * xiHeatFrequency q) := rfl

/-- The tilted real part `κ_β(q) = Re w_q − β Im w_q`. -/
def xiHeatTilt (β : ℝ) (q : XiZeroCopy) : ℝ := (xiHeatFrequency q).re - β * (xiHeatFrequency q).im

theorem le_xiHeatTilt {β : ℝ} (hβ : 0 ≤ β) (q : XiZeroCopy) :
    (xiSpectralPoint q).re ^ 2 / 2 - 1 / 4 - β ^ 2 / 2 ≤ xiHeatTilt β q := by
  rw [xiHeatTilt, xiHeatFrequency_re, xiHeatFrequency_im]
  set γ := (xiSpectralPoint q).re
  set η := (xiSpectralPoint q).im
  have hη := xiSpectralPoint_im_sq_lt_quarter q
  have h2η : 2 * |η| ≤ 1 := by nlinarith [sq_abs η, abs_nonneg η, sq_nonneg (2 * |η| - 1)]
  have h1 : β * (2 * γ * η) ≤ β * |γ| := by
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) hβ
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg γ, abs_nonneg η]
  have h2 : β * |γ| ≤ γ ^ 2 / 2 + β ^ 2 / 2 := by nlinarith [sq_nonneg (|γ| - β), sq_abs γ]
  nlinarith

theorem finite_xiHeatTilt_le {β C : ℝ} (hβ : 0 ≤ β) :
    {q : XiZeroCopy | xiHeatTilt β q ≤ C}.Finite := by
  refine (finite_xiOrdinateWindow (Real.sqrt (2 * C + 1 / 2 + β ^ 2)) 0).subset ?_
  intro q hq
  rw [mem_xiOrdinateWindow_iff, sub_zero, ← xiSpectralPoint_re_eq]
  have h := le_xiHeatTilt hβ q
  have h2 : (xiSpectralPoint q).re ^ 2 ≤ 2 * C + 1 / 2 + β ^ 2 := by
    have : xiHeatTilt β q ≤ C := hq
    linarith
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h2

/-- **Uniform summability far to the right.** -/
theorem summable_exp_neg_xiHeatTilt {β ℓ R x : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R) (hx : 2 * R + 2 ≤ x) :
    Summable (fun q : XiZeroCopy =>
      Real.exp (-(x * (xiHeatTilt β q - ℓ)) + R * ‖xiHeatFrequency q‖)) := by
  set K : ℝ := x * (1 / 4 + β ^ 2 / 2 + ℓ) + R / 4 with hK
  refine ((summable_norm_xiGaussianHeatTermC (τ := 1) (by simp)).mul_left (Real.exp K))
    |>.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun q => ?_
  rw [norm_xiGaussianHeatTermC, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  simp only [one_re, one_im, zero_mul, sub_zero, one_mul]
  have h1 := le_xiHeatTilt hβ q
  have h2 := norm_xiHeatFrequency_le q
  have h3 : (xiSpectralPoint q ^ (2 : ℕ)).re ≤ (xiSpectralPoint q).re ^ 2 := by
    have := xiHeatFrequency_re q
    rw [xiHeatFrequency] at this
    rw [this]; nlinarith [sq_nonneg (xiSpectralPoint q).im]
  have hx0 : 0 ≤ x := by linarith
  have h4 : x * ((xiSpectralPoint q).re ^ 2 / 2 - 1 / 4 - β ^ 2 / 2) ≤ x * xiHeatTilt β q :=
    mul_le_mul_of_nonneg_left h1 hx0
  have h5 : R * ‖xiHeatFrequency q‖ ≤ R * ((xiSpectralPoint q).re ^ 2 + 1 / 4) :=
    mul_le_mul_of_nonneg_left h2 hR
  have h6 : 0 ≤ (x / 2 - R - 1) * (xiSpectralPoint q).re ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [hK]
  nlinarith

/-! ## Translates along `n(1 + iβ)` -/

/-- The sample point `n(1 + iβ)`. -/
def heatSamplePoint (β : ℝ) (n : ℕ) : ℂ := (n : ℂ) * (1 + (β : ℂ) * I)

theorem re_heatSamplePoint (β : ℝ) (n : ℕ) : (heatSamplePoint β n).re = n := by
  simp [heatSamplePoint]

/-- The modulus of a term at the sample point. -/
theorem re_neg_heatSamplePoint_mul (β : ℝ) (n : ℕ) (q : XiZeroCopy) :
    (-(heatSamplePoint β n) * xiHeatFrequency q).re = -(n * xiHeatTilt β q) := by
  simp only [heatSamplePoint, xiHeatTilt, neg_mul, neg_re, Complex.mul_re, Complex.add_re,
    Complex.add_im, one_re, one_im, ofReal_re, ofReal_im, Complex.mul_im, I_re, I_im,
    natCast_re, natCast_im]
  ring

/-- The normalized translate `ν(n(1 + iβ) + ζ) e^{nℓ}`. -/
def heatTranslate (β ℓ : ℝ) (n : ℕ) (ζ : ℂ) : ℂ :=
  xiGaussianHeatTraceC (heatSamplePoint β n + ζ) * Complex.exp (((n : ℝ) * ℓ : ℝ) : ℂ)

/-- The phase factor of a term at the sample point. -/
def heatPhase (β ℓ : ℝ) (n : ℕ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-(heatSamplePoint β n) * xiHeatFrequency q + (((n : ℝ) * ℓ : ℝ) : ℂ))

theorem norm_heatPhase (β ℓ : ℝ) (n : ℕ) (q : XiZeroCopy) :
    ‖heatPhase β ℓ n q‖ = Real.exp (-(n * (xiHeatTilt β q - ℓ))) := by
  rw [heatPhase, Complex.norm_exp, add_re, re_neg_heatSamplePoint_mul, ofReal_re]
  congr 1; ring

/-- Each term of the translate factors through the phase. -/
theorem heatTerm_translate_eq (β ℓ : ℝ) (n : ℕ) (ζ : ℂ) (q : XiZeroCopy) :
    xiGaussianHeatTermC (heatSamplePoint β n + ζ) q * Complex.exp (((n : ℝ) * ℓ : ℝ) : ℂ) =
      heatPhase β ℓ n q * Complex.exp (-ζ * xiHeatFrequency q) := by
  rw [xiGaussianHeatTermC_eq_exp, heatPhase, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; ring

theorem norm_exp_neg_mul_le_exp_mul_norm {ζ w : ℂ} {R : ℝ} (hζ : ‖ζ‖ ≤ R) :
    ‖Complex.exp (-ζ * w)‖ ≤ Real.exp (R * ‖w‖) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
  rw [norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)

theorem tendsto_exp_neg_natCast_mul_add_atTop {c d : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-(n * c) + d)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  refine tendsto_atBot_add_const_right _ d ?_
  exact tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hc)

/-- **Convergence of the normalized translates.**  If every tilt is at least `ℓ`, `D` is the set
where it equals `ℓ`, and the phases converge along `φ`, then the translates converge uniformly on
the disk `‖ζ‖ ≤ R` to `F(ζ) = Σ_{q ∈ D} θ_q e^{-ζ w_q}`. -/
theorem tendstoUniformlyOn_heatTranslate {β ℓ R : ℝ} (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (hκ : ∀ q, ℓ ≤ xiHeatTilt β q) (D : Finset XiZeroCopy)
    (hD : ∀ q, q ∈ D ↔ xiHeatTilt β q = ℓ) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {θ : XiZeroCopy → ℂ} (hθ : ∀ q ∈ D, Tendsto (fun k => heatPhase β ℓ (φ k) q) atTop (𝓝 (θ q))) :
    TendstoUniformlyOn (fun k ζ => heatTranslate β ℓ (φ k) ζ)
      (fun ζ => ∑ q ∈ D, θ q * Complex.exp (-ζ * xiHeatFrequency q)) atTop (closedBall 0 R) := by
  classical
  set g : ℕ → XiZeroCopy → ℝ := fun n q =>
    if q ∈ D then 0 else Real.exp (-(n * (xiHeatTilt β q - ℓ)) + R * ‖xiHeatFrequency q‖) with hg
  set N₀ : ℕ := ⌈2 * R + 2⌉₊ with hN₀def
  have hN₀ : 2 * R + 2 ≤ (N₀ : ℝ) := Nat.le_ceil _
  have hsum₀ := summable_exp_neg_xiHeatTilt (ℓ := ℓ) hβ hR hN₀
  have hg0 : ∀ n q, 0 ≤ g n q := fun n q => by
    simp only [hg]; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  have hgle : ∀ n, N₀ ≤ n → ∀ q, g n q ≤
      Real.exp (-((N₀ : ℝ) * (xiHeatTilt β q - ℓ)) + R * ‖xiHeatFrequency q‖) := by
    intro n hn q
    simp only [hg]
    split_ifs
    · exact (Real.exp_pos _).le
    · refine Real.exp_le_exp.2 ?_
      have h1 : (N₀ : ℝ) ≤ n := by exact_mod_cast hn
      have h2 : 0 ≤ xiHeatTilt β q - ℓ := sub_nonneg.2 (hκ q)
      nlinarith
  have hgsum : ∀ n, N₀ ≤ n → Summable (g n) := fun n hn =>
    hsum₀.of_nonneg_of_le (hg0 n) (hgle n hn)
  have hT : Tendsto (fun n => ∑' q, g n q) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := g) (g := fun _ => (0 : ℝ)) hsum₀
      (fun q => ?_) ?_
    · simpa using h
    · by_cases hq : q ∈ D
      · simp only [hg, if_pos hq]; exact tendsto_const_nhds
      · simp only [hg, if_neg hq]
        have hpos : 0 < xiHeatTilt β q - ℓ := by
          rcases (sub_nonneg.2 (hκ q)).eq_or_lt with h | h
          · exact absurd ((hD q).2 (by linarith)) hq
          · exact h
        exact tendsto_exp_neg_natCast_mul_add_atTop hpos
    · filter_upwards [eventually_ge_atTop N₀] with n hn q
      rw [Real.norm_of_nonneg (hg0 n q)]
      exact hgle n hn q
  have hfin : Tendsto (fun k => ∑ q ∈ D, ‖heatPhase β ℓ (φ k) q - θ q‖ *
      Real.exp (R * ‖xiHeatFrequency q‖)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum D fun q hq =>
      (((hθ q hq).sub_const (θ q)).norm).mul_const (Real.exp (R * ‖xiHeatFrequency q‖))
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(hT.comp hφ).eventually (gt_mem_nhds (half_pos hε)),
    hfin.eventually (gt_mem_nhds (half_pos hε)), hφ.eventually (eventually_ge_atTop N₀)]
    with k hk1 hk2 hk3
  intro ζ hζ
  have hζR : ‖ζ‖ ≤ R := by simpa using hζ
  set n := φ k with hn
  have hnR : (2 * R + 2 : ℝ) ≤ n := hN₀.trans (by exact_mod_cast hk3)
  have hτ : 0 < (heatSamplePoint β n + ζ).re := by
    rw [add_re, re_heatSamplePoint]
    have := Complex.re_le_norm (-ζ)
    rw [neg_re, norm_neg] at this
    linarith
  set f : XiZeroCopy → ℂ := fun q => heatPhase β ℓ n q * Complex.exp (-ζ * xiHeatFrequency q)
    with hf
  have hfsum : Summable (fun q => ‖f q‖) := by
    refine ((summable_norm_xiGaussianHeatTermC hτ).mul_right
      ‖Complex.exp ((((n : ℝ) * ℓ : ℝ)) : ℂ)‖).congr fun q => ?_
    rw [hf]
    simp only
    rw [← heatTerm_translate_eq, norm_mul]
  have hexp : heatTranslate β ℓ n ζ = ∑ q ∈ D, f q + ∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, f q := by
    rw [heatTranslate, xiGaussianHeatTraceC, ← tsum_mul_right]
    rw [tsum_congr fun q => heatTerm_translate_eq β ℓ n ζ q]
    exact (hfsum.of_norm.sum_add_tsum_compl).symm
  rw [dist_eq_norm, hexp]
  have hsplit : (∑ q ∈ D, θ q * Complex.exp (-ζ * xiHeatFrequency q)) -
      (∑ q ∈ D, f q + ∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, f q) =
        ∑ q ∈ D, (θ q - heatPhase β ℓ n q) * Complex.exp (-ζ * xiHeatFrequency q) -
          ∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, f q := by
    rw [hf, ← sub_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit]
  have hA : ‖∑ q ∈ D, (θ q - heatPhase β ℓ n q) * Complex.exp (-ζ * xiHeatFrequency q)‖ < ε / 2 := by
    refine lt_of_le_of_lt ((norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)) hk2
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le_exp_mul_norm hζR) (norm_nonneg _)
  have hB : ‖∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, f q‖ < ε / 2 := by
    refine lt_of_le_of_lt ?_ hk1
    refine (norm_tsum_le_tsum_norm (hfsum.subtype _)).trans ?_
    have hle : ∀ q : ↑(↑D : Set XiZeroCopy)ᶜ, ‖f q‖ ≤ g n q := by
      intro q
      have hq : (q : XiZeroCopy) ∉ D := q.2
      simp only [hg, if_neg hq]
      rw [hf]
      simp only
      rw [norm_mul, norm_heatPhase, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le_exp_mul_norm hζR) (Real.exp_pos _).le
    refine ((hfsum.subtype _).tsum_le_tsum hle ((hgsum n hk3).subtype _)).trans ?_
    exact Summable.tsum_subtype_le (g n) _ (hg0 n) (hgsum n hk3)
  calc _ ≤ ‖∑ q ∈ D, (θ q - heatPhase β ℓ n q) * Complex.exp (-ζ * xiHeatFrequency q)‖ +
        ‖∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, f q‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hA hB
    _ = ε := by ring

theorem analyticAt_heatTranslate {β ℓ : ℝ} {n : ℕ} {ζ : ℂ}
    (hζ : 0 < (heatSamplePoint β n + ζ).re) : AnalyticAt ℂ (heatTranslate β ℓ n) ζ := by
  have hopen : IsOpen {ξ : ℂ | 0 < (heatSamplePoint β n + ξ).re} :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_const.add continuous_id))
  refine DifferentiableOn.analyticAt (s := {ξ : ℂ | 0 < (heatSamplePoint β n + ξ).re})
    (fun ξ hξ => ?_) (hopen.mem_nhds hζ)
  refine (DifferentiableAt.mul ?_ (differentiableAt_const _)).differentiableWithinAt
  exact (differentiableAt_xiGaussianHeatTraceC hξ).comp ξ
    ((differentiableAt_const _).add differentiableAt_id)

/-- **A balanced pair of frequencies forces zeros far to the right.**  If every tilt
`Re w_q − β Im w_q` is at least `ℓ` and two copies with distinct frequencies attain `ℓ`, then `ν` has a
zero in every right half-plane. -/
theorem exists_zero_xiGaussianHeatTraceC_of_balance {β ℓ : ℝ} (hβ : 0 ≤ β)
    (hκ : ∀ q, ℓ ≤ xiHeatTilt β q) {q₁ q₂ : XiZeroCopy} (h₁ : xiHeatTilt β q₁ = ℓ)
    (h₂ : xiHeatTilt β q₂ = ℓ) (hne : xiHeatFrequency q₁ ≠ xiHeatFrequency q₂) (a₀ : ℝ) :
    ∃ τ : ℂ, a₀ < τ.re ∧ xiGaussianHeatTraceC τ = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hDfin : {q : XiZeroCopy | xiHeatTilt β q = ℓ}.Finite :=
    (finite_xiHeatTilt_le (C := ℓ) hβ).subset fun q hq => le_of_eq hq
  set D := hDfin.toFinset with hDdef
  have hD : ∀ q, q ∈ D ↔ xiHeatTilt β q = ℓ := fun q => hDfin.mem_toFinset
  -- the phases along a subsequence
  set u : ℕ → (D → ℂ) := fun n q => heatPhase β ℓ n q with hu
  have hunorm : ∀ n (q : D), ‖u n q‖ = 1 := by
    intro n q
    simp only [hu]
    rw [norm_heatPhase, (hD q).1 q.2, sub_self, mul_zero, neg_zero, Real.exp_zero]
  have hball : ∀ n, u n ∈ closedBall (0 : D → ℂ) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun q => (hunorm n q).le
  obtain ⟨θv, -, φ, hφmono, hφlim⟩ := (isCompact_closedBall (0 : D → ℂ) 1).tendsto_subseq hball
  set θ : XiZeroCopy → ℂ := fun q => if h : q ∈ D then θv ⟨q, h⟩ else 0 with hθdef
  have hθ : ∀ q ∈ D, Tendsto (fun k => heatPhase β ℓ (φ k) q) atTop (𝓝 (θ q)) := by
    intro q hq
    have h := ((continuous_apply (⟨q, hq⟩ : D)).tendsto θv).comp hφlim
    rw [show θ q = θv ⟨q, hq⟩ by simp [hθdef, hq]]
    exact h
  have hθnorm : ∀ q ∈ D, ‖θ q‖ = 1 := by
    intro q hq
    have h1 := (hθ q hq).norm
    have h2 : (fun k => ‖heatPhase β ℓ (φ k) q‖) = fun _ => (1 : ℝ) :=
      funext fun k => hunorm (φ k) ⟨q, hq⟩
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hθw : ∀ q ∈ D, ∀ q' ∈ D, xiHeatFrequency q = xiHeatFrequency q' → θ q = θ q' := by
    intro q hq q' hq' hw
    have h1 := hθ q hq
    have heq : (fun k => heatPhase β ℓ (φ k) q) = fun k => heatPhase β ℓ (φ k) q' := by
      funext k; simp only [heatPhase, hw]
    rw [heq] at h1
    exact tendsto_nhds_unique h1 (hθ q' hq')
  -- the limit exponential sum and its distinct frequencies
  set W : Finset ℂ := D.image fun q => -xiHeatFrequency q with hW
  set A : ℂ → ℂ := fun c => ∑ q ∈ D with -xiHeatFrequency q = c, θ q with hA
  have hFA : ∀ ζ, ∑ q ∈ D, θ q * Complex.exp (-ζ * xiHeatFrequency q) =
      ∑ c ∈ W, A c * Complex.exp (c * ζ) := by
    intro ζ
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun q => -xiHeatFrequency q) (t := W)
      (fun q hq => Finset.mem_image_of_mem _ hq)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← (Finset.mem_filter.1 hq).2]
    ring_nf
  have hW2 : 2 ≤ W.card := by
    have hq₁ : -xiHeatFrequency q₁ ∈ W := Finset.mem_image_of_mem _ ((hD q₁).2 h₁)
    have hq₂ : -xiHeatFrequency q₂ ∈ W := Finset.mem_image_of_mem _ ((hD q₂).2 h₂)
    have hne' : -xiHeatFrequency q₁ ≠ -xiHeatFrequency q₂ := fun h => hne (neg_injective h)
    exact Finset.one_lt_card.2 ⟨_, hq₁, _, hq₂, hne'⟩
  have hAne : ∀ c ∈ W, A c ≠ 0 := by
    intro c hc
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hc
    have hall : ∀ q ∈ D.filter (fun q => -xiHeatFrequency q = -xiHeatFrequency q₀),
        θ q = θ q₀ := by
      intro q hq
      obtain ⟨hqD, hqw⟩ := Finset.mem_filter.1 hq
      exact hθw q hqD q₀ hq₀ (neg_injective hqw)
    simp only [hA]
    rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul]
    refine mul_ne_zero ?_ ?_
    · have hmem : q₀ ∈ D.filter (fun q => -xiHeatFrequency q = -xiHeatFrequency q₀) :=
        Finset.mem_filter.2 ⟨hq₀, rfl⟩
      exact_mod_cast (Finset.card_pos.2 ⟨q₀, hmem⟩).ne'
    · intro h0
      have := hθnorm q₀ hq₀
      rw [h0, norm_zero] at this
      norm_num at this
  obtain ⟨ζ₀, hζ₀, r, hr, hsph⟩ :=
    GaloisForLFunctions.HTGeometry.exists_isolated_zero_of_finset_frequencies W hW2 A hAne
  -- Hurwitz on the disk about `ζ₀`
  set F : ℂ → ℂ := fun ζ => ∑ q ∈ D, θ q * Complex.exp (-ζ * xiHeatFrequency q) with hF
  set R : ℝ := ‖ζ₀‖ + r with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hconv := tendstoUniformlyOn_heatTranslate hβ hR0 hκ D hD hφmono.tendsto_atTop hθ
  have hsub : closedBall ζ₀ r ⊆ closedBall 0 R := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right]
    rw [mem_closedBall, dist_eq_norm] at hζ
    calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
      _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
      _ ≤ R := by rw [hRdef]; linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, max a₀ 0 + R < φ k₀ := by
    obtain ⟨k₀, hk₀⟩ := (hφmono.tendsto_atTop.eventually
      (eventually_gt_atTop ⌈max a₀ 0 + R⌉₊)).exists
    exact ⟨k₀, (Nat.le_ceil _).trans_lt (by exact_mod_cast hk₀)⟩
  set gk : ℕ → ℂ → ℂ := fun k => heatTranslate β ℓ (φ (k + k₀)) with hgk
  have hre : ∀ k, ∀ ζ ∈ closedBall ζ₀ r, max a₀ 0 < (heatSamplePoint β (φ (k + k₀)) + ζ).re := by
    intro k ζ hζ
    have hζR : ‖ζ‖ ≤ R := by simpa using hsub hζ
    have hmono : φ k₀ ≤ φ (k + k₀) := hφmono.monotone (by omega)
    rw [add_re, re_heatSamplePoint]
    have h1 := Complex.re_le_norm (-ζ)
    rw [neg_re, norm_neg] at h1
    have h2 : (φ k₀ : ℝ) ≤ φ (k + k₀) := by exact_mod_cast hmono
    linarith
  have hgan : ∀ k, AnalyticOnNhd ℂ (gk k) (closedBall ζ₀ r) := fun k ζ hζ =>
    analyticAt_heatTranslate ((le_max_right _ _).trans_lt (hre k ζ hζ))
  have hg0 : ∀ k, ∀ ζ ∈ closedBall ζ₀ r, gk k ζ ≠ 0 := by
    intro k ζ hζ
    simp only [hgk, heatTranslate]
    exact mul_ne_zero (hcon _ ((le_max_left _ _).trans_lt (hre k ζ hζ))) (Complex.exp_ne_zero _)
  have hconv' : TendstoUniformlyOn gk F atTop (closedBall ζ₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := Metric.tendstoUniformlyOn_iff.1 (hconv.mono hsub) ε hε
    exact (tendsto_add_atTop_nat k₀).eventually h
  have hFc : ContinuousOn F (sphere ζ₀ r) := by
    refine Continuous.continuousOn ?_
    rw [hF]; fun_prop
  have hFne : ∀ u ∈ sphere ζ₀ r, F u ≠ 0 := by
    intro u hu
    rw [hF]; simp only
    rw [hFA u]; exact hsph u hu
  have hHur := GaloisForLFunctions.HTGeometry.ne_zero_of_tendstoUniformlyOn_of_forall_ne_zero hr
    hgan hg0 hconv' hFc hFne
  apply hHur
  rw [hF]; simp only
  rw [hFA ζ₀]; exact hζ₀

/-! ## Balanced configurations without RH -/

theorem exists_isMinOn_xiHeatTilt {β : ℝ} (hβ : 0 ≤ β) :
    ∃ q₀ : XiZeroCopy, ∀ q, xiHeatTilt β q₀ ≤ xiHeatTilt β q := by
  classical
  obtain ⟨q₁⟩ := xiZeroCopy_nonempty
  have hfin := finite_xiHeatTilt_le (C := xiHeatTilt β q₁) hβ
  obtain ⟨q₀, hq₀, hmin⟩ := hfin.toFinset.exists_min_image (xiHeatTilt β)
    ⟨q₁, hfin.mem_toFinset.2 (show xiHeatTilt β q₁ ≤ xiHeatTilt β q₁ from le_rfl)⟩
  refine ⟨q₀, fun q => ?_⟩
  by_cases hq : xiHeatTilt β q ≤ xiHeatTilt β q₁
  · exact hmin q (hfin.mem_toFinset.2 hq)
  · push Not at hq
    have := hmin q₁ (hfin.mem_toFinset.2 (show xiHeatTilt β q₁ ≤ xiHeatTilt β q₁ from le_rfl))
    linarith

theorem xiHeatFrequency_lineConj (q : XiZeroCopy) :
    xiHeatFrequency (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (xiHeatFrequency q) := by
  rw [xiHeatFrequency, xiHeatFrequency, xiSpectralPoint_lineConj, map_pow]

theorem xiHeatFrequency_im_ne_zero_iff (q : XiZeroCopy) :
    (xiHeatFrequency q).im ≠ 0 ↔ (xiSpectralPoint q).im ≠ 0 := by
  rw [xiHeatFrequency_im]
  have hγ : (xiSpectralPoint q).re ≠ 0 := by
    intro h
    have := xiSpectralPoint_re_sq_gt_floor q
    rw [h] at this
    norm_num at this
  constructor
  · intro h h0; exact h (by rw [h0]; ring)
  · intro h h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · norm_num at h2
      · exact hγ h2
    · exact h h1

/-- **Without RH there is a balanced pair of frequencies.** -/
theorem exists_balance_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ β ℓ : ℝ, 0 ≤ β ∧ (∀ q, ℓ ≤ xiHeatTilt β q) ∧ ∃ q₁ q₂ : XiZeroCopy,
      xiHeatTilt β q₁ = ℓ ∧ xiHeatTilt β q₂ = ℓ ∧ xiHeatFrequency q₁ ≠ xiHeatFrequency q₂ := by
  classical
  obtain ⟨qm, hqm⟩ := exists_isMinOn_xiHeatTilt (β := 0) le_rfl
  have htilt0 : ∀ q, xiHeatTilt 0 q = (xiHeatFrequency q).re := fun q => by simp [xiHeatTilt]
  set ℓ₁ := (xiHeatFrequency qm).re with hℓ₁
  have hmin : ∀ q, ℓ₁ ≤ (xiHeatFrequency q).re := fun q => by
    have := hqm q; rwa [htilt0, htilt0] at this
  -- an off-line copy with `Im w > 0`
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at hRH
  push Not at hRH
  obtain ⟨q₀', hq₀'⟩ := hRH
  have hw₀' := (xiHeatFrequency_im_ne_zero_iff q₀').2 hq₀'
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : XiZeroCopy, 0 < (xiHeatFrequency q₀).im := by
    rcases lt_or_gt_of_ne hw₀' with h | h
    · refine ⟨xiZeroCopyLineConjEquiv q₀', ?_⟩
      rw [xiHeatFrequency_lineConj, Complex.conj_im]; linarith
    · exact ⟨q₀', h⟩
  by_cases hA : ∃ q, (xiHeatFrequency q).re = ℓ₁ ∧ (xiHeatFrequency q).im ≠ 0
  · -- the conjugate pair at the minimal real part
    obtain ⟨q, hqre, hqim⟩ := hA
    refine ⟨0, ℓ₁, le_rfl, fun q' => by rw [htilt0]; exact hmin q', q,
      xiZeroCopyLineConjEquiv q, by rw [htilt0, hqre], ?_, ?_⟩
    · rw [htilt0, xiHeatFrequency_lineConj, Complex.conj_re, hqre]
    · rw [xiHeatFrequency_lineConj]
      intro h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      exact hqim (by linarith)
  · -- the real minimum and the steepest off-line frequency
    push Not at hA
    have hqmim : (xiHeatFrequency qm).im = 0 := hA qm rfl
    set ρ : XiZeroCopy → ℝ := fun q => ((xiHeatFrequency q).re - ℓ₁) / (xiHeatFrequency q).im
      with hρ
    have hρ₀ : 0 < ρ q₀ := by
      have h1 : ℓ₁ < (xiHeatFrequency q₀).re := by
        rcases (hmin q₀).eq_or_lt with h | h
        · exact absurd (hA q₀ h.symm) hq₀.ne'
        · exact h
      exact div_pos (by linarith) hq₀
    have hSfin : {q : XiZeroCopy | 0 < (xiHeatFrequency q).im ∧ ρ q ≤ ρ q₀}.Finite := by
      refine (finite_xiHeatTilt_le (C := ℓ₁) hρ₀.le).subset fun q hq => ?_
      obtain ⟨him, hle⟩ := hq
      show xiHeatTilt (ρ q₀) q ≤ ℓ₁
      rw [xiHeatTilt]
      have : ((xiHeatFrequency q).re - ℓ₁) / (xiHeatFrequency q).im ≤ ρ q₀ := hle
      rw [div_le_iff₀ him] at this
      linarith
    obtain ⟨qs, hqs, hqsmin⟩ := hSfin.toFinset.exists_min_image ρ
      ⟨q₀, hSfin.mem_toFinset.2 ⟨hq₀, le_rfl⟩⟩
    obtain ⟨hqsim, -⟩ := hSfin.mem_toFinset.1 hqs
    set β := ρ qs with hβ
    have hβpos : 0 < β := by
      rw [hβ]
      have h1 : ℓ₁ < (xiHeatFrequency qs).re := by
        rcases (hmin qs).eq_or_lt with h | h
        · exact absurd (hA qs h.symm) hqsim.ne'
        · exact h
      exact div_pos (by linarith) hqsim
    refine ⟨β, ℓ₁, hβpos.le, fun q => ?_, qm, qs, ?_, ?_, ?_⟩
    · rw [xiHeatTilt]
      rcases le_or_gt (xiHeatFrequency q).im 0 with him | him
      · nlinarith [hmin q]
      · have hρq : β ≤ ρ q := by
          by_cases hq : ρ q ≤ ρ q₀
          · exact hqsmin q (hSfin.mem_toFinset.2 ⟨him, hq⟩)
          · push Not at hq
            exact (hqsmin q₀ (hSfin.mem_toFinset.2 ⟨hq₀, le_rfl⟩)).trans hq.le
        have : β ≤ ((xiHeatFrequency q).re - ℓ₁) / (xiHeatFrequency q).im := hρq
        rw [le_div_iff₀ him] at this
        linarith
    · rw [xiHeatTilt, hqmim, mul_zero, sub_zero]
    · rw [xiHeatTilt, hβ]
      simp only [hρ]
      field_simp
      ring
    · intro h
      have := congrArg Complex.im h
      rw [hqmim] at this
      linarith

/-! ## Under RH the first term dominates -/

theorem exists_zeroFree_halfPlane_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ a₀ : ℝ, ∀ τ : ℂ, a₀ < τ.re → xiGaussianHeatTraceC τ ≠ 0 := by
  classical
  have him : ∀ q, (xiHeatFrequency q).im = 0 := fun q => by
    rw [xiHeatFrequency_im, (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q]
    ring
  have htilt0 : ∀ q, xiHeatTilt 0 q = (xiHeatFrequency q).re := fun q => by simp [xiHeatTilt]
  obtain ⟨qm, hqm⟩ := exists_isMinOn_xiHeatTilt (β := 0) le_rfl
  set ℓ₁ := (xiHeatFrequency qm).re with hℓ₁
  have hmin : ∀ q, ℓ₁ ≤ (xiHeatFrequency q).re := fun q => by
    have := hqm q; rwa [htilt0, htilt0] at this
  have hDfin : {q : XiZeroCopy | xiHeatTilt 0 q = ℓ₁}.Finite :=
    (finite_xiHeatTilt_le (C := ℓ₁) le_rfl).subset fun q hq => le_of_eq hq
  set D := hDfin.toFinset with hDdef
  have hD : ∀ q, q ∈ D ↔ xiHeatTilt 0 q = ℓ₁ := fun q => hDfin.mem_toFinset
  have hqmD : qm ∈ D := (hD qm).2 (htilt0 qm)
  -- the tail tends to zero
  set h : ℝ → ℝ := fun x => ∑' q : XiZeroCopy,
    (if q ∈ D then 0 else Real.exp (-(x * ((xiHeatFrequency q).re - ℓ₁)))) with hh
  have hsum₂ := summable_exp_neg_xiHeatTilt (β := 0) (ℓ := ℓ₁) (R := 0) le_rfl le_rfl
    (x := 2) (by norm_num)
  have hterm0 : ∀ x : ℝ, ∀ q, 0 ≤ (if q ∈ D then 0 else Real.exp (-(x * ((xiHeatFrequency q).re - ℓ₁)))) :=
    fun x q => by split_ifs <;> [exact le_rfl; exact (Real.exp_pos _).le]
  have hle2 : ∀ x : ℝ, 2 ≤ x → ∀ q, (if q ∈ D then 0 else Real.exp (-(x * ((xiHeatFrequency q).re - ℓ₁)))) ≤
      Real.exp (-(2 * (xiHeatTilt 0 q - ℓ₁)) + 0 * ‖xiHeatFrequency q‖) := by
    intro x hx q
    split_ifs
    · exact (Real.exp_pos _).le
    · rw [htilt0, zero_mul, add_zero]
      refine Real.exp_le_exp.2 ?_
      have := hmin q
      nlinarith
  have hT : Tendsto h atTop (𝓝 0) := by
    have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
      (f := fun x q => if q ∈ D then 0 else Real.exp (-(x * ((xiHeatFrequency q).re - ℓ₁))))
      (g := fun _ => (0 : ℝ)) hsum₂ (fun q => ?_) ?_
    · simpa using hlim
    · by_cases hq : q ∈ D
      · simp only [if_pos hq]; exact tendsto_const_nhds
      · simp only [if_neg hq]
        have hpos : 0 < (xiHeatFrequency q).re - ℓ₁ := by
          rcases (sub_nonneg.2 (hmin q)).eq_or_lt with h0 | h0
          · exact absurd ((hD q).2 (by rw [htilt0]; linarith)) hq
          · exact h0
        exact Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hpos))
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx q
      rw [Real.norm_of_nonneg (hterm0 x q)]
      exact hle2 x hx q
  obtain ⟨a₀, ha₀⟩ := (eventually_atTop.1 ((hT.eventually (gt_mem_nhds one_pos)).and
    (eventually_ge_atTop (2 : ℝ))))
  refine ⟨a₀, fun τ hτ => ?_⟩
  obtain ⟨hh1, hx2⟩ := ha₀ τ.re hτ.le
  have hτ0 : 0 < τ.re := by linarith
  have hs := summable_norm_xiGaussianHeatTermC hτ0
  have hsplit := hs.of_norm.sum_add_tsum_compl (s := D)
  -- the leading block
  have hlead : ∑ q ∈ D, xiGaussianHeatTermC τ q = (D.card : ℂ) * Complex.exp (-τ * ℓ₁) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hwq : xiHeatFrequency q = (ℓ₁ : ℂ) := by
      apply Complex.ext
      · rw [ofReal_re]; have := (hD q).1 hq; rwa [htilt0] at this
      · rw [ofReal_im, him q]
    rw [xiGaussianHeatTermC_eq_exp, hwq, Nat.cast_one, one_mul]
  -- the tail is smaller
  have htail : ‖∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, xiGaussianHeatTermC τ q‖ <
      ‖Complex.exp (-τ * ℓ₁)‖ := by
    have hnorm : ∀ q : XiZeroCopy, ‖xiGaussianHeatTermC τ q‖ =
        ‖Complex.exp (-τ * ℓ₁)‖ * Real.exp (-(τ.re * ((xiHeatFrequency q).re - ℓ₁))) := by
      intro q
      rw [norm_xiGaussianHeatTermC, Complex.norm_exp, ← Real.exp_add]
      congr 1
      have h1 : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := him q
      have h2 : (xiSpectralPoint q ^ (2 : ℕ)).re = (xiHeatFrequency q).re := rfl
      rw [h1, h2, neg_mul, neg_re, Complex.mul_re, ofReal_re, ofReal_im]
      ring
    calc ‖∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, xiGaussianHeatTermC τ q‖
        ≤ ∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, ‖xiGaussianHeatTermC τ q‖ :=
          norm_tsum_le_tsum_norm (hs.subtype _)
      _ = ∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, ‖Complex.exp (-τ * ℓ₁)‖ *
            (if (q : XiZeroCopy) ∈ D then 0 else
              Real.exp (-(τ.re * ((xiHeatFrequency q).re - ℓ₁)))) := by
          refine tsum_congr fun q => ?_
          have hq : (q : XiZeroCopy) ∉ D := q.2
          rw [if_neg hq, hnorm]
      _ ≤ ∑' q : XiZeroCopy, ‖Complex.exp (-τ * ℓ₁)‖ *
            (if q ∈ D then 0 else Real.exp (-(τ.re * ((xiHeatFrequency q).re - ℓ₁)))) := by
          refine Summable.tsum_subtype_le _ _ (fun q => mul_nonneg (norm_nonneg _) (hterm0 _ q))
            ?_
          refine Summable.mul_left _ ?_
          exact hsum₂.of_nonneg_of_le (hterm0 _) (hle2 _ hx2)
      _ = ‖Complex.exp (-τ * ℓ₁)‖ * h τ.re := by rw [tsum_mul_left]
      _ < ‖Complex.exp (-τ * ℓ₁)‖ * 1 := mul_lt_mul_of_pos_left hh1 (norm_pos_iff.2 (Complex.exp_ne_zero _))
      _ = ‖Complex.exp (-τ * ℓ₁)‖ := mul_one _
  intro h0
  rw [xiGaussianHeatTraceC, ← hsplit, hlead] at h0
  have hcard : (1 : ℝ) ≤ D.card := by exact_mod_cast Finset.card_pos.2 ⟨qm, hqmD⟩
  have h1 : ‖(D.card : ℂ) * Complex.exp (-τ * ℓ₁)‖ =
      ‖∑' q : ↑(↑D : Set XiZeroCopy)ᶜ, xiGaussianHeatTermC τ q‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  rw [norm_mul, Complex.norm_natCast] at h1
  have h2 : ‖Complex.exp (-τ * ℓ₁)‖ ≤ (D.card : ℝ) * ‖Complex.exp (-τ * ℓ₁)‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hcard
  linarith

/-! ## The criteria -/

/-- **RH as a zero-free right half-plane of the zero heat trace.** -/
theorem riemannHypothesis_iff_xiGaussianHeatTraceC_zeroFree_halfPlane :
    RiemannHypothesis ↔ ∃ a₀ : ℝ, ∀ τ : ℂ, a₀ < τ.re → xiGaussianHeatTraceC τ ≠ 0 := by
  refine ⟨exists_zeroFree_halfPlane_of_riemannHypothesis, fun ⟨a₀, ha₀⟩ => ?_⟩
  by_contra hRH
  obtain ⟨β, ℓ, hβ, hκ, q₁, q₂, h₁, h₂, hne⟩ := exists_balance_of_not_riemannHypothesis hRH
  obtain ⟨τ, hτ, h0⟩ := exists_zero_xiGaussianHeatTraceC_of_balance hβ hκ h₁ h₂ hne a₀
  exact ha₀ τ hτ h0

/-- **Prime form.**  RH holds iff the equation `(π/τ)^{1/2} S(τ) = Arch(τ) + 2π e^{τ/4}` has no
solution in some right half-plane. -/
theorem riemannHypothesis_iff_primeChirp_ne_arch_add_pole_halfPlane :
    RiemannHypothesis ↔ ∃ a₀ : ℝ, ∀ τ : ℂ, a₀ < τ.re →
      gaussianPrimeChirpC τ ≠ gaussianArchCriticalC τ + gaussianArchPoleC τ := by
  rw [riemannHypothesis_iff_xiGaussianHeatTraceC_zeroFree_halfPlane]
  have hiff : ∀ τ : ℂ, 0 < τ.re → (xiGaussianHeatTraceC τ ≠ 0 ↔
      gaussianPrimeChirpC τ ≠ gaussianArchCriticalC τ + gaussianArchPoleC τ) := by
    intro τ hτ
    have h := pi_mul_xiGaussianHeatTraceC_eq_arch_add_pole_sub_prime hτ
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    constructor
    · intro hν hp
      apply hν
      have : (Real.pi : ℂ) * xiGaussianHeatTraceC τ = 0 := by rw [h, hp]; ring
      exact (mul_eq_zero.1 this).resolve_left hπ
    · intro hp hν
      apply hp
      rw [hν, mul_zero] at h
      linear_combination h
  constructor
  · rintro ⟨a₀, ha₀⟩
    exact ⟨max a₀ 0, fun τ hτ => (hiff τ ((le_max_right _ _).trans_lt hτ)).1
      (ha₀ τ ((le_max_left _ _).trans_lt hτ))⟩
  · rintro ⟨a₀, ha₀⟩
    exact ⟨max a₀ 0, fun τ hτ => (hiff τ ((le_max_right _ _).trans_lt hτ)).2
      (ha₀ τ ((le_max_left _ _).trans_lt hτ))⟩

end

end RHTower
