import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawHoldsOnEveryStripAboutTheLine
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheLogarithmicDerivativeExpandsInAZeroFreeStrip
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.DirichletSeriesAreExpansionsOnTheScalesOneOverN
import GaloisForLFunctions.InfiniteRankPurityTheory.NoExponentialPolynomialIsAFactorOfXi
import GaloisForLFunctions.HTGeometry.BoundedStripAlmostPeriodicThreeLines

/-!
# No absolutely convergent Dirichlet series is a constituent with a zero

Let `F(s) = Σ a(n) n^{−s}` converge absolutely at a real point `x`, `F ≢ 0`. The statements have
content for `x < ½`, where the half-plane of absolute convergence contains the critical line.

* **Half-plane** (`LSeries_ne_zero_of_zeros_subset_xi`): if every zero of `F` in `Re s > x` is a
  zero of `ξ`, then `F` has no zero in `Re s > x`.
* **Strip** (`LSeries_ne_zero_of_strip_zeros_subset_xi`): if every zero of `F` in a strip
  `|Re s − ½| < ω` inside the half-plane of absolute convergence is a zero of `ξ`, then `F` has no
  zero in the strip, whatever its zeros outside the strip. This covers Dirichlet polynomials that
  share with `ξ` only their zeros near the line.

So the zero set of `ξ` contains the zero set, in a strip about the line, of no absolutely
convergent Dirichlet series that has a zero there.

The core (`expansion_ne_zero_of_zeros_cancelled`) is stated for expansions over positive real
scales. A zero in the strip off the line recurs with positive density and is excluded by the
density of the zeros of `ζ` (`re_eq_half_of_strip_zeros_subset_xi`). With the zeros on the line,
`F'/F` has absolutely convergent expansions over the scales on the two sides of the
line (Wiener's lemma on a strip); `−ζ F'/(sF)` is holomorphic on the strip and bounded near the
line (maximum principle between heights at which `F` is bounded below); by the jump law the two
expansions coincide and continue across the line. So `F'/F` has no pole on the line.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

theorem stripWeight_self (σ : ℝ) (q : Scale) : stripWeight σ σ q = q.toReal ^ σ := max_self _

/-! ### Heights at which an almost periodic function is bounded below -/

/-- **A lower bound on a horizontal segment recurs.** If `F` is continuous and almost periodic on
the closed strip `|Re z − σ| ≤ R` and does not vanish on its segment at one height, then
`‖F‖ ≥ μ > 0` on the segments at heights met in every interval of a fixed length. -/
theorem exists_good_heights {F : ℂ → ℂ} {σ R T₀ : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn F {z : ℂ | |z.re - σ| ≤ R}) (hAP : IsStripAlmostPeriodicOn F σ R)
    (hseg : ∀ x : ℝ, |x - σ| ≤ R → F ((x : ℂ) + (T₀ : ℂ) * I) ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ L : ℝ, ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, |z.re - σ| ≤ R →
      z.im = T → μ ≤ ‖F z‖ := by
  have hmem : ∀ x : ℝ, |x - σ| ≤ R ↔ x ∈ Icc (σ - R) (σ + R) := fun x => by
    rw [abs_le, mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hmaps : MapsTo (fun x : ℝ => (x : ℂ) + (T₀ : ℂ) * I) (Icc (σ - R) (σ + R))
      {z : ℂ | |z.re - σ| ≤ R} := fun x hx => by
    show |((x : ℂ) + (T₀ : ℂ) * I).re - σ| ≤ R
    have hre : ((x : ℂ) + (T₀ : ℂ) * I).re = x := by simp
    rw [hre]
    exact (hmem x).mpr hx
  have hcont : ContinuousOn (fun x : ℝ => ‖F ((x : ℂ) + (T₀ : ℂ) * I)‖) (Icc (σ - R) (σ + R)) :=
    (hF.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (T₀ : ℂ) * I).continuousOn
      hmaps).norm
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : σ - R ≤ σ + R)) hcont
  have hm₀pos : 0 < ‖F ((x₀ : ℂ) + (T₀ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (hseg x₀ ((hmem x₀).mpr hx₀))
  obtain ⟨L, -, hτ⟩ := hAP (‖F ((x₀ : ℂ) + (T₀ : ℂ) * I)‖ / 2) (by positivity)
  refine ⟨_, half_pos hm₀pos, L, fun y => ?_⟩
  obtain ⟨τ, hτmem, hτD⟩ := hτ (y - T₀)
  refine ⟨T₀ + τ, ⟨by linarith [hτmem.1], by linarith [hτmem.2]⟩, fun z hz hzT => ?_⟩
  have hzform : z = ((z.re : ℝ) : ℂ) + (T₀ : ℂ) * I + (τ : ℂ) * I := by
    apply Complex.ext <;> simp [hzT]
  have h1 := hτD (((z.re : ℝ) : ℂ) + (T₀ : ℂ) * I) (by simpa using hz)
  have h2 := isMinOn_iff.mp hmin z.re ((hmem z.re).mp hz)
  have h3 := norm_sub_norm_le (F (((z.re : ℝ) : ℂ) + (T₀ : ℂ) * I))
    (F (((z.re : ℝ) : ℂ) + (T₀ : ℂ) * I + (τ : ℂ) * I))
  rw [norm_sub_rev] at h3
  rw [hzform]
  linarith

/-- Near the line `‖ζ(s)/s‖ ≤ 8`. -/
theorem norm_riemannZeta_div_le_eight {z : ℂ} (h0 : 3 / 8 ≤ z.re) (h1 : z.re ≤ 5 / 8) :
    ‖riemannZeta z / z‖ ≤ 8 := by
  have h := norm_riemannZeta_div_le (z := z) (by linarith) (by linarith)
  have e1 : 1 / (1 - z.re) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have e2 : 1 / z.re ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-! ### The core: zeros on the line cannot all be cancelled by `ζ` -/

/-- **The zeros of `ζ` cancel no zero of an absolutely convergent expansion.** Let
`F(s) = Σ c(q) q^s` converge absolutely on the closed strip `|Re s − ½| ≤ 2η`, be almost periodic
near the line and have its zeros in the open strip on the critical line. If `ζ` vanishes at every
zero of `F` on the line, then `F` has no zero in the strip. -/
theorem expansion_ne_zero_of_zeros_cancelled {c : Scale → ℂ} {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 4) (hc : WSummable (1 / 2 - 2 * η) (1 / 2 + 2 * η) c)
    (hAP : IsStripAlmostPeriodicOn (expansion c) (1 / 2) (η / 2))
    (hoff : ∀ s : ℂ, |s.re - 1 / 2| < 2 * η → s.re ≠ 1 / 2 → expansion c s ≠ 0)
    (hline : ∀ s : ℂ, s.re = 1 / 2 → expansion c s = 0 → riemannZeta s = 0)
    (hne : c ≠ 0) {s : ℂ} (hs : |s.re - 1 / 2| < 2 * η) : expansion c s ≠ 0 := by
  by_cases hsre : s.re = 1 / 2
  swap
  · exact hoff s hs hsre
  intro hs0
  have hV : ∀ z : ℂ, 1 / 2 - 2 * η < z.re → z.re < 1 / 2 + 2 * η → |z.re - 1 / 2| < 2 * η :=
    fun z h1 h2 => abs_lt.mpr ⟨by linarith, by linarith⟩
  have hFd : DifferentiableOn ℂ (expansion c)
      {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := differentiableOn_expansion hc
  -- the logarithmic derivative on the two sides of the line
  obtain ⟨gL, hgL, hGL⟩ := exists_logDeriv_expansion (τ₁ := 1 / 2 - 2 * η) (τ₂ := 1 / 2)
    (by linarith) (hc.mono le_rfl (by linarith) (by linarith))
    (fun z h1 h2 => hoff z (hV z h1 (by linarith)) (ne_of_lt h2))
  obtain ⟨gR, hgR, hGR⟩ := exists_logDeriv_expansion (τ₁ := 1 / 2) (τ₂ := 1 / 2 + 2 * η)
    (by linarith) (hc.mono (by linarith) (by linarith) le_rfl)
    (fun z h1 h2 => hoff z (hV z (by linarith) h2) (ne_of_gt h1))
  have hsumR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η →
      Summable fun q : Scale => ‖gR q‖ * q.toReal ^ σ := fun σ h1 h2 => by
    refine (hgR σ σ h1 le_rfl (by linarith)).congr fun q => ?_
    rw [stripWeight_self]
  have hsumL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 →
      Summable fun q : Scale => ‖gL q‖ * q.toReal ^ σ := fun σ h1 h2 => by
    refine (hgL σ σ (by linarith) le_rfl h2).congr fun q => ?_
    rw [stripWeight_self]
  -- the quotient `−ζ F'/(sF)` on the strip of half-width `η`
  set U : Set ℂ := {z : ℂ | 1 / 2 - η < z.re ∧ z.re < 1 / 2 + η} with hU
  have hUo : IsOpen U := isOpen_openStrip _ _
  have hUV : ∀ z ∈ U, z ∈ {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hfd : DifferentiableOn ℂ (expansion c) U := hFd.mono hUV
  have hgd : DifferentiableOn ℂ (fun z : ℂ => -(riemannZeta z / z)) U := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => by
      have := hz.2
      rw [h, one_re] at this
      linarith
    have hz0 : z ≠ 0 := fun h => by
      have := hz.1
      rw [h, zero_re] at this
      linarith
    exact ((differentiableAt_riemannZeta hz1).div differentiableAt_id hz0).neg.differentiableWithinAt
  -- a real point right of the line, where `F` and `ζ` do not vanish
  set s₀ : ℂ := ((1 / 2 + η / 2 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = 1 / 2 + η / 2 := by rw [hs₀, ofReal_re]
  have hs₀U : s₀ ∈ U := ⟨by rw [hs₀re]; linarith, by rw [hs₀re]; linarith⟩
  have hp : expansion c s₀ ≠ 0 :=
    hoff s₀ (by rw [hs₀re, abs_lt]; constructor <;> linarith) (by rw [hs₀re]; linarith)
  have hFan : AnalyticOnNhd ℂ (expansion c)
      {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} :=
    hFd.analyticOnNhd (isOpen_openStrip _ _)
  have hfin : ∀ z ∈ U, analyticOrderAt (expansion c) z ≠ ⊤ := by
    intro z hz htop
    have hall := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip _ _) (hUV z hz) (analyticOrderAt_eq_top.mp htop)
    exact hp (hall (hUV s₀ hs₀U))
  have hzero : ∀ z ∈ U, expansion c z = 0 → -(riemannZeta z / z) = 0 := by
    intro z hz hz0
    have hre : z.re = 1 / 2 := by
      by_contra hne'
      exact hoff z (hV z (hUV z hz).1 (hUV z hz).2) hne' hz0
    rw [hline z hre hz0, zero_div, neg_zero]
  obtain ⟨Φ, hΦd, hΦ⟩ := exists_differentiableOn_deriv_mul_div hUo hfd hgd hfin hzero
  have hΦR : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 / 2 + η →
      Φ z = -(riemannZeta z / z) * ∑' q : Scale, gR q * (q.toReal : ℂ) ^ z := by
    intro z h1 h2
    have hz0 : expansion c z ≠ 0 := hoff z (hV z (by linarith) (by linarith)) (ne_of_gt h1)
    have hG : deriv (expansion c) z / expansion c z = ∑' q : Scale, gR q * (q.toReal : ℂ) ^ z :=
      hGR z h1 (by linarith)
    rw [hΦ z ⟨by linarith, h2⟩ hz0, ← hG]
    ring
  have hΦL : ∀ z : ℂ, 1 / 2 - η < z.re → z.re < 1 / 2 →
      Φ z = -(riemannZeta z / z) * ∑' q : Scale, gL q * (q.toReal : ℂ) ^ z := by
    intro z h1 h2
    have hz0 : expansion c z ≠ 0 := hoff z (hV z (by linarith) (by linarith)) (ne_of_lt h2)
    have hG : deriv (expansion c) z / expansion c z = ∑' q : Scale, gL q * (q.toReal : ℂ) ^ z :=
      hGL z (by linarith) h2
    rw [hΦ z ⟨h1, by linarith⟩ hz0, ← hG]
    ring
  -- bounds on the two boundary lines and at good heights
  have hx : (1 / 2 - η / 2 : ℝ) < 1 / 2 + η / 2 := by linarith
  have hWR : WSummable (1 / 2 + η / 2) (1 / 2 + η / 2) gR :=
    hgR _ _ (by linarith) le_rfl (by linarith)
  have hWL : WSummable (1 / 2 - η / 2) (1 / 2 - η / 2) gL :=
    hgL _ _ (by linarith) le_rfl (by linarith)
  have hWD : WSummable (1 / 2 - η / 2) (1 / 2 + η / 2) fun q => c q * ((q.log : ℝ) : ℂ) :=
    hc.log_mul (by linarith) hx.le (by linarith)
  have hζ : ∀ z : ℂ, 1 / 2 - η / 2 ≤ z.re → z.re ≤ 1 / 2 + η / 2 →
      ‖-(riemannZeta z / z)‖ ≤ 8 := fun z h1 h2 => by
    rw [norm_neg]
    exact norm_riemannZeta_div_le_eight (by linarith) (by linarith)
  have hcontF : ContinuousOn (expansion c) {z : ℂ | |z.re - 1 / 2| ≤ η / 2} :=
    hFd.continuousOn.mono fun z hz => by
      have h := abs_le.mp (show |z.re - 1 / 2| ≤ η / 2 from hz)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, expansion c (((1 / 2 : ℝ) : ℂ) + (T₀ : ℂ) * I) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith) le_rfl (by linarith)) fun z h1 h2 => ?_)
    have hre : z.re = 1 / 2 := le_antisymm h2 h1
    have hz : z = ((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    rw [hz]
    exact hcon z.im
  have hseg : ∀ x : ℝ, |x - 1 / 2| ≤ η / 2 → expansion c ((x : ℂ) + (T₀ : ℂ) * I) ≠ 0 := by
    intro x hx'
    have hre : ((x : ℂ) + (T₀ : ℂ) * I).re = x := by simp
    by_cases hx2 : x = 1 / 2
    · rw [hx2]
      exact hT₀
    · exact hoff _ (by rw [hre]; exact lt_of_le_of_lt hx' (by linarith)) (by rw [hre]; exact hx2)
  obtain ⟨μ, hμ, L, hgoodF⟩ := exists_good_heights (by positivity) hcontF hAP hseg
  set NR : ℝ := ∑' q, ‖gR q‖ * stripWeight (1 / 2 + η / 2) (1 / 2 + η / 2) q with hNR
  set NL : ℝ := ∑' q, ‖gL q‖ * stripWeight (1 / 2 - η / 2) (1 / 2 - η / 2) q with hNL
  set MD : ℝ := ∑' q, ‖c q * ((q.log : ℝ) : ℂ)‖ *
    stripWeight (1 / 2 - η / 2) (1 / 2 + η / 2) q with hMD
  have hNR0 : 0 ≤ NR := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hNL0 : 0 ≤ NL := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hMD0 : 0 ≤ MD := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hquot0 : 0 ≤ MD * 8 / μ := by positivity
  have hlineB : ∀ z : ℂ, z.re = 1 / 2 - η / 2 ∨ z.re = 1 / 2 + η / 2 →
      ‖Φ z‖ ≤ 8 * NR + 8 * NL + MD * 8 / μ := by
    rintro z (hz | hz)
    · rw [hΦL z (by rw [hz]; linarith) (by rw [hz]; linarith), norm_mul]
      have h1 := hζ z (by rw [hz]) (by rw [hz]; linarith)
      have h2 : ‖∑' q : Scale, gL q * (q.toReal : ℂ) ^ z‖ ≤ NL :=
        hWL.norm_expansion_le (le_of_eq hz.symm) (le_of_eq hz)
      have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
      linarith
    · rw [hΦR z (by rw [hz]; linarith) (by rw [hz]; linarith), norm_mul]
      have h1 := hζ z (by rw [hz]; linarith) (by rw [hz])
      have h2 : ‖∑' q : Scale, gR q * (q.toReal : ℂ) ^ z‖ ≤ NR :=
        hWR.norm_expansion_le (le_of_eq hz.symm) (le_of_eq hz)
      have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
      linarith
  have hgoodB : ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, 1 / 2 - η / 2 ≤ z.re →
      z.re ≤ 1 / 2 + η / 2 → z.im = T → ‖Φ z‖ ≤ 8 * NR + 8 * NL + MD * 8 / μ := by
    intro y
    obtain ⟨T, hT, hTF⟩ := hgoodF y
    refine ⟨T, hT, fun z h1 h2 hzT => ?_⟩
    have hμz := hTF z (abs_le.mpr ⟨by linarith, by linarith⟩) hzT
    have hz0 : expansion c z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hμ hμz)
    have hder : ‖deriv (expansion c) z‖ ≤ MD := by
      rw [deriv_expansion hc (by linarith) (by linarith)]
      exact hWD.norm_expansion_le h1 h2
    rw [hΦ z ⟨by linarith, by linarith⟩ hz0, norm_div, norm_mul]
    have h8 := hζ z h1 h2
    have e1 : ‖deriv (expansion c) z‖ * ‖-(riemannZeta z / z)‖ / ‖expansion c z‖ ≤
        MD * 8 / ‖expansion c z‖ :=
      div_le_div_of_nonneg_right (mul_le_mul hder h8 (norm_nonneg _) hMD0) (norm_nonneg _)
    have e2 : MD * 8 / ‖expansion c z‖ ≤ MD * 8 / μ :=
      div_le_div_of_nonneg_left (by positivity) hμ hμz
    linarith
  have hΦb : ∀ w : ℂ, 1 / 2 - η / 2 ≤ w.re → w.re ≤ 1 / 2 + η / 2 →
      ‖Φ w‖ ≤ 8 * NR + 8 * NL + MD * 8 / μ := fun w h1 h2 =>
    norm_le_of_good_heights hx (fun z h1 h2 => (⟨by linarith, by linarith⟩ : z ∈ U)) hΦd hlineB
      hgoodB h1 h2
  -- the jump law: the two expansions coincide and continue across the line
  obtain ⟨-, hsumAll, hΦall⟩ := eq_riemannZeta_div_mul_tsum_of_strip (b := gR) (c := gL)
    (a := Scale.toReal) Scale.toReal_pos Scale.toReal_injective hη0 (by linarith) hsumR hsumL
    hΦd hΦb hΦR hΦL
  have hWg : WSummable (1 / 2 - η) (1 / 2 + η) gR := by
    refine Summable.of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le) (fun q => ?_)
      ((hsumAll (1 / 2 - η) le_rfl (by linarith)).add (hsumAll (1 / 2 + η) (by linarith) le_rfl))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (Real.rpow_nonneg q.toReal_pos.le _)
      (Real.rpow_nonneg q.toReal_pos.le _)) (norm_nonneg _)
  have hHd : DifferentiableOn ℂ (expansion gR) U := differentiableOn_expansion hWg
  -- `F' = H F` on the strip
  have hs₀1 : s₀ ≠ 1 := fun h => by
    have := hs₀re
    rw [h, one_re] at this
    linarith
  have hζ0 : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_ofReal_mem_Ioo (by linarith) (by linarith)
  have hev : (fun z => deriv (expansion c) z - expansion gR z * expansion c z) =ᶠ[𝓝 s₀] 0 := by
    have h1 : ∀ᶠ z in 𝓝 s₀, riemannZeta z ≠ 0 :=
      (differentiableAt_riemannZeta hs₀1).continuousAt.eventually_ne hζ0
    have h2 : ∀ᶠ z in 𝓝 s₀, expansion c z ≠ 0 :=
      (hfd.continuousOn.continuousAt (hUo.mem_nhds hs₀U)).eventually_ne hp
    filter_upwards [h1, h2, hUo.mem_nhds hs₀U] with z hz1 hz2 hz3
    have hzne : z ≠ 0 := fun h => by
      have := hz3.1
      rw [h, zero_re] at this
      linarith
    have hg0 : -(riemannZeta z / z) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hz1 hzne)
    have e2 : Φ z = -(riemannZeta z / z) * expansion gR z := hΦall z hz3.1 hz3.2
    rw [hΦ z hz3 hz2] at e2
    have e3 := (div_eq_iff hz2).mp e2
    have e4 : -(riemannZeta z / z) *
        (deriv (expansion c) z - expansion gR z * expansion c z) = 0 := by
      linear_combination e3
    exact (mul_eq_zero.mp e4).resolve_left hg0
  have hPd : DifferentiableOn ℂ
      (fun z => deriv (expansion c) z - expansion gR z * expansion c z) U :=
    (hfd.deriv hUo).sub (hHd.mul hfd)
  have hPzero := (hPd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_openStrip _ _) hs₀U hev
  -- at a zero on the line the orders of `F'` and `H F` differ
  have hsU : s ∈ U := ⟨by rw [hsre]; linarith, by rw [hsre]; linarith⟩
  have hFs : AnalyticAt ℂ (expansion c) s := hfd.analyticAt (hUo.mem_nhds hsU)
  have hHs : AnalyticAt ℂ (expansion gR) s := hHd.analyticAt (hUo.mem_nhds hsU)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin s hsU)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (hFs.analyticOrderAt_ne_zero.mpr hs0) (by rw [← hm]; rfl)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hford : analyticOrderAt (expansion c) s = ((k + 1 : ℕ) : ℕ∞) := hm.symm
  have hdord : analyticOrderAt (deriv (expansion c)) s = (k : ℕ∞) :=
    analyticOrderAt_deriv_of_pos hFs (by rw [hford]; push_cast; rfl)
  have heq : deriv (expansion c) =ᶠ[𝓝 s] expansion gR * expansion c := by
    filter_upwards [hUo.mem_nhds hsU] with z hz
    have h : deriv (expansion c) z - expansion gR z * expansion c z = 0 := hPzero hz
    exact sub_eq_zero.mp h
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hHs hFs, hford] at hdord
  induction h : analyticOrderAt (expansion gR) s using ENat.recTopCoe with
  | top =>
    rw [h] at hdord
    simp at hdord
  | coe j =>
    rw [h] at hdord
    have h' : j + (k + 1) = k := by exact_mod_cast hdord
    omega

/-! ### Dirichlet series -/

section Dirichlet

variable {a : ℕ → ℂ} {x : ℝ}

theorem differentiableOn_LSeries_of_summable (hsum : LSeriesSummable a x) :
    DifferentiableOn ℂ (LSeries a) {z : ℂ | x < z.re} :=
  (LSeries_differentiableOn a).mono fun z hz => by
    have h := hsum.abscissaOfAbsConv_le
    rw [ofReal_re] at h
    exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hz)

theorem norm_LSeries_le_of_summable (hsum : LSeriesSummable a x) {z : ℂ} (hz : x ≤ z.re) :
    ‖LSeries a z‖ ≤ ∑' n, ‖LSeries.term a x n‖ := by
  have hz' : LSeriesSummable a z := hsum.of_re_le_re (by rwa [ofReal_re])
  exact (norm_tsum_le_tsum_norm hz'.norm).trans (hz'.norm.tsum_le_tsum
    (fun n => LSeries.norm_term_le_of_re_le_re a (by rwa [ofReal_re]) n) hsum.norm)

/-- A Dirichlet series with a nonzero coefficient does not vanish on a whole vertical line. -/
theorem exists_LSeries_ne_zero (hsum : LSeriesSummable a x) {n : ℕ} (hn : a (n + 1) ≠ 0) {y : ℝ}
    (hy : x ≤ y) : ∃ z : ℂ, z.re = y ∧ LSeries a z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine dirichletCoeff_ne_zero hn (eq_zero_of_expansion_eq_zero (le_refl y)
    (wsummable_dirichletCoeff hsum hy le_rfl) fun z h1 h2 => ?_)
  have hre : z.re = y := le_antisymm h2 h1
  rw [expansion_dirichletCoeff hsum (by rw [hre]; exact hy)]
  exact hcon z hre

/-- Right of its abscissa of absolute convergence a Dirichlet series is almost periodic on closed
strips. -/
theorem isStripAlmostPeriodicOn_expansion_dirichletCoeff (hsum : LSeriesSummable a x) {σ R : ℝ}
    (hR : 0 ≤ R) (hx : x < σ - R) :
    IsStripAlmostPeriodicOn (expansion (dirichletCoeff a)) σ R := by
  have h := isStripAlmostPeriodicOn_of_bounded_LSeries (F := LSeries a) (l' := σ - R)
    (u := σ + R) hx (by linarith) (by linarith) hsum (differentiableOn_LSeries_of_summable hsum)
    (fun z hz => norm_LSeries_le_of_summable hsum hz.le) fun z _ => rfl
  rw [show (σ - R + (σ + R)) / 2 = σ by ring, show (σ + R - (σ - R)) / 2 = R by ring] at h
  intro ε hε
  obtain ⟨L, hL, hτ⟩ := h ε hε
  refine ⟨L, hL, fun y => ?_⟩
  obtain ⟨τ, hτm, hτz⟩ := hτ y
  refine ⟨τ, hτm, fun z hz => ?_⟩
  have hzre : x ≤ z.re := by linarith [(abs_le.mp hz).1]
  have hre : (z + (τ : ℂ) * I).re = z.re := by simp
  rw [expansion_dirichletCoeff hsum (by rw [hre]; exact hzre), expansion_dirichletCoeff hsum hzre]
  exact hτz z hz

/-- **A constituent in a strip is pure.** If every zero of an absolutely convergent Dirichlet
series in a strip about the critical line is a zero of `ξ`, they all lie on the line: a zero off
the line recurs inside the strip with positive density, and the zeros of `ζ` near its vertical
line have density zero. -/
theorem re_eq_half_of_strip_zeros_subset_xi (hsum : LSeriesSummable a x) {ω : ℝ}
    (hx : x < 1 / 2 - ω) {n : ℕ} (hn : a (n + 1) ≠ 0)
    (hzero : ∀ s : ℂ, |s.re - 1 / 2| < ω → LSeries a s = 0 → xi s = 0) {ρ₀ : ℂ}
    (hρ : |ρ₀.re - 1 / 2| < ω) (hρ0 : LSeries a ρ₀ = 0) : ρ₀.re = 1 / 2 := by
  by_contra hne
  have hxi := hzero ρ₀ hρ hρ0
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero (re_pos_of_xi_eq_zero hxi)
    (re_lt_one_of_xi_eq_zero hxi) hne
  obtain ⟨z₁, hz₁re, hz₁⟩ := exists_LSeries_ne_zero hsum hn (y := x + 1) (by linarith)
  have hρx : x < ρ₀.re := by linarith [(abs_lt.mp hρ).1]
  set r' : ℝ := min r (ω - |ρ₀.re - 1 / 2|) with hr'
  have hr'pos : 0 < r' := lt_min hr (by linarith)
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts (F := LSeries a) hsum
    (differentiableOn_LSeries_of_summable hsum)
    (fun z hz => norm_LSeries_le_of_summable hsum hz.le) (fun z _ => rfl)
    ⟨z₁, by rw [hz₁re]; linarith, hz₁⟩ hρx hρ0 hr'pos
  have hthick' : ∀ y : ℝ, ∃ τ ∈ Icc y (y + L), Ioo (τ - d) (τ + d) ⊆ zetaZeroShiftSet ρ₀ r := by
    intro y
    obtain ⟨τ, hτ, hsub⟩ := hthick y
    refine ⟨τ, hτ, fun t ht => ?_⟩
    obtain ⟨z, hz, -, hz0⟩ := hsub ht
    have hzr : ‖z - ρ₀‖ < r' := mem_ball_iff_norm.mp hz
    have hzre := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt hzr)
    rw [sub_re] at hzre
    have hre : (z + (t : ℂ) * I).re = z.re := by simp
    have hstrip : |(z + (t : ℂ) * I).re - 1 / 2| < ω := by
      rw [hre]
      have h1 := abs_lt.mp hρ
      have h2 : r' ≤ ω - |ρ₀.re - 1 / 2| := min_le_right _ _
      rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;>
        rw [hab] at h2 <;> rw [abs_lt] <;> constructor <;> linarith [hzre.1, hzre.2]
    have hxiz := hzero _ hstrip hz0
    refine ⟨z, ball_subset_ball (min_le_left _ _) hz, ?_⟩
    exact (xi_eq_zero_iff (re_pos_of_xi_eq_zero hxiz) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, one_re] at this
      exact lt_irrefl _ this).mp hxiz
  -- positive lower density against density zero
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  have hκ0 : 0 < d / (L + 2 * d) := by positivity
  have hup := hdens (d / (L + 2 * d) / 2) (by positivity)
  obtain ⟨T, hT1, hT2, hT0⟩ := (hlow.and (hup.and (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith [mul_pos hκ0 hT0]

/-- **No absolutely convergent Dirichlet series is a constituent with a zero, in a strip.** Let
`Σ a(n) n^{−s}` converge absolutely at `x` and let the strip `|Re s − ½| < ω` lie right of `x`. If
every zero of the series in the strip is a zero of `ξ`, the series has no zero in the strip. Zeros
outside the strip are not restricted. -/
theorem LSeries_ne_zero_of_strip_zeros_subset_xi (hsum : LSeriesSummable a x) {ω : ℝ}
    (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) (hx : x < 1 / 2 - ω) {n : ℕ} (hn : a (n + 1) ≠ 0)
    (hzero : ∀ s : ℂ, |s.re - 1 / 2| < ω → LSeries a s = 0 → xi s = 0) {s : ℂ}
    (hs : |s.re - 1 / 2| < ω) : LSeries a s ≠ 0 := by
  have hexp : ∀ z : ℂ, |z.re - 1 / 2| < ω → expansion (dirichletCoeff a) z = LSeries a z :=
    fun z hz => expansion_dirichletCoeff hsum (by linarith [(abs_lt.mp hz).1])
  have hω2 : 2 * (ω / 2) = ω := by ring
  rw [← hexp s hs]
  refine expansion_ne_zero_of_zeros_cancelled (η := ω / 2) (by positivity) (by linarith)
    (wsummable_dirichletCoeff hsum (by linarith) (by linarith))
    (isStripAlmostPeriodicOn_expansion_dirichletCoeff hsum (by positivity) (by linarith))
    (fun z hz hre hz0 => ?_) (fun z hre hz0 => ?_) (dirichletCoeff_ne_zero hn) (by rwa [hω2])
  · rw [hω2] at hz
    rw [hexp z hz] at hz0
    exact hre (re_eq_half_of_strip_zeros_subset_xi hsum hx hn hzero hz hz0)
  · have hz : |z.re - 1 / 2| < ω := by rw [hre, sub_self, abs_zero]; exact hω0
    rw [hexp z hz] at hz0
    have hxiz := hzero z hz hz0
    exact (xi_eq_zero_iff (by rw [hre]; norm_num) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, one_re] at this
      exact lt_irrefl _ this).mp hxiz

/-- **No absolutely convergent Dirichlet series is a constituent with a zero.** Let
`Σ a(n) n^{−s}` converge absolutely at a real point `x` and not vanish identically. If every zero
of the series in `Re s > x` is a zero of `ξ`, the series has no zero in `Re s > x`. For `x ≥ ½`
this is purity; the content is `x < ½`, where the half-plane contains the critical line. -/
theorem LSeries_ne_zero_of_zeros_subset_xi (hsum : LSeriesSummable a x) {n : ℕ}
    (hn : a (n + 1) ≠ 0) (hzero : ∀ s : ℂ, x < s.re → LSeries a s = 0 → xi s = 0) {s : ℂ}
    (hs : x < s.re) : LSeries a s ≠ 0 := by
  intro h0
  obtain ⟨z₁, hz₁re, hz₁⟩ := exists_LSeries_ne_zero hsum hn (y := x + 1) (by linarith)
  have hre : s.re = 1 / 2 := re_eq_half_of_zeros_subset_xi (F := LSeries a) hsum
    (differentiableOn_LSeries_of_summable hsum)
    (fun z hz => norm_LSeries_le_of_summable hsum hz.le) (fun z _ => rfl)
    ⟨z₁, by rw [hz₁re]; linarith, hz₁⟩ hzero hs h0
  have hx : x < 1 / 2 := by
    rw [← hre]
    exact hs
  have hω0 : 0 < min (1 / 2 : ℝ) ((1 / 2 - x) / 2) := lt_min (by norm_num) (by linarith)
  have hω2 : min (1 / 2 : ℝ) ((1 / 2 - x) / 2) ≤ (1 / 2 - x) / 2 := min_le_right _ _
  exact LSeries_ne_zero_of_strip_zeros_subset_xi hsum hω0 (min_le_left _ _) (by linarith) hn
    (fun z hz hz0 => hzero z (by linarith [(abs_lt.mp hz).1]) hz0)
    (by rw [hre, sub_self, abs_zero]; exact hω0) h0

end Dirichlet

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
