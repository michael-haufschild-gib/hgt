import GaloisForLFunctions.SquareRootThreshold.WindowedOffDiagonalBeyondThreshold
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver

/-!
# The coupling of finitely many primes to the prime tail

At aperture `a` the localized Weil form of `ζ` at height `2πξ` is
`W_ζ(S_ξ f, S_ξ f) = A_f(ξ) − Π_f(ξ)`.
* `Π_f` is the prime polynomial over the finitely many prime powers `n ≤ e^{2a}`.
* `A_f` is the pole term plus the archimedean term.

The pole of `ζ` at `s = 1` is the contribution of the whole infinite prime tail. The archimedean
growth `μ(τ) ≈ log|τ|/2π` is the zero density, which the functional equation transports from the
prime tail.

**The coupled criterion** (`riemannHypothesis_iff_primePolynomial_le_archPart`). RH holds iff
`Re Π_f(ξ) ≤ Re A_f(ξ)` for every aperture, every `C²` profile and every height.

**The coupling is necessary** (`exists_archPart_zero_lt_primePolynomial`). Take the odd profile
`sinh(u/2)(a² − u²)₊^{5/2}`.
* The pole terms equal `−2(∫ f sinh(u/2))²` (`pole_terms_odd_eq`). This is the depth-`½` pair at
  height `0` from `IsolatedOffLinePairVisibilityLaw`, with its extremal witness.
* For large `a` this dominates the archimedean term (`integral_norm_sq_paperFT_mul_mu_le`), so
  `Re A_f(0) < 0`.
* The prime polynomial has windowed mean zero, so it is nonnegative at some height
  (`exists_lt_re_primePolynomial`).

Hence the inequality `Re Π_f(ξ) ≤ Re A_f(0)` with the archimedean–pole side frozen at height `0`
fails. If RH holds, the primes at height `0` must be negative (`re_primePolynomial_zero_neg`): the
finitely many primes `≤ e^{2a}` must cancel the pole.

**Minimal form and comparison.**
* `primePolynomial_le_archPart_iff_poleCompression`: by `RHTower.riemannHypothesis_iff_weilPoleCompression_nonneg`,
  the coupled criterion is equivalent to a `2 × 2` prime–Gamma inequality on the two pole
  directions `e^{±u/2}` at every aperture. This is the rank-two form: the depth-`½` pair sector at
  height `0` already carries the whole criterion.
* `primePolynomial_le_archPart_of_zetaStronglyRecurrent`: Bagchi's strong recurrence implies the
  coupled criterion (`RHTower.riemannHypothesis_of_zetaStronglyRecurrent`).
* Both criteria have unconditional density-zero shadows. For SRT, the heights with
  `Re W_ζ < 0` have proportion `O((log X/log T)²)` (`lintegral_bad_heights_le_of_height`). For
  recurrence, the self-return set around an off-line zero has density zero
  (`RHTower.exists_zetaSelfReturn_density_zero`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ### The coupled criterion -/

theorem heightShift_zero (f : ℝ → ℂ) : heightShift 0 f = f := by
  funext u
  simp [heightShift]

/-- **The coupled localized criterion.** RH holds iff at every aperture `a`, for every `C²`
profile supported in `[-a, a]` and every height, the prime polynomial over the prime powers
`n ≤ e^{2a}` is dominated by the pole-plus-archimedean part. -/
theorem riemannHypothesis_iff_primePolynomial_le_archPart :
    RiemannHypothesis ↔ ∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re := by
  rw [riemannHypothesis_iff_weilPositiveFull_vonMangoldt]
  constructor
  · intro hW a f hf hfs ξ
    have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
    have hgs := (tsupport_heightShift_subset ξ f).trans hfs
    have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
    have h := hW _ hg hgc
    rw [← zetaZeroConfig_W_eq_weilFullFunctional_bilinear hg hgc hg hgc,
      zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at h
    linarith
  · intro h g hg hgc
    obtain ⟨a, -, hsa⟩ := exists_radius_bound hgc
    have hgs : tsupport g ⊆ Icc (-a) a :=
      closure_minimal (fun u hu => abs_le.mp (hsa u hu)) isClosed_Icc
    have h0 := h a g hg hgs 0
    have hW := zetaZeroConfig_W_heightShift_eq_sub hg hgs 0
    rw [heightShift_zero] at hW
    rw [← zetaZeroConfig_W_eq_weilFullFunctional_bilinear hg hgc hg hgc, hW, Complex.sub_re]
    linarith

/-- **The minimal form.** The coupled criterion is equivalent to the `2 × 2` prime–Gamma
inequality on the two pole directions at every aperture. -/
theorem primePolynomial_le_archPart_iff_poleCompression :
    (∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re) ↔
      ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a :=
  riemannHypothesis_iff_primePolynomial_le_archPart.symm.trans
    riemannHypothesis_iff_weilPoleCompression_nonneg

/-- **Comparison with Bagchi.** Strong recurrence of `ζ` implies the coupled criterion. -/
theorem primePolynomial_le_archPart_of_zetaStronglyRecurrent (h : ZetaStronglyRecurrent) :
    ∀ a : ℝ, ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      ∀ ξ : ℝ, (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ≤ (archPart f ξ).re :=
  riemannHypothesis_iff_primePolynomial_le_archPart.mp
    (riemannHypothesis_of_zetaStronglyRecurrent h)

/-! ### The pole terms of an odd profile -/

/-- **The pole is a depth-`½` pair.** For a real odd profile the pole terms are
`−2(∫ s(u) sinh(u/2) du)²`. -/
theorem pole_terms_odd_eq {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) :
    paperFT (EF.weilTest (fun u => (s u : ℂ)) (fun u => (s u : ℂ))) (I / 2) +
        paperFT (EF.weilTest (fun u => (s u : ℂ)) (fun u => (s u : ℂ))) (-I / 2) =
      ((-(2 * (∫ u, s u * Real.sinh (1 / 2 * u)) ^ 2) : ℝ) : ℂ) := by
  have hS : Continuous fun u => (s u : ℂ) := Complex.continuous_ofReal.comp hs
  have hSc : HasCompactSupport fun u => (s u : ℂ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
      by_contra h
      exact hu (abs_le.mp (hsupp u fun h0 => h (by simp [h0])))
  have e1 : I / 2 = I * ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : -I / 2 = -(I * ((1 / 2 : ℝ) : ℂ)) := by push_cast; ring
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_weilTest hS hS hSc hSc, EF.paperFT_weilTest hS hS hSc hSc, hc1, hc2, e1, e2,
    paperFT_odd_I_mul hs hsupp hodd, paperFT_odd_neg_I_mul hs hsupp hodd]
  simp only [map_neg, Complex.conj_ofReal]
  push_cast
  ring

/-! ### The archimedean term -/

/-- An upper bound for the archimedean density: `μ(τ) ≤ log(1 + |τ|)/2π + C`. -/
theorem exists_mu_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  refine ⟨|C|, abs_nonneg C, fun τ => ?_⟩
  have hπ : 0 < 2 * π := by positivity
  have hlogpos : 0 ≤ Real.log (1 + |τ|) / (2 * π) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg τ])) hπ.le
  have hbig : ∀ t : ℝ, 1 ≤ |t| → mu t ≤ Real.log (1 + |t|) / (2 * π) + |C| := by
    intro t ht
    have h := hC t ht
    have hle := (abs_le.mp h).2
    have hlog : Real.log (|t| / (2 * π)) ≤ Real.log (1 + |t|) := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hπ]
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    have hCt : C / t ^ 2 ≤ |C| := by
      have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      calc C / t ^ 2 ≤ |C| / t ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| := div_le_self (abs_nonneg C) ht2
    have h3 : 1 / (2 * π) * Real.log (|t| / (2 * π)) ≤ Real.log (1 + |t|) / (2 * π) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hlog hπ.le
    linarith
  by_cases hτ : 1 ≤ |τ|
  · exact hbig τ hτ
  · rw [not_le] at hτ
    have heven : mu τ = mu |τ| := by
      rcases le_or_gt 0 τ with h0 | h0
      · rw [abs_of_nonneg h0]
      · rw [abs_of_neg h0, gammaFacts.even]
    have hmono : mu |τ| ≤ mu 1 :=
      gammaFacts.monotoneOn (abs_nonneg τ) (show (0 : ℝ) ≤ 1 by norm_num) hτ.le
    have h1 := hbig 1 (by norm_num)
    have hlog1 : Real.log (1 + |(1 : ℝ)|) / (2 * π) ≤ 1 / (2 * π) := by
      rw [abs_one]
      refine div_le_div_of_nonneg_right ?_ hπ.le
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 by norm_num)
      linarith
    have hμ1 : mu 1 ≤ 1 / (2 * π) + |C| := by linarith
    -- at `τ = 1` the Stirling bound is sharper: `μ(1) ≤ log(1/2π)/2π + |C| ≤ |C|`
    have hsharp : mu 1 ≤ |C| := by
      have h := hC 1 (by norm_num)
      have hle := (abs_le.mp h).2
      have hneg : 1 / (2 * π) * Real.log (|(1 : ℝ)| / (2 * π)) ≤ 0 := by
        rw [abs_one]
        refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos (by positivity) ?_)
        rw [div_le_one hπ]
        nlinarith [Real.pi_gt_three]
      have hC1 : C / (1 : ℝ) ^ 2 ≤ |C| := by rw [one_pow, div_one]; exact le_abs_self C
      linarith
    linarith

theorem one_div_one_add_abs_pow_four_le (τ : ℝ) : 1 / (1 + |τ|) ^ 4 ≤ (1 + τ ^ 2)⁻¹ := by
  have h1 : 1 + τ ^ 2 ≤ (1 + |τ|) ^ 4 := by
    have h2 : 1 + τ ^ 2 ≤ (1 + |τ|) ^ 2 := by nlinarith [sq_abs τ, abs_nonneg τ]
    have h3 : 1 ≤ (1 + |τ|) ^ 2 := by nlinarith [abs_nonneg τ]
    nlinarith
  rw [one_div]
  exact inv_anti₀ (by positivity) h1

/-- **The archimedean term of a profile.** With `B_c = 4(‖c‖₁ + ‖c''‖₁)`,
`∫ |h_c|² μ ≤ B_c² (1/2 + πC)`. -/
theorem integral_norm_sq_paperFT_mul_mu_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c)
    (hcc : HasCompactSupport c) {a : ℝ} (hca : ∀ u, c u ≠ 0 → |u| ≤ a) :
    ∫ τ : ℝ, ‖paperFT c τ‖ ^ 2 * mu τ ≤
      (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)) ^ 2 * (1 / 2 + π * C) := by
  set B := 4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖) with hB
  have hkd : ContDiff ℝ 2 (EF.weilTest c c) := EF.weilTest_contDiff hc hc.continuous hcc
  have hkc : HasCompactSupport (EF.weilTest c c) := EF.weilTest_hasCompactSupport hcc hcc
  have hval := paperFT_weilTest_self_ofReal hc.continuous hcc
  have hint : Integrable fun τ : ℝ => ‖paperFT c τ‖ ^ 2 * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
  have hπ : 0 < 2 * π := by positivity
  set K : ℝ := B ^ 2 * (1 / (2 * π) + C) with hK
  have hbound : Integrable fun τ : ℝ => K * (1 + τ ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul K
  have hptw : ∀ τ : ℝ, ‖paperFT c τ‖ ^ 2 * mu τ ≤ K * (1 + τ ^ 2)⁻¹ := by
    intro τ
    have hdec := norm_paperFT_le_decay hc hca (τ : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.ofReal_re] at hdec
    have hF0 : 0 ≤ ‖paperFT c τ‖ ^ 2 := sq_nonneg _
    have hF : ‖paperFT c τ‖ ^ 2 ≤ B ^ 2 * (1 / (1 + |τ|) ^ 4) := by
      calc ‖paperFT c τ‖ ^ 2 ≤ (B / (1 + |τ|) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hdec 2
        _ = B ^ 2 * (1 / (1 + |τ|) ^ 4) := by
            rw [div_pow, ← pow_mul]
            ring
    have hL0 : 0 ≤ Real.log (1 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
    have hL : Real.log (1 + |τ|) ≤ 1 + |τ| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + |τ| by positivity)
      linarith
    have hp1 : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have hw0 : 0 ≤ Real.log (1 + |τ|) / (2 * π) + C := by positivity
    have hstep : (1 / (1 + |τ|) ^ 4) * (Real.log (1 + |τ|) / (2 * π) + C) ≤
        (1 / (2 * π) + C) * (1 + τ ^ 2)⁻¹ := by
      have h4 := one_div_one_add_abs_pow_four_le τ
      have h3 : 1 / (1 + |τ|) ^ 4 * Real.log (1 + |τ|) ≤ (1 + τ ^ 2)⁻¹ := by
        have hq : 1 / (1 + |τ|) ^ 4 * Real.log (1 + |τ|) ≤ 1 / (1 + |τ|) ^ 4 * (1 + |τ|) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        have hq2 : 1 / (1 + |τ|) ^ 4 * (1 + |τ|) ≤ 1 / (1 + |τ|) ^ 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_le_pow_right₀ hp1 (show 3 ≤ 4 by norm_num)]
        have hq3 : 1 / (1 + |τ|) ^ 2 ≤ (1 + τ ^ 2)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ (by positivity) (by nlinarith [sq_abs τ, abs_nonneg τ])
        linarith
      have hC4 : 1 / (1 + |τ|) ^ 4 * C ≤ (1 + τ ^ 2)⁻¹ * C := mul_le_mul_of_nonneg_right h4 hC0
      calc (1 / (1 + |τ|) ^ 4) * (Real.log (1 + |τ|) / (2 * π) + C)
          = (1 / (1 + |τ|) ^ 4 * Real.log (1 + |τ|)) / (2 * π) + 1 / (1 + |τ|) ^ 4 * C := by ring
        _ ≤ (1 + τ ^ 2)⁻¹ / (2 * π) + (1 + τ ^ 2)⁻¹ * C := by
            gcongr
        _ = (1 / (2 * π) + C) * (1 + τ ^ 2)⁻¹ := by ring
    calc ‖paperFT c τ‖ ^ 2 * mu τ ≤ ‖paperFT c τ‖ ^ 2 * (Real.log (1 + |τ|) / (2 * π) + C) :=
          mul_le_mul_of_nonneg_left (hC τ) hF0
      _ ≤ B ^ 2 * (1 / (1 + |τ|) ^ 4) * (Real.log (1 + |τ|) / (2 * π) + C) :=
          mul_le_mul_of_nonneg_right hF hw0
      _ = B ^ 2 * ((1 / (1 + |τ|) ^ 4) * (Real.log (1 + |τ|) / (2 * π) + C)) := by ring
      _ ≤ B ^ 2 * ((1 / (2 * π) + C) * (1 + τ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg B)
      _ = K * (1 + τ ^ 2)⁻¹ := by rw [hK]; ring
  calc ∫ τ : ℝ, ‖paperFT c τ‖ ^ 2 * mu τ ≤ ∫ τ : ℝ, K * (1 + τ ^ 2)⁻¹ :=
        integral_mono hint hbound hptw
    _ = K * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
    _ = B ^ 2 * (1 / 2 + π * C) := by
        rw [hK]
        field_simp

/-! ### The archimedean–pole part at height `0` can be negative -/

theorem archPart_zero_eq (f : ℝ → ℂ) :
    archPart f 0 = paperFT (EF.weilTest f f) (I / 2) + paperFT (EF.weilTest f f) (-I / 2) +
      ∫ τ : ℝ, paperFT (EF.weilTest f f) τ * (mu τ : ℂ) := by
  rw [archPart, heightShift_zero]

theorem sinhTest_tsupport_subset {a δ : ℝ} (ha : 0 ≤ a) :
    tsupport (fun u => ((sinhTest a δ u : ℝ) : ℂ)) ⊆ Icc (-a) a :=
  closure_minimal (fun u hu => abs_le.mp (sinhTest_supp (δ := δ) ha u fun h => hu (by
    simp only [h, Complex.ofReal_zero]))) isClosed_Icc

theorem sinhTest_ofReal_contDiff (a δ : ℝ) :
    ContDiff ℝ 2 (fun u => ((sinhTest a δ u : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (sinhTest_contDiff a δ)

/-- **The archimedean–pole part of an odd profile at height `0`.** For a real odd `C²` profile
`s` supported in `[-a, a]`, `Re A(0) ≤ −2P² + (4N)²(1/2 + πC)`, with `P = ∫ s(u) sinh(u/2) du`
and `N = ‖s‖₁ + ‖s''‖₁`. -/
theorem re_archPart_zero_le_of_odd {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {s : ℝ → ℝ} {a : ℝ}
    (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) :
    (archPart (fun u => (s u : ℂ)) 0).re ≤
      -(2 * (∫ u, s u * Real.sinh (1 / 2 * u)) ^ 2) + (4 * testNorm s) ^ 2 * (1 / 2 + π * C) := by
  have hf : ContDiff ℝ 2 (fun u => (s u : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hfsupp : ∀ u, (fun u => (s u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    hsupp u fun h => hu (by simp only [h, Complex.ofReal_zero])
  have hfc : HasCompactSupport (fun u => (s u : ℂ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
      by_contra h
      exact hu (abs_le.mp (hfsupp u h))
  have hval := paperFT_weilTest_self_ofReal hf.continuous hfc
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (fun u => (s u : ℂ)) (fun u => (s u : ℂ))) τ *
      (mu τ : ℂ)).re = ∫ τ : ℝ, ‖paperFT (fun u => (s u : ℂ)) τ‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (fun u => (s u : ℂ)) (fun u => (s u : ℂ))) τ *
        (mu τ : ℂ)) = fun τ : ℝ => ((‖paperFT (fun u => (s u : ℂ)) τ‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  have harch := integral_norm_sq_paperFT_mul_mu_le hC0 hC hf hfc hfsupp
  have hB : 4 * ((∫ u, ‖(fun u => (s u : ℂ)) u‖) +
      ∫ u, ‖deriv (deriv (fun u => (s u : ℂ))) u‖) = 4 * testNorm s := rfl
  rw [hB] at harch
  rw [archPart_zero_eq, Complex.add_re, pole_terms_odd_eq hs.continuous hsupp hodd,
    Complex.ofReal_re, hμre]
  linarith

/-- Sizes of the depth-`½` odd profile `sinh(u/2)(a² − u²)₊^{5/2}` for `a ≥ 4`. -/
theorem sinhTest_half_sizes {a : ℝ} (ha4 : 4 ≤ a) :
    a ^ 5 * (Real.exp ((a - 2) / 2) / 4) ^ 4 ≤
        (∫ u, sinhTest a (1 / 2) u * Real.sinh (1 / 2 * u)) ^ 2 ∧
      4 * testNorm (sinhTest a (1 / 2)) ≤ 32 * a ^ 6 * Real.exp (a / 2) := by
  have ha : 0 < a := by linarith
  constructor
  · have hPlb := sinhTest_energy_ge (a := a) (δ := 1 / 2) (w := 1) (by norm_num) one_pos
      (by linarith)
    rw [one_mul, one_mul, show a - 2 * 1 = a - 2 by ring] at hPlb
    have hsinh : Real.exp ((a - 2) / 2) / 4 ≤ Real.sinh (1 / 2 * (a - 2)) := by
      rw [Real.sinh_eq, show 1 / 2 * (a - 2) = (a - 2) / 2 by ring]
      have he : 2 ≤ Real.exp ((a - 2) / 2) := by
        have := Real.add_one_le_exp ((a - 2) / 2)
        linarith
      have hpos := Real.exp_pos ((a - 2) / 2)
      have h2 : Real.exp (-((a - 2) / 2)) ≤ Real.exp ((a - 2) / 2) / 2 := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
        nlinarith
      linarith
    have hrpow : ((a : ℝ) ^ (5 / 2 : ℝ)) ^ 2 = a ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      norm_num
    have hsinh0 : 0 ≤ Real.exp ((a - 2) / 2) / 4 := by positivity
    have hP0 : 0 ≤ a ^ (5 / 2 : ℝ) * Real.sinh (1 / 2 * (a - 2)) ^ 2 := by positivity
    have h2 := pow_le_pow_left₀ hP0 hPlb 2
    have h3 : (Real.exp ((a - 2) / 2) / 4) ^ 4 ≤ Real.sinh (1 / 2 * (a - 2)) ^ 4 :=
      pow_le_pow_left₀ hsinh0 hsinh 4
    calc a ^ 5 * (Real.exp ((a - 2) / 2) / 4) ^ 4 ≤ a ^ 5 * Real.sinh (1 / 2 * (a - 2)) ^ 4 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (a ^ (5 / 2 : ℝ) * Real.sinh (1 / 2 * (a - 2)) ^ 2) ^ 2 := by
          rw [mul_pow, hrpow]
          ring
      _ ≤ _ := h2
  · have hN := testNorm_sinhTest_le ha.le (show (0 : ℝ) ≤ 1 / 2 by norm_num) (a := a)
    have hpoly : a ^ 5 + (1 / 2) ^ 2 * a ^ 5 + 10 * (1 / 2) * a ^ 4 + 20 * a ^ 3 ≤ 4 * a ^ 5 := by
      have ha2 : 16 ≤ a ^ 2 := by nlinarith
      have h3 : a ^ 3 * 16 ≤ a ^ 5 := by
        calc a ^ 3 * 16 ≤ a ^ 3 * a ^ 2 := mul_le_mul_of_nonneg_left ha2 (by positivity)
          _ = a ^ 5 := by ring
      have h4 : a ^ 4 * 4 ≤ a ^ 5 := by
        calc a ^ 4 * 4 ≤ a ^ 4 * a := mul_le_mul_of_nonneg_left ha4 (by positivity)
          _ = a ^ 5 := by ring
      nlinarith
    have hcosh : Real.cosh (1 / 2 * a) ≤ Real.exp (a / 2) := by
      rw [Real.cosh_eq, show 1 / 2 * a = a / 2 by ring]
      have : Real.exp (-(a / 2)) ≤ Real.exp (a / 2) := Real.exp_le_exp.mpr (by linarith)
      linarith
    calc 4 * testNorm (sinhTest a (1 / 2)) ≤ 4 * (2 * a * Real.cosh (1 / 2 * a) *
          (a ^ 5 + (1 / 2) ^ 2 * a ^ 5 + 10 * (1 / 2) * a ^ 4 + 20 * a ^ 3)) := by
          linarith
      _ ≤ 4 * (2 * a * Real.exp (a / 2) * (4 * a ^ 5)) := by
          gcongr
      _ = 32 * a ^ 6 * Real.exp (a / 2) := by ring

/-- The exponential beats the polynomial loss. -/
theorem pole_beats_arch {a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hexp : 131072 * K * Real.exp 4 * a ^ 7 < Real.exp a) :
    (32 * a ^ 6 * Real.exp (a / 2)) ^ 2 * K < 2 * (a ^ 5 * (Real.exp ((a - 2) / 2) / 4) ^ 4) := by
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  have hea : 0 < Real.exp a := Real.exp_pos a
  have hL : (32 * a ^ 6 * Real.exp (a / 2)) ^ 2 * K = 1024 * a ^ 12 * Real.exp a * K := by
    rw [mul_pow, mul_pow, sq (Real.exp (a / 2)), ← Real.exp_add, add_halves]
    ring
  have hR : (Real.exp ((a - 2) / 2) / 4) ^ 4 = Real.exp a * Real.exp a / (256 * Real.exp 4) := by
    rw [div_pow, ← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * ((a - 2) / 2) = a + a - 4 by
      push_cast; ring, Real.exp_sub, Real.exp_add]
    ring
  rw [hL, hR]
  have h1 : 2 * (a ^ 5 * (Real.exp a * Real.exp a / (256 * Real.exp 4))) =
      a ^ 5 * Real.exp a / (128 * Real.exp 4) * Real.exp a := by
    field_simp
    ring
  have h2 : 1024 * a ^ 12 * Real.exp a * K =
      a ^ 5 * Real.exp a / (128 * Real.exp 4) * (131072 * K * Real.exp 4 * a ^ 7) := by
    field_simp
    ring
  rw [h1, h2]
  exact mul_lt_mul_of_pos_left hexp (by positivity)

/-- **The pole dominates at large aperture.** For the odd profile `sinh(u/2)(a² − u²)₊^{5/2}`
and large `a`, the pole-plus-archimedean part at height `0` is negative. -/
theorem exists_archPart_zero_neg :
    ∃ a : ℝ, 0 < a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (archPart f 0).re < 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_mu_le
  have hK : 0 < 1 / 2 + π * C := by positivity
  obtain ⟨a, ha4, haM⟩ := ((Filter.eventually_ge_atTop (4 : ℝ)).and
    ((Real.tendsto_exp_div_pow_atTop 7).eventually_gt_atTop
      (131072 * (1 / 2 + π * C) * Real.exp 4))).exists
  have ha : 0 < a := by linarith
  have hexp : 131072 * (1 / 2 + π * C) * Real.exp 4 * a ^ 7 < Real.exp a := by
    have h7 : 0 < a ^ 7 := by positivity
    rwa [lt_div_iff₀ h7] at haM
  refine ⟨a, ha, fun u => ((sinhTest a (1 / 2) u : ℝ) : ℂ), sinhTest_ofReal_contDiff a _,
    sinhTest_tsupport_subset ha.le, ?_⟩
  have hle := re_archPart_zero_le_of_odd hC0 hC (sinhTest_contDiff a (1 / 2))
    (sinhTest_supp ha.le) (sinhTest_odd a _)
  obtain ⟨hP, hB⟩ := sinhTest_half_sizes ha4
  have hbeat := pole_beats_arch ha hK hexp
  have hB0 : 0 ≤ 4 * testNorm (sinhTest a (1 / 2)) := by
    have := testNorm_nonneg (sinhTest a (1 / 2))
    positivity
  have hB2 : (4 * testNorm (sinhTest a (1 / 2))) ^ 2 ≤ (32 * a ^ 6 * Real.exp (a / 2)) ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  have hB2K := mul_le_mul_of_nonneg_right hB2 hK.le
  linarith

/-! ### The prime polynomial takes values above any negative level -/

/-- The windowed mean of an exponential sum: `∫ |h_η(−2πξ)|² Q(ξ) dξ = Σ_j c_j k_η(ν_j)`. -/
theorem integral_pairTransform_mul_expSum {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) :
    ∫ ξ : ℝ, pairTransform η ξ * expSum s c ν ξ = ∑ j ∈ s, c j * EF.weilTest η η (ν j) := by
  obtain ⟨r, -, hsη⟩ := exists_radius_bound hηc
  have hPc : Continuous fun ξ : ℝ => pairTransform η ξ :=
    (differentiable_pairTransform hη hηc).continuous.comp Complex.continuous_ofReal
  have hPi := integrable_pairTransform hη hηc
  have hint : ∀ j : ι, Integrable fun ξ : ℝ => pairTransform η ξ *
      (c j * cexp (2 * π * I * ξ * ν j)) := by
    intro j
    refine (hPi.norm.const_mul ‖c j‖).mono'
      (hPc.mul (continuous_const.mul (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_mul, norm_cexp_two_pi_I_mul, mul_one, mul_comm]
  simp only [expSum, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => hint j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilTest_eq_integral hη hηc hsη (ν j), ← integral_const_mul]
  congr 1 with ξ
  ring

/-- A fixed window of aperture `1/4` with positive energy. -/
theorem integral_sinhTest_sq_pos : 0 < ∫ t, ‖((sinhTest (1 / 4) 1 t : ℝ) : ℂ)‖ ^ 2 := by
  set s := sinhTest (1 / 4) 1 with hs
  have hcont : Continuous s := (sinhTest_contDiff _ _).continuous
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ 1 / 4 := sinhTest_supp (by norm_num)
  have hsq : (fun t => ‖((s t : ℝ) : ℂ)‖ ^ 2) = fun t => s t ^ 2 := by
    funext t
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hcs : HasCompactSupport s :=
    HasCompactSupport.intro (isCompact_Icc (a := -(1 / 4)) (b := 1 / 4)) fun u hu => by
      by_contra h
      exact hu (abs_le.mp (hsupp u h))
  have hint : Integrable fun t => s t ^ 2 :=
    (hcont.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro hcs
      fun t ht => by simp [image_eq_zero_of_notMem_tsupport ht])
  have hnn : 0 ≤ ∫ t, s t ^ 2 := integral_nonneg fun t => sq_nonneg (s t)
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    have hae : (fun t => s t ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (f := fun t => s t ^ 2) (fun t => sq_nonneg (s t)) hint).mp
        h.symm
    have hae' : (fun t => s t * Real.sinh (1 * t)) =ᵐ[volume] 0 := by
      filter_upwards [hae] with t ht
      have : s t = 0 := by simpa using ht
      simp [this]
    have hzero : ∫ t, s t * Real.sinh (1 * t) = 0 := by
      rw [integral_congr_ae hae']
      simp
    have hlb := sinhTest_energy_ge (a := 1 / 4) (δ := 1) (w := 1 / 16) one_pos (by norm_num)
      (by norm_num)
    have hpos : 0 < 1 / 16 * (1 / 16 * (1 / 4)) ^ (5 / 2 : ℝ) *
        Real.sinh (1 * (1 / 4 - 2 * (1 / 16))) ^ 2 := by
      have : 0 < Real.sinh (1 * (1 / 4 - 2 * (1 / 16))) := Real.sinh_pos_iff.mpr (by norm_num)
      positivity
    rw [← hs, hzero] at hlb
    linarith

/-- **The prime polynomial exceeds every negative level somewhere.** Its windowed mean is zero,
since all its frequencies `±log n` lie outside the support `[-1/2, 1/2]` of `k_η`. -/
theorem exists_lt_re_primePolynomial (f : ℝ → ℂ) (N : ℕ) {A₀ : ℝ} (hA₀ : A₀ < 0) :
    ∃ ξ : ℝ, A₀ < (primePolynomial f N ξ).re := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  set η : ℝ → ℂ := fun u => ((sinhTest (1 / 4) 1 u : ℝ) : ℂ) with hηdef
  have hη : ContDiff ℝ 2 η := sinhTest_ofReal_contDiff _ _
  have hηs : tsupport η ⊆ Icc (-(1 / 4)) (1 / 4) := sinhTest_tsupport_subset (by norm_num)
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hPdef
  have hPval : ∀ ξ : ℝ, pairTransform η ξ = ((P ξ : ℝ) : ℂ) := fun ξ =>
    pairTransform_ofReal hη hηc ξ
  -- windowed mean zero
  have hmean : ∫ ξ : ℝ, pairTransform η ξ * primePolynomial f N ξ = 0 := by
    simp only [primePolynomial]
    rw [integral_pairTransform_mul_expSum hη hηc]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨n, b⟩ := j
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hj
    have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hj.1)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this
      linarith
    have hfar : 2 * (1 / 4 : ℝ) ≤ |primeFreq (n, b)| := by
      cases b <;> simp only [primeFreq, ↓reduceIte, Bool.false_eq_true, abs_neg] <;>
        rw [abs_of_nonneg (by linarith)] <;> linarith
    rw [weilTest_self_eq_zero_of_le hη hηs hfar, mul_zero]
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hPval, RCLike.re_to_complex, Complex.ofReal_re]
  have hQc : Continuous (primePolynomial f N) := by
    unfold primePolynomial
    exact continuous_expSum _ _ _
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖primePolynomial f N ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, hPval, Complex.ofReal_re]
  have hPQi : Integrable fun ξ => P ξ * (primePolynomial f N ξ).re := by
    refine (hPi.mul_const C).mono' (hPc.mul (Complex.continuous_re.comp hQc)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hQb ξ)) (sq_nonneg _)
  have hre0 : ∫ ξ, P ξ * (primePolynomial f N ξ).re = 0 := by
    have hcont : Integrable fun ξ : ℝ => pairTransform η ξ * primePolynomial f N ξ := by
      refine ((integrable_pairTransform hη hηc).norm.mul_const C).mono'
        ((differentiable_pairTransform hη hηc).continuous.comp
          Complex.continuous_ofReal |>.mul hQc).aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hQb ξ) (norm_nonneg _)
    have h := integral_re hcont
    simp only [RCLike.re_to_complex] at h
    rw [hmean, Complex.zero_re] at h
    rw [← h]
    congr 1 with ξ
    rw [hPval, Complex.re_ofReal_mul]
  have hmass : ∫ ξ, P ξ = ∫ t, ‖η t‖ ^ 2 := by
    have h := weilTest_eq_integral hη hηc (a := 1 / 4) (fun u hu => by
      by_contra h'
      exact hu (image_eq_zero_of_notMem_tsupport fun ht => h' (abs_le.mpr (hηs ht)))) 0
    rw [weilTest_self_zero] at h
    have h2 : ∫ ξ : ℝ, pairTransform η ξ * cexp (2 * π * I * ξ * ((0 : ℝ) : ℂ)) =
        ((∫ ξ, P ξ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1 with ξ
      rw [hPval]
      simp
    rw [h2] at h
    exact_mod_cast h.symm
  have hle : ∫ ξ, P ξ * (primePolynomial f N ξ).re ≤ ∫ ξ, P ξ * A₀ :=
    integral_mono hPQi (hPi.mul_const A₀) fun ξ =>
      mul_le_mul_of_nonneg_left (hcon ξ) (sq_nonneg _)
  rw [hre0, integral_mul_const, hmass] at hle
  have hpos := integral_sinhTest_sq_pos
  nlinarith

/-! ### The coupling is necessary -/

/-- **The archimedean–pole side cannot be frozen.** There is a profile whose pole-plus-archimedean
part at height `0` is negative and lies below the prime polynomial at some height. So the
inequality `Re Π_f(ξ) ≤ Re A_f(0)` fails: the prime polynomial must be compared with the
archimedean–pole side at its own height. -/
theorem exists_archPart_zero_lt_primePolynomial :
    ∃ a : ℝ, 0 < a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (archPart f 0).re < 0 ∧
        ∃ ξ : ℝ, (archPart f 0).re < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re := by
  obtain ⟨a, ha, f, hf, hfs, hneg⟩ := exists_archPart_zero_neg
  exact ⟨a, ha, f, hf, hfs, hneg, exists_lt_re_primePolynomial f _ hneg⟩

/-- **The primes must pay the pole.** For the same profile, RH forces the prime polynomial at
height `0` to be negative: the finitely many prime powers `n ≤ e^{2a}` must cancel the pole. -/
theorem re_primePolynomial_zero_neg :
    ∃ a : ℝ, 0 < a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (archPart f 0).re < 0 ∧
        (RiemannHypothesis → (primePolynomial f ⌊Real.exp (2 * a)⌋₊ 0).re < 0) := by
  obtain ⟨a, ha, f, hf, hfs, hneg⟩ := exists_archPart_zero_neg
  refine ⟨a, ha, f, hf, hfs, hneg, fun hRH => ?_⟩
  have h := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs 0
  linarith

end GaloisForLFunctions.SquareRootThreshold
