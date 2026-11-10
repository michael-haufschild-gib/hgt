import GaloisForLFunctions.InfiniteRankPurityTheory.ADirichletPolynomialWithItsZerosOnTheLineHasAFunctionalEquation
import GaloisForLFunctions.InfiniteRankPurityTheory.TheConstantTermsOnTheTwoSidesOfTheLineAgree
import GaloisForLFunctions.InfiniteRankPurityTheory.AZeroFreeExponentialPolynomialIsBoundedBelow
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# No Dirichlet polynomial is a factor of ξ

Every Dirichlet polynomial `D(s) = Σ a_n n^{−s}` with at least two terms has a zero that is not a
zero of `ξ` (`exists_zero_not_xi_zero`). No hypothesis is made on the support: there may be no
constant term and the frequencies may involve several bases.

Suppose every zero of `D` is a zero of `ξ`; let `m` be the lowest and `N` the highest frequency.

* The zeros lie on the critical line, and `ζ` vanishes at them. So `F = −(ζ/s) D'/D` is holomorphic
  on the strip (`exists_differentiableOn_deriv_mul_div`).
* Right of the line `D = a_m m^{−s} P(s)` and left of it `D = a_N N^{−s} Q(−s)` with exponential
  polynomials `P`, `Q` that have no zeros there. Their logarithmic derivatives expand absolutely up
  to the line (`hasSum_logWeight_of_zeroFree`): `D'/D = −log m + Σ b_i a_i^s` with `a_i < 1` on the
  right, `D'/D = −log N + Σ c_j q_j^s` with `q_j > 1` on the left.
* `F` is bounded near the line: on the lines `Re s = ¼, ¾` because `P` and `Q` are bounded below,
  in between by the maximum principle between heights at which `‖D‖` is bounded below
  (`exists_good_heights`, `norm_le_of_good_heights`), with `‖ζ(s)/s‖ ≤ 1/(1 − Re s) + 1/Re s`.
* By `constantTerms_agree` the two constant terms agree: `−log N = −log m`.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-- In the strip, `‖ζ(s)/s‖ ≤ 1/(1 − Re s) + 1/Re s`. -/
theorem norm_riemannZeta_div_le {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    ‖riemannZeta z / z‖ ≤ 1 / (1 - z.re) + 1 / z.re := by
  have hz1 : z ≠ 1 := fun h => by
    rw [h, Complex.one_re] at h1
    exact lt_irrefl 1 h1
  have hint := integral_ladderKernel h0 hz1
  have hI : ‖∫ x in Ioi (0 : ℝ), ladderKernel z x‖ ≤ 1 / z.re := by
    have hgi : IntegrableOn (fun x : ℝ => Real.exp (-z.re * x)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 h0
    have h := norm_integral_le_of_norm_le hgi (Eventually.of_forall fun x => by
      have := norm_ladderKernel_le z x
      rwa [← neg_mul] at this)
    rw [integral_exp_mul_Ioi (neg_neg_of_pos h0) 0, mul_zero, Real.exp_zero] at h
    refine h.trans (le_of_eq ?_)
    rw [neg_div_neg_eq]
  have hsub : ‖(1 : ℂ) / (z - 1)‖ ≤ 1 / (1 - z.re) := by
    rw [norm_div, norm_one]
    refine one_div_le_one_div_of_le (by linarith) ?_
    have := Complex.abs_re_le_norm (z - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [neg_le_abs (z.re - 1)]
  have heq : riemannZeta z / z = 1 / (z - 1) - ∫ x in Ioi (0 : ℝ), ladderKernel z x := by
    rw [hint]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hsub hI)

theorem norm_dirDeriv_le {a : ℕ →₀ ℂ} (ha0 : a 0 = 0) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖dirDeriv a z‖ ≤ ∑ n ∈ a.support, ‖a n‖ * Real.log n := by
  unfold dirDeriv
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 := pos_of_mem_support ha0 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1),
    Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (Real.log_nonneg hn1))
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hz))

theorem analyticOrderAt_finiteDirichletPolynomial_ne_top {a : ℕ →₀ ℂ} (ha0 : a 0 = 0)
    (hane : a ≠ 0) (z : ℂ) : analyticOrderAt (finiteDirichletPolynomial a) z ≠ ⊤ := by
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  exact finiteDirichletPolynomial_ne_zero a ha0 hane (funext fun s =>
    (hDd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) htop (mem_univ s))

/-- **No Dirichlet polynomial is a factor of `ξ`.** A Dirichlet polynomial with at least two terms
has a zero that is not a zero of `ξ`. -/
theorem exists_zero_not_xi_zero (a : ℕ →₀ ℂ) (ha0 : a 0 = 0) {n₁ n₂ : ℕ} (h₁ : a n₁ ≠ 0)
    (h₂ : a n₂ ≠ 0) (hne : n₁ ≠ n₂) :
    ∃ z : ℂ, finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0 := by
  by_contra hcon
  have hall : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → xi z = 0 := fun z hz => by
    by_contra hxi
    exact hcon ⟨z, hz, hxi⟩
  have hane : a ≠ 0 := fun h => h₁ (by rw [h]; rfl)
  have hline : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → z.re = 1 / 2 := fun z hz =>
    re_eq_half_of_dirichletPolynomial_zeros_subset_xi a ha0 hane hall hz
  have hζ : ∀ z : ℂ, finiteDirichletPolynomial a z = 0 → riemannZeta z = 0 := fun z hz =>
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp (hall z hz)).1
  have hDd := differentiable_finiteDirichletPolynomial a ha0
  -- the lowest and the highest frequency
  have hs₁ : n₁ ∈ a.support := Finsupp.mem_support_iff.mpr h₁
  have hs₂ : n₂ ∈ a.support := Finsupp.mem_support_iff.mpr h₂
  set m : ℕ := a.support.min' ⟨n₁, hs₁⟩ with hm
  set N : ℕ := a.support.max' ⟨n₁, hs₁⟩ with hN
  have hmS : m ∈ a.support := Finset.min'_mem _ _
  have hNS : N ∈ a.support := Finset.max'_mem _ _
  have hmN : m < N := Finset.min'_lt_max' _ hs₁ hs₂ hne
  have ham : a m ≠ 0 := Finsupp.mem_support_iff.mp hmS
  have haN : a N ≠ 0 := Finsupp.mem_support_iff.mp hNS
  have hpos : ∀ n ∈ a.support, 0 < n := fun n hn => pos_of_mem_support ha0 hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hmS
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos N hNS
  have hDexp : ∀ s : ℂ, finiteDirichletPolynomial a s =
      ∑ n ∈ a.support, a n * cexp (-(Real.log n : ℂ) * s) := fun s => by
    unfold finiteDirichletPolynomial
    exact Finset.sum_congr rfl fun n hn => by rw [natCast_cpow_neg_eq_cexp (hpos n hn)]
  -- right of the line: normalization at the lowest frequency
  set cR : a.support.erase m → ℂ := fun k => a k / a m with hcR
  set ℓR : a.support.erase m → ℝ := fun k => Real.log k - Real.log m with hℓRdef
  have hℓR : ∀ k, 0 < ℓR k := by
    intro k
    have hk := Finset.mem_erase.mp k.2
    have hmk : m < (k : ℕ) := lt_of_le_of_ne (Finset.min'_le _ _ hk.2) (Ne.symm hk.1)
    exact sub_pos.mpr (Real.log_lt_log hm0 (by exact_mod_cast hmk))
  have hDR : ∀ s : ℂ, finiteDirichletPolynomial a s =
      a m * cexp (-(Real.log m : ℂ) * s) * expPoly cR ℓR s := fun s => by
    rw [hDexp, sum_exp_eq_expPoly a.support (fun n => a n) (fun n => Real.log n) hmS ham]
  -- left of the line: normalization at the highest frequency
  set cL : a.support.erase N → ℂ := fun k => a k / a N with hcL
  set ℓL : a.support.erase N → ℝ := fun k => Real.log N - Real.log k with hℓLdef
  have hℓL : ∀ k, 0 < ℓL k := by
    intro k
    have hk := Finset.mem_erase.mp k.2
    have hkN : (k : ℕ) < N := lt_of_le_of_ne (Finset.le_max' _ _ hk.2) hk.1
    have hk0 : (0 : ℝ) < (k : ℕ) := by exact_mod_cast hpos k hk.2
    exact sub_pos.mpr (Real.log_lt_log hk0 (by exact_mod_cast hkN))
  have hDL : ∀ s : ℂ, finiteDirichletPolynomial a s =
      a N * cexp (-(Real.log N : ℂ) * s) * expPoly cL ℓL (-s) := fun s => by
    rw [hDexp, sum_exp_eq_expPoly_neg a.support (fun n => a n) (fun n => Real.log n) hNS haN]
  have hPR : ∀ w : ℂ, 1 / 2 < w.re → expPoly cR ℓR w ≠ 0 := fun w hw h0 => by
    have hD0 : finiteDirichletPolynomial a w = 0 := by rw [hDR, h0, mul_zero]
    have := hline w hD0
    linarith
  have hPL : ∀ w : ℂ, -(1 / 2) < w.re → expPoly cL ℓL w ≠ 0 := fun w hw h0 => by
    have hD0 : finiteDirichletPolynomial a (-w) = 0 := by rw [hDL, neg_neg, h0, mul_zero]
    have := hline _ hD0
    rw [Complex.neg_re] at this
    linarith
  -- the two expansions of the logarithmic derivative
  haveI : Countable (freqMonoid ℓR) := by
    unfold freqMonoid
    exact (Set.countable_range _).to_subtype
  haveI : Countable (freqMonoid ℓL) := by
    unfold freqMonoid
    exact (Set.countable_range _).to_subtype
  obtain ⟨hRsum, hRhas⟩ := hasSum_logWeight_of_zeroFree (-(Real.log m : ℂ)) cR hℓR hPR
  obtain ⟨hLsum, hLhas⟩ := hasSum_logWeight_of_zeroFree (Real.log N : ℂ) cL hℓL hPL
  have hderiv : ∀ s : ℂ, deriv (finiteDirichletPolynomial a) s = dirDeriv a s := fun s =>
    (hasDerivAt_finiteDirichletPolynomial ha0 s).deriv
  have hΛR : ∀ s : ℂ, 1 / 2 < s.re →
      deriv (finiteDirichletPolynomial a) s / finiteDirichletPolynomial a s =
        -(Real.log m : ℂ) + expPolyDeriv cR ℓR s / expPoly cR ℓR s := by
    intro s hs
    have h := logDeriv_exp_mul (A := a m) (lam := (Real.log m : ℂ)) ham
      (hasDerivAt_expPoly cR ℓR s) (hPR s hs)
    have hfun : finiteDirichletPolynomial a =
        fun z => a m * cexp (-(Real.log m : ℂ) * z) * expPoly cR ℓR z := funext hDR
    rw [hfun]
    exact h
  have hΛL : ∀ s : ℂ, s.re < 1 / 2 →
      deriv (finiteDirichletPolynomial a) s / finiteDirichletPolynomial a s =
        -(Real.log N : ℂ) - expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s) := by
    intro s hs
    have h := logDeriv_exp_mul_neg (A := a N) (lam := (Real.log N : ℂ)) haN
      (hasDerivAt_expPoly cL ℓL (-s)) (hPL (-s) (by rw [Complex.neg_re]; linarith))
    have hfun : finiteDirichletPolynomial a =
        fun z => a N * cexp (-(Real.log N : ℂ) * z) * expPoly cL ℓL (-z) := funext hDL
    rw [hfun]
    exact h
  -- the function `F = −(ζ/s) D'/D`
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  set g : ℂ → ℂ := fun s => -(riemannZeta s / s) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by
      have := hs.2
      rw [h, Complex.one_re] at this
      exact lt_irrefl 1 this
    have hs0 : s ≠ 0 := fun h => by
      have := hs.1
      rw [h, Complex.zero_re] at this
      exact lt_irrefl 0 this
    exact (((differentiableAt_riemannZeta hs1).div differentiableAt_id hs0).neg).differentiableWithinAt
  have hzero : ∀ z ∈ U, finiteDirichletPolynomial a z = 0 → g z = 0 := fun z _ hz => by
    show -(riemannZeta z / z) = 0
    rw [hζ z hz, zero_div, neg_zero]
  obtain ⟨F, hFd, hFeq⟩ := exists_differentiableOn_deriv_mul_div hUo hDd.differentiableOn hgd
    (fun z _ => analyticOrderAt_finiteDirichletPolynomial_ne_top ha0 hane z) hzero
  have hFval : ∀ z ∈ U, finiteDirichletPolynomial a z ≠ 0 → F z = -(riemannZeta z / z) *
      (deriv (finiteDirichletPolynomial a) z / finiteDirichletPolynomial a z) := by
    intro z hz h0
    rw [hFeq z hz h0]
    show deriv (finiteDirichletPolynomial a) z * -(riemannZeta z / z) /
      finiteDirichletPolynomial a z = _
    ring
  -- `F` is bounded near the line
  obtain ⟨δR, hδR, hlowR⟩ := exists_le_norm_expPoly_of_zeroFree hℓR
    (show (1 / 2 : ℝ) < 3 / 4 by norm_num) hPR
  obtain ⟨δL, hδL, hlowL⟩ := exists_le_norm_expPoly_of_zeroFree hℓL
    (show (-(1 / 2) : ℝ) < -(1 / 4) by norm_num) hPL
  obtain ⟨μ, hμ, L, hgood⟩ := exists_good_heights ha0 hane hline
    (show (1 / 4 : ℝ) < 3 / 4 by norm_num)
  have hDlineR : ∀ z : ℂ, z.re = 3 / 4 → ‖a m‖ * Real.exp (-(Real.log m * (3 / 4))) * δR ≤
      ‖finiteDirichletPolynomial a z‖ := by
    intro z hz
    rw [hDR, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul, hz]
    exact mul_le_mul_of_nonneg_left (hlowR z (le_of_eq hz.symm)) (by positivity)
  have hDlineL : ∀ z : ℂ, z.re = 1 / 4 → ‖a N‖ * Real.exp (-(Real.log N * (1 / 4))) * δL ≤
      ‖finiteDirichletPolynomial a z‖ := by
    intro z hz
    rw [hDL, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul, hz]
    exact mul_le_mul_of_nonneg_left (hlowL (-z) (by rw [Complex.neg_re, hz]))
      (by positivity)
  set ν : ℝ := min μ (min (‖a m‖ * Real.exp (-(Real.log m * (3 / 4))) * δR)
    (‖a N‖ * Real.exp (-(Real.log N * (1 / 4))) * δL)) with hν
  have hνpos : 0 < ν := lt_min hμ (lt_min
    (mul_pos (mul_pos (norm_pos_iff.mpr ham) (Real.exp_pos _)) hδR)
    (mul_pos (mul_pos (norm_pos_iff.mpr haN) (Real.exp_pos _)) hδL))
  set CD : ℝ := ∑ n ∈ a.support, ‖a n‖ * Real.log n with hCD
  have hCD0 : 0 ≤ CD := Finset.sum_nonneg fun n hn =>
    mul_nonneg (norm_nonneg _) (Real.log_nonneg (by exact_mod_cast hpos n hn))
  have hFbound : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 / 4 →
      ν ≤ ‖finiteDirichletPolynomial a z‖ → ‖F z‖ ≤ 8 * CD / ν := by
    intro z h1 h2 hD
    have hzU : z ∈ U := ⟨by linarith, by linarith⟩
    have hD0 : finiteDirichletPolynomial a z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hνpos hD)
    rw [hFval z hzU hD0, norm_mul, norm_neg, hderiv,
      norm_div (dirDeriv a z) (finiteDirichletPolynomial a z)]
    have ha4 : 1 / (1 - z.re) ≤ 4 :=
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) (by linarith)).trans_eq
        (by norm_num)
    have hb4 : 1 / z.re ≤ 4 :=
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) h1).trans_eq (by norm_num)
    have hg8 : ‖riemannZeta z / z‖ ≤ 8 :=
      (norm_riemannZeta_div_le (by linarith) (by linarith)).trans (by linarith)
    have hd := norm_dirDeriv_le ha0 (z := z) (by linarith)
    calc ‖riemannZeta z / z‖ * (‖dirDeriv a z‖ / ‖finiteDirichletPolynomial a z‖)
        ≤ 8 * (CD / ν) :=
          mul_le_mul hg8 (div_le_div₀ hCD0 hd hνpos hD) (by positivity) (by norm_num)
      _ = 8 * CD / ν := by ring
  have hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ 8 * CD / ν := by
    intro s h1 h2
    refine norm_le_of_good_heights (x₁ := 1 / 4) (x₂ := 3 / 4) (by norm_num) (U := U)
      (fun z hz1 hz2 => ⟨by linarith, by linarith⟩) hFd (L := L) ?_ ?_ h1 h2
    · rintro z (hz | hz)
      · exact hFbound z (le_of_eq hz.symm) (by rw [hz]; norm_num)
          ((min_le_right _ _).trans ((min_le_right _ _).trans (hDlineL z hz)))
      · exact hFbound z (by rw [hz]; norm_num) (le_of_eq hz)
          ((min_le_right _ _).trans ((min_le_left _ _).trans (hDlineR z hz)))
    · intro y
      obtain ⟨T, hT, hTD⟩ := hgood y
      exact ⟨T, hT, fun z hz1 hz2 hzT =>
        hFbound z hz1 hz2 ((min_le_left _ _).trans (hTD z hz1 hz2 hzT))⟩
  -- the hypotheses of the kernel theorem
  have hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i : LogIndex (a.support.erase m) ℓR =>
      ‖logWeight (-(Real.log m : ℂ)) cR ℓR i‖ * Real.exp (-logExp ℓR i) ^ σ := by
    intro σ hσ
    refine (hRsum σ hσ).congr fun i => ?_
    rw [← Real.exp_mul]
    congr 2
    ring
  have hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j : LogIndex (a.support.erase N) ℓL =>
      ‖-logWeight (Real.log N : ℂ) cL ℓL j‖ * Real.exp (logExp ℓL j) ^ σ := by
    intro σ hσ
    refine (hLsum (-σ) (by linarith)).congr fun j => ?_
    rw [norm_neg, ← Real.exp_mul]
    congr 2
    ring
  have hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → F s = -(riemannZeta s / s) *
      ∑' i : LogIndex (a.support.erase m) ℓR, logWeight (-(Real.log m : ℂ)) cR ℓR i *
        ((Real.exp (-logExp ℓR i) : ℝ) : ℂ) ^ s := by
    intro s h0 h1
    have hsU : s ∈ U := ⟨by linarith, h1⟩
    have hD0 : finiteDirichletPolynomial a s ≠ 0 := fun h => by
      have := hline s h
      linarith
    rw [hFval s hsU hD0, hΛR s h0, ← (hRhas s h0).tsum_eq]
    congr 1
    refine tsum_congr fun i => ?_
    rw [exp_cpow_eq_cexp, Complex.ofReal_neg]
  have hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → F s = -(riemannZeta s / s) *
      ∑' j : LogIndex (a.support.erase N) ℓL, -logWeight (Real.log N : ℂ) cL ℓL j *
        ((Real.exp (logExp ℓL j) : ℝ) : ℂ) ^ s := by
    intro s h0 h1
    have hsU : s ∈ U := ⟨h0, by linarith⟩
    have hD0 : finiteDirichletPolynomial a s ≠ 0 := fun h => by
      have := hline s h
      linarith
    have hsum := (hLhas (-s) (by rw [Complex.neg_re]; linarith)).tsum_eq
    rw [hFval s hsU hD0, hΛL s h1,
      show -(Real.log N : ℂ) - expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s) =
        -((Real.log N : ℂ) + expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s)) by ring,
      ← hsum, ← tsum_neg]
    congr 1
    refine tsum_congr fun j => ?_
    rw [exp_cpow_eq_cexp, neg_mul_neg, neg_mul]
  have key := constantTerms_agree
    (b := logWeight (-(Real.log m : ℂ)) cR ℓR) (a := fun i => Real.exp (-logExp ℓR i))
    (c := fun j => -logWeight (Real.log N : ℂ) cL ℓL j) (q := fun j => Real.exp (logExp ℓL j))
    (fun i => Real.exp_pos _)
    (fun i => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (logExp_nonneg hℓR i)))
    (fun j => Real.one_le_exp (logExp_nonneg hℓL j)) hR hL hFd hFb hFR hFL
  -- the two constant terms
  have hRHS : (∑' i : LogIndex (a.support.erase m) ℓR, if Real.exp (-logExp ℓR i) = 1
      then logWeight (-(Real.log m : ℂ)) cR ℓR i else 0) = -(Real.log m : ℂ) := by
    refine (tsum_congr fun i => ?_).trans (tsum_logWeight_zero (-(Real.log m : ℂ)) cR hℓR)
    by_cases h : logExp ℓR i = 0
    · rw [if_pos h, if_pos (by rw [h, neg_zero, Real.exp_zero])]
    · rw [if_neg h, if_neg fun h' => h (neg_eq_zero.mp ((Real.exp_eq_one_iff _).mp h'))]
  have hLHS : (∑' j : LogIndex (a.support.erase N) ℓL, if Real.exp (logExp ℓL j) = 1
      then -logWeight (Real.log N : ℂ) cL ℓL j else 0) = -(Real.log N : ℂ) := by
    refine (tsum_congr fun j => ?_).trans (tsum_neg.trans
      (congrArg Neg.neg (tsum_logWeight_zero (Real.log N : ℂ) cL hℓL)))
    by_cases h : logExp ℓL j = 0
    · rw [if_pos h, if_pos (by rw [h, Real.exp_zero])]
    · rw [if_neg h, if_neg fun h' => h ((Real.exp_eq_one_iff _).mp h'), neg_zero]
  rw [hLHS, hRHS] at key
  have hlog : Real.log N = Real.log m := by exact_mod_cast neg_injective key
  have hNm : (N : ℝ) = m := Real.log_injOn_pos (Set.mem_Ioi.mpr hN0) (Set.mem_Ioi.mpr hm0) hlog
  exact absurd (by exact_mod_cast hNm : N = m) (ne_of_gt hmN)

end GaloisForLFunctions.InfiniteRankPurityTheory
