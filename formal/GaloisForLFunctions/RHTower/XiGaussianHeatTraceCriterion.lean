import GaloisForLFunctions.RHTower.XiGaussianHeatTraceDisproof

/-!
# The polynomial-square Gaussian heat trace is an exact RH criterion

`XiGaussianHeatTraceDisproof` builds the multiplicity-exact trace

`T(P,t) = sum_q (evalRealPolynomial P (w q))^(2 : ℕ) * exp (-t * w q)`,  `w q = xiSpectralPoint q ^ (2 : ℕ)`,

proves it real unconditionally and nonnegative under RH.  This file supplies the converse, so the
family becomes a characterisation rather than a falsification device.

The squared coordinate is the right carrier.  With `rho = 1/2 + b + i g` one has
`Re (w q) = g^(2 : ℕ) - b^(2 : ℕ) > 0` and `Im (w q) = -2 g b`, and the height gap `2 < g^(2 : ℕ)` makes `w q` real
exactly when the copy lies on the critical line.  Moreover `Re w` is a genuine shell coordinate:
`normSq (xiSpectralPoint q) < 2 * Re (w q)` together with reciprocal-square summability makes every
shell `Re w <= R` finite.

Given an off-critical copy `q0`, take `R = Re (w q0) + 1`, let `P` be the real orbit separator of
the finite shell relative to `w q0`, and put `c = P (w q0) ^ (2 : ℕ) <> 0`.  Every shell copy outside the
conjugate pair `{w q0, conj (w q0)}` is annihilated, both members of that pair contribute the same
real part `‖c‖ * exp (-t * Re w0) * cos (arg c - t * Im w0)`, and the copies outside the shell are
bounded by `exp (-(t-1) * R)` times a fixed total.  Since `Im w0 <> 0` the cosine equals `-1` on an
unbounded arithmetic progression of heat times, on which the shell term beats the tail because
`R > Re w0`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## §1 The squared spectral coordinate and its shells -/

/-- The squared centered spectral coordinate has strictly positive real part: the open critical
strip together with the height gap keeps every squared copy in a right half-plane. -/
theorem xiSpectralSq_re_pos (q : XiZeroCopy) :
    0 < (xiSpectralPoint q ^ (2 : ℕ)).re := by
  have h := xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hpos : 0 < Complex.normSq (xiSpectralPoint q) :=
    Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  linarith

/-- The real part of the centered spectral point is the height of the zero. -/
theorem xiSpectralPoint_re_eq (q : XiZeroCopy) :
    (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

/-- Squaring detects the critical line: the squared coordinate is nonreal whenever the centered
coordinate is, because the height never vanishes. -/
theorem xiSpectralSq_im_ne_zero_of_im_ne_zero {q : XiZeroCopy}
    (h : (xiSpectralPoint q).im ≠ 0) :
    (xiSpectralPoint q ^ (2 : ℕ)).im ≠ 0 := by
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [xiSpectralPoint_re_eq]
    intro hzero
    have h2 := xiZeroCopy_two_lt_im_sq q
    rw [hzero] at h2
    norm_num at h2
  have hexp : (xiSpectralPoint q ^ (2 : ℕ)).im =
      2 * ((xiSpectralPoint q).re * (xiSpectralPoint q).im) := by
    rw [pow_two, Complex.mul_im]
    ring
  rw [hexp]
  exact mul_ne_zero two_ne_zero (mul_ne_zero hre h)

/-- **Shells of the squared divisor are finite.**  A copy with `Re (w q) <= R` satisfies
`‖xiSpectralPoint q‖ ^ (2 : ℕ) < 2 R`, so its reciprocal-square weight stays above a fixed positive
level, and a summable nonnegative family exceeds a positive level only finitely often. -/
theorem finite_xiHeatShell (R : ℝ) :
    {q : XiZeroCopy | (xiSpectralPoint q ^ (2 : ℕ)).re ≤ R}.Finite := by
  rcases le_or_gt R 0 with hR | hR
  · apply Set.Finite.subset Set.finite_empty
    intro q hq
    exact absurd (le_trans hq hR) (not_le.mpr (xiSpectralSq_re_pos q))
  · have hcof := xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero
    have hε : (0 : ℝ) < 1 / (2 * R) := by positivity
    have hev := (Metric.tendsto_nhds.mp hcof) _ hε
    rw [Filter.eventually_cofinite] at hev
    apply Set.Finite.subset hev
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    have hnormSq : Complex.normSq (xiSpectralPoint q) < 2 * R := by
      have := xiSpectralPoint_normSq_lt_two_mul_sq_re q
      linarith
    have hpos : 0 < Complex.normSq (xiSpectralPoint q) :=
      Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
    have hge : 1 / (2 * R) ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      rw [Complex.sq_norm]
      exact one_div_le_one_div_of_le hpos hnormSq.le
    intro hlt
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
    linarith

/-! ## §2 Real parts and norms of the heat summands -/

/-- The real part of a Gaussian summand written through the polar data of its coefficient. -/
theorem re_mul_exp_neg_mul (c z : ℂ) (t : ℝ) :
    (c * Complex.exp (-(t : ℂ) * z)).re =
      Real.exp (-(t * z.re)) *
        (c.re * Real.cos (t * z.im) + c.im * Real.sin (t * z.im)) := by
  have hre : (-(t : ℂ) * z).re = -(t * z.re) := by
    simp [Complex.mul_re]
  have him : (-(t : ℂ) * z).im = -(t * z.im) := by
    simp [Complex.mul_im]
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, hre, him,
    Real.cos_neg, Real.sin_neg]
  ring

/-- Both members of a conjugate pair contribute the same real part, because a real polynomial and
the Gaussian multiplier both commute with conjugation. -/
theorem re_heatSummand_conj (P : Polynomial ℝ) (t : ℝ) (z : ℂ) :
    (evalRealPolynomial P ((starRingEnd ℂ) z) ^ (2 : ℕ) *
        Complex.exp (-(t : ℂ) * (starRingEnd ℂ) z)).re =
      (evalRealPolynomial P z ^ (2 : ℕ) * Complex.exp (-(t : ℂ) * z)).re := by
  have hconj : (-(t : ℂ) * (starRingEnd ℂ) z) = (starRingEnd ℂ) (-(t : ℂ) * z) := by
    simp [Complex.conj_ofReal]
  rw [evalRealPolynomial_conj, hconj, Complex.exp_conj, ← map_pow, ← map_mul,
    Complex.conj_re]

/-- The norm of one polynomial-square Gaussian summand. -/
theorem norm_xiPolynomialGaussianHeatTerm (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm P t q‖ =
      ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
        Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re)) := by
  rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, norm_mul, norm_pow,
    Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- Absolute summability of the polynomial-square Gaussian summands. -/
theorem summable_norm_xiPolynomialGaussianHeatTerm {t : ℝ} (ht : 0 < t)
    (P : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy => ‖xiPolynomialGaussianHeatTerm P t q‖) :=
  summable_norm_iff.mpr (summable_xiPolynomialGaussianHeatTerm ht P)

/-! ## §3 The converse: one filtered trace detects an off-critical copy -/

/-- **An off-critical copy is detected by one filtered Gaussian trace.**  The real orbit separator
of the finite shell annihilates every competing copy inside the shell, the isolated conjugate pair
rotates with the heat time, and outside the shell the Gaussian damping is strictly stronger. -/
theorem exists_neg_xiPolynomialGaussianHeatTraceReal_of_spectralSq_im_pos
    {q₀ : XiZeroCopy} (h0 : 0 < (xiSpectralPoint q₀ ^ (2 : ℕ)).im) :
    ∃ (P : Polynomial ℝ) (t : ℝ), 0 < t ∧
      xiPolynomialGaussianHeatTraceReal P t < 0 := by
  classical
  set z₀ : ℂ := xiSpectralPoint q₀ ^ (2 : ℕ) with hz₀
  have hA : 0 < z₀.re := by rw [hz₀]; exact xiSpectralSq_re_pos q₀
  have hB : 0 < z₀.im := h0
  set R : ℝ := z₀.re + 1 with hRdef
  have hfin := finite_xiHeatShell R
  set S : Finset XiZeroCopy := hfin.toFinset with hSdef
  have hmemS : ∀ q : XiZeroCopy, q ∈ S ↔ (xiSpectralPoint q ^ (2 : ℕ)).re ≤ R := by
    intro q
    rw [hSdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hq₀S : q₀ ∈ S := by
    rw [hmemS, ← hz₀, hRdef]
    linarith
  set FS : Finset ℂ := S.image (fun q => xiSpectralPoint q ^ (2 : ℕ)) with hFSdef
  set P : Polynomial ℝ := realOrbitSeparator FS z₀ with hPdef
  set c : ℂ := evalRealPolynomial P z₀ ^ (2 : ℕ) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact pow_ne_zero _ evalRealOrbitSeparator_ne_zero
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set S₁ : Finset XiZeroCopy :=
    S.filter (fun q => xiSpectralPoint q ^ (2 : ℕ) = z₀ ∨
      xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) z₀) with hS₁def
  have hq₀S₁ : q₀ ∈ S₁ := by
    rw [hS₁def, Finset.mem_filter]
    exact ⟨hq₀S, Or.inl hz₀.symm⟩
  have hcard : (1 : ℝ) ≤ (S₁.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨q₀, hq₀S₁⟩
  have hcardpos : (0 : ℝ) < (S₁.card : ℝ) := lt_of_lt_of_le one_pos hcard
  -- the fixed tail total, measured at heat time one
  have hnorm1 := summable_norm_xiPolynomialGaussianHeatTerm (t := 1) one_pos P
  set C : ℝ := ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm P 1 q‖ with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef]
    exact tsum_nonneg fun q => norm_nonneg _
  set K : ℝ := Real.exp R * C / ((S₁.card : ℝ) * ‖c‖) with hKdef
  -- choose the heat time: large, and with the shell phase exactly at `-1`
  obtain ⟨m, hm⟩ :=
    exists_nat_gt ((max 1 K * z₀.im - c.arg - Real.pi) / (2 * Real.pi))
  set t : ℝ := (c.arg + Real.pi + 2 * Real.pi * (m : ℝ)) / z₀.im with htdef
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have htbig : max 1 K < t := by
    rw [htdef, lt_div_iff₀ hB]
    rw [div_lt_iff₀ h2pi] at hm
    linarith
  have ht1 : (1 : ℝ) ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) htbig)
  have htK : K < t := lt_of_le_of_lt (le_max_right _ _) htbig
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have hphase : t * z₀.im = c.arg + Real.pi + 2 * Real.pi * (m : ℝ) := by
    rw [htdef]
    field_simp
  have hcosval :
      c.re * Real.cos (t * z₀.im) + c.im * Real.sin (t * z₀.im) = -‖c‖ := by
    have hcre : c.re = ‖c‖ * Real.cos c.arg := by
      rw [Complex.cos_arg hc]
      field_simp
    have hcim : c.im = ‖c‖ * Real.sin c.arg := by
      rw [Complex.sin_arg]
      field_simp
    have hcos : Real.cos (c.arg - t * z₀.im) = -1 := by
      rw [hphase]
      have hrw : c.arg - (c.arg + Real.pi + 2 * Real.pi * (m : ℝ)) =
          -Real.pi + (((-(m : ℤ) : ℤ)) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [hrw, Real.cos_add_int_mul_two_pi, Real.cos_neg, Real.cos_pi]
    calc
      c.re * Real.cos (t * z₀.im) + c.im * Real.sin (t * z₀.im)
          = ‖c‖ * (Real.cos c.arg * Real.cos (t * z₀.im) +
              Real.sin c.arg * Real.sin (t * z₀.im)) := by
            rw [hcre, hcim]; ring
      _ = ‖c‖ * Real.cos (c.arg - t * z₀.im) := by rw [Real.cos_sub]
      _ = -‖c‖ := by rw [hcos]; ring
  -- the isolated conjugate pair contributes a fixed strictly negative real part
  have hpairRe : ∀ q ∈ S₁,
      (xiPolynomialGaussianHeatTerm P t q).re =
        -‖c‖ * Real.exp (-(t * z₀.re)) := by
    intro q hq
    have hq' := (Finset.mem_filter.mp (by rwa [hS₁def] at hq)).2
    have hbase :
        (c * Complex.exp (-(t : ℂ) * z₀)).re = -‖c‖ * Real.exp (-(t * z₀.re)) := by
      rw [re_mul_exp_neg_mul, hcosval]
      ring
    rcases hq' with heq | heq
    · rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, heq, ← hcdef, hbase]
    · rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, heq,
        re_heatSummand_conj, ← hcdef, hbase]
  -- every other shell copy is annihilated by the separator
  have hvanish : ∀ q ∈ S.filter (fun q => ¬ (xiSpectralPoint q ^ (2 : ℕ) = z₀ ∨
      xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) z₀)),
      (xiPolynomialGaussianHeatTerm P t q).re = 0 := by
    intro q hq
    obtain ⟨hqS, hqne⟩ := Finset.mem_filter.mp hq
    push Not at hqne
    have hmemFS : xiSpectralPoint q ^ (2 : ℕ) ∈ FS := by
      rw [hFSdef]
      exact Finset.mem_image_of_mem _ hqS
    have hPzero : evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) = 0 := by
      rw [hPdef]
      exact evalRealOrbitSeparator_eq_zero hmemFS hqne.1 hqne.2
    rw [xiPolynomialGaussianHeatTerm, hPzero]
    simp
  -- the shell sum
  have hSsum : ∑ q ∈ S, (xiPolynomialGaussianHeatTerm P t q).re =
      (S₁.card : ℝ) * (-‖c‖ * Real.exp (-(t * z₀.re))) := by
    rw [← Finset.sum_filter_add_sum_filter_not S
      (fun q => xiSpectralPoint q ^ (2 : ℕ) = z₀ ∨
        xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) z₀)
      (fun q => (xiPolynomialGaussianHeatTerm P t q).re)]
    rw [Finset.sum_eq_zero hvanish, add_zero, ← hS₁def]
    rw [Finset.sum_congr rfl hpairRe, Finset.sum_const, nsmul_eq_mul]
  -- the tail outside the shell
  have hsumt := summable_xiPolynomialGaussianHeatTerm htpos P
  have hnormt := summable_norm_xiPolynomialGaussianHeatTerm htpos P
  have htailnorm :
      ‖∑' q : ↑((S : Set XiZeroCopy))ᶜ, xiPolynomialGaussianHeatTerm P t q‖ ≤
        Real.exp R * C * Real.exp (-(t * R)) := by
    have hsub : Summable
        (fun q : ↑((S : Set XiZeroCopy))ᶜ =>
          ‖xiPolynomialGaussianHeatTerm P t q‖) := hnormt.subtype _
    have hsub1 : Summable
        (fun q : ↑((S : Set XiZeroCopy))ᶜ =>
          ‖xiPolynomialGaussianHeatTerm P 1 q‖) := hnorm1.subtype _
    have hbound : ∀ q : ↑((S : Set XiZeroCopy))ᶜ,
        ‖xiPolynomialGaussianHeatTerm P t (q : XiZeroCopy)‖ ≤
          Real.exp R * Real.exp (-(t * R)) *
            ‖xiPolynomialGaussianHeatTerm P 1 (q : XiZeroCopy)‖ := by
      rintro ⟨q, hq⟩
      have hqR : R < (xiSpectralPoint q ^ (2 : ℕ)).re := by
        have : q ∉ S := by simpa using hq
        rw [hmemS] at this
        exact not_le.mp this
      rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
      have hexp : Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re)) ≤
          Real.exp R * Real.exp (-(t * R)) *
            Real.exp (-(1 * (xiSpectralPoint q ^ (2 : ℕ)).re)) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        nlinarith [hqR, ht1]
      have hsq : (0 : ℝ) ≤ ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) := by
        positivity
      calc
        ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
            Real.exp (-(t * (xiSpectralPoint q ^ (2 : ℕ)).re))
            ≤ ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
              (Real.exp R * Real.exp (-(t * R)) *
                Real.exp (-(1 * (xiSpectralPoint q ^ (2 : ℕ)).re))) :=
              mul_le_mul_of_nonneg_left hexp hsq
        _ = Real.exp R * Real.exp (-(t * R)) *
              (‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
                Real.exp (-(1 * (xiSpectralPoint q ^ (2 : ℕ)).re))) := by ring
    calc
      ‖∑' q : ↑((S : Set XiZeroCopy))ᶜ, xiPolynomialGaussianHeatTerm P t q‖
          ≤ ∑' q : ↑((S : Set XiZeroCopy))ᶜ,
              ‖xiPolynomialGaussianHeatTerm P t (q : XiZeroCopy)‖ :=
            norm_tsum_le_tsum_norm hsub
      _ ≤ ∑' q : ↑((S : Set XiZeroCopy))ᶜ,
              Real.exp R * Real.exp (-(t * R)) *
                ‖xiPolynomialGaussianHeatTerm P 1 (q : XiZeroCopy)‖ :=
            hsub.tsum_le_tsum hbound (hsub1.mul_left _)
      _ = Real.exp R * Real.exp (-(t * R)) *
              ∑' q : ↑((S : Set XiZeroCopy))ᶜ,
                ‖xiPolynomialGaussianHeatTerm P 1 (q : XiZeroCopy)‖ :=
            hsub1.tsum_mul_left _
      _ ≤ Real.exp R * Real.exp (-(t * R)) * C := by
            have hle : ∑' q : ↑((S : Set XiZeroCopy))ᶜ,
                ‖xiPolynomialGaussianHeatTerm P 1 (q : XiZeroCopy)‖ ≤ C := by
              have hsplit := hnorm1.sum_add_tsum_compl (s := S)
              have hnn : 0 ≤ ∑ q ∈ S, ‖xiPolynomialGaussianHeatTerm P 1 q‖ :=
                Finset.sum_nonneg fun q _ => norm_nonneg _
              rw [hCdef, ← hsplit]
              linarith
            exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = Real.exp R * C * Real.exp (-(t * R)) := by ring
  -- assemble
  refine ⟨P, t, htpos, ?_⟩
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
    ← hsumt.sum_add_tsum_compl (s := S), Complex.add_re, Complex.re_sum, hSsum]
  have htail :
      (∑' q : ↑((S : Set XiZeroCopy))ᶜ, xiPolynomialGaussianHeatTerm P t q).re ≤
        Real.exp R * C * Real.exp (-(t * R)) :=
    le_trans (Complex.re_le_norm _) htailnorm
  have hkey : Real.exp R * C * Real.exp (-(t * R)) <
      (S₁.card : ℝ) * (‖c‖ * Real.exp (-(t * z₀.re))) := by
    have hexpt : t < Real.exp t := lt_of_lt_of_le (by linarith) (Real.add_one_le_exp t)
    have hKt : K < Real.exp t := lt_trans htK hexpt
    have hprod : Real.exp R * C < Real.exp t * ((S₁.card : ℝ) * ‖c‖) := by
      rw [hKdef] at hKt
      rw [div_lt_iff₀ (mul_pos hcardpos hcn)] at hKt
      linarith
    have hfac : Real.exp t * Real.exp (-(t * R)) = Real.exp (-(t * z₀.re)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hRdef]
      ring
    calc
      Real.exp R * C * Real.exp (-(t * R))
          < (Real.exp t * ((S₁.card : ℝ) * ‖c‖)) * Real.exp (-(t * R)) := by
            exact mul_lt_mul_of_pos_right hprod (Real.exp_pos _)
      _ = (S₁.card : ℝ) * ‖c‖ * (Real.exp t * Real.exp (-(t * R))) := by ring
      _ = (S₁.card : ℝ) * (‖c‖ * Real.exp (-(t * z₀.re))) := by
            rw [hfac]; ring
  nlinarith [htail, hkey, hcardpos]

/-- Failure of RH produces an off-critical copy with strictly positive squared imaginary part. -/
theorem exists_spectralSq_im_pos_of_not_riemannHypothesis
    (h : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 0 < (xiSpectralPoint q ^ (2 : ℕ)).im := by
  rw [rh_iff_xi_ne_zero_right] at h
  push Not at h
  obtain ⟨s, hs, hzero⟩ := h
  have hre : 1 / 2 < s.re := mem_rightHalf.mp hs
  set pt : ℂ := (s - 1 / 2) * (-Complex.I) with hpt
  have hXpt : XiC pt = 0 := by
    show xi ((1 / 2 : ℂ) + pt * Complex.I) = 0
    have harg : (1 / 2 : ℂ) + pt * Complex.I = s := by
      rw [hpt, show ((s - 1 / 2) * (-Complex.I) * Complex.I) =
        -(Complex.I * Complex.I) * (s - 1 / 2) from by ring, Complex.I_mul_I]
      ring
    rw [harg]
    exact hzero
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy pt).mp hXpt
  have hqim : (xiSpectralPoint q).im ≠ 0 := by
    rw [hq, hpt]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.sub_re, Complex.sub_im]
    intro hcontra
    norm_num at hcontra
    linarith
  have hne := xiSpectralSq_im_ne_zero_of_im_ne_zero hqim
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [xiSpectralPoint_lineConj, ← map_pow, Complex.conj_im]
    linarith
  · exact ⟨q, hgt⟩

/-- **RH is exactly nonnegativity of every polynomial-square Gaussian heat trace.**  The forward
direction is the divisor being real; the converse isolates one off-critical conjugate pair with the
real orbit separator of a finite shell and rotates it into the negative half-line by choosing the
heat time. -/
theorem riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg :
    RiemannHypothesis ↔
      ∀ (P : Polynomial ℝ) (t : ℝ), 0 < t →
        0 ≤ xiPolynomialGaussianHeatTraceReal P t := by
  constructor
  · intro hRH P t ht
    exact xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis hRH P ht
  · intro hpos
    by_contra hRH
    obtain ⟨q₀, hq₀⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    obtain ⟨P, t, ht, hneg⟩ :=
      exists_neg_xiPolynomialGaussianHeatTraceReal_of_spectralSq_im_pos hq₀
    exact absurd (hpos P t ht) (not_le.mpr hneg)

end

end RHTower
