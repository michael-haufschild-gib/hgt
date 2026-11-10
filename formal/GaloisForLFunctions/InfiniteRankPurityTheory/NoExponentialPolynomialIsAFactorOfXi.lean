import GaloisForLFunctions.InfiniteRankPurityTheory.AFactorWithADirichletSeriesIsPure
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius
import GaloisForLFunctions.InfiniteRankPurityTheory.TheJumpLawSurvivesFinitelyManyPolesOnTheLine
import GaloisForLFunctions.InfiniteRankPurityTheory.AZeroFreeExponentialPolynomialIsBoundedBelow
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# No exponential polynomial is a factor of ξ

An exponential polynomial `D(s) = Σ_k a_k e^{λ_k s}` with distinct real frequencies, nonzero
coefficients and at least two terms has infinitely many zeros that are not zeros of `ξ`
(`infinite_zeros_not_xi_zeros`). The frequencies are arbitrary real numbers; Dirichlet polynomials
`Σ a_n n^{−s}` are the case `λ = −log n` (`infinite_zeros_not_xi_zeros_dirichletPolynomial`,
`exists_zero_not_xi_zero`). So `D` is a factor of `ξ` in no sense that allows finitely many
exceptions: no quotient of `D` by a polynomial divides `ξ`.

Suppose only finitely many zeros of `D` are not zeros of `ξ`.

* *The zeros lie on the critical line.* `D` is almost periodic on vertical strips, so a zero recurs
  along a relatively dense thick set of heights. A zero in the open strip off the line then gives
  zeros at arbitrarily large heights at which `ζ` does not vanish, because the heights at which `ζ`
  has a zero near that vertical line have density zero
  (`infinite_zeros_not_xi_zeros_of_interior`). A zero outside the open strip recurs within distance
  `¼` of its vertical line, where a zero of `ξ` would be an interior zero off the line
  (`infinite_zeros_not_xi_zeros_of_re_ne_half`).
* Let `P` be the finite set of zeros of `D` that are not zeros of `ξ`. Then
  `−(ζ/s) (D'/D) Π_{p ∈ P} (s − p)` is holomorphic on the strip
  (`exists_differentiableOn_deriv_mul_div`), and `F = −(ζ/s) D'/D − Σ_p r_p/(s − p)` is holomorphic
  there for suitable residues (`exists_principalParts`).
* Right of the line `D = a_m e^{λ_m s} P(s)` with `λ_m` the highest frequency, left of it
  `D = a_N e^{λ_N s} Q(−s)` with `λ_N` the lowest, and the exponential polynomials `P`, `Q` have no
  zeros there. Their logarithmic derivatives expand absolutely up to the line
  (`hasSum_logWeight_of_zeroFree`): `D'/D = λ_m + Σ b_i a_i^s`, `a_i < 1`, on the right and
  `D'/D = λ_N + Σ c_j q_j^s`, `q_j > 1`, on the left.
* `F` is bounded near the line: on the lines `Re s = ¼, ¾` because `P` and `Q` are bounded below,
  in between by the maximum principle between heights at which `‖D‖` is bounded below
  (`exists_good_heights_of_almostPeriodic`, `norm_le_of_good_heights`); such heights stay away from
  `P` because `D` is Lipschitz on the strip.
* By `constantTerms_agree_of_poles` the two constant terms agree: `λ_N = λ_m`.
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

/-! ### A zero off the line -/

/-- A set of complex numbers with members of arbitrarily large height is infinite. -/
theorem infinite_of_forall_exists_im_gt {A : Set ℂ} (h : ∀ Y : ℝ, ∃ w ∈ A, Y < w.im) :
    A.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨w, hw, hlt⟩ := h M
  exact absurd (hM (mem_image_of_mem _ hw)) (not_le.mpr hlt)

/-- An entire function that is not identically zero does not vanish identically on the critical
line. -/
theorem exists_ne_zero_on_line_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hne : ∃ z₁ : ℂ, F z₁ ≠ 0) : ∃ t : ℝ, F ((1 / 2 : ℂ) + t * I) ≠ 0 := by
  by_contra hcon
  have hall : ∀ t : ℝ, F ((1 / 2 : ℂ) + t * I) = 0 := fun t => by
    by_contra h
    exact hcon ⟨t, h⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have han : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 / 2 : ℂ), F z = 0 := by
    rw [frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.mp hU
    refine ⟨(1 / 2 : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, hεU ⟨?_, ?_⟩, hall _⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
  exact hz₁ (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _)
    hfreq (mem_univ z₁))

/-- **An interior zero off the line gives infinitely many zeros outside the zeros of `ξ`.** Let `F`
be entire, not identically zero and almost periodic on vertical strips. A zero in the open strip
off the critical line recurs on a set of heights of positive lower density, and the heights at
which `ζ` has a zero near that vertical line have density zero. -/
theorem infinite_zeros_not_xi_zeros_of_interior {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFne : ∃ z₁ : ℂ, F z₁ ≠ 0) (hAP : ∀ σ R : ℝ, IsStripAlmostPeriodicOn F σ R) {ρ₀ : ℂ}
    (hρ : F ρ₀ = 0) (h0 : 0 < ρ₀.re) (h1 : ρ₀.re < 1) (hne : ρ₀.re ≠ 1 / 2) :
    {z : ℂ | F z = 0 ∧ xi z ≠ 0}.Infinite := by
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero h0 h1 hne
  obtain ⟨z₁, hz₁⟩ := hFne
  have hρx : min ρ₀.re z₁.re - 1 < ρ₀.re := by linarith [min_le_left ρ₀.re z₁.re]
  have hz₁x : min ρ₀.re z₁.re - 1 < z₁.re := by linarith [min_le_right ρ₀.re z₁.re]
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts_of_almostPeriodic
    hF.differentiableOn ⟨z₁, hz₁x, hz₁⟩ hρx hρ one_pos (hAP ρ₀.re 1) hr
  set E : Set ℝ := {t : ℝ | ∃ z ∈ ball ρ₀ r, F (z + t * I) = 0} with hE
  have hthick' : ∀ a : ℝ, ∃ τ ∈ Icc a (a + L), Ioo (τ - d) (τ + d) ⊆ E := by
    intro a
    obtain ⟨τ, hτ, hsub⟩ := hthick a
    refine ⟨τ, hτ, fun t ht => ?_⟩
    obtain ⟨z, hz, -, hz0⟩ := hsub ht
    exact ⟨z, hz, hz0⟩
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  set c : ℝ := d / (L + 2 * d) with hc
  have hc0 : 0 < c := by positivity
  have hup := hdens (c / 4) (by positivity)
  refine infinite_of_forall_exists_im_gt fun Y => ?_
  -- a shift beyond `Y'` that carries a zero of `F` and no zero of `ζ` into the disc
  set Y' : ℝ := max (Y - ρ₀.im + r) 0 with hY'
  have hY'0 : 0 ≤ Y' := le_max_right _ _
  obtain ⟨T, hT1, hT2, hT3⟩ := (hlow.and (hup.and (eventually_gt_atTop (4 * Y' / c)))).exists
  have hT0 : 0 < T :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg (by norm_num) hY'0) hc0.le) hT3
  have hex : ∃ t ∈ E ∩ Icc 0 T, t ∉ zetaZeroShiftSet ρ₀ r ∧ Y' < t := by
    by_contra hcon
    push Not at hcon
    have hsub : E ∩ Icc 0 T ⊆ (zetaZeroShiftSet ρ₀ r ∩ Icc 0 T) ∪ Icc 0 Y' := by
      intro t ht
      by_cases hZ : t ∈ zetaZeroShiftSet ρ₀ r
      · exact Or.inl ⟨hZ, ht.2⟩
      · exact Or.inr ⟨ht.2.1, hcon t ht hZ⟩
    have h := (hT1.trans (measure_mono hsub)).trans (measure_union_le _ _)
    rw [Real.volume_Icc, sub_zero] at h
    have h' := h.trans (add_le_add hT2 le_rfl)
    have hcT : 0 ≤ c / 4 * T := mul_nonneg (by positivity) hT0.le
    rw [← ENNReal.ofReal_add hcT hY'0, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h'
    rw [div_lt_iff₀ hc0] at hT3
    linarith [mul_pos hc0 hT0]
  obtain ⟨t, ⟨⟨z, hz, hz0⟩, -⟩, htZ, htY⟩ := hex
  refine ⟨z + t * I, ⟨hz0, fun hxi => htZ ⟨z, hz,
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1⟩⟩, ?_⟩
  have him : (z + t * I).im = z.im + t := by simp
  have hzi := abs_lt.mp ((abs_im_le_norm (z - ρ₀)).trans_lt (mem_ball_iff_norm.mp hz))
  rw [sub_im] at hzi
  rw [him]
  linarith [le_max_left (Y - ρ₀.im + r) 0, hzi.1]

/-- **A zero off the line gives infinitely many zeros outside the zeros of `ξ`.** Outside the open
strip a zero recurs at all heights within `¼` of its vertical line; there a zero of `ξ` would be
an interior zero off the line. -/
theorem infinite_zeros_not_xi_zeros_of_re_ne_half {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFne : ∃ z₁ : ℂ, F z₁ ≠ 0) (hAP : ∀ σ R : ℝ, IsStripAlmostPeriodicOn F σ R) {ρ₀ : ℂ}
    (hρ : F ρ₀ = 0) (hne : ρ₀.re ≠ 1 / 2) : {z : ℂ | F z = 0 ∧ xi z ≠ 0}.Infinite := by
  by_cases hin : 0 < ρ₀.re ∧ ρ₀.re < 1
  · exact infinite_zeros_not_xi_zeros_of_interior hF hFne hAP hρ hin.1 hin.2 hne
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hno : ∀ w : ℂ, F w = 0 → 0 < w.re → w.re < 1 → w.re = 1 / 2 := fun w hw h0 h1 => by
    by_contra h
    exact (infinite_zeros_not_xi_zeros_of_interior hF hFne hAP hw h0 h1 h) hfin
  obtain ⟨z₁, hz₁⟩ := hFne
  have hρx : min ρ₀.re z₁.re - 1 < ρ₀.re := by linarith [min_le_left ρ₀.re z₁.re]
  have hz₁x : min ρ₀.re z₁.re - 1 < z₁.re := by linarith [min_le_right ρ₀.re z₁.re]
  obtain ⟨L, -, d, hd, hthick⟩ := exists_thick_zero_shifts_of_almostPeriodic
    hF.differentiableOn ⟨z₁, hz₁x, hz₁⟩ hρx hρ one_pos (hAP ρ₀.re 1)
    (show (0 : ℝ) < 1 / 4 by norm_num)
  refine (infinite_of_forall_exists_im_gt fun Y => ?_) hfin
  obtain ⟨τ, hτ, hsub⟩ := hthick (Y - ρ₀.im + 1)
  obtain ⟨z, hz, -, hz0⟩ := hsub (show τ ∈ Ioo (τ - d) (τ + d) from ⟨by linarith, by linarith⟩)
  have hzr := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt (mem_ball_iff_norm.mp hz))
  have hzi := abs_lt.mp ((abs_im_le_norm (z - ρ₀)).trans_lt (mem_ball_iff_norm.mp hz))
  rw [sub_re] at hzr
  rw [sub_im] at hzi
  have hre : (z + τ * I).re = z.re := by simp
  have him : (z + τ * I).im = z.im + τ := by simp
  refine ⟨z + τ * I, ⟨hz0, fun hxi => ?_⟩, by rw [him]; linarith [hτ.1, hzi.1]⟩
  have hx0 := re_pos_of_xi_eq_zero hxi
  have hx1 := re_lt_one_of_xi_eq_zero hxi
  have hhalf := hno _ hz0 hx0 hx1
  rw [hre] at hhalf
  rw [not_and_or, not_lt, not_lt] at hin
  rcases hin with h | h <;> linarith [hzr.1, hzr.2]

/-! ### Exponential polynomials -/

/-- **No exponential polynomial is a factor of `ξ`.** An exponential polynomial
`Σ_k a_k e^{λ_k s}` with distinct real frequencies, nonzero coefficients and at least two terms has
infinitely many zeros that are not zeros of `ξ`. -/
theorem infinite_zeros_not_xi_zeros {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ)
    (hinj : Function.Injective lam) (ha : ∀ k, a k ≠ 0) {k₁ k₂ : Fin n} (hne : k₁ ≠ k₂) :
    {z : ℂ | expSum a lam z = 0 ∧ xi z ≠ 0}.Infinite := by
  classical
  by_contra hfin
  rw [Set.not_infinite] at hfin
  set D : ℂ → ℂ := expSum a lam with hD
  have hDd : Differentiable ℂ D := differentiable_expSum a lam
  have hAP : ∀ σ R : ℝ, IsStripAlmostPeriodicOn D σ R := fun σ R =>
    isStripAlmostPeriodic_expSum a lam σ (R + 1) R (by linarith)
  -- the highest and the lowest frequency
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ lam ⟨k₁, Finset.mem_univ _⟩
  obtain ⟨N, -, hN⟩ := Finset.exists_min_image Finset.univ lam ⟨k₁, Finset.mem_univ _⟩
  have hmN : lam N < lam m := by
    rcases lt_or_eq_of_le ((hN k₁ (Finset.mem_univ _)).trans (hm k₁ (Finset.mem_univ _)))
      with h | h
    · exact h
    · exfalso
      have h1 : lam k₁ = lam m := le_antisymm (hm k₁ (Finset.mem_univ _))
        (by have := hN k₁ (Finset.mem_univ _); linarith)
      have h2 : lam k₂ = lam m := le_antisymm (hm k₂ (Finset.mem_univ _))
        (by have := hN k₂ (Finset.mem_univ _); linarith)
      exact hne (hinj (h1.trans h2.symm))
  set LM : ℝ := -lam m with hLM
  set LN : ℝ := -lam N with hLN
  have hDexp : ∀ s : ℂ, D s =
      ∑ k ∈ (Finset.univ : Finset (Fin n)), a k * cexp (-((-lam k : ℝ) : ℂ) * s) := fun s => by
    show (∑ k, a k * cexp ((lam k : ℂ) * s)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_neg, neg_neg]
  -- right of the line: normalization at the highest frequency
  set cR : ↥((Finset.univ : Finset (Fin n)).erase m) → ℂ := fun k => a k / a m with hcR
  set ℓR : ↥((Finset.univ : Finset (Fin n)).erase m) → ℝ := fun k => -lam k - LM with hℓRdef
  have hℓR : ∀ k, 0 < ℓR k := by
    intro k
    have hk := Finset.mem_erase.mp k.2
    have hlt : lam k < lam m :=
      lt_of_le_of_ne (hm k (Finset.mem_univ _)) fun h => hk.1 (hinj h)
    show 0 < -lam k - -lam m
    linarith
  have hDR : ∀ s : ℂ, D s = a m * cexp (-(LM : ℂ) * s) * expPoly cR ℓR s := fun s => by
    rw [hDexp, sum_exp_eq_expPoly Finset.univ a (fun k => -lam k) (Finset.mem_univ m) (ha m)]
  -- left of the line: normalization at the lowest frequency
  set cL : ↥((Finset.univ : Finset (Fin n)).erase N) → ℂ := fun k => a k / a N with hcL
  set ℓL : ↥((Finset.univ : Finset (Fin n)).erase N) → ℝ := fun k => LN - -lam k with hℓLdef
  have hℓL : ∀ k, 0 < ℓL k := by
    intro k
    have hk := Finset.mem_erase.mp k.2
    have hlt : lam N < lam k :=
      lt_of_le_of_ne (hN k (Finset.mem_univ _)) fun h => hk.1 (hinj h.symm)
    show 0 < -lam N - -lam k
    linarith
  have hDL : ∀ s : ℂ, D s = a N * cexp (-(LN : ℂ) * s) * expPoly cL ℓL (-s) := fun s => by
    rw [hDexp, sum_exp_eq_expPoly_neg Finset.univ a (fun k => -lam k) (Finset.mem_univ N) (ha N)]
  -- `D` is not identically zero
  have hDne : ∃ z₁ : ℂ, D z₁ ≠ 0 := by
    obtain ⟨C₀, -, -, hfar⟩ := exists_far_bound_expPoly cR hℓR
    refine ⟨(C₀ : ℂ), ?_⟩
    have h := hfar (fun _ => 1) (fun _ => by simp) (C₀ : ℂ) (by simp)
    simp only [mul_one] at h
    have hP : expPoly cR ℓR (C₀ : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h)
    rw [hDR]
    exact mul_ne_zero (mul_ne_zero (ha m) (Complex.exp_ne_zero _)) hP
  have hord : ∀ z : ℂ, analyticOrderAt D z ≠ ⊤ := fun z htop => by
    rw [analyticOrderAt_eq_top] at htop
    obtain ⟨z₁, hz₁⟩ := hDne
    exact hz₁ ((hDd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) htop (mem_univ z₁))
  -- the zeros lie on the line; `P` is the finite set of those that are not zeros of `ξ`
  have hline : ∀ z : ℂ, D z = 0 → z.re = 1 / 2 := fun z hz => by
    by_contra hre
    exact (infinite_zeros_not_xi_zeros_of_re_ne_half hDd hDne hAP hz hre) hfin
  set P : Finset ℂ := hfin.toFinset with hPdef
  have hPmem : ∀ z : ℂ, z ∈ P ↔ D z = 0 ∧ xi z ≠ 0 := fun z => by
    rw [hPdef, Set.Finite.mem_toFinset]
    rfl
  have hPline : ∀ p ∈ P, p.re = 1 / 2 := fun p hp => hline p ((hPmem p).mp hp).1
  have hζ : ∀ z : ℂ, D z = 0 → z ∉ P → riemannZeta z = 0 := fun z hz hzP => by
    have hxi : xi z = 0 := by
      by_contra h
      exact hzP ((hPmem z).mpr ⟨hz, h⟩)
    exact (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
  have hPR : ∀ w : ℂ, 1 / 2 < w.re → expPoly cR ℓR w ≠ 0 := fun w hw h0 => by
    have hD0 : D w = 0 := by rw [hDR, h0, mul_zero]
    have := hline w hD0
    linarith
  have hPL : ∀ w : ℂ, -(1 / 2) < w.re → expPoly cL ℓL w ≠ 0 := fun w hw h0 => by
    have hD0 : D (-w) = 0 := by rw [hDL, neg_neg, h0, mul_zero]
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
  obtain ⟨hRsum, hRhas⟩ := hasSum_logWeight_of_zeroFree (-(LM : ℂ)) cR hℓR hPR
  obtain ⟨hLsum, hLhas⟩ := hasSum_logWeight_of_zeroFree (LN : ℂ) cL hℓL hPL
  have hΛR : ∀ s : ℂ, 1 / 2 < s.re →
      deriv D s / D s = -(LM : ℂ) + expPolyDeriv cR ℓR s / expPoly cR ℓR s := by
    intro s hs
    have h := logDeriv_exp_mul (A := a m) (lam := (LM : ℂ)) (ha m)
      (hasDerivAt_expPoly cR ℓR s) (hPR s hs)
    have hfun : D = fun z => a m * cexp (-(LM : ℂ) * z) * expPoly cR ℓR z := funext hDR
    rw [hfun]
    exact h
  have hΛL : ∀ s : ℂ, s.re < 1 / 2 →
      deriv D s / D s = -(LN : ℂ) - expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s) := by
    intro s hs
    have h := logDeriv_exp_mul_neg (A := a N) (lam := (LN : ℂ)) (ha N)
      (hasDerivAt_expPoly cL ℓL (-s)) (hPL (-s) (by rw [Complex.neg_re]; linarith))
    have hfun : D = fun z => a N * cexp (-(LN : ℂ) * z) * expPoly cL ℓL (-z) := funext hDL
    rw [hfun]
    exact h
  -- the derivative is bounded on the strip `0 ≤ Re z ≤ 1`
  have hDderiv : ∀ z : ℂ, HasDerivAt D (∑ k, a k * (cexp ((lam k : ℂ) * z) * (lam k : ℂ))) z := by
    intro z
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => cexp ((lam k : ℂ) * w))
        (cexp ((lam k : ℂ) * z) * (lam k : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (lam k : ℂ)).cexp
    exact h1.const_mul (a k)
  set CD : ℝ := ∑ k, ‖a k‖ * (Real.exp |lam k| * |lam k|) with hCD
  have hCD0 : 0 ≤ CD := Finset.sum_nonneg fun k _ => by positivity
  have hderiv_le : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖deriv D z‖ ≤ CD := by
    intro z h0 h1
    rw [(hDderiv z).deriv]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Complex.re_ofReal_mul]
    have hle : lam k * z.re ≤ |lam k| := by
      calc lam k * z.re ≤ |lam k * z.re| := le_abs_self _
        _ = |lam k| * |z.re| := abs_mul _ _
        _ ≤ |lam k| * 1 :=
          mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg h0]; exact h1) (abs_nonneg _)
        _ = |lam k| := mul_one _
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle) (abs_nonneg _)) (norm_nonneg _)
  -- the function `F = −(ζ/s) D'/D − Σ_p r_p/(s − p)`
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  set g : ℂ → ℂ := fun s => -(riemannZeta s / s) * ∏ p ∈ P, (s - p) with hg
  have hprodd : Differentiable ℂ fun s : ℂ => ∏ p ∈ P, (s - p) := by fun_prop
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
    exact ((((differentiableAt_riemannZeta hs1).div differentiableAt_id hs0).neg).mul
      (hprodd s)).differentiableWithinAt
  have hzero : ∀ z ∈ U, D z = 0 → g z = 0 := fun z _ hz => by
    show -(riemannZeta z / z) * ∏ p ∈ P, (z - p) = 0
    by_cases hzP : z ∈ P
    · rw [Finset.prod_eq_zero hzP (sub_self z), mul_zero]
    · rw [hζ z hz hzP, zero_div, neg_zero, zero_mul]
  obtain ⟨H, hHd, hHeq⟩ := exists_differentiableOn_deriv_mul_div hUo hDd.differentiableOn hgd
    (fun z _ => hord z) hzero
  obtain ⟨r, F, hFd, hFeq⟩ := exists_principalParts hUo P
    (fun p hp => ⟨by rw [hPline p hp]; norm_num, by rw [hPline p hp]; norm_num⟩) H hHd
  have hFval : ∀ z ∈ U, D z ≠ 0 →
      F z = -(riemannZeta z / z) * (deriv D z / D z) - ∑ p ∈ P, r p / (z - p) := by
    intro z hz h0
    have hzP : z ∉ P := fun h => h0 ((hPmem z).mp h).1
    have hprod : ∏ p ∈ P, (z - p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero.mpr fun h => hzP (by rw [h]; exact hp)
    rw [hFeq z hz hzP, hHeq z hz h0]
    show deriv D z * (-(riemannZeta z / z) * ∏ p ∈ P, (z - p)) / D z / ∏ p ∈ P, (z - p) - _ = _
    congr 1
    generalize -(riemannZeta z / z) = X
    field_simp
  -- lower bounds for `D` on the two lines and at good heights
  obtain ⟨δR, hδR, hlowR⟩ := exists_le_norm_expPoly_of_zeroFree hℓR
    (show (1 / 2 : ℝ) < 3 / 4 by norm_num) hPR
  obtain ⟨δL, hδL, hlowL⟩ := exists_le_norm_expPoly_of_zeroFree hℓL
    (show (-(1 / 2) : ℝ) < -(1 / 4) by norm_num) hPL
  obtain ⟨T₀, hT₀⟩ := exists_ne_zero_on_line_of_differentiable hDd hDne
  have hseg : ∀ x : ℝ, |x - 1 / 2| ≤ 1 / 4 → D ((x : ℂ) + T₀ * I) ≠ 0 := by
    intro x _ h0
    have hre := hline _ h0
    have hx' : x = 1 / 2 := by simpa using hre
    rw [hx'] at h0
    exact hT₀ (by simpa using h0)
  obtain ⟨μ, hμ, L, hgood⟩ :=
    exists_good_heights_of_almostPeriodic hDd.continuous (hAP (1 / 2) (1 / 4)) hseg
  have hDlineR : ∀ z : ℂ, z.re = 3 / 4 → ‖a m‖ * Real.exp (-(LM * (3 / 4))) * δR ≤ ‖D z‖ := by
    intro z hz
    rw [hDR, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul, hz]
    exact mul_le_mul_of_nonneg_left (hlowR z (le_of_eq hz.symm)) (by positivity)
  have hDlineL : ∀ z : ℂ, z.re = 1 / 4 → ‖a N‖ * Real.exp (-(LN * (1 / 4))) * δL ≤ ‖D z‖ := by
    intro z hz
    rw [hDL, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul, hz]
    exact mul_le_mul_of_nonneg_left (hlowL (-z) (by rw [Complex.neg_re, hz]))
      (by positivity)
  set ν : ℝ := min μ (min (‖a m‖ * Real.exp (-(LM * (3 / 4))) * δR)
    (‖a N‖ * Real.exp (-(LN * (1 / 4))) * δL)) with hν
  have hνpos : 0 < ν := lt_min hμ (lt_min
    (mul_pos (mul_pos (norm_pos_iff.mpr (ha m)) (Real.exp_pos _)) hδR)
    (mul_pos (mul_pos (norm_pos_iff.mpr (ha N)) (Real.exp_pos _)) hδL))
  -- `F` is bounded where `D` is bounded below and the poles are at a distance
  set ρs : ℝ := ∑ p ∈ P, ‖r p‖ with hρs
  set η : ℝ := min (1 / 4) (ν / (CD + 1)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (div_pos hνpos (by linarith))
  have hFbound : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 / 4 → ν ≤ ‖D z‖ → (∀ p ∈ P, η ≤ ‖z - p‖) →
      ‖F z‖ ≤ 8 * CD / ν + ρs / η := by
    intro z h1 h2 hDz hdist
    have hzU : z ∈ U := ⟨by linarith, by linarith⟩
    have hD0 : D z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hνpos hDz)
    rw [hFval z hzU hD0]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_neg, norm_div (deriv D z) (D z)]
      have ha4 : 1 / (1 - z.re) ≤ 4 :=
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) (by linarith)).trans_eq
          (by norm_num)
      have hb4 : 1 / z.re ≤ 4 :=
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) h1).trans_eq (by norm_num)
      have hg8 : ‖riemannZeta z / z‖ ≤ 8 :=
        (norm_riemannZeta_div_le (by linarith) (by linarith)).trans (by linarith)
      calc ‖riemannZeta z / z‖ * (‖deriv D z‖ / ‖D z‖) ≤ 8 * (CD / ν) :=
            mul_le_mul hg8 (div_le_div₀ hCD0 (hderiv_le z (by linarith) (by linarith)) hνpos hDz)
              (by positivity) (by norm_num)
        _ = 8 * CD / ν := by ring
    · rw [hρs, Finset.sum_div]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hηpos (hdist p hp)
  -- a height at which `D` is bounded below is at a distance from the zeros in `P`
  have hdistT : ∀ T : ℝ, μ ≤ ‖D ((1 / 2 : ℂ) + T * I)‖ → ∀ z : ℂ, z.im = T →
      ∀ p ∈ P, η ≤ ‖z - p‖ := by
    intro T hT z hzT p hp
    have hDp : D p = 0 := ((hPmem p).mp hp).1
    have hconv : Convex ℝ ({w : ℂ | 0 ≤ w.re} ∩ {w : ℂ | w.re ≤ 1}) :=
      (convex_halfSpace_re_ge 0).inter (convex_halfSpace_re_le 1)
    have hmv := hconv.norm_image_sub_le_of_norm_deriv_le (f := D) (C := CD)
      (fun w _ => hDd w) (fun w hw => hderiv_le w hw.1 hw.2)
      (x := p) (y := (1 / 2 : ℂ) + T * I)
      ⟨by show (0 : ℝ) ≤ p.re; rw [hPline p hp]; norm_num,
        by show p.re ≤ 1; rw [hPline p hp]; norm_num⟩
      ⟨by show (0 : ℝ) ≤ ((1 / 2 : ℂ) + T * I).re; simp,
        by show ((1 / 2 : ℂ) + T * I).re ≤ 1; simp; norm_num⟩
    rw [hDp, sub_zero] at hmv
    have hw : (1 / 2 : ℂ) + T * I - p = ((T - p.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hPline p hp]
    rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hmv
    have him : |T - p.im| ≤ ‖z - p‖ := by
      have := Complex.abs_im_le_norm (z - p)
      rwa [Complex.sub_im, hzT] at this
    have h1 : ν ≤ (CD + 1) * |T - p.im| := by
      have hνμ : ν ≤ μ := min_le_left _ _
      nlinarith [abs_nonneg (T - p.im), hνμ.trans (hT.trans hmv)]
    have h2 : ν / (CD + 1) ≤ |T - p.im| := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    exact (min_le_right _ _).trans (h2.trans him)
  have hFb : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → ‖F s‖ ≤ 8 * CD / ν + ρs / η := by
    intro s h1 h2
    refine norm_le_of_good_heights (x₁ := 1 / 4) (x₂ := 3 / 4) (by norm_num) (U := U)
      (fun z hz1 hz2 => ⟨by linarith, by linarith⟩) hFd (L := L) ?_ ?_ h1 h2
    · rintro z (hz | hz)
      · refine hFbound z (le_of_eq hz.symm) (by rw [hz]; norm_num)
          ((min_le_right _ _).trans ((min_le_right _ _).trans (hDlineL z hz))) fun p hp => ?_
        have h := Complex.abs_re_le_norm (z - p)
        rw [Complex.sub_re, hz, hPline p hp, show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4) by norm_num,
          abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
        exact (min_le_left _ _).trans h
      · refine hFbound z (by rw [hz]; norm_num) (le_of_eq hz)
          ((min_le_right _ _).trans ((min_le_left _ _).trans (hDlineR z hz))) fun p hp => ?_
        have h := Complex.abs_re_le_norm (z - p)
        rw [Complex.sub_re, hz, hPline p hp, show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num,
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
        exact (min_le_left _ _).trans h
    · intro y
      obtain ⟨T, hT, hTD⟩ := hgood y
      have hmid : μ ≤ ‖D ((1 / 2 : ℂ) + T * I)‖ :=
        hTD _ (by rw [show ((1 / 2 : ℂ) + T * I).re = 1 / 2 by simp]; norm_num) (by simp)
      exact ⟨T, hT, fun z hz1 hz2 hzT => hFbound z hz1 hz2
        ((min_le_left _ _).trans (hTD z (abs_le.mpr ⟨by linarith, by linarith⟩) hzT))
        (hdistT T hmid z hzT)⟩
  -- the hypotheses of the kernel theorem
  have hR : ∀ σ : ℝ, 1 / 2 < σ → Summable fun i : LogIndex _ ℓR =>
      ‖logWeight (-(LM : ℂ)) cR ℓR i‖ * Real.exp (-logExp ℓR i) ^ σ := by
    intro σ hσ
    refine (hRsum σ hσ).congr fun i => ?_
    rw [← Real.exp_mul]
    congr 2
    ring
  have hL : ∀ σ : ℝ, σ < 1 / 2 → Summable fun j : LogIndex _ ℓL =>
      ‖-logWeight (LN : ℂ) cL ℓL j‖ * Real.exp (logExp ℓL j) ^ σ := by
    intro σ hσ
    refine (hLsum (-σ) (by linarith)).congr fun j => ?_
    rw [norm_neg, ← Real.exp_mul]
    congr 2
    ring
  have hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → F s = -(riemannZeta s / s) *
      (∑' i : LogIndex _ ℓR, logWeight (-(LM : ℂ)) cR ℓR i *
        ((Real.exp (-logExp ℓR i) : ℝ) : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p) := by
    intro s h0 h1
    have hsU : s ∈ U := ⟨by linarith, h1⟩
    have hD0 : D s ≠ 0 := fun h => by
      have := hline s h
      linarith
    rw [hFval s hsU hD0, hΛR s h0, ← (hRhas s h0).tsum_eq]
    congr 2
    refine tsum_congr fun i => ?_
    rw [exp_cpow_eq_cexp, Complex.ofReal_neg (logExp ℓR i)]
  have hFL : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → F s = -(riemannZeta s / s) *
      (∑' j : LogIndex _ ℓL, -logWeight (LN : ℂ) cL ℓL j *
        ((Real.exp (logExp ℓL j) : ℝ) : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p) := by
    intro s h0 h1
    have hsU : s ∈ U := ⟨h0, by linarith⟩
    have hD0 : D s ≠ 0 := fun h => by
      have := hline s h
      linarith
    have hsum := (hLhas (-s) (by rw [Complex.neg_re]; linarith)).tsum_eq
    rw [hFval s hsU hD0, hΛL s h1,
      show -(LN : ℂ) - expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s) =
        -((LN : ℂ) + expPolyDeriv cL ℓL (-s) / expPoly cL ℓL (-s)) by ring,
      ← hsum, ← tsum_neg]
    congr 2
    refine tsum_congr fun j => ?_
    rw [exp_cpow_eq_cexp, neg_mul_neg, neg_mul]
  have key := constantTerms_agree_of_poles
    (b := logWeight (-(LM : ℂ)) cR ℓR) (a := fun i => Real.exp (-logExp ℓR i))
    (c := fun j => -logWeight (LN : ℂ) cL ℓL j) (q := fun j => Real.exp (logExp ℓL j))
    (fun i => Real.exp_pos _)
    (fun i => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (logExp_nonneg hℓR i)))
    (fun j => Real.one_le_exp (logExp_nonneg hℓL j)) hR hL hPline hFd hFb hFR hFL
  -- the two constant terms
  have hRHS : (∑' i : LogIndex _ ℓR, if Real.exp (-logExp ℓR i) = 1
      then logWeight (-(LM : ℂ)) cR ℓR i else 0) = -(LM : ℂ) := by
    refine (tsum_congr fun i => ?_).trans (tsum_logWeight_zero (-(LM : ℂ)) cR hℓR)
    by_cases h : logExp ℓR i = 0
    · rw [if_pos h, if_pos (by rw [h, neg_zero, Real.exp_zero])]
    · rw [if_neg h, if_neg fun h' => h (neg_eq_zero.mp ((Real.exp_eq_one_iff _).mp h'))]
  have hLHS : (∑' j : LogIndex _ ℓL, if Real.exp (logExp ℓL j) = 1
      then -logWeight (LN : ℂ) cL ℓL j else 0) = -(LN : ℂ) := by
    refine (tsum_congr fun j => ?_).trans (tsum_neg.trans
      (congrArg Neg.neg (tsum_logWeight_zero (LN : ℂ) cL hℓL)))
    by_cases h : logExp ℓL j = 0
    · rw [if_pos h, if_pos (by rw [h, Real.exp_zero])]
    · rw [if_neg h, if_neg fun h' => h ((Real.exp_eq_one_iff _).mp h'), neg_zero]
  rw [hLHS, hRHS] at key
  have hlog : LN = LM := by exact_mod_cast neg_injective key
  rw [hLN, hLM] at hlog
  linarith

/-- An exponential polynomial with at least two terms has a zero that is not a zero of `ξ`. -/
theorem exists_zero_expSum_not_xi_zero {n : ℕ} (a : Fin n → ℂ) (lam : Fin n → ℝ)
    (hinj : Function.Injective lam) (ha : ∀ k, a k ≠ 0) {k₁ k₂ : Fin n} (hne : k₁ ≠ k₂) :
    ∃ z : ℂ, expSum a lam z = 0 ∧ xi z ≠ 0 :=
  (infinite_zeros_not_xi_zeros a lam hinj ha hne).nonempty

/-! ### Dirichlet polynomials -/

/-- **Infinitely many zeros of a Dirichlet polynomial are not zeros of `ξ`.** A Dirichlet
polynomial with at least two terms is the exponential polynomial with the frequencies `−log n`. -/
theorem infinite_zeros_not_xi_zeros_dirichletPolynomial (a : ℕ →₀ ℂ) (ha0 : a 0 = 0) {n₁ n₂ : ℕ}
    (h₁ : a n₁ ≠ 0) (h₂ : a n₂ ≠ 0) (hne : n₁ ≠ n₂) :
    {z : ℂ | finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0}.Infinite := by
  classical
  set e := a.support.equivFin with he
  set a' : Fin a.support.card → ℂ := fun k => a (e.symm k) with ha'
  set lam' : Fin a.support.card → ℝ := fun k => -Real.log ((e.symm k : ℕ)) with hlam'
  have hpos : ∀ n ∈ a.support, 0 < n := fun n hn =>
    Nat.pos_of_ne_zero fun h => Finsupp.mem_support_iff.mp hn (by rw [h]; exact ha0)
  have hfun : ∀ s : ℂ, finiteDirichletPolynomial a s = expSum a' lam' s := by
    intro s
    show (∑ n ∈ a.support, a n * (n : ℂ) ^ (-s)) = ∑ k, a' k * cexp ((lam' k : ℂ) * s)
    refine (Finset.sum_coe_sort a.support (fun n => a n * (n : ℂ) ^ (-s))).symm.trans
      ((Equiv.sum_comp e.symm _).symm.trans (Finset.sum_congr rfl fun k _ => ?_))
    show a (e.symm k) * ((e.symm k : ℕ) : ℂ) ^ (-s) =
      a (e.symm k) * cexp (((-Real.log ((e.symm k : ℕ)) : ℝ) : ℂ) * s)
    rw [natCast_cpow_neg_eq_cexp (hpos _ (e.symm k).2), Complex.ofReal_neg]
  have hinj : Function.Injective lam' := by
    intro k l hkl
    have h1 : Real.log ((e.symm k : ℕ)) = Real.log ((e.symm l : ℕ)) := neg_injective hkl
    have h2 : (((e.symm k : ℕ)) : ℝ) = ((e.symm l : ℕ)) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hpos _ (e.symm k).2))
        (Set.mem_Ioi.mpr (by exact_mod_cast hpos _ (e.symm l).2)) h1
    exact e.symm.injective (Subtype.ext (by exact_mod_cast h2))
  have ha'ne : ∀ k, a' k ≠ 0 := fun k => Finsupp.mem_support_iff.mp (e.symm k).2
  have hk : e ⟨n₁, Finsupp.mem_support_iff.mpr h₁⟩ ≠ e ⟨n₂, Finsupp.mem_support_iff.mpr h₂⟩ :=
    fun h => hne (congrArg Subtype.val (e.injective h))
  have hset : {z : ℂ | finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0} =
      {z : ℂ | expSum a' lam' z = 0 ∧ xi z ≠ 0} := by
    ext z
    simp only [Set.mem_setOf_eq, hfun z]
  rw [hset]
  exact infinite_zeros_not_xi_zeros a' lam' hinj ha'ne hk

/-- **No Dirichlet polynomial is a factor of `ξ`.** A Dirichlet polynomial with at least two terms
has a zero that is not a zero of `ξ`. -/
theorem exists_zero_not_xi_zero (a : ℕ →₀ ℂ) (ha0 : a 0 = 0) {n₁ n₂ : ℕ} (h₁ : a n₁ ≠ 0)
    (h₂ : a n₂ ≠ 0) (hne : n₁ ≠ n₂) :
    ∃ z : ℂ, finiteDirichletPolynomial a z = 0 ∧ xi z ≠ 0 :=
  (infinite_zeros_not_xi_zeros_dirichletPolynomial a ha0 h₁ h₂ hne).nonempty

end GaloisForLFunctions.InfiniteRankPurityTheory
