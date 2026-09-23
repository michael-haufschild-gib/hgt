import GaloisForLFunctions.RHTower.PrimeLagLandauSeries

/-!
# Analytic continuation of the zero-side expression

`G_M(s) = M(−ζ'/ζ)(1+s) − Σ_q w_q (−ζ'/ζ)(s + 3/2 − ρ_q)` is analytic on boxes
`θ − ½ − η < Re s < 3/4`, `|Im s − t₀| < r`, away from the finitely many poles `ρ_q − ½` with
`|γ_q − t₀| < 5`: on such a box every shifted argument `w = s + 3/2 − ρ_q` has `Re w ≥ 1 − η > θ`,
so `ζ(w) ≠ 0`, and for the far copies `|Im w| ≥ 4` with distance at least `1/5` from every zero, so
the two-sided bound `‖ζ'/ζ(w)‖ ≤ 5C log|Im w|` gives a summable majorant `‖w_q‖ · 5C log(2 + |γ_q − t₀|)`.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- The zero-side continuation. -/
def landauG (M : ℝ) (s : ℂ) : ℂ :=
  (M : ℂ) * (-logDeriv riemannZeta (1 + s))
    - ∑' q : XiZeroCopy, lagWeight q * (-logDeriv riemannZeta (s + 3 / 2 - (q.1 : ℂ)))

/-- The term of the copy `q`. -/
def landauTerm_primeLagLandauContinuation (q : XiZeroCopy) (s : ℂ) : ℂ :=
  lagWeight q * (-logDeriv riemannZeta (s + 3 / 2 - (q.1 : ℂ)))

theorem landauG_eq (M : ℝ) (s : ℂ) :
    landauG M s = (M : ℂ) * (-logDeriv riemannZeta (1 + s)) - ∑' q, landauTerm_primeLagLandauContinuation q s := rfl

/-- The box `θ − ½ − η < Re s < 3/4`, `|Im s − t₀| < r`. -/
def landauBox (θ η t₀ r : ℝ) : Set ℂ :=
  {s | θ - 1 / 2 - η < s.re ∧ s.re < 3 / 4 ∧ |s.im - t₀| < r}

theorem isOpen_landauBox (θ η t₀ r : ℝ) : IsOpen (landauBox θ η t₀ r) := by
  unfold landauBox
  refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
    (IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const) ?_)
  exact isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

/-- Reflection: every copy has real part at least `1 − θ`. -/
theorem one_sub_le_re_of_forall_re_le {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (q : XiZeroCopy) : 1 - θ ≤ (q.1 : ℂ).re := by
  have := hθ (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at this
  linarith

/-- `ζ(w) ≠ 0` for `Re w > θ`, `Re w > 0`, `w ≠ 1`. -/
theorem riemannZeta_ne_zero_of_re_gt_bound {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    {w : ℂ} (hw : θ < w.re) (hw0 : 0 < w.re) (hw1 : w ≠ 1) : riemannZeta w ≠ 0 := by
  rcases le_or_gt 1 w.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · intro hζ
    have hw0' : w ≠ 0 := fun h => by rw [h] at hw0; simp at hw0
    have hxi : xi w = 0 := by rw [xi_eq_xiUnit_mul_zeta hw0' hw1 hw0, hζ, mul_zero]
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have := hθ q
    rw [hq] at this
    linarith

theorem differentiableAt_logDeriv_zeta {w : ℂ} (hw1 : w ≠ 1) (hw0 : riemannZeta w ≠ 0) :
    DifferentiableAt ℂ (logDeriv riemannZeta) w := by
  have h := analyticAt_riemannZeta_of_ne_one_zetaLocalZeroCount hw1
  exact (h.deriv.differentiableAt).div h.differentiableAt hw0

/-- Differentiability of the term of `q` on a set where its argument avoids `1` and the zeros. -/
theorem differentiableOn_landauTerm {U : Set ℂ} (q : XiZeroCopy)
    (h : ∀ s ∈ U, s + 3 / 2 - (q.1 : ℂ) ≠ 1 ∧ riemannZeta (s + 3 / 2 - (q.1 : ℂ)) ≠ 0) :
    DifferentiableOn ℂ (landauTerm_primeLagLandauContinuation q) U := by
  intro s hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => s + 3 / 2 - (q.1 : ℂ)) s :=
    (differentiableAt_id.add_const _).sub_const _
  have h2 := (differentiableAt_logDeriv_zeta (h s hs).1 (h s hs).2).comp s h1
  exact ((h2.neg).const_mul _).differentiableWithinAt

/-! ## The far-term bound on a box -/

/-- The argument `w = s + 3/2 − ρ_q` on the box: real part in `[1 − η, 2]`. -/
theorem shifted_re_bounds {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) {s : ℂ} (hs : s ∈ landauBox θ η t₀ r) (q : XiZeroCopy) :
    1 - η ≤ (s + 3 / 2 - (q.1 : ℂ)).re ∧ (s + 3 / 2 - (q.1 : ℂ)).re ≤ 2 := by
  obtain ⟨h1, h2, _⟩ := hs
  have hq := hθ q
  have hq' := one_sub_le_re_of_forall_re_le hθ q
  have h32 : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
  simp only [Complex.sub_re, Complex.add_re, h32]
  constructor <;> linarith

/-- On the box every shifted argument avoids the zeros of `ζ`. -/
theorem shifted_zeta_ne_zero {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) {s : ℂ} (hs : s ∈ landauBox θ η t₀ r) (q : XiZeroCopy)
    (hw1 : s + 3 / 2 - (q.1 : ℂ) ≠ 1) : riemannZeta (s + 3 / 2 - (q.1 : ℂ)) ≠ 0 := by
  have h := (shifted_re_bounds hθ hθ34 hs q).1
  exact riemannZeta_ne_zero_of_re_gt_bound hθ (by linarith) (by linarith) hw1

/-- The far-term bound: for `|γ_q − t₀| ≥ 5` and `s` in the box (radius `r ≤ 1`),
`‖term_q(s)‖ ≤ ‖w_q‖ · 5C · log(2 + |γ_q − t₀|)`. -/
theorem norm_landauTerm_le_far {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {s : ℂ} (hs : s ∈ landauBox θ η t₀ r)
    {q : XiZeroCopy} (hq : 5 ≤ |zeroOrdinate q - t₀|) :
    ‖landauTerm_primeLagLandauContinuation q s‖
      ≤ ‖lagWeight q‖ * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - t₀|)) := by
  obtain ⟨hb1, hb2, hb3⟩ := hs
  set w : ℂ := s + 3 / 2 - (q.1 : ℂ) with hw
  have hre := shifted_re_bounds hθ hθ34 ⟨hb1, hb2, hb3⟩ q
  rw [← hw] at hre
  have him : w.im = s.im - zeroOrdinate q := by
    rw [hw]; simp [zeroOrdinate]
  -- `|Im w| ≥ 4`
  have him4 : 4 ≤ |w.im| := by
    rw [him]
    have : |zeroOrdinate q - t₀| ≤ |s.im - zeroOrdinate q| + |s.im - t₀| := by
      have := abs_sub_le (zeroOrdinate q) s.im t₀
      rw [abs_sub_comm (zeroOrdinate q) s.im] at this
      exact this
    linarith
  -- `|Im w| ≤ 2 + |γ_q − t₀|`
  have himle : |w.im| ≤ 2 + |zeroOrdinate q - t₀| := by
    rw [him]
    have := abs_sub_le s.im t₀ (zeroOrdinate q)
    rw [abs_sub_comm t₀ (zeroOrdinate q)] at this
    linarith
  -- distance from the zeros is at least `1/5`
  have hdist : ∀ q' : XiZeroCopy, (1 / 5 : ℝ) ≤ ‖(w.re + w.im * I : ℂ) - (q'.1 : ℂ)‖ := by
    intro q'
    have h := Complex.re_le_norm ((w.re + w.im * I : ℂ) - (q'.1 : ℂ))
    have hq' := hθ q'
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero] at h
    linarith [hre.1]
  have hwform : w = (w.re + w.im * I : ℂ) := (Complex.re_add_im w).symm
  have hbound := norm_logDeriv_zeta_le_abs (σ := w.re) (t := w.im) (δ := 1 / 5)
    (by linarith [hre.1]) hre.2 him4 (by norm_num) (by norm_num) hdist
  rw [← hwform] at hbound
  have hC : 0 ≤ logDerivZetaConstant := by
    unfold logDerivZetaConstant; positivity
  have hlog : Real.log |w.im| ≤ Real.log (2 + |zeroOrdinate q - t₀|) :=
    Real.log_le_log (by linarith) himle
  have hlog0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
  unfold landauTerm_primeLagLandauContinuation
  rw [norm_mul, norm_neg, ← hw]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc ‖logDeriv riemannZeta w‖ ≤ logDerivZetaConstant * Real.log |w.im| / (1 / 5) := hbound
    _ = 5 * logDerivZetaConstant * Real.log |w.im| := by ring
    _ ≤ 5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - t₀|) := by gcongr

/-- The far majorant is summable. -/
theorem summable_far_majorant (t₀ : ℝ) :
    Summable fun q : XiZeroCopy =>
      ‖lagWeight q‖ * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - t₀|)) := by
  have hC : 0 ≤ logDerivZetaConstant := by unfold logDerivZetaConstant; positivity
  have h1 := summable_lagWeight_mul_log
  have h2 := summable_norm_lagWeight
  refine Summable.of_nonneg_of_le (fun q => by
      have : 0 ≤ Real.log (2 + |zeroOrdinate q - t₀|) := Real.log_nonneg (by linarith [abs_nonneg (zeroOrdinate q - t₀)])
      positivity)
    (fun q => ?_) ((h1.mul_left (5 * logDerivZetaConstant)).add
      (h2.mul_left (5 * logDerivZetaConstant * Real.log (2 + |t₀|))))
  have hlog : Real.log (2 + |zeroOrdinate q - t₀|)
      ≤ Real.log (2 + |zeroOrdinate q|) + Real.log (2 + |t₀|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have := abs_sub (zeroOrdinate q) t₀
    nlinarith [abs_nonneg (zeroOrdinate q), abs_nonneg t₀]
  have hw0 := norm_nonneg (lagWeight q)
  nlinarith [mul_le_mul_of_nonneg_left hlog (mul_nonneg hw0 (by positivity : (0:ℝ) ≤ 5 * logDerivZetaConstant))]

/-- The copies whose ordinate is within `5` of `t₀`. -/
def nearSet (t₀ : ℝ) : Set XiZeroCopy := {q | |zeroOrdinate q - t₀| < 5}

theorem five_le_of_mem_compl_nearSet {t₀ : ℝ} {q : XiZeroCopy} (hq : q ∈ (nearSet t₀)ᶜ) :
    5 ≤ |zeroOrdinate q - t₀| := not_lt.mp hq

/-- The copies with `|γ| ≤ T` form a finite set. -/
theorem finite_copies_abs_im_le (T : ℝ) : {q : XiZeroCopy | |zeroOrdinate q| ≤ T}.Finite := by
  classical
  have hZ : (xiZeroSet_weilLagFunctionCriterion ∩ closedBall (0 : ℂ) (|T| + 1)).Finite :=
    finite_xiZeroSet_inter (isCompact_closedBall _ _)
  have hsub : {q : XiZeroCopy | |zeroOrdinate q| ≤ T} ⊆
      ⋃ ρ ∈ xiZeroSet_weilLagFunctionCriterion ∩ closedBall (0 : ℂ) (|T| + 1), {q : XiZeroCopy | (q.1 : ℂ) = ρ} := by
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨(q.1 : ℂ), ⟨xi_xiZeroCopy_eq_zero q, ?_⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have hre := xiZeroCopy_re_pos q
    have hre1 := xiZeroCopy_re_lt_one q
    have him : |zeroOrdinate q| ≤ T := hq
    have hT : T ≤ |T| := le_abs_self T
    calc ‖(q.1 : ℂ)‖ ≤ |(q.1 : ℂ).re| + |(q.1 : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + |T| := by
          have : |(q.1 : ℂ).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          unfold zeroOrdinate at him
          linarith
      _ = |T| + 1 := by ring
  refine (hZ.biUnion fun ρ _ => ?_).subset hsub
  have hinj : Set.InjOn (fun q : XiZeroCopy => (q.2 : ℕ)) {q : XiZeroCopy | (q.1 : ℂ) = ρ} := by
    intro q hq q' hq' hqq'
    have hq1 : (q.1 : ℂ) = ρ := hq
    have hq1' : (q'.1 : ℂ) = ρ := hq'
    have h1 : q.1 = q'.1 := Subtype.ext (hq1.trans hq1'.symm)
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr hqq')
  refine Set.Finite.of_finite_image ((Set.finite_Iio
    ((MeromorphicOn.divisor xi Set.univ ρ).toNat)).subset ?_) hinj
  rintro _ ⟨q, hq, rfl⟩
  have hq' : (q.1 : ℂ) = ρ := hq
  exact lt_of_lt_of_eq q.2.isLt (by rw [hq'])

theorem finite_nearSet (t₀ : ℝ) : (nearSet t₀).Finite := by
  refine (finite_copies_abs_im_le (|t₀| + 5)).subset fun q hq => ?_
  have h : |zeroOrdinate q - t₀| < 5 := hq
  show |zeroOrdinate q| ≤ |t₀| + 5
  have := abs_sub_abs_le_abs_sub (zeroOrdinate q) t₀
  linarith

/-- The far tail is differentiable on the box. -/
theorem differentiableOn_farTail {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) :
    DifferentiableOn ℂ
      (fun s => ∑' q : ↑(nearSet t₀)ᶜ, landauTerm_primeLagLandauContinuation q s)
      (landauBox θ η t₀ r) := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : ↑(nearSet t₀)ᶜ =>
      ‖lagWeight q‖ * (5 * logDerivZetaConstant * Real.log (2 + |zeroOrdinate q - t₀|)))
    ((summable_far_majorant t₀).subtype _) (fun q => ?_) (isOpen_landauBox _ _ _ _)
    (fun q s hs => norm_landauTerm_le_far hθ hθ34 hη hr1 hs (five_le_of_mem_compl_nearSet q.2))
  have hq5 : 5 ≤ |zeroOrdinate q - t₀| := five_le_of_mem_compl_nearSet q.2
  refine differentiableOn_landauTerm q.1 fun s hs => ⟨?_, ?_⟩
  · -- the argument is not `1`: its imaginary part is nonzero
    intro h1
    have him : (s + 3 / 2 - (q.1.1 : ℂ)).im = s.im - zeroOrdinate q := by simp [zeroOrdinate]
    rw [h1, Complex.one_im] at him
    have hq := hq5
    have hs3 := hs.2.2
    have : |zeroOrdinate q - t₀| ≤ |s.im - zeroOrdinate q| + |s.im - t₀| := by
      have := abs_sub_le (zeroOrdinate q) s.im t₀
      rw [abs_sub_comm (zeroOrdinate q) s.im] at this
      exact this
    rw [show s.im - zeroOrdinate q = 0 by linarith, abs_zero] at this
    linarith
  · refine shifted_zeta_ne_zero hθ hθ34 hη hs q.1 ?_
    intro h1
    have him : (s + 3 / 2 - (q.1.1 : ℂ)).im = s.im - zeroOrdinate q := by simp [zeroOrdinate]
    rw [h1, Complex.one_im] at him
    have hq := hq5
    have hs3 := hs.2.2
    have : |zeroOrdinate q - t₀| ≤ |s.im - zeroOrdinate q| + |s.im - t₀| := by
      have := abs_sub_le (zeroOrdinate q) s.im t₀
      rw [abs_sub_comm (zeroOrdinate q) s.im] at this
      exact this
    rw [show s.im - zeroOrdinate q = 0 by linarith, abs_zero] at this
    linarith


/-- The far tail is summable at every point of the box. -/
theorem summable_farTail {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {s : ℂ} (hs : s ∈ landauBox θ η t₀ r) :
    Summable fun q : ↑(nearSet t₀)ᶜ => landauTerm_primeLagLandauContinuation q s :=
  Summable.of_norm_bounded ((summable_far_majorant t₀).subtype _)
    fun q => norm_landauTerm_le_far hθ hθ34 hη hr1 hs (five_le_of_mem_compl_nearSet q.2)

/-- The full family is summable at every point of the box, and splits into near and far parts. -/
theorem tsum_landauTerm_split {θ η t₀ r : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {s : ℂ} (hs : s ∈ landauBox θ η t₀ r) :
    ∑' q, landauTerm_primeLagLandauContinuation q s
      = ∑ q ∈ (finite_nearSet t₀).toFinset, landauTerm_primeLagLandauContinuation q s
        + ∑' q : ↑(nearSet t₀)ᶜ, landauTerm_primeLagLandauContinuation q s := by
  have hfar := summable_farTail hθ hθ34 hη hr1 hs
  have hnear : Summable fun q : nearSet t₀ => landauTerm_primeLagLandauContinuation q s := by
    haveI : Finite (nearSet t₀) := (finite_nearSet t₀).to_subtype
    exact Summable.of_finite
  have hsum : Summable fun q => landauTerm_primeLagLandauContinuation q s := summable_subtype_and_compl.mp ⟨hnear, hfar⟩
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl (nearSet t₀)]
  congr 1
  rw [← tsum_congr_set_coe (fun q => landauTerm_primeLagLandauContinuation q s) (Set.Finite.coe_toFinset (finite_nearSet t₀))]
  exact Finset.tsum_subtype' _ (fun q => landauTerm_primeLagLandauContinuation q s)

/-! ## Analyticity of the continuation on open sets avoiding the near poles -/

/-- **The continuation is differentiable on any open subset of the box that avoids the near
poles.** -/
theorem differentiableOn_landauG {θ η t₀ r M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {U : Set ℂ}
    (hUbox : U ⊆ landauBox θ η t₀ r) (hpos : ∀ s ∈ U, 0 < s.re)
    (hnear : ∀ q ∈ nearSet t₀, ∀ s ∈ U, s + 3 / 2 - (q.1 : ℂ) ≠ 1) :
    DifferentiableOn ℂ (landauG M) U := by
  have hfun : ∀ s ∈ U, landauG M s
      = (M : ℂ) * (-logDeriv riemannZeta (1 + s))
        - (∑ q ∈ (finite_nearSet t₀).toFinset, landauTerm_primeLagLandauContinuation q s
          + ∑' q : ↑(nearSet t₀)ᶜ, landauTerm_primeLagLandauContinuation q s) := by
    intro s hs
    rw [landauG_eq, tsum_landauTerm_split hθ hθ34 hη hr1 (hUbox hs)]
  refine DifferentiableOn.congr ?_ hfun
  -- the `M` term
  have hM : DifferentiableOn ℂ (fun s : ℂ => (M : ℂ) * (-logDeriv riemannZeta (1 + s))) U := by
    intro s hs
    have h0 : (1 : ℂ) + s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hpos s hs]
    have hζ : riemannZeta (1 + s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; linarith [hpos s hs])
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (1 : ℂ) + s) s := differentiableAt_id.const_add _
    exact (((differentiableAt_logDeriv_zeta h0 hζ).comp s h1).neg.const_mul _).differentiableWithinAt
  -- the near terms
  have hnearD : DifferentiableOn ℂ
      (fun s => ∑ q ∈ (finite_nearSet t₀).toFinset, landauTerm_primeLagLandauContinuation q s) U := by
    have := DifferentiableOn.sum (𝕜 := ℂ) (s := U) (u := (finite_nearSet t₀).toFinset)
      (A := fun q => landauTerm_primeLagLandauContinuation q) fun q hq => ?_
    · refine this.congr fun s _ => ?_
      simp [Finset.sum_apply]
    · have hqn : q ∈ nearSet t₀ := (Set.Finite.mem_toFinset _).mp hq
      refine differentiableOn_landauTerm q fun s hs => ⟨hnear q hqn s hs, ?_⟩
      exact shifted_zeta_ne_zero hθ hθ34 hη (hUbox hs) q (hnear q hqn s hs)
  have hfarD : DifferentiableOn ℂ (fun s => ∑' q : ↑(nearSet t₀)ᶜ, landauTerm_primeLagLandauContinuation q s) U :=
    (differentiableOn_farTail hθ hθ34 hη hr1).mono hUbox
  exact hM.sub (hnearD.add hfarD)

end

end RHTower
