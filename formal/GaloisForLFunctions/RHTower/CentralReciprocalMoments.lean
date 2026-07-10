import GaloisForLFunctions.RHTower.XiConvergenceExponent
import GaloisForLFunctions.RHTower.XiRealAnchorPositive
import GaloisForLFunctions.RHTower.RHLadderTheory

open Complex Metric Function Filter MeromorphicOn

namespace RHTower

noncomputable section

/-- The xi divisor remains inverse-square summable after centering at the FE fixed point. -/
theorem xi_zero_multiplicity_centered_inv_sq_summable :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) /
        ‖(ρ : ℂ) - 1 / 2‖ ^ 2) := by
  classical
  set D := MeromorphicOn.divisor xi Set.univ with hD
  set f : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) / ‖(ρ : ℂ)‖ ^ 2 with hf
  set g : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 with hg
  have hf_sum : Summable f := by
    simpa only [f, hD] using xi_zero_multiplicity_inv_sq_summable
  have hdom : Summable (fun ρ => 4 * f ρ) := hf_sum.mul_left 4
  have hLF : LocallyFiniteSupport D.toFun := Function.locallyFinsupp.locallyFiniteSupport D
  have hsmall : {ρ : ↥D.support | ‖(ρ : ℂ)‖ < 1}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset
      (hLF.finite_inter_support_of_isCompact (isCompact_closedBall (0 : ℂ) 1))
    rintro z ⟨ρ, hρ, rfl⟩
    exact ⟨by simpa [mem_closedBall] using le_of_lt hρ, ρ.2⟩
  have hg_sum : Summable g := hdom.of_norm_bounded_eventually (by
    filter_upwards [hsmall.eventually_cofinite_notMem] with ρ hρ
    simp only [not_lt] at hρ
    have hd : (0 : ℝ) ≤ (D (ρ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
    have hbpos : (0 : ℝ) < ‖(ρ : ℂ)‖ := lt_of_lt_of_le zero_lt_one hρ
    have htri : ‖(ρ : ℂ)‖ ≤ ‖(ρ : ℂ) - 1 / 2‖ + 1 / 2 := by
      calc
        ‖(ρ : ℂ)‖ = ‖((ρ : ℂ) - 1 / 2) + 1 / 2‖ := by ring_nf
        _ ≤ ‖(ρ : ℂ) - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
        _ = ‖(ρ : ℂ) - 1 / 2‖ + 1 / 2 := by norm_num
    have hab : ‖(ρ : ℂ)‖ / 2 ≤ ‖(ρ : ℂ) - 1 / 2‖ := by linarith
    have hapos : (0 : ℝ) < ‖(ρ : ℂ) - 1 / 2‖ :=
      lt_of_lt_of_le (half_pos hbpos) hab
    have hcomp :
        (D (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2 ≤
          4 * ((D (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
      calc
        (D (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2
            ≤ (D (ρ : ℂ) : ℝ) / (‖(ρ : ℂ)‖ / 2) ^ 2 :=
          div_le_div_of_nonneg_left hd (by positivity)
            (pow_le_pow_left₀ (by positivity) hab 2)
        _ = 4 * ((D (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
          field_simp
          ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ g ρ)]
    simpa only [hg, hf] using hcomp)
  simpa only [g, hD] using hg_sum

/-- The squared reciprocal spectral coordinate centered at the FE fixed point. -/
def xiCentralReciprocalSquare (ρ : ℂ) : ℂ :=
  -((ρ - 1 / 2)⁻¹) ^ 2

/-- The first centered reciprocal-square divisor moment is absolutely summable. -/
theorem xi_central_reciprocal_square_summable :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
        xiCentralReciprocalSquare (ρ : ℂ)) := by
  let D := MeromorphicOn.divisor xi Set.univ
  let f : ↥D.support → ℝ := fun ρ =>
    ((D (ρ : ℂ) : ℝ)) / ‖(ρ : ℂ) - 1 / 2‖ ^ 2
  have hf : Summable f := by
    simpa only [D, f] using xi_zero_multiplicity_centered_inv_sq_summable
  refine Summable.of_norm_bounded hf (fun ρ => ?_)
  have hd : (0 : ℝ) ≤ (D (ρ : ℂ) : ℝ) := by
    exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd,
    xiCentralReciprocalSquare, norm_neg, norm_pow, norm_inv]
  simp only [f]
  rw [div_eq_mul_inv, inv_pow]
  exact le_rfl

/-- The centered reciprocal-square coordinates of the actual xi divisor are
trace class even after forgetting their positive integer multiplicities. -/
theorem xi_central_reciprocal_square_unweighted_summable :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      xiCentralReciprocalSquare (ρ : ℂ)) := by
  let D := MeromorphicOn.divisor xi Set.univ
  let lam : ↥D.support → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  let weighted : ↥D.support → ℂ := fun ρ => ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ
  have hweighted : Summable weighted := by
    simpa [D, lam, weighted] using xi_central_reciprocal_square_summable
  refine hweighted.norm.of_norm_bounded (fun ρ => ?_)
  have hdnonneg : 0 ≤ D (ρ : ℂ) := by
    dsimp [D]
    exact xi_divisor_nonneg Set.univ (ρ : ℂ)
  have hdne : D (ρ : ℂ) ≠ 0 := Function.mem_support.mp ρ.2
  have hd : 1 ≤ D (ρ : ℂ) := by omega
  have hdR : (1 : ℝ) ≤ (D (ρ : ℂ) : ℝ) := by exact_mod_cast hd
  change ‖lam ρ‖ ≤ ‖((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by exact_mod_cast hdnonneg)]
  nlinarith [norm_nonneg (lam ρ)]

/-- The centered reciprocal-square spectrum tends to zero off a finite set. -/
theorem xi_central_reciprocal_square_tendsto_cofinite_zero :
    Filter.Tendsto
      (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
        xiCentralReciprocalSquare (ρ : ℂ))
      Filter.cofinite (nhds 0) :=
  xi_central_reciprocal_square_unweighted_summable.tendsto_cofinite_zero

/-- Only finitely many centered spectral coordinates have norm at least any fixed positive radius. -/
theorem xi_central_reciprocal_square_finite_norm_ge {r : ℝ} (hr : 0 < r) :
    {ρ : ↥(MeromorphicOn.divisor xi Set.univ).support |
      r ≤ ‖xiCentralReciprocalSquare (ρ : ℂ)‖}.Finite := by
  have hev : ∀ᶠ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support in Filter.cofinite,
      xiCentralReciprocalSquare (ρ : ℂ) ∈ Metric.ball 0 r :=
    xi_central_reciprocal_square_tendsto_cofinite_zero
      (Metric.ball_mem_nhds 0 hr)
  have hfinite := Filter.mem_cofinite.mp (Filter.eventually_iff.mp hev)
  simpa only [Set.compl_setOf, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right,
    not_lt] using hfinite

@[simp] theorem xiCentralReciprocalSquare_one_sub (ρ : ℂ) :
    xiCentralReciprocalSquare (1 - ρ) = xiCentralReciprocalSquare ρ := by
  simp only [xiCentralReciprocalSquare]
  rw [show 1 - ρ - 1 / 2 = -(ρ - 1 / 2) by ring, inv_neg]
  ring

@[simp] theorem xiCentralReciprocalSquare_conj (ρ : ℂ) :
    xiCentralReciprocalSquare ((starRingEnd ℂ) ρ) =
      (starRingEnd ℂ) (xiCentralReciprocalSquare ρ) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.conj_ofReal]
  rw [xiCentralReciprocalSquare, xiCentralReciprocalSquare, map_neg, map_pow,
    map_inv₀, map_sub, hhalf]

/-- Every positive-order centered reciprocal-square divisor moment is absolutely summable. -/
theorem xi_central_reciprocal_moment_summable (n : ℕ) :
    Summable (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
        xiCentralReciprocalSquare (ρ : ℂ) ^ (n + 1)) := by
  classical
  set D := MeromorphicOn.divisor xi Set.univ with hD
  set lam : ↥D.support → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ) with hlam
  set base : ↥D.support → ℂ := fun ρ => ((D (ρ : ℂ) : ℝ) : ℂ) * lam ρ with hbase
  have hbase_sum : Summable base := by
    simpa only [base, lam, hD] using xi_central_reciprocal_square_summable
  have hLF : LocallyFiniteSupport D.toFun := Function.locallyFinsupp.locallyFiniteSupport D
  have hnear : {ρ : ↥D.support | ‖(ρ : ℂ) - 1 / 2‖ < 1}.Finite := by
    apply Set.Finite.of_finite_image _ (Subtype.val_injective.injOn)
    apply Set.Finite.subset
      (hLF.finite_inter_support_of_isCompact (isCompact_closedBall (1 / 2 : ℂ) 1))
    rintro z ⟨ρ, hρ, rfl⟩
    change ‖(ρ : ℂ) - 1 / 2‖ < 1 at hρ
    exact ⟨by simpa [mem_closedBall, dist_eq_norm] using le_of_lt hρ, ρ.2⟩
  refine hbase_sum.norm.of_norm_bounded_eventually (by
    filter_upwards [hnear.eventually_cofinite_notMem] with ρ hρ
    simp only [not_lt] at hρ
    have hzinv : ‖((ρ : ℂ) - 1 / 2)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hρ)).2 hρ
    have hlamle : ‖lam ρ‖ ≤ 1 := by
      change ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ≤ 1
      simp only [xiCentralReciprocalSquare, norm_neg, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hzinv
    rw [norm_mul, norm_pow, hbase, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hlamle))

/-- The fixed target-free centered reciprocal moment sequence of the actual xi divisor. -/
def xiCentralReciprocalMoment (n : ℕ) : ℂ :=
  ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
    (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
      xiCentralReciprocalSquare (ρ : ℂ) ^ (n + 1)

/-- Conjugation preserves the actual xi divisor with multiplicity. -/
theorem xi_divisor_conj (z : ℂ) :
    (MeromorphicOn.divisor xi Set.univ) ((starRingEnd ℂ) z) =
      (MeromorphicOn.divisor xi Set.univ) z := by
  rw [xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ _),
    xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ _), xi_orderAt_conj]

/-- Conjugation as an involution of the multiplicity-bearing xi zero support. -/
def xiZeroConjEquiv :
    ↥(MeromorphicOn.divisor xi Set.univ).support ≃
      ↥(MeromorphicOn.divisor xi Set.univ).support where
  toFun ρ := ⟨(starRingEnd ℂ) (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_conj]
    exact Function.mem_support.mp ρ.2⟩
  invFun ρ := ⟨(starRingEnd ℂ) (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_conj]
    exact Function.mem_support.mp ρ.2⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

/-- Every centered reciprocal moment is real, unconditionally, by conjugation of the xi divisor. -/
theorem xiCentralReciprocalMoment_conj (n : ℕ) :
    (starRingEnd ℂ) (xiCentralReciprocalMoment n) = xiCentralReciprocalMoment n := by
  let term : ↥(MeromorphicOn.divisor xi Set.univ).support → ℂ := fun ρ =>
    (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
      xiCentralReciprocalSquare (ρ : ℂ) ^ (n + 1)
  change (starRingEnd ℂ) (∑' ρ, term ρ) = ∑' ρ, term ρ
  rw [Complex.conj_tsum]
  calc
    (∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
        (starRingEnd ℂ) (term ρ)) =
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, term (xiZeroConjEquiv ρ) := by
        apply tsum_congr
        intro ρ
        change (starRingEnd ℂ)
            ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
              xiCentralReciprocalSquare (ρ : ℂ) ^ (n + 1)) =
          (((MeromorphicOn.divisor xi Set.univ) ((starRingEnd ℂ) (ρ : ℂ)) : ℝ) : ℂ) *
            xiCentralReciprocalSquare ((starRingEnd ℂ) (ρ : ℂ)) ^ (n + 1)
        simp only [map_mul, map_pow, Complex.conj_ofReal]
        rw [← xiCentralReciprocalSquare_conj, xi_divisor_conj]
    _ = ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, term ρ :=
      xiZeroConjEquiv.tsum_eq term

theorem xiCentralReciprocalMoment_im_eq_zero (n : ℕ) :
    (xiCentralReciprocalMoment n).im = 0 :=
  Complex.conj_eq_iff_im.mp (xiCentralReciprocalMoment_conj n)

/-- Membership in the xi divisor support is an actual xi zero. -/
theorem xi_eq_zero_of_mem_divisor_support
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : xi (ρ : ℂ) = 0 := by
  by_contra hne
  have hord : analyticOrderAt xi (ρ : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hne)
  have hdiv : (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) = 0 := by
    rw [xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ _), hord]
    simp
  exact (Function.mem_support.mp ρ.2) hdiv

/-- Every xi zero belongs to the actual xi divisor support. -/
theorem mem_xi_divisor_support_of_eq_zero {ρ : ℂ} (hzero : xi ρ = 0) :
    ρ ∈ (MeromorphicOn.divisor xi Set.univ).support := by
  have hset := xi_analyticOnNhd_univ.meromorphicNFOn.zero_set_eq_divisor_support
    (fun u => by
      rw [(xi_analyticOnNhd_univ (u : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
      exact WithTop.map_eq_top_iff.not.mpr (xi_orderAt_ne_top (u : ℂ)))
  change ρ ∈ Function.support (MeromorphicOn.divisor xi Set.univ)
  rw [← hset]
  exact ⟨Set.mem_univ _, by simpa using hzero⟩

/-- The centre `1/2` is not in the actual xi divisor support. -/
theorem xi_divisor_support_ne_half
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    (ρ : ℂ) ≠ 1 / 2 := by
  have hzero := xi_eq_zero_of_mem_divisor_support ρ
  have hxipos : 0 < (xi ((1 / 2 : ℝ) : ℂ)).re :=
    xi_pos_on_real_anchor (by norm_num) (by norm_num)
  intro hρ
  rw [hρ] at hzero
  have : xi ((1 / 2 : ℝ) : ℂ) = 0 := by simpa using hzero
  rw [this] at hxipos
  simp at hxipos

/-- Every point of the actual xi divisor support lies strictly inside the critical strip. -/
theorem xi_divisor_support_re_mem_open_unit
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
  have hzero := xi_eq_zero_of_mem_divisor_support ρ
  constructor
  · by_contra hpos
    have hreflect : xi (1 - (ρ : ℂ)) = 0 := by rw [xi_one_sub, hzero]
    exact xi_ne_zero_of_one_le_re (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      hreflect
  · by_contra hlt
    exact xi_ne_zero_of_one_le_re (not_lt.mp hlt) hzero

/-- The actual xi divisor has no real point; its centered spectral coordinates therefore never
come from the degenerate negative-real branch. -/
theorem xi_divisor_support_im_ne_zero
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    (ρ : ℂ).im ≠ 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  have hzero := xi_eq_zero_of_mem_divisor_support ρ
  intro him
  have hρreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hpos := xi_pos_on_real_anchor hstrip.1 hstrip.2
  rw [hρreal] at hzero
  rw [hzero] at hpos
  simp at hpos

/-- No centered reciprocal-square spectral coordinate of the xi divisor vanishes. -/
theorem xiCentralReciprocalSquare_ne_zero
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    xiCentralReciprocalSquare (ρ : ℂ) ≠ 0 := by
  rw [xiCentralReciprocalSquare]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero (sub_ne_zero.mpr
    (xi_divisor_support_ne_half ρ))))

/-- Exact imaginary part of the centered reciprocal-square coordinate. -/
theorem xiCentralReciprocalSquare_im (ρ : ℂ) :
    (xiCentralReciprocalSquare ρ).im =
      2 * (ρ.re - 1 / 2) * ρ.im / Complex.normSq (ρ - 1 / 2) ^ 2 := by
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [xiCentralReciprocalSquare, hhalf]
  simp only [neg_im, pow_two, mul_im, Complex.inv_re, Complex.inv_im,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

/-- A centered xi-divisor coordinate is real exactly when its zero lies on the critical line. -/
theorem xiCentralReciprocalSquare_im_eq_zero_iff
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    (xiCentralReciprocalSquare (ρ : ℂ)).im = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [xiCentralReciprocalSquare_im]
  have hden : Complex.normSq ((ρ : ℂ) - 1 / 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact ne_of_gt (Complex.normSq_pos.mpr (sub_ne_zero.mpr
      (xi_divisor_support_ne_half ρ)))
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hbad
    · have him := xi_divisor_support_im_ne_zero ρ
      rcases mul_eq_zero.mp hnum with hre | him0
      · linarith
      · exact (him him0).elim
    · exact (hden hbad).elim
  · intro hre
    rw [hre]
    ring

/-- On the critical line the centered reciprocal-square coordinate is the positive number
`1 / Im(rho)^2`. -/
theorem xiCentralReciprocalSquare_pos_real_of_re_eq_half
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support)
    (hre : (ρ : ℂ).re = 1 / 2) :
    ∃ x : ℝ, 0 < x ∧ xiCentralReciprocalSquare (ρ : ℂ) = (x : ℂ) := by
  have him := xi_divisor_support_im_ne_zero ρ
  have hcoord : (ρ : ℂ) - 1 / 2 = (((ρ : ℂ).im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [hre]
    · simp
  refine ⟨1 / (ρ : ℂ).im ^ 2, by positivity, ?_⟩
  rw [xiCentralReciprocalSquare, hcoord]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- Under RH every point of the actual xi divisor support lies on the critical line. -/
theorem xi_divisor_support_re_eq_half_of_rh (hRH : RiemannHypothesis)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    (ρ : ℂ).re = 1 / 2 := by
  have hzero := xi_eq_zero_of_mem_divisor_support ρ
  have hright := rh_iff_xi_ne_zero_right.mp hRH
  by_contra hne
  rcases lt_or_gt_of_ne hne with hleft | hright'
  · let w : ℂ := 1 - (starRingEnd ℂ) (ρ : ℂ)
    have hwmem : w ∈ rightHalf := by
      rw [mem_rightHalf]
      dsimp [w]
      linarith
    have hwzero : xi w = 0 := by
      dsimp [w]
      rw [xi_one_sub, xi_conj, hzero, map_zero]
    exact hright w hwmem hwzero
  · exact hright (ρ : ℂ) (mem_rightHalf.mpr hright') hzero

/-- Under RH each centered reciprocal-square spectral coordinate is a positive real number. -/
theorem xiCentralReciprocalSquare_pos_real_of_rh (hRH : RiemannHypothesis)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    ∃ x : ℝ, 0 < x ∧ xiCentralReciprocalSquare (ρ : ℂ) = (x : ℂ) := by
  exact xiCentralReciprocalSquare_pos_real_of_re_eq_half ρ
    (xi_divisor_support_re_eq_half_of_rh hRH ρ)

end

end RHTower
