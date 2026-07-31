import GaloisForLFunctions.RHTower.PrimeArchBernsteinPencil
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Exponential phase selection for the prime--Gamma Bernstein pencil

The endpoint Bernstein coefficient vector is an entirely source-defined object.  This file
develops the exponential-separation mechanism that distinguishes its RH phase from its off-line
phase.  The geometric input is elementary: every nonreal normalized reciprocal-square coordinate
has a unit-disk direction in which its affine Bernstein base has modulus strictly larger than one.
-/

open Filter Topology Complex
open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

/-- Unit-circle phase aligning `u * w` with `1 - u`. -/
def bernsteinEllipsePhase (u : ℂ) : ℂ :=
  (starRingEnd ℂ u) / (‖u‖ : ℂ) * ((1 - u) / (‖1 - u‖ : ℂ))

lemma bernsteinEllipsePhase_norm_eq_one {u : ℂ} (him : u.im ≠ 0) :
    ‖bernsteinEllipsePhase u‖ = 1 := by
  have hu : u ≠ 0 := by
    intro h
    rw [h] at him
    exact him rfl
  have hsub : 1 - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at him
    exact him rfl
  rw [bernsteinEllipsePhase, norm_mul, norm_div, norm_div,
    norm_conj, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u), abs_of_nonneg (norm_nonneg (1 - u))]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hsub]

/-- A nonreal point lies strictly outside the degenerate focal segment: the sum of its distances
from `0` and `1` is greater than one. -/
lemma one_lt_norm_add_norm_one_sub {u : ℂ} (him : u.im ≠ 0) :
    1 < ‖u‖ + ‖1 - u‖ := by
  have hnormSq : u.re ^ 2 < ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_pos_of_ne_zero him]
  have hstrict : |u.re| < ‖u‖ := by
    nlinarith [sq_abs u.re, norm_nonneg u, abs_nonneg u.re]
  have hother : |1 - u.re| ≤ ‖1 - u‖ := by
    simpa only [sub_re, one_re] using abs_re_le_norm (1 - u)
  have hone : 1 ≤ |u.re| + |1 - u.re| := by
    have := abs_add_le u.re (1 - u.re)
    norm_num at this ⊢
    linarith
  linarith

/-- **Strict Bernstein ellipse direction.** Every nonreal normalized coordinate admits a unit
phase for which its affine Bernstein base has modulus `‖u‖ + ‖1-u‖ > 1`. -/
theorem exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero
    {u : ℂ} (him : u.im ≠ 0) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ‖1 - u + u * w‖ = ‖1 - u‖ + ‖u‖ ∧
      1 < ‖1 - u + u * w‖ := by
  let w := bernsteinEllipsePhase u
  have hnorm : ‖1 - u + u * w‖ = ‖1 - u‖ + ‖u‖ := by
    have hu : u ≠ 0 := by
      intro h
      rw [h] at him
      exact him rfl
    have hsub : 1 - u ≠ 0 := by
      intro h
      have hu1 : u = 1 := (sub_eq_zero.mp h).symm
      rw [hu1] at him
      exact him rfl
    have halign :
        u * w = ((‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) := by
      dsimp only [w, bernsteinEllipsePhase]
      rw [show u * ((starRingEnd ℂ u / (‖u‖ : ℂ)) *
          ((1 - u) / (‖1 - u‖ : ℂ))) =
          (u * starRingEnd ℂ u / (‖u‖ : ℂ)) *
            ((1 - u) / (‖1 - u‖ : ℂ)) by ring]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hsub]
    rw [halign]
    rw [show 1 - u + ((‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) =
        (((1 : ℝ) + ‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) by
          push_cast
          ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · field_simp [norm_ne_zero_iff.mpr hsub]
    · have : 0 < ‖1 - u‖ := norm_pos_iff.mpr hsub
      positivity
  refine ⟨w, bernsteinEllipsePhase_norm_eq_one him, hnorm, ?_⟩
  rw [hnorm]
  simpa [add_comm] using one_lt_norm_add_norm_one_sub him

end

end RHTower

namespace RHTower

noncomputable section

/-- A nonnegative sequence is subexponential when it vanishes after normalization by every
strictly exponential scale. This root-free formulation is the one needed by the Bernstein
pencil. -/
def SubexponentialAtNatInfinity (a : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 1 < r → Tendsto (fun n : ℕ => a n / r ^ n) atTop (nhds 0)

/-- The affine mode attached to one reciprocal-square divisor copy in the Bernstein pencil. -/
def xiBernsteinAffineBase (R : ℝ) (w : ℂ) (q : XiZeroCopy) : ℂ :=
  1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
    (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w

/-- The affine Bernstein modes converge cofinally to the neutral base `1`. -/
theorem xiBernsteinAffineBase_tendsto_cofinite_one
    (R : ℝ) (w : ℂ) :
    Tendsto (xiBernsteinAffineBase R w) cofinite (nhds 1) := by
  have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
    summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
  have hscaled : Tendsto
      (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q / (R : ℂ))
      cofinite (nhds 0) := by
    simpa using hzero.div_const (R : ℂ)
  have hone : Tendsto (fun _ : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have h := (hone.sub hscaled).add (hscaled.mul_const w)
  change Tendsto
    (fun q : XiZeroCopy =>
      1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
        xiZeroCopyReciprocalSquare q / (R : ℂ) * w)
    cofinite (nhds 1)
  simpa using h

/-- Above every threshold larger than one, only finitely many affine Bernstein modes remain. -/
theorem xiBernsteinAffineBase_finite_norm_ge
    (R : ℝ) (w : ℂ) {a : ℝ} (ha : 1 < a) :
    {q : XiZeroCopy | a ≤ ‖xiBernsteinAffineBase R w q‖}.Finite := by
  have hevent : ∀ᶠ q : XiZeroCopy in cofinite,
      ‖xiBernsteinAffineBase R w q‖ < a :=
    (xiBernsteinAffineBase_tendsto_cofinite_one R w).norm.eventually_lt_const
      (by simpa using ha)
  rw [Filter.eventually_cofinite] at hevent
  simpa only [not_lt] using hevent

/-- At nonzero scale and nontrivial phase, the affine Bernstein base determines its
reciprocal-square coefficient. -/
theorem xiBernsteinAffineBase_eq_iff
    {R : ℝ} (hR : R ≠ 0) {w : ℂ} (hw : w ≠ 1) (q q' : XiZeroCopy) :
    xiBernsteinAffineBase R w q = xiBernsteinAffineBase R w q' ↔
      xiZeroCopyReciprocalSquare q = xiZeroCopyReciprocalSquare q' := by
  constructor
  · intro h
    have hprod :
        (xiZeroCopyReciprocalSquare q - xiZeroCopyReciprocalSquare q') *
          (w - 1) = 0 := by
      dsimp only [xiBernsteinAffineBase] at h
      field_simp [hR] at h
      linear_combination h
    have hdiff := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hw)
    exact sub_eq_zero.mp hdiff
  · intro h
    simp only [xiBernsteinAffineBase, h]

/-- Failure of RH supplies an actual multiplicity copy with nonreal reciprocal-square
coordinate. -/
theorem exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
  have hright : ¬ ∀ s : ℂ, s ∈ rightHalf → xi s ≠ 0 := by
    exact hRH ∘ rh_iff_xi_ne_zero_right.mpr
  push Not at hright
  obtain ⟨s, hs, hzero⟩ := hright
  let ρ : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hnat : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hnat⟩⟩
  refine ⟨q, ?_⟩
  rw [xiZeroCopyReciprocalSquare_eq]
  intro him
  have hre := (xiCentralReciprocalSquare_im_eq_zero_iff ρ).mp him
  have hgt := mem_rightHalf.mp hs
  dsimp only [ρ] at hre
  linarith

end

end RHTower

namespace RHTower

noncomputable section

/-- **Off-line exponential-phase law.** At every positive normalization radius, failure of RH
forces one unit-circle direction in which the complete source-defined Xi Bernstein pencil has a
strictly exponential surviving mode. The conclusion is cancellation-resistant: it concerns the
full multiplicity-exact infinite pencil, not one isolated zero. -/
theorem exists_unit_xiCentralBernsteinPencil_not_subexponential_of_not_riemannHypothesis
    {R : ℝ} (hR : 0 < R) (hRH : ¬ RiemannHypothesis) :
    ∃ w : ℂ, ∃ r : ℝ, ‖w‖ = 1 ∧ 1 < r ∧
      ¬ Tendsto
        (fun n : ℕ => xiCentralBernsteinPencil R n w / (r : ℂ) ^ n)
        atTop (nhds 0) := by
  classical
  obtain ⟨q₀, hq₀im⟩ :=
    exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis hRH
  let u₀ : ℂ := xiZeroCopyReciprocalSquare q₀ / (R : ℂ)
  have hu₀im : u₀.im ≠ 0 := by
    dsimp only [u₀]
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
      Complex.normSq_ofReal]
    exact div_ne_zero (mul_ne_zero hq₀im hR.ne') (mul_ne_zero hR.ne' hR.ne')
  obtain ⟨w, hw, hbaseEq, hbaseGt⟩ :=
    exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero hu₀im
  have hq₀base :
      xiBernsteinAffineBase R w q₀ = 1 - u₀ + u₀ * w := by
    rfl
  have ha : 1 < ‖xiBernsteinAffineBase R w q₀‖ := by
    rw [hq₀base]
    exact hbaseGt
  have hw1 : w ≠ 1 := by
    intro hw1
    rw [hw1] at ha
    simp [xiBernsteinAffineBase] at ha
  let S : Finset XiZeroCopy :=
    (xiBernsteinAffineBase_finite_norm_ge R w ha).toFinset
  have hq₀S : q₀ ∈ S := by
    simp only [S, Set.Finite.mem_toFinset]
    show ‖xiBernsteinAffineBase R w q₀‖ ≤ ‖xiBernsteinAffineBase R w q₀‖
    exact le_rfl
  have hSne : S.Nonempty := ⟨q₀, hq₀S⟩
  obtain ⟨qmax, hqmaxS, hmax⟩ :=
    Finset.exists_max_image S (fun q => ‖xiBernsteinAffineBase R w q‖) hSne
  let r : ℝ := ‖xiBernsteinAffineBase R w qmax‖
  have haqmax : ‖xiBernsteinAffineBase R w q₀‖ ≤ r := hmax q₀ hq₀S
  have hr : 0 < r := lt_trans (by norm_num : (0 : ℝ) < 1) (ha.trans_le haqmax)
  have hrone : 1 < r := ha.trans_le haqmax
  let D : Finset XiZeroCopy :=
    S.filter (fun q => ‖xiBernsteinAffineBase R w q‖ = r)
  have hqmaxD : qmax ∈ D := by
    simp only [D, Finset.mem_filter]
    exact ⟨hqmaxS, rfl⟩
  have hdom : ∀ q ∈ D, ‖xiBernsteinAffineBase R w q‖ = r := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hsub : ∀ q ∉ D, ‖xiBernsteinAffineBase R w q‖ < r := by
    intro q hqD
    by_cases hqS : q ∈ S
    · have hle := hmax q hqS
      apply lt_of_le_of_ne hle
      intro heq
      exact hqD (Finset.mem_filter.mpr ⟨hqS, heq⟩)
    · have hlt : ‖xiBernsteinAffineBase R w q‖ <
          ‖xiBernsteinAffineBase R w q₀‖ := by
        apply lt_of_not_ge
        intro hge
        apply hqS
        simp only [S, Set.Finite.mem_toFinset]
        exact hge
      exact hlt.trans_le haqmax
  let c : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  let b : XiZeroCopy → ℂ := xiBernsteinAffineBase R w
  let z : XiZeroCopy → ℂ := fun q => b q / (r : ℂ)
  have hfiber : ∃ v ∈ D.image z,
      finiteExponentialFiberCoefficient D c z v ≠ 0 := by
    refine ⟨z qmax, Finset.mem_image.mpr ⟨qmax, hqmaxD, rfl⟩, ?_⟩
    let F : Finset XiZeroCopy := D.filter (fun q => z q = z qmax)
    have hqmaxF : qmax ∈ F := by
      simp [F, hqmaxD]
    have hconst : ∀ q ∈ F, c q = c qmax := by
      intro q hqF
      have hz := (Finset.mem_filter.mp hqF).2
      have hb : b q = b qmax := by
        exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
          ((div_eq_div_iff (Complex.ofReal_ne_zero.mpr hr.ne')
            (Complex.ofReal_ne_zero.mpr hr.ne')).mp hz)
      exact (xiBernsteinAffineBase_eq_iff hR.ne' hw1 q qmax).mp hb
    have hcard : ((F.card : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨qmax, hqmaxF⟩))
    have hcmax : c qmax ≠ 0 := by
      dsimp only [c]
      rw [xiZeroCopyReciprocalSquare_eq]
      exact xiCentralReciprocalSquare_ne_zero qmax.1
    rw [finiteExponentialFiberCoefficient]
    change (∑ q ∈ F, c q) ≠ 0
    rw [Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul]
    exact mul_ne_zero hcard hcmax
  have hnotTsum :=
    not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset
      c b summable_xiZeroCopyReciprocalSquare D hr hdom hsub hfiber
  have heq (n : ℕ) :
      (∑' q : XiZeroCopy, c q * (b q / (r : ℂ)) ^ n) =
        xiCentralBernsteinPencil R n w / (r : ℂ) ^ n := by
    rw [show (∑' q : XiZeroCopy, c q * (b q / (r : ℂ)) ^ n) =
        (∑' q : XiZeroCopy, c q * b q ^ n) / (r : ℂ) ^ n by
      simp_rw [div_pow, div_eq_mul_inv]
      rw [show (fun q : XiZeroCopy =>
          c q * (b q ^ n * ((r : ℂ) ^ n)⁻¹)) =
          fun q : XiZeroCopy => (c q * b q ^ n) * ((r : ℂ) ^ n)⁻¹ by
            funext q
            ring]
      rw [tsum_mul_right]]
    rfl
  refine ⟨w, r, hw, hrone, ?_⟩
  intro hpencil
  apply hnotTsum
  exact hpencil.congr' (Eventually.of_forall fun n => (heq n).symm)

end

end RHTower

namespace RHTower

noncomputable section

/-- The endpoint total variation of the canonical prime--Gamma Bernstein coefficient vector. -/
def primeArchEndpointBernsteinTotalVariation (n : ℕ) : ℝ :=
  bernsteinCoefficientL1
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n

/-- **Subexponential Bernstein phase criterion.** RH is equivalent to the genuinely weaker
asymptotic requirement that the entirely source-defined endpoint Bernstein total variation grow
more slowly than every exponential. Under failure of RH, an off-line reciprocal-square atom
creates a unit-disk pencil direction with a surviving base of modulus greater than one; the total
variation dominates that pencil and therefore cannot be subexponential. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential :
    RiemannHypothesis ↔
      SubexponentialAtNatInfinity primeArchEndpointBernsteinTotalVariation := by
  constructor
  · intro hRH r hr
    have hpow : Tendsto (fun n : ℕ => (r⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr (le_trans (by norm_num) hr.le))
        (inv_lt_one_of_one_lt₀ hr)
    have htarget : Tendsto
        (fun n : ℕ => normalizedPrimeArchMoment 0 * (r⁻¹) ^ n)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow
    have heq :
        (fun n : ℕ => normalizedPrimeArchMoment 0 * (r⁻¹) ^ n) =ᶠ[atTop]
          (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n) := by
      filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
      have hL1 :=
        riemannHypothesis_iff_forall_primeArchBernsteinCoefficientL1_eq_mass.mp hRH
          (n - 1)
      have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [hindex] at hL1
      rw [primeArchEndpointBernsteinTotalVariation, hL1]
      simp only [div_eq_mul_inv, inv_pow]
    exact htarget.congr' heq
  · intro hsub
    by_contra hRH
    obtain ⟨w, r, hw, hr, hnot⟩ :=
      exists_unit_xiCentralBernsteinPencil_not_subexponential_of_not_riemannHypothesis
        primeArchEndpointHausdorffRadius_pos hRH
    have hbound (n : ℕ) :
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ ≤
          primeArchEndpointBernsteinTotalVariation n := by
      rw [← bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil]
      exact norm_bernsteinCoefficientTransform_le_l1 _ _ hw.le
    have hpencil : Tendsto
        (fun n : ℕ => xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w /
          (r : ℂ) ^ n) atTop (nhds 0) := by
      apply squeeze_zero_norm'
        (a := fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      · exact Eventually.of_forall fun n => by
          have hrpos : 0 < r := lt_trans zero_lt_one hr
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hrpos]
          exact div_le_div_of_nonneg_right (hbound n) (pow_nonneg hrpos.le n)
      · exact hsub r hr
    exact hnot hpencil

end

end RHTower
