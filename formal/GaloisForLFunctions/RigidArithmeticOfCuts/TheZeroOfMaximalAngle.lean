import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniSource
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip
import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RigidArithmeticOfCuts.RotatedRelationsNeedNonvanishingCoefficients
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The zero of maximal angle

Put `Q(z²) = Ξ(z)`, with `Ξ(z) = ξ(½ + iz)`. The zeros of `Q` are `w = α²` for the spectral points
`α = (ρ − ½)(−i)`. They lie in the sector `|arg w| ≤ π/3`, and RH says they are all positive.

Unlike the top of the horizontal strip, **the maximal angle is always attained**: `arg w ≈ 2d/γ → 0`
along the zeros, so under `¬RH` there is a zero `w₀` with `Im w₀ > 0` and maximal argument.

At `w₀` every Hadamard factor points the same way. With `u = w₀/w`, `Im u ≥ 0` for every zero `w`, and
`‖1 − t u‖² − ‖1 − t̄ u‖² = 4 Im t Im u`. So `t ↦ Q(t w₀)` is of **Hermite–Biehler class**: its zeros lie
in the closed lower half-plane, one of them at `t = 1` on the boundary, and `‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖`
for `Im t > 0`. This is a statement of extremal position: it uses Hadamard's product and no form.

Consequently RH holds iff `‖Q(t w)‖ = ‖Q(t̄ w)‖` at every zero, for one fixed `t` off the real axis, and
any relation `a Q(t·) + b Q(t̄·) = 0` on the zeros with balanced coefficients nonvanishing there implies
RH.
-/

open Complex Filter Topology RHTower

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The function `Q` with `Q(z²) = Ξ(z)`. -/
abbrev squaredXi : ℂ → ℂ := xiSquaredSeamEntireQuotient

theorem squaredXi_sq (z : ℂ) : squaredXi (z ^ 2) = XiC z := xiSquaredSeamEntireQuotient_sq z

/-- The zero `w = α²` of `Q` attached to a multiplicity copy. -/
def zeroSq (q : XiZeroCopy) : ℂ := xiSpectralPoint q ^ 2

theorem zeroSq_re (q : XiZeroCopy) :
    (zeroSq q).re = (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 := by
  simp [zeroSq, pow_two, Complex.mul_re]

theorem zeroSq_im (q : XiZeroCopy) :
    (zeroSq q).im = 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
  simp [zeroSq, pow_two, Complex.mul_im]
  ring

/-- Every spectral point lies in the cone `3 c² ≤ a²`. -/
theorem three_mul_im_sq_le (q : XiZeroCopy) :
    3 * (xiSpectralPoint q).im ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
  have h := sqrt3Cone_centre q
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint, Complex.mul_re]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint, Complex.mul_im]
  rw [hre, him]
  linarith [neg_sq ((q.1 : ℂ).re - 1 / 2)]

theorem spectral_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  intro h
  have h1 := three_mul_im_sq_le q
  rw [h] at h1
  have h2 : (xiSpectralPoint q).im = 0 := by nlinarith [sq_nonneg (xiSpectralPoint q).im]
  exact xiSpectralPoint_ne_zero q (Complex.ext h h2)

/-- The zeros of `Q` lie in the right half-plane. -/
theorem zeroSq_re_pos (q : XiZeroCopy) : 0 < (zeroSq q).re := by
  have h1 := three_mul_im_sq_le q
  have h2 : 0 < (xiSpectralPoint q).re ^ 2 := by
    have := spectral_re_ne_zero q
    positivity
  rw [zeroSq_re]
  nlinarith [sq_nonneg (xiSpectralPoint q).im]

theorem zeroSq_ne_zero (q : XiZeroCopy) : zeroSq q ≠ 0 := fun h => by
  have := zeroSq_re_pos q
  rw [h] at this
  simp at this

/-- **The zeros of `Q`.** -/
theorem squaredXi_eq_zero_iff (w : ℂ) : squaredXi w = 0 ↔ ∃ q : XiZeroCopy, zeroSq q = w := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
    rw [← hz, squaredXi_sq] at h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
    exact ⟨q, by rw [zeroSq, hq, hz]⟩
  · rintro ⟨q, rfl⟩
    rw [zeroSq, squaredXi_sq]
    exact XiC_xiSpectralPoint_eq_zero q

/-- `Ξ` has real Taylor coefficients. -/
theorem XiC_conj (z : ℂ) : XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) := by
  rw [XiC, XiC]
  have harg : 1 / 2 + (starRingEnd ℂ) z * I = 1 - (starRingEnd ℂ) (1 / 2 + z * I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [harg, xi_one_sub, xi_conj]

/-- `Q` has real Taylor coefficients. -/
theorem squaredXi_conj (w : ℂ) : squaredXi ((starRingEnd ℂ) w) = (starRingEnd ℂ) (squaredXi w) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  rw [← hz, map_pow, squaredXi_sq, squaredXi_sq, XiC_conj]

theorem zeroSq_conjEquiv (q : XiZeroCopy) :
    zeroSq (xiZeroCopyConjEquiv q) = (starRingEnd ℂ) (zeroSq q) := by
  rw [zeroSq, zeroSq, xiSpectralPoint_conjEquiv, neg_sq, map_pow]

/-! ### The Hadamard product in the squared variable -/

/-- The genus-zero factor of `Q`. -/
def sqFactor (w : ℂ) (q : XiZeroCopy) : ℂ := 1 - w / zeroSq q

private lemma weierstrass_pair (x : ℂ) : weierstrassE1 x * weierstrassE1 (-x) = 1 - x ^ 2 := by
  unfold weierstrassE1
  have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc (1 - x) * Complex.exp x * ((1 - -x) * Complex.exp (-x))
      = (1 - x) * (1 + x) * (Complex.exp x * Complex.exp (-x)) := by ring
    _ = 1 - x ^ 2 := by rw [hexp]; ring

private lemma sqFactor_eq {z w : ℂ} (hz : z ^ 2 = w) (q : XiZeroCopy) :
    weierstrassE1 (z / xiSpectralPoint q) * weierstrassE1 (-z / xiSpectralPoint q) = sqFactor w q := by
  rw [neg_div, weierstrass_pair, sqFactor, zeroSq, div_pow, hz]

/-- The genus-zero product converges. -/
theorem multipliable_sqFactor (w : ℂ) : Multipliable (sqFactor w) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  have h := (xiCanonicalProduct_multipliable z).mul (xiCanonicalProduct_multipliable (-z))
  exact h.congr fun q => sqFactor_eq hz q

/-- **Hadamard's product for `Q²`.** All copies occur, and `α`, `−α` give the same factor, so the
product carries each functional-equation orbit twice. -/
theorem squaredXi_sq_eq (w : ℂ) : squaredXi w ^ 2 = XiC 0 ^ 2 * ∏' q, sqFactor w q := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  have h1 := congrFun XiC_eq_constant_mul_canonicalProduct z
  have h2 := congrFun XiC_eq_constant_mul_canonicalProduct (-z)
  simp only [Pi.mul_apply] at h1 h2
  rw [XiC_even] at h2
  have hprod : ∏' q, sqFactor w q = xiCanonicalProduct z * xiCanonicalProduct (-z) := by
    rw [xiCanonicalProduct, canonicalProductE1Indexed, canonicalProductE1Indexed,
      ← (xiCanonicalProduct_multipliable z).tprod_mul (xiCanonicalProduct_multipliable (-z))]
    exact tprod_congr fun q => (sqFactor_eq hz q).symm
  rw [hprod, ← hz, squaredXi_sq]
  calc XiC z ^ 2 = XiC z * XiC z := pow_two _
    _ = (XiC 0 * xiCanonicalProduct z) * (XiC 0 * xiCanonicalProduct (-z)) := by
        rw [← h1]
        nth_rewrite 2 [h2]
        rfl
    _ = _ := by ring

/-! ### Comparing infinite products -/

private lemma hasProd_tendsto {ι : Type*} {a : ι → ℂ} (ha : Multipliable a) :
    Tendsto (fun s : Finset ι => ∏ i ∈ s, ‖a i‖) atTop (𝓝 ‖∏' i, a i‖) := by
  have h : Tendsto (fun s : Finset ι => ∏ i ∈ s, a i) atTop (𝓝 (∏' i, a i)) := ha.hasProd
  simpa only [norm_prod] using h.norm

/-- Termwise domination passes to the product. -/
theorem norm_tprod_le_norm_tprod {ι : Type*} {a b : ι → ℂ} (ha : Multipliable a)
    (hb : Multipliable b) (h : ∀ i, ‖b i‖ ≤ ‖a i‖) : ‖∏' i, b i‖ ≤ ‖∏' i, a i‖ :=
  le_of_tendsto_of_tendsto' (hasProd_tendsto hb) (hasProd_tendsto ha) fun _ =>
    Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => h i

/-- One strict factor gives a strict inequality, provided the larger product is nonzero. -/
theorem norm_tprod_lt_norm_tprod {ι : Type*} [DecidableEq ι] {a b : ι → ℂ} (ha : Multipliable a)
    (hb : Multipliable b) (h : ∀ i, ‖b i‖ ≤ ‖a i‖) {i₀ : ι} (hi : ‖b i₀‖ < ‖a i₀‖)
    (hA : ∏' i, a i ≠ 0) : ‖∏' i, b i‖ < ‖∏' i, a i‖ := by
  have hpos : 0 < ‖a i₀‖ := lt_of_le_of_lt (norm_nonneg _) hi
  set r : ℝ := ‖b i₀‖ / ‖a i₀‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one hpos).mpr hi
  have hprod : HasProd (fun i => a i * if i = i₀ then (r : ℂ) else 1) ((∏' i, a i) * (r : ℂ)) :=
    ha.hasProd.mul (hasProd_ite_eq i₀ (r : ℂ))
  have hle := norm_tprod_le_norm_tprod hprod.multipliable hb (a := fun i =>
    a i * if i = i₀ then (r : ℂ) else 1) fun i => by
      by_cases he : i = i₀
      · subst he
        simp only [if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        rw [hr]
        field_simp
        exact le_rfl
      · simp only [he, if_false, mul_one]
        exact h i
  rw [hprod.tprod_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hle
  have hpos' := norm_pos_iff.mpr hA
  nlinarith

/-! ### The extremal zero -/

/-- The slope `tan arg w` of a zero. -/
def zeroSlope (q : XiZeroCopy) : ℝ := (zeroSq q).im / (zeroSq q).re

/-- Slopes tend to zero along the zeros: slope at least `ε > 0` confines a zero to a bounded set. -/
theorem finite_setOf_le_zeroSlope {ε : ℝ} (hε : 0 < ε) : {q : XiZeroCopy | ε ≤ zeroSlope q}.Finite := by
  set R : ℝ := 3 / (2 * ε) + 1 / 2 with hR
  have hRpos : 0 < R := by positivity
  have hsum := xiSpectralPoint_inv_sq_summable
  have hev := hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / R ^ 2 by positivity))
  refine Set.Finite.subset (Filter.eventually_cofinite.mp hev) fun q hq => ?_
  have hq' : ε ≤ zeroSlope q := hq
  simp only [Set.mem_setOf_eq, not_lt]
  set a := (xiSpectralPoint q).re with ha
  set c := (xiSpectralPoint q).im with hc
  have ha0 : a ≠ 0 := spectral_re_ne_zero q
  have hcone : 3 * c ^ 2 ≤ a ^ 2 := three_mul_im_sq_le q
  have hc2 : |c| ≤ 1 / 2 := by
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have him : c = -((q.1 : ℂ).re - 1 / 2) := by simp [hc, xiSpectralPoint, Complex.mul_im]
    rw [him, abs_le]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hare : 0 < |a| := abs_pos.mpr ha0
  have hre : 0 < (zeroSq q).re := zeroSq_re_pos q
  have hslope : ε * (a ^ 2 - c ^ 2) ≤ 2 * a * c := by
    have h1 : ε * (zeroSq q).re ≤ (zeroSq q).im := by
      rwa [zeroSlope, le_div_iff₀ hre] at hq'
    rwa [zeroSq_re, zeroSq_im] at h1
  have habs : 2 * a * c ≤ 2 * |a| * (1 / 2) := by
    have := le_abs_self (a * c)
    rw [abs_mul] at this
    nlinarith [abs_nonneg a, abs_nonneg c]
  have hsqa : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hlow : (2 / 3) * |a| ^ 2 ≤ a ^ 2 - c ^ 2 := by rw [← hsqa]; nlinarith
  have hkey : ε * (2 / 3) * |a| ^ 2 ≤ |a| := by nlinarith
  have hAbound : |a| ≤ 3 / (2 * ε) := by
    rw [le_div_iff₀ (by positivity)]
    have : ε * (2 / 3) * |a| * |a| ≤ 1 * |a| := by nlinarith
    have h2 := le_of_mul_le_mul_right this hare
    nlinarith
  have hnorm : ‖xiSpectralPoint q‖ ≤ R := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [hR]
    linarith
  have hne : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hne.le hnorm 2)

/-- Comparing slopes through the quotient. -/
private lemma im_div_of_slope_le {q q₀ : XiZeroCopy} (h : zeroSlope q ≤ zeroSlope q₀) :
    0 ≤ (zeroSq q₀ / zeroSq q).im := by
  have hre := zeroSq_re_pos q
  have hre₀ := zeroSq_re_pos q₀
  rw [zeroSlope, zeroSlope, div_le_div_iff₀ hre hre₀] at h
  rw [Complex.div_im]
  have hN : 0 < normSq (zeroSq q) := normSq_pos.mpr (zeroSq_ne_zero q)
  have : (zeroSq q₀).im * (zeroSq q).re / normSq (zeroSq q) -
      (zeroSq q₀).re * (zeroSq q).im / normSq (zeroSq q) =
      ((zeroSq q₀).im * (zeroSq q).re - (zeroSq q₀).re * (zeroSq q).im) / normSq (zeroSq q) := by
    ring
  rw [this]
  exact div_nonneg (by linarith) hN.le

/-- **The zero of maximal angle exists under `¬RH`.** -/
theorem exists_zero_of_maximal_angle (h : ¬ RiemannHypothesis) :
    ∃ q₀ : XiZeroCopy, 0 < (zeroSq q₀).im ∧ (∀ q, 0 ≤ (zeroSq q₀ / zeroSq q).im) ∧
      ∃ q₁, 0 < (zeroSq q₀ / zeroSq q₁).im := by
  classical
  rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at h
  push Not at h
  obtain ⟨q, hq⟩ := h
  have him : (zeroSq q).im ≠ 0 := by
    rw [zeroSq_im]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (spectral_re_ne_zero q)) hq
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : XiZeroCopy, 0 < (zeroSq q₁).im := by
    rcases lt_or_gt_of_ne him with h1 | h1
    · refine ⟨xiZeroCopyConjEquiv q, ?_⟩
      rw [zeroSq_conjEquiv, Complex.conj_im]
      linarith
    · exact ⟨q, h1⟩
  have hε : 0 < zeroSlope q₁ := div_pos hq₁ (zeroSq_re_pos q₁)
  have hfin := finite_setOf_le_zeroSlope hε
  obtain ⟨q₀, hq₀, hmax⟩ := Set.exists_max_image _ zeroSlope hfin
    ⟨q₁, show zeroSlope q₁ ≤ zeroSlope q₁ from le_rfl⟩
  have hq₀' : zeroSlope q₁ ≤ zeroSlope q₀ := hq₀
  have hall : ∀ q, zeroSlope q ≤ zeroSlope q₀ := by
    intro q
    by_cases hmem : zeroSlope q₁ ≤ zeroSlope q
    · exact hmax q hmem
    · exact (not_le.mp hmem).le.trans hq₀'
  have him₀ : 0 < (zeroSq q₀).im := by
    have h2 : 0 < zeroSlope q₀ := lt_of_lt_of_le hε hq₀'
    rw [zeroSlope] at h2
    exact (div_pos_iff_of_pos_right (zeroSq_re_pos q₀)).mp h2
  refine ⟨q₀, him₀, fun q => im_div_of_slope_le (hall q), xiZeroCopyConjEquiv q₀, ?_⟩
  rw [zeroSq_conjEquiv, Complex.div_im]
  have hN : 0 < normSq ((starRingEnd ℂ) (zeroSq q₀)) := normSq_pos.mpr (by
    simpa using zeroSq_ne_zero q₀)
  have hre₀ := zeroSq_re_pos q₀
  simp only [Complex.conj_re, Complex.conj_im]
  have : (zeroSq q₀).im * (zeroSq q₀).re / normSq ((starRingEnd ℂ) (zeroSq q₀)) -
      (zeroSq q₀).re * -(zeroSq q₀).im / normSq ((starRingEnd ℂ) (zeroSq q₀)) =
      2 * ((zeroSq q₀).im * (zeroSq q₀).re) / normSq ((starRingEnd ℂ) (zeroSq q₀)) := by ring
  rw [this]
  positivity

/-! ### Hermite–Biehler at the extremal zero -/

/-- Rotating a zero of `Q` to the upper side never lands on a zero. -/
theorem squaredXi_ne_zero_of_extremal {q₀ : XiZeroCopy} (h : ∀ q, 0 ≤ (zeroSq q₀ / zeroSq q).im)
    {t : ℂ} (ht : 0 < t.im) : squaredXi (t * zeroSq q₀) ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := (squaredXi_eq_zero_iff _).mp h0
  have hw₀ := zeroSq_ne_zero q₀
  have hw := zeroSq_ne_zero q
  have hu : t * (zeroSq q₀ / zeroSq q) = 1 := by
    rw [← mul_div_assoc, ← hq, div_self hw]
  have hu0 : zeroSq q₀ / zeroSq q ≠ 0 := div_ne_zero hw₀ hw
  have htval : t = (zeroSq q₀ / zeroSq q)⁻¹ := eq_inv_of_mul_eq_one_left hu
  have him := h q
  rw [htval, Complex.inv_im] at ht
  have hN : 0 < normSq (zeroSq q₀ / zeroSq q) := normSq_pos.mpr hu0
  have : -(zeroSq q₀ / zeroSq q).im / normSq (zeroSq q₀ / zeroSq q) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le
  linarith

/-- **Hermite–Biehler at the extremal zero.** At a zero of maximal angle,
`‖Q(t̄ w₀)‖ < ‖Q(t w₀)‖` for every `t` in the upper half-plane. -/
theorem norm_squaredXi_conj_lt {q₀ : XiZeroCopy} (h : ∀ q, 0 ≤ (zeroSq q₀ / zeroSq q).im)
    (hstrict : ∃ q₁, 0 < (zeroSq q₀ / zeroSq q₁).im) {t : ℂ} (ht : 0 < t.im) :
    ‖squaredXi (star t * zeroSq q₀)‖ < ‖squaredXi (t * zeroSq q₀)‖ := by
  classical
  obtain ⟨q₁, hq₁⟩ := hstrict
  set w₀ := zeroSq q₀ with hw₀
  have hC : XiC 0 ≠ 0 := by
    intro h0
    have := (squaredXi_eq_zero_iff 0).mpr
    have h1 : squaredXi 0 = XiC 0 := by
      have := xiSquaredSeamEntireQuotient_sq 0
      simpa using this
    obtain ⟨q, hq⟩ := (squaredXi_eq_zero_iff 0).mp (h1.trans h0)
    exact zeroSq_ne_zero q hq
  have hA0 : ∏' q, sqFactor (t * w₀) q ≠ 0 := by
    intro h0
    have := squaredXi_sq_eq (t * w₀)
    rw [h0, mul_zero] at this
    exact squaredXi_ne_zero_of_extremal h ht (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hfac : ∀ q, ‖1 - star t * (w₀ / zeroSq q)‖ ^ 2 ≤ ‖1 - t * (w₀ / zeroSq q)‖ ^ 2 := by
    intro q
    have h1 := rotated_factor_norm_sq_sub t (w₀ / zeroSq q)
    have h2 : 0 ≤ 4 * t.im * (w₀ / zeroSq q).im :=
      mul_nonneg (by positivity) (h q)
    linarith
  have hrw : ∀ (x : ℂ) (q : XiZeroCopy), sqFactor (x * w₀) q = 1 - x * (w₀ / zeroSq q) := by
    intro x q
    rw [sqFactor, mul_div_assoc]
  have hle : ∀ q, ‖sqFactor (star t * w₀) q‖ ≤ ‖sqFactor (t * w₀) q‖ := by
    intro q
    rw [hrw, hrw]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp (hfac q)
  have hlt : ‖sqFactor (star t * w₀) q₁‖ < ‖sqFactor (t * w₀) q₁‖ := by
    rw [hrw, hrw]
    refine (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp ?_
    have h1 := rotated_factor_norm_sq_sub t (w₀ / zeroSq q₁)
    have h2 : 0 < 4 * t.im * (w₀ / zeroSq q₁).im := by positivity
    linarith
  have hprod := norm_tprod_lt_norm_tprod (multipliable_sqFactor (t * w₀))
    (multipliable_sqFactor (star t * w₀)) hle hlt hA0
  have hsq : ‖squaredXi (star t * w₀)‖ ^ 2 < ‖squaredXi (t * w₀)‖ ^ 2 := by
    have h1 := congrArg norm (squaredXi_sq_eq (t * w₀))
    have h2 := congrArg norm (squaredXi_sq_eq (star t * w₀))
    rw [norm_pow, norm_mul, norm_pow] at h1 h2
    rw [h1, h2]
    exact mul_lt_mul_of_pos_left hprod (by have := norm_pos_iff.mpr hC; positivity)
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

/-- **The zeros of the rotated function lie in the closed lower half-plane.** -/
theorem im_nonpos_of_squaredXi_eq_zero {q₀ : XiZeroCopy} (h : ∀ q, 0 ≤ (zeroSq q₀ / zeroSq q).im)
    {t : ℂ} (ht : squaredXi (t * zeroSq q₀) = 0) : t.im ≤ 0 := by
  by_contra hpos
  exact squaredXi_ne_zero_of_extremal h (not_le.mp hpos) ht

/-! ### Equal modulus -/

/-- Under RH the rotated values at a zero are conjugate. -/
theorem norm_squaredXi_eq_of_riemannHypothesis (h : RiemannHypothesis) {w : ℂ}
    (hw : squaredXi w = 0) (t : ℂ) : ‖squaredXi (t * w)‖ = ‖squaredXi (star t * w)‖ := by
  obtain ⟨q, rfl⟩ := (squaredXi_eq_zero_iff w).mp hw
  have him : (zeroSq q).im = 0 := by
    rw [zeroSq_im, riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero.mp h q, mul_zero]
  have hreal : (starRingEnd ℂ) (zeroSq q) = zeroSq q := Complex.conj_eq_iff_im.mpr him
  have hconj : star t * zeroSq q = (starRingEnd ℂ) (t * zeroSq q) := by
    rw [map_mul, hreal]
    rfl
  rw [hconj, squaredXi_conj, Complex.norm_conj]

/-- **RH is equal rotated modulus at the zeros.** For one fixed `t` off the real axis. -/
theorem riemannHypothesis_iff_forall_norm_eq {t : ℂ} (ht : 0 < t.im) :
    RiemannHypothesis ↔ ∀ w, squaredXi w = 0 → ‖squaredXi (t * w)‖ = ‖squaredXi (star t * w)‖ := by
  refine ⟨fun h w hw => norm_squaredXi_eq_of_riemannHypothesis h hw t, fun h => ?_⟩
  by_contra hRH
  obtain ⟨q₀, _, hall, hstrict⟩ := exists_zero_of_maximal_angle hRH
  have h1 := norm_squaredXi_conj_lt hall hstrict ht
  have h2 := h (zeroSq q₀) ((squaredXi_eq_zero_iff _).mpr ⟨q₀, rfl⟩)
  linarith

/-- **A balanced relation with nonvanishing coefficients implies RH.** The coefficients are read at
the zeros only, and the `T Q` term of a second-order relation has already vanished there. -/
theorem riemannHypothesis_of_balanced_relation {a b : ℂ → ℂ} {t : ℂ} (ht : 0 < t.im)
    (hrel : ∀ w, squaredXi w = 0 → a w * squaredXi (t * w) + b w * squaredXi (star t * w) = 0)
    (hbal : ∀ w, squaredXi w = 0 → ‖a w‖ = ‖b w‖) (hne : ∀ w, squaredXi w = 0 → a w ≠ 0) :
    RiemannHypothesis := by
  refine (riemannHypothesis_iff_forall_norm_eq ht).mpr fun w hw => ?_
  rcases balanced_relation_zero_or_modulus_eq (hbal w hw) (hrel w hw) with h | h
  · exact absurd h.1 (hne w hw)
  · exact h

end GaloisForLFunctions.RigidArithmeticOfCuts
