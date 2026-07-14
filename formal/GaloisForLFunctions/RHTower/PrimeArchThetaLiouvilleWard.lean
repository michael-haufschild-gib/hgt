import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The positive Liouville Gibbs atom underlying one theta-cusp source atom. -/
def thetaCuspLiouvilleGibbsAtom (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspPolynomialAtom (X ^ 2) n x

theorem thetaCuspLiouvilleGibbsAtom_apply (n : ℕ) (x : ℝ) :
    thetaCuspLiouvilleGibbsAtom n x =
      Real.exp (x / 2) * ((n : ℝ) * Real.exp x) ^ 2 *
        Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) := by
  simp [thetaCuspLiouvilleGibbsAtom, thetaCuspPolynomialAtom]

theorem hasDerivAt_thetaCuspLiouvilleGibbsAtom (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspLiouvilleGibbsAtom n)
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep (X ^ 2)) n x) x := by
  exact hasDerivAt_thetaCuspPolynomialAtom (X ^ 2) n x

theorem thetaCuspSourceTerm_eq_liouvilleWard (n : ℕ) (x : ℝ) :
    thetaCuspSourceTerm x n =
      -2 * Real.pi *
        (deriv (thetaCuspLiouvilleGibbsAtom n) x +
          (1 / 2 : ℝ) * thetaCuspLiouvilleGibbsAtom n x) := by
  rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).deriv]
  simp [thetaCuspSourceTerm, thetaCuspSeed,
    thetaCuspLiouvilleGibbsAtom, thetaCuspPolynomialAtom,
    thetaCuspLogDerivativeStep]
  ring

theorem integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    (k : ℕ) (P : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x ^ k * thetaCuspPolynomialAtom P n x) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-x)) (Ioi 0) := by
    have hk : (-1 : ℝ) < (k : ℝ) :=
      lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
    convert integrableOn_rpow_mul_exp_neg_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) hk (by norm_num) using 1
    ext x
    rw [Real.rpow_natCast, Real.rpow_one]
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [thetaCuspGaussianConstant_nonneg P]
  have hdom : IntegrableOn (fun x : ℝ => C * (x ^ k * Real.exp (-x))) (Ioi 0) :=
    hbase.const_mul C
  apply Integrable.mono hdom
  · have hatom : Continuous (thetaCuspPolynomialAtom P n) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt
    exact ((continuous_id.pow k).mul hatom).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx.le hn
    change Real.exp x * |thetaCuspPolynomialAtom P n x| ≤ C at h
    have hsplit : |thetaCuspPolynomialAtom P n x| =
        Real.exp (-x) * (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg hx.le, abs_of_nonneg (mul_nonneg hC (mul_nonneg
        (pow_nonneg hx.le k) (Real.exp_pos _).le)), hsplit]
    calc
      x ^ k * (Real.exp (-x) *
          (Real.exp x * |thetaCuspPolynomialAtom P n x|)) ≤
          x ^ k * (Real.exp (-x) * C) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)
              (pow_nonneg hx.le k)
      _ = C * (x ^ k * Real.exp (-x)) := by ring

theorem pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    (k : ℕ) (P : ℝ[X]) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspPolynomialAtom P n x)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := thetaCuspGaussianConstant P *
    Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [thetaCuspGaussianConstant_nonneg P]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖x ^ k * thetaCuspPolynomialAtom P n x‖ ≤
        C * (x ^ k * Real.exp (-x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have h := exp_mul_abs_thetaCuspPolynomialAtom_le_of_pos P hx hn
    change Real.exp x * |thetaCuspPolynomialAtom P n x| ≤ C at h
    have hsplit : |thetaCuspPolynomialAtom P n x| =
        Real.exp (-x) * (Real.exp x * |thetaCuspPolynomialAtom P n x|) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx, hsplit]
    calc
      x ^ k * (Real.exp (-x) *
          (Real.exp x * |thetaCuspPolynomialAtom P n x|)) ≤
          x ^ k * (Real.exp (-x) * C) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)
              (pow_nonneg hx k)
      _ = C * (x ^ k * Real.exp (-x)) := by ring
  have hmajor : Tendsto (fun x : ℝ => C * (x ^ k * Real.exp (-x)))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul C
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

theorem pow_mul_thetaCuspPolynomialAtom_tendsto_zero_of_pos
    {k : ℕ} (hk : 0 < k) (P : ℝ[X]) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspPolynomialAtom P n x)
      (𝓝[>] 0) (𝓝 0) := by
  have hatom : Continuous (thetaCuspPolynomialAtom P n) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom P n x).continuousAt
  have hc : Continuous (fun x : ℝ => x ^ k * thetaCuspPolynomialAtom P n x) :=
    (continuous_id.pow k).mul hatom
  have h := (hc.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [Nat.ne_of_gt hk] using h

/-- Raw moments of the positive Liouville Gibbs atom. -/
def thetaCuspLiouvilleGibbsMoment (k n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ k * thetaCuspLiouvilleGibbsAtom n x

theorem thetaCuspLiouvilleGibbsAtom_zero (n : ℕ) :
    thetaCuspLiouvilleGibbsAtom n 0 =
      (n : ℝ) ^ 2 * Real.exp (-Real.pi * (n : ℝ) ^ 2) := by
  rw [thetaCuspLiouvilleGibbsAtom_apply]
  simp

theorem thetaCuspAtomRawEvenMoment_zero_eq_liouvilleGibbs
    {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment 0 n =
      4 * Real.pi * thetaCuspLiouvilleGibbsAtom n 0 -
        2 * Real.pi * thetaCuspLiouvilleGibbsMoment 0 n := by
  let b : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom n
  let b' : ℝ → ℝ := fun x =>
    thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep (X ^ 2)) n x
  have hbderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt b (b' x) x := by
    intro x hx
    exact hasDerivAt_thetaCuspLiouvilleGibbsAtom n x
  have hb'int : IntegrableOn b' (Ioi 0) := by
    simpa only [b', pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        0 (thetaCuspLogDerivativeStep (X ^ 2)) hn
  have hbint : IntegrableOn b (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom, pow_zero, one_mul] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos 0 (X ^ 2) hn
  have hbcont : Continuous b :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).continuousAt
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := b 0) (b' := (0 : ℝ))
    (u := fun _ : ℝ => 1) (u' := fun _ : ℝ => 0)
    (v := b) (v' := b')
    (fun x _ => hasDerivAt_const x 1)
    hbderiv
    (by
      exact hb'int.congr_fun (fun x _ => by simp) measurableSet_Ioi)
    (by
      exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0)).congr_fun
        (g := (fun _ : ℝ => 0) * b) (fun x _ => by simp) measurableSet_Ioi)
    (by
      exact Filter.Tendsto.congr'
        (f₁ := b) (f₂ := (fun _ : ℝ => 1) * b)
        (Eventually.of_forall fun x => by simp)
        ((hbcont.tendsto 0).mono_left
          (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)))
    (by
      exact Filter.Tendsto.congr'
        (f₁ := b) (f₂ := (fun _ : ℝ => 1) * b)
        (Eventually.of_forall fun x => by simp)
        (by
          simpa only [b, thetaCuspLiouvilleGibbsAtom] using
            thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos (X ^ 2) hn))
  have hibp' : (∫ x : ℝ in Ioi 0, b' x) = -b 0 := by
    simpa only [Pi.mul_apply, one_mul, zero_mul, integral_zero, sub_zero,
      zero_sub] using hibp
  have hsource : (fun x : ℝ => thetaCuspSourceTerm x n) =
      fun x => -2 * Real.pi * (b' x + (1 / 2 : ℝ) * b x) := by
    funext x
    rw [thetaCuspSourceTerm_eq_liouvilleWard,
      (hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).deriv]
  rw [thetaCuspAtomRawEvenMoment]
  simp only [Nat.mul_zero, pow_zero, one_mul]
  rw [hsource]
  rw [integral_const_mul, integral_add hb'int (hbint.const_mul (1 / 2 : ℝ)),
    integral_const_mul, hibp']
  change _ = 4 * Real.pi * b 0 -
    2 * Real.pi * thetaCuspLiouvilleGibbsMoment 0 n
  rw [thetaCuspLiouvilleGibbsMoment]
  simp only [pow_zero, one_mul]
  change _ = 4 * Real.pi * b 0 -
    2 * Real.pi * ∫ x : ℝ in Ioi 0, b x
  ring

theorem integral_pow_mul_thetaCuspLiouvilleGibbs_deriv_eq
    (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
        x ^ k * deriv (thetaCuspLiouvilleGibbsAtom n) x) =
      -(k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n := by
  let b : ℝ → ℝ := thetaCuspLiouvilleGibbsAtom n
  let b' : ℝ → ℝ := fun x =>
    thetaCuspPolynomialAtom (thetaCuspLogDerivativeStep (X ^ 2)) n x
  let u' : ℝ → ℝ := fun x => (k : ℝ) * x ^ (k - 1)
  have hbderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt b (b' x) x := by
    intro x hx
    exact hasDerivAt_thetaCuspLiouvilleGibbsAtom n x
  have hub'int : IntegrableOn (fun x : ℝ => x ^ k * b' x) (Ioi 0) := by
    simpa only [b'] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        k (thetaCuspLogDerivativeStep (X ^ 2)) hn
  have hbase : IntegrableOn
      (fun x : ℝ => x ^ (k - 1) * b x) (Ioi 0) := by
    simpa only [b, thetaCuspLiouvilleGibbsAtom] using
      integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        (k - 1) (X ^ 2) hn
  have hu'bint : IntegrableOn (fun x : ℝ => u' x * b x) (Ioi 0) := by
    have h : IntegrableOn
        (fun x : ℝ => (k : ℝ) * (x ^ (k - 1) * b x)) (Ioi 0) :=
      hbase.const_mul (k : ℝ)
    exact IntegrableOn.congr_fun h (fun x _ => by simp only [u']; ring)
      measurableSet_Ioi
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun x : ℝ => x ^ k) (u' := u')
    (v := b) (v' := b')
    (fun x _ => hasDerivAt_pow k x)
    hbderiv
    (hub'int.congr_fun (fun x _ => by rfl) measurableSet_Ioi)
    (hu'bint.congr_fun (fun x _ => by rfl) measurableSet_Ioi)
    (by
      exact Filter.Tendsto.congr'
        (f₁ := fun x : ℝ => x ^ k * b x)
        (f₂ := (fun x : ℝ => x ^ k) * b)
        (Eventually.of_forall fun x => by rfl)
        (by
          simpa only [b, thetaCuspLiouvilleGibbsAtom] using
            pow_mul_thetaCuspPolynomialAtom_tendsto_zero_of_pos
              hk (X ^ 2) n))
    (by
      exact Filter.Tendsto.congr'
        (f₁ := fun x : ℝ => x ^ k * b x)
        (f₂ := (fun x : ℝ => x ^ k) * b)
        (Eventually.of_forall fun x => by rfl)
        (by
          simpa only [b, thetaCuspLiouvilleGibbsAtom] using
            pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
              k (X ^ 2) hn))
  have hibp' :
      (∫ x : ℝ in Ioi 0, x ^ k * b' x) =
        -(k : ℝ) * (∫ x : ℝ in Ioi 0, x ^ (k - 1) * b x) := by
    rw [show (∫ x : ℝ in Ioi 0, u' x * b x) =
        (k : ℝ) * ∫ x : ℝ in Ioi 0, x ^ (k - 1) * b x by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [u']
      ring] at hibp
    simpa only [Pi.mul_apply, zero_sub, sub_eq_add_neg, neg_zero, zero_add,
      neg_mul]
      using hibp
  calc
    (∫ x : ℝ in Ioi 0, x ^ k * deriv b x) =
        ∫ x : ℝ in Ioi 0, x ^ k * b' x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).deriv]
    _ = -(k : ℝ) *
        (∫ x : ℝ in Ioi 0, x ^ (k - 1) * b x) := hibp'
    _ = -(k : ℝ) * thetaCuspLiouvilleGibbsMoment (k - 1) n := by
      rw [thetaCuspLiouvilleGibbsMoment]

theorem thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    thetaCuspAtomRawEvenMoment (j + 1) n =
      8 * Real.pi * (j + 1) *
          thetaCuspLiouvilleGibbsMoment (2 * j + 1) n -
        2 * Real.pi * thetaCuspLiouvilleGibbsMoment (2 * j + 2) n := by
  have hk : 0 < 2 * (j + 1) := by omega
  have hibp := integral_pow_mul_thetaCuspLiouvilleGibbs_deriv_eq
    (2 * (j + 1)) hk hn
  rw [thetaCuspAtomRawEvenMoment]
  rw [show (fun x : ℝ => x ^ (2 * (j + 1)) * thetaCuspSourceTerm x n) =
      fun x => -2 * Real.pi *
        (x ^ (2 * (j + 1)) * deriv (thetaCuspLiouvilleGibbsAtom n) x +
          x ^ (2 * (j + 1)) * ((1 / 2 : ℝ) *
            thetaCuspLiouvilleGibbsAtom n x)) by
    funext x
    rw [thetaCuspSourceTerm_eq_liouvilleWard]
    ring]
  rw [show (2 * (j + 1) : ℕ) = 2 * j + 2 by omega]
  rw [integral_const_mul]
  have hderiv : IntegrableOn (fun x : ℝ =>
      x ^ (2 * j + 2) * deriv (thetaCuspLiouvilleGibbsAtom n) x) (Ioi 0) := by
    have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      (2 * j + 2) (thetaCuspLogDerivativeStep (X ^ 2)) hn
    exact IntegrableOn.congr_fun h (fun x _ => by
      rw [(hasDerivAt_thetaCuspLiouvilleGibbsAtom n x).deriv]) measurableSet_Ioi
  have hbint : IntegrableOn (fun x : ℝ =>
      x ^ (2 * j + 2) * ((1 / 2 : ℝ) *
        thetaCuspLiouvilleGibbsAtom n x)) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) *
        (x ^ (2 * j + 2) * thetaCuspPolynomialAtom (X ^ 2) n x)) (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
        (2 * j + 2) (X ^ 2) hn).const_mul (1 / 2 : ℝ)
    exact IntegrableOn.congr_fun h (fun x _ => by
      simp only [thetaCuspLiouvilleGibbsAtom]
      ring) measurableSet_Ioi
  rw [integral_add hderiv hbint]
  rw [show (∫ x : ℝ in Ioi 0,
      x ^ (2 * j + 2) * ((1 / 2 : ℝ) *
        thetaCuspLiouvilleGibbsAtom n x)) =
      (1 / 2 : ℝ) * thetaCuspLiouvilleGibbsMoment (2 * j + 2) n by
    rw [thetaCuspLiouvilleGibbsMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring]
  rw [show (∫ x : ℝ in Ioi 0,
      x ^ (2 * j + 2) * deriv (thetaCuspLiouvilleGibbsAtom n) x) =
      -(2 * j + 2 : ℕ) * thetaCuspLiouvilleGibbsMoment (2 * j + 1) n by
    convert hibp using 1]
  push_cast
  ring

/-- The first theta atom's Ward-normalized raw moments.  The zeroth moment
contains the boundary charge; positive moments are pure Gibbs moments. -/
def thetaCuspFirstAtomWardMoment : ℕ → ℝ
  | 0 => 2 * Real.exp (-Real.pi) - thetaCuspLiouvilleGibbsMoment 0 1
  | j + 1 =>
      4 * (j + 1) * thetaCuspLiouvilleGibbsMoment (2 * j + 1) 1 -
        thetaCuspLiouvilleGibbsMoment (2 * j + 2) 1

theorem thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment (j : ℕ) :
    thetaCuspAtomRawEvenMoment j 1 =
      2 * Real.pi * thetaCuspFirstAtomWardMoment j := by
  cases j with
  | zero =>
      rw [thetaCuspAtomRawEvenMoment_zero_eq_liouvilleGibbs (by norm_num),
        thetaCuspLiouvilleGibbsAtom_zero]
      simp only [Nat.cast_one, one_pow, mul_one, thetaCuspFirstAtomWardMoment]
      ring
  | succ j =>
      rw [thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs j (by norm_num)]
      simp only [thetaCuspFirstAtomWardMoment]
      ring

theorem thetaCuspFirstAtomWardMoment_nonneg (j : ℕ) :
    0 ≤ thetaCuspFirstAtomWardMoment j := by
  have h := thetaCuspAtomRawEvenMoment_nonneg j 1
  rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment] at h
  nlinarith [Real.pi_pos]

/-- The all-order first-atom enclosure, transported to the Liouville Gibbs
moments.  This makes the Ward variables usable by every consumer of the
existing theta-cusp raw-moment bounds. -/
theorem thetaCuspRawEvenMoment_between_firstAtomWardMoment (j : ℕ) :
    2 * Real.pi * thetaCuspFirstAtomWardMoment j ≤ thetaCuspRawEvenMoment j ∧
      thetaCuspRawEvenMoment j ≤
        (3005 / 2997 : ℝ) *
          (2 * Real.pi * thetaCuspFirstAtomWardMoment j) := by
  constructor
  · simpa only [← thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment] using
      thetaCuspAtomRawEvenMoment_one_le_raw j
  · simpa only [← thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment] using
      thetaCuspRawEvenMoment_le_first_atom_factor j

/-- The existing first-atom Hankel criterion, expressed entirely in moments
of the positive Liouville Gibbs atom and its boundary charge. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_liouvilleWard
    (hupper :
      14 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2) ^ 2 ≤
        9 * thetaCuspFirstAtomWardMoment 1 * thetaCuspFirstAtomWardMoment 3)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 0) *
          ((3005 / 2997 : ℝ) * thetaCuspFirstAtomWardMoment 2) ≤
        45 * thetaCuspFirstAtomWardMoment 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom
  · rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 3]
    have hscaled := mul_le_mul_of_nonneg_left hupper
      (sq_nonneg (2 * Real.pi))
    convert hscaled using 1 <;> ring
  · rw [thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 0,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 1,
      thetaCuspAtomRawEvenMoment_one_eq_firstAtomWardMoment 2]
    have hscaled := mul_le_mul_of_nonneg_left hrelaxed
      (sq_nonneg (2 * Real.pi))
    convert hscaled using 1 <;> ring

end
end RHTower
