import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryPadeContactParity
import GaloisForLFunctions.HTGeometry.FiniteHankelMassShiftDeterminantContact
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit
import GaloisForLFunctions.HTGeometry.ScheffeCounting
import GaloisForLFunctions.RHTower.FiniteSpectralTraceNoGo
import GaloisForLFunctions.RHTower.XiShiftedHankelAdmittedGammaLorentzLanding
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryHilbertChargeFlow
import GaloisForLFunctions.RHTower.XiShiftedHankelLagrangeCapacity
import GaloisForLFunctions.RHTower.XiShiftedHankelRedundantSamplingCapacity

/-!
# Padé contact parity for shifted Xi Hankel faces

This module specializes the finite-Hankel Padé normal coordinates to the shifted reciprocal moments
of Xi.  In the zero-free window these defects are exactly the completed prime--archimedean defects.
At first contact, the linear Möbius coefficient is the negative of the existing Route-U monic
remainder, with the positive factor `2n+1`.
-/

open Matrix Polynomial

namespace RHTower

noncomputable section

/-- Difference between the shifted-Xi moments and the canonical flat atomic shadow. -/
def xiShiftedHankelBoundaryPadeDefect
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  HTGeometry.finiteHankelBoundaryPadeDefect
    (fun j => (xiShiftedReciprocalMoment y j).re) c k

/-- Source-side form of the same flat-shadow defect. -/
def primeArchShiftedHankelBoundaryPadeDefect
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  HTGeometry.finiteHankelBoundaryPadeDefect
    (fun j => (primeArchShiftedReciprocalMoment y j).re) c k

/-- In the local zero-free window, Xi and completed prime--archimedean Padé defects agree. -/
theorem xiShiftedHankelBoundaryPadeDefect_eq_primeArch
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) :
    xiShiftedHankelBoundaryPadeDefect y c k =
      primeArchShiftedHankelBoundaryPadeDefect y c k := by
  have hseq : (fun j => (xiShiftedReciprocalMoment y j).re) =
      (fun j => (primeArchShiftedReciprocalMoment y j).re) := by
    funext j
    rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax]
  simp only [xiShiftedHankelBoundaryPadeDefect,
    primeArchShiftedHankelBoundaryPadeDefect, hseq]

/-- Flatness annihilates every shifted-Xi defect visible to the singular Hankel face. -/
theorem xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le
    {y : ℝ} {n k : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hk : k ≤ 2 * n) :
    xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
  exact HTGeometry.finiteHankelBoundaryPadeDefect_eq_zero_of_le
    c hhead hc hlast hk

/-- The first shifted-Xi Padé defect is the Route-U monic remainder. -/
theorem xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + 1) =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryPadeDefect_first_eq_monicRemainder
    (fun j => (xiShiftedReciprocalMoment y j).re) c hhead hc hlast

/-- Exact first determinant coefficient of the shifted-Xi mass-shift orbit at a flat Hankel
boundary.  All lower moment defects disappear from the determinant, and the first surviving
coefficient is the head determinant times the first Padé defect with its universal
negative-binomial factor. -/
theorem coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
    {y : ℝ} {n d : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    PowerSeries.coeff d
        (GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)).det =
      (xiShiftedMomentHankelMatrix y n).det *
        ((-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) *
          xiShiftedHankelBoundaryPadeDefect y c (2 * n + d)) := by
  have hcard := HTGeometry.finiteHankelBoundaryNodes_card
    (s := fun k => (xiShiftedReciprocalMoment y k).re) c hhead hc hlast
  have hmoment : ∀ k < 2 * n + d,
      (xiShiftedReciprocalMoment y k).re =
        ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
          HTGeometry.finiteHankelBoundaryWeight
            (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ k := by
    intro k hk
    exact sub_eq_zero.mp (hzero k hk)
  have h := GaloisForLFunctions.HTGeometry.coeff_det_massShiftHankelPowerSeries_at_first_flat_defect
    (fun k => (xiShiftedReciprocalMoment y k).re)
    (HTGeometry.finiteHankelBoundaryNodes c)
    (HTGeometry.finiteHankelBoundaryWeight
      (fun j => (xiShiftedReciprocalMoment y j).re) c)
    hcard hd hmoment
  rw [show xiShiftedMomentHankelMatrix y n =
    HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n by rfl]
  simpa only [xiShiftedHankelBoundaryPadeDefect,
    HTGeometry.finiteHankelBoundaryPadeDefect] using h

/-- The order-one contact coefficient is `-(2n+1)` times the Route-U remainder. -/
theorem xiShiftedHankelBoundaryContactSeries_coeff_one
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    PowerSeries.coeff 1
        (HTGeometry.mobiusPadeContactSeries
          (xiShiftedHankelBoundaryPadeDefect y c)
          (HTGeometry.finiteHankelNullMonicPolynomial c) n) =
      -((2 * n + 1 : ℕ) : ℝ) * xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryContactSeries_coeff_one c hhead hc hlast

/-- Any completed source law with the opposite alternating defect sign excludes positive Padé
contact orientation.  This is the source-side consumer needed by the higher-contact Route-U pivot. -/
theorem not_xiShiftedHankelBoundaryContactCoefficient_pos_of_primeArch_opposite
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n d : ℕ} (c : Fin (n + 1) → ℝ) (hd : 0 < d)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + d,
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0)
    (hsource : (-1 : ℝ) ^ d *
      primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + d) < 0) :
    ¬ 0 < PowerSeries.coeff d
      (HTGeometry.mobiusPadeContactSeries
        (xiShiftedHankelBoundaryPadeDefect y c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n) := by
  have hseq : xiShiftedHankelBoundaryPadeDefect y c =
      primeArchShiftedHankelBoundaryPadeDefect y c := by
    funext k
    exact xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy hymax c k
  rw [hseq]
  exact HTGeometry.not_contactCoefficient_pos_of_source_opposite
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    hd hzero hsource

/-! ### Exact all-order shifted-Xi mass-shift semigroup -/

/-- Möbius translation of each Xi reciprocal-square atom is an additive semigroup. -/
theorem xiShiftedReciprocalSquare_add
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (q : XiZeroCopy) :
    xiShiftedReciprocalSquare (y + u) q =
      xiShiftedReciprocalSquare y q /
        (1 + (u : ℂ) * xiShiftedReciprocalSquare y q) := by
  have hyden := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q
  have hyuden := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hyu q
  let z := xiZeroCopyReciprocalSquare q
  have hyden' : 1 + z * (y : ℂ) ≠ 0 := by simpa [z, mul_comm] using hyden
  have hyuden' : 1 + z * ((y + u : ℝ) : ℂ) ≠ 0 := by
    simpa [z, mul_comm] using hyuden
  have hden : 1 + (u : ℂ) * (z / (1 + (y : ℂ) * z)) =
      (1 + ((y + u : ℝ) : ℂ) * z) / (1 + (y : ℂ) * z) := by
    field_simp [hyden, hyden']
    push_cast
    ring
  rw [xiShiftedReciprocalSquare, xiShiftedReciprocalSquare]
  change z / (1 + ((y + u : ℝ) : ℂ) * z) =
    (z / (1 + (y : ℂ) * z)) / (1 + (u : ℂ) * (z / (1 + (y : ℂ) * z)))
  rw [hden]
  field_simp [hyden, hyuden, hyden', hyuden']

/-- Pointwise negative-binomial expansion of the shifted-Xi semigroup around an arbitrary
nonnegative base point. -/
theorem hasSum_xiShiftedReciprocalSquare_pow_add
    {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) (humax : u < 41 / 2)
    (q : XiZeroCopy) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalSquare y q ^ (r + m + 1))
      (xiShiftedReciprocalSquare (y + u) q ^ (m + 1)) := by
  let z := xiShiftedReciprocalSquare y q
  have hz : ‖z‖ < (2 / 41 : ℝ) :=
    lt_of_le_of_lt (norm_xiShiftedReciprocalSquare_le hy q)
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q)
  have hur : u * (2 / 41 : ℝ) < 1 := by nlinarith
  have huz : ‖-((u : ℂ) * z)‖ < 1 := by
    by_cases hu0 : u = 0
    · subst u
      norm_num
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu]
    exact (mul_lt_mul_of_pos_left hz (lt_of_le_of_ne hu (Ne.symm hu0))).trans hur
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one m huz
  have hmul := hseries.mul_left (z ^ (m + 1))
  rw [xiShiftedReciprocalSquare_add hy (add_nonneg hy hu) q]
  change HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        z ^ (r + m + 1))
    ((z / (1 + (u : ℂ) * z)) ^ (m + 1))
  convert hmul using 2
  · exact rfl
  · rw [pow_add]
    ring
  · rw [div_pow]
    ring

/-- Absolute summability over contact order and Xi divisor copy at every nonnegative base point. -/
theorem summable_xiShiftedReciprocal_add_double
    {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) (humax : u < 41 / 2) (m : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      (-1 : ℂ) ^ p.1 * ((p.1 + m).choose m : ℂ) * (u : ℂ) ^ p.1 *
        xiShiftedReciprocalSquare y p.2 ^ (p.1 + m + 1)) := by
  let R : ℝ := 2 / 41
  let a : ℕ → ℝ := fun r => ((r + m).choose m : ℝ) * (u * R) ^ r
  let b : XiZeroCopy → ℝ := fun q => ‖xiShiftedReciprocalSquare y q ^ (m + 1)‖
  have htheta0 : 0 ≤ u * R := by dsimp only [R]; positivity
  have htheta : u * R < 1 := by dsimp only [R]; nlinarith
  have ha : Summable a := by
    apply summable_choose_mul_geometric_of_norm_lt_one m
    rw [Real.norm_eq_abs, abs_of_nonneg htheta0]
    exact htheta
  have hb : Summable b := by
    simpa only [b] using (summable_xiShiftedReciprocalSquare_pow hy m).norm
  have hab : Summable (fun p : ℕ × XiZeroCopy => a p.1 * b p.2) :=
    ha.mul_of_nonneg hb (fun r => by positivity) (fun q => norm_nonneg _)
  apply Summable.of_norm_bounded hab
  rintro ⟨r, q⟩
  have hz : ‖xiShiftedReciprocalSquare y q‖ ≤ R :=
    (norm_xiShiftedReciprocalSquare_le hy q).trans
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le
  change ‖(-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)‖ ≤ a r * b q
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, a, b]
  rw [show r + m + 1 = r + (m + 1) by omega, pow_add]
  have hcore : u ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r ≤ (u * R) ^ r := by
    rw [mul_pow]
    gcongr
  calc
    ((r + m).choose m : ℝ) * u ^ r *
          (‖xiShiftedReciprocalSquare y q‖ ^ r *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1)) =
        ((r + m).choose m : ℝ) *
          (u ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r) *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by ring
    _ ≤ ((r + m).choose m : ℝ) * (u * R) ^ r *
          ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by gcongr

/-- **All-order shifted-Xi semigroup law.**  Around every nonnegative base point, the entire
shifted reciprocal-moment tower is its own convergent negative-binomial mass-shift transform. -/
theorem xiShiftedReciprocalMoment_add_eq_negativeBinomial
    {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) (humax : u < 41 / 2) (m : ℕ) :
    xiShiftedReciprocalMoment (y + u) m =
      ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalMoment y (r + m) := by
  let f : ℕ → XiZeroCopy → ℂ := fun r q =>
    (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)
  have hf : Summable (Function.uncurry f) :=
    summable_xiShiftedReciprocal_add_double hy hu humax m
  have hpoint (q : XiZeroCopy) :
      ∑' r : ℕ, f r q = xiShiftedReciprocalSquare (y + u) q ^ (m + 1) :=
    (hasSum_xiShiftedReciprocalSquare_pow_add hy hu humax q m).tsum_eq
  calc
    xiShiftedReciprocalMoment (y + u) m =
        ∑' q : XiZeroCopy, xiShiftedReciprocalSquare (y + u) q ^ (m + 1) := rfl
    _ = ∑' q : XiZeroCopy, ∑' r : ℕ, f r q := by
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = ∑' r : ℕ, ∑' q : XiZeroCopy, f r q := by rw [hf.tsum_comm]
    _ = ∑' r : ℕ,
        (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
          xiShiftedReciprocalMoment y (r + m) := by
      apply tsum_congr
      intro r
      rw [xiShiftedReciprocalMoment, ← tsum_mul_left]

/-- Signed local version of the pointwise expansion.  This supplies a genuine two-sided analytic
germ whenever the translated base point remains nonnegative. -/
theorem hasSum_xiShiftedReciprocalSquare_pow_add_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (huabs : |u| < 41 / 2)
    (q : XiZeroCopy) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalSquare y q ^ (r + m + 1))
      (xiShiftedReciprocalSquare (y + u) q ^ (m + 1)) := by
  let z := xiShiftedReciprocalSquare y q
  have hz : ‖z‖ < (2 / 41 : ℝ) :=
    lt_of_le_of_lt (norm_xiShiftedReciprocalSquare_le hy q)
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q)
  have hur : |u| * (2 / 41 : ℝ) < 1 := by nlinarith [abs_nonneg u]
  have huz : ‖-((u : ℂ) * z)‖ < 1 := by
    by_cases hu0 : u = 0
    · subst u
      norm_num
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_lt_mul_of_pos_left hz (abs_pos.mpr hu0)).trans hur
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one m huz
  have hmul := hseries.mul_left (z ^ (m + 1))
  rw [xiShiftedReciprocalSquare_add hy hyu q]
  change HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        z ^ (r + m + 1))
    ((z / (1 + (u : ℂ) * z)) ^ (m + 1))
  convert hmul using 2
  · exact rfl
  · rw [pow_add]
    ring
  · rw [div_pow]
    ring

/-- Absolute double summability for signed local mass shifts. -/
theorem summable_xiShiftedReciprocal_add_double_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (huabs : |u| < 41 / 2) (m : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      (-1 : ℂ) ^ p.1 * ((p.1 + m).choose m : ℂ) * (u : ℂ) ^ p.1 *
        xiShiftedReciprocalSquare y p.2 ^ (p.1 + m + 1)) := by
  let R : ℝ := 2 / 41
  let a : ℕ → ℝ := fun r => ((r + m).choose m : ℝ) * (|u| * R) ^ r
  let b : XiZeroCopy → ℝ := fun q => ‖xiShiftedReciprocalSquare y q ^ (m + 1)‖
  have htheta0 : 0 ≤ |u| * R := by dsimp only [R]; positivity
  have htheta : |u| * R < 1 := by dsimp only [R]; nlinarith [abs_nonneg u]
  have ha : Summable a := by
    apply summable_choose_mul_geometric_of_norm_lt_one m
    rw [Real.norm_eq_abs, abs_of_nonneg htheta0]
    exact htheta
  have hb : Summable b := by
    simpa only [b] using (summable_xiShiftedReciprocalSquare_pow hy m).norm
  have hab : Summable (fun p : ℕ × XiZeroCopy => a p.1 * b p.2) :=
    ha.mul_of_nonneg hb (fun r => by positivity) (fun q => norm_nonneg _)
  apply Summable.of_norm_bounded hab
  rintro ⟨r, q⟩
  have hz : ‖xiShiftedReciprocalSquare y q‖ ≤ R :=
    (norm_xiShiftedReciprocalSquare_le hy q).trans
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le
  change ‖(-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)‖ ≤ a r * b q
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, a, b]
  rw [show r + m + 1 = r + (m + 1) by omega, pow_add]
  have hcore : |u| ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r ≤ (|u| * R) ^ r := by
    rw [mul_pow]
    gcongr
  calc
    ((r + m).choose m : ℝ) * |u| ^ r *
          (‖xiShiftedReciprocalSquare y q‖ ^ r *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1)) =
        ((r + m).choose m : ℝ) *
          (|u| ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r) *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by ring
    _ ≤ ((r + m).choose m : ℝ) * (|u| * R) ^ r *
          ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by gcongr

/-- **Signed all-order shifted-Xi semigroup law.**  The negative-binomial orbit formula is valid
on the full local disk, not merely for forward shifts. -/
theorem xiShiftedReciprocalMoment_add_eq_negativeBinomial_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (huabs : |u| < 41 / 2) (m : ℕ) :
    xiShiftedReciprocalMoment (y + u) m =
      ∑' r : ℕ, (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalMoment y (r + m) := by
  let f : ℕ → XiZeroCopy → ℂ := fun r q =>
    (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)
  have hf : Summable (Function.uncurry f) :=
    summable_xiShiftedReciprocal_add_double_of_abs_lt hy huabs m
  have hpoint (q : XiZeroCopy) :
      ∑' r : ℕ, f r q = xiShiftedReciprocalSquare (y + u) q ^ (m + 1) :=
    (hasSum_xiShiftedReciprocalSquare_pow_add_of_abs_lt hy hyu huabs q m).tsum_eq
  calc
    xiShiftedReciprocalMoment (y + u) m =
        ∑' q : XiZeroCopy, xiShiftedReciprocalSquare (y + u) q ^ (m + 1) := rfl
    _ = ∑' q : XiZeroCopy, ∑' r : ℕ, f r q := by
      apply tsum_congr
      exact fun q => (hpoint q).symm
    _ = ∑' r : ℕ, ∑' q : XiZeroCopy, f r q := by rw [hf.tsum_comm]
    _ = ∑' r : ℕ,
        (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
          xiShiftedReciprocalMoment y (r + m) := by
      apply tsum_congr
      intro r
      rw [xiShiftedReciprocalMoment, ← tsum_mul_left]

/-- The signed negative-binomial moment series converges to the actual shifted moment. -/
theorem hasSum_xiShiftedReciprocalMoment_add_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (huabs : |u| < 41 / 2) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalMoment y (r + m))
      (xiShiftedReciprocalMoment (y + u) m) := by
  let f : ℕ → XiZeroCopy → ℂ := fun r q =>
    (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)
  have hf : Summable (Function.uncurry f) :=
    summable_xiShiftedReciprocal_add_double_of_abs_lt hy huabs m
  have hinner (r : ℕ) : HasSum (f r)
      ((-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalMoment y (r + m)) := by
    rw [xiShiftedReciprocalMoment]
    exact ((summable_xiShiftedReciprocalSquare_pow hy (r + m)).hasSum.mul_left
      ((-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r))
  have hs := hf.hasSum.prod_fiberwise hinner
  have htotal : (∑' p : ℕ × XiZeroCopy, Function.uncurry f p) =
      xiShiftedReciprocalMoment (y + u) m := by
    calc
      (∑' p : ℕ × XiZeroCopy, Function.uncurry f p) =
          ∑' r : ℕ, ∑' q : XiZeroCopy, f r q :=
        hf.tsum_prod_uncurry (fun r => (hinner r).summable)
      _ = ∑' r : ℕ,
          (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
            xiShiftedReciprocalMoment y (r + m) :=
        tsum_congr fun r => (hinner r).tsum_eq
      _ = xiShiftedReciprocalMoment (y + u) m :=
        (xiShiftedReciprocalMoment_add_eq_negativeBinomial_of_abs_lt
          hy hyu huabs m).symm
  rw [htotal] at hs
  exact hs

/-- Real-part form of the local all-order shifted-Xi moment expansion. -/
theorem hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (huabs : |u| < 41 / 2) (m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℝ) ^ r * ((r + m).choose m : ℝ) * u ^ r *
        (xiShiftedReciprocalMoment y (r + m)).re)
      ((xiShiftedReciprocalMoment (y + u) m).re) := by
  have h := Complex.reCLM.hasSum
    (hasSum_xiShiftedReciprocalMoment_add_of_abs_lt hy hyu huabs m)
  have hterm (r : ℕ) :
      Complex.reCLM
          ((-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r *
            xiShiftedReciprocalMoment y (r + m)) =
        (-1 : ℝ) ^ r * ((r + m).choose m : ℝ) * u ^ r *
          (xiShiftedReciprocalMoment y (r + m)).re := by
    have hscalar :
        (-1 : ℂ) ^ r * ((r + m).choose m : ℂ) * (u : ℂ) ^ r =
          (((-1 : ℝ) ^ r * ((r + m).choose m : ℝ) * u ^ r : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hscalar]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  simpa only [Complex.reCLM_apply, hterm] using h

/-- Taylor series of one real shifted-Xi reciprocal moment around an arbitrary positive base. -/
def xiShiftedReciprocalMomentFPowerSeries (y : ℝ) (m : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun r =>
    (-1 : ℝ) ^ r * ((r + m).choose m : ℝ) *
      (xiShiftedReciprocalMoment y (r + m)).re

/-- The real shifted-Xi moment orbit has its exact negative-binomial power series at every positive
base point.  This closes the analytic-germ input needed for moving Padé contact. -/
theorem hasFPowerSeriesAt_re_xiShiftedReciprocalMoment_add
    {y : ℝ} (hy : 0 < y) (m : ℕ) :
    HasFPowerSeriesAt
      (fun u : ℝ => (xiShiftedReciprocalMoment (y + u) m).re)
      (xiShiftedReciprocalMomentFPowerSeries y m) 0 := by
  let c : ℕ → ℝ := fun r =>
    (-1 : ℝ) ^ r * ((r + m).choose m : ℝ) *
      (xiShiftedReciprocalMoment y (r + m)).re
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  let r0 : NNReal := ⟨min (y / 2) 1, by positivity⟩
  have hsumOne : Summable c := by
    have h := (hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
      hy.le (by linarith : 0 ≤ y + 1) (by norm_num : |(1 : ℝ)| < 41 / 2) m).summable
    simpa only [one_pow, mul_one, c] using h
  have hpRadius : (1 : ENNReal) ≤ p.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable_norm (r := (1 : NNReal)) p
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow,
      mul_one] using hsumOne.norm
  have hr0le : (r0 : ENNReal) ≤ 1 := by
    exact ENNReal.coe_le_coe.mpr (by
      change min (y / 2) 1 ≤ 1
      exact min_le_right _ _)
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt
  refine HasFPowerSeriesOnBall.mk (hr0le.trans hpRadius) ?_ ?_
  · exact ENNReal.coe_pos.mpr (by
      change 0 < min (y / 2) 1
      exact lt_min (half_pos hy) zero_lt_one)
  · intro u hu
    have huabs : |u| < min (y / 2) 1 := by
      rw [Metric.mem_eball, edist_dist] at hu
      have hdist : dist u 0 < (r0 : ℝ) :=
        (ENNReal.ofReal_lt_coe_iff (dist_nonneg : 0 ≤ dist u 0)).mp hu
      change |u| < (r0 : ℝ)
      simpa only [dist_zero_right, Real.norm_eq_abs] using hdist
    have hyu : 0 ≤ y + u := by
      have hneg : -(y / 2) < u :=
        lt_of_le_of_lt (neg_le_neg (min_le_left (y / 2) 1)) (abs_lt.mp huabs).1
      linarith
    have huwindow : |u| < 41 / 2 :=
      lt_trans (lt_of_lt_of_le huabs (min_le_right _ _)) (by norm_num)
    have hsum := hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
      hy.le hyu huwindow m
    simpa only [p, c, xiShiftedReciprocalMomentFPowerSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
      mul_assoc, mul_left_comm, mul_comm] using hsum

set_option maxHeartbeats 5000000 in
/-- The universal mass-shift series of one shifted-Xi moment converges absolutely throughout the
unit interval.  This is stronger than conditional Taylor convergence and permits exact polynomial
evaluation of finite Hankel determinants. -/
theorem massShiftMomentPowerSeries_xiShifted_realAbsoluteSummableAt
    {y u : ℝ} (hy : 0 ≤ y) (hu : |u| < 1) (m : ℕ) :
    (GaloisForLFunctions.HTGeometry.massShiftMomentPowerSeries
      (fun k => (xiShiftedReciprocalMoment y k).re) m).RealAbsoluteSummableAt u := by
  have hsumOne : Summable fun r : ℕ =>
      (-1 : ℝ) ^ r * ((r + m).choose m : ℝ) *
        (xiShiftedReciprocalMoment y (r + m)).re := by
    have h := (hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
      hy (by linarith : 0 ≤ y + 1) (by norm_num : |(1 : ℝ)| < 41 / 2) m).summable
    simpa only [one_pow, mul_one] using h
  rw [PowerSeries.RealAbsoluteSummableAt]
  apply (Summable.of_norm_bounded hsumOne.norm ?_).norm
  intro r
  rw [GaloisForLFunctions.HTGeometry.coeff_massShiftMomentPowerSeries]
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  calc
    ‖(-1 : ℝ) ^ r * ((m + r).choose m : ℝ) *
        (xiShiftedReciprocalMoment y (m + r)).re‖ * |u| ^ r ≤
        ‖(-1 : ℝ) ^ r * ((m + r).choose m : ℝ) *
          (xiShiftedReciprocalMoment y (m + r)).re‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg u) hu.le) (norm_nonneg _)
    _ = ‖(-1 : ℝ) ^ r * ((r + m).choose m : ℝ) *
          (xiShiftedReciprocalMoment y (r + m)).re‖ := by
      rw [mul_one, Nat.add_comm m r]

/-- Absolute evaluation of the formal mass-shift series is the actual shifted-Xi moment. -/
theorem realAbsoluteEval_massShiftMomentPowerSeries_xiShifted
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (hu : |u| < 1) (m : ℕ) :
    (GaloisForLFunctions.HTGeometry.massShiftMomentPowerSeries
      (fun k => (xiShiftedReciprocalMoment y k).re) m).realAbsoluteEval u =
        (xiShiftedReciprocalMoment (y + u) m).re := by
  rw [PowerSeries.realAbsoluteEval]
  have hsum := hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
    hy hyu (lt_trans hu (by norm_num : (1 : ℝ) < 41 / 2)) m
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro r
  rw [GaloisForLFunctions.HTGeometry.coeff_massShiftMomentPowerSeries]
  rw [Nat.add_comm m r]
  ring

/-- The determinant of the shifted-Xi Hankel mass-shift series converges absolutely and evaluates
to the actual shifted Hankel determinant. -/
theorem massShiftHankelDet_xiShifted_realAbsoluteSummableAt_and_eval
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (hu : |u| < 1) (N : ℕ) :
    let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
      (fun k => (xiShiftedReciprocalMoment y k).re) N
    A.det.RealAbsoluteSummableAt u ∧
      A.det.realAbsoluteEval u = (xiShiftedMomentHankelMatrix (y + u) N).det := by
  dsimp only
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) N
  have h := GaloisForLFunctions.HTGeometry.massShiftHankelDet_realAbsoluteSummableAt_and_eval
    A u (fun i j => by
      dsimp only [A, GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries,
        GaloisForLFunctions.HTGeometry.finiteHankelMatrixOver]
      exact massShiftMomentPowerSeries_xiShifted_realAbsoluteSummableAt
        hy hu ((i : ℕ) + (j : ℕ)))
  refine ⟨h.1, h.2.trans ?_⟩
  congr 1
  apply Matrix.ext
  intro i j
  dsimp only [A, GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries,
    GaloisForLFunctions.HTGeometry.finiteHankelMatrixOver, Matrix.of_apply]
  rw [realAbsoluteEval_massShiftMomentPowerSeries_xiShifted hy hyu hu]
  rfl

/-- Exact Taylor series of a finite shifted-Xi Hankel determinant under the mass shift. -/
def xiShiftedHankelDetFPowerSeries (y : ℝ) (N : ℕ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun r =>
    PowerSeries.coeff r
      (GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
        (fun k => (xiShiftedReciprocalMoment y k).re) N).det

set_option maxHeartbeats 2000000 in
/-- The finite shifted-Xi Hankel determinant has exactly the universal mass-shift determinant as
its Taylor series at every positive base point. -/
theorem hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add
    {y : ℝ} (hy : 0 < y) (N : ℕ) :
    HasFPowerSeriesAt
      (fun u : ℝ => (xiShiftedMomentHankelMatrix (y + u) N).det)
      (xiShiftedHankelDetFPowerSeries y N) 0 := by
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) N
  let c : ℕ → ℝ := fun r => PowerSeries.coeff r A.det
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c
  let ρ : NNReal := ⟨1 / 2, by norm_num⟩
  let r0 : NNReal := ⟨min (y / 2) (1 / 2), by positivity⟩
  have hdetHalf :=
    (massShiftHankelDet_xiShifted_realAbsoluteSummableAt_and_eval
      hy.le (by linarith : 0 ≤ y + 1 / 2) (by norm_num : |(1 / 2 : ℝ)| < 1) N).1
  have hpRadius : (ρ : ENNReal) ≤ p.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable_norm (r := ρ) p
    dsimp only [p, c, ρ]
    simp only [FormalMultilinearSeries.ofScalars_norm]
    change Summable fun n : ℕ => ‖PowerSeries.coeff n A.det‖ * (1 / 2 : ℝ) ^ n
    rw [PowerSeries.RealAbsoluteSummableAt] at hdetHalf
    simpa only [norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hdetHalf
  have hr0le : (r0 : ENNReal) ≤ ρ := by
    exact ENNReal.coe_le_coe.mpr (by
      change min (y / 2) (1 / 2) ≤ 1 / 2
      exact min_le_right _ _)
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt
  refine HasFPowerSeriesOnBall.mk (hr0le.trans hpRadius) ?_ ?_
  · exact ENNReal.coe_pos.mpr (by
      change 0 < min (y / 2) (1 / 2)
      exact lt_min (half_pos hy) (by norm_num))
  · intro u hu
    have huabs : |u| < min (y / 2) (1 / 2) := by
      rw [Metric.mem_eball, edist_dist] at hu
      have hdist : dist u 0 < (r0 : ℝ) :=
        (ENNReal.ofReal_lt_coe_iff (dist_nonneg : 0 ≤ dist u 0)).mp hu
      change |u| < (r0 : ℝ)
      simpa only [dist_zero_right, Real.norm_eq_abs] using hdist
    have hyu : 0 ≤ y + u := by
      have hneg : -(y / 2) < u :=
        lt_of_le_of_lt (neg_le_neg (min_le_left (y / 2) (1 / 2)))
          (abs_lt.mp huabs).1
      linarith
    have huone : |u| < 1 :=
      lt_trans (lt_of_lt_of_le huabs (min_le_right _ _)) (by norm_num)
    have hdet := massShiftHankelDet_xiShifted_realAbsoluteSummableAt_and_eval
      hy.le hyu huone N
    have hsum : HasSum (fun r : ℕ => PowerSeries.coeff r A.det * u ^ r)
        (A.det.realAbsoluteEval u) := by
      simpa only [PowerSeries.realAbsoluteEval] using hdet.1.of_norm.hasSum
    rw [hdet.2] at hsum
    simpa only [p, c, A, xiShiftedHankelDetFPowerSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hsum

/-- A genuine two-sided sign crossing of a real analytic germ has odd first contact order. -/
theorem odd_of_analytic_first_contact_crossing
    {f : ℝ → ℝ} {c : ℕ → ℝ} {d : ℕ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ c) 0)
    (hzero : ∀ j < d, c j = 0) (hfirst : c d ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ f u)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (-u) < 0) :
    Odd d := by
  let negId : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  let creflect : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * c j
  let cneg : ℕ → ℝ := fun j => -creflect j
  have hf0 : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ c)
      (negId (0 : ℝ)) := by
    simpa [negId] using hf
  have hcomp := hf0.compContinuousLinearMap (u := negId) (x := (0 : ℝ))
  have hcomp' : HasFPowerSeriesAt (f ∘ negId)
      (FormalMultilinearSeries.ofScalars ℝ creflect) 0 := by
    simpa only [negId, creflect,
      FormalMultilinearSeries.ofScalars_comp_neg_id] using hcomp
  have hneg := hcomp'.neg
  have hseries : -(FormalMultilinearSeries.ofScalars ℝ creflect) =
      FormalMultilinearSeries.ofScalars ℝ cneg := by
    ext j
    simp [FormalMultilinearSeries.ofScalars, cneg]
  rw [hseries] at hneg
  have hzeroNeg : ∀ j < d, cneg j = 0 := by
    intro j hj
    simp only [cneg, creflect, hzero j hj, mul_zero, neg_zero]
  have hfirstNeg : cneg d ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num)) hfirst)
  have hrightNeg : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ (-(f ∘ negId)) u := by
    filter_upwards [hleft] with u hu
    change 0 ≤ -f (-u)
    linarith
  have hpos := HTGeometry.leading_scalar_coeff_pos_of_eventually_nonneg_right
    hf hzero hfirst hright
  have hnegPos := HTGeometry.leading_scalar_coeff_pos_of_eventually_nonneg_right
    hneg hzeroNeg hfirstNeg hrightNeg
  rcases Nat.even_or_odd d with heven | hodd
  · dsimp only [cneg, creflect] at hnegPos
    rw [Even.neg_one_pow heven] at hnegPos
    linarith
  · exact hodd

/-! ### Exact moving-null Padé energy -/

/-- Polynomial representative of the Möbius transport of a degree-at-most-`n` null
polynomial.  Its value at `z / (1 + u z)` is `P(z) / (1 + u z)^n`. -/
def mobiusTransportedNullPolynomial
    (P : Polynomial ℝ) (n : ℕ) (u : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    C (P.coeff j) * X ^ j * (1 - C u * X) ^ (n - j)

theorem eval₂_mobiusTransportedNullPolynomial
    {P : Polynomial ℝ} {n : ℕ} (hPdeg : P.natDegree ≤ n)
    {u : ℝ} {z : ℂ} (hden : 1 + (u : ℂ) * z ≠ 0) :
    (mobiusTransportedNullPolynomial P n u).eval₂ Complex.ofRealHom
        (z / (1 + (u : ℂ) * z)) =
      P.eval₂ Complex.ofRealHom z / (1 + (u : ℂ) * z) ^ n := by
  rw [mobiusTransportedNullPolynomial, eval₂_finsetSum]
  rw [P.eval₂_eq_sum_range' Complex.ofRealHom (by omega : P.natDegree < n + 1)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_one,
    eval₂_sub, Complex.ofRealHom_eq_coe]
  have hone : 1 - (u : ℂ) * (z / (1 + (u : ℂ) * z)) =
      1 / (1 + (u : ℂ) * z) := by
    field_simp [hden]
    ring
  rw [hone, div_pow, div_pow]
  field_simp [hden]
  rw [one_pow]
  have hpow : (1 + (u : ℂ) * z) ^ j * (1 + (u : ℂ) * z) ^ (n - j) =
      (1 + (u : ℂ) * z) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hjle]
  rw [← hpow]
  ring

/-- The denominator of a further admissible mass shift never vanishes. -/
theorem one_add_mul_xiShiftedReciprocalSquare_ne_zero
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u) (q : XiZeroCopy) :
    1 + (u : ℂ) * xiShiftedReciprocalSquare y q ≠ 0 := by
  let z := xiZeroCopyReciprocalSquare q
  have hyden := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hy q
  have hyuden := one_add_mul_xiZeroCopyReciprocalSquare_ne_zero hyu q
  have hyden' : 1 + z * (y : ℂ) ≠ 0 := by simpa [z, mul_comm] using hyden
  have hratio : 1 + (u : ℂ) * xiShiftedReciprocalSquare y q =
      (1 + ((y + u : ℝ) : ℂ) * z) / (1 + (y : ℂ) * z) := by
    rw [xiShiftedReciprocalSquare]
    change 1 + (u : ℂ) * (z / (1 + (y : ℂ) * z)) =
      (1 + ((y + u : ℝ) : ℂ) * z) / (1 + (y : ℂ) * z)
    field_simp [hyden, hyden']
    push_cast
    ring
  rw [hratio]
  exact div_ne_zero hyuden hyden

/-- Atomwise representation of a shifted-Xi polynomial-square moment. -/
def xiShiftedPolynomialSquareAtomSum
    (y : ℝ) (P : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    (xiShiftedReciprocalSquare y q *
      (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2).re

theorem momentFunctional_xiShifted_eq_polynomialSquareAtomSum
    {y : ℝ} (hy : 0 ≤ y) (P : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2) =
      xiShiftedPolynomialSquareAtomSum y P := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [xiShiftedReciprocalMoment]
  have hsumm (k : ℕ) : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (k + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy k
  simp_rw [Complex.re_tsum (hsumm _)]
  rw [xiShiftedPolynomialSquareAtomSum]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro q
    have hterm (i : ℕ) :
        (P ^ 2).coeff i * (xiShiftedReciprocalSquare y q ^ (i + 1)).re =
          (((P ^ 2).coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ (i + 1)).re := by
      rw [Complex.mul_re]
      simp
    simp_rw [hterm]
    change (∑ i ∈ (P ^ 2).support,
      Complex.reCLM (((P ^ 2).coeff i : ℂ) *
        xiShiftedReciprocalSquare y q ^ (i + 1))) =
      Complex.reCLM (xiShiftedReciprocalSquare y q *
        (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2)
    rw [← map_sum Complex.reCLM]
    have hfac :
        (∑ i ∈ (P ^ 2).support, ((P ^ 2).coeff i : ℂ) *
          xiShiftedReciprocalSquare y q ^ (i + 1)) =
        xiShiftedReciprocalSquare y q *
          ∑ i ∈ (P ^ 2).support, ((P ^ 2).coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    rw [hfac]
    have heval :
        (∑ i ∈ (P ^ 2).support, ((P ^ 2).coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ i) =
          (P ^ 2).eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q) := by
      rw [eval₂_eq_sum, Polynomial.sum_def]
      rfl
    rw [heval, eval₂_pow]
  · intro k hk
    exact (Complex.reCLM.summable (hsumm k)).mul_left ((P ^ 2).coeff k)

/-- Padé normal energy of `P` under a mass shift by `u`, expressed at the base atoms. -/
def xiShiftedPadeNormalEnergy
    (y : ℝ) (P : Polynomial ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    (xiShiftedReciprocalSquare y q *
      (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2 /
        (1 + (u : ℂ) * xiShiftedReciprocalSquare y q) ^ (2 * n + 1)).re

/-- **Exact moving-null energy law.**  Evaluating the transported null polynomial against the
actual shifted-Xi moment functional is exactly the Padé normal energy.  No boundary or analytic
assumption enters this identity. -/
theorem momentFunctional_mobiusTransportedNullPolynomial_eq_padeNormalEnergy
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u)
    {P : Polynomial ℝ} {n : ℕ} (hPdeg : P.natDegree ≤ n) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (y + u) k).re)
        ((mobiusTransportedNullPolynomial P n u) ^ 2) =
      xiShiftedPadeNormalEnergy y P n u := by
  rw [momentFunctional_xiShifted_eq_polynomialSquareAtomSum hyu]
  rw [xiShiftedPolynomialSquareAtomSum, xiShiftedPadeNormalEnergy]
  apply tsum_congr
  intro q
  let z := xiShiftedReciprocalSquare y q
  have hden : 1 + (u : ℂ) * z ≠ 0 :=
    one_add_mul_xiShiftedReciprocalSquare_ne_zero hy hyu q
  have hflow : xiShiftedReciprocalSquare (y + u) q =
      z / (1 + (u : ℂ) * z) := xiShiftedReciprocalSquare_add hy hyu q
  rw [hflow, eval₂_mobiusTransportedNullPolynomial hPdeg hden]
  congr 1
  rw [div_pow]
  field_simp [hden]
  have hpow : (1 + (u : ℂ) * z) ^ (2 * n + 1) =
      (1 + (u : ℂ) * z) * ((1 + (u : ℂ) * z) ^ n) ^ 2 := by
    rw [show 2 * n + 1 = 1 + n * 2 by omega, pow_add, pow_one, pow_mul]
  rw [hpow]
  ring

/-! ### Analytic Padé normal series -/

/-- Atomwise representation of an arbitrary shifted-Xi polynomial moment. -/
def xiShiftedPolynomialAtomSum
    (y : ℝ) (A : Polynomial ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    (xiShiftedReciprocalSquare y q *
      A.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)).re

theorem momentFunctional_xiShifted_eq_polynomialAtomSum
    {y : ℝ} (hy : 0 ≤ y) (A : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) A =
      xiShiftedPolynomialAtomSum y A := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [xiShiftedReciprocalMoment]
  have hsumm (k : ℕ) : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (k + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy k
  simp_rw [Complex.re_tsum (hsumm _)]
  rw [xiShiftedPolynomialAtomSum]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro q
    have hterm (i : ℕ) :
        A.coeff i * (xiShiftedReciprocalSquare y q ^ (i + 1)).re =
          ((A.coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ (i + 1)).re := by
      rw [Complex.mul_re]
      simp
    simp_rw [hterm]
    change (∑ i ∈ A.support,
      Complex.reCLM ((A.coeff i : ℂ) *
        xiShiftedReciprocalSquare y q ^ (i + 1))) =
      Complex.reCLM (xiShiftedReciprocalSquare y q *
        A.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q))
    rw [← map_sum Complex.reCLM]
    have hfac :
        (∑ i ∈ A.support, (A.coeff i : ℂ) *
          xiShiftedReciprocalSquare y q ^ (i + 1)) =
        xiShiftedReciprocalSquare y q *
          ∑ i ∈ A.support, (A.coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    rw [hfac]
    have heval :
        (∑ i ∈ A.support, (A.coeff i : ℂ) *
            xiShiftedReciprocalSquare y q ^ i) =
          A.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q) := by
      rw [eval₂_eq_sum, Polynomial.sum_def]
      rfl
    rw [heval]
  · intro k hk
    exact (Complex.reCLM.summable (hsumm k)).mul_left (A.coeff k)

/-- Negative-binomial Padé kernel for an arbitrary numerator moment. -/
theorem hasSum_xiShiftedReciprocal_padeKernel_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (huabs : |u| < 41 / 2)
    (q : XiZeroCopy) (N m : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + N).choose N : ℂ) * (u : ℂ) ^ r *
        xiShiftedReciprocalSquare y q ^ (r + m + 1))
      (xiShiftedReciprocalSquare y q ^ (m + 1) /
        (1 + (u : ℂ) * xiShiftedReciprocalSquare y q) ^ (N + 1)) := by
  let z := xiShiftedReciprocalSquare y q
  have hz : ‖z‖ < (2 / 41 : ℝ) :=
    lt_of_le_of_lt (norm_xiShiftedReciprocalSquare_le hy q)
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q)
  have hur : |u| * (2 / 41 : ℝ) < 1 := by nlinarith [abs_nonneg u]
  have huz : ‖-((u : ℂ) * z)‖ < 1 := by
    by_cases hu0 : u = 0
    · subst u
      norm_num
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_lt_mul_of_pos_left hz (abs_pos.mpr hu0)).trans hur
  have hseries := hasSum_choose_mul_geometric_of_norm_lt_one N huz
  have hmul := hseries.mul_left (z ^ (m + 1))
  change HasSum (fun r : ℕ =>
      (-1 : ℂ) ^ r * ((r + N).choose N : ℂ) * (u : ℂ) ^ r *
        z ^ (r + m + 1))
    (z ^ (m + 1) / (1 + (u : ℂ) * z) ^ (N + 1))
  convert hmul using 2
  · exact rfl
  · rw [pow_add]
    ring
  · ring

/-- Absolute summability needed to interchange contact order and Xi-zero copy. -/
theorem summable_xiShiftedReciprocal_padeKernel_double_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (huabs : |u| < 41 / 2) (N m : ℕ) :
    Summable (fun p : ℕ × XiZeroCopy =>
      (-1 : ℂ) ^ p.1 * ((p.1 + N).choose N : ℂ) * (u : ℂ) ^ p.1 *
        xiShiftedReciprocalSquare y p.2 ^ (p.1 + m + 1)) := by
  let R : ℝ := 2 / 41
  let a : ℕ → ℝ := fun r => ((r + N).choose N : ℝ) * (|u| * R) ^ r
  let b : XiZeroCopy → ℝ := fun q => ‖xiShiftedReciprocalSquare y q ^ (m + 1)‖
  have htheta0 : 0 ≤ |u| * R := by dsimp only [R]; positivity
  have htheta : |u| * R < 1 := by dsimp only [R]; nlinarith [abs_nonneg u]
  have ha : Summable a := by
    apply summable_choose_mul_geometric_of_norm_lt_one N
    rw [Real.norm_eq_abs, abs_of_nonneg htheta0]
    exact htheta
  have hb : Summable b := by
    simpa only [b] using (summable_xiShiftedReciprocalSquare_pow hy m).norm
  have hab : Summable (fun p : ℕ × XiZeroCopy => a p.1 * b p.2) :=
    ha.mul_of_nonneg hb (fun r => by positivity) (fun q => norm_nonneg _)
  apply Summable.of_norm_bounded hab
  rintro ⟨r, q⟩
  have hz : ‖xiShiftedReciprocalSquare y q‖ ≤ R :=
    (norm_xiShiftedReciprocalSquare_le hy q).trans
      (norm_xiZeroCopyReciprocalSquare_lt_two_over_fortyOne q).le
  change ‖(-1 : ℂ) ^ r * ((r + N).choose N : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + m + 1)‖ ≤ a r * b q
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, a, b]
  rw [show r + m + 1 = r + (m + 1) by omega, pow_add]
  have hcore : |u| ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r ≤
      (|u| * R) ^ r := by
    rw [mul_pow]
    gcongr
  calc
    ((r + N).choose N : ℝ) * |u| ^ r *
          (‖xiShiftedReciprocalSquare y q‖ ^ r *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1)) =
        ((r + N).choose N : ℝ) *
          (|u| ^ r * ‖xiShiftedReciprocalSquare y q‖ ^ r) *
            ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by ring
    _ ≤ ((r + N).choose N : ℝ) * (|u| * R) ^ r *
          ‖xiShiftedReciprocalSquare y q‖ ^ (m + 1) := by gcongr

set_option maxHeartbeats 1200000 in
/-- The Padé normal energy is exactly the convergent contact series throughout the local disk. -/
theorem hasSum_xiShiftedPadeNormalEnergy_of_abs_lt
    {y u : ℝ} (hy : 0 ≤ y) (huabs : |u| < 41 / 2)
    (P : Polynomial ℝ) (n : ℕ) :
    HasSum (fun r : ℕ =>
      (-1 : ℝ) ^ r * ((2 * n + r).choose r : ℝ) * u ^ r *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ r))
      (xiShiftedPadeNormalEnergy y P n u) := by
  let f : ℕ → XiZeroCopy → ℂ := fun r q =>
    (-1 : ℂ) ^ r * ((r + 2 * n).choose (2 * n) : ℂ) * (u : ℂ) ^ r *
      xiShiftedReciprocalSquare y q ^ (r + 1) *
        (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2
  have hf : Summable (Function.uncurry f) := by
    have hfinite : Summable (fun p : ℕ × XiZeroCopy =>
        ∑ i ∈ (P ^ 2).support, (((P ^ 2).coeff i : ℝ) : ℂ) *
          ((-1 : ℂ) ^ p.1 * ((p.1 + 2 * n).choose (2 * n) : ℂ) *
            (u : ℂ) ^ p.1 *
              xiShiftedReciprocalSquare y p.2 ^ (p.1 + i + 1))) := by
      exact summable_sum fun i _ =>
        (summable_xiShiftedReciprocal_padeKernel_double_of_abs_lt
          hy huabs (2 * n) i).mul_left (((P ^ 2).coeff i : ℝ) : ℂ)
    apply hfinite.congr
    rintro ⟨r, q⟩
    dsimp only [Function.uncurry_apply_pair, f]
    rw [← eval₂_pow, eval₂_eq_sum, Polynomial.sum_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.ofRealHom_eq_coe]
    rw [show r + i + 1 = (r + 1) + i by omega, pow_add]
    ring
  have hfre : Summable (fun p : ℕ × XiZeroCopy =>
      (Function.uncurry f p).re) := Complex.reCLM.summable hf
  have hpoint (q : XiZeroCopy) :
      HasSum (fun r : ℕ => (f r q).re)
        (xiShiftedReciprocalSquare y q *
          (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2 /
            (1 + (u : ℂ) * xiShiftedReciprocalSquare y q) ^ (2 * n + 1)).re := by
    have hk := hasSum_xiShiftedReciprocal_padeKernel_of_abs_lt
      hy huabs q (2 * n) 0
    have hmul := hk.mul_right
      ((P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2)
    have hre := Complex.reCLM.hasSum hmul
    have hre' : HasSum (fun r : ℕ => (f r q).re)
        (Complex.reCLM
          (xiShiftedReciprocalSquare y q ^ (0 + 1) /
            (1 + (u : ℂ) * xiShiftedReciprocalSquare y q) ^ (2 * n + 1) *
              (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q)) ^ 2)) := by
      apply HasSum.congr_fun hre
      intro r
      simp only [f, Complex.reCLM_apply]
    convert hre' using 1
    simp only [Complex.reCLM_apply, zero_add, pow_one]
    congr 1
    ring
  have htotal : (∑' p : ℕ × XiZeroCopy, (Function.uncurry f p).re) =
      xiShiftedPadeNormalEnergy y P n u := by
    calc
      (∑' p : ℕ × XiZeroCopy, (Function.uncurry f p).re) =
          ∑' r : ℕ, ∑' q : XiZeroCopy, (f r q).re := hfre.tsum_prod
      _ = ∑' q : XiZeroCopy, ∑' r : ℕ, (f r q).re := hfre.tsum_comm.symm
      _ = xiShiftedPadeNormalEnergy y P n u := by
        rw [xiShiftedPadeNormalEnergy]
        apply tsum_congr
        intro q
        exact (hpoint q).tsum_eq
  have houter : HasSum (fun r : ℕ => ∑' q : XiZeroCopy, (f r q).re)
      (∑' p : ℕ × XiZeroCopy, (Function.uncurry f p).re) :=
    hfre.hasSum.prod_fiberwise fun r => (hfre.prod_factor r).hasSum
  rw [htotal] at houter
  apply HasSum.congr_fun houter
  intro r
  rw [momentFunctional_xiShifted_eq_polynomialAtomSum hy]
  rw [xiShiftedPolynomialAtomSum]
  have hscalar :
      ((-1 : ℝ) ^ r * ((2 * n + r).choose r : ℝ) * u ^ r) =
        ((-1 : ℝ) ^ r * ((r + 2 * n).choose (2 * n) : ℝ) * u ^ r) := by
    rw [Nat.add_comm (2 * n) r, Nat.choose_symm_add]
  rw [hscalar, ← tsum_mul_left]
  apply tsum_congr
  intro q
  simp only [eval₂_mul, eval₂_pow, eval₂_X]
  let a : ℝ := (-1 : ℝ) ^ r * ((r + 2 * n).choose (2 * n) : ℝ) * u ^ r
  let Z : ℂ := xiShiftedReciprocalSquare y q *
    (P.eval₂ Complex.ofRealHom (xiShiftedReciprocalSquare y q) ^ 2 *
      xiShiftedReciprocalSquare y q ^ r)
  change a * Z.re = (f r q).re
  calc
    a * Z.re = (((a : ℝ) : ℂ) * Z).re := by simp
    _ = (f r q).re := by
      congr 1
      dsimp only [a, Z, f]
      push_cast
      ring

/-- Exact analytic germ of the Padé normal energy. -/
theorem hasFPowerSeriesAt_xiShiftedPadeNormalEnergy
    {y : ℝ} (hy : 0 ≤ y) (P : Polynomial ℝ) (n : ℕ) :
    HasFPowerSeriesAt
      (xiShiftedPadeNormalEnergy y P n)
      (HTGeometry.mobiusPadeContactFPowerSeries
        (fun k => (xiShiftedReciprocalMoment y k).re) P n) 0 := by
  let c : ℕ → ℝ := fun r =>
    (-1 : ℝ) ^ r * ((2 * n + r).choose r : ℝ) *
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ r)
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ c
  have hsumOne : Summable c := by
    have h := (hasSum_xiShiftedPadeNormalEnergy_of_abs_lt hy
      (by norm_num : |(1 : ℝ)| < 41 / 2) P n).summable
    simpa only [one_pow, mul_one, c] using h
  have hpRadius : (1 : ENNReal) ≤ p.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable_norm (r := (1 : NNReal)) p
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow,
      mul_one] using hsumOne.norm
  have hp : HTGeometry.mobiusPadeContactFPowerSeries
      (fun k => (xiShiftedReciprocalMoment y k).re) P n = p := by
    simp only [p, c, HTGeometry.mobiusPadeContactFPowerSeries,
      HTGeometry.coeff_mobiusPadeContactSeries]
  rw [hp]
  apply HasFPowerSeriesOnBall.hasFPowerSeriesAt
  refine HasFPowerSeriesOnBall.mk hpRadius zero_lt_one ?_
  intro u hu
  have huabs : |u| < 1 := by
    rw [Metric.mem_eball, edist_dist] at hu
    have hdist : dist u 0 < (1 : ℝ) :=
      (ENNReal.ofReal_lt_coe_iff (dist_nonneg : 0 ≤ dist u 0)).mp hu
    simpa only [dist_zero_right, Real.norm_eq_abs] using hdist
  have hsum := hasSum_xiShiftedPadeNormalEnergy_of_abs_lt hy
    (lt_trans huabs (by norm_num : (1 : ℝ) < 41 / 2)) P n
  simpa only [p, c, HTGeometry.mobiusPadeContactFPowerSeries,
    HTGeometry.coeff_mobiusPadeContactSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add,
    mul_assoc, mul_left_comm, mul_comm] using hsum

/-- Moment functional of a finite atomic moment sequence. -/
theorem momentFunctional_finiteAtomicMoment
    (S : Finset ℝ) (w : ℝ → ℝ) (A : Polynomial ℝ) :
    HTGeometry.momentFunctional (fun k => ∑ x ∈ S, w x * x ^ k) A =
      ∑ x ∈ S, w x * A.eval x := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [A.eval_eq_sum]
  simp only [Polynomial.sum_def]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem momentFunctional_sequence_sub
    (s q : ℕ → ℝ) (A : Polynomial ℝ) :
    HTGeometry.momentFunctional (fun k => s k - q k) A =
      HTGeometry.momentFunctional s A - HTGeometry.momentFunctional q A := by
  simp only [HTGeometry.momentFunctional_eq_support_sum, mul_sub,
    Finset.sum_sub_distrib]

/-- The canonical flat quadrature contributes zero to every null-square contact coefficient. -/
theorem momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (j : ℕ) :
    HTGeometry.momentFunctional
        (HTGeometry.finiteHankelBoundaryPadeDefect s c)
        ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * X ^ j) =
      HTGeometry.momentFunctional s
        ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * X ^ j) := by
  let q : ℕ → ℝ := fun k =>
    ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
      HTGeometry.finiteHankelBoundaryWeight s c x * x ^ k
  have hq : HTGeometry.momentFunctional q
      ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * X ^ j) = 0 := by
    rw [momentFunctional_finiteAtomicMoment]
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul, eval_pow,
      HTGeometry.finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx]
    simp
  change HTGeometry.momentFunctional (fun k => s k - q k)
      ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * X ^ j) = _
  rw [momentFunctional_sequence_sub, hq, sub_zero]

/-- The flat quadrature annihilates the null square times an arbitrary polynomial, not only a
monomial.  This is the linear multiplier form needed to expose the whole lifted null subspace. -/
theorem momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (A : Polynomial ℝ) :
    HTGeometry.momentFunctional
        (HTGeometry.finiteHankelBoundaryPadeDefect s c)
        ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * A) =
      HTGeometry.momentFunctional s
        ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * A) := by
  let q : ℕ → ℝ := fun k =>
    ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
      HTGeometry.finiteHankelBoundaryWeight s c x * x ^ k
  have hq : HTGeometry.momentFunctional q
      ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * A) = 0 := by
    rw [momentFunctional_finiteAtomicMoment]
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul, eval_pow,
      HTGeometry.finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx]
    simp
  change HTGeometry.momentFunctional (fun k => s k - q k)
      ((HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2 * A) = _
  rw [momentFunctional_sequence_sub, hq, sub_zero]

/-- Contact series of the actual Xi moments equals that of the flat-shadow defect. -/
theorem mobiusPadeContactFPowerSeries_boundaryDefect_eq_xiShifted
    {y : ℝ} (_hy : 0 ≤ y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    HTGeometry.mobiusPadeContactFPowerSeries
        (HTGeometry.finiteHankelBoundaryPadeDefect
          (fun k => (xiShiftedReciprocalMoment y k).re) c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n =
      HTGeometry.mobiusPadeContactFPowerSeries
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n := by
  simp only [HTGeometry.mobiusPadeContactFPowerSeries]
  congr 1
  funext j
  rw [HTGeometry.coeff_mobiusPadeContactSeries,
    HTGeometry.coeff_mobiusPadeContactSeries,
    momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X]

/-- The actual boundary energy has the exact flat-shadow defect contact series. -/
theorem hasFPowerSeriesAt_xiShiftedPadeNormalEnergy_boundaryDefect
    {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    HasFPowerSeriesAt
      (xiShiftedPadeNormalEnergy y
        (HTGeometry.finiteHankelNullMonicPolynomial c) n)
      (HTGeometry.mobiusPadeContactFPowerSeries
        (HTGeometry.finiteHankelBoundaryPadeDefect
          (fun k => (xiShiftedReciprocalMoment y k).re) c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n) 0 := by
  rw [mobiusPadeContactFPowerSeries_boundaryDefect_eq_xiShifted hy]
  exact hasFPowerSeriesAt_xiShiftedPadeNormalEnergy hy
    (HTGeometry.finiteHankelNullMonicPolynomial c) n

/-! ### Right-cone orientation and crossing exclusion -/

theorem natDegree_mobiusTransportedNullPolynomial_le
    (P : Polynomial ℝ) (n : ℕ) (u : ℝ) :
    (mobiusTransportedNullPolynomial P n u).natDegree ≤ n := by
  rw [mobiusTransportedNullPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc
    (C (P.coeff j) * X ^ j * (1 - C u * X) ^ (n - j)).natDegree ≤
        (C (P.coeff j) * X ^ j).natDegree +
          ((1 - C u * X) ^ (n - j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ j + (n - j) := by
      gcongr
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
      · calc
          ((1 - C u * X) ^ (n - j)).natDegree ≤
              (n - j) * (1 - C u * X).natDegree := Polynomial.natDegree_pow_le
          _ ≤ (n - j) * 1 := by
            gcongr
            exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp)
              ((Polynomial.natDegree_C_mul_le u X).trans (by simp)))
          _ = n - j := by omega
    _ = n := Nat.add_sub_of_le hjle

/-- A positive-semidefinite finite Hankel block makes every represented polynomial square
nonnegative. -/
theorem momentFunctional_sq_nonneg_of_momentHankelMatrix_posSemidef
    {s : ℕ → ℝ} {N : ℕ}
    (hpsd : (HTGeometry.momentHankelMatrix s N).PosSemidef)
    {P : Polynomial ℝ} (hPdeg : P.natDegree < N) :
    0 ≤ HTGeometry.momentFunctional s (P ^ 2) := by
  let a : Fin N → ℝ := Polynomial.toFn N P
  have hpof : Polynomial.ofFn N a = P :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hPdeg
  have hquad := hpsd.dotProduct_mulVec_nonneg a
  rw [star_trivial, HTGeometry.dotProduct_mulVec_momentHankelMatrix, hpof] at hquad
  exact hquad

/-- Right-shifted Xi Hankel positivity makes the transported Padé normal energy nonnegative. -/
theorem xiShiftedPadeNormalEnergy_nonneg_of_momentHankelMatrix_posSemidef
    {y u : ℝ} (hy : 0 ≤ y) (hyu : 0 ≤ y + u)
    {P : Polynomial ℝ} {n : ℕ}
    (hPdeg : P.natDegree ≤ n)
    (hpsd : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (n + 1)).PosSemidef) :
    0 ≤ xiShiftedPadeNormalEnergy y P n u := by
  rw [← momentFunctional_mobiusTransportedNullPolynomial_eq_padeNormalEnergy
    (P := P) (n := n) hy hyu hPdeg]
  exact momentFunctional_sq_nonneg_of_momentHankelMatrix_posSemidef hpsd
    (lt_of_le_of_lt (natDegree_mobiusTransportedNullPolynomial_le P n u)
      (Nat.lt_succ_self n))

/-- **Scalar Schur gate for one new Hankel degree.**  Once the preceding shifted-Xi block is
positive definite, positivity of the next block is controlled by its single remaining Schur
coordinate, equivalently by the sign of its determinant.  This turns a first-loss question into
one scalar analytic parity question. -/
theorem xiShiftedMomentHankelMatrix_succ_posSemidef_iff_det_nonneg_of_head_posDef
    {y : ℝ} {n : ℕ}
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef) :
    (xiShiftedMomentHankelMatrix y (n + 1)).PosSemidef ↔
      0 ≤ (xiShiftedMomentHankelMatrix y (n + 1)).det := by
  constructor
  · exact fun h => h.det_nonneg
  · intro hdet
    let A : Matrix (Fin n) (Fin n) ℝ := xiShiftedMomentHankelMatrix y n
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
      Matrix.reindex e.symm e.symm (xiShiftedMomentHankelMatrix y (n + 1))
    let B : Matrix (Fin n) (Fin 1) ℝ := M.toBlocks₁₂
    let D : Matrix (Fin 1) (Fin 1) ℝ := M.toBlocks₂₂
    have hA : A.PosDef := hhead
    letI : Invertible A := hA.isUnit.invertible
    let S : Matrix (Fin 1) (Fin 1) ℝ := D - B.conjTranspose * A⁻¹ * B
    have h11 : M.toBlocks₁₁ = A := by
      ext i j
      rfl
    have h21 : M.toBlocks₂₁ = B.conjTranspose := by
      ext i j
      simp [M, B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
        xiShiftedMomentHankelMatrix,
        GaloisForLFunctions.HTGeometry.finiteHankelMatrix, add_comm]
    have hblock : Matrix.fromBlocks A B B.conjTranspose D = M := by
      rw [← h11, ← h21]
      exact Matrix.fromBlocks_toBlocks _
    have hdetM : 0 ≤ M.det := by
      change 0 ≤ (Matrix.reindex e.symm e.symm
        (xiShiftedMomentHankelMatrix y (n + 1))).det
      rwa [Matrix.det_reindex_self]
    have hfactor : M.det = A.det * S.det := by
      rw [← hblock, Matrix.det_fromBlocks₁₁]
      rw [Matrix.invOf_eq_nonsing_inv]
    have hdetS : 0 ≤ S.det := by
      have hprod : 0 ≤ A.det * S.det := hfactor ▸ hdetM
      nlinarith [hA.det_pos]
    have hS : S.PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      constructor
      · apply Matrix.IsHermitian.ext
        intro i j
        fin_cases i
        fin_cases j
        simp
      · intro x
        rw [Matrix.det_fin_one] at hdetS
        simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
        nlinarith [sq_nonneg (x 0)]
    have hblockPSD : (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef :=
      (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS
    have hM : M.PosSemidef := hblock ▸ hblockPSD
    have hback := hM.submatrix e.symm
    simpa [M, Matrix.reindex_apply, Matrix.submatrix_submatrix] using hback

/-- Positive definiteness of a finite shifted-Xi Hankel head persists on a neighborhood of every
positive mass parameter.  Proof is recursive Schur geometry: each preceding head persists, while
analyticity keeps the next determinant strictly positive. -/
theorem eventually_posDef_xiShiftedMomentHankelMatrix_add
    {y : ℝ} (hy : 0 < y) {N : ℕ}
    (hN : (xiShiftedMomentHankelMatrix y N).PosDef) :
    ∀ᶠ u in nhds (0 : ℝ), (xiShiftedMomentHankelMatrix (y + u) N).PosDef := by
  induction N with
  | zero =>
      filter_upwards with u
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨xiShiftedMomentHankelMatrix_isHermitian (y + u) 0, ?_⟩
      intro x hx
      exact (hx (Subsingleton.elim x 0)).elim
  | succ n ih =>
      have hsub := hN.submatrix (Fin.castSucc_injective n)
      have hhead : (xiShiftedMomentHankelMatrix y n).PosDef := by
        have hmatrix :
            (xiShiftedMomentHankelMatrix y (n + 1)).submatrix
                Fin.castSucc Fin.castSucc = xiShiftedMomentHankelMatrix y n := by
          ext i j
          rfl
        exact hmatrix ▸ hsub
      have hheadEv := ih hhead
      let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det
      have hf : ContinuousAt f 0 :=
        (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 1)).continuousAt
      have hf0 : 0 < f 0 := by
        simpa only [f, add_zero] using hN.det_pos
      have hdetEv : ∀ᶠ u in nhds (0 : ℝ), 0 < f u :=
        (continuousAt_const.eventually_lt hf hf0)
      filter_upwards [hheadEv, hdetEv] with u huhead hudet
      have hpsd :=
        (xiShiftedMomentHankelMatrix_succ_posSemidef_iff_det_nonneg_of_head_posDef
          huhead).2 hudet.le
      exact hpsd.posDef_iff_det_ne_zero.mpr hudet.ne'

/-- **Genuine crossing parity law.**  At a corank-one shifted-Xi Hankel boundary, if the next block
is positive semidefinite immediately to the right and fails to be positive semidefinite immediately
to the left, then the first nonzero flat-shadow contact order is odd.  Head stability and all
determinant signs are derived rather than assumed. -/
theorem odd_first_contact_of_genuine_xiShiftedHankel_crossing
    {y : ℝ} (hy : 0 < y) {n d : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    Odd d := by
  let A := GaloisForLFunctions.HTGeometry.massShiftHankelPowerSeries
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1)
  let a : ℕ → ℝ := fun j => PowerSeries.coeff j A.det
  let f : ℝ → ℝ := fun u => (xiShiftedMomentHankelMatrix (y + u) (n + 1)).det
  have hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ a) 0 := by
    simpa only [f, a, A, xiShiftedHankelDetFPowerSeries] using
      (hasFPowerSeriesAt_det_xiShiftedMomentHankelMatrix_add hy (n + 1))
  have haZero : ∀ j < d, a j = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      dsimp only [a, A]
      rw [GaloisForLFunctions.HTGeometry.coeff_zero_det_massShiftHankelPowerSeries]
      have hdet : (xiShiftedMomentHankelMatrix y (n + 1)).det = 0 := by
        apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hc
          (i := Fin.last n)
        exact mem_nonZeroDivisors_iff_ne_zero.mpr hlast
      rw [show HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) =
          xiShiftedMomentHankelMatrix y (n + 1) by
        ext i j
        rfl]
      exact hdet
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hzeroj : ∀ k < 2 * n + j,
          xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
        intro k hk
        exact hzero k (by omega)
      dsimp only [a, A]
      rw [coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
        c hhead hc hlast hjpos hzeroj]
      rw [hzero (2 * n + j) (by omega)]
      ring
  have haFirst : a d ≠ 0 := by
    dsimp only [a, A]
    rw [coeff_det_massShiftHankelPowerSeries_xiShifted_at_first_contact
      c hhead hc hlast hd hzero]
    exact mul_ne_zero hhead.det_pos.ne'
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega))))
        hfirst)
  have hrightDet : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ f u := by
    filter_upwards [hright] with u hu
    exact hu.det_nonneg
  have hheadEv := eventually_posDef_xiShiftedMomentHankelMatrix_add hy hhead
  have hheadReflected : ∀ᶠ u in nhds (0 : ℝ),
      (xiShiftedMomentHankelMatrix (y - u) n).PosDef := by
    have hneg : ContinuousAt (fun u : ℝ => -u) 0 := continuousAt_id.neg
    have hnegT : Filter.Tendsto (fun u : ℝ => -u) (nhds 0) (nhds 0) := by
      simpa only [neg_zero] using hneg.tendsto
    have hreflected := hnegT.eventually hheadEv
    simpa only [sub_eq_add_neg] using hreflected
  have hleftDet : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (-u) < 0 := by
    filter_upwards [hleft, hheadReflected.filter_mono inf_le_left] with u hu hhu
    have hgate :=
      xiShiftedMomentHankelMatrix_succ_posSemidef_iff_det_nonneg_of_head_posDef hhu
    have hnot : ¬ 0 ≤ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).det := by
      exact fun hdet => hu (hgate.2 hdet)
    dsimp only [f]
    rw [show y + -u = y - u by ring]
    exact lt_of_not_ge hnot
  exact odd_of_analytic_first_contact_crossing hf haZero haFirst hrightDet hleftDet

/-- **Closed Xi contact-parity law.**  Right-neighborhood Hankel positivity fixes the alternating
sign of the first nonzero flat-shadow defect, with no abstract analytic-series premise. -/
theorem signed_first_xiShiftedHankelBoundaryPadeDefect_pos_of_right_posSemidef
    {y : ℝ} (hy : 0 ≤ y) {n d : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0)
    (hpsd : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef) :
    0 < (-1 : ℝ) ^ d * xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) := by
  apply HTGeometry.signed_first_defect_pos_of_right_nonnegative_contact
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    hd hzero hfirst
  · change HasFPowerSeriesAt
      (xiShiftedPadeNormalEnergy y
        (HTGeometry.finiteHankelNullMonicPolynomial c) n)
      (HTGeometry.mobiusPadeContactFPowerSeries
        (HTGeometry.finiteHankelBoundaryPadeDefect
          (fun k => (xiShiftedReciprocalMoment y k).re) c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) n) 0
    exact hasFPowerSeriesAt_xiShiftedPadeNormalEnergy_boundaryDefect hy c
  · filter_upwards [hpsd, self_mem_nhdsWithin] with u huPSD hu
    have hu0 : 0 < u := hu
    apply xiShiftedPadeNormalEnergy_nonneg_of_momentHankelMatrix_posSemidef
      hy (by linarith)
      (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast).le
    have hmatrix : xiShiftedMomentHankelMatrix (y + u) (n + 1) =
        HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment (y + u) k).re) (n + 1) := rfl
    rwa [hmatrix] at huPSD

/-- An opposite source sign excludes continued right-neighborhood Hankel positivity. -/
theorem not_eventually_right_xiShiftedMomentHankelMatrix_posSemidef_of_source_opposite
    {y : ℝ} (hy : 0 ≤ y) {n d : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0)
    (hsource : (-1 : ℝ) ^ d *
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) < 0) :
    ¬ ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef := by
  intro hpsd
  have hforced :=
    signed_first_xiShiftedHankelBoundaryPadeDefect_pos_of_right_posSemidef
      hy c hlast hd hzero hfirst hpsd
  linarith

/-- **Ordinary Route-U crossing exclusion.**  A positive monic extension remainder at a flat Xi
Hankel face is incompatible with positive semidefiniteness on every sufficiently small right
shift. -/
theorem not_eventually_right_xiShiftedMomentHankelMatrix_posSemidef_of_monicRemainder_pos
    {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hremainder : 0 < xiShiftedHankelBoundaryMonicRemainder y c) :
    ¬ ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef := by
  let d : ℕ := 1
  have hzero : ∀ k < 2 * n + d,
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    apply xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le c hhead hc hlast
    dsimp only [d] at hk
    omega
  have hdefect : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) =
      xiShiftedHankelBoundaryMonicRemainder y c := by
    dsimp only [d]
    exact xiShiftedHankelBoundaryPadeDefect_first_eq_monicRemainder
      c hhead hc hlast
  have hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0 := by
    rw [hdefect]
    exact ne_of_gt hremainder
  have hsource : (-1 : ℝ) ^ d *
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) < 0 := by
    rw [hdefect]
    dsimp only [d]
    linarith
  exact not_eventually_right_xiShiftedMomentHankelMatrix_posSemidef_of_source_opposite
    hy c hlast (by simp [d]) hzero hfirst hsource

/-! ### Infinite-contact exclusion from the infinite Xi divisor -/

/-- Denominator factor of one finite atomic Möbius trajectory in the centered Xi coordinate. -/
def finiteAtomicXiDenominatorFactor (y x : ℝ) : Polynomial ℂ :=
  1 + C (x : ℂ) * (X ^ 2 - C (y : ℂ))

/-- Common denominator of a finite atomic Möbius trajectory. -/
def finiteAtomicXiDenominatorPolynomial (y : ℝ) (S : Finset ℝ) : Polynomial ℂ :=
  ∏ x ∈ S, finiteAtomicXiDenominatorFactor y x

/-- Cleared numerator of `w * ∑ x in S, weight x / (1 + (w²-y)x)`. -/
def finiteAtomicXiNumeratorPolynomial
    (y : ℝ) (S : Finset ℝ) (weight : ℝ → ℝ) : Polynomial ℂ :=
  X * ∑ x ∈ S, C (weight x : ℂ) *
    ∏ z ∈ S.erase x, finiteAtomicXiDenominatorFactor y z

theorem finiteAtomicXiDenominatorFactor_ne_zero (y x : ℝ) :
    finiteAtomicXiDenominatorFactor y x ≠ 0 := by
  by_cases hx : x = 0
  · simp [finiteAtomicXiDenominatorFactor, hx]
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 2) hzero
  norm_num [finiteAtomicXiDenominatorFactor, Polynomial.coeff_one] at hcoeff
  exact hx hcoeff

theorem finiteAtomicXiDenominatorPolynomial_ne_zero (y : ℝ) (S : Finset ℝ) :
    finiteAtomicXiDenominatorPolynomial y S ≠ 0 := by
  simp only [finiteAtomicXiDenominatorPolynomial]
  exact Finset.prod_ne_zero_iff.mpr fun x hx =>
    finiteAtomicXiDenominatorFactor_ne_zero y x

theorem eval_finiteAtomicXiDenominatorFactor (y x : ℝ) (w : ℂ) :
    (finiteAtomicXiDenominatorFactor y x).eval w =
      1 + (x : ℂ) * (w ^ 2 - (y : ℂ)) := by
  simp [finiteAtomicXiDenominatorFactor]

theorem eval_finiteAtomicXiDenominatorPolynomial (y : ℝ) (S : Finset ℝ) (w : ℂ) :
    (finiteAtomicXiDenominatorPolynomial y S).eval w =
      ∏ x ∈ S, (1 + (x : ℂ) * (w ^ 2 - (y : ℂ))) := by
  rw [finiteAtomicXiDenominatorPolynomial, eval_prod]
  apply Finset.prod_congr rfl
  intro x hx
  exact eval_finiteAtomicXiDenominatorFactor y x w

theorem eval_finiteAtomicXiNumeratorPolynomial
    (y : ℝ) (S : Finset ℝ) (weight : ℝ → ℝ) (w : ℂ) :
    (finiteAtomicXiNumeratorPolynomial y S weight).eval w =
      w * ∑ x ∈ S, (weight x : ℂ) *
        ∏ z ∈ S.erase x, (1 + (z : ℂ) * (w ^ 2 - (y : ℂ))) := by
  rw [finiteAtomicXiNumeratorPolynomial, eval_mul, eval_X]
  congr 1
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro z hz
  exact eval_finiteAtomicXiDenominatorFactor y z w

/-- Clearing the common denominator of a finite atomic Möbius trajectory gives its polynomial
numerator. -/
theorem finiteAtomicXiDenominator_mul_trajectory
    (y : ℝ) (S : Finset ℝ) (weight : ℝ → ℝ) (w : ℂ)
    (hden : ∀ x ∈ S, 1 + (x : ℂ) * (w ^ 2 - (y : ℂ)) ≠ 0) :
    (finiteAtomicXiDenominatorPolynomial y S).eval w *
        (w * ∑ x ∈ S, (weight x : ℂ) /
          (1 + (x : ℂ) * (w ^ 2 - (y : ℂ)))) =
      (finiteAtomicXiNumeratorPolynomial y S weight).eval w := by
  rw [eval_finiteAtomicXiDenominatorPolynomial,
    eval_finiteAtomicXiNumeratorPolynomial]
  calc
    (∏ x ∈ S, (1 + (x : ℂ) * (w ^ 2 - (y : ℂ)))) *
          (w * ∑ x ∈ S, (weight x : ℂ) /
            (1 + (x : ℂ) * (w ^ 2 - (y : ℂ)))) =
        w * ∑ x ∈ S,
          (∏ z ∈ S, (1 + (z : ℂ) * (w ^ 2 - (y : ℂ)))) *
            ((weight x : ℂ) / (1 + (x : ℂ) * (w ^ 2 - (y : ℂ)))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = w * ∑ x ∈ S, (weight x : ℂ) *
          ∏ z ∈ S.erase x, (1 + (z : ℂ) * (w ^ 2 - (y : ℂ))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hprod := Finset.mul_prod_erase S
        (fun z : ℝ => 1 + (z : ℂ) * (w ^ 2 - (y : ℂ))) hx
      rw [← hprod]
      field_simp [hden x hx]

/-- Entire relation obtained by clearing a putative finite atomic model for the shifted-Xi
moment germ. -/
def finiteAtomicXiClearedRelation
    (y : ℝ) (S : Finset ℝ) (weight : ℝ → ℝ) (w : ℂ) : ℂ :=
  (finiteAtomicXiDenominatorPolynomial y S).eval w * deriv xi (1 / 2 + w) -
    (finiteAtomicXiNumeratorPolynomial y S weight).eval w * xi (1 / 2 + w)

theorem differentiable_finiteAtomicXiClearedRelation
    (y : ℝ) (S : Finset ℝ) (weight : ℝ → ℝ) :
    Differentiable ℂ (finiteAtomicXiClearedRelation y S weight) := by
  unfold finiteAtomicXiClearedRelation
  intro w
  have hshift : HasDerivAt (fun z : ℂ => 1 / 2 + z) 1 w := by
    simpa using (hasDerivAt_id w).const_add (1 / 2 : ℂ)
  have hD := (show DifferentiableAt ℂ
      (fun z => (finiteAtomicXiDenominatorPolynomial y S).eval z) w by fun_prop).hasDerivAt
  have hN := (show DifferentiableAt ℂ
      (fun z => (finiteAtomicXiNumeratorPolynomial y S weight).eval z) w by fun_prop).hasDerivAt
  have hdx := (xi_differentiable.deriv (1 / 2 + w)).hasDerivAt.comp w hshift
  have hx := (xi_differentiable (1 / 2 + w)).hasDerivAt.comp w hshift
  exact ((hD.mul hdx).sub (hN.mul hx)).differentiableAt

/-- If every shifted-Xi moment at one positive base agrees with a finite atomic sequence, then the
order-zero shifted moment agrees locally with the corresponding finite Möbius trajectory. -/
theorem eventuallyEq_re_xiShiftedReciprocalMoment_zero_finiteAtomic
    {y : ℝ} (hy : 0 < y) (S : Finset ℝ) (weight : ℝ → ℝ)
    (hmom : ∀ k : ℕ, (xiShiftedReciprocalMoment y k).re =
      ∑ x ∈ S, weight x * x ^ k) :
    (fun u : ℝ => (xiShiftedReciprocalMoment (y + u) 0).re) =ᶠ[nhds 0]
      (fun u : ℝ => ∑ x ∈ S, weight x / (1 + u * x)) := by
  let M : ℝ := ∑ x ∈ S, |x|
  let ε : ℝ := min (y / 2) (min 1 (1 / (1 + M)))
  have hM : 0 ≤ M := Finset.sum_nonneg fun x hx => abs_nonneg x
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (half_pos hy) (lt_min zero_lt_one (by positivity))
  filter_upwards [Metric.ball_mem_nhds 0 hε] with u hu
  have huabs : |u| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hu
  have hyu : 0 ≤ y + u := by
    have hneg : -(y / 2) < u := by
      have habs : |u| < y / 2 := lt_of_lt_of_le huabs (min_le_left _ _)
      exact (abs_lt.mp habs).1
    linarith
  have huwindow : |u| < 41 / 2 :=
    lt_trans (lt_of_lt_of_le huabs (min_le_right _ _ |>.trans (min_le_left _ _)))
      (by norm_num)
  have hactual := hasSum_re_xiShiftedReciprocalMoment_add_of_abs_lt
    hy.le hyu huwindow 0
  have hnode : ∀ x ∈ S, ‖-(u * x)‖ < 1 := by
    intro x hx
    have hxM : |x| ≤ M := Finset.single_le_sum (fun z _ => abs_nonneg z) hx
    have huM : |u| < 1 / (1 + M) :=
      lt_of_lt_of_le huabs (min_le_right _ _ |>.trans (min_le_right _ _))
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    calc
      |u| * |x| ≤ |u| * (1 + M) := by
        gcongr
        linarith
      _ < (1 / (1 + M)) * (1 + M) :=
        mul_lt_mul_of_pos_right huM (by positivity)
      _ = 1 := by field_simp
  have hatomic : HasSum
      (fun r : ℕ => ∑ x ∈ S, weight x * (-(u * x)) ^ r)
      (∑ x ∈ S, weight x / (1 + u * x)) := by
    have haux : ∀ T : Finset ℝ, T ⊆ S →
        HasSum (fun r : ℕ => ∑ x ∈ T, weight x * (-(u * x)) ^ r)
          (∑ x ∈ T, weight x / (1 + u * x)) := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro; simp
      | @insert x T hx ih =>
          intro hsub
          have hxS : x ∈ S := hsub (Finset.mem_insert_self x T)
          have hxsum := (hasSum_geometric_of_norm_lt_one (hnode x hxS)).mul_left
            (weight x)
          have hden : (1 - (-(u * x)) : ℝ)⁻¹ = 1 / (1 + u * x) := by ring
          rw [hden] at hxsum
          have hi := ih fun z hz => hsub (Finset.mem_insert_of_mem hz)
          have hval : weight x * (1 / (1 + u * x)) +
                ∑ z ∈ T, weight z / (1 + u * z) =
              weight x / (1 + u * x) +
                ∑ z ∈ T, weight z / (1 + u * z) := by ring
          simp only [Finset.sum_insert hx]
          rw [← hval]
          exact hxsum.add hi
    exact haux S (fun _ h => h)
  have hsame : ∀ r : ℕ,
      ∑ x ∈ S, weight x * (-(u * x)) ^ r =
        (-1 : ℝ) ^ r * ((r + 0).choose 0 : ℝ) * u ^ r *
          (xiShiftedReciprocalMoment y (r + 0)).re := by
    intro r
    simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one]
    rw [hmom r]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show -(u * x) = (-1) * u * x by ring, mul_pow, mul_pow]
    ring
  exact HasSum.unique hactual (hatomic.congr_fun fun r => (hsame r).symm)

/-- All-order agreement with a finite atomic moment sequence would make the cleared Xi relation
vanish identically.  Real-axis germ equality is propagated by the entire identity theorem. -/
theorem finiteAtomicXiClearedRelation_eq_zero_of_all_moments
    {y : ℝ} (hy : 0 < y) (S : Finset ℝ) (weight : ℝ → ℝ)
    (hmom : ∀ k : ℕ, (xiShiftedReciprocalMoment y k).re =
      ∑ x ∈ S, weight x * x ^ k) (z : ℂ) :
    finiteAtomicXiClearedRelation y S weight z = 0 := by
  let w0 : ℝ := Real.sqrt y
  have hw0 : 0 < w0 := Real.sqrt_pos.mpr hy
  have hw0sq : w0 ^ 2 = y := Real.sq_sqrt hy.le
  have heqU := eventuallyEq_re_xiShiftedReciprocalMoment_zero_finiteAtomic
    hy S weight hmom
  have hdenU : ∀ᶠ u : ℝ in nhds 0,
      ∀ x ∈ S, 1 + u * x ≠ 0 := by
    rw [Finset.eventually_all]
    intro x hx
    have hcont : ContinuousAt (fun u : ℝ => 1 + u * x) 0 := by fun_prop
    exact hcont.eventually_ne (by norm_num)
  have hshift : Filter.Tendsto (fun w : ℝ => w ^ 2 - y) (nhds w0) (nhds 0) := by
    have hcont : ContinuousAt (fun w : ℝ => w ^ 2 - y) w0 := by fun_prop
    convert hcont.tendsto using 1
    rw [hw0sq, sub_self]
  have hlocal : ∀ᶠ w : ℝ in nhds w0,
      finiteAtomicXiClearedRelation y S weight (w : ℂ) = 0 := by
    filter_upwards [hshift.eventually heqU, hshift.eventually hdenU,
      Ioi_mem_nhds hw0] with w heq hden hw
    have heq' : (xiShiftedReciprocalMoment (w ^ 2) 0).re =
        ∑ x ∈ S, weight x / (1 + (w ^ 2 - y) * x) := by
      have hbase : y + (w ^ 2 - y) = w ^ 2 := by ring
      rw [hbase] at heq
      exact heq
    have hdenC : ∀ x ∈ S,
        1 + (x : ℂ) * ((w : ℂ) ^ 2 - (y : ℂ)) ≠ 0 := by
      intro x hx
      have hcast : (((1 + (w ^ 2 - y) * x : ℝ)) : ℂ) =
          1 + (x : ℂ) * ((w : ℂ) ^ 2 - (y : ℂ)) := by
        push_cast
        ring
      rw [← hcast]
      exact Complex.ofReal_ne_zero.mpr (hden x hx)
    have him : (xiShiftedReciprocalMoment (w ^ 2) 0).im = 0 :=
      xiShiftedReciprocalMoment_im_eq_zero (sq_nonneg w) 0
    have hmomC : xiShiftedReciprocalMoment (w ^ 2) 0 =
        ((∑ x ∈ S, weight x / (1 + (w ^ 2 - y) * x) : ℝ) : ℂ) := by
      apply Complex.ext
      · simpa only [Complex.ofReal_re] using heq'
      · simp only [him, Complex.ofReal_im]
    have hxi : xi (1 / 2 + (w : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero w
    have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    have hhad := xiShiftedReciprocalMoment_zero_eq hw
    have hderiv : deriv xi (1 / 2 + (w : ℂ)) =
        (w : ℂ) * xiShiftedReciprocalMoment (w ^ 2) 0 *
          xi (1 / 2 + (w : ℂ)) := by
      have hcross := (eq_div_iff (mul_ne_zero hwC hxi)).mp hhad
      rw [← hcross]
      ring
    have hsumC :
        (((∑ x ∈ S, weight x / (1 + (w ^ 2 - y) * x) : ℝ)) : ℂ) =
          ∑ x ∈ S, (weight x : ℂ) /
            (1 + (x : ℂ) * ((w : ℂ) ^ 2 - (y : ℂ))) := by
      push_cast
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      ring
    have hclear := finiteAtomicXiDenominator_mul_trajectory y S weight (w : ℂ) hdenC
    rw [hmomC, hsumC] at hderiv
    rw [finiteAtomicXiClearedRelation, hderiv]
    linear_combination hclear * xi (1 / 2 + (w : ℂ))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  exact GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    (differentiable_finiteAtomicXiClearedRelation y S weight) hr
    (fun t ht => hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      exact ht)) z

/-- **No finite atomic shadow has infinite-order contact with shifted Xi.**  At every positive
squared base, the real shifted reciprocal-moment tower differs from every finite real atomic
moment sequence at some finite order.  The obstruction is the infinite Xi divisor: infinite contact
would make `xi'/xi` locally rational, hence meromorphically rational, despite its infinitely many
distinct poles. -/
theorem not_forall_re_xiShiftedReciprocalMoment_eq_finiteAtomic
    {y : ℝ} (hy : 0 < y) (S : Finset ℝ) (weight : ℝ → ℝ) :
    ¬ ∀ k : ℕ, (xiShiftedReciprocalMoment y k).re =
      ∑ x ∈ S, weight x * x ^ k := by
  intro hmom
  let D : Polynomial ℂ := finiteAtomicXiDenominatorPolynomial y S
  let N : Polynomial ℂ := finiteAtomicXiNumeratorPolynomial y S weight
  let bad : Finset ℂ := D.roots.toFinset.image (fun w : ℂ => 1 / 2 + w)
  obtain ⟨m, hm⟩ := exists_xiZeroPoint_not_mem bad
  let ρ : ℂ := xiZeroPoint m
  let wρ : ℂ := ρ - 1 / 2
  have hρzero : xi ρ = 0 := xiZeroPoint_eq_zero m
  have hDne : D ≠ 0 := finiteAtomicXiDenominatorPolynomial_ne_zero y S
  have hwρroot : wρ ∉ D.roots := by
    intro hwmem
    apply hm
    change ρ ∈ D.roots.toFinset.image (fun w : ℂ => 1 / 2 + w)
    apply Finset.mem_image.mpr
    refine ⟨wρ, Multiset.mem_toFinset.mpr hwmem, ?_⟩
    dsimp only [wρ, ρ]
    ring
  have hDeval : D.eval wρ ≠ 0 := by
    intro hzero
    exact hwρroot ((Polynomial.mem_roots hDne).mpr hzero)
  let R : ℂ → ℂ := fun s => N.eval (s - 1 / 2) / D.eval (s - 1 / 2)
  have hshiftAnalytic : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) ρ := by fun_prop
  have hNanalytic : AnalyticAt ℂ (fun s : ℂ => N.eval (s - 1 / 2)) ρ :=
    AnalyticAt.comp (f := fun s : ℂ => s - 1 / 2) (x := ρ)
      ((AnalyticOnNhd.eval_polynomial N) _ (Set.mem_univ _)) hshiftAnalytic
  have hDanalytic : AnalyticAt ℂ (fun s : ℂ => D.eval (s - 1 / 2)) ρ :=
    AnalyticAt.comp (f := fun s : ℂ => s - 1 / 2) (x := ρ)
      ((AnalyticOnNhd.eval_polynomial D) _ (Set.mem_univ _)) hshiftAnalytic
  have hRanalytic : AnalyticAt ℂ R ρ := by
    apply hNanalytic.div hDanalytic
    simpa only [wρ] using hDeval
  have hxiNotZeroGerm : ¬ ∀ᶠ s : ℂ in nhds ρ, xi s = 0 := by
    intro hev
    have hall := xi_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ ρ) hev (Set.mem_univ 0)
    have hzero : xi 0 = 0 := hall
    rw [xi] at hzero
    norm_num at hzero
  have hxiPunct : ∀ᶠ s : ℂ in nhdsWithin ρ ({ρ}ᶜ), xi s ≠ 0 :=
    (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hxiNotZeroGerm
  have hDPunct : ∀ᶠ s : ℂ in nhdsWithin ρ ({ρ}ᶜ), D.eval (s - 1 / 2) ≠ 0 := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact hDanalytic.continuousAt.eventually_ne (by simpa only [wρ] using hDeval)
  have hcongr : R =ᶠ[nhdsWithin ρ ({ρ}ᶜ)] logDeriv xi := by
    filter_upwards [hxiPunct, hDPunct] with s hxi hDs
    have hrel := finiteAtomicXiClearedRelation_eq_zero_of_all_moments
      hy S weight hmom (s - 1 / 2)
    have hcenter : (1 : ℂ) / 2 + (s - 1 / 2) = s := by ring
    rw [finiteAtomicXiClearedRelation, hcenter] at hrel
    dsimp only [R]
    rw [logDeriv_apply, div_eq_div_iff hDs hxi]
    linear_combination -hrel
  have hnonneg : 0 ≤ meromorphicOrderAt R ρ := hRanalytic.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hcongr,
    meromorphicOrderAt_logDeriv_xi_eq_neg_one hρzero] at hnonneg
  have hlt : (((-1 : ℤ) : WithTop ℤ)) < 0 := WithTop.coe_lt_coe.mpr (by omega)
  exact (not_le_of_gt hlt) hnonneg

/-- Every canonical finite Hankel shadow of shifted Xi has a first nonzero defect at some finite
order.  No positivity or singular-face hypothesis is needed for existence. -/
theorem exists_xiShiftedHankelBoundaryPadeDefect_ne_zero
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    ∃ k : ℕ, xiShiftedHankelBoundaryPadeDefect y c k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply not_forall_re_xiShiftedReciprocalMoment_eq_finiteAtomic hy
    (HTGeometry.finiteHankelBoundaryNodes c)
    (HTGeometry.finiteHankelBoundaryWeight
      (fun k => (xiShiftedReciprocalMoment y k).re) c)
  intro k
  have hk := hall k
  rw [xiShiftedHankelBoundaryPadeDefect,
    HTGeometry.finiteHankelBoundaryPadeDefect, sub_eq_zero] at hk
  exact hk

/-- A positive flat Xi Hankel face has a genuine finite first contact order beyond the visible
quadrature range.  This removes the existential `hfirst` premise from higher-contact arguments. -/
theorem exists_first_xiShiftedHankelBoundaryPadeDefect
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    ∃ d : ℕ, 0 < d ∧
      (∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0 := by
  let hex : ∃ k : ℕ, xiShiftedHankelBoundaryPadeDefect y c k ≠ 0 :=
    exists_xiShiftedHankelBoundaryPadeDefect_ne_zero hy c
  let k0 : ℕ := Nat.find hex
  have hk0ne : xiShiftedHankelBoundaryPadeDefect y c k0 ≠ 0 := Nat.find_spec hex
  have hk0gt : 2 * n < k0 := by
    by_contra hnot
    have hk0le : k0 ≤ 2 * n := Nat.le_of_not_gt hnot
    exact hk0ne (xiShiftedHankelBoundaryPadeDefect_eq_zero_of_le
      c hhead hc hlast hk0le)
  let d : ℕ := k0 - 2 * n
  have hd : 0 < d := Nat.sub_pos_of_lt hk0gt
  have hsum : 2 * n + d = k0 := Nat.add_sub_of_le hk0gt.le
  refine ⟨d, hd, ?_, ?_⟩
  · intro k hk
    rw [hsum] at hk
    exact not_ne_iff.mp (Nat.find_min hex hk)
  · rwa [hsum]

/-- **Automatic closed Xi contact-parity law.**  At a positive flat face that remains positive
semidefinite immediately to the right, some finite first defect exists and has the forced
alternating sign. -/
theorem exists_signed_first_xiShiftedHankelBoundaryPadeDefect_of_right_posSemidef
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hpsd : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef) :
    ∃ d : ℕ, 0 < d ∧
      (∀ k < 2 * n + d, xiShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      0 < (-1 : ℝ) ^ d * xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) := by
  obtain ⟨d, hd, hzero, hfirst⟩ :=
    exists_first_xiShiftedHankelBoundaryPadeDefect hy c hhead hc hlast
  refine ⟨d, hd, hzero, ?_⟩
  exact signed_first_xiShiftedHankelBoundaryPadeDefect_pos_of_right_posSemidef
    hy.le c hlast hd hzero hfirst hpsd

/-! ### Source-side finite-contact closure -/

/-- No finite atomic shadow has infinite-order contact with the completed prime--archimedean
source in the endpoint window.  This is the source-coordinate form of the infinite-Xi-divisor
obstruction. -/
theorem not_forall_re_primeArchShiftedReciprocalMoment_eq_finiteAtomic
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    (S : Finset ℝ) (weight : ℝ → ℝ) :
    ¬ ∀ k : ℕ, (primeArchShiftedReciprocalMoment y k).re =
      ∑ x ∈ S, weight x * x ^ k := by
  intro hall
  apply not_forall_re_xiShiftedReciprocalMoment_eq_finiteAtomic hy S weight
  intro k
  rw [xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax]
  exact hall k

/-- Every canonical finite Hankel shadow of the completed source differs from that source at a
finite order. -/
theorem exists_primeArchShiftedHankelBoundaryPadeDefect_ne_zero
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ) :
    ∃ k : ℕ, primeArchShiftedHankelBoundaryPadeDefect y c k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply not_forall_re_primeArchShiftedReciprocalMoment_eq_finiteAtomic hy hymax
    (HTGeometry.finiteHankelBoundaryNodes c)
    (HTGeometry.finiteHankelBoundaryWeight
      (fun k => (primeArchShiftedReciprocalMoment y k).re) c)
  intro k
  have hk := hall k
  rw [primeArchShiftedHankelBoundaryPadeDefect,
    HTGeometry.finiteHankelBoundaryPadeDefect, sub_eq_zero] at hk
  simpa using hk

/-- A positive flat source face has a genuine finite first Padé defect beyond its visible
quadrature range. -/
theorem exists_first_primeArchShiftedHankelBoundaryPadeDefect
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    ∃ d : ℕ, 0 < d ∧
      (∀ k < 2 * n + d, primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0 := by
  obtain ⟨d, hd, hzero, hfirst⟩ :=
    exists_first_xiShiftedHankelBoundaryPadeDefect hy c hhead hc hlast
  refine ⟨d, hd, ?_, ?_⟩
  · intro k hk
    rw [← xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzero k hk
  · rw [← xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hfirst

/-- **Automatic source-coordinate contact parity.**  A hypothetical flat face that remains in the
right shifted Hankel cone selects a finite first completed-source defect, and the cone forces its
alternating orientation. -/
theorem exists_signed_first_primeArchShiftedHankelBoundaryPadeDefect_of_right_posSemidef
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hpsd : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef) :
    ∃ d : ℕ, 0 < d ∧
      (∀ k < 2 * n + d, primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      0 < (-1 : ℝ) ^ d *
        primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + d) := by
  obtain ⟨d, hd, hzero, hsigned⟩ :=
    exists_signed_first_xiShiftedHankelBoundaryPadeDefect_of_right_posSemidef
      hy c hhead hc hlast hpsd
  refine ⟨d, hd, ?_, ?_⟩
  · intro k hk
    rw [← xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzero k hk
  · rw [← xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hsigned

/-! ### Parity-lifted square classification -/

/-- A finite real atomic sequence with nonnegative weights has positive-semidefinite Hankel blocks
in every finite degree. -/
theorem momentHankelMatrix_finiteAtomic_posSemidef
    (S : Finset ℝ) (weight : ℝ → ℝ)
    (hweight : ∀ x ∈ S, 0 ≤ weight x) (N : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun k => ∑ x ∈ S, weight x * x ^ k) N).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨HTGeometry.momentHankelMatrix_isHermitian _ _, ?_⟩
  intro a
  rw [star_trivial, HTGeometry.dotProduct_mulVec_momentHankelMatrix,
    momentFunctional_finiteAtomicMoment]
  apply Finset.sum_nonneg
  intro x hx
  rw [eval_pow]
  exact mul_nonneg (hweight x hx) (sq_nonneg _)

/-- Vanishing through an odd first-contact index makes the larger Hankel block exactly the same
finite positive atomic Gram matrix.  This is the flat-plateau meaning of higher odd contact. -/
theorem xiShiftedMomentHankelMatrix_eq_boundaryAtomic_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedMomentHankelMatrix y (n + m + 1) =
      HTGeometry.momentHankelMatrix
        (fun k => ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
          HTGeometry.finiteHankelBoundaryWeight
            (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ k)
        (n + m + 1) := by
  ext i j
  have hij : (i : ℕ) + (j : ℕ) < 2 * n + (2 * m + 1) := by
    have hi : (i : ℕ) < n + m + 1 := i.isLt
    have hj : (j : ℕ) < n + m + 1 := j.isLt
    omega
  have hz := hzero ((i : ℕ) + (j : ℕ)) hij
  rw [xiShiftedHankelBoundaryPadeDefect,
    HTGeometry.finiteHankelBoundaryPadeDefect, sub_eq_zero] at hz
  exact hz

/-- Every higher odd contact contains an explicit positive-semidefinite flat plateau: the block of
size `n+m+1` is the Gram matrix of the original `n` positive quadrature atoms. -/
theorem xiShiftedMomentHankelMatrix_posSemidef_flatPlateau_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    (xiShiftedMomentHankelMatrix y (n + m + 1)).PosSemidef := by
  change (HTGeometry.momentHankelMatrix
    (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
  change HTGeometry.momentHankelMatrix
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
  rw [xiShiftedMomentHankelMatrix_eq_boundaryAtomic_of_odd_contact c hzero]
  apply momentHankelMatrix_finiteAtomic_posSemidef
  intro x hx
  exact (HTGeometry.finiteHankelBoundaryWeight_pos c hhead hc hlast hx).le

/-- Vanishing through an even first-contact index makes the enlarged block the positive atomic
flat block plus one terminal rank-one correction carrying precisely the first defect. -/
theorem xiShiftedMomentHankelMatrix_eq_boundaryAtomic_add_terminal_of_even_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedMomentHankelMatrix y (n + m + 1) =
      HTGeometry.momentHankelMatrix
        (fun k => ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
          HTGeometry.finiteHankelBoundaryWeight
            (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ k)
        (n + m + 1) +
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) •
        GaloisForLFunctions.HTGeometry.realOuterProduct
          (GaloisForLFunctions.HTGeometry.hankelTerminalBasis (n + m + 1))
          (GaloisForLFunctions.HTGeometry.hankelTerminalBasis (n + m + 1)) := by
  open GaloisForLFunctions.HTGeometry in
    ext i j
    have hi : (i : ℕ) < n + m + 1 := i.isLt
    have hj : (j : ℕ) < n + m + 1 := j.isLt
    have hle : (i : ℕ) + (j : ℕ) ≤ 2 * n + 2 * m := by omega
    by_cases hlt : (i : ℕ) + (j : ℕ) < 2 * n + 2 * m
    · have hz := hzero ((i : ℕ) + (j : ℕ)) hlt
      rw [xiShiftedHankelBoundaryPadeDefect,
        HTGeometry.finiteHankelBoundaryPadeDefect, sub_eq_zero] at hz
      have houter : hankelTerminalBasis (n + m + 1) i *
          hankelTerminalBasis (n + m + 1) j = 0 := by
        simp only [hankelTerminalBasis]
        split_ifs with hiterm hjterm
        · omega
        · ring
        · ring
        · ring
      simp only [xiShiftedMomentHankelMatrix, finiteHankelMatrix,
        HTGeometry.momentHankelMatrix, Matrix.add_apply, Matrix.smul_apply,
        realOuterProduct, houter, smul_zero, add_zero]
      exact hz
    · have heq : (i : ℕ) + (j : ℕ) = 2 * n + 2 * m := by omega
      have hiterm : (i : ℕ) = n + m := by omega
      have hjterm : (j : ℕ) = n + m := by omega
      simp only [xiShiftedMomentHankelMatrix, finiteHankelMatrix,
        HTGeometry.momentHankelMatrix, Matrix.add_apply, Matrix.smul_apply,
        realOuterProduct, hankelTerminalBasis, hiterm, hjterm, Nat.add_one,
        ↓reduceIte, mul_one, smul_eq_mul]
      have hnm : n + m + (n + m) = 2 * n + 2 * m := by omega
      rw [hnm]
      simp only [xiShiftedHankelBoundaryPadeDefect,
        HTGeometry.finiteHankelBoundaryPadeDefect]
      ring

/-- A nonnegative multiple of the terminal coordinate outer product is positive semidefinite. -/
theorem terminalHankelOuterProduct_posSemidef
    {N : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    (δ • GaloisForLFunctions.HTGeometry.realOuterProduct
      (GaloisForLFunctions.HTGeometry.hankelTerminalBasis N)
      (GaloisForLFunctions.HTGeometry.hankelTerminalBasis N)).PosSemidef := by
  open GaloisForLFunctions.HTGeometry in
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · apply Matrix.IsHermitian.ext
      intro i j
      simp [realOuterProduct, mul_comm]
    · intro a
      rw [star_trivial, Matrix.smul_mulVec, dotProduct_smul,
        dotProduct_realOuterProduct_mulVec]
      have hsquare : 0 ≤ (a ⬝ᵥ hankelTerminalBasis N) ^ 2 := sq_nonneg _
      have hcomm : hankelTerminalBasis N ⬝ᵥ a = a ⬝ᵥ hankelTerminalBasis N := by
        rw [dotProduct_comm]
      rw [hcomm]
      simpa only [smul_eq_mul, pow_two] using mul_nonneg hδ hsquare

/-- **Even-contact rank-one filling law.** If the first even defect has its forced nonnegative
orientation, the enlarged block remains positive semidefinite: even contact fills one terminal
rank rather than leaving the cone. -/
theorem xiShiftedMomentHankelMatrix_posSemidef_rankOneFilled_of_even_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirstNonneg : 0 ≤ xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m)) :
    (xiShiftedMomentHankelMatrix y (n + m + 1)).PosSemidef := by
  rw [xiShiftedMomentHankelMatrix_eq_boundaryAtomic_add_terminal_of_even_contact c hzero]
  apply Matrix.PosSemidef.add
  · apply momentHankelMatrix_finiteAtomic_posSemidef
    intro x hx
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).PosDef at hhead
    change HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *ᵥ c = 0 at hc
    exact (HTGeometry.finiteHankelBoundaryWeight_pos c hhead hc hlast hx).le
  · exact terminalHankelOuterProduct_posSemidef hfirstNonneg

/-- Coefficient vector of the parity-lifted null polynomial `X^m P` in the enlarged flat
plateau. -/
def xiShiftedHankelBoundaryLiftedNullVector
    {n : ℕ} (c : Fin (n + 1) → ℝ) (m : ℕ) : Fin (n + m + 1) → ℝ :=
  Polynomial.toFn (n + m + 1)
    (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m)

theorem ofFn_xiShiftedHankelBoundaryLiftedNullVector
    {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    Polynomial.ofFn (n + m + 1)
        (xiShiftedHankelBoundaryLiftedNullVector c m) =
      HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m := by
  apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
    Polynomial.natDegree_X_pow]
  omega

/-- Every lifted null square still has zero norm throughout an odd-contact flat plateau. -/
theorem momentFunctional_liftedNullSquare_eq_zero_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        ((HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) = 0 := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg := HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hdeg : (P ^ 2 * X ^ (2 * m)).natDegree < 2 * n + (2 * m + 1) := by
    rw [(hP.pow 2).natDegree_mul (Polynomial.monic_X_pow (2 * m)),
      show (P ^ 2).natDegree = 2 * n by
        rw [pow_two, hP.natDegree_mul hP, hPdeg]
        omega,
      Polynomial.natDegree_X_pow]
    omega
  calc
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) ((P * X ^ m) ^ 2) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ (2 * m)) := by
      congr 1
      ring
    _ = HTGeometry.momentFunctional
        (xiShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * X ^ (2 * m)) :=
      (momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
        (fun k => (xiShiftedReciprocalMoment y k).re) c (2 * m)).symm
    _ = 0 := HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero hdeg

/-- **Lifted null-subspace law.** Odd contact of order `2m+1` annihilates every square in the
`m+1` dimensional polynomial space generated by `P, PX, ..., PX^m`, not only the terminal monomial
lift `PX^m`. -/
theorem momentFunctional_liftedNullSubspace_eq_zero_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (Q : Polynomial ℝ) (hQdeg : Q.natDegree ≤ m) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        ((HTGeometry.finiteHankelNullMonicPolynomial c * Q) ^ 2) = 0 := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hdeg : (P ^ 2 * Q ^ 2).natDegree < 2 * n + (2 * m + 1) := by
    calc
      (P ^ 2 * Q ^ 2).natDegree ≤ (P ^ 2).natDegree + (Q ^ 2).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2 * P.natDegree + 2 * Q.natDegree := by
        exact Nat.add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le
      _ ≤ 2 * n + 2 * m := by omega
      _ < 2 * n + (2 * m + 1) := by omega
  calc
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) ((P * Q) ^ 2) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * Q ^ 2) := by
      congr 1
      ring
    _ = HTGeometry.momentFunctional
        (xiShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * Q ^ 2) :=
      (momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul
        (fun k => (xiShiftedReciprocalMoment y k).re) c (Q ^ 2)).symm
    _ = 0 := HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero hdeg

/-- The lifted polynomial `X^m P` is an actual kernel vector of the enlarged odd-contact flat
plateau, not only a zero-energy test polynomial. -/
theorem xiShiftedHankelBoundaryLiftedNullVector_mem_kernel_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedMomentHankelMatrix y (n + m + 1) *ᵥ
        xiShiftedHankelBoundaryLiftedNullVector c m = 0 := by
  have hpsd := xiShiftedMomentHankelMatrix_posSemidef_flatPlateau_of_odd_contact
    c hhead hc hlast hzero
  apply (hpsd.dotProduct_mulVec_zero_iff
    (xiShiftedHankelBoundaryLiftedNullVector c m)).mp
  change xiShiftedHankelBoundaryLiftedNullVector c m ⬝ᵥ
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + m + 1) *ᵥ
          xiShiftedHankelBoundaryLiftedNullVector c m) = 0
  rw [HTGeometry.dotProduct_mulVec_momentHankelMatrix,
    ofFn_xiShiftedHankelBoundaryLiftedNullVector c hlast,
    momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzero]

/-- A monic polynomial of degree `K` evaluates under a sequence vanishing below `K` to the first
surviving sequence coefficient. -/
theorem momentFunctional_monic_eq_first_of_zero_below
    {a : ℕ → ℝ} {K : ℕ} (hzero : ∀ k < K, a k = 0)
    {A : Polynomial ℝ} (hA : A.Monic) (hAdeg : A.natDegree = K) :
    HTGeometry.momentFunctional a A = a K := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  have hKcoeff : A.coeff K = 1 := by
    rw [← hAdeg]
    exact hA.coeff_natDegree
  have hKmem : K ∈ A.support := Polynomial.mem_support_iff.mpr (by simp [hKcoeff])
  rw [Finset.sum_eq_single K]
  · rw [hKcoeff, one_mul]
  · intro k hk hkne
    have hkle : k ≤ A.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    rw [hzero k (by omega), mul_zero]
  · exact fun h => (h hKmem).elim

/-- Every pair of parity-lifted null polynomials below the first odd anti-diagonal is mutually
orthogonal.  Thus higher odd contact creates a whole totally isotropic lifted flag, not merely one
terminal null vector. -/
theorem momentInner_liftedNullPair_eq_zero_of_odd_contact
    {y : ℝ} {n m i j : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hij : i + j < 2 * m + 1) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ i)
        (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ j) = 0 := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg := HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : (P ^ 2 * X ^ (i + j)).Monic :=
    (hP.pow 2).mul (Polynomial.monic_X_pow (i + j))
  have hAdeg : (P ^ 2 * X ^ (i + j)).natDegree = 2 * n + (i + j) := by
    rw [(hP.pow 2).natDegree_mul (Polynomial.monic_X_pow (i + j)),
      show (P ^ 2).natDegree = 2 * n by
        rw [pow_two, hP.natDegree_mul hP, hPdeg]
        omega,
      Polynomial.natDegree_X_pow]
  rw [HTGeometry.momentInner_def]
  have hpoly :
      (P * X ^ i) * (P * X ^ j) = P ^ 2 * X ^ (i + j) := by ring
  rw [hpoly]
  rw [← momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
    (fun k => (xiShiftedReciprocalMoment y k).re) c (i + j)]
  apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
  rw [hAdeg]
  omega

/-- The first surviving odd anti-diagonal pairing is exactly the first Padé defect. -/
theorem momentInner_liftedNullPair_eq_first_odd_defect
    {y : ℝ} {n m i j : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hij : i + j = 2 * m + 1) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ i)
        (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ j) =
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg := HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : (P ^ 2 * X ^ (i + j)).Monic :=
    (hP.pow 2).mul (Polynomial.monic_X_pow (i + j))
  have hAdeg : (P ^ 2 * X ^ (i + j)).natDegree = 2 * n + (2 * m + 1) := by
    rw [(hP.pow 2).natDegree_mul (Polynomial.monic_X_pow (i + j)),
      show (P ^ 2).natDegree = 2 * n by
        rw [pow_two, hP.natDegree_mul hP, hPdeg]
        omega,
      Polynomial.natDegree_X_pow, hij]
  rw [HTGeometry.momentInner_def]
  have hpoly :
      (P * X ^ i) * (P * X ^ j) = P ^ 2 * X ^ (i + j) := by ring
  rw [hpoly]
  rw [← momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
    (fun k => (xiShiftedReciprocalMoment y k).re) c (i + j)]
  exact momentFunctional_monic_eq_first_of_zero_below hzero hA hAdeg

/-- **Odd-contact hyperbolic-plane law.**  On the last two lifted null directions, the Gram
determinant is exactly minus the square of the first odd Padé defect.  Its sign is independent of
the still-unseen next moment. -/
theorem liftedNullPair_gramDet_eq_neg_sq_of_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    let B := P * X ^ (m + 1)
    HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) A A *
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) B B -
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) A B ^ 2 =
      -(xiShiftedHankelBoundaryPadeDefect y c
          (2 * n + (2 * m + 1))) ^ 2 := by
  dsimp only
  have hAA := momentInner_liftedNullPair_eq_zero_of_odd_contact
    c hlast hzero (i := m) (j := m) (by omega)
  have hAB := momentInner_liftedNullPair_eq_first_odd_defect
    c hlast hzero (i := m) (j := m + 1) (by omega)
  rw [hAA, hAB]
  ring

/-- A nonzero first odd defect makes the lifted two-plane strictly indefinite. -/
theorem liftedNullPair_gramDet_neg_of_first_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    let B := P * X ^ (m + 1)
    HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) A A *
        HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) B B -
      HTGeometry.momentInner
          (fun k => (xiShiftedReciprocalMoment y k).re) A B ^ 2 < 0 := by
  dsimp only
  rw [liftedNullPair_gramDet_eq_neg_sq_of_odd_contact c hlast hzero]
  exact neg_neg_of_pos (sq_pos_of_ne_zero hfirst)

/-- Source-only form of the odd-contact hyperbolic-plane law in the prime--Gamma convergence
window. -/
theorem liftedNullPair_primeArch_gramDet_neg_of_first_odd_contact
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : primeArchShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    let B := P * X ^ (m + 1)
    HTGeometry.momentInner
          (fun k => (primeArchShiftedReciprocalMoment y k).re) A A *
        HTGeometry.momentInner
          (fun k => (primeArchShiftedReciprocalMoment y k).re) B B -
        HTGeometry.momentInner
          (fun k => (primeArchShiftedReciprocalMoment y k).re) A B ^ 2 < 0 := by
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzero k hk
  have hfirstXi : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0 := by
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hfirst
  have hdet := liftedNullPair_gramDet_neg_of_first_odd_contact
    c hlast hzeroXi hfirstXi
  have hseq :
      (fun k => (xiShiftedReciprocalMoment y k).re) =
        fun k => (primeArchShiftedReciprocalMoment y k).re := by
    funext k
    exact congrArg Complex.re
      (xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy.le hymax k)
  simpa only [hseq] using hdet

/-- The first omitted coupling of the enlarged odd-contact plateau is exactly the original first
odd Padé defect. -/
theorem xiShiftedHankelFirstOmittedCoupling_liftedNullVector_eq_odd_defect
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedHankelFirstOmittedCoupling y (n + m + 1)
        (xiShiftedHankelBoundaryLiftedNullVector c m) =
      xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let R := P * X ^ m
  let v := xiShiftedHankelBoundaryLiftedNullVector c m
  let K := 2 * n + (2 * m + 1)
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R, P]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  let A : Polynomial ℝ := X ^ (n + m + 1) * R
  have hA : A.Monic := (Polynomial.monic_X_pow (n + m + 1)).mul hR
  have hAdeg : A.natDegree = K := by
    dsimp only [A, K]
    rw [(Polynomial.monic_X_pow (n + m + 1)).natDegree_mul hR,
      Polynomial.natDegree_X_pow, hRdeg]
    omega
  have hatomic : HTGeometry.momentFunctional
      (fun k => ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
        HTGeometry.finiteHankelBoundaryWeight
          (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ k) A = 0 := by
    rw [momentFunctional_finiteAtomicMoment]
    apply Finset.sum_eq_zero
    intro x hx
    dsimp only [A, R, P]
    rw [eval_mul, eval_mul,
      HTGeometry.finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx]
    ring
  have hdefectA : HTGeometry.momentFunctional
      (xiShiftedHankelBoundaryPadeDefect y c) A =
      xiShiftedHankelBoundaryPadeDefect y c K :=
    momentFunctional_monic_eq_first_of_zero_below hzero hA hAdeg
  have hactualA : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) A =
      xiShiftedHankelBoundaryPadeDefect y c K := by
    change HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re -
        ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
          HTGeometry.finiteHankelBoundaryWeight
            (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ k) A =
      (xiShiftedReciprocalMoment y K).re -
        ∑ x ∈ HTGeometry.finiteHankelBoundaryNodes c,
          HTGeometry.finiteHankelBoundaryWeight
            (fun j => (xiShiftedReciprocalMoment y j).re) c x * x ^ K at hdefectA
    rw [momentFunctional_sequence_sub] at hdefectA
    rw [hatomic, sub_zero] at hdefectA
    simpa [xiShiftedHankelBoundaryPadeDefect,
      HTGeometry.finiteHankelBoundaryPadeDefect] using hdefectA
  have hcoupling := HTGeometry.momentFunctional_X_pow_mul_finiteHankelNullPolynomial
    (fun k => (xiShiftedReciprocalMoment y k).re) (n + m + 1) v
  change HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re)
      (X ^ (n + m + 1) * HTGeometry.finiteHankelNullPolynomial v) =
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + m + 1) v at hcoupling
  rw [show HTGeometry.finiteHankelNullPolynomial v = R by
    simpa only [v, HTGeometry.finiteHankelNullPolynomial] using
      ofFn_xiShiftedHankelBoundaryLiftedNullVector c hlast] at hcoupling
  change HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) A = _ at hcoupling
  unfold xiShiftedHankelFirstOmittedCoupling
  rw [← hcoupling, hactualA]

/-- **Odd-contact escalation law.** A first defect at `2n+2m+1` makes the enlarged block of size
`n+m+1` a positive flat plateau, but its very next principal Hankel extension is indefinite. -/
theorem xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_odd_contact
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (hfirst : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0) :
    ¬ (xiShiftedMomentHankelMatrix y (n + m + 2)).PosSemidef := by
  apply xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    y (n + m + 1) (xiShiftedHankelBoundaryLiftedNullVector c m)
    (xiShiftedHankelBoundaryLiftedNullVector_mem_kernel_of_odd_contact
      c hhead hc hlast hzero)
  rw [xiShiftedHankelFirstOmittedCoupling_liftedNullVector_eq_odd_defect c hlast hzero]
  exact hfirst

/-- At a first even Padé contact `d = 2m`, the defect is the ordinary square norm of the
canonically lifted null polynomial `X^m P`.  Thus the even branch is Hamburger rather than
Stieltjes geometry. -/
theorem xiShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (hm : 0 < m)
    (hzero : ∀ k < 2 * n + 2 * m,
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        ((HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hfirst := HTGeometry.momentFunctional_monic_first_contact
    (a := xiShiftedHankelBoundaryPadeDefect y c) (P := P)
    (n := n) (d := 2 * m)
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    (by omega) hzero
  calc
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) =
        HTGeometry.momentFunctional
          (xiShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * X ^ (2 * m)) := hfirst.symm
    _ = HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ (2 * m)) :=
      momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
        (fun k => (xiShiftedReciprocalMoment y k).re) c (2 * m)
    _ = HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) ((P * X ^ m) ^ 2) := by
      congr 1
      ring

/-- At a first odd Padé contact `d = 2m+1`, the defect is the shifted-square norm of the
canonically lifted null polynomial `X^m P`.  This is exactly the Stieltjes direction capable of
leaving a Hankel cone. -/
theorem xiShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hfirst := HTGeometry.momentFunctional_monic_first_contact
    (a := xiShiftedHankelBoundaryPadeDefect y c) (P := P)
    (n := n) (d := 2 * m + 1)
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    (by omega) hzero
  calc
    xiShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) =
        HTGeometry.momentFunctional
          (xiShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * X ^ (2 * m + 1)) := hfirst.symm
    _ = HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ (2 * m + 1)) :=
      momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
        (fun k => (xiShiftedReciprocalMoment y k).re) c (2 * m + 1)
    _ = HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) (X * (P * X ^ m) ^ 2) := by
      congr 1
      ring

/-- Completed-source form of the even parity lift. -/
theorem primeArchShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (hm : 0 < m)
    (hzero : ∀ k < 2 * n + 2 * m,
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0) :
    primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) =
      HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        ((HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hfirst := HTGeometry.momentFunctional_monic_first_contact
    (a := primeArchShiftedHankelBoundaryPadeDefect y c) (P := P)
    (n := n) (d := 2 * m)
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    (by omega) hzero
  calc
    primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + 2 * m) =
        HTGeometry.momentFunctional
          (primeArchShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * X ^ (2 * m)) := hfirst.symm
    _ = HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ (2 * m)) :=
      momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
        (fun k => (primeArchShiftedReciprocalMoment y k).re) c (2 * m)
    _ = HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re) ((P * X ^ m) ^ 2) := by
      congr 1
      ring

/-- Completed-source form of the odd parity lift. -/
theorem primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0) :
    primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) =
      HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (X * (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) := by
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hfirst := HTGeometry.momentFunctional_monic_first_contact
    (a := primeArchShiftedHankelBoundaryPadeDefect y c) (P := P)
    (n := n) (d := 2 * m + 1)
    (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast)
    (HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast)
    (by omega) hzero
  calc
    primeArchShiftedHankelBoundaryPadeDefect y c (2 * n + (2 * m + 1)) =
        HTGeometry.momentFunctional
          (primeArchShiftedHankelBoundaryPadeDefect y c) (P ^ 2 * X ^ (2 * m + 1)) := hfirst.symm
    _ = HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re) (P ^ 2 * X ^ (2 * m + 1)) :=
      momentFunctional_finiteHankelBoundaryPadeDefect_nullSquare_mul_X
        (fun k => (primeArchShiftedReciprocalMoment y k).re) c (2 * m + 1)
    _ = HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re) (X * (P * X ^ m) ^ 2) := by
      congr 1
      ring

/-- **Parity-lifted source classification.** Every right-positive finite Xi contact has exactly
one of two forms: an even contact is a strictly positive completed-source square norm, while an
odd contact is a strictly negative completed-source shifted-square norm.  The latter is the only
branch with Stieltjes crossing orientation. -/
theorem exists_primeArchShiftedHankelBoundaryPadeContact_parity_lift
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hpsd : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef) :
    ∃ d : ℕ, 0 < d ∧
      (∀ k < 2 * n + d, primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      ((∃ m : ℕ, d = 2 * m ∧ 0 < m ∧
          0 < HTGeometry.momentFunctional
            (fun k => (primeArchShiftedReciprocalMoment y k).re)
            ((HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2)) ∨
        (∃ m : ℕ, d = 2 * m + 1 ∧
          HTGeometry.momentFunctional
            (fun k => (primeArchShiftedReciprocalMoment y k).re)
            (X * (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) < 0)) := by
  obtain ⟨d, hd, hzero, hsigned⟩ :=
    exists_signed_first_primeArchShiftedHankelBoundaryPadeDefect_of_right_posSemidef
      hy hymax c hhead hc hlast hpsd
  refine ⟨d, hd, hzero, ?_⟩
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    have hdform : d = 2 * m := by omega
    have hmpos : 0 < m := by omega
    refine ⟨m, hdform, hmpos, ?_⟩
    have hvalue := primeArchShiftedHankelBoundaryPadeDefect_first_even_eq_liftedSquare
      c hlast hmpos (by simpa [hdform] using hzero)
    rw [hdform] at hsigned
    have hpow : (-1 : ℝ) ^ (2 * m) = 1 := by
      rw [pow_mul]
      norm_num
    simpa only [hpow, one_mul, hvalue] using hsigned
  · right
    have hdform : d = 2 * m + 1 := by omega
    refine ⟨m, hdform, ?_⟩
    have hvalue := primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
      c hlast (by simpa [hdform] using hzero)
    rw [hdform] at hsigned
    have hodd : Odd (2 * m + 1) := ⟨m, by omega⟩
    rw [Odd.neg_one_pow hodd, neg_mul, hvalue] at hsigned
    linarith

/-- **Genuine Route-U crossing normal form.** Every actual two-sided first loss produces an
adaptively selected polynomial whose completed prime--archimedean shifted-square moment is strictly
negative.  The even/Hamburger alternative is absent. -/
theorem exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (X * (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) < 0 := by
  obtain ⟨d, hd, hzero, hsigned⟩ :=
    exists_signed_first_xiShiftedHankelBoundaryPadeDefect_of_right_posSemidef
      hy c hhead hc hlast hright
  have hfirst : xiShiftedHankelBoundaryPadeDefect y c (2 * n + d) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsigned
    exact (lt_irrefl 0 hsigned).elim
  have hodd := odd_first_contact_of_genuine_xiShiftedHankel_crossing
    hy c hhead hc hlast hd hzero hfirst hright hleft
  rcases hodd with ⟨m, hm⟩
  have hdform : d = 2 * m + 1 := by omega
  have hzeroPA : ∀ k < 2 * n + (2 * m + 1),
      primeArchShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [← xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzero k (by omega)
  refine ⟨m, hzeroPA, ?_⟩
  have hvalue := primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroPA
  have hsourceEq := xiShiftedHankelBoundaryPadeDefect_eq_primeArch
    hy.le hymax c (2 * n + d)
  rw [hsourceEq, hdform] at hsigned
  have hparity : Odd (2 * m + 1) := ⟨m, by omega⟩
  rw [Odd.neg_one_pow hparity, neg_mul, hvalue] at hsigned
  linarith

/-- **Odd contact--dimension escalation normal form.**  A genuine two-sided Route-U loss does not
merely select a negative shifted square.  The same adaptive exponent `m` extends the original
corank-one face to a positive-semidefinite flat plateau with lifted kernel `P * X^m`, while the
very next principal Hankel block is already indefinite.  Thus contact order `2m+1`, plateau
length `m`, and first failing extension are one invariant. -/
theorem exists_flatPlateau_kernel_nextFailure_and_negativeSource_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      (xiShiftedMomentHankelMatrix y (n + m + 1)).PosSemidef ∧
      xiShiftedMomentHankelMatrix y (n + m + 1) *ᵥ
          xiShiftedHankelBoundaryLiftedNullVector c m = 0 ∧
      ¬ (xiShiftedMomentHankelMatrix y (n + m + 2)).PosSemidef ∧
      HTGeometry.momentFunctional
        (fun k => (primeArchShiftedReciprocalMoment y k).re)
        (X * (HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m) ^ 2) < 0 := by
  obtain ⟨m, hzeroPA, hnegative⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA k hk
  have hplateau := xiShiftedMomentHankelMatrix_posSemidef_flatPlateau_of_odd_contact
    c hhead hc hlast hzeroXi
  have hkernel := xiShiftedHankelBoundaryLiftedNullVector_mem_kernel_of_odd_contact
    c hhead hc hlast hzeroXi
  have hvalue := primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroPA
  have hdefectNeg :
      primeArchShiftedHankelBoundaryPadeDefect y c
          (2 * n + (2 * m + 1)) < 0 := by
    rw [hvalue]
    exact hnegative
  have hfirst : xiShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0 := by
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact ne_of_lt hdefectNeg
  have hnext := xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_first_odd_contact
    c hhead hc hlast hzeroXi hfirst
  exact ⟨m, hzeroPA, hplateau, hkernel, hnext, hnegative⟩

/-- **Genuine-crossing hyperbolic source plane.**  Every hypothetical two-sided Route-U loss
selects two consecutive lifted null reporters whose completed prime--Gamma Gram determinant is
strictly negative.  The same selected plane carries the negative marked-`X` source channel. -/
theorem exists_primeArch_liftedNull_hyperbolicPlane_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ,
      (∀ k < 2 * n + (2 * m + 1),
        primeArchShiftedHankelBoundaryPadeDefect y c k = 0) ∧
      let P := HTGeometry.finiteHankelNullMonicPolynomial c
      let A := P * X ^ m
      let B := P * X ^ (m + 1)
      HTGeometry.momentInner
            (fun k => (primeArchShiftedReciprocalMoment y k).re) A A *
          HTGeometry.momentInner
            (fun k => (primeArchShiftedReciprocalMoment y k).re) B B -
          HTGeometry.momentInner
            (fun k => (primeArchShiftedReciprocalMoment y k).re) A B ^ 2 < 0 ∧
      HTGeometry.momentInner
          (fun k => (primeArchShiftedReciprocalMoment y k).re)
          A (X * A) < 0 := by
  obtain ⟨m, hzero, hnegative⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  have hfirst : primeArchShiftedHankelBoundaryPadeDefect y c
      (2 * n + (2 * m + 1)) ≠ 0 := by
    rw [primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
      c hlast hzero]
    exact ne_of_lt hnegative
  have hdet := liftedNullPair_primeArch_gramDet_neg_of_first_odd_contact
    hy hymax c hlast hzero hfirst
  refine ⟨m, hzero, hdet, ?_⟩
  simpa only [HTGeometry.momentInner_def, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using hnegative

/-! ### Certified critical-prefix versus adaptive tail -/

/-- A shifted reciprocal-square copy on the critical line is a strictly positive real node.
Unlike the global RH version, this only assumes criticality of the selected copy. -/
theorem xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2) :
    ∃ x : ℝ, 0 < x ∧ xiShiftedReciprocalSquare y q = (x : ℂ) := by
  obtain ⟨x, hx, hcoord⟩ :=
    xiCentralReciprocalSquare_pos_real_of_re_eq_half q.1 hline
  have hcopy : xiZeroCopyReciprocalSquare q = (x : ℂ) := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact hcoord
  refine ⟨x / (1 + y * x), div_pos hx (by nlinarith), ?_⟩
  rw [xiShiftedReciprocalSquare, hcopy]
  push_cast
  rfl

/-- The real polarized trace-Hankel atom is summable.  This missing public form follows from the
already-summable longitudinal and transverse channels. -/
theorem summable_xiShiftedApertureHankelPairTerm
    {y : ℝ} (hy : 0 < y) (p r : Polynomial ℝ) :
    Summable (xiShiftedApertureHankelPairTerm y p r) := by
  have h := (summable_xiShiftedApertureHilbertPairTerm hy p r).sub
    (summable_xiShiftedApertureTransversePairTerm hy p r)
  exact h.congr fun q =>
    (xiShiftedApertureHankelPairTerm_eq_hilbert_sub_transverse hy p r q).symm

/-- **Critical-line tail absorption.** For every fixed positive sampling frame, canonical capacity
over any subtype of critical-line Xi copies is automatically summable.  This uses only unconditional
summability of shifted reciprocal powers; no quantitative zero-density input is required. -/
theorem summable_canonicalCapacity_xiCriticalLineSubtype
    {N n : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (hx : ∀ r, 0 < x r)
    (hcard : n ≤ ((Finset.univ : Finset (Fin N)).image x).card)
    (Q : Set XiZeroCopy)
    (hline : ∀ q : Q, ((q : XiZeroCopy).1 : ℂ).re = 1 / 2) :
    Summable (fun q : Q => weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x n
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
      (xiShiftedReciprocalSquare y (q : XiZeroCopy))) := by
  have hpos : ∀ q : Q, ∃ t : ℝ, 0 < t ∧
      xiShiftedReciprocalSquare y (q : XiZeroCopy) = (t : ℂ) := by
    intro q
    exact xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy.le
      (q : XiZeroCopy) (hline q)
  choose t ht hcoord using hpos
  have hpow : ∀ i j : Fin n,
      Summable (fun q : Q => t q ^ ((i : ℕ) + (j : ℕ) + 1)) := by
    intro i j
    have hs := ((summable_xiShiftedReciprocalSquare_pow hy.le
      ((i : ℕ) + (j : ℕ))).norm.subtype Q)
    exact hs.congr (fun q => by
      change ‖xiShiftedReciprocalSquare y (q : XiZeroCopy) ^
        ((i : ℕ) + (j : ℕ) + 1)‖ = _
      rw [hcoord q, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht q)])
  have hs := canonicalCapacity_positiveTargets_summable_of_power_summable
    x hx hcard t ht hpow
  exact hs.congr (fun q => by rw [hcoord q])

/-- **Off-critical capacity reduction.** Fixing one canonical positive frame, subunit canonical
capacity is required only from off-critical-line Xi copies.  The entire critical-line sector is
automatically summable and a finite part of it can be added to the positive prefix until its
remaining capacity is arbitrarily small. -/
theorem full_xiShiftedHankelPair_tsum_pos_of_offCriticalCanonicalCapacity_lt_one
    {N d : ℕ} {y : ℝ} (hy : 0 < y)
    (x : Fin N → ℝ) (qbase : Fin N → XiZeroCopy)
    (hx : ∀ i, 0 < x i) (hqinj : Function.Injective qbase)
    (hcoord : ∀ i, xiShiftedReciprocalSquare y (qbase i) = (x i : ℂ))
    (hqline : ∀ i, ((qbase i).1 : ℂ).re = 1 / 2)
    (hcard : d < ((Finset.univ : Finset (Fin N)).image x).card)
    (p : Polynomial ℝ) (hp : p ≠ 0) (hdegree : p.natDegree ≤ d)
    (hoffSummable : Summable (fun q : ↥(({q : XiZeroCopy |
        (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ) =>
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))))
    (hoff : (∑' q : ↥(({q : XiZeroCopy |
        (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
      weightedRedundantSamplingCapacity x
        (HTGeometry.canonicalMonomialReconstruction x (d + 1)
          (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) :
    0 < ∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y p p q := by
  classical
  let P : Set XiZeroCopy := {q | (q.1 : ℂ).re = 1 / 2}
  let B : Finset XiZeroCopy := (Finset.univ : Finset (Fin N)).image qbase
  let f : XiZeroCopy → ℝ := fun q =>
    weightedRedundantSamplingCapacity x
      (HTGeometry.canonicalMonomialReconstruction x (d + 1)
        (xiShiftedReciprocalSquare y q))
      (xiShiftedReciprocalSquare y q)
  have hf0 : ∀ q, 0 ≤ f q := fun q =>
    weightedRedundantSamplingCapacity_nonneg x hx _ _
  have hPsum : Summable (fun q : P => f (q : XiZeroCopy)) := by
    apply summable_canonicalCapacity_xiCriticalLineSubtype hy x hx
      (Nat.succ_le_iff.mpr hcard) P
    intro q
    exact q.property
  have hCsum : Summable (fun q : ↥(Pᶜ) => f (q : XiZeroCopy)) := by
    simpa only [P, f] using hoffSummable
  have hClt : (∑' q : ↥(Pᶜ), f (q : XiZeroCopy)) < 1 := by
    simpa only [P, f] using hoff
  have hBP : ∀ q ∈ B, q ∈ P := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hqline i
  obtain ⟨S, hBS, hSP, hSsum, hSlt⟩ :=
    GaloisForLFunctions.HTGeometry.exists_finset_absorber_of_compl_tsum_lt_one
      f hf0 P hPsum hCsum hClt B hBP
  apply full_xiShiftedHankelPair_tsum_pos_of_canonicalBaseFrame_positiveAbsorber
    hy x qbase hx hqinj hcoord hcard S
  · intro i
    exact hBS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro q hq
    exact xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy.le q (hSP q hq)
  · exact hp
  · exact hdegree
  · simpa only [f] using hSsum
  · simpa only [f] using hSlt

/-- More distinct positive critical-line nodes than the polynomial degree force a strictly
positive finite-prefix square.  No coefficient-norm or eigenvalue estimate is used. -/
theorem finite_criticalLine_bulk_hankelPair_self_pos
    {y : ℝ} (hy : 0 ≤ y) (S : Finset XiZeroCopy) (p : Polynomial ℝ)
    (hp : p ≠ 0)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : p.natDegree <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    0 < ∑ q ∈ S, xiShiftedApertureHankelPairTerm y p p q := by
  have hnonneg : ∀ q ∈ S,
      0 ≤ xiShiftedApertureHankelPairTerm y p p q := by
    intro q hq
    obtain ⟨x, hx, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy q (hline q hq)
    rw [xiShiftedApertureHankelPairTerm, hcoord]
    simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc
      0 ≤ x * Polynomial.eval x p ^ 2 := mul_nonneg hx.le (sq_nonneg _)
      _ = x * Polynomial.eval x p * Polynomial.eval x p := by ring
  apply Finset.sum_pos' hnonneg
  by_contra hnone
  push Not at hnone
  let T : Finset ℝ := S.image fun q => (xiShiftedReciprocalSquare y q).re
  have heval : ∀ x : T, Polynomial.eval (x : ℝ) p = 0 := by
    intro x
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp x.property
    have hterm := hnone q hq
    obtain ⟨a, ha, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy q (hline q hq)
    have hreal : (xiShiftedReciprocalSquare y q).re = a := by
      rw [hcoord]
      rfl
    rw [xiShiftedApertureHankelPairTerm, hcoord] at hterm
    simp only [evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re] at hterm
    have hpa : Polynomial.eval a p = 0 := by
      by_contra hne
      have hpos : 0 < a * Polynomial.eval a p * Polynomial.eval a p := by
        nlinarith [sq_pos_of_ne_zero hne]
      linarith
    have hax : a = (x : ℝ) := hreal.symm.trans hqx
    simpa only [hax] using hpa
  have hpzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (f := fun x : T => (x : ℝ)) Subtype.val_injective heval (by simpa [T] using hcard)
  exact hp hpzero

/-- Every finite critical-line prefix is nonnegative in the marked-`X` polarized channel. -/
theorem finite_criticalLine_bulk_hankelPair_X_mul_nonneg
    {y : ℝ} (hy : 0 ≤ y) (S : Finset XiZeroCopy) (p : Polynomial ℝ)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2) :
    0 ≤ ∑ q ∈ S, xiShiftedApertureHankelPairTerm y p (X * p) q := by
  apply Finset.sum_nonneg
  intro q hq
  obtain ⟨x, hx, hcoord⟩ :=
    xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy q (hline q hq)
  rw [xiShiftedApertureHankelPairTerm, hcoord]
  simp only [evalRealPolynomial_ofReal, eval_mul, eval_X,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  nlinarith [sq_nonneg (Polynomial.eval x p)]

/-- **Off-critical carrier law.** If a polynomial is null for the full shifted Xi square but its
marked-`X` square is negative, then every sufficiently rich finite critical-line prefix forces both
negative channels to live entirely in the off-critical divisor.  Critical-line atoms contribute a
strictly positive null-square total and a nonnegative marked total; they cannot carry the Krein
birth. -/
theorem offCritical_energy_doubleNegative_of_null_and_marked_negative
    {y : ℝ} (hy : 0 < y) (R : Polynomial ℝ) (hR : R ≠ 0)
    (hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0)
    (hfullX :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R (X * R) q) < 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : R.natDegree <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
        xiShiftedApertureHankelPairTerm y R R (q : XiZeroCopy)) < 0 ∧
      (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
        xiShiftedApertureHankelPairTerm y R (X * R) (q : XiZeroCopy)) < 0 := by
  classical
  let P : Set XiZeroCopy := {q | (q.1 : ℂ).re = 1 / 2}
  let fSelf : XiZeroCopy → ℝ := xiShiftedApertureHankelPairTerm y R R
  let fX : XiZeroCopy → ℝ := xiShiftedApertureHankelPairTerm y R (X * R)
  have hSelfSum : Summable fSelf := by
    simpa only [fSelf] using summable_xiShiftedApertureHankelPairTerm hy R R
  have hXSum : Summable fX := by
    simpa only [fX] using summable_xiShiftedApertureHankelPairTerm hy R (X * R)
  have hLineSelfSum : Summable (fun q : P => fSelf (q : XiZeroCopy)) :=
    hSelfSum.subtype P
  have hOffSelfSum : Summable (fun q : ↥(Pᶜ) => fSelf (q : XiZeroCopy)) :=
    hSelfSum.subtype Pᶜ
  have hLineXSum : Summable (fun q : P => fX (q : XiZeroCopy)) :=
    hXSum.subtype P
  have hOffXSum : Summable (fun q : ↥(Pᶜ) => fX (q : XiZeroCopy)) :=
    hXSum.subtype Pᶜ
  have hLineSelf0 : ∀ q : P, 0 ≤ fSelf (q : XiZeroCopy) := by
    intro q
    obtain ⟨t, ht, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy.le
        (q : XiZeroCopy) q.property
    simp only [fSelf, xiShiftedApertureHankelPairTerm, hcoord,
      evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (Polynomial.eval t R)]
  let e : ↥S → P := fun q => ⟨(q : XiZeroCopy), hline q q.property⟩
  have heinj : Function.Injective e := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : P => (z : XiZeroCopy)) hqr
  have hFiniteSum : Summable (fun q : ↥S => fSelf (q : XiZeroCopy)) :=
    Summable.of_finite
  have hFiniteLeLine :
      (∑' q : ↥S, fSelf (q : XiZeroCopy)) ≤
        ∑' q : P, fSelf (q : XiZeroCopy) := by
    exact hFiniteSum.tsum_le_tsum_of_inj e heinj
      (fun q _ => hLineSelf0 q) (fun q => le_rfl) hLineSelfSum
  have hFinitePos : 0 < ∑' q : ↥S, fSelf (q : XiZeroCopy) := by
    rw [tsum_fintype]
    rw [← Finset.sum_subtype S (fun q => Iff.rfl)]
    simpa only [fSelf] using
      finite_criticalLine_bulk_hankelPair_self_pos hy.le S R hR hline hcard
  have hLineSelfPos : 0 < ∑' q : P, fSelf (q : XiZeroCopy) :=
    hFinitePos.trans_le hFiniteLeLine
  have hLineX0 : ∀ q : P, 0 ≤ fX (q : XiZeroCopy) := by
    intro q
    obtain ⟨t, ht, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy.le
        (q : XiZeroCopy) q.property
    simp only [fX, xiShiftedApertureHankelPairTerm, hcoord,
      evalRealPolynomial_ofReal, eval_mul, eval_X,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (Polynomial.eval t R)]
  have hLineXNonneg : 0 ≤ ∑' q : P, fX (q : XiZeroCopy) :=
    tsum_nonneg hLineX0
  have hsplitSelf :
      (∑' q : P, fSelf (q : XiZeroCopy)) +
        (∑' q : ↥(Pᶜ), fSelf (q : XiZeroCopy)) = ∑' q, fSelf q :=
    Summable.tsum_add_tsum_compl (f := fSelf) (s := P) hLineSelfSum hOffSelfSum
  have hsplitX :
      (∑' q : P, fX (q : XiZeroCopy)) +
        (∑' q : ↥(Pᶜ), fX (q : XiZeroCopy)) = ∑' q, fX q :=
    Summable.tsum_add_tsum_compl (f := fX) (s := P) hLineXSum hOffXSum
  refine ⟨?_, ?_⟩
  · simpa only [P, fSelf] using (by
      have hfull : (∑' q, fSelf q) = 0 := by simpa only [fSelf] using hfullSelf
      linarith : ∑' q : ↥(Pᶜ), fSelf (q : XiZeroCopy) < 0)
  · simpa only [P, fX] using (by
      have hfull : (∑' q, fX q) < 0 := by simpa only [fX] using hfullX
      linarith : ∑' q : ↥(Pᶜ), fX (q : XiZeroCopy) < 0)

/-- **Off-critical negative-index amplification.** If odd contact has order `2m+1`, then after any
critical-line prefix with more than `n+m` distinct shifted nodes, the off-critical divisor is
strictly negative on every nonzero vector `P Q`, `deg Q ≤ m`.  Thus order `2m+1` forces an
`m+1`-dimensional negative polynomial sector off the critical line; the terminal hyperbolic plane
is only its first visible corner. -/
theorem offCritical_liftedNullSubspace_neg_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card)
    (Q : Polynomial ℝ) (hQ : Q ≠ 0) (hQdeg : Q.natDegree ≤ m) :
    let A := HTGeometry.finiteHankelNullMonicPolynomial c * Q
    (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
      xiShiftedApertureHankelPairTerm y A A (q : XiZeroCopy)) < 0 := by
  classical
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * Q
  let L : Set XiZeroCopy := {q | (q.1 : ℂ).re = 1 / 2}
  let f : XiZeroCopy → ℝ := xiShiftedApertureHankelPairTerm y A A
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A ≠ 0 := mul_ne_zero hP.ne_zero hQ
  have hAdeg : A.natDegree ≤ n + m := by
    calc
      A.natDegree ≤ P.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
      _ ≤ n + m := by omega
  have hnull := momentFunctional_liftedNullSubspace_eq_zero_of_odd_contact
    c hlast hzero Q hQdeg
  have hfull : (∑' q : XiZeroCopy, f q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [f, A, P, pow_two] using hnull
  have hsum : Summable f := by
    simpa only [f] using summable_xiShiftedApertureHankelPairTerm hy A A
  have hLineSum : Summable (fun q : L => f (q : XiZeroCopy)) := hsum.subtype L
  have hOffSum : Summable (fun q : ↥(Lᶜ) => f (q : XiZeroCopy)) := hsum.subtype Lᶜ
  have hLine0 : ∀ q : L, 0 ≤ f (q : XiZeroCopy) := by
    intro q
    obtain ⟨t, ht, hcoord⟩ :=
      xiShiftedReciprocalSquare_pos_real_of_copy_re_eq_half hy.le
        (q : XiZeroCopy) q.property
    simp only [f, xiShiftedApertureHankelPairTerm, hcoord,
      evalRealPolynomial_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (Polynomial.eval t A)]
  let e : ↥S → L := fun q => ⟨(q : XiZeroCopy), hline q q.property⟩
  have heinj : Function.Injective e := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : L => (z : XiZeroCopy)) hqr
  have hFiniteSum : Summable (fun q : ↥S => f (q : XiZeroCopy)) := Summable.of_finite
  have hFiniteLeLine :
      (∑' q : ↥S, f (q : XiZeroCopy)) ≤ ∑' q : L, f (q : XiZeroCopy) := by
    exact hFiniteSum.tsum_le_tsum_of_inj e heinj
      (fun q _ => hLine0 q) (fun q => le_rfl) hLineSum
  have hFinitePos : 0 < ∑' q : ↥S, f (q : XiZeroCopy) := by
    rw [tsum_fintype]
    rw [← Finset.sum_subtype S (fun q => Iff.rfl)]
    simpa only [f] using finite_criticalLine_bulk_hankelPair_self_pos
      hy.le S A hA hline (hAdeg.trans_lt hcard)
  have hLinePos : 0 < ∑' q : L, f (q : XiZeroCopy) := hFinitePos.trans_le hFiniteLeLine
  have hsplit :
      (∑' q : L, f (q : XiZeroCopy)) +
        (∑' q : ↥(Lᶜ), f (q : XiZeroCopy)) = ∑' q, f q :=
    Summable.tsum_add_tsum_compl (f := f) (s := L) hLineSum hOffSum
  simpa only [L, f, A, P] using (by
    linarith : ∑' q : ↥(Lᶜ), f (q : XiZeroCopy) < 0)

/-- Functional-equation reflection is invisible to every shifted trace-Hankel pair atom. -/
theorem xiShiftedApertureHankelPairTerm_reflect
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p r (xiZeroCopyReflectEquiv q) =
      xiShiftedApertureHankelPairTerm y p r q := by
  simp [xiShiftedApertureHankelPairTerm, xiShiftedReciprocalSquare_reflect]

/-- Critical-line conjugation is also invisible: it conjugates the coordinate and both real
polynomial evaluations, leaving the real part of their product fixed. -/
theorem xiShiftedApertureHankelPairTerm_lineConj
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p r (xiZeroCopyLineConjEquiv q) =
      xiShiftedApertureHankelPairTerm y p r q := by
  rw [xiShiftedApertureHankelPairTerm, xiShiftedApertureHankelPairTerm,
    xiShiftedReciprocalSquare_lineConj, evalRealPolynomial_conj,
    evalRealPolynomial_conj]
  simp only [← map_mul, Complex.conj_re]

/-- Ordinary Schwarz conjugation is the composition of critical-line conjugation and functional
reflection, so it fixes every shifted trace-Hankel pair atom as well. -/
theorem xiShiftedApertureHankelPairTerm_copyConj
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p r (xiZeroCopyConjEquiv q) =
      xiShiftedApertureHankelPairTerm y p r q := by
  have hreflect := xiShiftedApertureHankelPairTerm_reflect y p r
    (xiZeroCopyConjEquiv q)
  have hline := xiShiftedApertureHankelPairTerm_lineConj y p r q
  rw [xiZeroCopyLineConjEquiv, Equiv.trans_apply] at hline
  exact hreflect.symm.trans hline

/-- Canonical representative of a complex-conjugation pair, chosen in the closed upper
half-plane.  The real trace-Hankel form can see a shifted reciprocal-square node only through this
fold. -/
def complexConjugationFold (z : ℂ) : ℂ :=
  ⟨z.re, |z.im|⟩

theorem complexConjugationFold_eq_self_or_conj (z : ℂ) :
    complexConjugationFold z = z ∨
      complexConjugationFold z = (starRingEnd ℂ) z := by
  by_cases hz : 0 ≤ z.im
  · left
    apply Complex.ext
    · rfl
    · simp only [complexConjugationFold, abs_of_nonneg hz]
  · right
    have hzlt : z.im < 0 := lt_of_not_ge hz
    apply Complex.ext
    · simp only [complexConjugationFold, Complex.conj_re]
    · simp only [complexConjugationFold, Complex.conj_im, abs_of_neg hzlt]

@[simp]
theorem complexConjugationFold_conj (z : ℂ) :
    complexConjugationFold ((starRingEnd ℂ) z) = complexConjugationFold z := by
  apply Complex.ext
  · simp [complexConjugationFold]
  · simp [complexConjugationFold]

/-- Equality after upper-half-plane folding is exactly equality modulo complex conjugation. -/
theorem complexConjugationFold_eq_iff {z w : ℂ} :
    complexConjugationFold z = complexConjugationFold w ↔
      z = w ∨ z = (starRingEnd ℂ) w := by
  constructor
  · intro h
    rcases complexConjugationFold_eq_self_or_conj z with hz | hz <;>
      rcases complexConjugationFold_eq_self_or_conj w with hw | hw
    · exact Or.inl (hz.symm.trans (h.trans hw))
    · exact Or.inr (hz.symm.trans (h.trans hw))
    · right
      have hc := congrArg (starRingEnd ℂ) (hz.symm.trans (h.trans hw))
      simpa using hc
    · left
      have hc := congrArg (starRingEnd ℂ) (hz.symm.trans (h.trans hw))
      simpa using hc
  · rintro (h | h)
    · rw [h]
    · rw [h, complexConjugationFold_conj]

/-- Equality of shifted reciprocal-square atoms determines the centered spectral point up to
functional-equation sign.  The mass Möbius transform creates no collisions. -/
theorem xiSpectralPoint_eq_or_eq_neg_of_shiftedReciprocalSquare_eq
    {y : ℝ} (hy : 0 ≤ y) {q r : XiZeroCopy}
    (h : xiShiftedReciprocalSquare y q = xiShiftedReciprocalSquare y r) :
    xiSpectralPoint q = xiSpectralPoint r ∨
      xiSpectralPoint q = -xiSpectralPoint r := by
  rw [xiShiftedReciprocalSquare_eq_inv hy,
    xiShiftedReciprocalSquare_eq_inv hy] at h
  have hden := (_root_.inv_inj).mp h
  have hs : xiSpectralPoint q ^ 2 = xiSpectralPoint r ^ 2 := by
    simpa only [xiSquaredNode] using add_left_cancel hden
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hs

/-- **Faithfulness of the folded node.**  Two Xi copies have the same folded shifted node only
when their centered spectral points lie in the same FE--Schwarz quartet.  Thus folded-node count is
geometric orbit count with analytic multiplicities and all accidental copy duplication removed. -/
theorem xiSpectralPoint_mem_quartet_of_conjugationFold_eq
    {y : ℝ} (hy : 0 ≤ y) {q r : XiZeroCopy}
    (h : complexConjugationFold (xiShiftedReciprocalSquare y q) =
      complexConjugationFold (xiShiftedReciprocalSquare y r)) :
    xiSpectralPoint q = xiSpectralPoint r ∨
      xiSpectralPoint q = -xiSpectralPoint r ∨
      xiSpectralPoint q = (starRingEnd ℂ) (xiSpectralPoint r) ∨
      xiSpectralPoint q = -(starRingEnd ℂ) (xiSpectralPoint r) := by
  rcases complexConjugationFold_eq_iff.mp h with hsame | hconj
  · rcases xiSpectralPoint_eq_or_eq_neg_of_shiftedReciprocalSquare_eq hy hsame with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hcopy : xiShiftedReciprocalSquare y q =
        xiShiftedReciprocalSquare y (xiZeroCopyConjEquiv r) := by
      rw [xiShiftedReciprocalSquare_copyConj hy]
      exact hconj
    rcases xiSpectralPoint_eq_or_eq_neg_of_shiftedReciprocalSquare_eq hy hcopy with h | h
    · rw [xiSpectralPoint_copyConj] at h
      exact Or.inr (Or.inr (Or.inr h))
    · rw [xiSpectralPoint_copyConj] at h
      right
      right
      left
      simpa only [neg_neg] using h

theorem conjugationFold_xiShiftedReciprocalSquare_eq_of_spectralPoint_mem_quartet
    {y : ℝ} (hy : 0 ≤ y) {q r : XiZeroCopy}
    (h : xiSpectralPoint q = xiSpectralPoint r ∨
      xiSpectralPoint q = -xiSpectralPoint r ∨
      xiSpectralPoint q = (starRingEnd ℂ) (xiSpectralPoint r) ∨
      xiSpectralPoint q = -(starRingEnd ℂ) (xiSpectralPoint r)) :
    complexConjugationFold (xiShiftedReciprocalSquare y q) =
      complexConjugationFold (xiShiftedReciprocalSquare y r) := by
  apply complexConjugationFold_eq_iff.mpr
  rcases h with h | h | h | h
  · left
    rw [xiShiftedReciprocalSquare_eq_inv hy,
      xiShiftedReciprocalSquare_eq_inv hy, xiSquaredNode, xiSquaredNode, h]
  · left
    rw [xiShiftedReciprocalSquare_eq_inv hy,
      xiShiftedReciprocalSquare_eq_inv hy, xiSquaredNode, xiSquaredNode, h]
    ring
  · right
    rw [xiShiftedReciprocalSquare_eq_inv hy,
      xiShiftedReciprocalSquare_eq_inv hy, map_inv₀, map_add,
      Complex.conj_ofReal, xiSquaredNode, xiSquaredNode, map_pow, h]
  · right
    rw [xiShiftedReciprocalSquare_eq_inv hy,
      xiShiftedReciprocalSquare_eq_inv hy, map_inv₀, map_add,
      Complex.conj_ofReal, xiSquaredNode, xiSquaredNode, map_pow, h]
    ring

/-- **Mass-shift invariance of the folded orbit relation.**  Every nonnegative real Möbius shift
induces exactly the same equivalence relation on Xi copies: equality of folded shifted nodes is
equality of the underlying centered spectral points modulo the FE--Schwarz quartet. -/
theorem conjugationFold_xiShiftedReciprocalSquare_eq_iff_shift
    {y v : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v) (q r : XiZeroCopy) :
    complexConjugationFold (xiShiftedReciprocalSquare y q) =
        complexConjugationFold (xiShiftedReciprocalSquare y r) ↔
      complexConjugationFold (xiShiftedReciprocalSquare v q) =
        complexConjugationFold (xiShiftedReciprocalSquare v r) := by
  constructor
  · intro h
    exact conjugationFold_xiShiftedReciprocalSquare_eq_of_spectralPoint_mem_quartet hv
      (xiSpectralPoint_mem_quartet_of_conjugationFold_eq hy h)
  · intro h
    exact conjugationFold_xiShiftedReciprocalSquare_eq_of_spectralPoint_mem_quartet hy
      (xiSpectralPoint_mem_quartet_of_conjugationFold_eq hv h)

/-- Finite folded-node count is independent of nonnegative mass shift.  In particular every
adaptive Route-U orbit-rank obstruction can be transported without loss to shift one. -/
theorem card_image_conjugationFold_xiShiftedReciprocalSquare_eq_shift
    {y v : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v) (T : Finset XiZeroCopy) :
    (T.image fun q =>
        complexConjugationFold (xiShiftedReciprocalSquare y q)).card =
      (T.image fun q =>
        complexConjugationFold (xiShiftedReciprocalSquare v q)).card := by
  classical
  let f : XiZeroCopy → ℂ := fun q =>
    complexConjugationFold (xiShiftedReciprocalSquare y q)
  let g : XiZeroCopy → ℂ := fun q =>
    complexConjugationFold (xiShiftedReciprocalSquare v q)
  have hfg : ∀ q r, f q = f r ↔ g q = g r := fun q r => by
    simpa only [f, g] using
      conjugationFold_xiShiftedReciprocalSquare_eq_iff_shift hy hv q r
  let rep : (z : ℂ) → z ∈ T.image f → XiZeroCopy := fun z hz =>
    (Finset.mem_image.mp hz).choose
  have hrepMem (z : ℂ) (hz : z ∈ T.image f) : rep z hz ∈ T :=
    (Finset.mem_image.mp hz).choose_spec.1
  have hrepEq (z : ℂ) (hz : z ∈ T.image f) : f (rep z hz) = z :=
    (Finset.mem_image.mp hz).choose_spec.2
  change (T.image f).card = (T.image g).card
  apply Finset.card_bij (fun z hz => g (rep z hz))
  · intro z hz
    exact Finset.mem_image.mpr ⟨rep z hz, hrepMem z hz, rfl⟩
  · intro z hz w hw heq
    have hfeq : f (rep z hz) = f (rep w hw) :=
      (hfg (rep z hz) (rep w hw)).mpr heq
    simpa only [hrepEq] using hfeq
  · intro b hb
    obtain ⟨r, hrT, hrg⟩ := Finset.mem_image.mp hb
    let a := f r
    have ha : a ∈ T.image f := Finset.mem_image.mpr ⟨r, hrT, rfl⟩
    refine ⟨a, ha, ?_⟩
    have hfeq : f (rep a ha) = f r := by
      simpa only [a] using hrepEq a ha
    exact (hfg (rep a ha) r).mp hfeq |>.trans hrg

theorem card_univ_image_conjugationFold_xiShiftedReciprocalSquare_eq_shift
    {ι : Type*} [Fintype ι] {y v : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v)
    (target : ι → XiZeroCopy) :
    (Finset.univ.image fun i : ι =>
        complexConjugationFold (xiShiftedReciprocalSquare y (target i))).card =
      (Finset.univ.image fun i : ι =>
        complexConjugationFold (xiShiftedReciprocalSquare v (target i))).card := by
  classical
  have h := card_image_conjugationFold_xiShiftedReciprocalSquare_eq_shift
    hy hv (Finset.univ.image target)
  change (Finset.univ.image ((fun q =>
      complexConjugationFold (xiShiftedReciprocalSquare y q)) ∘ target)).card =
    (Finset.univ.image ((fun q =>
      complexConjugationFold (xiShiftedReciprocalSquare v q)) ∘ target)).card
  simpa only [Finset.image_image] using h

/-- Multiplicity-exact off-critical Xi-copy type used by Route U. -/
abbrev XiOffCriticalCopy :=
  ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ)

/-- Critical-line conjugation restricted to off-critical copies. -/
def xiOffCriticalLineConj (q : XiOffCriticalCopy) : XiOffCriticalCopy := by
  refine ⟨xiZeroCopyLineConjEquiv (q : XiZeroCopy), ?_⟩
  have hoff : ((q : XiZeroCopy).1 : ℂ).re ≠ 1 / 2 := by
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using q.property
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  change (1 - (starRingEnd ℂ) ((q : XiZeroCopy).1 : ℂ)).re ≠ 1 / 2
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
  intro h
  apply hoff
  linarith

/-- Schwarz conjugation restricted to off-critical copies. -/
def xiOffCriticalConj (q : XiOffCriticalCopy) : XiOffCriticalCopy := by
  refine ⟨xiZeroCopyConjEquiv (q : XiZeroCopy), ?_⟩
  have hoff : ((q : XiZeroCopy).1 : ℂ).re ≠ 1 / 2 := by
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using q.property
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  change ((starRingEnd ℂ) ((q : XiZeroCopy).1 : ℂ)).re ≠ 1 / 2
  simpa only [Complex.conj_re] using hoff

/-- Finite FE--Schwarz quartet completion.  Repetitions are removed as a finite set. -/
def xiOffCriticalQuartetCompletion (T : Finset XiOffCriticalCopy) :
    Finset XiOffCriticalCopy :=
  T ∪ T.image xiOffCriticalLineConj ∪ T.image xiOffCriticalConj ∪
    T.image (xiOffCriticalLineConj ∘ xiOffCriticalConj)

theorem subset_xiOffCriticalQuartetCompletion (T : Finset XiOffCriticalCopy) :
    T ⊆ xiOffCriticalQuartetCompletion T := by
  intro q hq
  simp only [xiOffCriticalQuartetCompletion, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hq))

/-- Every shifted Xi trace-Hankel atom is exactly the block attached to its conjugation-folded
reciprocal-square node.  Functional-equation reflection already fixes the node; this additional
fold removes the remaining Schwarz-conjugate duplication. -/
theorem xiShiftedApertureHankelPairTerm_eq_conjugationFold
    (y : ℝ) (p r : Polynomial ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y p r q =
      (complexConjugationFold (xiShiftedReciprocalSquare y q) *
        evalRealPolynomial p (complexConjugationFold (xiShiftedReciprocalSquare y q)) *
        evalRealPolynomial r (complexConjugationFold (xiShiftedReciprocalSquare y q))).re := by
  let z := xiShiftedReciprocalSquare y q
  rcases complexConjugationFold_eq_self_or_conj z with hz | hz
  · simp only [xiShiftedApertureHankelPairTerm, z, hz]
  · rw [xiShiftedApertureHankelPairTerm]
    change (z * evalRealPolynomial p z * evalRealPolynomial r z).re = _
    rw [hz, evalRealPolynomial_conj, evalRealPolynomial_conj]
    rw [← map_mul, ← map_mul, Complex.conj_re]

/-- **One negative-index unit per finite Xi copy.**  A finite family of shifted Xi atoms cannot be
strictly negative on all nonzero real polynomials of degree at most `m` unless it has at least
`m+1` members.  Choose a square root `rᵢ² = zᵢ` of each atom.  Its block is
`Re(zᵢ A(zᵢ)²) = Re(rᵢ A(zᵢ))² - Im(rᵢ A(zᵢ))²`, hence contributes only the single negative
coordinate `Im(rᵢ A(zᵢ))`.  If all these coordinates vanish, every block is nonnegative; strict
negativity therefore makes the negative-coordinate map injective.  Finite-dimensional rank gives
the sharp cardinality bound. -/
theorem finite_xiFamily_negative_degreeLT_card
    {ι : Type*} [Fintype ι] {m : ℕ} (y : ℝ) (P : Polynomial ℝ)
    (target : ι → XiZeroCopy)
    (hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ q : ι, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0) :
    m + 1 ≤ Fintype.card ι := by
  classical
  let root : ι → ℂ := fun i =>
    (IsAlgClosed.exists_eq_mul_self (xiShiftedReciprocalSquare y (target i))).choose
  have hroot : ∀ i : ι,
      xiShiftedReciprocalSquare y (target i) = root i * root i := fun i =>
    (IsAlgClosed.exists_eq_mul_self (xiShiftedReciprocalSquare y (target i))).choose_spec
  let Ψ : Polynomial.degreeLT ℝ (m + 1) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun Q q =>
        (root q *
          evalRealPolynomial (P * (Q : Polynomial ℝ))
            (xiShiftedReciprocalSquare y (target q))).im
      map_add' := by
        intro Q R
        funext q
        simp only [Submodule.coe_add, mul_add, evalRealPolynomial, Polynomial.map_add,
          Polynomial.eval_add]
        simp [mul_add]
      map_smul' := by
        intro a Q
        funext q
        simp only [Submodule.coe_smul_of_tower, evalRealPolynomial]
        simp [Complex.mul_im, mul_left_comm] }
  have hΨ : Function.Injective Ψ := by
    intro Q R hQR
    apply sub_eq_zero.mp
    let D : Polynomial.degreeLT ℝ (m + 1) := Q - R
    suffices hD : D = 0 by
      simpa only [D, sub_eq_zero] using hD
    by_contra hD
    have hmap : Ψ D = 0 := by
      rw [map_sub, hQR, sub_self]
    have hnonneg : ∀ q : ι,
        0 ≤ xiShiftedApertureHankelPairTerm y
          (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target q) := by
      intro q
      let z := xiShiftedReciprocalSquare y (target q)
      let a := evalRealPolynomial (P * (D : Polynomial ℝ)) z
      let b := root q * a
      have hbim : b.im = 0 := by
        have := congrFun hmap q
        change Ψ D q = 0 at this
        have hΨapply : Ψ D q = b.im := by rfl
        rw [hΨapply] at this
        exact this
      have hterm : xiShiftedApertureHankelPairTerm y
          (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target q) =
          b.re ^ 2 - b.im ^ 2 := by
        have hz : z = root q * root q := hroot q
        calc
          _ = (z * a * a).re := by rfl
          _ = (b * b).re := by rw [hz]; simp only [b]; ring_nf
          _ = b.re ^ 2 - b.im ^ 2 := by simp only [Complex.mul_re]; ring
      rw [hterm, hbim]
      nlinarith [sq_nonneg b.re]
    have hsum : 0 ≤ ∑ q : ι, xiShiftedApertureHankelPairTerm y
        (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target q) :=
      Finset.sum_nonneg fun q _ => hnonneg q
    exact (not_lt_of_ge hsum) (hneg D hD)
  calc
    m + 1 = Module.finrank ℝ (Polynomial.degreeLT ℝ (m + 1)) := by
      rw [(Polynomial.degreeLTEquiv ℝ (m + 1)).finrank_eq, Module.finrank_pi]
      simp
    _ ≤ Module.finrank ℝ (ι → ℝ) := Ψ.finrank_le_finrank_of_injective hΨ
    _ = Fintype.card ι := by rw [Module.finrank_pi]

/-- **Sharp folded-node negative-index law.**  Copy count is not the intrinsic bound: reflection
fixes the shifted reciprocal square, conjugation replaces it by its complex conjugate, and the real
trace-Hankel block is unchanged.  Therefore strict negativity on degree at most `m` requires at
least `m+1` *distinct conjugation-folded shifted nodes*.  Multiplicity, quartet duplication, and
accidental collisions of different zero orbits cannot create additional negative directions. -/
theorem finite_xiFamily_negative_degreeLT_foldedNode_card
    {ι : Type*} [Fintype ι] {m : ℕ} (y : ℝ) (P : Polynomial ℝ)
    (target : ι → XiZeroCopy)
    (hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ q : ι, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0) :
    m + 1 ≤ (Finset.univ.image fun i : ι =>
      complexConjugationFold (xiShiftedReciprocalSquare y (target i))).card := by
  classical
  let nodes : Finset ℂ := Finset.univ.image fun i : ι =>
    complexConjugationFold (xiShiftedReciprocalSquare y (target i))
  let node : ι → ↥nodes := fun i =>
    ⟨complexConjugationFold (xiShiftedReciprocalSquare y (target i)),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let root : ↥nodes → ℂ := fun z =>
    (IsAlgClosed.exists_eq_mul_self (z : ℂ)).choose
  have hroot : ∀ z : ↥nodes, (z : ℂ) = root z * root z := fun z =>
    (IsAlgClosed.exists_eq_mul_self (z : ℂ)).choose_spec
  let Ψ : Polynomial.degreeLT ℝ (m + 1) →ₗ[ℝ] (↥nodes → ℝ) :=
    { toFun := fun Q z =>
        (root z * evalRealPolynomial (P * (Q : Polynomial ℝ)) (z : ℂ)).im
      map_add' := by
        intro Q R
        funext z
        simp only [Submodule.coe_add, mul_add, evalRealPolynomial, Polynomial.map_add,
          Polynomial.eval_add]
        simp [mul_add]
      map_smul' := by
        intro a Q
        funext z
        simp only [Submodule.coe_smul_of_tower, evalRealPolynomial]
        simp [Complex.mul_im, mul_left_comm] }
  have hΨ : Function.Injective Ψ := by
    intro Q R hQR
    apply sub_eq_zero.mp
    let D : Polynomial.degreeLT ℝ (m + 1) := Q - R
    suffices hD : D = 0 by
      simpa only [D, sub_eq_zero] using hD
    by_contra hD
    have hmap : Ψ D = 0 := by
      rw [map_sub, hQR, sub_self]
    have hnonneg : ∀ i : ι,
        0 ≤ xiShiftedApertureHankelPairTerm y
          (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target i) := by
      intro i
      let z : ↥nodes := node i
      let a := evalRealPolynomial (P * (D : Polynomial ℝ)) (z : ℂ)
      let b := root z * a
      have hbim : b.im = 0 := by
        have hzero := congrFun hmap z
        change Ψ D z = 0 at hzero
        have hΨapply : Ψ D z = b.im := by rfl
        rw [hΨapply] at hzero
        exact hzero
      have hterm : xiShiftedApertureHankelPairTerm y
          (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target i) =
          b.re ^ 2 - b.im ^ 2 := by
        rw [xiShiftedApertureHankelPairTerm_eq_conjugationFold]
        change ((z : ℂ) * a * a).re = _
        calc
          ((z : ℂ) * a * a).re = (b * b).re := by
            rw [hroot z]
            simp only [b]
            ring_nf
          _ = b.re ^ 2 - b.im ^ 2 := by
            simp only [Complex.mul_re]
            ring
      rw [hterm, hbim]
      nlinarith [sq_nonneg b.re]
    have hsum : 0 ≤ ∑ i : ι, xiShiftedApertureHankelPairTerm y
        (P * (D : Polynomial ℝ)) (P * (D : Polynomial ℝ)) (target i) :=
      Finset.sum_nonneg fun i _ => hnonneg i
    exact (not_lt_of_ge hsum) (hneg D hD)
  change m + 1 ≤ nodes.card
  calc
    m + 1 = Module.finrank ℝ (Polynomial.degreeLT ℝ (m + 1)) := by
      rw [(Polynomial.degreeLTEquiv ℝ (m + 1)).finrank_eq, Module.finrank_pi]
      simp
    _ ≤ Module.finrank ℝ (↥nodes → ℝ) := Ψ.finrank_le_finrank_of_injective hΨ
    _ = Fintype.card ↥nodes := by rw [Module.finrank_pi]
    _ = nodes.card := Fintype.card_coe nodes

/-- **One negative-index unit per folded Xi quartet.**  Reflection and both conjugations make all
four members of an off-critical Xi quartet contribute the same shifted trace-Hankel block.  Hence a
family of complete quartet blocks that is negative on the degree-`m` polynomial space needs at
least `m+1` quartet representatives.  Multiplicity four changes mass, not inertia. -/
theorem finite_xiQuartetFamily_negative_degreeLT_card
    {ι : Type*} [Fintype ι] {m : ℕ} (y : ℝ) (P : Polynomial ℝ)
    (base : ι → XiZeroCopy)
    (hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ i : ι,
        (xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (base i) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyLineConjEquiv (base i)) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyConjEquiv (base i)) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyLineConjEquiv (xiZeroCopyConjEquiv (base i))))) < 0) :
    m + 1 ≤ Fintype.card ι := by
  apply finite_xiFamily_negative_degreeLT_card y P base
  intro Q hQ
  have h := hneg Q hQ
  have heq :
      (∑ i : ι,
        (xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (base i) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyLineConjEquiv (base i)) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyConjEquiv (base i)) +
          xiShiftedApertureHankelPairTerm y
            (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (xiZeroCopyLineConjEquiv (xiZeroCopyConjEquiv (base i))))) =
        4 * ∑ i : ι, xiShiftedApertureHankelPairTerm y
          (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (base i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [xiShiftedApertureHankelPairTerm_lineConj,
      xiShiftedApertureHankelPairTerm_copyConj,
      xiShiftedApertureHankelPairTerm_lineConj,
      xiShiftedApertureHankelPairTerm_copyConj]
    ring
  rw [heq] at h
  nlinarith

/-- Coefficient expansion of one lifted Xi atom.  This identifies its degree-`d` polynomial form
with the quadratic form of the monomial-basis Gram matrix. -/
theorem xiShiftedApertureHankelPairTerm_P_mul_ofFn_self
    (y : ℝ) (P : Polynomial ℝ) (d : ℕ) (x : Fin d → ℝ) (q : XiZeroCopy) :
    xiShiftedApertureHankelPairTerm y
        (P * Polynomial.ofFn d x) (P * Polynomial.ofFn d x) q =
      ∑ i : Fin d, ∑ j : Fin d, x i *
        xiShiftedApertureHankelPairTerm y
          (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) q * x j := by
  let z := xiShiftedReciprocalSquare y q
  have heval : evalRealPolynomial (Polynomial.ofFn d x) z =
      ∑ i : Fin d, ((x i : ℝ) : ℂ) * z ^ (i : ℕ) := by
    rw [evalRealPolynomial, Polynomial.ofFn_eq_sum_monomial]
    simp
  have hcomplex :
      z * evalRealPolynomial (P * Polynomial.ofFn d x) z *
          evalRealPolynomial (P * Polynomial.ofFn d x) z =
        ∑ i : Fin d, ∑ j : Fin d, (((x i * x j : ℝ) : ℂ) *
          (z * evalRealPolynomial (P * X ^ (i : ℕ)) z *
            evalRealPolynomial (P * X ^ (j : ℕ)) z)) := by
    simp only [evalRealPolynomial_mul, evalRealPolynomial_pow, heval]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [evalRealPolynomial, Polynomial.map_X, Polynomial.eval_X]
    push_cast
    ring
  rw [xiShiftedApertureHankelPairTerm]
  change (z * evalRealPolynomial (P * Polynomial.ofFn d x) z *
      evalRealPolynomial (P * Polynomial.ofFn d x) z).re = _
  rw [hcomplex]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, xiShiftedApertureHankelPairTerm, z]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Finite witness for a summable negative polynomial sector.**  If a summable Xi family is
strictly negative on every nonzero polynomial of degree at most `m`, one finite subfamily already
has the same simultaneous strict negativity.  The proof forms the full `(m+1)`-dimensional Gram,
uses its coercive negative margin, and applies openness of positive definiteness to finite partial
sums.  Thus an infinite divisor cannot hide the forced negative index only in a diffuse tail. -/
theorem exists_finsetCompletion_xiFamily_negative_degreeLT_of_tsum_negative
    {ι : Type*} {m : ℕ} (y : ℝ) (P : Polynomial ℝ) (target : ι → XiZeroCopy)
    (completion : Finset ι → Finset ι)
    (hcompletion : ∀ T, T ⊆ completion T)
    (hsum : ∀ i j : Fin (m + 1), Summable (fun q : ι =>
      xiShiftedApertureHankelPairTerm y
        (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) (target q)))
    (hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑' q : ι, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0) :
    ∃ T : Finset ι, ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ q ∈ completion T, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0 := by
  classical
  let B : Fin (m + 1) → Fin (m + 1) → ι → ℝ := fun i j q =>
    xiShiftedApertureHankelPairTerm y
      (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) (target q)
  let G0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun i j => ∑' q, B i j q
  let G : Finset ι → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun T i j =>
    ∑ q ∈ T, B i j q
  have hBsymm : ∀ i j q, B i j q = B j i q := by
    intro i j q
    simp only [B, xiShiftedApertureHankelPairTerm]
    congr 1
    ring
  have hG0Herm : G0.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [G0, star_trivial]
    exact tsum_congr fun q => hBsymm j i q
  have hGHerm : ∀ T, (-(G T)).IsHermitian := by
    intro T
    apply Matrix.IsHermitian.neg
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [G, star_trivial]
    apply Finset.sum_congr rfl
    intro q _
    exact hBsymm j i q
  have hquad_tsum : ∀ x : Fin (m + 1) → ℝ,
      x ⬝ᵥ G0 *ᵥ x = ∑' q : ι, xiShiftedApertureHankelPairTerm y
        (P * Polynomial.ofFn (m + 1) x) (P * Polynomial.ofFn (m + 1) x) (target q) := by
    intro x
    calc
      x ⬝ᵥ G0 *ᵥ x = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          x i * (∑' q : ι, B i j q) * x j := by
        simp only [dotProduct, Matrix.mulVec, G0, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑' q : ι, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          x i * B i j q * x j := by
        rw [Summable.tsum_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [Summable.tsum_finsetSum]
          · apply Finset.sum_congr rfl
            intro j _
            calc
              x i * (∑' q : ι, B i j q) * x j =
                  (∑' q : ι, x i * B i j q) * x j := by
                    rw [Summable.tsum_mul_left (x i) (hsum i j)]
              _ = ∑' q : ι, x i * B i j q * x j := by
                    rw [Summable.tsum_mul_right (x j) ((hsum i j).mul_left (x i))]
          · intro j _
            exact ((hsum i j).mul_left (x i)).mul_right (x j)
        · intro i _
          exact summable_sum fun j _ =>
            ((hsum i j).mul_left (x i)).mul_right (x j)
      _ = _ := tsum_congr fun q => by
        simpa only [B] using
          (xiShiftedApertureHankelPairTerm_P_mul_ofFn_self
            y P (m + 1) x (target q)).symm
  have hquad_sum : ∀ (T : Finset ι) (x : Fin (m + 1) → ℝ),
      x ⬝ᵥ G T *ᵥ x = ∑ q ∈ T, xiShiftedApertureHankelPairTerm y
        (P * Polynomial.ofFn (m + 1) x) (P * Polynomial.ofFn (m + 1) x) (target q) := by
    intro T x
    rw [show (∑ q ∈ T, xiShiftedApertureHankelPairTerm y
        (P * Polynomial.ofFn (m + 1) x) (P * Polynomial.ofFn (m + 1) x) (target q)) =
      ∑ q ∈ T, ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * B i j q * x j by
        apply Finset.sum_congr rfl
        intro q _
        simpa only [B] using
          xiShiftedApertureHankelPairTerm_P_mul_ofFn_self y P (m + 1) x (target q)]
    simp only [dotProduct, Matrix.mulVec, G, Finset.mul_sum]
    have hdistrib (i j : Fin (m + 1)) :
        x i * ((∑ q ∈ T, B i j q) * x j) =
          ∑ q ∈ T, x i * B i j q * x j := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    simp_rw [hdistrib]
    conv_lhs =>
      enter [2, j]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hnegG0 : (-G0).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · exact hG0Herm.neg
    · intro x hx
      rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg]
      have hp : Polynomial.ofFn (m + 1) x ≠ 0 := by
        intro hp0
        apply hx
        apply Polynomial.injective_ofFn (m + 1)
        simpa only [Polynomial.ofFn_zero] using hp0
      let Q : Polynomial.degreeLT ℝ (m + 1) :=
        ⟨Polynomial.ofFn (m + 1) x, by
          apply Polynomial.mem_degreeLT.mpr
          exact (Polynomial.natDegree_lt_iff_degree_lt hp).mp
            (Polynomial.ofFn_natDegree_lt (Nat.succ_pos m) x)⟩
      have hQ : Q ≠ 0 := by
        intro hQ0
        apply hp
        exact congrArg Subtype.val hQ0
      have h := hneg Q hQ
      rw [← hquad_tsum x] at h
      linarith
  have hcompletionTendsto : Filter.Tendsto completion Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro S
    filter_upwards [Filter.eventually_ge_atTop S] with T hST
    exact hST.trans (hcompletion T)
  have htend : ∀ i j, Filter.Tendsto (fun T : Finset ι => (-(G (completion T))) i j)
      Filter.atTop (nhds ((-G0) i j)) := by
    intro i j
    have hs : Filter.Tendsto (fun T : Finset ι => ∑ q ∈ T, B i j q)
        Filter.atTop (nhds (∑' q, B i j q)) := (hsum i j).hasSum
    simpa only [Function.comp_apply, Matrix.neg_apply, G, G0] using
      (hs.comp hcompletionTendsto).neg
  have hevent := GaloisForLFunctions.HTGeometry.posDef_eventually_of_tendsto
    hnegG0 (Filter.Eventually.of_forall fun T => hGHerm (completion T)) htend
  obtain ⟨T, hT⟩ := hevent.exists
  refine ⟨T, fun Q hQ => ?_⟩
  have hQpoly : (Q : Polynomial ℝ) ≠ 0 := by
    intro hQ0
    apply hQ
    exact Subtype.ext hQ0
  have hQdeg : (Q : Polynomial ℝ).natDegree < m + 1 :=
    (Polynomial.natDegree_lt_iff_degree_lt hQpoly).mpr
      (Polynomial.mem_degreeLT.mp Q.property)
  let x : Fin (m + 1) → ℝ := Polynomial.toFn (m + 1) (Q : Polynomial ℝ)
  have hpof : Polynomial.ofFn (m + 1) x = (Q : Polynomial ℝ) :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hQdeg
  have hx : x ≠ 0 := by
    intro hx0
    apply hQpoly
    rw [← hpof, hx0, Polynomial.ofFn_zero]
  have hpos := hT.dotProduct_mulVec_pos hx
  rw [star_trivial, Matrix.neg_mulVec, dotProduct_neg, hquad_sum, hpof] at hpos
  linarith

/-- The unrestricted finite-witness theorem is the identity-completion specialization. -/
theorem exists_finset_xiFamily_negative_degreeLT_of_tsum_negative
    {ι : Type*} {m : ℕ} (y : ℝ) (P : Polynomial ℝ) (target : ι → XiZeroCopy)
    (hsum : ∀ i j : Fin (m + 1), Summable (fun q : ι =>
      xiShiftedApertureHankelPairTerm y
        (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) (target q)))
    (hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑' q : ι, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0) :
    ∃ T : Finset ι, ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ q ∈ T, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (target q)) < 0 := by
  simpa using exists_finsetCompletion_xiFamily_negative_degreeLT_of_tsum_negative
    y P target id (fun T => Finset.Subset.rfl) hsum hneg

/-- **Odd contact has a finite off-critical negative-index witness.**  Even when the off-critical
Xi divisor is infinite, one finite off-critical packet is already strictly negative on the entire
`(m+1)`-dimensional lifted null sector.  Its cardinality is therefore strictly greater than `m`.
This closes the diffuse-tail loophole and localizes every odd-contact index birth to finitely many
actual Xi copies. -/
theorem exists_offCritical_finset_liftedNullSubspace_neg_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    ∃ T : Finset ↥(({q : XiZeroCopy |
        (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
      m < T.card ∧
      ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
        (∑ q ∈ T, xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (q : XiZeroCopy)) < 0 := by
  classical
  let L : Set XiZeroCopy :=
    ({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hsum : ∀ i j : Fin (m + 1), Summable (fun q : L =>
      xiShiftedApertureHankelPairTerm y
        (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) (q : XiZeroCopy)) := by
    intro i j
    exact (summable_xiShiftedApertureHankelPairTerm hy
      (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ))).subtype L
  have hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑' q : L, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (q : XiZeroCopy)) < 0 := by
    intro Q hQ
    have hQpoly : (Q : Polynomial ℝ) ≠ 0 := by
      intro hz
      apply hQ
      exact Subtype.ext hz
    have hQdeg : (Q : Polynomial ℝ).natDegree ≤ m := by
      have hlt : (Q : Polynomial ℝ).natDegree < m + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hQpoly).mpr
          (Polynomial.mem_degreeLT.mp Q.property)
      omega
    simpa only [L, P] using offCritical_liftedNullSubspace_neg_of_odd_contact
      hy c hlast hzero S hline hcard (Q : Polynomial ℝ) hQpoly hQdeg
  obtain ⟨T, hT⟩ := exists_finset_xiFamily_negative_degreeLT_of_tsum_negative
    y P (fun q : L => (q : XiZeroCopy)) hsum hneg
  have hTcard' : m + 1 ≤ Fintype.card ↥T :=
    finite_xiFamily_negative_degreeLT_card y P
      (fun q : ↥T => ((q : L) : XiZeroCopy)) (fun Q hQ => by
        calc
          (∑ q : ↥T, xiShiftedApertureHankelPairTerm y
              (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (((q : ↥T) : L) : XiZeroCopy)) =
              ∑ q ∈ T.attach, xiShiftedApertureHankelPairTerm y
                (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                (((q : ↥T) : L) : XiZeroCopy) := by
                  rw [Finset.attach_eq_univ]
          _ = ∑ q ∈ T, xiShiftedApertureHankelPairTerm y
                (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                (q : XiZeroCopy) := Finset.sum_attach T (fun q : L =>
                  xiShiftedApertureHankelPairTerm y
                    (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                    (q : XiZeroCopy))
          _ < 0 := hT Q hQ)
  have hTcard : m + 1 ≤ T.card := by simpa using hTcard'
  refine ⟨T, by omega, ?_⟩
  simpa only [L, P] using hT

/-- **Odd contact forces finitely many distinct folded off-critical nodes.**  The finite witness can
be chosen so that its conjugation-folded shifted reciprocal-square support has more than `m`
distinct points.  This removes all false index supplied by multiplicity, FE--Schwarz quartet
duplication, or collisions between different zero orbits. -/
theorem exists_offCritical_finset_foldedNodes_neg_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    ∃ T : Finset ↥(({q : XiZeroCopy |
        (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
      m < (Finset.univ.image fun q : ↥T =>
        complexConjugationFold
          (xiShiftedReciprocalSquare y (((q : ↥T) :
            ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ)) :
              XiZeroCopy))).card ∧
      ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
        (∑ q ∈ T, xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (q : XiZeroCopy)) < 0 := by
  classical
  let L : Set XiZeroCopy :=
    ({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  obtain ⟨T, -, hT⟩ :=
    exists_offCritical_finset_liftedNullSubspace_neg_of_odd_contact
      hy c hlast hzero S hline hcard
  have hfold : m + 1 ≤ (Finset.univ.image fun q : ↥T =>
      complexConjugationFold
        (xiShiftedReciprocalSquare y (((q : ↥T) : L) : XiZeroCopy))).card :=
    finite_xiFamily_negative_degreeLT_foldedNode_card y P
      (fun q : ↥T => (((q : ↥T) : L) : XiZeroCopy)) (fun Q hQ => by
        calc
          (∑ q : ↥T, xiShiftedApertureHankelPairTerm y
              (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (((q : ↥T) : L) : XiZeroCopy)) =
              ∑ q ∈ T, xiShiftedApertureHankelPairTerm y
                (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                (q : XiZeroCopy) := Finset.sum_attach T (fun q : L =>
                  xiShiftedApertureHankelPairTerm y
                    (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                    (q : XiZeroCopy))
          _ < 0 := by simpa only [L, P] using hT Q hQ)
  refine ⟨T, ?_, ?_⟩
  · simpa only [L] using (show m < _ by omega)
  · simpa only [L, P] using hT

/-- **Symmetry-complete finite witness.**  Every odd Route-U contact has a finite witness obtained
as an explicit FE--Schwarz quartet completion.  That completed packet remains strictly negative on
the full lifted null sector and contains more than `m` distinct folded shifted nodes.  Finite
localization therefore respects all divisor symmetries; neither a diffuse tail nor asymmetric
truncation is responsible for the forced index. -/
theorem exists_offCritical_quartetCompletion_foldedNodes_neg_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    ∃ T : Finset XiOffCriticalCopy,
      let U := xiOffCriticalQuartetCompletion T
      m < (Finset.univ.image fun q : ↥U =>
        complexConjugationFold
          (xiShiftedReciprocalSquare y (((q : ↥U) : XiOffCriticalCopy) :
            XiZeroCopy))).card ∧
      ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
        (∑ q ∈ U, xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (q : XiZeroCopy)) < 0 := by
  classical
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hsum : ∀ i j : Fin (m + 1), Summable (fun q : XiOffCriticalCopy =>
      xiShiftedApertureHankelPairTerm y
        (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ)) (q : XiZeroCopy)) := by
    intro i j
    exact (summable_xiShiftedApertureHankelPairTerm hy
      (P * X ^ (i : ℕ)) (P * X ^ (j : ℕ))).subtype _
  have hneg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑' q : XiOffCriticalCopy, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (q : XiZeroCopy)) < 0 := by
    intro Q hQ
    have hQpoly : (Q : Polynomial ℝ) ≠ 0 := by
      intro hz
      apply hQ
      exact Subtype.ext hz
    have hQdeg : (Q : Polynomial ℝ).natDegree ≤ m := by
      have hlt : (Q : Polynomial ℝ).natDegree < m + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hQpoly).mpr
          (Polynomial.mem_degreeLT.mp Q.property)
      omega
    simpa only [XiOffCriticalCopy, P] using
      offCritical_liftedNullSubspace_neg_of_odd_contact
        hy c hlast hzero S hline hcard (Q : Polynomial ℝ) hQpoly hQdeg
  obtain ⟨T, hT⟩ :=
    exists_finsetCompletion_xiFamily_negative_degreeLT_of_tsum_negative
      y P (fun q : XiOffCriticalCopy => (q : XiZeroCopy))
        xiOffCriticalQuartetCompletion subset_xiOffCriticalQuartetCompletion hsum hneg
  let U := xiOffCriticalQuartetCompletion T
  have hfold : m + 1 ≤ (Finset.univ.image fun q : ↥U =>
      complexConjugationFold
        (xiShiftedReciprocalSquare y (((q : ↥U) : XiOffCriticalCopy) :
          XiZeroCopy))).card :=
    finite_xiFamily_negative_degreeLT_foldedNode_card y P
      (fun q : ↥U => (((q : ↥U) : XiOffCriticalCopy) : XiZeroCopy)) (fun Q hQ => by
        calc
          (∑ q : ↥U, xiShiftedApertureHankelPairTerm y
              (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
              (((q : ↥U) : XiOffCriticalCopy) : XiZeroCopy)) =
              ∑ q ∈ U, xiShiftedApertureHankelPairTerm y
                (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                (q : XiZeroCopy) := Finset.sum_attach U (fun q : XiOffCriticalCopy =>
                  xiShiftedApertureHankelPairTerm y
                    (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ))
                    (q : XiZeroCopy))
          _ < 0 := by simpa only [U] using hT Q hQ)
  refine ⟨T, ?_, ?_⟩
  · simpa only [U] using Nat.lt_of_succ_le hfold
  · simpa only [U, P] using hT

/-- **Adaptive-to-fixed-source orbit-rank bridge.**  A crossing at any positive shift in the source
window forces more than `m` distinct folded nodes already at fixed shift one, while the original
quartet-completed packet remains negative at the crossing shift.  Shift one is the corpus's
Cassini entire-source center, so the remaining index exclusion can be formulated on one fixed
prime--Gamma logarithmic derivative rather than on a moving divisor coordinate. -/
theorem exists_offCritical_cassiniFoldedNodes_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    ∃ T : Finset XiOffCriticalCopy,
      let U := xiOffCriticalQuartetCompletion T
      m < (Finset.univ.image fun q : ↥U =>
        complexConjugationFold
          (xiShiftedReciprocalSquare 1 (((q : ↥U) : XiOffCriticalCopy) :
            XiZeroCopy))).card ∧
      ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
        (∑ q ∈ U, xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (q : XiZeroCopy)) < 0 := by
  obtain ⟨T, hcardY, hneg⟩ :=
    exists_offCritical_quartetCompletion_foldedNodes_neg_of_odd_contact
      hy c hlast hzero S hline hcard
  let U := xiOffCriticalQuartetCompletion T
  have hshift :=
    card_univ_image_conjugationFold_xiShiftedReciprocalSquare_eq_shift
      hy.le (by norm_num : (0 : ℝ) ≤ 1)
      (fun q : ↥U => (((q : ↥U) : XiOffCriticalCopy) : XiZeroCopy))
  refine ⟨T, ?_, ?_⟩
  · rw [← hshift]
    simpa only [U] using hcardY
  · simpa only [U] using hneg

/-- Same fixed-source bridge in the corpus's intrinsic Cassini coordinate. -/
theorem exists_offCritical_cassiniCoordinateFoldedNodes_of_odd_contact
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card) :
    ∃ T : Finset XiOffCriticalCopy,
      let U := xiOffCriticalQuartetCompletion T
      m < (Finset.univ.image fun q : ↥U =>
        complexConjugationFold
          (xiSquaredSeamOneCoordinate (((q : ↥U) : XiOffCriticalCopy) :
            XiZeroCopy))).card ∧
      ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
        (∑ q ∈ U, xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (HTGeometry.finiteHankelNullMonicPolynomial c * (Q : Polynomial ℝ))
          (q : XiZeroCopy)) < 0 := by
  simpa only [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate] using
    exists_offCritical_cassiniFoldedNodes_of_odd_contact
      hy c hlast hzero S hline hcard

/-- **Intrinsic finite-support contact bound.** If a finite packet `T` contains every off-critical
Xi copy, odd contact order `2m+1` forces more than `m` distinct conjugation-folded shifted nodes in
`T`.  This is sharper than copy count: analytic multiplicity, all FE--Schwarz duplication, and
colliding zero orbits are removed before counting. -/
theorem oddContact_order_lt_offCriticalCover_foldedNode_card
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card)
    (T : Finset XiZeroCopy)
    (hcover : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → q ∈ T) :
    m < (T.image fun q =>
      complexConjugationFold (xiShiftedReciprocalSquare y q)).card := by
  classical
  let L : Set XiZeroCopy :=
    ({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ
  have hLfinite : L.Finite := by
    apply T.finite_toSet.subset
    intro q hq
    apply hcover q
    simpa only [L, Set.mem_compl_iff, Set.mem_setOf_eq] using hq
  letI : Fintype L := hLfinite.fintype
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  have hpacketNeg : ∀ Q : Polynomial.degreeLT ℝ (m + 1), Q ≠ 0 →
      (∑ q : L, xiShiftedApertureHankelPairTerm y
        (P * (Q : Polynomial ℝ)) (P * (Q : Polynomial ℝ)) (q : XiZeroCopy)) < 0 := by
    intro Q hQ
    have hQpoly : (Q : Polynomial ℝ) ≠ 0 := by
      intro hz
      apply hQ
      exact Subtype.ext hz
    have hQdeg : (Q : Polynomial ℝ).natDegree ≤ m := by
      have hlt : (Q : Polynomial ℝ).natDegree < m + 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hQpoly).mpr
          (Polynomial.mem_degreeLT.mp Q.property)
      omega
    have hneg := offCritical_liftedNullSubspace_neg_of_odd_contact
      hy c hlast hzero S hline hcard (Q : Polynomial ℝ) hQpoly hQdeg
    simpa only [L, P, tsum_fintype] using hneg
  have hindex : m + 1 ≤ (Finset.univ.image fun q : L =>
      complexConjugationFold
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))).card :=
    finite_xiFamily_negative_degreeLT_foldedNode_card y P
      (fun q : L => (q : XiZeroCopy)) hpacketNeg
  have himage : (Finset.univ.image fun q : L =>
      complexConjugationFold
        (xiShiftedReciprocalSquare y (q : XiZeroCopy))) ⊆
      T.image fun q => complexConjugationFold (xiShiftedReciprocalSquare y q) := by
    intro z hz
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨(q : XiZeroCopy), hcover q ?_, rfl⟩
    simpa only [L, Set.mem_compl_iff, Set.mem_setOf_eq] using q.property
  have hcardle := Finset.card_le_card himage
  omega

/-- Raw copy count follows from the stronger folded-node support bound. -/
theorem oddContact_order_lt_offCriticalCover_card
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card)
    (T : Finset XiZeroCopy)
    (hcover : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → q ∈ T) :
    m < T.card := by
  exact (oddContact_order_lt_offCriticalCover_foldedNode_card
    hy c hlast hzero S hline hcard T hcover).trans_le Finset.card_image_le

/-- **Finite off-critical support bounds contact order.** If a finite packet `T` contains every
off-critical Xi copy, odd contact order `2m+1` forces `m < 2|T|`.  Otherwise the product of the
real conjugate quadratics of all shifted off-critical atoms has degree at most `m`, lies in the
negative lifted sector, and simultaneously annihilates that entire sector—a contradiction. -/
theorem oddContact_order_lt_twice_offCriticalCover_card
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2)
    (hcard : n + m <
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card)
    (T : Finset XiZeroCopy)
    (hcover : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → q ∈ T) :
    m < 2 * T.card := by
  classical
  by_contra hm
  have htwice : 2 * T.card ≤ m := by omega
  let Q : Polynomial ℝ :=
    ∏ q ∈ T, HTGeometry.conjQuadratic (xiShiftedReciprocalSquare y q)
  have hQmonic : Q.Monic := by
    dsimp only [Q]
    exact Polynomial.monic_prod_of_monic T _
      (fun q _ => HTGeometry.conjQuadratic_monic (xiShiftedReciprocalSquare y q))
  have hQdegEq : Q.natDegree = 2 * T.card := by
    dsimp only [Q]
    rw [Polynomial.natDegree_prod T _ (fun q _ =>
      HTGeometry.conjQuadratic_ne_zero (xiShiftedReciprocalSquare y q))]
    simp only [HTGeometry.conjQuadratic_natDegree, Finset.sum_const_nat]
    omega
  have hQdeg : Q.natDegree ≤ m := by omega
  have hneg := offCritical_liftedNullSubspace_neg_of_odd_contact
    hy c hlast hzero S hline hcard Q hQmonic.ne_zero hQdeg
  have hzeroOff : ∀ q : ↥(({q : XiZeroCopy |
      (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
      xiShiftedApertureHankelPairTerm y
        (HTGeometry.finiteHankelNullMonicPolynomial c * Q)
        (HTGeometry.finiteHankelNullMonicPolynomial c * Q)
        (q : XiZeroCopy) = 0 := by
    intro q
    have hqoff : (((q : XiZeroCopy).1 : ℂ).re ≠ 1 / 2) := by
      simpa only [Set.mem_compl_iff, Set.mem_setOf_eq] using q.property
    have hqT := hcover (q : XiZeroCopy) hqoff
    have hQeval : evalRealPolynomial Q
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)) = 0 := by
      dsimp only [Q]
      rw [evalRealPolynomial]
      rw [Polynomial.map_prod, Polynomial.eval_prod]
      apply Finset.prod_eq_zero hqT
      change evalRealPolynomial
        (HTGeometry.conjQuadratic (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
        (xiShiftedReciprocalSquare y (q : XiZeroCopy)) = 0
      simpa only [evalRealPolynomial, Polynomial.aeval_def, Polynomial.eval_map] using
        HTGeometry.aeval_conjQuadratic (xiShiftedReciprocalSquare y (q : XiZeroCopy))
    rw [xiShiftedApertureHankelPairTerm, evalRealPolynomial_mul, hQeval]
    simp
  have hsumZero :
      (∑' q : ↥(({q : XiZeroCopy |
          (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
        xiShiftedApertureHankelPairTerm y
          (HTGeometry.finiteHankelNullMonicPolynomial c * Q)
          (HTGeometry.finiteHankelNullMonicPolynomial c * Q)
          (q : XiZeroCopy)) = 0 := by
    calc
      _ = ∑' _q : ↥(({q : XiZeroCopy |
          (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ), (0 : ℝ) :=
        tsum_congr hzeroOff
      _ = 0 := tsum_zero
  dsimp only at hneg
  rw [hsumZero] at hneg
  exact lt_irrefl 0 hneg

/-- **Critical-prefix escape/saturation law.**  Against every chosen finite critical-line prefix,
a genuine Route-U crossing has exactly two possible burdens.  Either its adaptive lifted degree is
at least the number of distinct prefix nodes, or the complementary divisor tail exactly cancels a
strictly positive prefix square and is strictly negative both in that null channel and in the
marked-`X` crossing channel.  This is the relative-tail form that survives the absolute monomial
tail no-go. -/
theorem exists_degreeEscape_or_criticalPrefixTail_doubleNegative_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2) :
    ∃ m : ℕ,
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m ∨
      let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
      (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y R R (q : XiZeroCopy)) =
        -(∑ q ∈ S, xiShiftedApertureHankelPairTerm y R R q) ∧
      (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y R R (q : XiZeroCopy)) < 0 ∧
      (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y R (X * R) (q : XiZeroCopy)) < 0 := by
  obtain ⟨m, hzeroPA, hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  refine ⟨m, ?_⟩
  by_cases hdegree :
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m
  · exact Or.inl hdegree
  right
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA k hk
  have hnull : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hvaluePA := primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroPA
  have hvalueXi := xiShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroXi
  have hnegativeXi : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) (X * R ^ 2) < 0 := by
    rw [← hvalueXi,
      xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax, hvaluePA]
    simpa only [R] using hnegativePA
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullX :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R (X * R) q) < 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    have hpoly : R * (X * R) = X * R ^ 2 := by ring
    rw [hpoly]
    exact hnegativeXi
  have hbulkSelf :
      0 < ∑ q ∈ S, xiShiftedApertureHankelPairTerm y R R q := by
    apply finite_criticalLine_bulk_hankelPair_self_pos hy.le S R hR.ne_zero hline
    rw [hRdeg]
    omega
  have hbulkX :
      0 ≤ ∑ q ∈ S, xiShiftedApertureHankelPairTerm y R (X * R) q :=
    finite_criticalLine_bulk_hankelPair_X_mul_nonneg hy.le S R hline
  have hsplitSelf :=
    (summable_xiShiftedApertureHankelPairTerm hy R R).sum_add_tsum_compl (s := S)
  have hsplitX :=
    (summable_xiShiftedApertureHankelPairTerm hy R (X * R)).sum_add_tsum_compl (s := S)
  rw [hfullSelf] at hsplitSelf
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- **Adaptive off-critical carrier at genuine contact.** Against every finite critical-line
prefix, a genuine crossing either escapes beyond its distinct-node count or its selected lifted
null reporter has strictly negative unmarked and marked energy on the off-critical divisor alone.
This removes every remaining critical-line atom from the negative carrier, not merely the chosen
finite prefix. -/
theorem exists_degreeEscape_or_offCritical_doubleNegative_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2) :
    ∃ m : ℕ,
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m ∨
      let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
      (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y R R (q : XiZeroCopy)) < 0 ∧
        (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y R (X * R) (q : XiZeroCopy)) < 0 := by
  obtain ⟨m, hzeroPA, hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  refine ⟨m, ?_⟩
  by_cases hdegree :
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m
  · exact Or.inl hdegree
  right
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA k hk
  have hnull : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hvaluePA := primeArchShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroPA
  have hvalueXi := xiShiftedHankelBoundaryPadeDefect_first_odd_eq_liftedShiftedSquare
    c hlast hzeroXi
  have hnegativeXi : HTGeometry.momentFunctional
      (fun k => (xiShiftedReciprocalMoment y k).re) (X * R ^ 2) < 0 := by
    rw [← hvalueXi,
      xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax, hvaluePA]
    simpa only [R] using hnegativePA
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullX :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R (X * R) q) < 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    have hpoly : R * (X * R) = X * R ^ 2 := by ring
    rw [hpoly]
    exact hnegativeXi
  apply offCritical_energy_doubleNegative_of_null_and_marked_negative
    hy R hR.ne_zero hfullSelf hfullX S hline
  rw [hRdeg]
  omega

/-- **Genuine-contact negative-index law.** Against every finite critical-line prefix, a genuine
crossing either has contact lift beyond the prefix's distinct-node count or forces the entire
`m+1` dimensional lifted space `P · Poly≤m` to be strictly negative on the off-critical divisor.
This is the index-amplified form of Route U's surviving obstruction. -/
theorem exists_degreeEscape_or_offCritical_liftedSubspace_neg_of_genuine_crossing
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (S : Finset XiZeroCopy)
    (hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2) :
    ∃ m : ℕ,
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m ∨
      ∀ (Q : Polynomial ℝ), Q ≠ 0 → Q.natDegree ≤ m →
        let A := HTGeometry.finiteHankelNullMonicPolynomial c * Q
        (∑' q : ↥(({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
          xiShiftedApertureHankelPairTerm y A A (q : XiZeroCopy)) < 0 := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  refine ⟨m, ?_⟩
  by_cases hdegree :
      (S.image fun q => (xiShiftedReciprocalSquare y q).re).card ≤ n + m
  · exact Or.inl hdegree
  right
  have hzeroXi : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA k hk
  intro Q hQ hQdeg
  exact offCritical_liftedNullSubspace_neg_of_odd_contact
    hy c hlast hzeroXi S hline (by omega) Q hQ hQdeg

/-! ### Polynomial-free Lagrange-capacity closure target -/

/-- **Route-U scalar-capacity reduction.**  A genuine two-sided crossing is impossible if, at
every possible lifted-null degree, one can select more distinct positive Xi nodes than that degree
whose complementary weighted Lagrange capacity is below one.  No bound in this hypothesis depends
on the adaptive null polynomial: all dependence has been compressed into the scalar Xi-node
capacity. -/
theorem no_genuine_crossing_of_compl_lagrangeCapacity_lt_one
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (hcapacity : ∀ m : ℕ,
      ∃ (k : ℕ) (x : Fin k → ℝ) (qcrit : Fin k → XiZeroCopy)
          (S : Finset XiZeroCopy),
        (∀ i, 0 < x i) ∧
        Function.Injective x ∧
        (∀ i, xiShiftedReciprocalSquare y (qcrit i) = (x i : ℂ)) ∧
        n + m < k ∧
        (∀ i, qcrit i ∈ S) ∧
        (∀ q ∈ S, ∃ t : ℝ, 0 < t ∧
          xiShiftedReciprocalSquare y q = (t : ℂ)) ∧
        (∑' q : ↥((↑S : Set XiZeroCopy)ᶜ),
          weightedLagrangeEvaluationCapacity x
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) : False := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  obtain ⟨k, x, qcrit, S, hx, hinj, hcoord, hk, hinclude, hpositive, hcap⟩ :=
    hcapacity m
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA j hj
  have hnull : HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullPositive :=
    full_xiShiftedHankelPair_tsum_pos_of_saturated_capacity_lt_one
      hy x qcrit hx hinj R hR.ne_zero (by simpa only [hRdeg] using hk)
        hcoord S hinclude hpositive hcap
  rw [hfullSelf] at hfullPositive
  exact lt_irrefl 0 hfullPositive

/-- **Route-U redundant-frame reduction.**  A genuine crossing is impossible if every possible
lifted degree admits a finite positive Xi sampling frame with enough distinct nodes and
polynomial-independent dual vectors that reconstruct all complementary atoms through that degree
with total weighted capacity below one.  Reflection and analytic multiplicity may repeat nodes in
the frame; they increase sampling energy rather than obstructing the criterion. -/
theorem no_genuine_crossing_of_redundantSamplingCapacity_lt_one
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (hcapacity : ∀ m : ℕ,
      ∃ (N : ℕ) (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy),
        (∀ i, 0 < x i) ∧
        Function.Injective qsample ∧
        (∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ)) ∧
        n + m < ((Finset.univ : Finset (Fin N)).image x).card ∧
        ∃ a : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
            Set XiZeroCopy)ᶜ) → Fin N → ℂ,
          (∀ q j, j ≤ n + m →
            ∑ i : Fin N, a q i * (x i : ℂ) ^ j =
              xiShiftedReciprocalSquare y (q : XiZeroCopy) ^ j) ∧
          Summable (fun q => weightedRedundantSamplingCapacity x (a q)
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) ∧
          (∑' q, weightedRedundantSamplingCapacity x (a q)
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) : False := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  obtain ⟨N, x, qsample, hx, hqinj, hcoord, hcard, a, hrepro,
      hcapSummable, hcap⟩ := hcapacity m
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA j hj
  have hnull : HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullPositive :=
    full_xiShiftedHankelPair_tsum_pos_of_redundantSamplingCapacity_lt_one
      (d := n + m) hy x qsample hx hqinj hcoord hcard R hR.ne_zero
        (by rw [hRdeg]) a hrepro hcapSummable hcap
  rw [hfullSelf] at hfullPositive
  exact lt_irrefl 0 hfullPositive

/-- **Canonical Route-U leverage reduction.** A genuine crossing is impossible if every adaptive
lifted degree admits a finite positive Xi packet with enough distinct reciprocal-square nodes whose
complement has summable subunit canonical inverse-Gram capacity.  Exact dual reconstruction is no
longer a hypothesis: finite weighted-frame strictness constructs it. -/
theorem no_genuine_crossing_of_canonicalRedundantSamplingCapacity_lt_one
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (hcapacity : ∀ m : ℕ,
      ∃ (N : ℕ) (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy),
        (∀ i, 0 < x i) ∧
        Function.Injective qsample ∧
        (∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ)) ∧
        n + m < ((Finset.univ : Finset (Fin N)).image x).card ∧
        Summable (fun q : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
            Set XiZeroCopy)ᶜ) =>
          weightedRedundantSamplingCapacity x
            (HTGeometry.canonicalMonomialReconstruction x (n + m + 1)
              (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) ∧
        (∑' q : ↥((↑((Finset.univ : Finset (Fin N)).image qsample) :
            Set XiZeroCopy)ᶜ),
          weightedRedundantSamplingCapacity x
            (HTGeometry.canonicalMonomialReconstruction x (n + m + 1)
              (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) : False := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  obtain ⟨N, x, qsample, hx, hqinj, hcoord, hcard,
      hcapSummable, hcap⟩ := hcapacity m
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA j hj
  have hnull : HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullPositive :=
    full_xiShiftedHankelPair_tsum_pos_of_canonicalRedundantSamplingCapacity_lt_one
      (d := n + m) hy x qsample hx hqinj hcoord hcard R hR.ne_zero
        (by rw [hRdeg]) hcapSummable hcap
  rw [hfullSelf] at hfullPositive
  exact lt_irrefl 0 hfullPositive

/-- **Route-U off-critical reduction at genuine contact.** Critical-line canonical capacity is not
part of the obstruction: at every adaptive lifted degree it is absorbed by a finite positive Xi
packet.  A genuine crossing can therefore survive only if the total off-critical canonical
capacity of every admissible base frame reaches at least one. -/
theorem no_genuine_crossing_of_offCriticalCanonicalCapacity_lt_one
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (hcapacity : ∀ m : ℕ,
      ∃ (N : ℕ) (x : Fin N → ℝ) (qbase : Fin N → XiZeroCopy),
        (∀ i, 0 < x i) ∧
        Function.Injective qbase ∧
        (∀ i, xiShiftedReciprocalSquare y (qbase i) = (x i : ℂ)) ∧
        (∀ i, ((qbase i).1 : ℂ).re = 1 / 2) ∧
        n + m < ((Finset.univ : Finset (Fin N)).image x).card ∧
        Summable (fun q : ↥(({q : XiZeroCopy |
            (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ) =>
          weightedRedundantSamplingCapacity x
            (HTGeometry.canonicalMonomialReconstruction x (n + m + 1)
              (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) ∧
        (∑' q : ↥(({q : XiZeroCopy |
            (q.1 : ℂ).re = 1 / 2} : Set XiZeroCopy)ᶜ),
          weightedRedundantSamplingCapacity x
            (HTGeometry.canonicalMonomialReconstruction x (n + m + 1)
              (xiShiftedReciprocalSquare y (q : XiZeroCopy)))
            (xiShiftedReciprocalSquare y (q : XiZeroCopy))) < 1) : False := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  obtain ⟨N, x, qbase, hx, hqinj, hcoord, hqline, hcard,
      hoffSummable, hoff⟩ := hcapacity m
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA j hj
  have hnull : HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullPositive :=
    full_xiShiftedHankelPair_tsum_pos_of_offCriticalCanonicalCapacity_lt_one
      (d := n + m) hy x qbase hx hqinj hcoord hqline hcard R hR.ne_zero
        (by rw [hRdeg]) hoffSummable hoff
  rw [hfullSelf] at hfullPositive
  exact lt_irrefl 0 hfullPositive

/-- **Route-U relative-trace reduction.** A genuine crossing is impossible if every adaptive lifted
degree admits a positive Xi packet with enough distinct nodes and a uniform subunit inverse-Gram
trace bound on every finite complementary packet.  This is polynomial-free, dual-free, and removes
infinite summability from the hypothesis. -/
theorem no_genuine_crossing_of_uniformFiniteCanonicalCapacityTrace_lt_one
    {y : ℝ} (hy : 0 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef)
    (hcapacity : ∀ m : ℕ,
      ∃ (N : ℕ) (x : Fin N → ℝ) (qsample : Fin N → XiZeroCopy) (C : ℝ),
        (∀ i, 0 < x i) ∧
        Function.Injective qsample ∧
        (∀ i, xiShiftedReciprocalSquare y (qsample i) = (x i : ℂ)) ∧
        n + m < ((Finset.univ : Finset (Fin N)).image x).card ∧
        C < 1 ∧
        XiCanonicalComplementTraceBound x qsample y (n + m + 1) C) : False := by
  obtain ⟨m, hzeroPA, _hnegativePA⟩ :=
    exists_negative_primeArchShifted_liftedShiftedSquare_of_genuine_crossing
      hy hymax c hhead hc hlast hright hleft
  obtain ⟨N, x, qsample, C, hx, hqinj, hcoord, hcard, hC, htrace⟩ := hcapacity m
  let R := HTGeometry.finiteHankelNullMonicPolynomial c * X ^ m
  have hP := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hR : R.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hRdeg : R.natDegree = n + m := by
    dsimp only [R]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m),
      HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast,
      Polynomial.natDegree_X_pow]
  have hzeroXi : ∀ j < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c j = 0 := by
    intro j hj
    rw [xiShiftedHankelBoundaryPadeDefect_eq_primeArch hy.le hymax]
    exact hzeroPA j hj
  have hnull : HTGeometry.momentFunctional
      (fun j => (xiShiftedReciprocalMoment y j).re) (R ^ 2) = 0 := by
    simpa only [R] using
      momentFunctional_liftedNullSquare_eq_zero_of_odd_contact c hlast hzeroXi
  have hfullSelf :
      (∑' q : XiZeroCopy, xiShiftedApertureHankelPairTerm y R R q) = 0 := by
    rw [← xiShiftedAperturePairGap_eq_tsum_hankelPairTerm hy,
      xiShiftedAperturePairGap_eq_momentInner hy, HTGeometry.momentInner_def]
    simpa only [pow_two] using hnull
  have hfullPositive :=
    full_xiShiftedHankelPair_tsum_pos_of_uniformFiniteCanonicalCapacityTrace_lt_one
      (d := n + m) hy x qsample hx hqinj hcoord hcard R hR.ne_zero
        (by rw [hRdeg]) C hC htrace
  rw [hfullSelf] at hfullPositive
  exact lt_irrefl 0 hfullPositive

end

end RHTower
