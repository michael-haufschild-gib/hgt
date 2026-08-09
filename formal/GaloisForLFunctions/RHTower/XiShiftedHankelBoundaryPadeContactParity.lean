import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryPadeContactParity
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass

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

end

end RHTower
