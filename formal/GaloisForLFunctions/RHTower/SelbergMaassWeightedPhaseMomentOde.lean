import GaloisForLFunctions.RHTower.SelbergMaassWeightedPhaseKernel

/-!
# Finite Maass moments for the weighted phase current

The denominator-free weighted phase current contains the polynomial tail weight
`(m + n)^(2 : ℕ)`.  This module packages finite coefficient moments and proves their
literal Maass ODE.  In particular, the squared-frequency moment is the second
height derivative of the zeroth moment up to the common eigenvalue potential.
This is the exact bridge needed to couple the derivative and tail terms in the
off-diagonal phase current.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassWeightedPhaseMomentOde
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace
open SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks SelbergMaassCharacterProjection
  SelbergMaassCharacterFourier SelbergMaassInversionGram SelbergMaassUnipotentFourier
  SelbergMaassCharacterGradient SelbergMaassFourier SelbergMaassMixedLoss
  SelbergMaassSliceRigidity SelbergMaassKernelWronskian
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- A finite complex-weighted sum of literal original coefficient vectors. -/
def finiteCoefficientMoment (I : Finset ℤ) (a : ℤ → ℂ) (y : ℝ) :
    EuclideanSpace ℂ (Deck N) :=
  ∑ n ∈ I, a n • coefficientVector N f n y

/-- The height derivative of a finite coefficient moment, before using the modal ODE. -/
def finiteCoefficientHeightMoment (I : Finset ℤ) (a : ℤ → ℂ) (y : ℝ) :
    EuclideanSpace ℂ (Deck N) :=
  ∑ n ∈ I, a n • coefficientHeightVector N f n y

/-- Finite coefficient moments differentiate termwise into their literal height moments. -/
theorem finiteCoefficientMoment_hasDerivAt (I : Finset ℤ) (a : ℤ → ℂ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (finiteCoefficientMoment N f I a)
      (finiteCoefficientHeightMoment N f I a y) y := by
  have hfun : finiteCoefficientMoment N f I a =
      ∑ n ∈ I, a n • coefficientVector N f n := by
    funext t
    simp [finiteCoefficientMoment]
  rw [hfun]
  unfold finiteCoefficientHeightMoment
  exact HasDerivAt.sum (fun n hn =>
    (coefficientVector_hasDerivAt N f n hy).const_smul (a n))

/-- Finite height moments differentiate termwise using the literal modal potential. -/
theorem finiteCoefficientHeightMoment_hasDerivAt (I : Finset ℤ) (a : ℤ → ℂ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (finiteCoefficientHeightMoment N f I a)
      (∑ n ∈ I, a n •
        (((signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) - lam / y ^ (2 : ℕ) : ℝ) : ℂ) •
          coefficientVector N f n y)) y := by
  have hfun : finiteCoefficientHeightMoment N f I a =
      ∑ n ∈ I, a n • coefficientHeightVector N f n := by
    funext t
    simp [finiteCoefficientHeightMoment]
  rw [hfun]
  exact HasDerivAt.sum (fun n hn =>
    (coefficientHeightVector_hasDerivAt N f n hy).const_smul (a n))

/-- The finite zeroth coefficient moment. -/
def finiteZerothMoment (I : Finset ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  finiteCoefficientMoment N f I (fun _ => 1) y

/-- The finite moment with literal squared Fourier-index weight. -/
def finiteFrequencySquareMoment (I : Finset ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  finiteCoefficientMoment N f I (fun n => ((n ^ (2 : ℕ) : ℤ) : ℂ)) y

/-- The zeroth finite moment obeys the summed Maass equation. -/
theorem finiteZerothHeightMoment_hasDerivAt (I : Finset ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (finiteCoefficientHeightMoment N f I (fun _ => 1))
      (((2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) : ℂ) •
          finiteFrequencySquareMoment N f I y -
        ((lam / y ^ (2 : ℕ) : ℝ) : ℂ) • finiteZerothMoment N f I y) y := by
  have h := finiteCoefficientHeightMoment_hasDerivAt N f I (fun _ => 1) hy
  convert h using 1
  unfold finiteFrequencySquareMoment finiteZerothMoment finiteCoefficientMoment
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [one_smul, smul_smul]
  rw [← sub_smul]
  congr 1
  unfold signedFrequency
  push_cast
  ring

/-- The finite quadratic form of the literal tail Gram kernel. -/
def tailLossQuadratic (r s : ZMod (N + 1)) (I : Finset ℤ) (a : ℤ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ I, ∑ m ∈ I, (starRingEnd ℂ) (a n) * a m * tailLoss N r s f n m Y

/-- The full `(m + n)^(2 : ℕ)` tail weight is the polarization of the zeroth,
first, and squared-frequency coefficient Gram forms. -/
theorem tailLoss_squareWeight_polarization (r s : ZMod (N + 1)) (I : Finset ℤ)
    (Y : ℝ) :
    (∑ n ∈ I, ∑ m ∈ I,
      (((m + n : ℤ) : ℂ) ^ (2 : ℕ)) * tailLoss N r s f n m Y) =
      (1 / 2 : ℂ) *
        (tailLossQuadratic N f r s I (fun n => 1 + ((n ^ (2 : ℕ) : ℤ) : ℂ)) Y -
          tailLossQuadratic N f r s I (fun n => 1 - ((n ^ (2 : ℕ) : ℤ) : ℂ)) Y) +
        2 * tailLossQuadratic N f r s I (fun n => (n : ℂ)) Y := by
  unfold tailLossQuadratic
  rw [mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_add, map_sub, map_one, map_intCast]
  push_cast
  ring

private theorem complexLoss_hasDerivAt_moment {r s : ZMod (N + 1)}
    {u v : ℝ → EuclideanSpace ℂ (Deck N)}
    {u' v' : EuclideanSpace ℂ (Deck N)} {y : ℝ}
    (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun t => complexLoss N r s (u t) (v t))
      (complexLoss N r s (u y) v' + complexLoss N r s u' (v y)) y := by
  let T := (inversionTransfer N r s).toContinuousLinearMap.restrictScalars ℝ
  have h := (hu.inner ℂ hv).sub
    ((T.hasFDerivAt.comp_hasDerivAt y hu).inner ℂ (T.hasFDerivAt.comp_hasDerivAt y hv))
  convert h using 1 <;> try rfl
  simp only [complexLoss]
  dsimp [T]
  ring

/-- The finite transfer-loss current pairing the zeroth moment with its height derivative. -/
def finiteZerothMomentCurrent (r s : ZMod (N + 1)) (I : Finset ℤ) (y : ℝ) : ℂ :=
  complexLoss N r s (finiteZerothMoment N f I y)
    (finiteCoefficientHeightMoment N f I (fun _ => 1) y)

/-- The moment-current derivative couples the signed squared-frequency cross moment to
nonnegative zeroth- and first-height transfer energies. -/
theorem finiteZerothMomentCurrent_re_hasDerivAt (r s : ZMod (N + 1)) (I : Finset ℤ)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => (finiteZerothMomentCurrent N f r s I t).re)
      (lossEnergy N r s (finiteCoefficientHeightMoment N f I (fun _ => 1) y) +
        (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) *
          (complexLoss N r s (finiteZerothMoment N f I y)
            (finiteFrequencySquareMoment N f I y)).re -
        (lam / y ^ (2 : ℕ)) * lossEnergy N r s (finiteZerothMoment N f I y)) y := by
  have hu := finiteCoefficientMoment_hasDerivAt N f I (fun _ => 1) hy
  have hv := finiteZerothHeightMoment_hasDerivAt N f I hy
  have h := complexLoss_hasDerivAt_moment (N := N) (r := r) (s := s) hu hv
  have hre : HasDerivAt (fun t =>
      (complexLoss N r s (finiteZerothMoment N f I t)
        (finiteCoefficientHeightMoment N f I (fun _ => 1) t)).re)
      (complexLoss N r s (finiteZerothMoment N f I y)
        (((2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) : ℂ) •
          finiteFrequencySquareMoment N f I y -
          ((lam / y ^ (2 : ℕ) : ℝ) : ℂ) • finiteZerothMoment N f I y) +
        complexLoss N r s (finiteCoefficientHeightMoment N f I (fun _ => 1) y)
          (finiteCoefficientHeightMoment N f I (fun _ => 1) y)).re y :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h
  have hsmul (a : ℂ) (v w : EuclideanSpace ℂ (Deck N)) :
      complexLoss N r s v (a • w) = a * complexLoss N r s v w := by
    simp only [complexLoss, map_smul, inner_smul_right, mul_sub]
  have hsub (v w z : EuclideanSpace ℂ (Deck N)) :
      complexLoss N r s v (w - z) =
        complexLoss N r s v w - complexLoss N r s v z := by
    unfold complexLoss
    simp only [map_sub, inner_sub_right]
    ring
  have hvalue :
      (complexLoss N r s (finiteZerothMoment N f I y)
        (((2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) : ℂ) •
          finiteFrequencySquareMoment N f I y -
          ((lam / y ^ (2 : ℕ) : ℝ) : ℂ) • finiteZerothMoment N f I y) +
        complexLoss N r s (finiteCoefficientHeightMoment N f I (fun _ => 1) y)
          (finiteCoefficientHeightMoment N f I (fun _ => 1) y)).re =
      lossEnergy N r s (finiteCoefficientHeightMoment N f I (fun _ => 1) y) +
        (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) *
          (complexLoss N r s (finiteZerothMoment N f I y)
            (finiteFrequencySquareMoment N f I y)).re -
        (lam / y ^ (2 : ℕ)) * lossEnergy N r s (finiteZerothMoment N f I y) := by
    rw [hsub, hsmul, hsmul, complexLoss_self, complexLoss_self]
    have hc :
        (2 * (Real.pi : ℂ) / (((N + 1 : ℕ) : ℝ) : ℂ)) ^ (2 : ℕ) =
          (((2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc]
    simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hvalue] at hre
  exact hre

private theorem moment_complexLoss_norm_le (N : ℕ) (r s : ZMod (N + 1))
    (v w : EuclideanSpace ℂ (Deck N)) :
    ‖complexLoss N r s v w‖ ≤ ‖v‖^(2 : ℕ) + ‖w‖^(2 : ℕ) := by
  have ht (a : EuclideanSpace ℂ (Deck N)) : ‖inversionTransfer N r s a‖ ≤ ‖a‖ := by
    have h := lossEnergy_nonneg N r s a
    unfold lossEnergy at h
    nlinarith [norm_nonneg a, norm_nonneg (inversionTransfer N r s a)]
  calc
    _ ≤ ‖inner ℂ v w‖ + ‖inner ℂ (inversionTransfer N r s v)
        (inversionTransfer N r s w)‖ := norm_sub_le _ _
    _ ≤ ‖v‖ * ‖w‖ + ‖inversionTransfer N r s v‖ * ‖inversionTransfer N r s w‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ :=
      add_le_add_right (mul_le_mul (ht v) (ht w) (norm_nonneg _) (norm_nonneg _)) _
    _ ≤ _ := by nlinarith [sq_nonneg (‖v‖ - ‖w‖)]

section ExceptionalTail

variable (e : Ioo (0 : ℝ) (1 / 4))
  (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))

private theorem moment_coefficient_norm_integrable (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖coefficientVector N g n y‖^(2 : ℕ)) (Ioi Y) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Deck N))
    (fun q _ => SelbergMaassBessel.mode_mass_integrable N e (quotientForm N g q) n hY)
  have he : (fun y => ‖coefficientVector N g n y‖^(2 : ℕ)) =
      fun y => ∑ q : Deck N, normSq (maassCoefficient N (quotientForm N g q) n y) := by
    funext y
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm, coefficientVector, WithLp.ofLp_toLp]
  rw [he]
  exact h

private theorem moment_height_norm_integrable (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖coefficientHeightVector N g n y‖^(2 : ℕ)) (Ioi Y) := by
  have h := integrable_finsetSum (Finset.univ : Finset (Deck N))
    (fun q _ => SelbergMaassBessel.mode_deriv_integrable N e (quotientForm N g q) n hY)
  have he : (fun y => ‖coefficientHeightVector N g n y‖^(2 : ℕ)) =
      fun y => ∑ q : Deck N, normSq (deriv (maassCoefficient N (quotientForm N g q) n) y) := by
    funext y
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm, coefficientHeightVector, WithLp.ofLp_toLp]
  rw [he]
  exact h

private theorem moment_loss_integrable (r s : ZMod (N + 1))
    {u v : ℝ → EuclideanSpace ℂ (Deck N)} {Y : ℝ}
    (hu : ContinuousOn u (Ioi Y)) (hv : ContinuousOn v (Ioi Y))
    (hiu : IntegrableOn (fun y => ‖u y‖^(2 : ℕ)) (Ioi Y))
    (hiv : IntegrableOn (fun y => ‖v y‖^(2 : ℕ)) (Ioi Y)) :
    IntegrableOn (fun y => complexLoss N r s (u y) (v y)) (Ioi Y) := by
  let T := (inversionTransfer N r s).toContinuousLinearMap
  have hc : ContinuousOn (fun y => complexLoss N r s (u y) (v y)) (Ioi Y) :=
    (hu.inner hv).sub ((T.continuous.comp_continuousOn hu).inner
      (T.continuous.comp_continuousOn hv))
  exact (hiu.add hiv).mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    (Filter.Eventually.of_forall (fun y => moment_complexLoss_norm_le N r s (u y) (v y)))

private theorem moment_coefficient_continuous {Y : ℝ} (hY : 0 < Y) (n : ℤ) :
    ContinuousOn (coefficientVector N g n) (Ioi Y) := fun _ hy =>
  (coefficientVector_hasDerivAt N g n (hY.trans hy)).continuousAt.continuousWithinAt

private theorem moment_height_continuous {Y : ℝ} (hY : 0 < Y) (n : ℤ) :
    ContinuousOn (coefficientHeightVector N g n) (Ioi Y) := fun _ hy =>
  (coefficientHeightVector_hasDerivAt N g n (hY.trans hy)).continuousAt.continuousWithinAt

private theorem moment_coefficient_height_loss_integrable (r s : ZMod (N + 1))
    (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => complexLoss N r s (coefficientVector N g n y)
      (coefficientHeightVector N g m y)) (Ioi Y) :=
  moment_loss_integrable N r s (moment_coefficient_continuous N e g hY n)
    (moment_height_continuous N e g hY m)
    (moment_coefficient_norm_integrable N e g n hY)
    (moment_height_norm_integrable N e g m hY)

private theorem finiteZerothMomentCurrent_eq_sum (r s : ZMod (N + 1)) (I : Finset ℤ) (y : ℝ) :
    finiteZerothMomentCurrent N g r s I y =
      ∑ n ∈ I, ∑ m ∈ I,
        complexLoss N r s (coefficientVector N g n y) (coefficientHeightVector N g m y) := by
  unfold finiteZerothMomentCurrent finiteZerothMoment finiteCoefficientMoment finiteCoefficientHeightMoment
  conv_rhs => rw [Finset.sum_comm]
  simp only [one_smul, complexLoss, map_sum, sum_inner, inner_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_sub_distrib]

/-- The finite zeroth moment current has a genuine absolutely integrable cusp tail. -/
theorem finiteZerothMomentCurrent_integrable (r s : ZMod (N + 1)) (I : Finset ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (finiteZerothMomentCurrent N g r s I) (Ioi Y) := by
  rw [show finiteZerothMomentCurrent N g r s I =
      fun y => ∑ n ∈ I, ∑ m ∈ I,
        complexLoss N r s (coefficientVector N g n y) (coefficientHeightVector N g m y) by
    funext y
    exact finiteZerothMomentCurrent_eq_sum N e g r s I y]
  exact integrable_finsetSum I (fun n _ =>
    integrable_finsetSum I (fun m _ =>
      moment_coefficient_height_loss_integrable N e g r s n m hY))

private theorem moment_coefficient_loss_integrable (r s : ZMod (N + 1))
    (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => complexLoss N r s (coefficientVector N g n y)
      (coefficientVector N g m y)) (Ioi Y) :=
  moment_loss_integrable N r s (moment_coefficient_continuous N e g hY n)
    (moment_coefficient_continuous N e g hY m)
    (moment_coefficient_norm_integrable N e g n hY)
    (moment_coefficient_norm_integrable N e g m hY)

private theorem moment_height_loss_integrable (r s : ZMod (N + 1))
    (n m : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => complexLoss N r s (coefficientHeightVector N g n y)
      (coefficientHeightVector N g m y)) (Ioi Y) :=
  moment_loss_integrable N r s (moment_height_continuous N e g hY n)
    (moment_height_continuous N e g hY m)
    (moment_height_norm_integrable N e g n hY)
    (moment_height_norm_integrable N e g m hY)

private theorem moment_complexLoss_bisum {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (r s : ZMod (N + 1)) (a : ι → ℂ) (b : κ → ℂ)
    (u : ι → EuclideanSpace ℂ (Deck N))
    (v : κ → EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s (∑ i ∈ I, a i • u i) (∑ j ∈ J, b j • v j) =
      ∑ i ∈ I, ∑ j ∈ J,
        (starRingEnd ℂ) (a i) * b j * complexLoss N r s (u i) (v j) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [complexLoss, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem finiteMoment_loss_integrable (r s : ZMod (N + 1)) (I : Finset ℤ)
    (a b : ℤ → ℂ) (u v : ℤ → ℝ → EuclideanSpace ℂ (Deck N)) {Y : ℝ}
    (hbase : ∀ n m : ℤ, IntegrableOn (fun y => complexLoss N r s (u n y) (v m y)) (Ioi Y)) :
    IntegrableOn (fun y => complexLoss N r s
      (∑ n ∈ I, a n • u n y) (∑ m ∈ I, b m • v m y)) (Ioi Y) := by
  rw [show (fun y => complexLoss N r s
      (∑ n ∈ I, a n • u n y) (∑ m ∈ I, b m • v m y)) =
      fun y => ∑ n ∈ I, ∑ m ∈ I,
        (starRingEnd ℂ) (a n) * b m * complexLoss N r s (u n y) (v m y) by
    funext y
    exact moment_complexLoss_bisum N I I r s a b (fun n => u n y) (fun m => v m y)]
  exact integrable_finsetSum I (fun n _ => integrable_finsetSum I (fun m _ =>
    (hbase n m).const_mul ((starRingEnd ℂ) (a n) * b m)))

private theorem finiteCoefficientMoment_loss_integrable (r s : ZMod (N + 1))
    (I : Finset ℤ) (a b : ℤ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => complexLoss N r s
      (finiteCoefficientMoment N g I a y) (finiteCoefficientMoment N g I b y)) (Ioi Y) := by
  unfold finiteCoefficientMoment
  exact finiteMoment_loss_integrable N r s I a b (coefficientVector N g) (coefficientVector N g)
    (fun n m => moment_coefficient_loss_integrable N e g r s n m hY)

private theorem finiteCoefficientHeightMoment_loss_integrable (r s : ZMod (N + 1))
    (I : Finset ℤ) (a b : ℤ → ℂ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => complexLoss N r s
      (finiteCoefficientHeightMoment N g I a y)
      (finiteCoefficientHeightMoment N g I b y)) (Ioi Y) := by
  unfold finiteCoefficientHeightMoment
  exact finiteMoment_loss_integrable N r s I a b (coefficientHeightVector N g)
    (coefficientHeightVector N g)
    (fun n m => moment_height_loss_integrable N e g r s n m hY)

private theorem inverseSquare_mul_integrable {c Y : ℝ} (hY : 0 < Y) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ioi Y)) :
    IntegrableOn (fun y => (c / y^(2 : ℕ)) * F y) (Ioi Y) := by
  refine hF.bdd_mul (c := |c| / Y^(2 : ℕ)) ?_ ?_
  · exact (continuousOn_const.div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hY.trans hy)))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos (hY.trans hy))]
    have hsq : Y^(2 : ℕ) ≤ y^(2 : ℕ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hy))
        (add_nonneg (le_of_lt hY) (le_of_lt (hY.trans hy)))]
    exact div_le_div_of_nonneg_left (abs_nonneg c) (sq_pos_of_pos hY) hsq

/-- The exact derivative in the finite zeroth-current identity is integrable on every cusp tail. -/
theorem finiteZerothMomentCurrent_re_deriv_integrable (r s : ZMod (N + 1)) (I : Finset ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y =>
      lossEnergy N r s (finiteCoefficientHeightMoment N g I (fun _ => 1) y) +
        (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) *
          (complexLoss N r s (finiteZerothMoment N g I y)
            (finiteFrequencySquareMoment N g I y)).re -
        ((e : ℝ) / y ^ (2 : ℕ)) * lossEnergy N r s (finiteZerothMoment N g I y)) (Ioi Y) := by
  have hheight0 := finiteCoefficientHeightMoment_loss_integrable N e g r s I
    (fun _ => 1) (fun _ => 1) hY
  have hheight : IntegrableOn (fun y =>
      lossEnergy N r s (finiteCoefficientHeightMoment N g I (fun _ => 1) y)) (Ioi Y) := by
    rw [show (fun y => complexLoss N r s
        (finiteCoefficientHeightMoment N g I (fun _ => 1) y)
        (finiteCoefficientHeightMoment N g I (fun _ => 1) y)) =
        fun y => (lossEnergy N r s (finiteCoefficientHeightMoment N g I (fun _ => 1) y) : ℂ) by
      funext y
      rw [complexLoss_self]] at hheight0
    change Integrable (fun y => lossEnergy N r s
      (finiteCoefficientHeightMoment N g I (fun _ => 1) y)) (volume.restrict (Ioi Y))
    have hr := hheight0.re
    change Integrable (fun y => RCLike.re ((lossEnergy N r s
      (finiteCoefficientHeightMoment N g I (fun _ => 1) y) : ℂ))) (volume.restrict (Ioi Y)) at hr
    simpa using hr
  have hcross0 := finiteCoefficientMoment_loss_integrable N e g r s I
    (fun _ => 1) (fun n => ((n ^ (2 : ℕ) : ℤ) : ℂ)) hY
  have hcross : IntegrableOn (fun y =>
      (complexLoss N r s (finiteZerothMoment N g I y)
        (finiteFrequencySquareMoment N g I y)).re) (Ioi Y) := by
    change IntegrableOn (fun y => (complexLoss N r s
      (finiteCoefficientMoment N g I (fun _ => 1) y)
      (finiteCoefficientMoment N g I (fun n => ((n ^ (2 : ℕ) : ℤ) : ℂ)) y)).re) (Ioi Y)
    exact hcross0.re
  have hzero0 := finiteCoefficientMoment_loss_integrable N e g r s I
    (fun _ => 1) (fun _ => 1) hY
  have hzero : IntegrableOn (fun y =>
      lossEnergy N r s (finiteZerothMoment N g I y)) (Ioi Y) := by
    rw [show (fun y => complexLoss N r s
        (finiteCoefficientMoment N g I (fun _ => 1) y)
        (finiteCoefficientMoment N g I (fun _ => 1) y)) =
        fun y => (lossEnergy N r s (finiteCoefficientMoment N g I (fun _ => 1) y) : ℂ) by
      funext y
      rw [complexLoss_self]] at hzero0
    change Integrable (fun y => lossEnergy N r s
      (finiteCoefficientMoment N g I (fun _ => 1) y)) (volume.restrict (Ioi Y))
    have hr := hzero0.re
    change Integrable (fun y => RCLike.re ((lossEnergy N r s
      (finiteCoefficientMoment N g I (fun _ => 1) y) : ℂ))) (volume.restrict (Ioi Y)) at hr
    simpa using hr
  exact (hheight.add (hcross.const_mul ((2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ)))).sub
    (inverseSquare_mul_integrable (c := (e : ℝ)) hY _ hzero)

/-- The finite zeroth current has vanishing real boundary value at the cusp. -/
theorem finiteZerothMomentCurrent_re_tendsto_zero (r s : ZMod (N + 1)) (I : Finset ℤ) :
    Tendsto (fun y => (finiteZerothMomentCurrent N g r s I y).re) atTop (nhds 0) := by
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
  · intro y hy
    exact finiteZerothMomentCurrent_re_hasDerivAt N g r s I (lt_trans zero_lt_one hy)
  · exact finiteZerothMomentCurrent_re_deriv_integrable N e g r s I zero_lt_one
  · exact (finiteZerothMomentCurrent_integrable N e g r s I zero_lt_one).re

/-- The finite zeroth phase current equals the negative integral of its exact cusp-tail source. -/
theorem finiteZerothMomentCurrent_re_eq_neg_integral_tail (r s : ZMod (N + 1)) (I : Finset ℤ)
    {Y : ℝ} (hY : 0 < Y) :
    (finiteZerothMomentCurrent N g r s I Y).re = -∫ y in Ioi Y,
      lossEnergy N r s (finiteCoefficientHeightMoment N g I (fun _ => 1) y) +
        (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ (2 : ℕ) *
          (complexLoss N r s (finiteZerothMoment N g I y)
            (finiteFrequencySquareMoment N g I y)).re -
        ((e : ℝ) / y ^ (2 : ℕ)) * lossEnergy N r s (finiteZerothMoment N g I y) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => finiteZerothMomentCurrent_re_hasDerivAt N g r s I (hY.trans_le hy))
    (finiteZerothMomentCurrent_re_deriv_integrable N e g r s I hY)
    (finiteZerothMomentCurrent_re_tendsto_zero N e g r s I)
  linarith

end ExceptionalTail

end
end GaloisForLFunctions.RHTower.SelbergMaassWeightedPhaseMomentOde
