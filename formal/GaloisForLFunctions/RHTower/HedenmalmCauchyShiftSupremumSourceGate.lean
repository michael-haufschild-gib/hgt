import GaloisForLFunctions.RHTower.XiCenteredRealShiftCauchyPairExactCorrection

/-!
# Predetermined Cauchy-shift supremum gate for a finite height fibre

The reciprocal source shifts `eps_n = 1/(n+1)` require no zero spacing.  On a finite packet of
distinct transverse locations, their positive Cauchy pair covariances increase to exact ordered
off-diagonal multiplicity mass.  Therefore a quantitative ceiling for that collision-free mass is
equivalent to one uniform ceiling over all predetermined finite shifts.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Cauchy pair covariance on a finite transverse packet at predetermined reciprocal shift. -/
def finiteCauchyShiftFibreCovariance {ι : Type*}
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ s.product s,
    m p.1 * m p.2 *
      cauchyPairSaturation (1 / ((n : ℝ) + 1)) (x p.1 - x p.2)

/-- Exact ordered mass of pairs at distinct transverse support locations. -/
def finiteFibreOrderedOffDiagonalMass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ι → ℝ) : ℝ :=
  ∑ p ∈ s.product s, if p.1 = p.2 then 0 else m p.1 * m p.2

/-- Ordered multiplicity mass of distinct transverse pairs closer than `delta`. -/
def finiteFibreOrderedClosePairMass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (delta : ℝ) : ℝ :=
  ∑ p ∈ s.product s,
    if p.1 = p.2 then 0 else
      if |x p.1 - x p.2| < delta then m p.1 * m p.2 else 0

private theorem one_sub_cauchyPairSaturation_eq
    (eps d : ℝ) (heps : eps ≠ 0) :
    1 - cauchyPairSaturation eps d =
      eps ^ 2 / (d ^ 2 + eps ^ 2) := by
  rw [cauchyPairSaturation]
  have hden : d ^ 2 + eps ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero heps, sq_nonneg d]
  field_simp [hden]
  ring

/-- Shrinking the predetermined reciprocal shift increases every Cauchy saturation. -/
theorem monotone_cauchyPairSaturation_reciprocal (d : ℝ) :
    Monotone (fun n : ℕ =>
      cauchyPairSaturation (1 / ((n : ℝ) + 1)) d) := by
  intro a b hab
  simp only [cauchyPairSaturation]
  have habCast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have habR : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    linarith
  have heps : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) habR
  have hepsSq : (1 / ((b : ℝ) + 1)) ^ 2 ≤
      (1 / ((a : ℝ) + 1)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 heps
  have hden : d ^ 2 + (1 / ((b : ℝ) + 1)) ^ 2 ≤
      d ^ 2 + (1 / ((a : ℝ) + 1)) ^ 2 := by
    linarith
  exact div_le_div_of_nonneg_left (sq_nonneg d)
    (by positivity) hden

/-- Finite positive multiplicity packets inherit monotonicity in reciprocal-shift depth. -/
theorem monotone_finiteCauchyShiftFibreCovariance {ι : Type*}
    (s : Finset ι) (x m : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i) :
    Monotone (finiteCauchyShiftFibreCovariance s x m) := by
  intro a b hab
  rw [finiteCauchyShiftFibreCovariance, finiteCauchyShiftFibreCovariance]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  exact mul_le_mul_of_nonneg_left
    (monotone_cauchyPairSaturation_reciprocal (x p.1 - x p.2) hab)
    (mul_nonneg (hm p.1 hp₁) (hm p.2 hp₂))

/-- Every finite shift covariance is bounded by exact off-diagonal mass. -/
theorem finiteCauchyShiftFibreCovariance_le_offDiagonalMass
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i) (n : ℕ) :
    finiteCauchyShiftFibreCovariance s x m n ≤
      finiteFibreOrderedOffDiagonalMass s m := by
  rw [finiteCauchyShiftFibreCovariance, finiteFibreOrderedOffDiagonalMass]
  apply Finset.sum_le_sum
  intro p hp
  rcases p with ⟨i, j⟩
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  by_cases hdiag : i = j
  · subst j
    simp [cauchyPairSaturation]
  · rw [if_neg hdiag]
    simpa using mul_le_mul_of_nonneg_left
      (cauchyPairSaturation_le_one
        (1 / ((n : ℝ) + 1)) (x i - x j))
      (mul_nonneg (hm i hp₁) (hm j hp₂))

/-- Exact unresolved mass at a finite reciprocal shift.  Every off-diagonal pair pays the explicit
factor `eps² / (gap² + eps²)`; no divisor or zero selector occurs in the identity. -/
theorem finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_eq
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) :
    finiteFibreOrderedOffDiagonalMass s m -
        finiteCauchyShiftFibreCovariance s x m n =
      ∑ p ∈ s.product s,
        if p.1 = p.2 then 0 else
          m p.1 * m p.2 *
            ((1 / ((n : ℝ) + 1)) ^ 2 /
              ((x p.1 - x p.2) ^ 2 +
                (1 / ((n : ℝ) + 1)) ^ 2)) := by
  rw [finiteFibreOrderedOffDiagonalMass,
    finiteCauchyShiftFibreCovariance, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hdiag : p.1 = p.2
  · simp [hdiag, cauchyPairSaturation]
  · simp only [if_neg hdiag]
    calc
      m p.1 * m p.2 -
          m p.1 * m p.2 *
            cauchyPairSaturation (1 / ((n : ℝ) + 1))
              (x p.1 - x p.2) =
        m p.1 * m p.2 *
          (1 - cauchyPairSaturation (1 / ((n : ℝ) + 1))
            (x p.1 - x p.2)) := by ring
      _ = m p.1 * m p.2 *
          ((1 / ((n : ℝ) + 1)) ^ 2 /
            ((x p.1 - x p.2) ^ 2 +
              (1 / ((n : ℝ) + 1)) ^ 2)) := by
        rw [one_sub_cauchyPairSaturation_eq]
        positivity

/-- Near/far decomposition of unresolved Cauchy mass.  No pointwise separation is required:
near pairs pay their full mass, while every far pair pays the explicit Cauchy ratio. -/
theorem finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_le_closePair_add_gapRatio
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) {delta : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hdelta : 0 < delta) :
    finiteFibreOrderedOffDiagonalMass s m -
        finiteCauchyShiftFibreCovariance s x m n ≤
      finiteFibreOrderedClosePairMass s x m delta +
        ((1 / ((n : ℝ) + 1)) ^ 2 /
          (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
            finiteFibreOrderedOffDiagonalMass s m := by
  rw [finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_eq,
    finiteFibreOrderedClosePairMass, finiteFibreOrderedOffDiagonalMass,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · simp only [if_neg hdiag]
    have hmass : 0 ≤ m p.1 * m p.2 :=
      mul_nonneg (hm p.1 hp1) (hm p.2 hp2)
    by_cases hclose : |x p.1 - x p.2| < delta
    · rw [if_pos hclose]
      have hden : 0 < (x p.1 - x p.2) ^ 2 +
          (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
      have hfrac :
          (1 / ((n : ℝ) + 1)) ^ 2 /
              ((x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
        rw [div_le_one hden]
        exact le_add_of_nonneg_left (sq_nonneg _)
      have hratio : 0 ≤
          (1 / ((n : ℝ) + 1)) ^ 2 /
            (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hfrac hmass,
        mul_nonneg hratio hmass]
    · rw [if_neg hclose]
      have hgap : delta ≤ |x p.1 - x p.2| := le_of_not_gt hclose
      have hsq : delta ^ 2 ≤ (x p.1 - x p.2) ^ 2 := by
        rw [← sq_abs (x p.1 - x p.2)]
        exact (sq_le_sq₀ hdelta.le (abs_nonneg _)).2 hgap
      have hden : delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 ≤
          (x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 := by
        linarith
      have hfrac :
          (1 / ((n : ℝ) + 1)) ^ 2 /
              ((x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ≤
            (1 / ((n : ℝ) + 1)) ^ 2 /
              (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) := by
        exact div_le_div_of_nonneg_left (sq_nonneg _)
          (by positivity) hden
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hfrac hmass

/-- Quantitative source-scale modulus.  If distinct support points are separated by `delta`, the
unresolved Cauchy mass is at most the exact gap ratio times total off-diagonal mass. -/
theorem finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_le_gapRatio
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) {delta : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hdelta : 0 < delta)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → delta ≤ |x i - x j|) :
    finiteFibreOrderedOffDiagonalMass s m -
        finiteCauchyShiftFibreCovariance s x m n ≤
      ((1 / ((n : ℝ) + 1)) ^ 2 /
          (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
        finiteFibreOrderedOffDiagonalMass s m := by
  rw [finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_eq,
    finiteFibreOrderedOffDiagonalMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · rw [if_neg hdiag, if_neg hdiag]
    have hgap' := hgap p.1 hp1 p.2 hp2 hdiag
    have hsq : delta ^ 2 ≤ (x p.1 - x p.2) ^ 2 := by
      rw [← sq_abs (x p.1 - x p.2)]
      exact (sq_le_sq₀ hdelta.le (abs_nonneg _)).2 hgap'
    have hden : delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 ≤
        (x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 := by
      linarith
    have hfrac :
        (1 / ((n : ℝ) + 1)) ^ 2 /
            ((x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ≤
          (1 / ((n : ℝ) + 1)) ^ 2 /
            (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        (by positivity) hden
    have hmass : 0 ≤ m p.1 * m p.2 :=
      mul_nonneg (hm p.1 hp1) (hm p.2 hp2)
    calc
      m p.1 * m p.2 *
          ((1 / ((n : ℝ) + 1)) ^ 2 /
            ((x p.1 - x p.2) ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) ≤
        m p.1 * m p.2 *
          ((1 / ((n : ℝ) + 1)) ^ 2 /
            (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hfrac hmass
      _ = ((1 / ((n : ℝ) + 1)) ^ 2 /
          (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
            (m p.1 * m p.2) := by ring

/-- A deterministic shift recovers the complementary fraction of off-diagonal mass controlled
by the packet's separation modulus. -/
theorem finiteCauchyShiftFibreCovariance_ge_gapRatio
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) {delta : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hdelta : 0 < delta)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → delta ≤ |x i - x j|) :
    (1 - (1 / ((n : ℝ) + 1)) ^ 2 /
        (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
        finiteFibreOrderedOffDiagonalMass s m ≤
      finiteCauchyShiftFibreCovariance s x m n := by
  have h := finiteFibreOrderedOffDiagonalMass_sub_cauchyShift_le_gapRatio
    s x m n hm hdelta hgap
  rw [show
    (1 - (1 / ((n : ℝ) + 1)) ^ 2 /
        (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
        finiteFibreOrderedOffDiagonalMass s m =
      finiteFibreOrderedOffDiagonalMass s m -
        ((1 / ((n : ℝ) + 1)) ^ 2 /
          (delta ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2)) *
          finiteFibreOrderedOffDiagonalMass s m by ring]
  linarith

/-- On distinct support, predetermined finite-shift covariances converge to exact off-diagonal
mass, with multiplicities retained as weights. -/
theorem tendsto_finiteCauchyShiftFibreCovariance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (hx : Set.InjOn x s) :
    Tendsto (finiteCauchyShiftFibreCovariance s x m) atTop
      (nhds (finiteFibreOrderedOffDiagonalMass s m)) := by
  change Tendsto
    (fun n : ℕ => ∑ p ∈ s.product s,
      m p.1 * m p.2 *
        cauchyPairSaturation (1 / ((n : ℝ) + 1)) (x p.1 - x p.2))
    atTop (nhds (finiteFibreOrderedOffDiagonalMass s m))
  rw [finiteFibreOrderedOffDiagonalMass]
  apply tendsto_finsetSum (s.product s)
  intro p hp
  rcases p with ⟨i, j⟩
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  by_cases hdiag : i = j
  · subst j
    simp [cauchyPairSaturation]
  · have hsep : x i - x j ≠ 0 :=
      sub_ne_zero.mpr (fun h => hdiag (hx hp₁ hp₂ h))
    have hmass : Tendsto (fun _ : ℕ => m i * m j) atTop
        (nhds (m i * m j)) := tendsto_const_nhds
    simpa [hdiag] using hmass.mul (tendsto_cauchyPairSaturation hsep)

/-- **Uniform source-shift ceiling gate.**  For a finite distinct height fibre, bounding exact
collision-free pair mass is equivalent to bounding every predetermined positive-real source
shift.  No minimum zero spacing or divisor-adaptive displacement appears. -/
theorem finiteFibreOrderedOffDiagonalMass_le_iff_forall_cauchyShift
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (hx : Set.InjOn x s)
    (hm : ∀ i ∈ s, 0 ≤ m i) (B : ℝ) :
    finiteFibreOrderedOffDiagonalMass s m ≤ B ↔
      ∀ n : ℕ, finiteCauchyShiftFibreCovariance s x m n ≤ B := by
  constructor
  · intro h n
    exact (finiteCauchyShiftFibreCovariance_le_offDiagonalMass s x m hm n).trans h
  · intro h
    exact le_of_tendsto
      (tendsto_finiteCauchyShiftFibreCovariance s x m hx)
      (Filter.Eventually.of_forall h)

/-- Two genuinely distinct support points whose gap collapses on the canonical height clock. -/
def collapsingTwoPointFibre (height : ℕ) (i : Fin 2) : ℝ :=
  if i = 0 then 0 else 1 / ((height : ℝ) + 1)

theorem collapsingTwoPointFibre_zero_ne_one (height : ℕ) :
    collapsingTwoPointFibre height 0 ≠ collapsingTwoPointFibre height 1 := by
  change (0 : ℝ) ≠ 1 / ((height : ℝ) + 1)
  exact ne_of_lt (by positivity)

theorem collapsingTwoPointFibre_gap (height : ℕ) :
    collapsingTwoPointFibre height 0 - collapsingTwoPointFibre height 1 =
      -1 / ((height : ℝ) + 1) := by
  change (0 : ℝ) - 1 / ((height : ℝ) + 1) = _
  ring

/-- Transverse real covariance is exactly the existing meromorphic source-pair covariance after
embedding the fibre on the imaginary axis. -/
theorem ofReal_finiteCauchyShiftFibreCovariance_eq_rationalCauchyPairCovariance
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) :
    (finiteCauchyShiftFibreCovariance s x m n : ℂ) =
      finiteRationalCauchyPairCovarianceAtScale s
        (fun i => I * (x i : ℂ)) (fun i => (m i : ℂ))
        (1 / ((n : ℝ) + 1)) := by
  rw [finiteCauchyShiftFibreCovariance,
    finiteRationalCauchyPairCovarianceAtScale]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [show I * (x p.1 : ℂ) =
      ((0 : ℝ) : ℂ) + I * (x p.1 : ℂ) by simp,
    show I * (x p.2 : ℂ) =
      ((0 : ℝ) : ℂ) + I * (x p.2 : ℂ) by simp,
    meromorphicCauchyPairKernel_equalOrdinate]

/-- On a transverse fibre, prescribed positive-real poles never collide with pair differences. -/
theorem imaginaryFibre_sub_ne_realShift
    (x y eps : ℝ) (heps : eps ≠ 0) :
    I * (x : ℂ) - I * (y : ℂ) - (eps : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [sub_re, mul_re, I_re, ofReal_re, I_im, ofReal_im,
    zero_mul, one_mul, sub_self, zero_sub] at hre
  exact heps (neg_eq_zero.mp hre)

/-- **Exact finite-shift source correction on a transverse fibre.**  The positive Cauchy packet
is total squared mass minus the centered prescribed-shift diagonal covariance.  Pole avoidance is
automatic and requires neither support separation nor a divisor-adaptive displacement. -/
theorem ofReal_finiteCauchyShiftFibreCovariance_eq_totalSquare_sub_centeredShift
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ) (n : ℕ) :
    (finiteCauchyShiftFibreCovariance s x m n : ℂ) =
      (∑ i ∈ s, (m i : ℂ)) ^ 2 -
        finiteCenteredReciprocalShiftDiagonalCovariance s
          (fun i => I * (x i : ℂ)) (fun i => (m i : ℂ))
          (1 / ((n : ℝ) + 1)) := by
  let eps : ℝ := 1 / ((n : ℝ) + 1)
  have heps : eps ≠ 0 := by
    dsimp only [eps]
    positivity
  have hminus : ∀ i ∈ s, ∀ j ∈ s,
      I * (x i : ℂ) - I * (x j : ℂ) - (eps : ℂ) ≠ 0 := by
    intro i hi j hj
    exact imaginaryFibre_sub_ne_realShift (x i) (x j) eps heps
  have hplus : ∀ i ∈ s, ∀ j ∈ s,
      I * (x i : ℂ) - I * (x j : ℂ) + (eps : ℂ) ≠ 0 := by
    intro i hi j hj h
    have hre := congrArg Complex.re h
    simp only [add_re, sub_re, mul_re, I_re, ofReal_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_self, zero_add] at hre
    exact heps hre
  rw [ofReal_finiteCauchyShiftFibreCovariance_eq_rationalCauchyPairCovariance]
  symm
  exact totalMass_sq_sub_centeredReciprocalShiftDiagonalCovariance_eq_pairCovariance
    s (fun i => I * (x i : ℂ)) (fun i => (m i : ℂ)) eps hminus hplus

end

end RHTower
