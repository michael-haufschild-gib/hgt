import GaloisForLFunctions.RHTower.SemilocalProlateFirstEulerCriticalJet
import GaloisForLFunctions.HTGeometry.CentralBinomialConvolutionAsymptotic

/-!
# Second Euler jet of the semilocal prolate critical potential

The published one-prime `q²` squared-Jacobi-radius coefficient contains a cancellation governed by
the hypergeometric tail

`Yₙ = ₂F₁(1, n + 1/2; n + 1; -1)`.

This file realizes `Yₙ` as a normalized alternating central-binomial tail and proves the sharp
unconditional estimate

`1/2 ≤ Yₙ ≤ 1/2 + 1/(4n+4)`.

The estimate forces the squared-radius second coefficient to grow like `16n/π`, while the square
of the first radius jet grows like `8n/π`.  Hence the positive-branch second radius coefficient
converges to `4/π`.

After propagation through the four-radius Route-J critical residual, every term linear in the
second radius coefficient cancels at degree scale.  Four quadratic products of the alternating
first radius jets remain, each contributing `-8/π`.  Therefore the exact `q²` critical
coefficient satisfies

`criticalSecondJet (n+1) / (2(n+1)) -> -32/π`.

Together with the first-jet `sqrt n` law, this proves that the `n ≍ p²` interaction scale survives
through Euler order two.  No claim about all higher Euler orders or resummation is made.
-/

noncomputable section

open Filter Real
open scoped BigOperators Topology

namespace RHTower.SecondEulerCriticalJet

open GaloisForLFunctions.HTGeometry
open FirstEulerCriticalJet

private theorem normalizedCentralBinom_succ_le (n : ℕ) :
    normalizedCentralBinom (n + 1) ≤ normalizedCentralBinom n := by
  rw [normalizedCentralBinom_succ_eq_ratio]
  have hc : 0 ≤ normalizedCentralBinom n :=
    FirstEulerCriticalJet.normalizedCentralBinom_nonneg n
  have hratio : centralBinomRatio n ≤ 1 := by
    unfold centralBinomRatio
    have hden : 0 < 2 * (n : ℝ) + 2 := by positivity
    rw [div_le_one hden]
    linarith
  exact mul_le_of_le_one_right hc hratio

private theorem normalizedCentralBinom_antitone :
    Antitone normalizedCentralBinom :=
  antitone_nat_of_succ_le normalizedCentralBinom_succ_le

private theorem tendsto_normalizedCentralBinom_zero :
    Tendsto normalizedCentralBinom atTop (nhds 0) := by
  have hinv :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hproduct :
      Tendsto
        (fun n : ℕ =>
          (Real.sqrt (n : ℝ))⁻¹ *
            (Real.sqrt n * normalizedCentralBinom n))
        atTop (nhds 0) := by
    simpa using hinv.mul tendsto_sqrtNat_mul_normalizedCentralBinom
  apply hproduct.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  field_simp [hsqrt]

private theorem exists_centralBinomAlternatingTail (n : ℕ) :
    ∃ l : ℝ,
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N,
            (-1 : ℝ) ^ k * normalizedCentralBinom (n + k))
        atTop (nhds l) := by
  exact
    (normalizedCentralBinom_antitone.comp_monotone
      (monotone_id.const_add n)).tendsto_alternating_series_of_tendsto_zero
        (tendsto_normalizedCentralBinom_zero.comp (by
          simpa [add_comm] using Filter.tendsto_add_atTop_nat n))

def centralBinomAlternatingTail (n : ℕ) : ℝ :=
  Classical.choose (exists_centralBinomAlternatingTail n)

theorem tendsto_centralBinomAlternatingPartialSums (n : ℕ) :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * normalizedCentralBinom (n + k))
      atTop (nhds (centralBinomAlternatingTail n)) :=
  Classical.choose_spec (exists_centralBinomAlternatingTail n)

private theorem alternatingPartialSum_succ (n N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
        (-1 : ℝ) ^ k * normalizedCentralBinom (n + k)) =
      normalizedCentralBinom n -
        ∑ k ∈ Finset.range N,
          (-1 : ℝ) ^ k * normalizedCentralBinom (n + 1 + k) := by
  rw [Finset.sum_range_succ']
  simp only [pow_add, pow_one]
  rw [show (∑ k ∈ Finset.range N,
        ((-1 : ℝ) ^ k * -1) * normalizedCentralBinom (n + (k + 1))) =
      -(∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * normalizedCentralBinom (n + 1 + k)) by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          rw [show n + (k + 1) = n + 1 + k by omega]
          ring]
  simp only [add_comm, add_left_comm, pow_zero, one_mul, Nat.add_zero,
    sub_eq_add_neg]

theorem centralBinomAlternatingTail_add_succ (n : ℕ) :
    centralBinomAlternatingTail n +
        centralBinomAlternatingTail (n + 1) =
      normalizedCentralBinom n := by
  have hshift :
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range (N + 1),
            (-1 : ℝ) ^ k * normalizedCentralBinom (n + k))
        atTop (nhds (centralBinomAlternatingTail n)) := by
    exact (tendsto_centralBinomAlternatingPartialSums n).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hright :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => normalizedCentralBinom n) atTop
        (nhds (normalizedCentralBinom n))).sub
      (tendsto_centralBinomAlternatingPartialSums (n + 1))
  have heq : centralBinomAlternatingTail n =
      normalizedCentralBinom n - centralBinomAlternatingTail (n + 1) := by
    apply tendsto_nhds_unique hshift
    apply hright.congr'
    exact Filter.Eventually.of_forall fun N =>
      (alternatingPartialSum_succ n N).symm
  linarith

def centralBinomForwardDrop (n : ℕ) : ℝ :=
  normalizedCentralBinom n - normalizedCentralBinom (n + 1)

theorem centralBinomForwardDrop_eq (n : ℕ) :
    centralBinomForwardDrop n =
      normalizedCentralBinom n / (2 * (n : ℝ) + 2) := by
  unfold centralBinomForwardDrop
  rw [normalizedCentralBinom_succ_eq_ratio]
  unfold centralBinomRatio
  have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

private theorem centralBinomForwardDrop_succ_le (n : ℕ) :
    centralBinomForwardDrop (n + 1) ≤ centralBinomForwardDrop n := by
  rw [centralBinomForwardDrop_eq, centralBinomForwardDrop_eq,
    normalizedCentralBinom_succ_eq_ratio]
  unfold centralBinomRatio
  have hc : 0 ≤ normalizedCentralBinom n :=
    FirstEulerCriticalJet.normalizedCentralBinom_nonneg n
  have h₂ : 0 < 2 * (n : ℝ) + 2 := by positivity
  have h₄ : 0 < 2 * (n : ℝ) + 4 := by positivity
  push_cast
  rw [show 2 * ((n : ℝ) + 1) + 2 = 2 * (n : ℝ) + 4 by ring]
  rw [div_le_div_iff₀ h₄ h₂]
  rw [mul_assoc, div_mul_cancel₀ _ h₂.ne']
  exact mul_le_mul_of_nonneg_left (by linarith) hc

private theorem centralBinomForwardDrop_antitone :
    Antitone centralBinomForwardDrop :=
  antitone_nat_of_succ_le centralBinomForwardDrop_succ_le

private theorem tendsto_centralBinomForwardDrop_zero :
    Tendsto centralBinomForwardDrop atTop (nhds 0) := by
  have h := tendsto_normalizedCentralBinom_zero.sub
      (tendsto_normalizedCentralBinom_zero.comp (by
        simpa using Filter.tendsto_add_atTop_nat 1))
  change Tendsto
    (fun n : ℕ =>
      normalizedCentralBinom n - normalizedCentralBinom (n + 1))
    atTop (nhds 0)
  simpa [Function.comp_apply] using h

private theorem alternatingDropPartialSum_eq (n N : ℕ) :
    (∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * centralBinomForwardDrop (n + k)) =
      (∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * normalizedCentralBinom (n + k)) -
      (∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * normalizedCentralBinom (n + 1 + k)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold centralBinomForwardDrop
  rw [show n + k + 1 = n + 1 + k by omega]
  ring

theorem centralBinomAlternatingTail_sub_succ_bounds (n : ℕ) :
    0 ≤ centralBinomAlternatingTail n -
        centralBinomAlternatingTail (n + 1) ∧
      centralBinomAlternatingTail n -
          centralBinomAlternatingTail (n + 1) ≤
        centralBinomForwardDrop n := by
  have hdropTendsto :
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N,
            (-1 : ℝ) ^ k * centralBinomForwardDrop (n + k))
        atTop
        (nhds (centralBinomAlternatingTail n -
          centralBinomAlternatingTail (n + 1))) := by
    have hsub :=
      (tendsto_centralBinomAlternatingPartialSums n).sub
        (tendsto_centralBinomAlternatingPartialSums (n + 1))
    apply hsub.congr'
    exact Filter.Eventually.of_forall fun N =>
      (alternatingDropPartialSum_eq n N).symm
  have hantitone :
      Antitone (fun k : ℕ => centralBinomForwardDrop (n + k)) :=
    centralBinomForwardDrop_antitone.comp_monotone
      (monotone_id.const_add n)
  constructor
  · simpa using hantitone.alternating_series_le_tendsto hdropTendsto 0
  · simpa using hantitone.tendsto_le_alternating_series hdropTendsto 0

def semilocalHypergeometricTail (n : ℕ) : ℝ :=
  centralBinomAlternatingTail n / normalizedCentralBinom n

theorem semilocalHypergeometricTail_bounds (n : ℕ) :
    (1 / 2 : ℝ) ≤ semilocalHypergeometricTail n ∧
      semilocalHypergeometricTail n ≤
        1 / 2 + 1 / (4 * (n : ℝ) + 4) := by
  have hc : 0 < normalizedCentralBinom n := by
    unfold normalizedCentralBinom
    exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)
  have hsum := centralBinomAlternatingTail_add_succ n
  have hdiff := centralBinomAlternatingTail_sub_succ_bounds n
  have hdrop := centralBinomForwardDrop_eq n
  unfold semilocalHypergeometricTail
  constructor
  · apply (le_div_iff₀ hc).2
    linarith
  · apply (div_le_iff₀ hc).2
    rw [hdrop] at hdiff
    have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hden]
    field_simp [hden] at hdiff
    nlinarith

theorem tendsto_semilocalHypergeometricTail :
    Tendsto semilocalHypergeometricTail atTop (nhds (1 / 2 : ℝ)) := by
  have hdiff :
      Tendsto (fun n : ℕ =>
        semilocalHypergeometricTail n - 1 / 2)
        atTop (nhds 0) := by
    apply squeeze_zero (g := fun n : ℕ => 1 / (4 * (n : ℝ) + 4))
    · exact fun n =>
      sub_nonneg.2 (semilocalHypergeometricTail_bounds n).1
    · exact fun n => by
        apply (sub_le_iff_le_add).2
        simpa [add_comm] using (semilocalHypergeometricTail_bounds n).2
    · have hden :
        Tendsto (fun n : ℕ => 4 * (n : ℝ) + 4) atTop atTop := by
        have hfour :
            Tendsto (fun n : ℕ => 4 * (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
        simpa using hfour.atTop_add
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4))
      simpa [Function.comp_def, one_div] using
        tendsto_inv_atTop_zero.comp hden
  have hadd := hdiff.add_const (1 / 2 : ℝ)
  simpa [sub_add_cancel] using hadd

/-- Literal `ℓ=0` Euler atom `2√2 αₙ`. -/
def semilocalFirstEulerAtom (n : ℕ) : ℝ :=
  2 * Real.sqrt 2 * signedCentralBinom n

/-- Published form of the cancellation bracket in the relative `q²` coefficient of `aₙ(q)²`. -/
def publishedSecondSquaredRadiusBracket (n : ℕ) : ℝ :=
  ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) -
    centralBinomRatio n *
      ((n : ℝ) - 1 + semilocalHypergeometricTail n / 2)

/-- Cancellation-exposing form of the same bracket. -/
def secondSquaredRadiusBracket (n : ℕ) : ℝ :=
  2 - semilocalHypergeometricTail n +
    ((n : ℝ) - 1 + semilocalHypergeometricTail n / 2) /
      (2 * (n : ℝ) + 2)

theorem publishedSecondSquaredRadiusBracket_eq (n : ℕ) :
    publishedSecondSquaredRadiusBracket n =
      secondSquaredRadiusBracket n := by
  unfold publishedSecondSquaredRadiusBracket secondSquaredRadiusBracket
    centralBinomRatio
  have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Exact published relative `q²` coefficient after parity-sum reduction. -/
def squaredJacobiRadiusSecondRelativeCoefficient (n : ℕ) : ℝ :=
  semilocalFirstEulerAtom n ^ (2 : ℕ) * secondSquaredRadiusBracket n

/-- Exact `q²` coefficient of the squared Jacobi radius. -/
def squaredJacobiRadiusSecondCoefficient (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n *
    squaredJacobiRadiusSecondRelativeCoefficient n

/-- Exact `q²` coefficient on the positive square-root radius branch. -/
def jacobiRadiusSecondCoefficient (n : ℕ) : ℝ :=
  (squaredJacobiRadiusSecondCoefficient n - jacobiRadiusJet n ^ (2 : ℕ)) /
    (2 * semilocalArchimedeanJacobiCoefficient n)

theorem semilocalFirstEulerAtom_sq (n : ℕ) :
    semilocalFirstEulerAtom n ^ (2 : ℕ) =
      8 * normalizedCentralBinom n ^ (2 : ℕ) := by
  unfold semilocalFirstEulerAtom signedCentralBinom
  rw [mul_pow, mul_pow]
  have hsqrt : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  rw [hsqrt]
  have hsign : ((-1 : ℝ) ^ n) ^ (2 : ℕ) = 1 := by
    rw [← pow_mul]
    norm_num
  rw [mul_pow, hsign]
  ring

private theorem tendsto_normalizedCentralBinom_sq_zero :
    Tendsto (fun n : ℕ => normalizedCentralBinom n ^ (2 : ℕ))
      atTop (nhds 0) := by
  simpa using tendsto_normalizedCentralBinom_zero.pow 2

theorem tendsto_succ_mul_normalizedCentralBinom_sq :
    Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) * normalizedCentralBinom n ^ (2 : ℕ))
      atTop (nhds (1 / Real.pi)) := by
  have hmain :
      Tendsto
        (fun n : ℕ => (n : ℝ) * normalizedCentralBinom n ^ (2 : ℕ))
        atTop (nhds (1 / Real.pi)) := by
    convert tendsto_sqrtNat_mul_normalizedCentralBinom_sq using 1
    funext n
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hadd := hmain.add tendsto_normalizedCentralBinom_sq_zero
  convert hadd using 1
  · funext n
    ring
  · ring

theorem tendsto_sqrt_succ_mul_normalizedCentralBinom :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt ((n : ℝ) + 1) * normalizedCentralBinom n)
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
  have hsqrt :=
    Real.continuous_sqrt.continuousAt.tendsto.comp
      tendsto_succ_mul_normalizedCentralBinom_sq
  convert hsqrt using 1
  · funext n
    have hc : 0 ≤ normalizedCentralBinom n :=
      FirstEulerCriticalJet.normalizedCentralBinom_nonneg n
    rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (by positivity)]
    congr 1
  · rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1)]
    simp only [Real.sqrt_one, one_div]

theorem tendsto_succ_mul_semilocalFirstEulerAtom_sq :
    Tendsto
      (fun n : ℕ => ((n : ℝ) + 1) * semilocalFirstEulerAtom n ^ (2 : ℕ))
      atTop (nhds (8 / Real.pi)) := by
  have h := tendsto_succ_mul_normalizedCentralBinom_sq.const_mul 8
  convert h using 1
  · funext n
    rw [semilocalFirstEulerAtom_sq]
    ring
  · ring

theorem tendsto_secondSquaredRadiusBracket :
    Tendsto secondSquaredRadiusBracket atTop (nhds 2) := by
  have hfirst :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).sub
      tendsto_semilocalHypergeometricTail
  have hbase :
      Tendsto
        (fun n : ℕ => ((n : ℝ) - 1) / (2 * (n : ℝ) + 2))
        atTop (nhds (1 / 2 : ℝ)) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (-1 : ℝ) 2 1 (by norm_num : (2 : ℝ) ≠ 0)) using 1
    funext n
    ring
  have hdenInv :
      Tendsto (fun n : ℕ => (2 * (n : ℝ) + 2)⁻¹)
        atTop (nhds 0) := by
    have hden :
        Tendsto (fun n : ℕ => 2 * (n : ℝ) + 2) atTop atTop := by
      have htwo :
          Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
      simpa using htwo.atTop_add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2))
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  have htail :
      Tendsto
        (fun n : ℕ =>
          (semilocalHypergeometricTail n / 2) *
            (2 * (n : ℝ) + 2)⁻¹)
        atTop (nhds 0) := by
    simpa using (tendsto_semilocalHypergeometricTail.div_const 2).mul hdenInv
  have hquot := hbase.add htail
  have hsecond :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) - 1 + semilocalHypergeometricTail n / 2) /
            (2 * (n : ℝ) + 2))
        atTop (nhds (1 / 2 : ℝ)) := by
    have hquot' :
        Tendsto
          (fun n : ℕ =>
            ((n : ℝ) - 1) / (2 * (n : ℝ) + 2) +
              (semilocalHypergeometricTail n / 2) *
                (2 * (n : ℝ) + 2)⁻¹)
          atTop (nhds (1 / 2 : ℝ)) := by
      simpa using hquot
    apply hquot'.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hden]
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · funext n
    rfl
  · norm_num

theorem tendsto_squaredJacobiRadiusSecondCoefficient_div_succ :
    Tendsto
      (fun n : ℕ =>
        squaredJacobiRadiusSecondCoefficient n / ((n : ℝ) + 1))
      atTop (nhds (16 / Real.pi)) := by
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hatom := tendsto_succ_mul_semilocalFirstEulerAtom_sq
  have hbracket := tendsto_secondSquaredRadiusBracket
  have hproduct := (hr.pow 2).mul (hatom.mul hbracket)
  convert hproduct using 1
  · funext n
    unfold squaredJacobiRadiusSecondCoefficient
      squaredJacobiRadiusSecondRelativeCoefficient
    rw [archimedeanSquaredRadius_eq_coefficient_sq]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  · field_simp [Real.pi_ne_zero]
    ring

theorem tendsto_centralBinomJumpFactor :
    Tendsto centralBinomJumpFactor atTop (nhds 2) := by
  unfold centralBinomJumpFactor
  convert
    (tendsto_add_mul_div_add_mul_atTop_nhds
      (3 : ℝ) 2 4 (by norm_num : (2 : ℝ) ≠ 0)) using 1
  · funext n
    ring
  · norm_num

theorem tendsto_jacobiRadiusJet_sq_div_succ :
    Tendsto
      (fun n : ℕ => jacobiRadiusJet n ^ (2 : ℕ) / ((n : ℝ) + 1))
      atTop (nhds (8 / Real.pi)) := by
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hc := tendsto_succ_mul_normalizedCentralBinom_sq
  have hh := tendsto_centralBinomJumpFactor
  have hproduct := ((hr.pow 2).mul hc).mul ((hh.pow 2).const_mul 2)
  convert hproduct using 1
  · funext n
    rw [jacobiRadiusJet_eq_signed_positive]
    unfold positiveEulerRadiusJet
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hsign : ((-1 : ℝ) ^ (n + 1)) ^ (2 : ℕ) = 1 := by
      rw [← pow_mul]
      norm_num
    rw [mul_pow, hsign, one_mul]
    have hsqrt : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
    rw [show
      (Real.sqrt 2 * semilocalArchimedeanJacobiCoefficient n *
        centralBinomJumpFactor n * normalizedCentralBinom n) ^ (2 : ℕ) =
        2 * semilocalArchimedeanJacobiCoefficient n ^ (2 : ℕ) *
          centralBinomJumpFactor n ^ (2 : ℕ) *
          normalizedCentralBinom n ^ (2 : ℕ) by
            rw [mul_pow, mul_pow, mul_pow, hsqrt]]
    field_simp [hn]
  · field_simp [Real.pi_ne_zero]
    ring

theorem jacobiRadiusSecondCoefficient_eq_normalized (n : ℕ) :
    jacobiRadiusSecondCoefficient n =
      ((squaredJacobiRadiusSecondCoefficient n / ((n : ℝ) + 1)) -
        (jacobiRadiusJet n ^ (2 : ℕ) / ((n : ℝ) + 1))) /
      (2 * (semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1))) := by
  unfold jacobiRadiusSecondCoefficient
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hr := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  field_simp [hn, hr]

theorem tendsto_jacobiRadiusSecondCoefficient :
    Tendsto jacobiRadiusSecondCoefficient atTop (nhds (4 / Real.pi)) := by
  have hnum :=
    tendsto_squaredJacobiRadiusSecondCoefficient_div_succ.sub
      tendsto_jacobiRadiusJet_sq_div_succ
  have hden :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.const_mul 2
  have hquot := hnum.div hden (by norm_num)
  convert hquot using 1
  · funext n
    exact jacobiRadiusSecondCoefficient_eq_normalized n
  · congr 1
    field_simp [Real.pi_ne_zero]
    ring

/-- Terms in the critical `q²` coefficient which are linear in the second radius coefficient. -/
def criticalResidualSecondLinearCoefficient (n : ℕ) : ℝ :=
  let m := 2 * n
  let r := semilocalArchimedeanJacobiCoefficient
  let v := jacobiRadiusSecondCoefficient
  v m * r (m + 1) + r m * v (m + 1) -
    2 * r (m + 1) * v (m + 1) -
    2 * r (m + 2) * v (m + 2) +
    v (m + 2) * r (m + 3) + r (m + 2) * v (m + 3)

/-- Quadratic first-jet terms in the critical `q²` coefficient. -/
def criticalResidualFirstJetQuadraticCoefficient (n : ℕ) : ℝ :=
  let m := 2 * n
  jacobiRadiusJet m * jacobiRadiusJet (m + 1) -
    jacobiRadiusJet (m + 1) ^ (2 : ℕ) -
    jacobiRadiusJet (m + 2) ^ (2 : ℕ) +
    jacobiRadiusJet (m + 2) * jacobiRadiusJet (m + 3)

/-- Exact `q²` coefficient of the four-radius critical residual. -/
def criticalResidualSecondCoefficient (n : ℕ) : ℝ :=
  criticalResidualSecondLinearCoefficient n +
    criticalResidualFirstJetQuadraticCoefficient n

theorem criticalResidualSecondCoefficient_eq_expanded (n : ℕ) :
    criticalResidualSecondCoefficient n =
      let m := 2 * n
      let r := semilocalArchimedeanJacobiCoefficient
      let u := jacobiRadiusJet
      let v := jacobiRadiusSecondCoefficient
      v m * r (m + 1) + u m * u (m + 1) + r m * v (m + 1) -
        (u (m + 1) ^ (2 : ℕ) + 2 * r (m + 1) * v (m + 1)) -
        (u (m + 2) ^ (2 : ℕ) + 2 * r (m + 2) * v (m + 2)) +
        v (m + 2) * r (m + 3) + u (m + 2) * u (m + 3) +
        r (m + 2) * v (m + 3) := by
  unfold criticalResidualSecondCoefficient
    criticalResidualSecondLinearCoefficient
    criticalResidualFirstJetQuadraticCoefficient
  dsimp only
  ring

private theorem tendsto_criticalBoundaryDegree_add (j : ℕ) :
    Tendsto (fun n : ℕ => criticalBoundaryDegree n + j) atTop atTop :=
  (Filter.tendsto_add_atTop_nat j).comp tendsto_criticalBoundaryDegree

private theorem tendsto_boundaryShiftRatio (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1) /
          (criticalBoundaryDegree n : ℝ)))
      atTop (nhds 1) := by
  convert
    (tendsto_add_mul_div_add_mul_atTop_nhds
      ((j : ℝ) + 3) 2 2 (by norm_num : (2 : ℝ) ≠ 0)) using 1
  · funext n
    unfold criticalBoundaryDegree
    push_cast
    ring
  · norm_num

private theorem tendsto_radius_boundaryShift_div (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j) /
          (criticalBoundaryDegree n : ℝ))
      atTop (nhds 1) := by
  have hr :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hratio := tendsto_boundaryShiftRatio j
  have hproduct := hr.mul hratio
  convert hproduct using 1
  · funext n
    simp only [Function.comp_apply]
    have hm : (criticalBoundaryDegree n : ℝ) ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hk :
        ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hm, hk]
  · norm_num

private theorem tendsto_secondRadius_boundaryShift (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        jacobiRadiusSecondCoefficient (criticalBoundaryDegree n + j))
      atTop (nhds (4 / Real.pi)) :=
  tendsto_jacobiRadiusSecondCoefficient.comp
    (tendsto_criticalBoundaryDegree_add j)

theorem tendsto_criticalResidualSecondLinearCoefficient_div_boundary :
    Tendsto
      (fun n : ℕ =>
        criticalResidualSecondLinearCoefficient (n + 1) /
          (criticalBoundaryDegree n : ℝ))
      atTop (nhds 0) := by
  have hv₀ := tendsto_secondRadius_boundaryShift 0
  have hv₁ := tendsto_secondRadius_boundaryShift 1
  have hv₂ := tendsto_secondRadius_boundaryShift 2
  have hv₃ := tendsto_secondRadius_boundaryShift 3
  have hr₀ := tendsto_radius_boundaryShift_div 0
  have hr₁ := tendsto_radius_boundaryShift_div 1
  have hr₂ := tendsto_radius_boundaryShift_div 2
  have hr₃ := tendsto_radius_boundaryShift_div 3
  have h :=
    ((((hv₀.mul hr₁).add (hr₀.mul hv₁)).sub
      ((hr₁.mul hv₁).const_mul 2)).sub
      ((hr₂.mul hv₂).const_mul 2)).add
      ((hv₂.mul hr₃).add (hr₂.mul hv₃))
  convert h using 1
  · funext n
    unfold criticalResidualSecondLinearCoefficient criticalBoundaryDegree
    dsimp only
    push_cast
    have hm : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
    field_simp [hm]
    ring
  · field_simp [Real.pi_ne_zero]
    ring

/-- Natural amplitude of the alternating first radius jet. -/
def positiveEulerBoundaryAmplitude : ℝ :=
  2 * Real.sqrt 2 / Real.sqrt Real.pi

theorem positiveEulerBoundaryAmplitude_sq :
    positiveEulerBoundaryAmplitude ^ (2 : ℕ) = 8 / Real.pi := by
  unfold positiveEulerBoundaryAmplitude
  have hsqrtTwo : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtPi : Real.sqrt Real.pi ^ (2 : ℕ) = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  field_simp [Real.sqrt_ne_zero'.2 Real.pi_pos]
  rw [hsqrtPi, hsqrtTwo]
  ring

theorem tendsto_positiveEulerRadiusJet_div_sqrt_succ :
    Tendsto
      (fun n : ℕ =>
        positiveEulerRadiusJet n / Real.sqrt ((n : ℝ) + 1))
      atTop (nhds positiveEulerBoundaryAmplitude) := by
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hh := tendsto_centralBinomJumpFactor
  have hc := tendsto_sqrt_succ_mul_normalizedCentralBinom
  have hproduct := (((hr.mul hh).mul hc).const_mul (Real.sqrt 2))
  convert hproduct using 1
  · funext n
    unfold positiveEulerRadiusJet
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hsqrt : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    have hsquare :
        Real.sqrt ((n : ℝ) + 1) ^ (2 : ℕ) = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    field_simp [hn, hsqrt]
    rw [hsquare]
  · unfold positiveEulerBoundaryAmplitude
    ring

private theorem tendsto_sqrt_boundaryShiftRatio (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          ((((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1) /
            (criticalBoundaryDegree n : ℝ)))
      atTop (nhds 1) := by
  simpa using (tendsto_boundaryShiftRatio j).sqrt

private theorem tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrt (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        positiveEulerRadiusJet (criticalBoundaryDegree n + j) /
          Real.sqrt (criticalBoundaryDegree n))
      atTop (nhds positiveEulerBoundaryAmplitude) := by
  have hp :=
    tendsto_positiveEulerRadiusJet_div_sqrt_succ.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hsqrt := tendsto_sqrt_boundaryShiftRatio j
  have hproduct := hp.mul hsqrt
  convert hproduct using 1
  · funext n
    simp only [Function.comp_apply]
    have hmpos : 0 < (criticalBoundaryDegree n : ℝ) := by
      unfold criticalBoundaryDegree
      positivity
    have hkpos :
        0 < ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1 := by positivity
    have hm : Real.sqrt (criticalBoundaryDegree n) ≠ 0 :=
      (Real.sqrt_pos.2 hmpos).ne'
    have hk :
        Real.sqrt (((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1) ≠ 0 :=
      (Real.sqrt_pos.2 hkpos).ne'
    rw [Real.sqrt_div (by positivity :
      0 ≤ (((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1))]
    field_simp [hm, hk]
  · simp

theorem criticalResidualFirstJetQuadraticCoefficient_eq_negative_amplitudes
    (n : ℕ) :
    criticalResidualFirstJetQuadraticCoefficient (n + 1) =
      -(positiveEulerRadiusJet (criticalBoundaryDegree n) *
          positiveEulerRadiusJet (criticalBoundaryDegree n + 1)) -
        positiveEulerRadiusJet (criticalBoundaryDegree n + 1) ^ (2 : ℕ) -
        positiveEulerRadiusJet (criticalBoundaryDegree n + 2) ^ (2 : ℕ) -
        positiveEulerRadiusJet (criticalBoundaryDegree n + 2) *
          positiveEulerRadiusJet (criticalBoundaryDegree n + 3) := by
  unfold criticalResidualFirstJetQuadraticCoefficient criticalBoundaryDegree
  dsimp only
  rw [jacobiRadiusJet_even (n + 1),
    jacobiRadiusJet_odd (n + 1),
    show 2 * (n + 1) + 2 = 2 * (n + 2) by omega,
    show 2 * (n + 1) + 3 = 2 * (n + 2) + 1 by omega,
    jacobiRadiusJet_even (n + 2),
    jacobiRadiusJet_odd (n + 2)]
  ring

theorem tendsto_criticalResidualFirstJetQuadraticCoefficient_div_boundary :
    Tendsto
      (fun n : ℕ =>
        criticalResidualFirstJetQuadraticCoefficient (n + 1) /
          (criticalBoundaryDegree n : ℝ))
      atTop (nhds (-32 / Real.pi)) := by
  have hp₀ := tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrt 0
  have hp₁ := tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrt 1
  have hp₂ := tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrt 2
  have hp₃ := tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrt 3
  have h :=
    ((((hp₀.mul hp₁).neg).sub (hp₁.pow 2)).sub (hp₂.pow 2)).sub
      (hp₂.mul hp₃)
  convert h using 1
  · funext n
    rw [criticalResidualFirstJetQuadraticCoefficient_eq_negative_amplitudes]
    have hmpos : 0 < (criticalBoundaryDegree n : ℝ) := by
      unfold criticalBoundaryDegree
      positivity
    have hm : Real.sqrt (criticalBoundaryDegree n) ≠ 0 :=
      (Real.sqrt_pos.2 hmpos).ne'
    have hsquare :
        Real.sqrt (criticalBoundaryDegree n) ^ (2 : ℕ) =
          (criticalBoundaryDegree n : ℝ) :=
      Real.sq_sqrt hmpos.le
    field_simp [hm, hmpos.ne']
    rw [hsquare]
    ring
  · rw [show
      -(positiveEulerBoundaryAmplitude * positiveEulerBoundaryAmplitude) -
          positiveEulerBoundaryAmplitude ^ (2 : ℕ) -
          positiveEulerBoundaryAmplitude ^ (2 : ℕ) -
          positiveEulerBoundaryAmplitude * positiveEulerBoundaryAmplitude =
        -4 * positiveEulerBoundaryAmplitude ^ (2 : ℕ) by ring,
      positiveEulerBoundaryAmplitude_sq]
    field_simp [Real.pi_ne_zero]
    ring

/-- **Sharp second-Euler critical boundary law.**  The `q²` coefficient of the fully
orthogonalized four-radius residual grows linearly with degree, with exact normalized constant
`-32/π`. -/
theorem tendsto_criticalResidualSecondCoefficient_div_boundary :
    Tendsto
      (fun n : ℕ =>
        criticalResidualSecondCoefficient (n + 1) /
          (criticalBoundaryDegree n : ℝ))
      atTop (nhds (-32 / Real.pi)) := by
  have h :=
    tendsto_criticalResidualSecondLinearCoefficient_div_boundary.add
      tendsto_criticalResidualFirstJetQuadraticCoefficient_div_boundary
  convert h using 1
  · funext n
    unfold criticalResidualSecondCoefficient
    ring
  · ring

end RHTower.SecondEulerCriticalJet
