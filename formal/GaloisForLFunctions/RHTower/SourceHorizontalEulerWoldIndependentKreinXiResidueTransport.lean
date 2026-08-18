import GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVKreinSelectedResidueThirdJetDescent

/-!
# Independent Euler--Wold Krein transport through a selected Xi residue

This module closes the completed-residue transport obligation for the source-natural negative
Euler cubic current. One bivariate source is differentiated in independent Euler and Wold
coordinates before either Gamma variable is selected. Its pure third jets recover the complete
negative Euler moment and positive Wold counterterm, while the mixed third-by-third jet vanishes.

Both pure jets then pass successively through the same multiplicity-normalized completed Gamma
gauges. Their common polar factor is forced to be `2`; their target remains the literal sum of four
FE--Schwarz--Krein orientation blocks. The pre-existing signed BV endpoint block is transported as
an unchanged third component. Summation over the actual Xi support fibre restores exact analytic
multiplicity.

After, and only after, the two separate residue proofs, linear grade-forgetting is classified
exactly: it is the negative normalized summable Euler--Wold defect, nonzero at every finite clock
but converging entrywise to zero. This is an unconditional transport theorem, not an RH proof.
-/

open Complex Filter Function Set WithTop Topology MeasureTheory
open scoped BigOperators ComplexOrder
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions

namespace RHTower

noncomputable section

def sourceHorizontalEulerOrderedLogDeformation (N : ℕ) (s : ℝ) : ℝ :=
  primeEulerLogBelow s ((nthPrimeSubtype N : ℕ) + 1)

def sourceHorizontalWoldOrderedPrimeDeformation (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype n) t

theorem primesBelow_succ_nthPrimeSubtype (N : ℕ) :
    Nat.primesBelow ((nthPrimeSubtype N : ℕ) + 1) =
      (Finset.Icc 0 (nthPrimeSubtype N : ℕ)).filter Nat.Prime := by
  ext p
  simp [Nat.mem_primesBelow]

theorem sourceHorizontalEulerGammaCubicNegativeCurrentBelow_succ_eq (N : ℕ) :
    sourceHorizontalEulerGammaCubicNegativeCurrentBelow
        ((nthPrimeSubtype N : ℕ) + 1) =
      -sourceHorizontalEulerGammaCubicMoment N := by
  rw [sourceHorizontalEulerGammaCubicNegativeCurrentBelow,
    primesBelow_succ_nthPrimeSubtype, ← image_range_succ_nthPrimeSubtype_eq_primes_Icc,
    Finset.sum_image]
  · simp [sourceHorizontalEulerGammaCubicMoment,
      sourceHorizontalEulerGammaCubicAtom]
  · intro a ha b hb hab
    apply nthPrimeSubtype_injective
    exact Subtype.ext hab

theorem iteratedDeriv_sourceHorizontalEulerOrderedLogDeformation_three (N : ℕ) :
    iteratedDeriv 3 (sourceHorizontalEulerOrderedLogDeformation N) 1 =
      -sourceHorizontalEulerGammaCubicMoment N := by
  change iteratedDeriv 3
      (fun s => primeEulerLogBelow s ((nthPrimeSubtype N : ℕ) + 1)) 1 = _
  rw [← sourceHorizontalEulerGammaCubicNegativeCurrentBelow_eq_eulerThirdJet]
  exact sourceHorizontalEulerGammaCubicNegativeCurrentBelow_succ_eq N

theorem contDiffAt_sourceHorizontalWoldOrderedPrimeDeformation
    (N n : ℕ) (t : ℝ) :
    ContDiffAt ℝ n (sourceHorizontalWoldOrderedPrimeDeformation N) t := by
  unfold sourceHorizontalWoldOrderedPrimeDeformation
  exact ContDiffAt.sum fun p hp =>
    contDiff_sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype p) n |>.contDiffAt

theorem iteratedDeriv_sourceHorizontalWoldOrderedPrimeDeformation_three (N : ℕ) :
    iteratedDeriv 3 (sourceHorizontalWoldOrderedPrimeDeformation N) 0 =
      ∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2 := by
  change iteratedDeriv 3
      (fun t => ∑ n ∈ Finset.range (N + 1),
        sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype n) t) 0 = _
  rw [iteratedDeriv_fun_sum (fun n hn =>
      contDiff_sourceHorizontalWoldPrimeDeformation (nthPrimeSubtype n) 3 |>.contDiffAt)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_sourceHorizontalWoldPrimeDeformation_three,
    xiMassNthPrimeLogHeight]

/-- Completed two-pole kernel retaining the full four-orientation orbit. -/
def sourceHorizontalEulerWoldGammaPolarOrbitKernel
    (c : ℂ) (q : XiRightZeroCopy) (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((frankensteinCCMGammaCenteredResidueGauge q.1.1 u +
      frankensteinCCMGammaCenteredResidueGauge
        (xiRightZeroCopyConjEquiv q).1.1 v) ^ 3) /
    ((4 * (xiRightCenteredZero q).re ^ 3 : ℝ) : ℂ)) •
      routePJuliaSharedOrientationOrbitBlock c

/-- First completed residue leaves the Schwarz-conjugate pole variable free. -/
def sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((xiRightCenteredZero q +
      frankensteinCCMGammaCenteredResidueGauge
        (xiRightZeroCopyConjEquiv q).1.1 v) ^ 3) /
    ((4 * (xiRightCenteredZero q).re ^ 3 : ℝ) : ℂ)) •
      routePJuliaSharedOrientationOrbitBlock c

/-- Both completed residues produce the forced factor two, not a chosen scalar. -/
def sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding
    (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ) • routePJuliaSharedOrientationOrbitBlock c

theorem tendsto_sourceHorizontalEulerWoldGammaPolarOrbitKernel_first
    (c : ℂ) (q : XiRightZeroCopy) (v : ℂ) :
    Tendsto (fun u => sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v)
      (nhdsWithin (criticalMellinXiPole q.1.1)
        ({criticalMellinXiPole q.1.1}ᶜ))
      (nhds (sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q v)) := by
  have h := (tendsto_frankensteinCCMGammaCenteredResidueGauge q.1.1).add_const
    (frankensteinCCMGammaCenteredResidueGauge
      (xiRightZeroCopyConjEquiv q).1.1 v)
  have hdiv := (h.pow 3).div_const
    (((4 * (xiRightCenteredZero q).re ^ 3 : ℝ) : ℂ))
  have hsmul := hdiv.smul_const (routePJuliaSharedOrientationOrbitBlock c)
  simpa [sourceHorizontalEulerWoldGammaPolarOrbitKernel,
    sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding,
    xiRightCenteredZero_eq_support_sub_half] using hsmul

theorem tendsto_sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) :
    Tendsto (sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding c)) := by
  have hconst : Tendsto (fun _ : ℂ => xiRightCenteredZero q)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (xiRightCenteredZero q)) := tendsto_const_nhds
  have h := (hconst.add
    (tendsto_frankensteinCCMGammaCenteredResidueGauge
      (xiRightZeroCopyConjEquiv q).1.1)).pow 3
  have hdiv := h.div_const
    (((4 * (xiRightCenteredZero q).re ^ 3 : ℝ) : ℂ))
  have hsmul := hdiv.smul_const (routePJuliaSharedOrientationOrbitBlock c)
  have hconj :
      (((xiRightZeroCopyConjEquiv q).1.1 : ℂ) - 1 / 2) =
        (starRingEnd ℂ) (xiRightCenteredZero q) := by
    rw [← xiRightCenteredZero_eq_support_sub_half,
      xiRightCenteredZero_conj]
  have hpair :
      xiRightCenteredZero q +
          (((xiRightZeroCopyConjEquiv q).1.1 : ℂ) - 1 / 2) =
        (((2 * (xiRightCenteredZero q).re : ℝ) : ℂ)) := by
    rw [hconj]
    apply Complex.ext <;> simp
    ring_nf
  have hr : (xiRightCenteredZero q).re ≠ 0 :=
    (xiRightCenteredZero_re_pos q).ne'
  rw [sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding]
  convert hsmul using 1
  · funext v
    rfl
  · rw [hpair]
    congr 1
    push_cast
    field_simp [hr]
    ring_nf

/-- One source with independent Euler and Wold coordinates, before either completed residue. -/
def sourceHorizontalEulerWoldBigradedCompletedSource
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ)
    (s t : ℝ) (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((sourceHorizontalEulerOrderedLogDeformation N s +
      sourceHorizontalWoldOrderedPrimeDeformation N t) /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v

private theorem contDiffAt_sourceHorizontalEulerOrderedLogDeformation_three (N : ℕ) :
    ContDiffAt ℝ 3 (sourceHorizontalEulerOrderedLogDeformation N) 1 := by
  change ContDiffAt ℝ 3
    (fun s => primeEulerLogBelow s ((nthPrimeSubtype N : ℕ) + 1)) 1
  exact ((contDiffOn_primeEulerLogBelow 3
      ((nthPrimeSubtype N : ℕ) + 1)) 1
        (show (1 : ℝ) ∈ Ioi 0 by norm_num)).contDiffAt
    (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))

/-- Pure `(3,0)` source jet: exact negative Euler coefficient, Gamma variables still free. -/
theorem iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_euler
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (t : ℝ) (u v : ℂ) :
    iteratedDeriv 3
        (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 1 =
      (-sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3) •
        sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v := by
  have hs : ContDiffAt ℝ 3
      (fun s =>
        (sourceHorizontalEulerOrderedLogDeformation N s +
          sourceHorizontalWoldOrderedPrimeDeformation N t) /
            xiMassNthPrimeLogHeight N ^ 3) 1 :=
    ((contDiffAt_sourceHorizontalEulerOrderedLogDeformation_three N).add
      contDiffAt_const).div_const _
  rw [show (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
      c q N s t u v) =
      fun s =>
        ((sourceHorizontalEulerOrderedLogDeformation N s +
          sourceHorizontalWoldOrderedPrimeDeformation N t) /
            xiMassNthPrimeLogHeight N ^ 3) •
          sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v by rfl]
  rw [iteratedDeriv_smul_const hs,
    iteratedDeriv_div_const,
    iteratedDeriv_fun_add
      (contDiffAt_sourceHorizontalEulerOrderedLogDeformation_three N)
      contDiffAt_const,
    iteratedDeriv_sourceHorizontalEulerOrderedLogDeformation_three]
  norm_num [iteratedDeriv_const]

/-- Pure `(0,3)` source jet: exact positive Wold coefficient, Gamma variables still free. -/
theorem iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_wold
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (s : ℝ) (u v : ℂ) :
    iteratedDeriv 3
        (fun t => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 0 =
      ((∑ n ∈ Finset.range (N + 1),
          woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2) /
        xiMassNthPrimeLogHeight N ^ 3) •
        sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v := by
  have ht : ContDiffAt ℝ 3
      (fun t =>
        (sourceHorizontalEulerOrderedLogDeformation N s +
          sourceHorizontalWoldOrderedPrimeDeformation N t) /
            xiMassNthPrimeLogHeight N ^ 3) 0 :=
    (contDiffAt_const.add
      (contDiffAt_sourceHorizontalWoldOrderedPrimeDeformation N 3 0)).div_const _
  rw [show (fun t => sourceHorizontalEulerWoldBigradedCompletedSource
      c q N s t u v) =
      fun t =>
        ((sourceHorizontalEulerOrderedLogDeformation N s +
          sourceHorizontalWoldOrderedPrimeDeformation N t) /
            xiMassNthPrimeLogHeight N ^ 3) •
          sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v by rfl]
  rw [iteratedDeriv_smul_const ht,
    iteratedDeriv_div_const,
    iteratedDeriv_fun_add contDiffAt_const
      (contDiffAt_sourceHorizontalWoldOrderedPrimeDeformation N 3 0),
    iteratedDeriv_sourceHorizontalWoldOrderedPrimeDeformation_three]
  norm_num [iteratedDeriv_const]

/-- Intrinsic independence: the `(3,0)` Euler jet has zero third Wold derivative. -/
theorem iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_mixed_zero
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (u v : ℂ) :
    iteratedDeriv 3
      (fun t => iteratedDeriv 3
        (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 1) 0 = 0 := by
  rw [show (fun t => iteratedDeriv 3
      (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
        c q N s t u v) 1) =
      fun _ : ℝ =>
        (-sourceHorizontalEulerGammaCubicMoment N /
          xiMassNthPrimeLogHeight N ^ 3) •
          sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v by
    funext t
    exact iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_euler
      c q N t u v]
  simp [iteratedDeriv_const]

/-- Literal depth-`k+1` Euler logarithm summand; its denominator is what leaves `k²` after the
third source derivative. -/
def sourceHorizontalEulerLogDepthDeformation
    (p : Nat.Primes) (k : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) * s) / (k + 1 : ℝ)

/-- Each prime-power label survives with exact valuation-square coefficient. -/
theorem iteratedDeriv_sourceHorizontalEulerLogDepthDeformation_three
    (p : Nat.Primes) (k : ℕ) :
    iteratedDeriv 3 (sourceHorizontalEulerLogDepthDeformation p k) 1 =
      -(Real.log (p : ℝ) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 *
        ((p : ℝ)⁻¹) ^ (k + 1)) := by
  rw [show sourceHorizontalEulerLogDepthDeformation p k =
      fun s => Real.exp
        (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) * s) / (k + 1 : ℝ) by
    rfl]
  rw [iteratedDeriv_div_const, iteratedDeriv_exp_const_mul]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only
  have hnode :
      Real.exp (-(((k + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) * 1) =
        ((p : ℝ)⁻¹) ^ (k + 1) := by
    rw [mul_one, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp]
    rw [inv_pow]
  rw [hnode]
  field_simp [hk]
  push_cast
  ring_nf

/-- Positive Wold counterterm through the same ordered source clock. -/
def sourceHorizontalWoldCubicCountertermMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    woldCoeff 1 (nthPrimeSubtype n) * xiMassNthPrimeLogHeight n ^ 2

theorem sourceHorizontalEulerGammaCubicAtom_pos (p : Nat.Primes) :
    0 < sourceHorizontalEulerGammaCubicAtom p := by
  rw [sourceHorizontalEulerGammaCubicAtom]
  exact div_pos (cubicAnnulusPrimeCurrent_pos p.property) (by norm_num)

theorem sourceHorizontalEulerGammaCubicMoment_pos (N : ℕ) :
    0 < sourceHorizontalEulerGammaCubicMoment N := by
  rw [sourceHorizontalEulerGammaCubicMoment]
  exact Finset.sum_pos
    (fun n hn => sourceHorizontalEulerGammaCubicAtom_pos
      (nthPrimeSubtype n)) ⟨0, by simp⟩

theorem sourceHorizontalWoldCubicCountertermMoment_pos (N : ℕ) :
    0 < sourceHorizontalWoldCubicCountertermMoment N := by
  rw [sourceHorizontalWoldCubicCountertermMoment]
  apply Finset.sum_pos
  · intro n hn
    exact mul_pos (woldCoeff_pos 1 (nthPrimeSubtype n))
      (sq_pos_of_pos (xiMassNthPrimeLogHeight_pos n))
  · exact ⟨0, by simp⟩

theorem sourceHorizontalEulerGammaPolarSelectedCoefficient_neg (N : ℕ) :
    (-2 : ℝ) * sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3 < 0 := by
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num)
      (sourceHorizontalEulerGammaCubicMoment_pos N))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

theorem sourceHorizontalWoldGammaPolarSelectedCoefficient_pos (N : ℕ) :
    0 < (2 : ℝ) * sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3 := by
  exact div_pos
    (mul_pos (by norm_num) (sourceHorizontalWoldCubicCountertermMoment_pos N))
    (pow_pos (xiMassNthPrimeLogHeight_pos N) 3)

/-- Negative Euler pure jet before either completed Gamma residue. -/
def sourceHorizontalEulerGammaPolarPureSourceLeg
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (u v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (-sourceHorizontalEulerGammaCubicMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v

/-- Positive Wold pure jet before either completed Gamma residue. -/
def sourceHorizontalWoldGammaPolarPureSourceLeg
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (u v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (sourceHorizontalWoldCubicCountertermMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitKernel c q u v

def sourceHorizontalEulerGammaPolarPureFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (-sourceHorizontalEulerGammaCubicMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q v

def sourceHorizontalWoldGammaPolarPureFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (sourceHorizontalWoldCubicCountertermMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q v

/-- Negative Euler leg after both completed residues. -/
def sourceHorizontalEulerGammaPolarPureSelectedLanding
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-sourceHorizontalEulerGammaCubicMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding c

/-- Positive Wold leg after both completed residues. -/
def sourceHorizontalWoldGammaPolarPureSelectedLanding
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (sourceHorizontalWoldCubicCountertermMoment N /
    xiMassNthPrimeLogHeight N ^ 3) •
      sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding c

theorem tendsto_sourceHorizontalEulerGammaPolarPureSourceLeg_first
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Tendsto (fun u => sourceHorizontalEulerGammaPolarPureSourceLeg c q N u v)
      (nhdsWithin (criticalMellinXiPole q.1.1)
        ({criticalMellinXiPole q.1.1}ᶜ))
      (nhds (sourceHorizontalEulerGammaPolarPureFirstLanding c q N v)) := by
  simpa [sourceHorizontalEulerGammaPolarPureSourceLeg,
    sourceHorizontalEulerGammaPolarPureFirstLanding] using
    (tendsto_sourceHorizontalEulerWoldGammaPolarOrbitKernel_first c q v).const_smul
      (-sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3)

theorem tendsto_sourceHorizontalWoldGammaPolarPureSourceLeg_first
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Tendsto (fun u => sourceHorizontalWoldGammaPolarPureSourceLeg c q N u v)
      (nhdsWithin (criticalMellinXiPole q.1.1)
        ({criticalMellinXiPole q.1.1}ᶜ))
      (nhds (sourceHorizontalWoldGammaPolarPureFirstLanding c q N v)) := by
  simpa [sourceHorizontalWoldGammaPolarPureSourceLeg,
    sourceHorizontalWoldGammaPolarPureFirstLanding] using
    (tendsto_sourceHorizontalEulerWoldGammaPolarOrbitKernel_first c q v).const_smul
      (sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3)

theorem tendsto_sourceHorizontalEulerGammaPolarPureFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (sourceHorizontalEulerGammaPolarPureFirstLanding c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalEulerGammaPolarPureSelectedLanding c N)) := by
  change Tendsto (fun v =>
      (-sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3) •
          sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q v) _
    (nhds ((-sourceHorizontalEulerGammaCubicMoment N /
      xiMassNthPrimeLogHeight N ^ 3) •
        sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding c))
  exact
    (tendsto_sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q).const_smul
      (-sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3)

theorem tendsto_sourceHorizontalWoldGammaPolarPureFirstLanding
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (sourceHorizontalWoldGammaPolarPureFirstLanding c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalWoldGammaPolarPureSelectedLanding c N)) := by
  change Tendsto (fun v =>
      (sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3) •
          sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q v) _
    (nhds ((sourceHorizontalWoldCubicCountertermMoment N /
      xiMassNthPrimeLogHeight N ^ 3) •
        sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding c))
  exact
    (tendsto_sourceHorizontalEulerWoldGammaPolarOrbitFirstLanding c q).const_smul
      (sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3)

/-- Exact forced coefficient after completed Gamma/polar residue. -/
theorem sourceHorizontalEulerGammaPolarPureSelectedLanding_eq
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerGammaPolarPureSelectedLanding c N =
      (((-2 : ℝ) * sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c := by
  ext i j
  simp [sourceHorizontalEulerGammaPolarPureSelectedLanding,
    sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding]
  ring

/-- Exact positive counterterm coefficient after the same residue. -/
theorem sourceHorizontalWoldGammaPolarPureSelectedLanding_eq
    (c : ℂ) (N : ℕ) :
    sourceHorizontalWoldGammaPolarPureSelectedLanding c N =
      (((2 : ℝ) * sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c := by
  ext i j
  simp [sourceHorizontalWoldGammaPolarPureSelectedLanding,
    sourceHorizontalEulerWoldGammaPolarOrbitSelectedLanding]
  ring

/-- The pure Euler source jet is definitionally the transported negative leg. -/
theorem sourceHorizontalEulerGammaPolarPureSourceLeg_eq_partialThirdJet
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (t : ℝ) (u v : ℂ) :
    sourceHorizontalEulerGammaPolarPureSourceLeg c q N u v =
      iteratedDeriv 3
        (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 1 := by
  rw [iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_euler]
  rfl

/-- The pure Wold source jet is definitionally the transported positive leg. -/
theorem sourceHorizontalWoldGammaPolarPureSourceLeg_eq_partialThirdJet
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (s : ℝ) (u v : ℂ) :
    sourceHorizontalWoldGammaPolarPureSourceLeg c q N u v =
      iteratedDeriv 3
        (fun t => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 0 := by
  rw [iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_wold]
  rfl

/-- Three signed outer legs after first residue: unchanged BV endpoint, negative Euler jet,
positive Wold counterterm. The external product is introduced only after intrinsic source
bigrading has been proved by the mixed-jet theorem. -/
def sourceHorizontalEulerWoldKreinFirstLandingBundle
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N v,
    sourceHorizontalEulerGammaPolarPureFirstLanding c q N v,
    sourceHorizontalWoldGammaPolarPureFirstLanding c q N v]

/-- Same three legs on the selected Xi fibre. -/
def sourceHorizontalEulerWoldKreinSelectedLandingBundle
    (c : ℂ) (_q : XiRightZeroCopy) (N : ℕ) :
    Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![sourceHorizontalWoldBVKreinSignedLanding c N,
    sourceHorizontalEulerGammaPolarPureSelectedLanding c N,
    sourceHorizontalWoldGammaPolarPureSelectedLanding c N]

/-- One selected completed residue transports all three independent signed Krein legs. -/
theorem tendsto_sourceHorizontalEulerWoldKreinFirstLandingBundle
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (sourceHorizontalEulerWoldKreinFirstLandingBundle c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · simpa [sourceHorizontalEulerWoldKreinFirstLandingBundle,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle] using
      tendsto_frankensteinCCMGammaWoldBVKreinSignedSourceBlock c q N
  · simpa [sourceHorizontalEulerWoldKreinFirstLandingBundle,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle] using
      tendsto_sourceHorizontalEulerGammaPolarPureFirstLanding c q N
  · simpa [sourceHorizontalEulerWoldKreinFirstLandingBundle,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle] using
      tendsto_sourceHorizontalWoldGammaPolarPureFirstLanding c q N

/-- Projection to the BV component is exactly the pre-existing endpoint-defect landing. -/
@[simp] theorem sourceHorizontalEulerWoldKreinSelectedLandingBundle_bv
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N 0 =
      sourceHorizontalWoldBVKreinSignedLanding c N := by
  rfl

/-- Actual copy summation restores exact analytic multiplicity componentwise. -/
theorem sourceHorizontalEulerWoldKreinSelectedLandingBundle_actualFiber_sum
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle c r.1 N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N := by
  rw [show (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle c r.1 N) =
      Fintype.card (XiRightSupportFiber q) •
        sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N by
    simp [sourceHorizontalEulerWoldKreinSelectedLandingBundle]]
  rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- Linear grade-forgetting is formed only after both residue proofs. -/
def sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding
    (c : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  sourceHorizontalEulerGammaPolarPureSelectedLanding c N +
    sourceHorizontalWoldGammaPolarPureSelectedLanding c N

theorem sourceHorizontalWoldCubicCountertermMoment_add_defect (N : ℕ) :
    sourceHorizontalEulerGammaCubicMoment N =
      sourceHorizontalWoldCubicCountertermMoment N +
        sourceHorizontalEulerGammaWoldCubicDefectMoment N := by
  simpa [sourceHorizontalWoldCubicCountertermMoment] using
    sourceHorizontalEulerGammaCubicMoment_eq_wold_add_defect N

/-- Exact hostile classification: faithful linear addition sees only the negative summable
Euler--Wold defect. -/
theorem sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_eq_defect
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N =
      (((-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c := by
  rw [sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding,
    sourceHorizontalEulerGammaPolarPureSelectedLanding_eq,
    sourceHorizontalWoldGammaPolarPureSelectedLanding_eq,
    sourceHorizontalWoldCubicCountertermMoment_add_defect]
  ext i j
  simp
  ring

theorem sourceHorizontalEulerGammaWoldCubicDefectMoment_pos (N : ℕ) :
    0 < sourceHorizontalEulerGammaWoldCubicDefectMoment N := by
  rw [sourceHorizontalEulerGammaWoldCubicDefectMoment]
  exact Finset.sum_pos
    (fun n hn => sourceHorizontalEulerGammaWoldCubicDefect_pos
      (nthPrimeSubtype n)) ⟨0, by simp⟩

/-- Finite-clock combined environment corner is strictly negative, so transport is nontrivial. -/
theorem sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_environment_re_neg
    (c : ℂ) (N : ℕ) :
    (sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N 1 1).re < 0 := by
  rw [sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_eq_defect,
    routePJuliaSharedOrientationOrbitBlock_eq_diagonal]
  simp
  have hD := sourceHorizontalEulerGammaWoldCubicDefectMoment_pos N
  have hH := xiMassNthPrimeLogHeight_pos N
  rw [Complex.div_re]
  norm_num
  norm_cast
  have hnum : 0 <
      2 * sourceHorizontalEulerGammaWoldCubicDefectMoment N *
        xiMassNthPrimeLogHeight N ^ 3 := by positivity
  have hden : 0 <
      (xiMassNthPrimeLogHeight N * xiMassNthPrimeLogHeight N) ^ 3 := by
    positivity
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum) hden) (by norm_num)

theorem sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_ne_zero
    (c : ℂ) (N : ℕ) :
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hzero
  have hneg :=
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_environment_re_neg c N
  simp at hentry
  linarith

/-- Despite finite nontriviality, every matrix entry vanishes on the intrinsic prime clock. -/
theorem tendsto_sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_zero
    (c : ℂ) :
    Tendsto (fun N =>
      sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N)
      atTop (nhds 0) := by
  rw [show (fun N =>
      sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N) =
      fun N =>
        (((-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
          xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
            routePJuliaSharedOrientationOrbitBlock c by
    funext N
    exact sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_eq_defect c N]
  have hreal :=
    tendsto_sourceHorizontalEulerGammaWoldCubicDefectMoment_normalized_zero.const_mul (-2)
  have hreal' : Tendsto (fun N =>
      (-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ 3) atTop (nhds 0) := by
    convert hreal using 1
    · funext N
      ring
    · norm_num
  have hcomplex := hreal'.ofReal
  simpa using hcomplex.smul_const (routePJuliaSharedOrientationOrbitBlock c)

/-- Capstone: literal `k²` depth labels, intrinsic Euler/Wold bigrading, both completed residues,
the unchanged BV endpoint leg, four orientations, actual Xi-copy multiplicity, and the sharp
finite/noncofinal defect classification hold simultaneously. -/

theorem sourceHorizontalEulerWoldIndependentKreinXiResidueTransport
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) (u v : ℂ) :
    (∀ (p : Nat.Primes) (k : ℕ),
      iteratedDeriv 3 (sourceHorizontalEulerLogDepthDeformation p k) 1 =
        -(Real.log (p : ℝ) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 *
          ((p : ℝ)⁻¹) ^ (k + 1))) ∧
    sourceHorizontalEulerGammaPolarPureSourceLeg c q N u v =
      iteratedDeriv 3
        (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s 0 u v) 1 ∧
    sourceHorizontalWoldGammaPolarPureSourceLeg c q N u v =
      iteratedDeriv 3
        (fun t => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N 1 t u v) 0 ∧
    iteratedDeriv 3
      (fun t => iteratedDeriv 3
        (fun s => sourceHorizontalEulerWoldBigradedCompletedSource
          c q N s t u v) 1) 0 = 0 ∧
    sourceHorizontalEulerGammaPolarPureSelectedLanding c N =
      (((-2 : ℝ) * sourceHorizontalEulerGammaCubicMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c ∧
    sourceHorizontalWoldGammaPolarPureSelectedLanding c N =
      (((2 : ℝ) * sourceHorizontalWoldCubicCountertermMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c ∧
    Tendsto (sourceHorizontalEulerWoldKreinFirstLandingBundle c q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N)) ∧
    sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N 0 =
      sourceHorizontalWoldBVKreinSignedLanding c N ∧
    (∑ r : XiRightSupportFiber q,
      sourceHorizontalEulerWoldKreinSelectedLandingBundle c r.1 N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalEulerWoldKreinSelectedLandingBundle c q N ∧
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N =
      (((-2 : ℝ) * sourceHorizontalEulerGammaWoldCubicDefectMoment N /
        xiMassNthPrimeLogHeight N ^ 3 : ℝ) : ℂ) •
          routePJuliaSharedOrientationOrbitBlock c ∧
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c N ≠ 0 ∧
    Tendsto (fun M =>
      sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding c M)
      atTop (nhds 0) := by
  refine ⟨?_,
    sourceHorizontalEulerGammaPolarPureSourceLeg_eq_partialThirdJet c q N 0 u v,
    sourceHorizontalWoldGammaPolarPureSourceLeg_eq_partialThirdJet c q N 1 u v,
    iteratedDeriv_sourceHorizontalEulerWoldBigradedCompletedSource_mixed_zero c q N u v,
    sourceHorizontalEulerGammaPolarPureSelectedLanding_eq c N,
    sourceHorizontalWoldGammaPolarPureSelectedLanding_eq c N,
    tendsto_sourceHorizontalEulerWoldKreinFirstLandingBundle c q N,
    sourceHorizontalEulerWoldKreinSelectedLandingBundle_bv c q N,
    sourceHorizontalEulerWoldKreinSelectedLandingBundle_actualFiber_sum c q N,
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_eq_defect c N,
    sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_ne_zero c N,
    tendsto_sourceHorizontalEulerWoldGammaPolarCombinedSelectedLanding_zero c⟩
  intro p k
  exact iteratedDeriv_sourceHorizontalEulerLogDepthDeformation_three p k

end

end RHTower
