import GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics

/-!
# Navier--Stokes finite exponential-tilt convexity

Finite exact analogue of the variance argument in Appendix C of the Navier--Stokes paper.
It upgrades the corpus exponential-tilt derivative calculus to strict positivity and proves the
doubled log-partition gap used there is positive away from the origin.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesFiniteTiltConvexity

open Finset Set

variable {n : ℕ}

/-- Logarithm of the finite exponential partition function. -/
noncomputable def finiteLogPartition (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  Real.log (finiteExpPartition w r t)

/-- The self-covariance is a weighted sum of squares. -/
theorem finiteTiltCovariance_self_eq_sum_sq {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    finiteTiltCovariance w r r t =
      ∑ x, finiteExponentialTilt w r t x *
        (r x - finiteTiltScoreMean w r t) ^ (2 : ℕ) := by
  rw [finiteTiltCovariance_eq_centered (r := r) (f := r) hw hsum t]
  apply Finset.sum_congr rfl
  intro x _
  simp only [finiteTiltExpectation, finiteTiltScoreMean, pow_two]
  ring

/-- Every coordinate of a strictly positive exponential tilt stays strictly positive. -/
theorem finiteExponentialTilt_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) (x : Fin n) :
    0 < finiteExponentialTilt w r t x := by
  unfold finiteExponentialTilt
  exact div_pos (mul_pos (hw x) (Real.exp_pos _))
    (finiteExpPartition_pos (fun y => (hw y).le) hsum t)

/-- A nonconstant score has strictly positive variance under every positive finite tilt. -/
theorem finiteTiltCovariance_self_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) {a b : Fin n} (hab : r a ≠ r b) (t : ℝ) :
    0 < finiteTiltCovariance w r r t := by
  rw [finiteTiltCovariance_self_eq_sum_sq (fun x => (hw x).le) hsum]
  have haway : r a ≠ finiteTiltScoreMean w r t ∨
      r b ≠ finiteTiltScoreMean w r t := by
    by_contra h
    push Not at h
    exact hab (h.1.trans h.2.symm)
  refine Finset.sum_pos' (fun x _ => mul_nonneg
    (finiteExponentialTilt_pos hw hsum t x).le (sq_nonneg _)) ?_
  rcases haway with ha | hb
  · exact ⟨a, Finset.mem_univ a,
      mul_pos (finiteExponentialTilt_pos hw hsum t a) (sq_pos_of_ne_zero (sub_ne_zero.mpr ha))⟩
  · exact ⟨b, Finset.mem_univ b,
      mul_pos (finiteExponentialTilt_pos hw hsum t b) (sq_pos_of_ne_zero (sub_ne_zero.mpr hb))⟩

/-- Derivative of the log partition is the tilted score mean. -/
theorem hasDerivAt_finiteLogPartition {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) :
    HasDerivAt (finiteLogPartition w r) (finiteTiltScoreMean w r t) t := by
  have hZ : finiteExpPartition w r t ≠ 0 := (finiteExpPartition_pos hw hsum t).ne'
  have hlog := (hasDerivAt_finiteExpPartition w r t).log hZ
  have hmean : finiteTiltScoreMean w r t =
      (∑ x, w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
    unfold finiteTiltScoreMean finiteExponentialTilt
    calc
      ∑ x, w x * Real.exp (t * r x) / finiteExpPartition w r t * r x =
          ∑ x, (w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = _ := (Finset.sum_div Finset.univ
        (fun x => w x * r x * Real.exp (t * r x)) (finiteExpPartition w r t)).symm
  change HasDerivAt (fun s => Real.log (finiteExpPartition w r s)) _ t
  rw [hmean]
  exact hlog

/-- Derivative of the tilted score mean is its variance. -/
theorem hasDerivAt_finiteTiltScoreMean {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) :
    HasDerivAt (finiteTiltScoreMean w r)
      (finiteTiltCovariance w r r t) t := by
  change HasDerivAt (finiteTiltExpectation w r r) (finiteTiltCovariance w r r t) t
  exact hasDerivAt_finiteTiltExpectation (r := r) (f := r) hw hsum t

/-- For a nonconstant score and positive base weights, tilted score mean is strictly increasing. -/
theorem finiteTiltScoreMean_strictMono {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) {a b : Fin n} (hab : r a ≠ r b) :
    StrictMono (finiteTiltScoreMean w r) := by
  apply strictMono_of_hasDerivAt_pos
  · exact hasDerivAt_finiteTiltScoreMean (fun x => (hw x).le) hsum
  · exact finiteTiltCovariance_self_pos hw hsum hab

/-- Difference between the log partition at doubled and ordinary tilt. -/
noncomputable def doubledLogPartitionGap (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  finiteLogPartition w r (2 * t) - 2 * finiteLogPartition w r t

/-- Exact derivative of the doubled log-partition gap. -/
theorem hasDerivAt_doubledLogPartitionGap {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) :
    HasDerivAt (doubledLogPartitionGap w r)
      (2 * (finiteTiltScoreMean w r (2 * t) - finiteTiltScoreMean w r t)) t := by
  have hdouble : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have hfirst := HasDerivAt.scomp (𝕜 := ℝ) t
    (hasDerivAt_finiteLogPartition (r := r) hw hsum (2 * t)) hdouble
  have hsecond := (hasDerivAt_finiteLogPartition (r := r) hw hsum t).const_mul 2
  have hsource := hfirst.sub hsecond
  change HasDerivAt
    (fun s => finiteLogPartition w r (2 * s) - 2 * finiteLogPartition w r s)
    (2 • finiteTiltScoreMean w r (2 * t) - 2 * finiteTiltScoreMean w r t) t at hsource
  change HasDerivAt
    (fun s => finiteLogPartition w r (2 * s) - 2 * finiteLogPartition w r s) _ t
  convert hsource using 1
  simp only [two_smul]
  ring

/-- The doubled gap has positive derivative at every positive tilt. -/
theorem doubledLogPartitionGap_deriv_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) {a b : Fin n} (hab : r a ≠ r b) {t : ℝ} (ht : 0 < t) :
    0 < deriv (doubledLogPartitionGap w r) t := by
  rw [(hasDerivAt_doubledLogPartitionGap (fun x => (hw x).le) hsum t).deriv]
  have hmean := finiteTiltScoreMean_strictMono hw hsum hab
  have : finiteTiltScoreMean w r t < finiteTiltScoreMean w r (2 * t) :=
    hmean (by linarith)
  linarith

/-- The doubled log-partition gap vanishes at zero. -/
theorem doubledLogPartitionGap_zero {w r : Fin n → ℝ} (hsum : ∑ x, w x = 1) :
    doubledLogPartitionGap w r 0 = 0 := by
  simp [doubledLogPartitionGap, finiteLogPartition, finiteExpPartition_zero, hsum]

/-- Strictly positive finite analogue of the Appendix C tilted log-partition inequality. -/
theorem doubledLogPartitionGap_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) {a b : Fin n} (hab : r a ≠ r b) {t : ℝ} (ht : 0 < t) :
    0 < doubledLogPartitionGap w r t := by
  have hcontinuous : Continuous (doubledLogPartitionGap w r) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hasDerivAt_doubledLogPartitionGap (fun x => (hw x).le) hsum s).continuousAt
  have hmono : StrictMonoOn (doubledLogPartitionGap w r) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcontinuous.continuousOn
    intro s hs
    have hspos : 0 < s := by simpa using hs
    exact doubledLogPartitionGap_deriv_pos hw hsum hab hspos
  rw [← doubledLogPartitionGap_zero (w := w) (r := r) hsum]
  exact hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht

end GaloisForLFunctions.HTGeometry.NavierStokesFiniteTiltConvexity
