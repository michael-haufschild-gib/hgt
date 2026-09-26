import GaloisForLFunctions.RHTower.ThetaCuspPrimeArchSourceEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Noether current of the literal prime shifts

The prime action couples `p(x)` to `q(x + log n)` with its literal
von Mangoldt coefficient. Reciprocal scaling is an exact symmetry.
Its localized first variation is the difference of the gauge parameter
at the two ends of this arithmetic link.

For continuous theta sources the corresponding current crosses the whole
interval of the shift. Its derivative is the forward source minus its
reflected adjoint. The complete theta source equation identifies the
infinite prime divergence with Gamma and pole exchange, including the
nonzero multiplication term `2 x k(x)^2`.
-/

open MeasureTheory

noncomputable section

namespace RHTower.ThetaSourceWard

/-- The bilocal action density of one literal prime-power shift. -/
def primeShiftActionDensity (n : ℕ) (p q : ℝ → ℂ) (x : ℝ) : ℂ :=
  primeCoefficient n * p x * q (x + Real.log n)

theorem primeShiftActionDensity_symmetry (n : ℕ) (p q : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    primeShiftActionDensity n (fun y => Complex.exp (-s) * p y)
        (fun y => Complex.exp s * q y) x = primeShiftActionDensity n p q x := by
  unfold primeShiftActionDensity
  calc
    _ = (Complex.exp (-s) * Complex.exp s) *
        (primeCoefficient n * p x * q (x + Real.log n)) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp

/-- An actual complex first variation under a position-dependent reciprocal scaling. -/
theorem hasDerivAt_primeShiftActionDensity_localScaling
    (n : ℕ) (p q chi : ℝ → ℂ) (x : ℝ) :
    HasDerivAt (fun e : ℂ => primeShiftActionDensity n
      (fun y => Complex.exp (-(e * chi y)) * p y)
      (fun y => Complex.exp (e * chi y) * q y) x)
      ((chi (x + Real.log n) - chi x) * primeShiftActionDensity n p q x) 0 := by
  have hp := (((hasDerivAt_id (0 : ℂ)).mul_const (chi x)).neg.cexp).mul_const (p x)
  have hq := (((hasDerivAt_id (0 : ℂ)).mul_const (chi (x + Real.log n))).cexp).mul_const
    (q (x + Real.log n))
  convert! (hp.const_mul (primeCoefficient n)).mul hq using 1
  simp [primeShiftActionDensity]
  ring

/-- Action of finitely many arithmetic shifts on a finite observation interval. -/
def finitePrimeShiftAction (ns : Finset ℕ) (p q : ℝ → ℂ) (l r : ℝ) : ℂ :=
  ∫ x in l..r, ∑ n ∈ ns, primeShiftActionDensity n p q x

theorem finitePrimeShiftAction_symmetry
    (ns : Finset ℕ) (p q : ℝ → ℂ) (s : ℂ) (l r : ℝ) :
    finitePrimeShiftAction ns (fun y => Complex.exp (-s) * p y)
        (fun y => Complex.exp s * q y) l r = finitePrimeShiftAction ns p q l r := by
  simp only [finitePrimeShiftAction, primeShiftActionDensity_symmetry]

/-- Transposing one prime link reverses its shift under the bilinear integral pairing. -/
theorem primeShiftActionDensity_transpose (n : ℕ) (p q : ℝ → ℂ) :
    (∫ x : ℝ, primeShiftActionDensity n p q x) =
      ∫ x : ℝ, primeCoefficient n * p (x - Real.log n) * q x := by
  simpa only [primeShiftActionDensity, add_sub_cancel_right] using
    MeasureTheory.integral_add_right_eq_self
      (fun x : ℝ => primeCoefficient n * p (x - Real.log n) * q x) (Real.log n)

/-- The full arithmetic action retains the same reciprocal symmetry. -/
def fullPrimeShiftAction (p q : ℝ → ℂ) (l r : ℝ) : ℂ :=
  ∫ x in l..r, ∑' n : ℕ, primeShiftActionDensity n p q x

theorem fullPrimeShiftAction_symmetry (p q : ℝ → ℂ) (s : ℂ) (l r : ℝ) :
    fullPrimeShiftAction (fun y => Complex.exp (-s) * p y)
        (fun y => Complex.exp s * q y) l r = fullPrimeShiftAction p q l r := by
  simp only [fullPrimeShiftAction, primeShiftActionDensity_symmetry]

/-- On actual theta sources the full action density is the convergent prime operator pairing. -/
theorem fullPrimeShiftAction_source_density (S T : ThetaSource) (x : ℝ) :
    (∑' n : ℕ, primeShiftActionDensity n (fun y => (T.k y : ℂ))
      (fun y => (S.k y : ℂ)) x) = (T.k x : ℂ) * fullPrimeSource S x := by
  rw [fullPrimeSource, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold primeShiftActionDensity primeSourceTerm
  ring

/-- Density along a link crossing the current observation point. -/
def primeShiftLinkDensity (S T : ThetaSource) (n : ℕ) (y : ℝ) : ℂ :=
  (S.k y : ℂ) * (T.k (y - Real.log n) : ℂ)

theorem continuous_primeShiftLinkDensity (S T : ThetaSource) (n : ℕ) :
    Continuous (primeShiftLinkDensity S T n) := by
  exact (Complex.continuous_ofReal.comp S.cont).mul
    (Complex.continuous_ofReal.comp (T.cont.comp (continuous_id.sub continuous_const)))

/-- The nonlocal Noether current integrates every point crossed by the arithmetic link. -/
def primeShiftNoetherCurrent (S T : ThetaSource) (n : ℕ) (x : ℝ) : ℂ :=
  primeCoefficient n * ∫ y in x..x + Real.log n, primeShiftLinkDensity S T n y

/-- The current derivative is the forward prime source minus the reflected adjoint source. -/
theorem hasDerivAt_primeShiftNoetherCurrent (S T : ThetaSource) (n : ℕ) (x : ℝ) :
    HasDerivAt (primeShiftNoetherCurrent S T n)
      ((T.k x : ℂ) * primeSourceTerm S n x -
        (S.k x : ℂ) * primeSourceTerm T n (-x)) x := by
  let f := primeShiftLinkDensity S T n
  have hc : Continuous f := continuous_primeShiftLinkDensity S T n
  have hd (u : ℝ) : HasDerivAt (fun b => ∫ y in (0 : ℝ)..b, f y) (f u) u :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := (((hd (x + Real.log n)).scomp x ((hasDerivAt_id x).add_const (Real.log n))).sub
    (hd x)).const_mul (primeCoefficient n)
  have hf : (fun b => primeCoefficient n *
      ((∫ y in (0 : ℝ)..b + Real.log n, f y) - ∫ y in (0 : ℝ)..b, f y)) =
        primeShiftNoetherCurrent S T n := by
    funext b
    rw [intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 (b + Real.log n)) (hc.intervalIntegrable 0 b)]
    rfl
  have he : T.k (x - Real.log n) = T.k (-x + Real.log n) := by
    rw [← T.even' (x - Real.log n)]
    congr 1
    ring
  convert! h using 1
  · exact hf.symm
  · simp only [f, primeShiftLinkDensity, add_sub_cancel_right, one_smul, primeSourceTerm, he]
    ring

def finitePrimeShiftSource (S : ThetaSource) (ns : Finset ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ ns, primeSourceTerm S n x

def finitePrimeShiftNoetherCurrent (S T : ThetaSource) (ns : Finset ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ ns, primeShiftNoetherCurrent S T n x

theorem hasDerivAt_finitePrimeShiftNoetherCurrent
    (S T : ThetaSource) (ns : Finset ℕ) (x : ℝ) :
    HasDerivAt (finitePrimeShiftNoetherCurrent S T ns)
      ((T.k x : ℂ) * finitePrimeShiftSource S ns x -
        (S.k x : ℂ) * finitePrimeShiftSource T ns (-x)) x := by
  convert! HasDerivAt.fun_sum (fun n (_ : n ∈ ns) =>
    hasDerivAt_primeShiftNoetherCurrent S T n x) using 1
  simp only [finitePrimeShiftSource, Finset.sum_sub_distrib, Finset.mul_sum]

/-- The full prime divergence is defined by the convergent literal prime sources. -/
def fullPrimeShiftWardDivergence (S T : ThetaSource) (x : ℝ) : ℂ :=
  (T.k x : ℂ) * fullPrimeSource S x - (S.k x : ℂ) * fullPrimeSource T (-x)

/-- Its exact coefficient expansion retains every prime-power term. -/
theorem fullPrimeShiftWardDivergence_eq_tsum (S T : ThetaSource) (x : ℝ) :
    fullPrimeShiftWardDivergence S T x =
      ∑' n : ℕ, ((T.k x : ℂ) * primeSourceTerm S n x -
        (S.k x : ℂ) * primeSourceTerm T n (-x)) := by
  rw [fullPrimeShiftWardDivergence, fullPrimeSource, fullPrimeSource,
    ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_sub ((summable_primeSourceTerm S x).mul_left _)
      ((summable_primeSourceTerm T (-x)).mul_left _)]

/-- Gamma and pole channels of the completed arithmetic source. -/
def thetaArchimedeanShiftSource (x : ℝ) : ℂ :=
  gammaSource x + polarSource (1 / 2) x + polarSource (-1 / 2) x

/-- The complete source equation yields a literal arithmetic Ward balance.
The multiplication term survives reflection and is not a conserved positive energy. -/
theorem completeTheta_primeShiftWard_balance (x : ℝ) :
    fullPrimeShiftWardDivergence thetaCuspTiltSource thetaCuspTiltSource x =
      (thetaCuspFullSource x : ℂ) *
        (thetaArchimedeanShiftSource x - thetaArchimedeanShiftSource (-x)) -
          2 * (x : ℂ) * (thetaCuspFullSource x : ℂ) ^ 2 := by
  have hp := complete_theta_source_equation x
  have hm := complete_theta_source_equation (-x)
  rw [thetaCuspFullSource_neg, Complex.ofReal_neg] at hm
  unfold fullPrimeShiftWardDivergence thetaArchimedeanShiftSource
  simp only [thetaCuspTiltSource_k]
  linear_combination (thetaCuspFullSource x : ℂ) * (hm - hp)

/-- Reversing all shift terms while retaining the original multiplication term. -/
def thetaReflectedShiftResidual (x : ℝ) : ℂ :=
  -archConstant * (thetaCuspFullSource x : ℂ) +
    thetaArchimedeanShiftSource (-x) - fullPrimeSource thetaCuspTiltSource (-x) -
      (x : ℂ) * (thetaCuspFullSource x : ℂ)

/-- The same theta source does not annihilate the shift-reversed equation. -/
theorem thetaReflectedShiftResidual_eq (x : ℝ) :
    thetaReflectedShiftResidual x = -2 * (x : ℂ) * (thetaCuspFullSource x : ℂ) := by
  have h := complete_theta_source_equation (-x)
  rw [thetaCuspFullSource_neg, Complex.ofReal_neg] at h
  unfold thetaReflectedShiftResidual thetaArchimedeanShiftSource
  linear_combination h

theorem thetaReflectedShiftResidual_eq_zero_iff (x : ℝ) :
    thetaReflectedShiftResidual x = 0 ↔ x = 0 := by
  have hp : 0 < thetaCuspFullSource x := thetaCuspTiltSource.pos x
  have hn : (thetaCuspFullSource x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [thetaReflectedShiftResidual_eq]
  simp [mul_eq_zero, hn]

theorem thetaReflectedShiftResidual_not_identically_zero :
    ¬ ∀ x : ℝ, thetaReflectedShiftResidual x = 0 := by
  intro h
  exact one_ne_zero ((thetaReflectedShiftResidual_eq_zero_iff 1).mp (h 1))

end RHTower.ThetaSourceWard
