import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedOrientedWallLightIncidence

/-!
# Quadratic jet of matched CCM wall-light incidence

The literal Suzuki light imbalance and the matched polar sine profile both vanish at spectral
center but have strictly positive first jets at every prime-power wall.  Their product therefore
has exact positive quadratic contact.  This identifies a jet-level source channel that survives
the center-reserve obstruction and explains why the causal Gamma entry first appears with a
quadratic spectral factor.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section
namespace RHTower

/-- Second frequency jet of the odd matched radial sine profile. -/
def ccmActualHeadMatchedSinePhaseSecondJet (n : ℕ) (xi : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    -8 * Real.pi ^ 2 * r ^ 2 * Real.exp (Real.log n / 2) *
      Real.sinh (r / 2) * Real.sin (2 * Real.pi * r * xi)

theorem hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet_integrand
    (n : ℕ) (r xi : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
          Real.cos (2 * Real.pi * r * x))
      (-8 * Real.pi ^ 2 * r ^ 2 * Real.exp (Real.log n / 2) *
        Real.sinh (r / 2) * Real.sin (2 * Real.pi * r * xi)) xi := by
  have hlin : HasDerivAt (fun x : ℝ => 2 * Real.pi * r * x)
      (2 * Real.pi * r) xi := by
    simpa using (hasDerivAt_id xi).const_mul (2 * Real.pi * r)
  have hbase := hlin.cos.const_mul
    (4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2))
  apply hbase.congr_deriv
  ring

theorem hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet
    (n : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedSinePhaseFirstJet n)
      (ccmActualHeadMatchedSinePhaseSecondJet n xi) xi := by
  let rho := ccmActualHeadMatchedPrimePolarRadius n
  let F : ℝ → ℝ → ℝ := fun x r =>
    4 * Real.pi * r * Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      Real.cos (2 * Real.pi * r * x)
  let F' : ℝ → ℝ → ℝ := fun x r =>
    -8 * Real.pi ^ 2 * r ^ 2 * Real.exp (Real.log n / 2) *
      Real.sinh (r / 2) * Real.sin (2 * Real.pi * r * x)
  let bound : ℝ → ℝ := fun r =>
    |-8 * Real.pi ^ 2 * r ^ 2 * Real.exp (Real.log n / 2) *
      Real.sinh (r / 2)|
  have hFmeas : ∀ᶠ x : ℝ in nhds xi,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc (0 : ℝ) rho)) :=
    Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (F x)).aestronglyMeasurable
  have hFint : IntervalIntegrable (F xi) volume 0 rho :=
    (by fun_prop : Continuous (F xi)).intervalIntegrable _ _
  have hF'meas : AEStronglyMeasurable (F' xi)
      (volume.restrict (uIoc (0 : ℝ) rho)) :=
    (by fun_prop : Continuous (F' xi)).aestronglyMeasurable
  have hbound : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ), ‖F' x r‖ ≤ bound r := by
    filter_upwards with r
    intro hr x hx
    dsimp only [F', bound]
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
  have hboundint : IntervalIntegrable bound volume 0 rho :=
    (by fun_prop : Continuous bound).intervalIntegrable _ _
  have hdiff : ∀ᵐ r : ℝ ∂volume, r ∈ uIoc (0 : ℝ) rho →
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun y => F y r) (F' x r) x := by
    filter_upwards with r
    intro hr x hx
    simpa only [F, F'] using
      hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet_integrand n r x
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (x₀ := xi)
    (show (Set.univ : Set ℝ) ∈ nhds xi from univ_mem)
    hFmeas hFint hF'meas hbound hboundint hdiff).2
  unfold ccmActualHeadMatchedSinePhaseFirstJet
    ccmActualHeadMatchedSinePhaseSecondJet
  simpa only [F, F', rho] using hmain

@[simp] theorem ccmActualHeadMatchedSinePhaseSecondJet_zero
    (n : ℕ) :
    ccmActualHeadMatchedSinePhaseSecondJet n 0 = 0 := by
  simp [ccmActualHeadMatchedSinePhaseSecondJet]

theorem hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet_zero
    (n : ℕ) :
    HasDerivAt (ccmActualHeadMatchedSinePhaseFirstJet n) 0 0 := by
  simpa using hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet n 0

/-- First jet of literal wall-light imbalance. -/
def ccmActualHeadMatchedWallLightImbalanceFirstJet
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  criticalMellinAtomWeight n *
    (2 * Real.pi * Real.log n) *
      Real.cos (2 * Real.pi * Real.log n * xi)

theorem hasDerivAt_ccmActualHeadMatchedWallLightImbalance
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedWallLightImbalance p e)
      (ccmActualHeadMatchedWallLightImbalanceFirstJet p e xi) xi := by
  let n := xiGammaEulerValuationNat (p, e)
  let a := 2 * Real.pi * Real.log n
  have hfun : ccmActualHeadMatchedWallLightImbalance p e =
      fun x : ℝ => criticalMellinAtomWeight n * Real.sin (a * x) := by
    funext x
    rw [ccmActualHeadMatchedWallLightImbalance_eq]
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => a * x) a xi := by
    simpa using (hasDerivAt_id xi).const_mul a
  have h := hlin.sin.const_mul (criticalMellinAtomWeight n)
  apply h.congr_deriv
  simp only [ccmActualHeadMatchedWallLightImbalanceFirstJet, n, a]
  ring

@[simp] theorem ccmActualHeadMatchedWallLightImbalanceFirstJet_zero
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedWallLightImbalanceFirstJet p e 0 =
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        (2 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e))) := by
  simp [ccmActualHeadMatchedWallLightImbalanceFirstJet]

theorem hasDerivAt_ccmActualHeadMatchedWallLightImbalanceFirstJet_zero
    (p : Nat.Primes) (e : ℕ) :
    HasDerivAt (ccmActualHeadMatchedWallLightImbalanceFirstJet p e) 0 0 := by
  let n := xiGammaEulerValuationNat (p, e)
  let a := 2 * Real.pi * Real.log n
  unfold ccmActualHeadMatchedWallLightImbalanceFirstJet
  dsimp only [n, a]
  have hlin : HasDerivAt (fun x : ℝ => a * x) a 0 := by
    simpa using (hasDerivAt_id 0).const_mul a
  have h := hlin.cos.const_mul (criticalMellinAtomWeight n * a)
  simpa [a] using h

/-- Product of literal wall-light imbalance with the matched polar orientation profile. -/
def ccmActualHeadMatchedWallLightOrientedCoupling
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  ccmActualHeadMatchedWallLightImbalance p e xi *
    ccmActualHeadMatchedSinePhaseProfile n xi

def ccmActualHeadMatchedWallLightOrientedCouplingFirstJet
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  ccmActualHeadMatchedWallLightImbalanceFirstJet p e xi *
      ccmActualHeadMatchedSinePhaseProfile n xi +
    ccmActualHeadMatchedWallLightImbalance p e xi *
      ccmActualHeadMatchedSinePhaseFirstJet n xi

theorem hasDerivAt_ccmActualHeadMatchedWallLightOrientedCoupling
    (p : Nat.Primes) (e : ℕ) (xi : ℝ) :
    HasDerivAt (ccmActualHeadMatchedWallLightOrientedCoupling p e)
      (ccmActualHeadMatchedWallLightOrientedCouplingFirstJet p e xi) xi := by
  let n := xiGammaEulerValuationNat (p, e)
  have h := (hasDerivAt_ccmActualHeadMatchedWallLightImbalance p e xi).mul
    (hasDerivAt_ccmActualHeadMatchedSinePhaseProfile n xi)
  change HasDerivAt
    (fun x : ℝ => ccmActualHeadMatchedWallLightImbalance p e x *
      ccmActualHeadMatchedSinePhaseProfile n x)
    (ccmActualHeadMatchedWallLightImbalanceFirstJet p e xi *
        ccmActualHeadMatchedSinePhaseProfile n xi +
      ccmActualHeadMatchedWallLightImbalance p e xi *
        ccmActualHeadMatchedSinePhaseFirstJet n xi) xi
  exact h

@[simp] theorem ccmActualHeadMatchedWallLightOrientedCouplingFirstJet_zero
    (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedWallLightOrientedCouplingFirstJet p e 0 = 0 := by
  simp [ccmActualHeadMatchedWallLightOrientedCouplingFirstJet,
    ccmActualHeadMatchedWallLightImbalance_eq,
    ccmActualHeadMatchedSinePhaseProfile_zero]

/-- Exact positive quadratic coefficient of the light/polar oriented coupling. -/
def ccmActualHeadMatchedWallLightOrientedQuadraticJet
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat (p, e)
  2 * (criticalMellinAtomWeight n *
      (2 * Real.pi * Real.log n)) *
    ccmActualHeadMatchedOrientedFirstMoment n

theorem hasDerivAt_ccmActualHeadMatchedWallLightOrientedCouplingFirstJet_zero
    (p : Nat.Primes) (e : ℕ) :
    HasDerivAt (ccmActualHeadMatchedWallLightOrientedCouplingFirstJet p e)
      (ccmActualHeadMatchedWallLightOrientedQuadraticJet p e) 0 := by
  let n := xiGammaEulerValuationNat (p, e)
  have hleft :=
    (hasDerivAt_ccmActualHeadMatchedWallLightImbalanceFirstJet_zero p e).mul
      (hasDerivAt_ccmActualHeadMatchedSinePhaseProfile_zero n)
  have hright :=
    (hasDerivAt_ccmActualHeadMatchedWallLightImbalance p e 0).mul
      (hasDerivAt_ccmActualHeadMatchedSinePhaseFirstJet_zero n)
  have h := hleft.add hright
  change HasDerivAt
    (fun x : ℝ =>
      ccmActualHeadMatchedWallLightImbalanceFirstJet p e x *
          ccmActualHeadMatchedSinePhaseProfile n x +
        ccmActualHeadMatchedWallLightImbalance p e x *
          ccmActualHeadMatchedSinePhaseFirstJet n x)
    (2 * (criticalMellinAtomWeight n *
      (2 * Real.pi * Real.log n)) *
        ccmActualHeadMatchedOrientedFirstMoment n) 0
  apply h.congr_deriv
  rw [ccmActualHeadMatchedWallLightImbalanceFirstJet_zero,
    ccmActualHeadMatchedSinePhaseProfile_zero,
    ccmActualHeadMatchedSinePhaseFirstJet_zero,
    ccmActualHeadMatchedWallLightImbalance_eq]
  simp only [Real.sin_zero, mul_zero, add_zero, zero_add]
  ring

theorem deriv_ccmActualHeadMatchedWallLightOrientedCoupling_eq_firstJet
    (p : Nat.Primes) (e : ℕ) :
    deriv (ccmActualHeadMatchedWallLightOrientedCoupling p e) =
      ccmActualHeadMatchedWallLightOrientedCouplingFirstJet p e := by
  funext xi
  exact (hasDerivAt_ccmActualHeadMatchedWallLightOrientedCoupling p e xi).deriv

theorem ccmActualHeadMatchedWallLightOrientedCoupling_secondDeriv_zero
    (p : Nat.Primes) (e : ℕ) :
    deriv (deriv (ccmActualHeadMatchedWallLightOrientedCoupling p e)) 0 =
      ccmActualHeadMatchedWallLightOrientedQuadraticJet p e := by
  rw [deriv_ccmActualHeadMatchedWallLightOrientedCoupling_eq_firstJet]
  exact
    (hasDerivAt_ccmActualHeadMatchedWallLightOrientedCouplingFirstJet_zero p e).deriv

/-- Every literal prime-power wall has strict positive quadratic light/polar contact. -/
theorem ccmActualHeadMatchedWallLightOrientedQuadraticJet_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ccmActualHeadMatchedWallLightOrientedQuadraticJet p e := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn2 : 2 ≤ n := by
    dsimp only [n, xiGammaEulerValuationNat]
    exact p.property.two_le.trans (Nat.le_pow (by omega))
  have hw : 0 < criticalMellinAtomWeight n := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact sq_pos_of_pos (suzukiCriticalEntryWallBareAmplitude_pos p e)
  have ha : 0 < 2 * Real.pi * Real.log n := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hmoment : 0 < ccmActualHeadMatchedOrientedFirstMoment n :=
    ccmActualHeadMatchedOrientedFirstMoment_primePower_pos p e
  unfold ccmActualHeadMatchedWallLightOrientedQuadraticJet
  dsimp only [n]
  positivity

end RHTower
