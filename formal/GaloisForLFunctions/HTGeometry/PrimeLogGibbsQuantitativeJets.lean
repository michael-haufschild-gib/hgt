import GaloisForLFunctions.HTGeometry.PrimeLogGibbsJointCompactOpen
import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetDerivatives

/-!
# Quantitative susceptibility jets of prime-log Gibbs responses

[BRIDGE] In the finite Lehmann representation, every frequency derivative raises a resolvent
power and contributes a factorial.  The subsystem-independent prime gap `log 2` therefore
controls not only the response value but every holomorphic susceptibility jet.  On the upper
strip `η ≤ Im z`, the exact cold-limit error is bounded by

`m! * exp (-β log 2) * η⁻¹^(m+1) * totalMass`.

The same compact-open argument also upgrades the simultaneous cold/thermodynamic limit from
pointwise convergence of each jet to locally uniform convergence of each derivative function.
-/

open scoped BigOperators
open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The all-order derivative formula for the reflected real-frequency resolvent. -/
theorem iteratedDeriv_add_real_inv
    (t : ℝ) (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    iteratedDeriv m (fun w : ℂ => ((t : ℂ) + w)⁻¹) z =
      (-1 : ℂ) ^ m * (m.factorial : ℂ) *
        (((t : ℂ) + z)⁻¹) ^ (m + 1) := by
  have hne : z + (t : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp at him
    exact (ne_of_gt hz) him
  simpa only [add_comm, inv_pow] using
    (GaloisForLFunctions.iteratedDeriv_inv_add_const (t : ℂ) m z hne)

/-- Exact spectral formula for the cold-limit error in every susceptibility order. -/
theorem iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_eq
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ)
    (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    iteratedDeriv m (finitePrimeLogHermitianGibbsCarrier P u β) z -
        iteratedDeriv m (finitePrimeLogHerglotz P u) z =
      -((-1 : ℂ) ^ m * (m.factorial : ℂ)) *
        ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            (((primeLogSupport p : ℂ) + z)⁻¹) ^ (m + 1) := by
  have hG : ContDiffAt ℂ (m : WithTop ℕ∞)
      (finitePrimeLogHermitianGibbsCarrier P u β) z :=
    (((differentiableOn_finitePrimeLogHermitianGibbsCarrier_upperHalfPlane
      P u β).analyticOnNhd isOpen_upperHalfPlane) z hz).contDiffAt
  have hH : ContDiffAt ℂ (m : WithTop ℕ∞)
      (finitePrimeLogHerglotz P u) z :=
    (((differentiableOn_finitePrimeLogHerglotz_upperHalfPlane
      P u).analyticOnNhd isOpen_upperHalfPlane) z hz).contDiffAt
  rw [← iteratedDeriv_sub hG hH]
  have hfun :
      finitePrimeLogHermitianGibbsCarrier P u β -
        finitePrimeLogHerglotz P u =
      -(fun w => ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        (Real.exp (-β * primeLogSupport p) : ℂ) *
          ((primeLogSupport p : ℂ) + w)⁻¹) := by
    funext w
    change finitePrimeLogHermitianGibbsCarrier P u β w -
      finitePrimeLogHerglotz P u w = _
    rw [finitePrimeLogHermitianGibbsCarrier, finitePrimeLogHerglotz,
      ← Finset.sum_sub_distrib]
    change (∑ p ∈ P, ((primeDyadicWeight u p : ℂ) *
        (((primeLogSupport p : ℂ) - w)⁻¹ -
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            ((primeLogSupport p : ℂ) + w)⁻¹) -
        (primeDyadicWeight u p : ℂ) *
          ((primeLogSupport p : ℂ) - w)⁻¹)) =
      -(∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        (Real.exp (-β * primeLogSupport p) : ℂ) *
          ((primeLogSupport p : ℂ) + w)⁻¹)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hfun, iteratedDeriv_neg,
    iteratedDeriv_fun_sum (fun p hp => by
      have hne : (primeLogSupport p : ℂ) + z ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        simp at him
        exact (ne_of_gt hz) him
      exact contDiffAt_const.mul
        ((by fun_prop : ContDiffAt ℂ (m : WithTop ℕ∞)
          (fun w : ℂ => (primeLogSupport p : ℂ) + w) z).inv hne))]
  simp_rw [GaloisForLFunctions.iteratedDeriv_const_mul_field,
    iteratedDeriv_add_real_inv _ _ _ hz]
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- **Uniform all-order Boltzmann estimate.**  Every susceptibility jet has a cold-limit error
bound independent of the finite prime subsystem. -/
theorem norm_iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_le
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (C : ℝ)
    (hu : ∀ p, u p ≤ C) (β : ℝ) (hβ : 0 ≤ β)
    (m : ℕ) {η : ℝ} (hη : 0 < η) (z : ℂ) (hz : η ≤ z.im) :
    ‖iteratedDeriv m (finitePrimeLogHermitianGibbsCarrier P u β) z -
        iteratedDeriv m (finitePrimeLogHerglotz P u) z‖ ≤
      (m.factorial : ℝ) * Real.exp (-β * Real.log 2) *
        η⁻¹ ^ (m + 1) * primeDyadicTotalMass u := by
  have hzim : 0 < z.im := hη.trans_le hz
  have hinv : (z.im)⁻¹ ≤ η⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hη hz
  have hsumMass : ∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ)‖ ≤
      primeDyadicTotalMass u :=
    (summable_norm_primeDyadicWeight u C hu).sum_le_tsum P
      (fun p hp => norm_nonneg _)
  rw [iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_eq
    P u β m z hzim, norm_mul, norm_neg, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, norm_natCast]
  have hsum :
      ‖∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            (((primeLogSupport p : ℂ) + z)⁻¹) ^ (m + 1)‖ ≤
        Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
          primeDyadicTotalMass u := by
    calc
      _ ≤ ∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ) *
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            (((primeLogSupport p : ℂ) + z)⁻¹) ^ (m + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P, Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
          ‖(primeDyadicWeight u p : ℂ)‖ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul, norm_mul,
          Complex.norm_real (Real.exp (-β * primeLogSupport p)), Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), norm_pow]
        have hres : ‖((primeLogSupport p : ℂ) + z)⁻¹‖ ≤ η⁻¹ :=
          (norm_primeLogSupport_add_inv_le_im_inv p z hzim).trans hinv
        have hgap := exp_neg_beta_primeLogSupport_le_gap p hβ
        have hw : 0 ≤ ‖(primeDyadicWeight u p : ℂ)‖ := norm_nonneg _
        have he : 0 ≤ Real.exp (-β * primeLogSupport p) := (Real.exp_pos _).le
        have hegap : 0 ≤ Real.exp (-β * Real.log 2) := (Real.exp_pos _).le
        have hres0 : 0 ≤ ‖((primeLogSupport p : ℂ) + z)⁻¹‖ := norm_nonneg _
        have hetaInv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
        calc
          ‖(primeDyadicWeight u p : ℂ)‖ *
              Real.exp (-β * primeLogSupport p) *
                ‖((primeLogSupport p : ℂ) + z)⁻¹‖ ^ (m + 1) ≤
              ‖(primeDyadicWeight u p : ℂ)‖ *
                Real.exp (-β * Real.log 2) *
                  ‖((primeLogSupport p : ℂ) + z)⁻¹‖ ^ (m + 1) := by
            gcongr
          _ ≤ ‖(primeDyadicWeight u p : ℂ)‖ *
                Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) := by
            gcongr
          _ = Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
                ‖(primeDyadicWeight u p : ℂ)‖ := by ring
      _ = Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
          (∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ)‖) := by
        rw [Finset.mul_sum]
      _ ≤ Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
          primeDyadicTotalMass u := by
        exact mul_le_mul_of_nonneg_left hsumMass
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg (inv_nonneg.mpr hη.le) _))
  calc
    1 * (m.factorial : ℝ) *
        ‖∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            (((primeLogSupport p : ℂ) + z)⁻¹) ^ (m + 1)‖ =
        (m.factorial : ℝ) *
          ‖∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
            (Real.exp (-β * primeLogSupport p) : ℂ) *
              (((primeLogSupport p : ℂ) + z)⁻¹) ^ (m + 1)‖ := by ring
    _ ≤ (m.factorial : ℝ) *
        (Real.exp (-β * Real.log 2) * η⁻¹ ^ (m + 1) *
          primeDyadicTotalMass u) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (m.factorial : ℝ) * Real.exp (-β * Real.log 2) *
        η⁻¹ ^ (m + 1) * primeDyadicTotalMass u := by ring

/-- Exact finite Hermitian Gibbs response form of the all-order Boltzmann estimate. -/
theorem norm_iteratedDeriv_finiteHermitianGibbsResponse_sub_le
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (C : ℝ)
    (hu : ∀ p, u p ≤ C) (β : ℝ) (hβ : 0 ≤ β)
    (m : ℕ) {η : ℝ} (hη : 0 < η) (z : ℂ) (hz : η ≤ z.im) :
    ‖iteratedDeriv m
        (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogGibbsFiniteHermitianAmplitude P u β))
          (primeLogKMSFiniteEnergy P) w) z -
        iteratedDeriv m (finitePrimeLogHerglotz P u) z‖ ≤
      (m.factorial : ℝ) * Real.exp (-β * Real.log 2) *
        η⁻¹ ^ (m + 1) * primeDyadicTotalMass u := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    norm_iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_sub_le
      P u C hu β hβ m hη z hz

/-- Every derivative function of the finite Gibbs carriers converges locally uniformly in the
simultaneous cold/thermodynamic product limit. -/
theorem iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ =>
        iteratedDeriv m (finitePrimeLogHermitianGibbsCarrier x.1 u x.2))
      (iteratedDeriv m (primeLogHerglotz u)) Filter.atTop upperHalfPlane := by
  exact GaloisForLFunctions.iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
    isOpen_upperHalfPlane
    (finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint u C hu)
    (Filter.Eventually.of_forall fun x =>
      differentiableOn_finitePrimeLogHermitianGibbsCarrier_upperHalfPlane x.1 u x.2)
    m

/-- Every exact Hermitian Gibbs susceptibility function converges locally uniformly in the same
simultaneous limit. -/
theorem iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => iteratedDeriv m
        (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1 u x.2))
          (primeLogKMSFiniteEnergy x.1) w))
      (iteratedDeriv m (primeLogHerglotz u)) Filter.atTop upperHalfPlane := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint
      u C hu m

/-- Universal-gauge all-order locally uniform susceptibility limit. -/
theorem universalFacetOrbitGauge_iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
    (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => iteratedDeriv m
        (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1
              (fun q => universalFacetOrbitGauge q) x.2))
          (primeLogKMSFiniteEnergy x.1) w))
      (iteratedDeriv m (primeLogHerglotz (fun q => universalFacetOrbitGauge q)))
      Filter.atTop upperHalfPlane :=
  iteratedDeriv_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) m

end

end GaloisForLFunctions.HTGeometry
