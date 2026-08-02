import GaloisForLFunctions.RHTower.MobiusThetaInternalJetSourceLocalSpanning
import GaloisForLFunctions.RHTower.XiSourceMatroidCircuitFracture

/-!
# Cofinal complex landing of the internally promoted Möbius--theta source

Every finite high-exponent rung is a target-free physical source whose Fourier--Laplace
transform is a reciprocal-zeta multiplier times one Xi jet.  This file passes to the exponent
cofinal limit before selecting a divisor.  Reciprocal zeta tends to one along every integral
dilation in the open right half-plane, so the source transforms converge to the exact Xi jet
throughout the honest theta strip.

The normalized Hellinger--Beta cofaces telescope to the same rungs.  Their finite codiagonals
therefore converge to every Xi jet at every actual divisor coordinate, retaining the first
nonzero multiplicity jet.  No zero, divisor, or Xi value enters any source definition.

This is complex analytic source landing, not half-density or Hellinger graph-norm admission.
The latter remains the RH-bearing step.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The centered Möbius--theta parameter sends an actual centered Xi divisor coordinate back to
the corresponding classical Xi coordinate. -/
theorem mobiusThetaCenteredParameter_xiSpectralPointSupport
    (rho : XiDivisorSupport) :
    mobiusThetaCenteredParameter (xiSpectralPointSupport rho) = (rho : ℂ) := by
  have hI : I * (-I) = (1 : ℂ) := by
    rw [mul_neg, I_mul_I, neg_neg]
  rw [mobiusThetaCenteredParameter, xiSpectralPointSupport]
  calc
    1 / 2 + I * (((rho : ℂ) - 1 / 2) * -I) =
        1 / 2 + ((rho : ℂ) - 1 / 2) * (I * -I) := by ring
    _ = 1 / 2 + ((rho : ℂ) - 1 / 2) := by rw [hI, mul_one]
    _ = (rho : ℂ) := by ring

/-- Adjacent internally promoted source orders, retained as a division-free conormal pair. -/
def mobiusThetaInternalJetConormalPair
    (k m : ℕ) (w : ℂ) : ℂ × ℂ :=
  (mobiusThetaInternalJetFourierLaplace k m w,
    mobiusThetaInternalJetFourierLaplace (k + 1) m w)

/-- Both conormal coordinates carry the same reciprocal-zeta source multiplier. -/
theorem mobiusThetaInternalJetConormalPair_eq
    (k : ℕ) {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetConormalPair k m w =
      ((riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ *
          iteratedDeriv k XiC w,
        (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ *
          iteratedDeriv (k + 1) XiC w) := by
  rw [mobiusThetaInternalJetConormalPair,
    mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
      k hm hw hms,
    mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
      (k + 1) hm hw hms]

/-- On the regular locus, projectivizing the source conormal pair recovers the Xi logarithmic
derivative.  Division occurs only after the source pair has landed. -/
theorem mobiusThetaInternalJetConormalPair_slope_eq_logDeriv
    {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hXi : XiC w ≠ 0) :
    (mobiusThetaInternalJetConormalPair 0 m w).2 /
        (mobiusThetaInternalJetConormalPair 0 m w).1 =
      logDeriv XiC w := by
  rw [mobiusThetaInternalJetConormalPair_eq 0 hm hw hms]
  simp only [iteratedDeriv_zero, zero_add, iteratedDeriv_one]
  have hmult :
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ ≠ 0 :=
    inv_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re
        (one_lt_natCast_mul_re hm hms))
  have _hden :
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ *
          XiC w ≠ 0 :=
    mul_ne_zero hmult hXi
  change
    ((riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ * deriv XiC w) /
          ((riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ * XiC w) =
      deriv XiC w / XiC w
  exact mul_div_mul_left _ _ hmult

/-- **Cofinal complex source-to-Xi jet landing.**  At every point in the honest theta strip whose
classical centered parameter lies in the open right half-plane, the target-free internally
promoted source rungs converge after Fourier--Laplace transform to the exact Xi jet. -/
theorem tendsto_mobiusThetaInternalJetFourierLaplace_cofinal
    (k K : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hs : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto
      (fun N : ℕ =>
        mobiusThetaInternalJetFourierLaplace k (K + N) w)
      atTop (𝓝 (iteratedDeriv k XiC w)) := by
  have hmult :=
    (tendsto_inv_riemannZeta_nat_dilation_one (K := K) hs).mul_const
      (iteratedDeriv k XiC w)
  have hlimit :
      Tendsto
        (fun N : ℕ =>
          (riemannZeta (((K + N : ℕ) : ℂ) *
            mobiusThetaCenteredParameter w))⁻¹ *
              iteratedDeriv k XiC w)
        atTop (𝓝 (iteratedDeriv k XiC w)) := by
    simpa only [one_mul] using hmult
  obtain ⟨M, hM⟩ :=
    exists_nat_gt (1 / (mobiusThetaCenteredParameter w).re)
  have hMpos : 0 < M := by
    have hone : 0 < 1 / (mobiusThetaCenteredParameter w).re :=
      one_div_pos.mpr hs
    have hMreal : 0 < (M : ℝ) := hone.trans hM
    exact_mod_cast hMreal
  refine hlimit.congr' ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  have hMN : M ≤ K + N := hN.trans (Nat.le_add_left N K)
  have hmpos : 0 < K + N := lt_of_lt_of_le hMpos hMN
  have hMcast : (M : ℝ) ≤ (K : ℝ) + (N : ℝ) := by
    exact_mod_cast hMN
  have hbase : 1 < (M : ℝ) * (mobiusThetaCenteredParameter w).re :=
    (div_lt_iff₀ hs).mp hM
  have hprod :
      1 < (mobiusThetaCenteredParameter w).re * (K + N : ℝ) := by
    calc
      1 < (M : ℝ) * (mobiusThetaCenteredParameter w).re := hbase
      _ = (mobiusThetaCenteredParameter w).re * (M : ℝ) := by ring
      _ ≤ (mobiusThetaCenteredParameter w).re * (K + N : ℝ) :=
        mul_le_mul_of_nonneg_left hMcast hs.le
  have hdomain :
      1 / ((K + N : ℕ) : ℝ) < (mobiusThetaCenteredParameter w).re := by
    norm_num only [Nat.cast_add]
    exact
      (div_lt_iff₀ (by exact_mod_cast hmpos : (0 : ℝ) < K + N)).mpr hprod
  exact
    (mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
      k (Nat.ne_of_gt hmpos) hw hdomain).symm

/-- The division-free conormal pair converges throughout the complex landing domain. -/
theorem tendsto_mobiusThetaInternalJetConormalPair_cofinal
    (k K : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hs : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto
      (fun N : ℕ => mobiusThetaInternalJetConormalPair k (K + N) w)
      atTop
      (𝓝 (iteratedDeriv k XiC w, iteratedDeriv (k + 1) XiC w)) := by
  simpa only [mobiusThetaInternalJetConormalPair] using
    (tendsto_mobiusThetaInternalJetFourierLaplace_cofinal k K hw hs).prodMk_nhds
      (tendsto_mobiusThetaInternalJetFourierLaplace_cofinal (k + 1) K hw hs)

/-- The completed source coface has the same cofinal complex landing: its finite codiagonal
converges to the exact Xi jet. -/
theorem
    tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace
    (k K : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hs : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (N + 1),
          mobiusThetaInternalJetCompleteChannelFourierLaplace k K j w)
      atTop (𝓝 (iteratedDeriv k XiC w)) := by
  have hlimit :=
    tendsto_mobiusThetaInternalJetFourierLaplace_cofinal k K hw hs
  refine hlimit.congr' ?_
  filter_upwards with N
  exact
    (sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace
      k K N w).symm

/-- Every actual Xi divisor coordinate lies in the unconditional complex landing domain. -/
theorem tendsto_mobiusThetaInternalJetFourierLaplace_cofinal_at_divisor
    (k K : ℕ) (rho : XiDivisorSupport) :
    Tendsto
      (fun N : ℕ =>
        mobiusThetaInternalJetFourierLaplace k (K + N)
          (xiSpectralPointSupport rho))
      atTop
      (𝓝 (iteratedDeriv k XiC (xiSpectralPointSupport rho))) := by
  apply tendsto_mobiusThetaInternalJetFourierLaplace_cofinal k K
  · exact abs_im_xiSpectralPointSupport_lt_one rho
  · rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1

/-- At every actual divisor coordinate, the completed source coface codiagonal lands in every Xi
jet without an RH hypothesis. -/
theorem
    tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace_at_divisor
    (k K : ℕ) (rho : XiDivisorSupport) :
    Tendsto
      (fun N : ℕ =>
        ∑ j ∈ Finset.range (N + 1),
          mobiusThetaInternalJetCompleteChannelFourierLaplace k K j
            (xiSpectralPointSupport rho))
      atTop
      (𝓝 (iteratedDeriv k XiC (xiSpectralPointSupport rho))) := by
  apply
    tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace
      k K
  · exact abs_im_xiSpectralPointSupport_lt_one rho
  · rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1

/-- The cofinal source landing retains the first nonzero Xi jet at every divisor point, including
arbitrary analytic multiplicity. -/
theorem mobiusThetaInternalJetCofinalLanding_retains_supportMultiplicity
    (K : ℕ) (rho : XiDivisorSupport) :
    Tendsto
        (fun N : ℕ =>
          ∑ j ∈ Finset.range (N + 1),
            mobiusThetaInternalJetCompleteChannelFourierLaplace
              (xiSupportMultiplicity rho) K j
              (xiSpectralPointSupport rho))
        atTop
        (𝓝 (iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho))) ∧
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) ≠ 0 := by
  exact
    ⟨tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace_at_divisor
        (xiSupportMultiplicity rho) K rho,
      iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho⟩

/-- At a divisor of arbitrary multiplicity, the cofinal source conormal graph lands in the
nonzero vertical conormal `(0, XiC^(r))`.  This is the singular Ward graph before projective
division. -/
theorem mobiusThetaInternalJetConormalPair_leading_vertical_at_divisor
    (K : ℕ) (rho : XiDivisorSupport) :
    Tendsto
        (fun N : ℕ =>
          mobiusThetaInternalJetConormalPair
            (xiSupportMultiplicity rho - 1) (K + N)
            (xiSpectralPointSupport rho))
        atTop
        (𝓝 (0, iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho))) ∧
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) ≠ 0 := by
  have hrpos : 0 < xiSupportMultiplicity rho :=
    xiSupportMultiplicity_pos rho
  have hrpred : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho :=
    Nat.sub_lt hrpos (by omega)
  have hzero :=
    iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hrpred
  have hsucc : xiSupportMultiplicity rho - 1 + 1 = xiSupportMultiplicity rho := by
    omega
  have hlimit := tendsto_mobiusThetaInternalJetConormalPair_cofinal
    (xiSupportMultiplicity rho - 1) K
    (abs_im_xiSpectralPointSupport_lt_one rho)
    (by
      rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
      exact (xi_divisor_support_re_mem_open_unit rho).1)
  exact
    ⟨by simpa only [hzero, hsucc] using hlimit,
      iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho⟩

end

end RHTower
