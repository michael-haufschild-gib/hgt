import GaloisForLFunctions.RHTower.MobiusThetaComplexSourceToXiLanding
import GaloisForLFunctions.RHTower.HellingerBetaCovariantCofaceTransgression

/-!
# Internally promoted Möbius--theta source-to-Xi jet landing

An unpromoted Möbius--theta source transforms to a multiple of `XiC`; in the Xi quotient it is
therefore exact.  This module performs the missing source operation before arithmetic translation:
the `k`-th logarithmic moment is taken in the local coordinate of each translated theta packet.
The resulting target-free physical source has Fourier--Laplace transform

`ζ(m(1/2 + I w))⁻¹ · ∂^k XiC(w)`.

Thus primitive promotion is not differentiation of a target expression after landing.  It is an
explicit source object built only from Möbius coefficients, logarithmic translations, and local
theta moments.  All orders are constructed so multiplicity jets are retained without selecting a
divisor point.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Set
open scoped BigOperators LSeries.notation Moebius

noncomputable section
namespace RHTower

/-- The `k`-th theta moment promoted in the local coordinate of the `n`-labelled packet. -/
def mobiusThetaInternalJetLaplaceSourceTerm
    (k m n : ℕ) (x : ℝ) : ℂ :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
    (-I * ((x - Real.log n : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (x - Real.log n) : ℂ)

/-- Complete target-free internally promoted source. -/
def mobiusThetaInternalJetLaplaceSource
    (k m : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusThetaInternalJetLaplaceSourceTerm k m n x

/-- Fourier--Laplace integrand of one internally promoted arithmetic packet. -/
def mobiusThetaInternalJetLaplaceIntegrandTerm
    (k m : ℕ) (w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetLaplaceSourceTerm k m n x

/-- Fourier--Laplace transform of the internally promoted physical source. -/
def mobiusThetaInternalJetFourierLaplace
    (k m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetLaplaceSource k m x

/-- Zeroth internal promotion recovers the original physical Möbius--theta packet. -/
theorem mobiusThetaInternalJetLaplaceSourceTerm_zero
    (m n : ℕ) (x : ℝ) :
    mobiusThetaInternalJetLaplaceSourceTerm 0 m n x =
      mobiusThetaLaplaceSourceTerm m n x := by
  simp [mobiusThetaInternalJetLaplaceSourceTerm,
    mobiusThetaLaplaceSourceTerm]

theorem mobiusThetaInternalJetLaplaceSource_zero
    (m : ℕ) (x : ℝ) :
    mobiusThetaInternalJetLaplaceSource 0 m x =
      mobiusThetaLaplaceSource m x := by
  unfold mobiusThetaInternalJetLaplaceSource mobiusThetaLaplaceSource
  exact tsum_congr fun n => mobiusThetaInternalJetLaplaceSourceTerm_zero m n x

/-- Translation promotes the half-density coefficient to the centered parameter while preserving
the local theta-jet coordinate. -/
theorem mobiusThetaInternalJetLaplaceIntegrandTerm_eq
    (k m : ℕ) (w : ℂ) (n : ℕ) (x : ℝ) :
    mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x =
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n *
        thetaCuspFourierLaplaceJetIntegrand k w (x - Real.log n) := by
  rw [mobiusThetaInternalJetLaplaceIntegrandTerm,
    mobiusThetaInternalJetLaplaceSourceTerm,
    thetaCuspFourierLaplaceJetIntegrand,
    thetaCuspFourierLaplaceIntegrand]
  rw [show Complex.exp (-I * w * (x : ℂ)) =
      Complex.exp (-I * w * (Real.log n : ℂ)) *
        Complex.exp (-I * w * ((x - Real.log n : ℝ) : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [← LSeries_term_half_mul_exp_neg_I_mul_log]
  ring

theorem integrable_mobiusThetaInternalJetLaplaceIntegrandTerm
    (k : ℕ) {m : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    Integrable (mobiusThetaInternalJetLaplaceIntegrandTerm k m w n) := by
  rw [show mobiusThetaInternalJetLaplaceIntegrandTerm k m w n =
      fun x : ℝ =>
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w) n *
          thetaCuspFourierLaplaceJetIntegrand k w (x - Real.log n) by
    funext x
    exact mobiusThetaInternalJetLaplaceIntegrandTerm_eq k m w n x]
  exact ((integrable_thetaCuspFourierLaplaceJetIntegrand k hw).comp_add_right
    (-Real.log n)).const_mul _

theorem integral_norm_mobiusThetaInternalJetLaplaceIntegrandTerm
    (k : ℕ) {m : ℕ} {w : ℂ} (n : ℕ) :
    ∫ x : ℝ, ‖mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n‖ *
        ∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k w x‖ := by
  simp_rw [mobiusThetaInternalJetLaplaceIntegrandTerm_eq, norm_mul]
  rw [integral_const_mul]
  congr 1
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self
      (fun x : ℝ => ‖thetaCuspFourierLaplaceJetIntegrand k w x‖)
      (-Real.log n))

theorem summable_integral_norm_mobiusThetaInternalJetLaplaceIntegrandTerm
    (k : ℕ) {m : ℕ} (hm : m ≠ 0) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x‖) := by
  have hcoeff := LSeriesSummable_mPart_moebius hm hms
  unfold LSeriesSummable at hcoeff
  simpa only [integral_norm_mobiusThetaInternalJetLaplaceIntegrandTerm] using
    hcoeff.norm.mul_right
      (∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k w x‖)

/-- One physical packet lands in the corresponding centered Dirichlet coefficient times the
actual `k`-th Xi jet. -/
theorem integral_mobiusThetaInternalJetLaplaceIntegrandTerm
    (k : ℕ) {m : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    ∫ x : ℝ, mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x =
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n *
        iteratedDeriv k XiC w := by
  simp_rw [mobiusThetaInternalJetLaplaceIntegrandTerm_eq]
  rw [integral_const_mul]
  rw [show
      (∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w
        (x - Real.log n)) =
      ∫ x : ℝ, thetaCuspFourierLaplaceJetIntegrand k w x by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (thetaCuspFourierLaplaceJetIntegrand k w) (-Real.log n))]
  rw [← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet]
  exact (abs_lt.mp hw)

/-- **Unconditional internally promoted physical source-to-Xi jet landing.**  On the honest joint
theta strip and Möbius half-plane, every source-built local moment lands in the reciprocal-zeta
multiple of the corresponding Xi jet.  Source construction precedes both transform evaluation and
divisor selection. -/
theorem mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
    (k : ℕ) {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetFourierLaplace k m w =
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ *
        iteratedDeriv k XiC w := by
  unfold mobiusThetaInternalJetFourierLaplace
    mobiusThetaInternalJetLaplaceSource
  have hinter (x : ℝ) :
      Complex.exp (-I * w * (x : ℂ)) *
          (∑' n : ℕ, mobiusThetaInternalJetLaplaceSourceTerm k m n x) =
        ∑' n : ℕ,
          mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  simp_rw [hinter]
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => integrable_mobiusThetaInternalJetLaplaceIntegrandTerm k hw n)
    (summable_integral_norm_mobiusThetaInternalJetLaplaceIntegrandTerm
      k hm hms)]
  rw [show
      (∑' n : ℕ,
        ∫ x : ℝ, mobiusThetaInternalJetLaplaceIntegrandTerm k m w n x) =
      ∑' n : ℕ,
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w) n *
          iteratedDeriv k XiC w by
    apply tsum_congr
    intro n
    exact integral_mobiusThetaInternalJetLaplaceIntegrandTerm k hw n]
  rw [tsum_mul_right]
  change LSeries (↗(mPart m (μ : ArithmeticFunction ℤ)))
      (mobiusThetaCenteredParameter w) * iteratedDeriv k XiC w = _
  rw [LSeries_mPart_moebius hm hms]

/-- Primitive (`k = 1`) specialization: the first non-exact divisor-normal source lands in
`ζ(ms)⁻¹ XiC'`. -/
theorem mobiusThetaInternalPrimitiveFourierLaplace_eq_invZeta_mul_deriv_XiC
    {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetFourierLaplace 1 m w =
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ *
        deriv XiC w := by
  simpa [iteratedDeriv_one] using
    mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
      1 hm hw hms

/-- On the honest source half-plane, a nonzero Xi jet remains nonzero after physical Möbius
promotion.  In particular, the first nonvanishing multiplicity jet is retained rather than killed
as an Xi multiple. -/
theorem mobiusThetaInternalJetFourierLaplace_ne_zero
    (k : ℕ) {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hjet : iteratedDeriv k XiC w ≠ 0) :
    mobiusThetaInternalJetFourierLaplace k m w ≠ 0 := by
  rw [mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
    k hm hw hms]
  exact mul_ne_zero
    (inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re
      (one_lt_natCast_mul_re hm hms))) hjet

/-! ## Cofinal primitive source channel

Adjacent exponent differences are now taken after internal jet promotion.  Consequently their
finite codiagonal lands in an Xi jet, rather than in an exact Xi multiple.
-/

/-- Complete internally promoted source channel: head rung followed by adjacent exponent
differences. -/
def mobiusThetaInternalJetCompleteSourceChannel
    (k K : ℕ) : ℕ → ℝ → ℂ
  | 0 => mobiusThetaInternalJetLaplaceSource k K
  | j + 1 => fun x =>
      mobiusThetaInternalJetLaplaceSource k (K + j + 1) x -
        mobiusThetaInternalJetLaplaceSource k (K + j) x

/-- Exact finite source telescope, before Fourier--Laplace evaluation. -/
theorem sum_range_mobiusThetaInternalJetCompleteSourceChannel
    (k K N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
        mobiusThetaInternalJetCompleteSourceChannel k K j =
      mobiusThetaInternalJetLaplaceSource k (K + N) := by
  induction N with
  | zero => simp [mobiusThetaInternalJetCompleteSourceChannel]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [mobiusThetaInternalJetCompleteSourceChannel]
      rw [show K + N + 1 = K + (N + 1) by omega]
      ext x
      simp

/-- Transform channel attached to the physical source channel.  Each coordinate is an actual
Fourier--Laplace integral constructed above. -/
def mobiusThetaInternalJetCompleteChannelFourierLaplace
    (k K : ℕ) : ℕ → ℂ → ℂ
  | 0 => mobiusThetaInternalJetFourierLaplace k K
  | j + 1 => fun w =>
      mobiusThetaInternalJetFourierLaplace k (K + j + 1) w -
        mobiusThetaInternalJetFourierLaplace k (K + j) w

/-- Every promoted coface coordinate lands in the usual complete-resolution multiplier times the
same Xi jet. -/
theorem mobiusThetaInternalJetCompleteChannelFourierLaplace_eq
    (k : ℕ) {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetCompleteChannelFourierLaplace k K j w =
      completeResolutionMultiplier K j (mobiusThetaCenteredParameter w) *
        iteratedDeriv k XiC w := by
  cases j with
  | zero =>
      rw [mobiusThetaInternalJetCompleteChannelFourierLaplace,
        mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
          k (by omega) hw hKs]
      rfl
  | succ j =>
      have hleft := mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
        k (m := K + j + 1) (by omega) hw
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      have hright := mobiusThetaInternalJetFourierLaplace_eq_invZeta_mul_iteratedDeriv_XiC
        k (m := K + j) (by omega) hw
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      change
        mobiusThetaInternalJetFourierLaplace k (K + j + 1) w -
          mobiusThetaInternalJetFourierLaplace k (K + j) w = _
      rw [hleft, hright]
      simp only [completeResolutionMultiplier, shellMultiplier]
      push_cast
      ring

/-- Exact finite transform telescope. -/
theorem sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace
    (k K N : ℕ) (w : ℂ) :
    ∑ j ∈ Finset.range (N + 1),
        mobiusThetaInternalJetCompleteChannelFourierLaplace k K j w =
      mobiusThetaInternalJetFourierLaplace k (K + N) w := by
  induction N with
  | zero => simp [mobiusThetaInternalJetCompleteChannelFourierLaplace]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp [mobiusThetaInternalJetCompleteChannelFourierLaplace, add_assoc]

/-! ### Hellinger--Beta covariant form

The same unique source gauge now acts on the non-exact internally promoted chain.  Normalization
recovers its adjacent source boundary exactly.
-/

/-- Hellinger--Beta gauged internally promoted source rung. -/
def hellingerBetaMobiusThetaInternalJetGaugedRung
    (k m : ℕ) : ℝ → ℂ :=
  hellingerHodgeBetaColumnComplex (m : ℂ) •
    mobiusThetaInternalJetLaplaceSource k m

/-- Covariant adjacent-grade coface on the internally promoted source. -/
def hellingerBetaMobiusThetaInternalJetCovariantCoface
    (k m : ℕ) : ℝ → ℂ :=
  hellingerBetaMobiusThetaInternalJetGaugedRung k (m + 1) -
    ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) •
      hellingerBetaMobiusThetaInternalJetGaugedRung k m

theorem hellingerBetaMobiusThetaInternalJetCovariantCoface_eq
    (k m : ℕ) :
    hellingerBetaMobiusThetaInternalJetCovariantCoface k m =
      hellingerHodgeBetaColumnComplex (((m + 1 : ℕ) : ℝ) : ℂ) •
        (mobiusThetaInternalJetLaplaceSource k (m + 1) -
          mobiusThetaInternalJetLaplaceSource k m) := by
  have hrec := hellingerHodgeBetaColumnComplex_real_add_one
    (a := (m : ℝ))
      (lt_of_lt_of_le (by norm_num : -(1 / 2 : ℝ) < 0) (Nat.cast_nonneg m))
  unfold hellingerBetaMobiusThetaInternalJetCovariantCoface
    hellingerBetaMobiusThetaInternalJetGaugedRung
  have hrec' :
      hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) =
        ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) *
          hellingerHodgeBetaColumnComplex (m : ℂ) := by
    convert hrec using 1 <;> norm_num
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show ((((m : ℝ) + 1 : ℝ) : ℂ)) = (m : ℂ) + 1 by norm_num]
  change
    hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) •
          mobiusThetaInternalJetLaplaceSource k (m + 1) -
        ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) •
          (hellingerHodgeBetaColumnComplex (m : ℂ) •
            mobiusThetaInternalJetLaplaceSource k m) =
      hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) •
        (mobiusThetaInternalJetLaplaceSource k (m + 1) -
          mobiusThetaInternalJetLaplaceSource k m)
  rw [hrec']
  module

theorem hellingerBetaMobiusThetaInternalJetCovariantCoface_normalized
    (k m : ℕ) :
    (hellingerHodgeBetaColumnComplex (((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ •
        hellingerBetaMobiusThetaInternalJetCovariantCoface k m =
      mobiusThetaInternalJetLaplaceSource k (m + 1) -
        mobiusThetaInternalJetLaplaceSource k m := by
  rw [hellingerBetaMobiusThetaInternalJetCovariantCoface_eq]
  rw [inv_smul_smul₀]
  exact hellingerHodgeBetaColumnComplex_real_ne_zero
    (a := ((m + 1 : ℕ) : ℝ))
      (lt_of_lt_of_le (by norm_num : -(1 / 2 : ℝ) < 0)
        (Nat.cast_nonneg (m + 1)))

/-- Completed normalized Hellinger--Beta coface on the promoted chain. -/
def hellingerBetaMobiusThetaInternalJetCompleteCoface
    (k K : ℕ) : ℕ → ℝ → ℂ
  | 0 => mobiusThetaInternalJetLaplaceSource k K
  | j + 1 =>
      (hellingerHodgeBetaColumnComplex
        (((K + j + 1 : ℕ) : ℝ) : ℂ))⁻¹ •
          hellingerBetaMobiusThetaInternalJetCovariantCoface k (K + j)

theorem hellingerBetaMobiusThetaInternalJetCompleteCoface_eq
    (k K j : ℕ) :
    hellingerBetaMobiusThetaInternalJetCompleteCoface k K j =
      mobiusThetaInternalJetCompleteSourceChannel k K j := by
  cases j with
  | zero => rfl
  | succ j =>
      simp only [hellingerBetaMobiusThetaInternalJetCompleteCoface,
        mobiusThetaInternalJetCompleteSourceChannel]
      have h :=
        hellingerBetaMobiusThetaInternalJetCovariantCoface_normalized k (K + j)
      ext x
      exact congrFun h x

/-- **Cofinal non-exact source telescope.**  Finite normalized Hellinger--Beta boundaries recover
the terminal internally promoted Möbius--theta source exactly. -/
theorem sum_range_hellingerBetaMobiusThetaInternalJetCompleteCoface
    (k K N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
        hellingerBetaMobiusThetaInternalJetCompleteCoface k K j =
      mobiusThetaInternalJetLaplaceSource k (K + N) := by
  rw [show
      (fun j => hellingerBetaMobiusThetaInternalJetCompleteCoface k K j) =
        mobiusThetaInternalJetCompleteSourceChannel k K by
    funext j
    exact hellingerBetaMobiusThetaInternalJetCompleteCoface_eq k K j]
  exact sum_range_mobiusThetaInternalJetCompleteSourceChannel k K N

end RHTower
