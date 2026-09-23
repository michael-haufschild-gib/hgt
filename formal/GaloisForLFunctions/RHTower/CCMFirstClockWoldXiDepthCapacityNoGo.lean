import GaloisForLFunctions.RHTower.HighExponentShellLeastAtomAsymptotic
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Wold-vacuum / Xi-depth capacity no-go

The actual Xi depth successor is harmonic to first order.  Summing those
successors over the literal Wold vacuum therefore grows in the Xi logarithmic
connection direction.  A nonnegative lower-semicontinuous two-homogeneous
capacity cannot both detect that direction and remain uniformly bounded on
the vacuum truncations.

This is unconditional and does not assume a Xi zero or RH.
-/

open Asymptotics Complex Filter Finset Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Weighted Cesàro convergence in a real normed space. -/
theorem weightedCesaro_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℕ → E} {L : E} (hy : Tendsto y atTop (𝓝 L))
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hW : Tendsto (fun N => ∑ n ∈ range N, w n) atTop atTop) :
    Tendsto
      (fun N =>
        ((∑ n ∈ range N, w n)⁻¹) •
          ∑ n ∈ range N, w n • y n)
      atTop (𝓝 L) := by
  let W : ℕ → ℝ := fun N => ∑ n ∈ range N, w n
  have herr :
      (fun n => w n • (y n - L)) =o[atTop] w := by
    have hy0 : Tendsto (fun n => y n - L) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hy
    have hlo :
        (fun n => y n - L) =o[atTop] (fun _ => (1 : ℝ)) :=
      (isLittleO_one_iff ℝ).mpr hy0
    simpa only [smul_eq_mul, mul_one] using
      (isBigO_refl w atTop).smul_isLittleO hlo
  have hsum :
      (fun N => ∑ n ∈ range N, w n • (y n - L)) =o[atTop] W := by
    simpa only [W] using herr.sum_range hw hW
  have hzero :
      Tendsto
        (fun N => (W N)⁻¹ •
          ∑ n ∈ range N, w n • (y n - L))
        atTop (𝓝 0) :=
    hsum.tendsto_inv_smul_nhds_zero
  rw [← tendsto_sub_nhds_zero_iff]
  refine hzero.congr' ?_
  have hWpos : ∀ᶠ N in atTop, 0 < W N :=
    hW.eventually_gt_atTop 0
  filter_upwards [hWpos] with N hWN
  simp only [W] at hWN ⊢
  have hsumw :
      (∑ n ∈ range N, w n)⁻¹ * (∑ n ∈ range N, w n) = 1 :=
    inv_mul_cancel₀ hWN.ne'
  calc
    (∑ n ∈ range N, w n)⁻¹ •
          ∑ n ∈ range N, w n • (y n - L) =
        (∑ n ∈ range N, w n)⁻¹ •
          ((∑ n ∈ range N, w n • y n) -
            ∑ n ∈ range N, w n • L) := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      exact smul_sub _ _ _
    _ = (∑ n ∈ range N, w n)⁻¹ •
          (∑ n ∈ range N, w n • y n) -
        (∑ n ∈ range N, w n)⁻¹ •
          (∑ n ∈ range N, w n • L) := by
      exact smul_sub _ _ _
    _ = (∑ n ∈ range N, w n)⁻¹ •
          (∑ n ∈ range N, w n • y n) -
        ((∑ n ∈ range N, w n)⁻¹ *
          (∑ n ∈ range N, w n)) • L := by
      rw [← Finset.sum_smul, smul_smul]
    _ = (∑ n ∈ range N, w n)⁻¹ •
          (∑ n ∈ range N, w n • y n) - L := by
      rw [hsumw, one_smul]

/-- If normalized partial sums converge along a divergent scale, every
nonnegative lower-semicontinuous two-homogeneous capacity which is uniformly
bounded on the unnormalized sums annihilates their limit direction. -/
theorem lowerSemicontinuous_twoHomogeneous_normalizedBudget_annihilates_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℝ) (partialSum : ℕ → E) (scale : ℕ → ℝ) (L : E)
    (hscale : Tendsto scale atTop atTop)
    (hnormalized :
      Tendsto (fun N => (scale N)⁻¹ • partialSum N) atTop (𝓝 L))
    (hqnonneg : ∀ v, 0 ≤ q v)
    (hqhom : ∀ (r : ℝ) v, q (r • v) = r ^ (2 : ℕ) * q v)
    (hlsc : LowerSemicontinuousAt q L)
    {M : ℝ} (hbudget : ∀ N, q (partialSum N) ≤ M) :
    q L = 0 := by
  have hinv : Tendsto (fun N => (scale N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  have hbound0 :
      Tendsto (fun N => (scale N)⁻¹ ^ (2 : ℕ) * M)
        atTop (𝓝 0) := by
    simpa using (hinv.pow 2).mul_const M
  have hqnormalized0 :
      Tendsto
        (fun N => q ((scale N)⁻¹ • partialSum N))
        atTop (𝓝 0) := by
    refine squeeze_zero
      (f := fun N => q ((scale N)⁻¹ • partialSum N))
      (g := fun N => (scale N)⁻¹ ^ (2 : ℕ) * M) ?_ ?_ hbound0
    · exact fun N => hqnonneg _
    · intro N
      calc
        q ((scale N)⁻¹ • partialSum N) =
            (scale N)⁻¹ ^ (2 : ℕ) * q (partialSum N) :=
          hqhom _ _
        _ ≤ (scale N)⁻¹ ^ (2 : ℕ) * M :=
          mul_le_mul_of_nonneg_left (hbudget N) (sq_nonneg _)
  apply le_antisymm ?_ (hqnonneg L)
  by_contra hnot
  have hpos : 0 < q L := lt_of_not_ge hnot
  have hhalf : q L / 2 < q L := by linarith
  have hlower :
      ∀ᶠ v in 𝓝 L, q L / 2 < q v :=
    hlsc (q L / 2) hhalf
  have hlower' :
      ∀ᶠ N in atTop,
        q L / 2 < q ((scale N)⁻¹ • partialSum N) :=
    hnormalized.eventually hlower
  have hupper :
      ∀ᶠ N in atTop,
        q ((scale N)⁻¹ • partialSum N) < q L / 2 :=
    hqnormalized0.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hlo, hup⟩ := (hlower'.and hupper).exists
  linarith

/-- The `(M+1)`-renormalized actual Xi depth-successor defect. -/
def xiDepthMomentReporter (u : ℂ) (M : ℕ) : ℂ :=
  (((M + 1 : ℕ) : ℂ)) *
    (xiDepthSuccessorTransport ((((M + 1 : ℕ) : ℂ)⁻¹)) u -
      xiDepthSuccessorTransport 0 u)

/-- Renormalized actual depth successors converge to the Xi logarithmic
connection at every point outside the Xi divisor. -/
theorem tendsto_xiDepthMomentReporter
    {u : ℂ} (hu : xi u ≠ 0) :
    Tendsto (xiDepthMomentReporter u) atTop
      (𝓝 (-u * logDeriv xi u)) := by
  have heps :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹))
        atTop (𝓝[≠] 0) :=
    GaloisForLFunctions.tendsto_natCast_inv_complex_nhdsNE.comp
      (tendsto_add_atTop_nat 1)
  have h :=
    (tendsto_xiDepthSuccessorTransport_differenceQuotient hu).comp heps
  refine h.congr' (Eventually.of_forall fun M => ?_)
  simp only [Function.comp_apply, xiDepthMomentReporter]
  rw [inv_inv]

/-- Harmonic weight forced by one adjacent depth step. -/
def xiHarmonicDepthWeight (M : ℕ) : ℝ :=
  ((M + 1 : ℕ) : ℝ)⁻¹

/-- Harmonic mass of the first `N` depth steps. -/
def xiHarmonicDepthScale (N : ℕ) : ℝ :=
  ∑ M ∈ range N, xiHarmonicDepthWeight M

/-- Literal, unrenormalized Xi depth-successor defect. -/
def xiDepthSuccessorDefect (u : ℂ) (M : ℕ) : ℂ :=
  xiHarmonicDepthWeight M • xiDepthMomentReporter u M

/-- Reporter image of the first `N` shells of the literal Wold vacuum. -/
def xiDepthVacuumPartialReporter (u : ℂ) (N : ℕ) : ℂ :=
  ∑ M ∈ range N, xiDepthSuccessorDefect u M

/-- The harmonic definition is exactly the actual Xi depth transport minus
its zero-depth value; no fitted reporter is introduced. -/
theorem xiDepthSuccessorDefect_eq_transport_sub
    (u : ℂ) (M : ℕ) :
    xiDepthSuccessorDefect u M =
      xiDepthSuccessorTransport ((((M + 1 : ℕ) : ℂ)⁻¹)) u -
        xiDepthSuccessorTransport 0 u := by
  rw [xiDepthSuccessorDefect, xiHarmonicDepthWeight,
    xiDepthMomentReporter]
  change
    (((((M + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) *
          ((((M + 1 : ℕ) : ℂ)) *
            (xiDepthSuccessorTransport ((((M + 1 : ℕ) : ℂ)⁻¹)) u -
              xiDepthSuccessorTransport 0 u)) =
      xiDepthSuccessorTransport ((((M + 1 : ℕ) : ℂ)⁻¹)) u -
        xiDepthSuccessorTransport 0 u
  rw [← mul_assoc]
  push_cast
  have hne : (M : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show M + 1 ≠ 0 by omega)
  rw [inv_mul_cancel₀ hne, one_mul]

/-- Harmonic depth mass diverges. -/
theorem tendsto_xiHarmonicDepthScale_atTop :
    Tendsto xiHarmonicDepthScale atTop atTop := by
  convert Real.tendsto_sum_range_one_div_nat_succ_atTop using 1
  funext N
  apply Finset.sum_congr rfl
  intro M hM
  simp only [xiHarmonicDepthWeight,
    one_div, Nat.cast_add, Nat.cast_one]

/-- Actual Wold shell source mass has the forced prime-two exponential
envelope. -/
theorem shellSourceMass_isBigO_inv_two_pow :
    shellSourceMass =O[atTop]
      (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) := by
  have hscaled :
      scaledShellSourceMass =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    exact tendsto_scaledShellSourceMass.isBigO_one ℝ
  have hprod :
      (fun n : ℕ =>
        scaledShellSourceMass n * ((2 : ℝ) ^ n)⁻¹) =O[atTop]
        (fun n : ℕ => (1 : ℝ) * ((2 : ℝ) ^ n)⁻¹) :=
    hscaled.mul
      (isBigO_refl (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop)
  refine hprod.congr' ?_ (Eventually.of_forall fun n => by simp)
  filter_upwards [] with n
  rw [scaledShellSourceMass_eq]
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The squared norm series of the canonical depth-moment source vector is
summable.  This also gives the graph-null sequence behind nonclosability. -/
theorem summable_woldDepthMoment_normSq :
    Summable
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * shellSourceMass (n + 2)) := by
  have hmassShift :
      (fun n : ℕ => shellSourceMass (n + 2)) =O[atTop]
        (fun n : ℕ => ((2 : ℝ) ^ (n + 2))⁻¹) :=
    shellSourceMass_isBigO_inv_two_pow.comp_tendsto
      (tendsto_add_atTop_nat 2)
  have hpoly :
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =O[atTop]
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) :=
    isBigO_refl _ _
  apply summable_of_isBigO_nat
    (g := fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * ((2 : ℝ) ^ (n + 2))⁻¹)
  · have hbase :
        Summable (fun n : ℕ =>
          (n : ℝ) ^ (2 : ℕ) * (1 / 2 : ℝ) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
    have hshift :
        Summable (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * (1 / 2 : ℝ) ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    apply (hshift.mul_left (1 / 2 : ℝ)).congr
    intro n
    have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
    rw [hhalf]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [inv_pow]
    ring
  · exact hpoly.mul hmassShift

/-- The literal Wold-vacuum shell masses are summable. -/
theorem summable_woldVacuumShellMass :
    Summable (fun n : ℕ => shellSourceMass (n + 2)) := by
  apply Summable.of_nonneg_of_le
    (fun n => (shellSourceMass_pos (n := n + 2) (by omega)).le)
    (fun n => ?_)
    summable_woldDepthMoment_normSq
  have hmass :
      0 ≤ shellSourceMass (n + 2) :=
    (shellSourceMass_pos (n := n + 2) (by omega)).le
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
    nlinarith
  nlinarith

/-- The reporter of the literal Wold-vacuum truncation, divided by harmonic
depth, converges to the Xi logarithmic connection. -/
theorem tendsto_normalized_xiDepthVacuumPartialReporter
    {u : ℂ} (hu : xi u ≠ 0) :
    Tendsto
      (fun N =>
        (xiHarmonicDepthScale N)⁻¹ •
          xiDepthVacuumPartialReporter u N)
      atTop (𝓝 (-u * logDeriv xi u)) := by
  have h :=
    weightedCesaro_smul (tendsto_xiDepthMomentReporter hu)
      xiHarmonicDepthWeight
      (fun M => by
        rw [xiHarmonicDepthWeight]
        positivity)
      tendsto_xiHarmonicDepthScale_atTop
  simpa only [xiHarmonicDepthScale, xiDepthVacuumPartialReporter,
    xiDepthSuccessorDefect] using h

/-- A uniformly budgeted stable capacity on actual Wold-vacuum truncations
must annihilate the Xi logarithmic connection. -/
theorem xiDepthVacuum_lowerSemicontinuous_capacity_budget_annihilates_connection
    {u : ℂ} (hu : xi u ≠ 0)
    (q : ℂ → ℝ)
    (hqnonneg : ∀ v, 0 ≤ q v)
    (hqhom : ∀ (r : ℝ) v, q (r • v) = r ^ (2 : ℕ) * q v)
    (hlsc : LowerSemicontinuousAt q (-u * logDeriv xi u))
    {M : ℝ}
    (hbudget : ∀ N, q (xiDepthVacuumPartialReporter u N) ≤ M) :
    q (-u * logDeriv xi u) = 0 :=
  lowerSemicontinuous_twoHomogeneous_normalizedBudget_annihilates_limit
    q (xiDepthVacuumPartialReporter u) xiHarmonicDepthScale
    (-u * logDeriv xi u)
    tendsto_xiHarmonicDepthScale_atTop
    (tendsto_normalized_xiDepthVacuumPartialReporter hu)
    hqnonneg hqhom hlsc hbudget

/-- Any stable capacity which strictly detects the Xi logarithmic connection
is not uniformly bounded on the actual Wold-vacuum truncations. -/
theorem xiDepthVacuum_detecting_capacity_not_uniformly_bounded
    {u : ℂ} (hu : xi u ≠ 0)
    (q : ℂ → ℝ)
    (hqnonneg : ∀ v, 0 ≤ q v)
    (hqhom : ∀ (r : ℝ) v, q (r • v) = r ^ (2 : ℕ) * q v)
    (hlsc : LowerSemicontinuousAt q (-u * logDeriv xi u))
    (hdetect : 0 < q (-u * logDeriv xi u)) :
    ¬ ∃ M : ℝ,
      ∀ N, q (xiDepthVacuumPartialReporter u N) ≤ M := by
  rintro ⟨M, hbudget⟩
  have hzero :=
    xiDepthVacuum_lowerSemicontinuous_capacity_budget_annihilates_connection
      hu q hqnonneg hqhom hlsc hbudget
  linarith

end RHTower

