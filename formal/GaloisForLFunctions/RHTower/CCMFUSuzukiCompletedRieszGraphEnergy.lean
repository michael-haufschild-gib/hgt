import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorUnitRieszWeld
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.DeningerAbelSummation
import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.SuzukiCoupledErrorCriticalDerivative

/-!
# Unconditional completed Riesz graph energy

The universal CCM-FU/Suzuki scalar itself is RH-equivalent, but its source-faithful radial graph
derivative has an unconditional finite energy.  The key point is an exact successor law before
estimation: the increment of the completed square-root Riesz moment is the completed Chebyshev
prefix multiplied by one square-root mesh edge.  The prime, polar, and Gamma terms never split.

The prime number theorem makes the resulting singular graph derivative square-summable.  This is
strictly weaker than boundedness of the window: square-summable increments need not have bounded
partial sums.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open ArithmeticFunction Finset

/-- Public prefix form of the completed prime--polar source. -/
theorem sum_Icc_vonMangoldt_sub_one_eq_psiRemainder_graph (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
      (ArithmeticFunction.vonMangoldt k - 1)) = psiRemainder M := by
  rw [Finset.sum_sub_distrib, sum_Icc_vonMangoldt_eq_psi]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  rw [psiRemainder, chebyshevPsi_eq_psi]
  norm_num

/-- The full finite source prefix is `psi(M)-M` plus the unique Gamma atom. -/
theorem sum_completedPrimePolarGammaAtom_eq_psiRemainder_add_gamma
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 M, completedPrimePolarGammaAtom k) =
      psiRemainder M + 2 * Real.eulerMascheroniConstant := by
  have hgamma :
      (∑ k ∈ Finset.Icc 1 M,
        if k = 1 then 2 * Real.eulerMascheroniConstant else 0) =
        2 * Real.eulerMascheroniConstant := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro b hb hbne
      rw [if_neg hbne]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨by omega, hM⟩)).elim
  rw [show (∑ k ∈ Finset.Icc 1 M, completedPrimePolarGammaAtom k) =
      (∑ k ∈ Finset.Icc 1 M,
        (ArithmeticFunction.vonMangoldt k - 1)) +
      ∑ k ∈ Finset.Icc 1 M,
        (if k = 1 then 2 * Real.eulerMascheroniConstant else 0) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [completedPrimePolarGammaAtom]]
  rw [sum_Icc_vonMangoldt_sub_one_eq_psiRemainder_graph, hgamma]

/-- Exact successor law for the pre-scalar completed Riesz moment.  This is a finite conservation
law: every old coefficient sees the same mesh displacement and the new coefficient joins at that
same displacement, so the entire source remains one completed prefix. -/
theorem mobiusDivisorSquareRootAbelMoment_succ_sub
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorSquareRootAbelMoment (M + 1) -
        mobiusDivisorSquareRootAbelMoment M =
      (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
        (psiRemainder M + 2 * Real.eulerMascheroniConstant) := by
  rw [← sum_completedPrimePolarGammaAtom_mul_sqrtGap_eq_mobiusMoment (M + 1),
    ← sum_completedPrimePolarGammaAtom_mul_sqrtGap_eq_mobiusMoment M]
  have htop : M + 1 - 1 = M := by omega
  have hpred : M - 1 + 1 = M := Nat.sub_add_cancel hM
  rw [htop]
  have hzeroExtend :
      (∑ k ∈ Finset.Icc 1 (M - 1),
        completedPrimePolarGammaAtom k * (Real.sqrt M - Real.sqrt k)) =
      ∑ k ∈ Finset.Icc 1 M,
        completedPrimePolarGammaAtom k * (Real.sqrt M - Real.sqrt k) := by
    rw [← hpred, Finset.sum_Icc_succ_top (by omega : 1 ≤ M - 1 + 1)]
    simp
  rw [hzeroExtend]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ k ∈ Finset.Icc 1 M,
      (completedPrimePolarGammaAtom k *
          (Real.sqrt (M + 1 : ℕ) - Real.sqrt k) -
        completedPrimePolarGammaAtom k *
          (Real.sqrt M - Real.sqrt k))) =
      ∑ k ∈ Finset.Icc 1 M,
        (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
          completedPrimePolarGammaAtom k := by
            apply Finset.sum_congr rfl
            intro k _hk
            ring
    _ = (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
        (∑ k ∈ Finset.Icc 1 M, completedPrimePolarGammaAtom k) := by
          rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_completedPrimePolarGammaAtom_eq_psiRemainder_add_gamma hM]

/-- Singular graph derivative of the actual pre-scalar completed Riesz producer.  Index shifting
keeps the denominator positive at every natural index. -/
def completedRieszGraphIncrement (k : ℕ) : ℝ :=
  (mobiusDivisorSquareRootAbelMoment (k + 2) -
      mobiusDivisorSquareRootAbelMoment (k + 1)) / (k + 1 : ℕ)

/-- Source-faithful normal form of every graph edge. -/
theorem completedRieszGraphIncrement_eq (k : ℕ) :
    completedRieszGraphIncrement k =
      ((Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) / (k + 1 : ℕ)) *
        (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) := by
  rw [completedRieszGraphIncrement,
    mobiusDivisorSquareRootAbelMoment_succ_sub (by omega : 1 ≤ k + 1)]
  ring

private theorem sq_sqrtSucc_sub_sqrt_le_inv (k : ℕ) :
    (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) ^ (2 : ℕ) ≤
      1 / (k + 1 : ℕ) := by
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hks : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  have hs1 : Real.sqrt (k + 1 : ℕ) ^ (2 : ℕ) = (k + 1 : ℕ) :=
    Real.sq_sqrt hk.le
  have hs2 : Real.sqrt (k + 2 : ℕ) ^ (2 : ℕ) = (k + 2 : ℕ) :=
    Real.sq_sqrt hks.le
  have hsum : Real.sqrt (k + 1 : ℕ) ≤ Real.sqrt (k + 2 : ℕ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  let d := Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)
  let s := Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)
  have hds : d * s = 1 := by
    dsimp only [d, s]
    calc
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) *
          (Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)) =
        Real.sqrt (k + 2 : ℕ) ^ (2 : ℕ) - Real.sqrt (k + 1 : ℕ) ^ (2 : ℕ) := by ring
      _ = 1 := by rw [hs2, hs1]; norm_num
  have hdenSq : (k + 1 : ℕ) ≤
      (Real.sqrt (k + 2 : ℕ) + Real.sqrt (k + 1 : ℕ)) ^ (2 : ℕ) := by
    nlinarith [Real.sqrt_nonneg (k + 1 : ℕ), Real.sqrt_nonneg (k + 2 : ℕ)]
  apply (le_div_iff₀ hk).2
  have hmul : d ^ (2 : ℕ) * (k + 1 : ℕ) ≤ d ^ (2 : ℕ) * s ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left (by simpa only [s] using hdenSq) (sq_nonneg d)
  have hone : d ^ (2 : ℕ) * s ^ (2 : ℕ) = 1 := by nlinarith [hds]
  simpa only [d] using hmul.trans_eq hone

private theorem abs_psiRemainder_le_eight_mul (k : ℕ) :
    |psiRemainder (k + 1)| ≤ 8 * (k + 1 : ℕ) := by
  exact abs_psiRemainder_le (k + 1)

private theorem psiRemainder_eq_realError (k : ℕ) :
    psiRemainder (k + 1) =
      Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1) := by
  simp [psiRemainder, chebyshevPsi_eq_psi]

/-- Pointwise domination by the PNT's summable error weight plus a cubic Gamma tail. -/
theorem sq_completedRieszGraphIncrement_le_majorant (k : ℕ) :
    completedRieszGraphIncrement k ^ (2 : ℕ) ≤
      8 *
          (|Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)| *
            (2 / (((k : ℝ) + 1) ^ (2 : ℕ)))) +
        2 * (2 * Real.eulerMascheroniConstant) ^ (2 : ℕ) /
          (((k : ℝ) + 1) ^ (3 : ℕ)) := by
  let n : ℝ := (k : ℝ) + 1
  let R : ℝ := psiRemainder (k + 1)
  let G : ℝ := 2 * Real.eulerMascheroniConstant
  have hn : 0 < n := by positivity
  have hmesh := sq_sqrtSucc_sub_sqrt_le_inv k
  have hR := abs_psiRemainder_le_eight_mul k
  have hR2 : R ^ (2 : ℕ) ≤ 8 * n * |R| := by
    have hnonneg : 0 ≤ |R| := abs_nonneg R
    have hm := mul_le_mul_of_nonneg_right hR hnonneg
    calc
      R ^ (2 : ℕ) = |R| * |R| := by
        rw [pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg R)]
      _ ≤ 8 * (k + 1 : ℕ) * |R| := hm
      _ = 8 * n * |R| := by simp only [n, Nat.cast_add, Nat.cast_one]
  rw [completedRieszGraphIncrement_eq]
  have hshape :
      (((Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) / (k + 1 : ℕ)) *
        (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant)) ^ (2 : ℕ) =
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) ^ (2 : ℕ) / n ^ (2 : ℕ) *
        (R + G) ^ (2 : ℕ) := by
    dsimp only [n, R, G]
    push_cast
    field_simp
  rw [hshape]
  have hsumSq : (R + G) ^ (2 : ℕ) ≤ 2 * (R ^ (2 : ℕ) + G ^ (2 : ℕ)) := by nlinarith [sq_nonneg (R - G)]
  have hfirst :
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) ^ (2 : ℕ) / n ^ (2 : ℕ) *
          (R + G) ^ (2 : ℕ) ≤
        (1 / n) / n ^ (2 : ℕ) * (2 * (R ^ (2 : ℕ) + G ^ (2 : ℕ))) := by
    gcongr
    · simpa only [n, Nat.cast_add, Nat.cast_one] using hmesh
  calc
    (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) ^ (2 : ℕ) / n ^ (2 : ℕ) *
          (R + G) ^ (2 : ℕ) ≤
        (1 / n) / n ^ (2 : ℕ) * (2 * (R ^ (2 : ℕ) + G ^ (2 : ℕ))) := hfirst
    _ ≤ 16 * |R| / n ^ (2 : ℕ) + 2 * G ^ (2 : ℕ) / n ^ (3 : ℕ) := by
      have hcoef : 0 ≤ 2 / n ^ (3 : ℕ) := by positivity
      have hRterm : 2 * R ^ (2 : ℕ) / n ^ (3 : ℕ) ≤ 16 * |R| / n ^ (2 : ℕ) := by
        calc
          2 * R ^ (2 : ℕ) / n ^ (3 : ℕ) = (2 / n ^ (3 : ℕ)) * R ^ (2 : ℕ) := by ring
          _ ≤ (2 / n ^ (3 : ℕ)) * (8 * n * |R|) :=
            mul_le_mul_of_nonneg_left hR2 hcoef
          _ = 16 * |R| / n ^ (2 : ℕ) := by field_simp [hn.ne']; ring
      calc
        (1 / n) / n ^ (2 : ℕ) * (2 * (R ^ (2 : ℕ) + G ^ (2 : ℕ))) =
            2 * R ^ (2 : ℕ) / n ^ (3 : ℕ) + 2 * G ^ (2 : ℕ) / n ^ (3 : ℕ) := by
              field_simp [hn.ne']
        _ ≤ 16 * |R| / n ^ (2 : ℕ) + 2 * G ^ (2 : ℕ) / n ^ (3 : ℕ) :=
          add_le_add hRterm (le_refl _)
    _ = 8 * (|Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)| *
          (2 / (((k : ℝ) + 1) ^ (2 : ℕ)))) +
        2 * (2 * Real.eulerMascheroniConstant) ^ (2 : ℕ) /
          (((k : ℝ) + 1) ^ (3 : ℕ)) := by
      rw [← psiRemainder_eq_realError k]
      dsimp only [n, R, G]
      ring

/-- **Unconditional completed-source graph energy.**  The literal prime--polar--Gamma Riesz
producer has finite singular graph energy on all cofinal aperture edges. -/
theorem summable_sq_completedRieszGraphIncrement :
    Summable (fun k : ℕ => completedRieszGraphIncrement k ^ (2 : ℕ)) := by
  have hprime : Summable (fun k : ℕ =>
      8 *
        (|Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)| *
          (2 / (((k : ℝ) + 1) ^ (2 : ℕ))))) :=
    summable_psi_error_weight.mul_left 8
  have hcube0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (3 : ℕ))) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hcube : Summable (fun k : ℕ =>
      2 * (2 * Real.eulerMascheroniConstant) ^ (2 : ℕ) /
        (((k : ℝ) + 1) ^ (3 : ℕ))) := by
    have hshift : Summable (fun k : ℕ => 1 / ((((k + 1 : ℕ) : ℝ)) ^ (3 : ℕ))) :=
      (summable_nat_add_iff 1).2 hcube0
    refine (hshift.mul_left (2 * (2 * Real.eulerMascheroniConstant) ^ (2 : ℕ))).congr
      (fun k => ?_)
    push_cast
    ring
  exact Summable.of_nonneg_of_le
    (fun k => sq_nonneg (completedRieszGraphIncrement k))
    sq_completedRieszGraphIncrement_le_majorant (hprime.add hcube)

/-- Same finite graph energy in the normalized Suzuki unit-aperture coordinate. -/
theorem summable_sq_weighted_unitApertureWindow_increment :
    Summable fun k : ℕ =>
      ((((k + 2 : ℕ) : ℝ) * completedPrimePolarGammaUnitApertureWindow (k + 2) -
          ((k + 1 : ℕ) : ℝ) * completedPrimePolarGammaUnitApertureWindow (k + 1)) /
        (2 * ((k + 1 : ℕ) : ℝ))) ^ (2 : ℕ) := by
  refine summable_sq_completedRieszGraphIncrement.congr (fun k => ?_)
  have h1 := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
    (M := k + 1) (by omega : 1 ≤ k + 1)
  have h2 := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
    (M := k + 2) (by omega : 1 ≤ k + 2)
  have hedge : completedRieszGraphIncrement k =
      (((k + 2 : ℕ) : ℝ) * completedPrimePolarGammaUnitApertureWindow (k + 2) -
          ((k + 1 : ℕ) : ℝ) * completedPrimePolarGammaUnitApertureWindow (k + 1)) /
        (2 * ((k + 1 : ℕ) : ℝ)) := by
    rw [completedRieszGraphIncrement, h1, h2]
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hk]
  exact congrArg (fun x : ℝ => x ^ (2 : ℕ)) hedge

/-! ## Exact zero charge in the harmonic source clock -/

/-- Harmonic-clock readout of the same completed prime--polar--Gamma prefix. -/
def completedPrimePolarGammaHarmonicCharge (k : ℕ) : ℝ :=
  (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
    (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))

private theorem hasSum_harmonicGraphClock :
    HasSum (fun k : ℕ =>
      1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hpartial : ∀ N : ℕ,
        (∑ k ∈ Finset.range N,
          (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) =
            1 - 1 / ((N : ℝ) + 1) := by
      intro N
      induction N with
      | zero => norm_num
      | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
          have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
          field_simp [h1, h2]
          ring
    simp_rw [hpartial]
    simpa using
      (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)))
  · intro k
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [sub_nonneg, div_le_div_iff₀ h2 h1]
    nlinarith

/-- **Exact completed harmonic cancellation.**  Mertens' Abel tail is precisely cancelled by
the Gamma atom: the absolutely convergent harmonic charge of the literal completed source is
zero.  No prime, polar, or Gamma region is estimated separately. -/
theorem hasSum_completedPrimePolarGammaHarmonicCharge_zero :
    HasSum completedPrimePolarGammaHarmonicCharge 0 := by
  have hpsi0 : HasSum (fun k : ℕ =>
      psiError k * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)))
      mertensAbelTail := by
    rw [mertensAbelTail]
    exact summable_psiError_increment.hasSum
  have hpsi : HasSum (fun k : ℕ =>
      psiRemainder (k + 1) *
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)))
      (-2 * Real.eulerMascheroniConstant) := by
    have h : HasSum (fun k : ℕ =>
        psiRemainder (k + 1) *
          (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)))
        mertensAbelTail := by
      simpa [psiError, psiRemainder, chebyshevPsi_eq_psi] using hpsi0
    simpa only [mertensAbelTail_eq] using h
  have hgamma :=
    hasSum_harmonicGraphClock.mul_left (2 * Real.eulerMascheroniConstant)
  have hcompleted := hpsi.add hgamma
  convert hcompleted using 1
  · funext k
    rw [completedPrimePolarGammaHarmonicCharge]
    ring
  · ring

/-- Absolute convergence accompanies the exact zero completed charge. -/
theorem summable_completedPrimePolarGammaHarmonicCharge :
    Summable completedPrimePolarGammaHarmonicCharge :=
  hasSum_completedPrimePolarGammaHarmonicCharge_zero.summable

/-! ## Exact clock transmutation

The harmonic charge is absolutely summable and has total mass zero, but the square-root Riesz
producer reads it through an unbounded moving clock.  The following identities retain that signed
cancellation exactly: no absolute value is introduced before the final Abel transform.
-/

/-- Ratio converting one completed harmonic edge into its square-root Riesz edge. -/
def completedRieszHarmonicClockRatio (k : ℕ) : ℝ :=
  (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) /
    (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))

/-- Every source edge is unchanged by passage from the harmonic clock to the square-root clock. -/
theorem completedPrimePolarGammaHarmonicCharge_mul_clockRatio (k : ℕ) :
    completedPrimePolarGammaHarmonicCharge k * completedRieszHarmonicClockRatio k =
      (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
        (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hgap_eq : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) =
      1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [h1.ne', h2.ne']
    ring
  rw [completedPrimePolarGammaHarmonicCharge, completedRieszHarmonicClockRatio]
  rw [hgap_eq]
  field_simp [h1.ne', h2.ne']

/-- The completed Riesz moment is the discrete flux of the literal completed Chebyshev prefix
through the square-root mesh. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      ∑ k ∈ Finset.range (M - 1),
        (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
          (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) := by
  induction M, hM using Nat.le_induction with
  | base =>
      rw [← sum_completedPrimePolarGammaAtom_mul_sqrtGap_eq_mobiusMoment 1]
      norm_num
  | succ M hM ih =>
      have hpred : M + 1 - 1 = M := by omega
      have hsum :
          (∑ k ∈ Finset.range M,
            (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
              (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))) =
            (∑ k ∈ Finset.range (M - 1),
              (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
                (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))) +
              (psiRemainder M + 2 * Real.eulerMascheroniConstant) *
                (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) := by
        have hm1 : M - 1 + 1 = M := Nat.sub_add_cancel hM
        have hm2 : M - 1 + 2 = M + 1 := by omega
        rw [← hm1, Finset.sum_range_succ, hm1, hm2]
      rw [hpred, hsum, ← ih]
      have hstep := mobiusDivisorSquareRootAbelMoment_succ_sub hM
      nlinarith

/-- Exact transmutation of the finite completed source from harmonic into square-root time. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_harmonicCharge_clock
    {M : ℕ} (hM : 1 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      ∑ k ∈ Finset.range (M - 1),
        completedPrimePolarGammaHarmonicCharge k *
          completedRieszHarmonicClockRatio k := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh hM]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (completedPrimePolarGammaHarmonicCharge_mul_clockRatio k).symm

/-- **Signed Abel tail law.**  The RH-equivalent Riesz producer is exactly a moving boundary
readout of harmonic partial charges plus their signed interaction with clock acceleration.  This
is the source-faithful obstruction left after the unconditional zero-total-charge law. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_harmonicPrefix_clockAcceleration
    {M : ℕ} (hM : 2 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      deningerPartialSum completedPrimePolarGammaHarmonicCharge (M - 2) *
          completedRieszHarmonicClockRatio (M - 2) +
        ∑ k ∈ Finset.range (M - 2),
          deningerPartialSum completedPrimePolarGammaHarmonicCharge k *
            (completedRieszHarmonicClockRatio k -
              completedRieszHarmonicClockRatio (k + 1)) := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_harmonicCharge_clock
    (by omega : 1 ≤ M)]
  have hlen : M - 2 + 1 = M - 1 := by omega
  simpa only [hlen] using
    (deningerAbelSummation completedPrimePolarGammaHarmonicCharge
      completedRieszHarmonicClockRatio (M - 2))

/-- Completed harmonic prefixes converge to zero without splitting prime, polar, and Gamma
regions.  The remaining difficulty is their rate against the accelerating square-root clock. -/
theorem tendsto_completedPrimePolarGammaHarmonicPrefix_zero :
    Tendsto (fun N : ℕ =>
      deningerPartialSum completedPrimePolarGammaHarmonicCharge N) atTop (nhds 0) := by
  change Tendsto
    ((fun n : ℕ => ∑ i ∈ Finset.range n,
      completedPrimePolarGammaHarmonicCharge i) ∘ fun N : ℕ => N + 1)
    atTop (nhds 0)
  exact
    hasSum_completedPrimePolarGammaHarmonicCharge_zero.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)

/-- Exact tail form of the zero-charge conservation law at every moving boundary. -/
theorem hasSum_completedPrimePolarGammaHarmonicCharge_tail
    (N : ℕ) :
    HasSum (fun k : ℕ => completedPrimePolarGammaHarmonicCharge (k + (N + 1)))
      (-deningerPartialSum completedPrimePolarGammaHarmonicCharge N) := by
  have h := (hasSum_nat_add_iff' (f := completedPrimePolarGammaHarmonicCharge)
    (N + 1) (g := 0)).2 hasSum_completedPrimePolarGammaHarmonicCharge_zero
  simpa only [deningerPartialSum, zero_sub] using h

/-! ## Suzuki critical-jet landing on the completed Riesz producer -/

/-- Finite pre-scalar Suzuki producer.  The arithmetic coordinate is the right critical jet of
Suzuki's coupled error; the Gamma completion is inserted before the square-root clock is read. -/
def suzukiCompletedRieszCriticalJetApprox (ω : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 1),
    ((1 / 2 : ℝ) * ((suzukiCoupledError ω (k + 1) - 1) / ω) +
        2 * Real.eulerMascheroniConstant) *
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))

/-- **Coefficient-faithful Suzuki landing.**  At every finite aperture, the right critical jet of
the shifted-Euler coupled error converges to the literal completed prime--polar--Gamma Riesz
producer.  Finite support makes passage of the jet through the moving clock unconditional. -/
theorem tendsto_suzukiCompletedRieszCriticalJetApprox
    (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun ω : ℝ => suzukiCompletedRieszCriticalJetApprox ω M)
      (𝓝[>] 0) (nhds (mobiusDivisorSquareRootAbelMoment M)) := by
  have hsum : Tendsto (fun ω : ℝ =>
      ∑ k ∈ Finset.range (M - 1),
        ((1 / 2 : ℝ) * ((suzukiCoupledError ω (k + 1) - 1) / ω) +
            2 * Real.eulerMascheroniConstant) *
          (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)))
      (𝓝[>] 0)
      (nhds (∑ k ∈ Finset.range (M - 1),
        (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
          (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)))) := by
    apply tendsto_finsetSum
    intro k _hk
    have hjet := suzukiCoupledError_critical_derivative_base_one
      (k + 1) (by omega : 1 ≤ k + 1)
    have hscaled := (hjet.const_mul (1 / 2 : ℝ)).add_const
      (2 * Real.eulerMascheroniConstant)
    have hclock := hscaled.mul_const
      (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ))
    convert hclock using 1
    rw [psiRemainder, chebyshevPsi_eq_psi]
    push_cast
    ring_nf
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh hM]
  exact hsum

/-- Normalized critical-jet producer in the exact Suzuki unit-aperture coordinate. -/
def suzukiCompletedUnitApertureCriticalJetApprox (ω : ℝ) (M : ℕ) : ℝ :=
  2 / (M : ℝ) * suzukiCompletedRieszCriticalJetApprox ω M

/-- The same Suzuki critical jet lands on the literal RH-equivalent unit-aperture window. -/
theorem tendsto_suzukiCompletedUnitApertureCriticalJetApprox
    (M : ℕ) (hM : 1 ≤ M) :
    Tendsto (fun ω : ℝ => suzukiCompletedUnitApertureCriticalJetApprox ω M)
      (𝓝[>] 0) (nhds (completedPrimePolarGammaUnitApertureWindow M)) := by
  have h := (tendsto_suzukiCompletedRieszCriticalJetApprox M hM).const_mul
    (2 / (M : ℝ))
  convert h using 1
  · funext ω
    rw [suzukiCompletedUnitApertureCriticalJetApprox]
  · have hMR : (M : ℝ) ≠ 0 := by positivity
    rw [mobiusMoment_eq_half_aperture_mul_unitApertureWindow hM]
    field_simp [hMR]

/-- **Unconditional joint critical/cofinal selection.**  One positive critical parameter can be
selected at every growing aperture so that it tends to zero and the finite Suzuki affine producer
tracks the literal completed Riesz moment with vanishing absolute error.  This closes existence of
a coefficient-faithful joint limit; it deliberately supplies no uniform bound on the tracked
RH-equivalent moments. -/
theorem exists_suzukiCompletedRieszCriticalJetCofinalSchedule :
    ∃ ω : ℕ → ℝ,
      Tendsto ω atTop (nhds 0) ∧
      Tendsto (fun N : ℕ =>
        suzukiCompletedRieszCriticalJetApprox (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)) atTop (nhds 0) ∧
      ∀ N : ℕ,
        0 < ω N ∧
        ω N < 1 / ((N : ℝ) + 1) ∧
        |suzukiCompletedRieszCriticalJetApprox (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)| < 1 / ((N : ℝ) + 1) := by
  have hselect : ∀ N : ℕ, ∃ u : ℝ,
      0 < u ∧ u < 1 / ((N : ℝ) + 1) ∧
        |suzukiCompletedRieszCriticalJetApprox u (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1)| < 1 / ((N : ℝ) + 1) := by
    intro N
    let ε : ℝ := 1 / ((N : ℝ) + 1)
    have hε : 0 < ε := by dsimp only [ε]; positivity
    have hlim := tendsto_suzukiCompletedRieszCriticalJetApprox
      (N + 1) (by omega : 1 ≤ N + 1)
    have herr : ∀ᶠ u : ℝ in 𝓝[>] 0,
        suzukiCompletedRieszCriticalJetApprox u (N + 1) ∈
          Metric.ball (mobiusDivisorSquareRootAbelMoment (N + 1)) ε :=
      hlim.eventually (Metric.ball_mem_nhds _ hε)
    have hcap : ∀ᶠ u : ℝ in 𝓝[>] 0, u ∈ Set.Ioo 0 ε :=
      Ioo_mem_nhdsGT hε
    obtain ⟨u, huerr, hucap⟩ := (herr.and hcap).exists
    refine ⟨u, hucap.1, hucap.2, ?_⟩
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using huerr
  choose ω hωpos hωcap hωerr using hselect
  refine ⟨ω, ?_, ?_, fun N => ⟨hωpos N, hωcap N, hωerr N⟩⟩
  · apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => (hωpos N).le)
      (Filter.Eventually.of_forall fun N => (hωcap N).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => norm_nonneg _)
      (Filter.Eventually.of_forall fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.norm_eq_abs] using (hωerr N).le

/-- The selected joint limit also tracks the normalized, RH-equivalent Suzuki unit-aperture
window.  Thus finite-aperture identification and cofinal diagonal convergence are unconditional;
only a uniform bound on this tracked scalar remains RH-bearing. -/
theorem exists_suzukiCompletedUnitApertureCriticalJetCofinalSchedule :
    ∃ ω : ℕ → ℝ,
      Tendsto ω atTop (nhds 0) ∧
      Tendsto (fun N : ℕ =>
        suzukiCompletedUnitApertureCriticalJetApprox (ω N) (N + 1) -
          completedPrimePolarGammaUnitApertureWindow (N + 1)) atTop (nhds 0) := by
  obtain ⟨ω, hω, hRiesz, _hpoint⟩ :=
    exists_suzukiCompletedRieszCriticalJetCofinalSchedule
  refine ⟨ω, hω, ?_⟩
  have hinv : Tendsto (fun N : ℕ => 1 / (((N + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    have hraw := tendsto_inv_natCast_atTop_zero.comp (tendsto_add_atTop_nat 1)
    simpa [one_div, Function.comp_def] using hraw
  have hfactor : Tendsto (fun N : ℕ => 2 / (((N + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using hinv.const_mul 2
  have hprod : Tendsto (fun N : ℕ =>
      2 / (((N + 1 : ℕ) : ℝ)) *
        (suzukiCompletedRieszCriticalJetApprox (ω N) (N + 1) -
          mobiusDivisorSquareRootAbelMoment (N + 1))) atTop (nhds 0) := by
    simpa only [mul_zero] using hfactor.mul hRiesz
  apply hprod.congr'
  exact Filter.Eventually.of_forall fun N => by
    have hM : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hw := mobiusMoment_eq_half_aperture_mul_unitApertureWindow
      (M := N + 1) (by omega : 1 ≤ N + 1)
    change
      2 / (((N + 1 : ℕ) : ℝ)) *
          (suzukiCompletedRieszCriticalJetApprox (ω N) (N + 1) -
            mobiusDivisorSquareRootAbelMoment (N + 1)) =
        2 / (((N + 1 : ℕ) : ℝ)) *
            suzukiCompletedRieszCriticalJetApprox (ω N) (N + 1) -
          completedPrimePolarGammaUnitApertureWindow (N + 1)
    rw [hw]
    field_simp [hM.ne']

end

end RHTower
