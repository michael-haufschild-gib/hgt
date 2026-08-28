import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinFundamentalSymmetry
import GaloisForLFunctions.RHTower.SourceHorizontalWoldNeutralJetBridge
import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux
import GaloisForLFunctions.HTGeometry.PeriodRigidity
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant collapse of source-horizontal rigged Krein prime packets

This file decides two structural determinant questions left by the source-horizontal SC phase
object.  First, every finite shared-reservoir Gram matrix has the exact rank-one determinant

`det = orientation^m * (1 - m) * ∏ᵢ weightᵢ`.

The source Gamma-Bockstein bound then forces ordinary determinants of the cofinal prime packets to
converge to zero at every point of the open critical strip.  This rules out the raw Gram
determinant as a coefficient-faithful Xi landing.

Second, resolving the common orientation against the absolute weights recovers the signed
Gamma-Bocksteins.  A packet of `m + 2` primes consequently has exact neutral asymptotic order
`m + 2`, with a nonzero leading coefficient equal to a finite product of prime-log jets.  Hence
every renormalizer of any fixed finite pole order still gives zero on all sufficiently large
packets.  A surviving SC determinant construction must therefore regularize with packet-growing
order before wall specialization.

Finally, no arbitrary scalar profile depending only on the horizontal real coordinate can equal
normalized centered Xi: complex differentiability would make that profile constant, contradicting
Xi's nonzero central curvature.  Thus the surviving construction must separately restore a
genuinely complex vertical parameter or operator-valued datum.

All statements are pre-divisor and unconditional.  No Xi zero is selected or enumerated.
-/

open scoped BigOperators
open Complex
open Matrix
open Filter

namespace RHTower

noncomputable section

private def reservoirColumn (m : ℕ) : Matrix (Fin m) (Fin 1) ℝ := fun _ _ => 1
private def reservoirRow (m : ℕ) : Matrix (Fin 1) (Fin m) ℝ := fun _ _ => 1

private theorem reservoirBaseMatrix_apply (m : ℕ) (i j : Fin m) :
    (1 - reservoirColumn m * reservoirRow m : Matrix (Fin m) (Fin m) ℝ) i j =
      if i = j then 0 else -1 := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  simp [reservoirColumn, reservoirRow, Matrix.mul_apply]
  split_ifs <;> ring

private theorem reservoirBaseMatrix_det (m : ℕ) :
    (1 - reservoirColumn m * reservoirRow m).det = (1 : ℝ) - (m : ℝ) := by
  rw [Matrix.det_one_sub_mul_comm]
  have hmatrix :
      (1 - reservoirRow m * reservoirColumn m : Matrix (Fin 1) (Fin 1) ℝ) =
        !![(1 - m : ℝ)] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [reservoirRow, reservoirColumn, Matrix.mul_apply]
  rw [hmatrix]
  simp

private def reservoirSqrtDiagonal {m : ℕ} (w : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => Real.sqrt (w i))

private theorem sourceSharedReservoirMatrix_factor {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    sourceSharedReservoirMatrix w =
      reservoirSqrtDiagonal w *
        (1 - reservoirColumn m * reservoirRow m) *
          reservoirSqrtDiagonal w := by
  ext i j
  rw [sourceSharedReservoirMatrix_apply hw]
  simp only [reservoirSqrtDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [reservoirBaseMatrix_apply]
  split_ifs <;> ring

/-- Exact determinant of the positive weighted shared-reservoir matrix. -/
theorem sourceSharedReservoirMatrix_det {m : ℕ} {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    (sourceSharedReservoirMatrix w).det =
      (1 - m : ℝ) * ∏ i, w i := by
  rw [sourceSharedReservoirMatrix_factor hw, Matrix.det_mul, Matrix.det_mul,
    reservoirBaseMatrix_det]
  change
    (Matrix.diagonal (fun i => Real.sqrt (w i))).det * (1 - (m : ℝ)) *
        (Matrix.diagonal (fun i => Real.sqrt (w i))).det = _
  simp only [Matrix.det_diagonal]
  rw [show (∏ i, √(w i)) * (1 - (m : ℝ)) * (∏ i, √(w i)) =
      (1 - (m : ℝ)) * ((∏ i, √(w i)) * (∏ i, √(w i))) by ring]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← pow_two, Real.sq_sqrt (hw _)]

/-- Scalar orientation contributes its dimension power to the reservoir determinant. -/
theorem orientedSourceSharedReservoirMatrix_det {m : ℕ} (o : ℝ) {w : Fin m → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    (orientedSourceSharedReservoirMatrix o w).det =
      o ^ m * (1 - m : ℝ) * ∏ i, w i := by
  rw [orientedSourceSharedReservoirMatrix, Matrix.det_smul,
    Fintype.card_fin, sourceSharedReservoirMatrix_det hw]
  ring

/-- Exact determinant of every finite pre-divisor shared-reservoir packet. -/
theorem preDivisorSharedReservoirMatrix_det {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) :
    (PreDivisorReflectionDefectStabilization.preDivisorSharedReservoirMatrix s p).det =
      PreDivisorReflectionDefectStabilization.preDivisorOrientation s ^ m *
        (1 - m : ℝ) *
          ∏ i, preDivisorRiggedPrimeWeight s (p i) := by
  rw [PreDivisorReflectionDefectStabilization.preDivisorSharedReservoirMatrix,
    orientedSourceSharedReservoirMatrix_det]
  · rfl
  · intro i
    exact abs_nonneg _

open PreDivisorReflectionDefectStabilization

/-- Uniform geometric contraction dominating every prime weight at a fixed open-strip point. -/
def preDivisorRiggedPrimeDeterminantContraction (s : ℂ) : ℝ :=
  (2 : ℝ) ^ (|preDivisorCenteredRate s| - 1)

/-- The determinant contraction lies strictly between zero and one in the open critical strip. -/
theorem preDivisorRiggedPrimeDeterminantContraction_mem_unit
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    0 < preDivisorRiggedPrimeDeterminantContraction s ∧
      preDivisorRiggedPrimeDeterminantContraction s < 1 := by
  have ht : |preDivisorCenteredRate s| < 1 := by
    rw [abs_lt]
    constructor <;> simp only [preDivisorCenteredRate] <;> linarith [hs.1, hs.2]
  constructor
  · exact Real.rpow_pos_of_pos (by norm_num) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- Every source Gamma-Bockstein prime weight is bounded by the common contraction. -/
theorem preDivisorRiggedPrimeWeight_le_determinantContraction
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (p : Nat.Primes) :
    preDivisorRiggedPrimeWeight s p ≤
      preDivisorRiggedPrimeDeterminantContraction s := by
  have ht : |preDivisorCenteredRate s| - 1 ≤ 0 := by
    have habs : |preDivisorCenteredRate s| < 1 := by
      rw [abs_lt]
      constructor <;> simp only [preDivisorCenteredRate] <;> linarith [hs.1, hs.2]
    linarith
  have hmag :=
    (primeGammaCofinalBocksteinMagnitude_bounds
      (preDivisorCenteredRate s) p).2
  change |primeGammaCofinalBocksteinCoefficient
      (preDivisorCenteredRate s) p| ≤ _
  exact hmag.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast p.2.two_le) ht)

/-- Determinant of the packet on the first `m + 2` source-enumerated ordinary primes. -/
def preDivisorRiggedPrimePacketDeterminant (s : ℂ) (m : ℕ) : ℝ :=
  (preDivisorRiggedPrimeWittGram s
    (fun i : Fin (m + 2) => nthPrimePoint i)).det

/-- Away from the critical wall, the source orientation has unit absolute value. -/
theorem abs_preDivisorOrientation_eq_one_of_offWall
    {s : ℂ} (hoff : s.re ≠ 1 / 2) :
    |preDivisorOrientation s| = 1 := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · rw [preDivisorOrientation_eq_one_of_left s hleft]
    norm_num
  · rw [preDivisorOrientation_eq_neg_one_of_right s hright]
    norm_num

/-- Exact product formula for the source-enumerated finite prime packet. -/
theorem preDivisorRiggedPrimePacketDeterminant_eq
    (s : ℂ) (m : ℕ) :
    preDivisorRiggedPrimePacketDeterminant s m =
      preDivisorOrientation s ^ (m + 2) *
        (1 - (m + 2 : ℕ) : ℝ) *
          ∏ i : Fin (m + 2),
            preDivisorRiggedPrimeWeight s (nthPrimePoint i) := by
  rw [preDivisorRiggedPrimePacketDeterminant,
    preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix]
  · exact preDivisorSharedReservoirMatrix_det s _
  · intro i j hij
    apply Fin.ext
    exact preDivisorRiggedNthPrimePoint_injective hij

/-- Exponentially collapsing upper envelope for finite packet determinants off the wall. -/
theorem abs_preDivisorRiggedPrimePacketDeterminant_le
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (hoff : s.re ≠ 1 / 2)
    (m : ℕ) :
    |preDivisorRiggedPrimePacketDeterminant s m| ≤
      (m + 1 : ℝ) * preDivisorRiggedPrimeDeterminantContraction s ^ (m + 2) := by
  rw [preDivisorRiggedPrimePacketDeterminant_eq, abs_mul, abs_mul, abs_pow,
    abs_preDivisorOrientation_eq_one_of_offWall hoff, one_pow]
  have hscalar : |(1 - (m + 2 : ℕ) : ℝ)| = (m + 1 : ℝ) := by
    rw [abs_of_nonpos]
    · push_cast
      ring
    · push_cast
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
  rw [hscalar]
  have hprod0 : 0 ≤ ∏ i : Fin (m + 2),
      preDivisorRiggedPrimeWeight s (nthPrimePoint i) := by
    exact Finset.prod_nonneg (fun i _ => abs_nonneg _)
  rw [abs_of_nonneg hprod0]
  have hprod :
      (∏ i : Fin (m + 2), preDivisorRiggedPrimeWeight s (nthPrimePoint i)) ≤
        ∏ _i : Fin (m + 2), preDivisorRiggedPrimeDeterminantContraction s :=
    Finset.prod_le_prod
      (s := Finset.univ)
      (fun i _ => abs_nonneg (preDivisorPrimeCarrier s (nthPrimePoint i)))
      (fun i _ => preDivisorRiggedPrimeWeight_le_determinantContraction hs _)
  have hprod' :
      (∏ i : Fin (m + 2), preDivisorRiggedPrimeWeight s (nthPrimePoint i)) ≤
        preDivisorRiggedPrimeDeterminantContraction s ^ (m + 2) := by
    simpa using hprod
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_left hprod' (by positivity : (0 : ℝ) ≤ (m + 1 : ℝ))

private lemma tendsto_natCast_add_one_mul_pow_nhds_zero'
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ) * q ^ n)
      Filter.atTop (nhds 0) := by
  rcases hq0.eq_or_lt with hq | hq
  · rw [← hq]
    refine (tendsto_congr' (show ∀ᶠ n : ℕ in Filter.atTop,
      (n + 1 : ℝ) * 0 ^ n = 0 by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp [Nat.ne_of_gt hn])).mpr tendsto_const_nhds
  · let rho : ℝ := 1 / q
    have hrho : 1 < rho := by
      dsimp only [rho]
      exact (one_lt_div hq).2 hq1
    have hn := tendsto_pow_const_div_const_pow_of_one_lt 1 hrho
    have hpow : Filter.Tendsto (fun n : ℕ => q ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1
    have hadd := hn.add hpow
    simpa only [rho, one_div, inv_pow, div_inv_eq_mul, pow_one, zero_add,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hadd

/-- Off the wall, absolute ordinary packet determinants collapse cofinally to zero. -/
theorem tendsto_abs_preDivisorRiggedPrimePacketDeterminant
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (hoff : s.re ≠ 1 / 2) :
    Filter.Tendsto (fun m : ℕ => |preDivisorRiggedPrimePacketDeterminant s m|)
      Filter.atTop (nhds 0) := by
  let q := preDivisorRiggedPrimeDeterminantContraction s
  have hq := preDivisorRiggedPrimeDeterminantContraction_mem_unit hs
  have hgeom := tendsto_natCast_add_one_mul_pow_nhds_zero' hq.1.le hq.2
  have hupper : Filter.Tendsto
      (fun m : ℕ => (m + 1 : ℝ) * q ^ (m + 2))
      Filter.atTop (nhds 0) := by
    have hscaled := (hgeom.mul_const (q ^ 2))
    convert hscaled using 1
    · funext m
      rw [pow_add]
      ring
    · ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun m => abs_preDivisorRiggedPrimePacketDeterminant_le hs hoff m)
  · exact hupper

/-- Every finite ordinary packet determinant is exactly zero on the critical wall. -/
@[simp] theorem preDivisorRiggedPrimePacketDeterminant_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) (m : ℕ) :
    preDivisorRiggedPrimePacketDeterminant s m = 0 := by
  rw [preDivisorRiggedPrimePacketDeterminant_eq]
  have ho : preDivisorOrientation s = 0 := by
    rw [preDivisorOrientation, preDivisorTailLog, hs]
    norm_num
  rw [ho]
  simp

/-- **Raw determinant collapse.** Ordinary SC prime-packet determinants converge to zero at every
point of the open critical strip, including the wall. -/
theorem tendsto_preDivisorRiggedPrimePacketDeterminant_zero
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    Tendsto (fun m : ℕ => preDivisorRiggedPrimePacketDeterminant s m)
      atTop (nhds 0) := by
  by_cases hoff : s.re = 1 / 2
  · have hzero :
        (fun m : ℕ => preDivisorRiggedPrimePacketDeterminant s m) =
          fun _ => 0 := by
      funext m
      exact preDivisorRiggedPrimePacketDeterminant_eq_zero_of_re_eq_half hoff m
    rw [hzero]
    exact tendsto_const_nhds
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using
      tendsto_abs_preDivisorRiggedPrimePacketDeterminant hs hoff

/-- Real transverse wall coordinate, normalized so its centered horizontal rate is exactly `t`. -/
def preDivisorRiggedNeutralSpectralPoint (t : ℝ) : ℂ :=
  (((t + 1) / 2 : ℝ) : ℂ)

/-- Real part of the normalized transverse wall coordinate. -/
@[simp] theorem preDivisorRiggedNeutralSpectralPoint_re (t : ℝ) :
    (preDivisorRiggedNeutralSpectralPoint t).re = (t + 1) / 2 := by
  simp [preDivisorRiggedNeutralSpectralPoint]

/-- The normalized transverse coordinate recovers the source-centered rate without rescaling. -/
@[simp] theorem preDivisorCenteredRate_neutralSpectralPoint (t : ℝ) :
    preDivisorCenteredRate (preDivisorRiggedNeutralSpectralPoint t) = t := by
  simp [preDivisorCenteredRate]
  ring

/-- Source orientation resolves each absolute rigged weight into its signed Gamma-Bockstein. -/
theorem preDivisorOrientation_mul_riggedPrimeWeight_neutralSpectralPoint
    (t : ℝ) (p : Nat.Primes) :
    preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t) *
        preDivisorRiggedPrimeWeight (preDivisorRiggedNeutralSpectralPoint t) p =
      primeGammaCofinalBocksteinCoefficient t p := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hleft : (preDivisorRiggedNeutralSpectralPoint t).re < 1 / 2 := by
      simp
      linarith
    rw [preDivisorOrientation_eq_one_of_left _ hleft, one_mul,
      preDivisorRiggedPrimeWeight, preDivisorPrimeCarrier,
      preDivisorCenteredRate_neutralSpectralPoint,
      abs_of_pos (primeGammaCofinalBocksteinCoefficient_pos_of_neg ht p)]
  · simp [preDivisorRiggedNeutralSpectralPoint, preDivisorOrientation,
      preDivisorTailLog, preDivisorRiggedPrimeWeight, preDivisorPrimeCarrier,
      preDivisorCenteredRate, primeGammaCofinalBocksteinCoefficient]
  · have hright : 1 / 2 < (preDivisorRiggedNeutralSpectralPoint t).re := by
      simp
      linarith
    rw [preDivisorOrientation_eq_neg_one_of_right _ hright,
      preDivisorRiggedPrimeWeight, preDivisorPrimeCarrier,
      preDivisorCenteredRate_neutralSpectralPoint,
      abs_of_neg (primeGammaCofinalBocksteinCoefficient_neg_of_pos ht p)]
    ring

/-- Finite packet determinant pulled back to the normalized transverse wall coordinate. -/
def preDivisorRiggedPrimeNeutralPacketDeterminant (m : ℕ) (t : ℝ) : ℝ :=
  preDivisorRiggedPrimePacketDeterminant
    (preDivisorRiggedNeutralSpectralPoint t) m

/-- The transverse packet determinant is exactly the product of its signed Bocksteins. -/
theorem preDivisorRiggedPrimeNeutralPacketDeterminant_eq
    (m : ℕ) (t : ℝ) :
    preDivisorRiggedPrimeNeutralPacketDeterminant m t =
      (1 - (m + 2 : ℕ) : ℝ) *
        ∏ i : Fin (m + 2),
          primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i) := by
  rw [preDivisorRiggedPrimeNeutralPacketDeterminant,
    preDivisorRiggedPrimePacketDeterminant_eq]
  calc
    preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t) ^ (m + 2) *
          (1 - (m + 2 : ℕ) : ℝ) *
          ∏ i : Fin (m + 2),
            preDivisorRiggedPrimeWeight
              (preDivisorRiggedNeutralSpectralPoint t) (nthPrimePoint i) =
        (1 - (m + 2 : ℕ) : ℝ) *
          (∏ i : Fin (m + 2),
            preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t)) *
          (∏ i : Fin (m + 2),
              preDivisorRiggedPrimeWeight
                (preDivisorRiggedNeutralSpectralPoint t) (nthPrimePoint i)) := by
                have hconst :
                    (∏ _i : Fin (m + 2),
                      preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t)) =
                      preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t) ^
                        (m + 2) := by simp
                rw [hconst]
                ring
    _ = (1 - (m + 2 : ℕ) : ℝ) *
          ∏ i : Fin (m + 2),
            (preDivisorOrientation (preDivisorRiggedNeutralSpectralPoint t) *
              preDivisorRiggedPrimeWeight
                (preDivisorRiggedNeutralSpectralPoint t) (nthPrimePoint i)) := by
          rw [Finset.prod_mul_distrib]
          ring
    _ = _ := by
      simp_rw [preDivisorOrientation_mul_riggedPrimeWeight_neutralSpectralPoint]

/-- Nonzero first neutral jet of the signed Gamma-Bockstein at one ordinary prime. -/
def preDivisorRiggedPrimeNeutralJet (p : Nat.Primes) : ℝ :=
  -2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)

/-- Every prime-labelled neutral jet is nonzero. -/
theorem preDivisorRiggedPrimeNeutralJet_ne_zero (p : Nat.Primes) :
    preDivisorRiggedPrimeNeutralJet p ≠ 0 := by
  have hdensity : 0 < primeActivationOccupancyFisherDensity p := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hden : (0 : ℝ) < ((p : ℝ) + 1) ^ 2 := by positivity
    rw [primeActivationOccupancyFisherDensity_eq]
    exact div_pos hp0 hden
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [preDivisorRiggedPrimeNeutralJet]
  positivity

/-- The divided Gamma-Bockstein converges to its nonzero prime-log neutral jet. -/
theorem tendsto_primeGammaCofinalBocksteinCoefficient_div_id_neutral
    (p : Nat.Primes) :
    Tendsto (fun t : ℝ => primeGammaCofinalBocksteinCoefficient t p / t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (preDivisorRiggedPrimeNeutralJet p)) := by
  have h := (hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero p).tendsto_slope_zero
  simpa [preDivisorRiggedPrimeNeutralJet,
    primeGammaCofinalBocksteinCoefficient, div_eq_inv_mul, mul_comm] using h

/-- **Exact growing neutral order.** The `m + 2` prime packet divided by `t^(m+2)` converges to
the explicit product of its nonzero prime-log jets. -/
theorem tendsto_preDivisorRiggedPrimeNeutralPacketDeterminant_div_pow
    (m : ℕ) :
    Tendsto
      (fun t : ℝ =>
        preDivisorRiggedPrimeNeutralPacketDeterminant m t / t ^ (m + 2))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds ((1 - (m + 2 : ℕ) : ℝ) *
        ∏ i : Fin (m + 2),
          preDivisorRiggedPrimeNeutralJet (nthPrimePoint i))) := by
  have hprod : Tendsto
      (fun t : ℝ => ∏ i : Fin (m + 2),
        (primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i) / t))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (∏ i : Fin (m + 2),
        preDivisorRiggedPrimeNeutralJet (nthPrimePoint i))) :=
    tendsto_finsetProd _ fun i _ =>
      tendsto_primeGammaCofinalBocksteinCoefficient_div_id_neutral _
  have hscaled := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => (1 - (m + 2 : ℕ) : ℝ))
      (nhdsWithin (0 : ℝ) ({0}ᶜ))
      (nhds (1 - (m + 2 : ℕ) : ℝ))).mul hprod
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  rw [preDivisorRiggedPrimeNeutralPacketDeterminant_eq]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const]
  rw [Finset.card_univ, Fintype.card_fin]
  ring

/-- The leading coefficient in the exact neutral-order law never vanishes. -/
theorem preDivisorRiggedPrimeNeutralPacketLeadingCoefficient_ne_zero
    (m : ℕ) :
    (1 - (m + 2 : ℕ) : ℝ) *
        ∏ i : Fin (m + 2),
          preDivisorRiggedPrimeNeutralJet (nthPrimePoint i) ≠ 0 := by
  apply mul_ne_zero
  · have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
    push_cast
    linarith
  · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      preDivisorRiggedPrimeNeutralJet_ne_zero _

/-- **Fixed-pole regularization obstruction.** If `g` has pole order at most `k` in the weak sense
that `t^k g(t)` has a finite punctured limit, then every packet of size strictly greater than `k`
still vanishes after multiplication by `g`. -/
theorem tendsto_fixedPole_mul_preDivisorRiggedPrimeNeutralPacketDeterminant_zero
    {k m : ℕ} (hkm : k < m + 2) (g : ℝ → ℝ) {c : ℝ}
    (hg : Tendsto (fun t : ℝ => t ^ k * g t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds c)) :
    Tendsto
      (fun t : ℝ => g t * preDivisorRiggedPrimeNeutralPacketDeterminant m t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
  have hnormalized :=
    tendsto_preDivisorRiggedPrimeNeutralPacketDeterminant_div_pow m
  have hid : Tendsto (fun t : ℝ => t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsubne : m + 2 - k ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hkm
  have hvanish : Tendsto (fun t : ℝ => t ^ (m + 2 - k))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa [zero_pow hsubne] using hid.pow (m + 2 - k)
  have hproduct := (hg.mul hnormalized).mul hvanish
  have hproduct' : Tendsto
      (fun t : ℝ =>
        (t ^ k * g t) *
          (preDivisorRiggedPrimeNeutralPacketDeterminant m t / t ^ (m + 2)) *
            t ^ (m + 2 - k))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  have hk_le : k ≤ m + 2 := hkm.le
  have hpow : k + (m + 2 - k) = m + 2 := Nat.add_sub_of_le hk_le
  have hpowe : t ^ k * t ^ (m + 2 - k) = t ^ (m + 2) := by
    rw [← pow_add, hpow]
  field_simp [ht0]
  rw [← hpowe]
  ring

/-- No fixed-order wall renormalizer can give the normalized determinant value `1` on a packet
whose prime cardinality exceeds that pole order. -/
theorem not_tendsto_fixedPole_mul_preDivisorRiggedPrimeNeutralPacketDeterminant_one
    {k m : ℕ} (hkm : k < m + 2) (g : ℝ → ℝ) {c : ℝ}
    (hg : Tendsto (fun t : ℝ => t ^ k * g t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds c)) :
    ¬ Tendsto
      (fun t : ℝ => g t * preDivisorRiggedPrimeNeutralPacketDeterminant m t)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 1) := by
  intro hone
  have hzero :=
    tendsto_fixedPole_mul_preDivisorRiggedPrimeNeutralPacketDeterminant_zero
      hkm g hg
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at h01

/-! ## Horizontal-only scalar landing obstruction -/

/-- A complex-differentiable function which factors through the real coordinate is constant.
Imaginary dyadic periods converge to zero while remaining nonzero, so the corpus small-period
rigidity theorem applies. -/
theorem differentiable_constant_of_eq_realProfile
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (g : ℝ → ℂ)
    (hfg : ∀ z, f z = g z.re) :
    ∀ x y, f x = f y := by
  let p : ℕ → ℂ := fun n =>
    Complex.I * (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)
  have hp0 : Tendsto p atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    have hcast : Tendsto
        (fun n : ℕ => ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)))
        atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hreal
    simpa [p] using (tendsto_const_nhds.mul hcast :
      Tendsto (fun n : ℕ => Complex.I * ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)))
        atTop (nhds (Complex.I * 0)))
  have hpne : ∀ n, p n ≠ 0 := by
    intro n
    apply mul_ne_zero (by simp)
    exact ofReal_ne_zero.mpr (pow_ne_zero n (by norm_num))
  have hperiod : ∀ n, Function.Periodic f (p n) := by
    intro n z
    rw [hfg (z + p n), hfg z]
    congr 1
    rw [Complex.add_re]
    have hpre : (p n).re = 0 := by
      simp only [p, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    rw [hpre, add_zero]
  exact GaloisForLFunctions.differentiable_constant_of_small_periods
    f hf p hp0 hpne hperiod

/-- **Horizontal scalar landing no-go.** No scalar profile depending only on the horizontal real
coordinate can equal normalized centered Xi on the complex plane.  Holomorphy would force such a
profile to be constant, contradicting the strictly negative central Xi curvature.  Consequently
arbitrary scalar normalization of the SC packets cannot repair the missing vertical variable;
the surviving landing must add genuinely complex or operator-valued data. -/
theorem no_realProfile_normalizedXiC :
    ¬ ∃ g : ℝ → ℂ, ∀ z : ℂ, XiC z / XiC 0 = g z.re := by
  rintro ⟨g, hg⟩
  let f : ℂ → ℂ := fun z => XiC z / XiC 0
  have hf : Differentiable ℂ f := XiC_differentiable.div_const _
  have hfactor : ∀ z, f z = g z.re := by
    intro z
    simpa [f] using hg z
  have hconstant := differentiable_constant_of_eq_realProfile f hf g hfactor
  have hXiConst : ∀ z : ℂ, XiC z = XiC 0 := by
    intro z
    have h := hconstant z 0
    dsimp only [f] at h
    field_simp [XiC_zero_ne] at h
    exact h
  have hfun : XiC = fun _ : ℂ => XiC 0 := funext hXiConst
  have hsecond : deriv (deriv XiC) 0 = 0 := by
    rw [hfun]
    simp
  have hneg := XiC_secondDeriv_div_center_re_neg
  rw [hsecond] at hneg
  simp at hneg

end
end RHTower
