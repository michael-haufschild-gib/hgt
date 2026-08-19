import GaloisForLFunctions.RHTower.MobiusPrelimitSafeWidth
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation

/-!
# The Riemann hypothesis supplies the whole half-unit moment tower

Littlewood's half-power Mertens bound, together with the unconditional square integrability of the
critical vector, forces `m₀(t) = O(e^{-(1/2-δ)t})` for every `δ > 0`: Abel summation writes `m₀`
as a boundary term plus a convergent series whose tail is `O(N^{-1/2+δ})`, and the limit constant
must vanish because a nonzero constant is not square integrable on a half line.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The real Möbius coefficient. -/
def mobiusRealCoeff (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- The real reciprocal Möbius term `μ(n)/n`. -/
def mobiusReciprocalTerm (n : ℕ) : ℝ := mobiusRealCoeff n * ((n : ℝ))⁻¹

/-- The partial sums of `μ(n)/n`. -/
def mobiusReciprocalPartial (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, mobiusReciprocalTerm i

theorem mobiusRealWeight_one_eq (n : ℕ) :
    mobiusRealWeight 1 n = ((mobiusReciprocalTerm n : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst hn
    simp [mobiusRealWeight, mobiusReciprocalTerm, mobiusRealCoeff]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [mobiusRealWeight, if_neg hn, mobiusReciprocalTerm, mobiusRealCoeff,
      Real.rpow_neg hnpos.le, Real.rpow_one]
    push_cast
    ring

theorem mobiusWeightedPartial_one_eq (t : ℝ) :
    mobiusWeightedPartial 1 t
      = ((mobiusReciprocalPartial (⌊Real.exp t⌋₊ + 1) : ℝ) : ℂ) := by
  rw [mobiusWeightedPartial, mobiusReciprocalPartial, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => mobiusRealWeight_one_eq n

/-- The Mertens partial sums, in the real Abel form. -/
theorem partialSum_mobiusRealCoeff_eq (N : ℕ) :
    ((HTGeometry.partialSum mobiusRealCoeff (N + 1) : ℝ) : ℂ) = mobiusMertensPartialSum N := by
  rw [HTGeometry.partialSum, mobiusMertensPartialSum, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [mobiusRealCoeff, mobiusComplexCoefficient, Complex.ofReal_intCast]

/-- Littlewood's bound in the real Abel form. -/
theorem abs_partialSum_le_of_mertensBound {δ C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ))
    (N : ℕ) : |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [HTGeometry.partialSum]
    positivity
  · obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
    have h := hM M
    rw [← partialSum_mobiusRealCoeff_eq M, Complex.norm_real, Real.norm_eq_abs] at h
    have hcast : ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
    rwa [hcast] at h

/-- The Abel increment coefficient. -/
def mobiusAbelIncrement (j : ℕ) : ℝ :=
  HTGeometry.partialSum mobiusRealCoeff (j + 1) * ((((j : ℝ) + 1))⁻¹ - ((j : ℝ))⁻¹)

/-- **The exact Abel identity for the reciprocal Möbius partial sums.** -/
theorem mobiusReciprocalPartial_eq (n : ℕ) :
    mobiusReciprocalPartial n
      = HTGeometry.partialSum mobiusRealCoeff n * ((n : ℝ))⁻¹
        - ∑ j ∈ Finset.range n, mobiusAbelIncrement j := by
  have h := HTGeometry.sum_mul_weight_eq mobiusRealCoeff (fun i : ℕ => ((i : ℝ))⁻¹) n
  rw [mobiusReciprocalPartial]
  simp only [mobiusReciprocalTerm, mobiusAbelIncrement]
  convert h using 3
  push_cast
  ring

/-! ## The Abel increments -/

theorem mobiusAbelIncrement_zero : mobiusAbelIncrement 0 = 0 := by
  rw [mobiusAbelIncrement, HTGeometry.partialSum]
  simp [mobiusRealCoeff]

theorem abs_mobiusAbelIncrement_le {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ))
    (j : ℕ) :
    |mobiusAbelIncrement j|
      ≤ (C * 2 ^ ((1 / 2 : ℝ) + δ)) * ((j : ℝ)) ^ (-(3 / 2 : ℝ) + δ) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [mobiusAbelIncrement_zero, abs_zero]
    positivity
  · have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hstep : (((j : ℝ) + 1))⁻¹ - ((j : ℝ))⁻¹ = -(1 / ((j : ℝ) * ((j : ℝ) + 1))) := by
      field_simp
      ring
    have habs : |(((j : ℝ) + 1))⁻¹ - ((j : ℝ))⁻¹| = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
      rw [hstep, abs_neg, abs_of_nonneg (by positivity)]
    have hSj := hS (j + 1)
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hSj
    have hle2 : ((j : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)
        ≤ (2 : ℝ) ^ ((1 / 2 : ℝ) + δ) * (j : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
      have h2j : ((j : ℝ) + 1) ≤ 2 * (j : ℝ) := by linarith
      calc ((j : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) ≤ (2 * (j : ℝ)) ^ ((1 / 2 : ℝ) + δ) :=
            Real.rpow_le_rpow (by positivity) h2j (by linarith)
        _ = (2 : ℝ) ^ ((1 / 2 : ℝ) + δ) * (j : ℝ) ^ ((1 / 2 : ℝ) + δ) :=
            Real.mul_rpow (by norm_num) hjpos.le
    have hinv : 1 / ((j : ℝ) * ((j : ℝ) + 1)) ≤ (j : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hjpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
    have hsplit : (j : ℝ) ^ ((1 / 2 : ℝ) + δ) * (j : ℝ) ^ (-(2 : ℝ))
        = (j : ℝ) ^ (-(3 / 2 : ℝ) + δ) := by
      rw [← Real.rpow_add hjpos]
      congr 1
      ring
    rw [mobiusAbelIncrement, abs_mul, habs]
    calc |HTGeometry.partialSum mobiusRealCoeff (j + 1)| * (1 / ((j : ℝ) * ((j : ℝ) + 1)))
        ≤ (C * ((j : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)) * ((j : ℝ) ^ (-(2 : ℝ))) := by
          exact mul_le_mul hSj hinv (by positivity) (by positivity)
      _ ≤ (C * ((2 : ℝ) ^ ((1 / 2 : ℝ) + δ) * (j : ℝ) ^ ((1 / 2 : ℝ) + δ)))
            * ((j : ℝ) ^ (-(2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hle2 hC
      _ = (C * 2 ^ ((1 / 2 : ℝ) + δ)) * ((j : ℝ) ^ ((1 / 2 : ℝ) + δ) * (j : ℝ) ^ (-(2 : ℝ))) := by
          ring
      _ = (C * 2 ^ ((1 / 2 : ℝ) + δ)) * (j : ℝ) ^ (-(3 / 2 : ℝ) + δ) := by rw [hsplit]

theorem summable_mobiusAbelIncrement {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ)) :
    Summable mobiusAbelIncrement := by
  refine Summable.of_abs ?_
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _)
    (abs_mobiusAbelIncrement_le hC hδ hS) ?_
  exact (Real.summable_nat_rpow.mpr (by linarith : -(3 / 2 : ℝ) + δ < -1)).mul_left _

/-! ## The Abel tail and the limit constant -/

theorem summable_shift_mobiusAbelIncrement {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ))
    (n : ℕ) : Summable (fun j : ℕ => mobiusAbelIncrement (j + n)) :=
  (summable_mobiusAbelIncrement hC hδ hδ2 hS).comp_injective (add_left_injective n)

theorem abs_tsum_shift_le {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ))
    {n : ℕ} (hn : 1 ≤ n) :
    |∑' j : ℕ, mobiusAbelIncrement (j + n)|
      ≤ ((C * 2 ^ ((1 / 2 : ℝ) + δ)) * (∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)))
        * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := by
  have hδ2 : δ < 1 / 2 := by linarith
  set K : ℝ := C * 2 ^ ((1 / 2 : ℝ) + δ) with hKdef
  have hK : 0 ≤ K := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbase : Summable (fun m : ℕ => ((m : ℝ)) ^ (-(1 : ℝ) - δ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm : ∀ j : ℕ, |mobiusAbelIncrement (j + n)|
      ≤ (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) * (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ) := by
    intro j
    have hjn : (1 : ℝ) ≤ ((j + n : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ j + n := by omega
      exact_mod_cast this
    have hjnpos : (0 : ℝ) < ((j + n : ℕ) : ℝ) := by linarith
    have hstep : ((j + n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ) + δ)
        = ((j + n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
          * ((j + n : ℕ) : ℝ) ^ (-(1 : ℝ) - δ) := by
      rw [← Real.rpow_add hjnpos]
      congr 1
      ring
    have hmono : ((j + n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
        ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := by
      refine Real.rpow_le_rpow_of_nonpos hnpos ?_ (by linarith)
      have : (n : ℕ) ≤ j + n := by omega
      exact_mod_cast this
    calc |mobiusAbelIncrement (j + n)|
        ≤ K * ((j + n : ℕ) : ℝ) ^ (-(3 / 2 : ℝ) + δ) :=
          abs_mobiusAbelIncrement_le hC hδ hS (j + n)
      _ = K * (((j + n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
            * ((j + n : ℕ) : ℝ) ^ (-(1 : ℝ) - δ)) := by rw [hstep]
      _ ≤ K * ((n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) * ((j + n : ℕ) : ℝ) ^ (-(1 : ℝ) - δ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hjnpos.le _)
      _ = (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) * ((j + n : ℕ) : ℝ) ^ (-(1 : ℝ) - δ) := by ring
  have hsum1 : Summable (fun j : ℕ => |mobiusAbelIncrement (j + n)|) :=
    (summable_shift_mobiusAbelIncrement hC hδ hδ2 hS n).abs
  have hsum2 : Summable (fun j : ℕ =>
      (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) * (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ)) :=
    ((hbase.comp_injective (add_left_injective n))).mul_left _
  have hcmp : ∑' j : ℕ, |mobiusAbelIncrement (j + n)|
      ≤ ∑' j : ℕ, (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) * (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ) :=
    hsum1.tsum_le_tsum hterm hsum2
  have hshift : ∑' j : ℕ, (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ)
      ≤ ∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ) := by
    refine (hbase.comp_injective (add_left_injective n)).tsum_le_tsum_of_inj
      (fun j : ℕ => j + n) (add_left_injective n) (fun c _ => Real.rpow_nonneg
        (Nat.cast_nonneg c) _) (fun c => le_rfl) hbase
  calc |∑' j : ℕ, mobiusAbelIncrement (j + n)|
      ≤ ∑' j : ℕ, |mobiusAbelIncrement (j + n)| := by
        have hnorm : Summable (fun j : ℕ => ‖mobiusAbelIncrement (j + n)‖) := by
          simpa [Real.norm_eq_abs] using hsum1
        have h := norm_tsum_le_tsum_norm (f := fun j : ℕ => mobiusAbelIncrement (j + n)) hnorm
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' j : ℕ, (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ))
          * (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ) := hcmp
    _ = (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ))
          * ∑' j : ℕ, (((j + n : ℕ) : ℝ)) ^ (-(1 : ℝ) - δ) := tsum_mul_left
    _ ≤ (K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) * ∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ) := by
        refine mul_le_mul_of_nonneg_left hshift ?_
        positivity
    _ = (K * ∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)) * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := by ring

/-! ## The limit constant vanishes -/

/-- The Abel limit constant of the reciprocal Möbius partial sums. -/
def mobiusAbelLimit : ℝ := -(∑' j : ℕ, mobiusAbelIncrement j)

theorem mobiusReciprocalPartial_sub_limit {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ))
    (n : ℕ) :
    mobiusReciprocalPartial n - mobiusAbelLimit
      = HTGeometry.partialSum mobiusRealCoeff n * ((n : ℝ))⁻¹
        + ∑' j : ℕ, mobiusAbelIncrement (j + n) := by
  have hsum := summable_mobiusAbelIncrement hC hδ hδ2 hS
  have hsplit := hsum.sum_add_tsum_nat_add n
  rw [mobiusReciprocalPartial_eq n, mobiusAbelLimit]
  linarith [hsplit]

theorem abs_mobiusReciprocalPartial_sub_limit_le {δ C : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4)
    (hS : ∀ N : ℕ, |HTGeometry.partialSum mobiusRealCoeff N| ≤ C * (N : ℝ) ^ ((1 / 2 : ℝ) + δ))
    {n : ℕ} (hn : 1 ≤ n) :
    |mobiusReciprocalPartial n - mobiusAbelLimit|
      ≤ (C + (C * 2 ^ ((1 / 2 : ℝ) + δ)) * (∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)))
        * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := by
  have hδ2 : δ < 1 / 2 := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbound1 : |HTGeometry.partialSum mobiusRealCoeff n * ((n : ℝ))⁻¹|
      ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := by
    have hsplit : (n : ℝ) ^ ((1 / 2 : ℝ) + δ) * ((n : ℝ))⁻¹ = (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by
      rw [show ((n : ℝ))⁻¹ = (n : ℝ) ^ (-(1 : ℝ)) by
        rw [Real.rpow_neg hnpos.le, Real.rpow_one], ← Real.rpow_add hnpos]
      congr 1
      ring
    have hmono : (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ))⁻¹)]
    calc |HTGeometry.partialSum mobiusRealCoeff n| * ((n : ℝ))⁻¹
        ≤ (C * (n : ℝ) ^ ((1 / 2 : ℝ) + δ)) * ((n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right (hS n) (by positivity)
      _ = C * ((n : ℝ) ^ ((1 / 2 : ℝ) + δ) * ((n : ℝ))⁻¹) := by ring
      _ = C * (n : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by rw [hsplit]
      _ ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := mul_le_mul_of_nonneg_left hmono hC
  have hbound2 := abs_tsum_shift_le hC hδ hδ4 hS hn
  rw [mobiusReciprocalPartial_sub_limit hC hδ hδ2 hS n]
  calc |HTGeometry.partialSum mobiusRealCoeff n * ((n : ℝ))⁻¹
        + ∑' j : ℕ, mobiusAbelIncrement (j + n)|
      ≤ |HTGeometry.partialSum mobiusRealCoeff n * ((n : ℝ))⁻¹|
        + |∑' j : ℕ, mobiusAbelIncrement (j + n)| := abs_add_le _ _
    _ ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
        + ((C * 2 ^ ((1 / 2 : ℝ) + δ)) * (∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)))
          * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := add_le_add hbound1 hbound2
    _ = _ := by ring

theorem criticalMertensVector_eq_partial {t : ℝ} (ht : 0 < t) :
    criticalMertensVector t = ((mobiusReciprocalPartial (⌊Real.exp t⌋₊ + 1) : ℝ) : ℂ) := by
  rw [criticalMertensVector, Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
    mobiusWeightedPartial_one_eq]

theorem mobiusAbelLimit_eq_zero_of_bound {δ K : ℝ} (hδ : 0 < δ) (hδ4 : δ < 1 / 4) (hK : 0 ≤ K)
    (hb : ∀ n : ℕ, 1 ≤ n → |mobiusReciprocalPartial n - mobiusAbelLimit|
      ≤ K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)) : mobiusAbelLimit = 0 := by
  by_contra hL
  set L : ℝ := mobiusAbelLimit with hLdef
  set ε : ℝ := |L| / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have : 0 < |L| := abs_pos.mpr hL
    linarith
  have hexpneg : (-(1 / 2 : ℝ) + 2 * δ) < 0 := by linarith
  have htend : Tendsto (fun t : ℝ => K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t)) atTop (nhds 0) := by
    have hpos : (0 : ℝ) < -(-(1 / 2 : ℝ) + 2 * δ) := by linarith
    have h1 : Tendsto (fun t : ℝ => (-(-(1 / 2 : ℝ) + 2 * δ)) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hpos Filter.tendsto_id
    have h2 : Tendsto (fun t : ℝ => (-(1 / 2 : ℝ) + 2 * δ) * t) atTop atBot := by
      have h3 := Filter.tendsto_neg_atTop_atBot.comp h1
      refine h3.congr fun t => ?_
      simp only [Function.comp_apply]
      ring
    have h4 := (Real.tendsto_exp_atBot.comp h2).const_mul K
    rw [mul_zero] at h4
    exact h4
  have hev : ∀ᶠ t in atTop, K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) < ε :=
    htend.eventually (Iio_mem_nhds hε)
  have hfinal : ∀ᶠ t in atTop, ε ≤ ‖criticalMertensVector t‖ := by
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with t h1 h2
    set n : ℕ := ⌊Real.exp t⌋₊ + 1 with hndef
    have hn1 : 1 ≤ n := by omega
    have hexpn : Real.exp t ≤ (n : ℝ) := by
      rw [hndef]
      push_cast
      exact (Nat.lt_floor_add_one (Real.exp t)).le
    have hmono : (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
        ≤ Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) := by
      have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos t) hexpn hexpneg.le
      rw [← Real.exp_mul] at h
      rwa [mul_comm t] at h
    have hb' := hb n hn1
    have hchain : |mobiusReciprocalPartial n - L| < ε := by
      calc |mobiusReciprocalPartial n - L| ≤ K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := hb'
        _ ≤ K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) := mul_le_mul_of_nonneg_left hmono hK
        _ < ε := h1
    rw [criticalMertensVector_eq_partial h2, Complex.norm_real, Real.norm_eq_abs]
    have hrev := abs_sub_abs_le_abs_sub L (mobiusReciprocalPartial n)
    rw [abs_sub_comm L (mobiusReciprocalPartial n)] at hrev
    rw [hεdef] at hchain ⊢
    linarith [hchain, hrev]
  obtain ⟨T, hT⟩ := eventually_atTop.mp hfinal
  have hsq : Integrable (fun t : ℝ => ‖criticalMertensVector t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm memLp_criticalMertensVector.1).mp memLp_criticalMertensVector
  have hIoi : IntegrableOn (fun t : ℝ => ‖criticalMertensVector t‖ ^ 2) (Ioi T) volume :=
    hsq.integrableOn
  have hlow : ENNReal.ofReal (ε ^ 2) * volume (Ioi T)
      ≤ ∫⁻ t in Ioi T, ‖‖criticalMertensVector t‖ ^ 2‖ₑ := by
    rw [← MeasureTheory.setLIntegral_const]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have h1 := hT t (le_of_lt (mem_Ioi.mp ht))
    rw [Real.enorm_eq_ofReal (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hε.le, norm_nonneg (criticalMertensVector t)]
  have hne : ENNReal.ofReal (ε ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [Real.volume_Ioi, ENNReal.mul_top hne] at hlow
  have hfin : ∫⁻ t in Ioi T, ‖‖criticalMertensVector t‖ ^ 2‖ₑ < ⊤ := hIoi.hasFiniteIntegral
  exact absurd hfin (not_lt.mpr hlow)

/-! ## The half-unit tower under the Riemann hypothesis -/

theorem exists_decay_of_riemannHypothesis (hRH : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ < 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      ‖criticalMertensVector t‖ ≤ K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) := by
  obtain ⟨C, hC, hM⟩ := riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound hRH δ hδ
  have hS := abs_partialSum_le_of_mertensBound hC hM
  have htsum : (0 : ℝ) ≤ ∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ) :=
    tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  set K : ℝ := C + (C * 2 ^ ((1 / 2 : ℝ) + δ)) * (∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)) with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    have h2 : (0 : ℝ) < 2 ^ ((1 / 2 : ℝ) + δ) := Real.rpow_pos_of_pos (by norm_num) _
    have hprod : 0 ≤ C * 2 ^ ((1 / 2 : ℝ) + δ) * (∑' m : ℕ, ((m : ℝ)) ^ (-(1 : ℝ) - δ)) :=
      mul_nonneg (mul_nonneg hC h2.le) htsum
    linarith
  have hzero := mobiusAbelLimit_eq_zero_of_bound hδ hδ4 hK
    (fun n hn => abs_mobiusReciprocalPartial_sub_limit_le hC hδ hδ4.le hS hn)
  refine ⟨K, hK, fun t ht => ?_⟩
  set n : ℕ := ⌊Real.exp t⌋₊ + 1 with hndef
  have hn1 : 1 ≤ n := by omega
  have hb := abs_mobiusReciprocalPartial_sub_limit_le hC hδ hδ4.le hS hn1
  rw [hzero, sub_zero, ← hKdef] at hb
  have hexpneg : (-(1 / 2 : ℝ) + 2 * δ) < 0 := by linarith
  have hexpn : Real.exp t ≤ (n : ℝ) := by
    rw [hndef]
    push_cast
    exact (Nat.lt_floor_add_one (Real.exp t)).le
  have hmono : (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ)
      ≤ Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) := by
    have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos t) hexpn hexpneg.le
    rw [← Real.exp_mul] at h
    rwa [mul_comm t] at h
  rw [criticalMertensVector_eq_partial ht, Complex.norm_real, Real.norm_eq_abs]
  calc |mobiusReciprocalPartial n| ≤ K * (n : ℝ) ^ (-(1 / 2 : ℝ) + 2 * δ) := hb
    _ ≤ K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t) := mul_le_mul_of_nonneg_left hmono hK

/-- **Section 3, `(i) → (ii)`.**  The Riemann hypothesis supplies every weighted domain below the
half-unit seam. -/
theorem weightedMertensMoment_of_riemannHypothesis (hRH : RiemannHypothesis) {α : ℝ}
    (_hα0 : 0 ≤ α) (hα : α < 1 / 2) : WeightedMertensMoment α := by
  set δ : ℝ := min ((1 / 2 - α) / 8) (1 / 8) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set γ : ℝ := α + (-(1 / 2 : ℝ) + 2 * δ) with hγdef
  have hγ : γ < 0 := by
    have hle : δ ≤ (1 / 2 - α) / 8 := min_le_left _ _
    rw [hγdef]
    linarith
  obtain ⟨K, hK, hbd⟩ := exists_decay_of_riemannHypothesis hRH hδ hδ4
  set g : ℝ → ℝ := fun t => Set.indicator (Set.Ioi (0 : ℝ)) (fun s => K * Real.exp (γ * s)) t
    with hgdef
  have hgmeas : AEStronglyMeasurable g volume := by
    refine (Measurable.indicator ?_ measurableSet_Ioi).aestronglyMeasurable
    exact measurable_const.mul (Real.measurable_exp.comp (by fun_prop))
  have hgL : MemLp g 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hgmeas).mpr ?_
    have hint : IntegrableOn (fun t : ℝ => K ^ 2 * Real.exp (-(-(2 * γ)) * t))
        (Ioi (0 : ℝ)) volume :=
      (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
    refine (IntegrableOn.integrable_of_ae_notMem_eq_zero (s := Ioi (0 : ℝ)) ?_ ?_)
    · refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
      simp only [hgdef]
      rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    · refine Filter.Eventually.of_forall fun t ht => ?_
      simp only [hgdef]
      rw [Set.indicator_of_notMem ht, norm_zero]
      norm_num
  have hfmeas : AEStronglyMeasurable
      (weightedMertensVector α) volume := by
    refine ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (by fun_prop))).measurable.mul measurable_criticalMertensVector).aestronglyMeasurable
  refine (hgL.of_le hfmeas (Filter.Eventually.of_forall fun t => ?_)).restrict _
  rcases le_or_gt t 0 with ht | ht
  · have h0 : criticalMertensVector t = 0 := by
      rw [criticalMertensVector, Set.indicator_of_notMem (by simpa using ht)]
    rw [weightedMertensVector, h0, mul_zero, norm_zero]
    positivity
  · have hb := hbd t ht
    simp only [hgdef]
    rw [weightedMertensVector, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hprod : Real.exp (α * t) * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t)
        = Real.exp (γ * t) := by
      rw [← Real.exp_add, hγdef]
      congr 1
      ring
    calc Real.exp (α * t) * ‖criticalMertensVector t‖
        ≤ Real.exp (α * t) * (K * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = K * (Real.exp (α * t) * Real.exp ((-(1 / 2 : ℝ) + 2 * δ) * t)) := by ring
      _ = K * Real.exp (γ * t) := by rw [hprod]

/-- **Card equation `(8)`: the exact RH criterion.**  The Riemann hypothesis is equivalent to the
full half-unit exponential-moment tower. -/
theorem riemannHypothesis_iff_forall_weightedMertensMoment :
    RiemannHypothesis ↔ ∀ α : ℝ, 0 ≤ α → α < 1 / 2 → WeightedMertensMoment α :=
  ⟨fun hRH _α hα0 hα => weightedMertensMoment_of_riemannHypothesis hRH hα0 hα,
    riemannHypothesis_of_forall_weightedMertensMoment⟩

end

end RHTower
