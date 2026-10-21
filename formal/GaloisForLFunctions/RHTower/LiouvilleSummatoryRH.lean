import GaloisForLFunctions.RHTower.LiouvilleExponentialSumPowerLaw
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.JordanFloorSymbolLaw

/-!
# The Liouville summatory function under RH

`λ = μ * 1_□` (`liouvilleC_eq_moebius_mul`): the Liouville function is the Möbius convolution of
the indicator of the squares, because `1 * λ = 1_□`.  Hence
`L(N) = Σ_{n ≤ N} λ(n) = Σ_{d ≤ N, d = □} M(⌊N/d⌋)` (`sourcePartialSum_liouvilleR_eq`), and a
Mertens bound `M(x) = O(x^{½+δ})` gives `L(N) = O(N^{½+δ})` with the constant multiplied by
`Σ_j j^{-1-2δ}` (`exists_abs_sourcePartialSum_liouvilleR_le_of_riemannHypothesis`).
-/

open Complex Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RHTower

noncomputable section

/-- The square indicator as an arithmetic function. -/
def squareIndicatorAF : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else squareIndicator n, by simp⟩

theorem coe_zeta_mul_liouvilleC :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * liouvilleC = squareIndicatorAF := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [squareIndicatorAF]
  · rw [ArithmeticFunction.coe_zeta_mul_apply, sum_divisors_liouvilleC hn]
    simp [squareIndicatorAF, hn]

/-- **`λ = μ * 1_□`.** -/
theorem liouvilleC_eq_moebius_mul :
    liouvilleC = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) * squareIndicatorAF := by
  rw [← coe_zeta_mul_liouvilleC, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    one_mul]

/-- The real square indicator. -/
def squareIndicatorR (n : ℕ) : ℝ := if IsSquare n then 1 else 0

/-- The real Möbius function. -/
def moebiusR (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- The real Liouville function. -/
def liouvilleR (n : ℕ) : ℝ := ((ArithmeticFunction.liouville n : ℤ) : ℝ)

theorem liouvilleR_eq_dirichletConv (n : ℕ) :
    liouvilleR n = dirichletConv squareIndicatorR moebiusR n := by
  apply Complex.ofReal_injective
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n) liouvilleC_eq_moebius_mul
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (f := fun a b => ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) a) *
      squareIndicatorAF b)] at h
  rw [liouvilleR, dirichletConv, Complex.ofReal_sum]
  rw [liouvilleC_apply] at h
  push_cast
  rw [h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp only [squareIndicatorAF, ArithmeticFunction.coe_mk, if_neg hd0, squareIndicator,
    squareIndicatorR, moebiusR, ArithmeticFunction.intCoe_apply]
  split_ifs <;> push_cast <;> ring

theorem sourcePartialSum_liouvilleR_eq (N : ℕ) :
    sourcePartialSum liouvilleR N =
      floorTransform squareIndicatorR (sourcePartialSum moebiusR) N := by
  rw [floorTransform_sourcePartialSum, sourcePartialSum, sourcePartialSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact liouvilleR_eq_dirichletConv n

theorem norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR (k : ℕ) :
    ‖mobiusMertensPartialSum k‖ = |sourcePartialSum moebiusR k| := by
  rw [mobiusMertensPartialSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [mobiusComplexCoefficient, ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
  rw [show Finset.Ico 1 (k + 1) = Finset.Icc 1 k by ext; simp, sourcePartialSum]
  have e : ∑ x ∈ Finset.Icc 1 k, ((ArithmeticFunction.moebius x : ℤ) : ℂ) =
      ((∑ m ∈ Finset.Icc 1 k, moebiusR m : ℝ) : ℂ) := by push_cast [moebiusR]; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs]

/-- **The Liouville summatory function under RH.**  For every `δ > 0`,
`|L(N)| ≤ C (N + 1)^{½+δ}`. -/
theorem exists_abs_sourcePartialSum_liouvilleR_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |sourcePartialSum liouvilleR N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ) := by
  obtain ⟨CM, hCM0, hCM⟩ := mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis.2 hRH δ hδ
  set p : ℝ := 1 / 2 + δ with hp
  have hp0 : 0 < p := by positivity
  have hZs : Summable fun j : ℕ => 1 / (j : ℝ) ^ (2 * p) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  set Z := ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * p) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun j => by positivity
  refine ⟨CM * 2 ^ p * Z, by positivity, fun N => ?_⟩
  rw [sourcePartialSum_liouvilleR_eq, floorTransform]
  have hpt : ∀ d ∈ Finset.Icc 1 N, |squareIndicatorR d * sourcePartialSum moebiusR (N / d)| ≤
      squareIndicatorR d * (CM * (2 * ((N : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p)) := by
    intro d hd
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hsq : 0 ≤ squareIndicatorR d := by unfold squareIndicatorR; split_ifs <;> norm_num
    have hsq1 : squareIndicatorR d ≤ 1 := by unfold squareIndicatorR; split_ifs <;> norm_num
    rw [abs_mul, abs_of_nonneg hsq]
    refine mul_le_mul_of_nonneg_left ?_ hsq
    rw [← norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR]
    refine le_trans (hCM (N / d)) ?_
    have hfl : ((N / d : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) / d := by
      have h1 : ((N / d : ℕ) : ℝ) ≤ N / d := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ ((N : ℝ) + 1) / d := by
        rw [le_div_iff₀ hd0]; have : (d : ℝ) ≤ N := by exact_mod_cast hdN
        linarith
      have h3 : (N : ℝ) / d ≤ ((N : ℝ) + 1) / d := div_le_div_of_nonneg_right (by linarith) hd0.le
      rw [mul_div_assoc]; linarith
    calc CM * (((N / d : ℕ) : ℝ) + 1) ^ p ≤ CM * (2 * ((N : ℝ) + 1) / d) ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfl hp0.le) hCM0
      _ = CM * (2 * ((N : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p) := by
          rw [Real.div_rpow (by positivity) hd0.le]; ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hpt) ?_)
  have hsum : ∑ i ∈ Finset.Icc 1 N, squareIndicatorR i * (1 / (i : ℝ) ^ p) ≤ Z := by
    have e1 : ∑ i ∈ Finset.Icc 1 N, squareIndicatorR i * (1 / (i : ℝ) ^ p) =
        ∑ i ∈ (Finset.Icc 1 N).filter IsSquare, 1 / (i : ℝ) ^ p := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold squareIndicatorR; split_ifs <;> simp
    rw [e1]
    have hsub : (Finset.Icc 1 N).filter IsSquare ⊆ (Finset.Icc 1 N).image (fun j => j ^ 2) := by
      intro i hi
      obtain ⟨hi1, ⟨j, rfl⟩⟩ := Finset.mem_filter.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi1
      refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨?_, ?_⟩, by ring⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at h1
        · exact hj
      · nlinarith
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) ?_
    rw [Finset.sum_image fun a _ b _ h => by
      exact Nat.pow_left_injective (by norm_num) h]
    have e2 : ∀ j ∈ Finset.Icc 1 N, 1 / (((j ^ 2 : ℕ) : ℝ)) ^ p = 1 / (j : ℝ) ^ (2 * p) := by
      intro j _
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg j)]
      norm_num
    rw [Finset.sum_congr rfl e2]
    exact hZs.sum_le_tsum _ fun j _ => by positivity
  have e3 : ∑ i ∈ Finset.Icc 1 N, squareIndicatorR i * (CM * (2 * ((N : ℝ) + 1)) ^ p *
      (1 / (i : ℝ) ^ p)) = CM * (2 * ((N : ℝ) + 1)) ^ p *
        ∑ i ∈ Finset.Icc 1 N, squareIndicatorR i * (1 / (i : ℝ) ^ p) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3, Real.mul_rpow (by norm_num) (by positivity)]
  have hK : 0 ≤ CM * (2 ^ p * ((N : ℝ) + 1) ^ p) := by positivity
  calc CM * (2 ^ p * ((N : ℝ) + 1) ^ p) *
        ∑ i ∈ Finset.Icc 1 N, squareIndicatorR i * (1 / (i : ℝ) ^ p)
      ≤ CM * (2 ^ p * ((N : ℝ) + 1) ^ p) * Z := mul_le_mul_of_nonneg_left hsum hK
    _ = CM * 2 ^ p * Z * ((N : ℝ) + 1) ^ p := by ring

end

end RHTower
