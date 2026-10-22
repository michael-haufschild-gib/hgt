import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaExactKernel
import GaloisForLFunctions.HTGeometry.MixedEvenTrigMoments

/-!
# Boundary cancellation for the two-leg Suzuki Gamma source

Multiplication of each prime column by its prime destroys the amplitude's square
summability. Adjacent Gamma-coordinate differences nevertheless remain square
summable. Their common homogeneous solution is the Jacobi normalization sequence,
which is not square summable. These two facts permit a closed synthesis graph
without changing any deattenuated source column.
-/

open Filter Topology
open scoped BigOperators ENNReal
set_option autoImplicit false

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Jacobi normalization in the surviving degree enumeration. -/
def suzukiGammaBoundaryCoefficient (k : ℕ) : ℝ :=
  semilocalArchimedeanJacobiNormalization (suzukiCausalDepthGammaSurvivingDegree k)

theorem suzukiGammaBoundaryCoefficient_pos (k : ℕ) :
    0 < suzukiGammaBoundaryCoefficient k :=
  semilocalArchimedeanJacobiNormalization_pos _

theorem suzukiGammaBoundaryCoefficient_le_one (k : ℕ) :
    suzukiGammaBoundaryCoefficient k ≤ 1 := by
  have h := normalizedCentralBinom_le_one
    (suzukiCausalDepthGammaSurvivingDegree k)
  rw [← semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom] at h
  have hp := suzukiGammaBoundaryCoefficient_pos k
  change suzukiGammaBoundaryCoefficient k ^ 2 ≤ 1 at h
  nlinarith

private theorem reciprocal_le_normalizedCentralBinom (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ normalizedCentralBinom n := by
  induction n with
  | zero => simp [normalizedCentralBinom]
  | succ n ih =>
    rw [normalizedCentralBinom_succ]
    push_cast
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
    calc
      1 / ((n : ℝ) + 1 + 1) ≤
          (1 / ((n : ℝ) + 1)) * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
        apply (div_le_div_iff₀ (by positivity) hd).2
        rw [show 1 / ((n : ℝ) + 1) * (2 * n + 1) * (n + 1 + 1) =
          ((2 * n + 1) * (n + 2)) / (n + 1) by ring]
        apply (le_div_iff₀ hn).2
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right ih (by positivity)) hd.le

/-- The sole homogeneous boundary mode is excluded by the Hilbert norm. -/
theorem not_summable_sq_suzukiGammaBoundaryCoefficient :
    ¬ Summable (fun k : ℕ => suzukiGammaBoundaryCoefficient k ^ 2) := by
  intro h
  have htail := (summable_nat_add_iff 1).2 h
  have hlower (k : ℕ) :
      1 / ((k : ℝ) + 4) ≤ suzukiGammaBoundaryCoefficient (k + 1) ^ 2 := by
    simpa [suzukiGammaBoundaryCoefficient, suzukiCausalDepthGammaSurvivingDegree,
      semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom,
      Nat.cast_add, Nat.cast_ofNat, add_assoc, show (3 : ℝ) + 1 = 4 by norm_num] using
      reciprocal_le_normalizedCentralBinom (k + 3)
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 4)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hlower htail
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff 4).1 (by simpa using hs))

/-- Exact Cayley boundary defect at every prime and every valuation depth. -/
theorem suzukiCausalDepthGamma_prime_mul_boundaryDefect_le_two
    (pe : Nat.Primes × ℕ) :
    (pe.1 : ℝ) * (1 - Real.tanh (suzukiCausalDepthGammaFrequency pe)) ≤ 2 := by
  let n : ℝ := xiGammaEulerValuationNat pe
  have hp : (1 : ℝ) ≤ pe.1 := by exact_mod_cast pe.1.property.one_lt.le
  have hn : 0 < n := by
    dsimp [n, xiGammaEulerValuationNat]
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hpn : (pe.1 : ℝ) ≤ n := by
    dsimp [n, xiGammaEulerValuationNat]
    push_cast
    exact le_self_pow₀ hp (by omega)
  have hexp : Real.exp (2 * suzukiCausalDepthGammaFrequency pe) = n := by
    rw [suzukiCausalDepthGammaFrequency, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.exp_log hn
  have htanh (t : ℝ) :
      1 - Real.tanh t = 2 / (Real.exp (2 * t) + 1) := by
    rw [Real.tanh_eq, Real.exp_neg]
    have he : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    have he2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by
      rw [two_mul, Real.exp_add]
    rw [he2]
    field_simp
    ring
  rw [htanh, hexp]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < n + 1)).2
  nlinarith

/-- The actual two-leg column, with no change to its Gamma coordinates. -/
def suzukiGammaTwoLegColumn
    (h a : Set.Ioi (0 : ℝ)) (pe : Nat.Primes × ℕ) :
    SuzukiCausalDepthGammaTraceL2 :=
  (pe.1 : ℂ) • suzukiCausalDepthGammaFeatureOperator h.1 a.1 h.2 a.2
    (lp.single 2 (Sum.inl pe) (1 : ℂ))

theorem suzukiGammaTwoLegColumn_inr
    (h a : Set.Ioi (0 : ℝ)) (pe : Nat.Primes × ℕ) (k : ℕ) :
    suzukiGammaTwoLegColumn h a pe (Sum.inr k) =
      ((pe.1 : ℝ) * suzukiCausalDepthGammaWeightedFeature h.1 a.1 pe k : ℝ) := by
  simp [suzukiGammaTwoLegColumn, suzukiCausalDepthGammaFeatureOperator_apply_inr,
    lp.single_apply, Pi.single_apply, Complex.ofReal_mul]

theorem suzukiGammaTwoLegColumn_inl
    (h a : Set.Ioi (0 : ℝ)) (pe qe : Nat.Primes × ℕ) :
    suzukiGammaTwoLegColumn h a pe (Sum.inl qe) = 0 := by
  simp [suzukiGammaTwoLegColumn, suzukiCausalDepthGammaFeatureOperator_apply_inl]

/-- The continuous row equations will use these exact adjacent differences. -/
def suzukiGammaBoundaryRow (h a : ℝ) (k : ℕ) (pe : Nat.Primes × ℕ) : ℝ :=
  suzukiGammaBoundaryCoefficient (k + 1) *
      ((pe.1 : ℝ) * suzukiCausalDepthGammaWeightedFeature h a pe k) -
    suzukiGammaBoundaryCoefficient k *
      ((pe.1 : ℝ) * suzukiCausalDepthGammaWeightedFeature h a pe (k + 1))

theorem abs_suzukiGammaBoundaryRow_le
    (h a : Set.Ioi (0 : ℝ)) (k : ℕ) (pe : Nat.Primes × ℕ) :
    |suzukiGammaBoundaryRow h.1 a.1 k pe| ≤
      4 * suzukiCausalDepthGammaWeight h.1 a.1 pe := by
  let r := Real.tanh (suzukiCausalDepthGammaFrequency pe)
  let phi := semilocalArchimedeanCharacteristic (suzukiCausalDepthGammaFrequency pe)
  let w := suzukiCausalDepthGammaWeight h.1 a.1 pe
  have hr0 : 0 ≤ r := (tanh_pos_of_pos (suzukiCausalDepthGammaFrequency_pos pe)).le
  have hr1 : r < 1 := Real.tanh_lt_one _
  have hrdef : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hw : 0 ≤ w := (suzukiCausalDepthGammaWeight_pos h.2 a.2 pe).le
  have hphi0 : 0 ≤ phi := (semilocalArchimedeanCharacteristic_pos _).le
  have hphi1 : phi ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh _) (by norm_num)
  have hboundary := suzukiCausalDepthGamma_prime_mul_boundaryDefect_le_two pe
  have hcn := suzukiGammaBoundaryCoefficient_pos k
  have hcn' := suzukiGammaBoundaryCoefficient_pos (k + 1)
  have hc1 := suzukiGammaBoundaryCoefficient_le_one k
  have hc1' := suzukiGammaBoundaryCoefficient_le_one (k + 1)
  have hpow : 0 ≤ r ^ suzukiCausalDepthGammaSurvivingDegree k :=
    pow_nonneg hr0 _
  have hpow1 : r ^ suzukiCausalDepthGammaSurvivingDegree k ≤ 1 :=
    pow_le_one₀ hr0 hr1.le
  have hfactor : suzukiGammaBoundaryRow h.1 a.1 k pe =
      w * phi * suzukiGammaBoundaryCoefficient k *
        suzukiGammaBoundaryCoefficient (k + 1) *
        r ^ suzukiCausalDepthGammaSurvivingDegree k *
        ((pe.1 : ℝ) * (1 - r)) * (if k = 0 then 1 + r else 1) := by
    cases k with
    | zero =>
      simp [suzukiGammaBoundaryRow, suzukiCausalDepthGammaWeightedFeature,
        suzukiCausalDepthGammaFeature, suzukiGammaBoundaryCoefficient,
        suzukiCausalDepthGammaSurvivingDegree, gammaConductorJacobiFeature, r, phi, w]
      ring
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, mul_one]
      simp only [suzukiGammaBoundaryRow, suzukiCausalDepthGammaWeightedFeature,
        suzukiCausalDepthGammaFeature, suzukiGammaBoundaryCoefficient,
        suzukiCausalDepthGammaSurvivingDegree, gammaConductorJacobiFeature]
      dsimp [r, phi, w]
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
      ring
  have hlast0 : 0 ≤ (if k = 0 then 1 + r else 1) := by split_ifs <;> positivity
  have hlast : (if k = 0 then 1 + r else 1) ≤ 2 := by split_ifs <;> linarith
  rw [hfactor, abs_of_nonneg (by positivity)]
  calc
    _ ≤ w * 1 * 1 * 1 * 1 * 2 * 2 := by gcongr
    _ = 4 * w := by ring

/-- All prime depths are admitted by each cancelled row. -/
theorem summable_sq_suzukiGammaBoundaryRow
    (h a : Set.Ioi (0 : ℝ)) (k : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ => suzukiGammaBoundaryRow h.1 a.1 k pe ^ 2) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_
    ((summable_sq_suzukiCausalDepthGammaWeight_allPrime h.2 a.2).mul_left 16)
  intro pe
  have hb := abs_suzukiGammaBoundaryRow_le h a k pe
  have hw := (suzukiCausalDepthGammaWeight_pos h.2 a.2 pe).le
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ 4 * suzukiCausalDepthGammaWeight h.1 a.1 pe)).2 hb
  nlinarith only [hs, sq_abs (suzukiGammaBoundaryRow h.1 a.1 k pe)]

end RHTower
