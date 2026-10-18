import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailSmoothing
import GaloisForLFunctions.RHTower.EvenSectorStripPositivity

/-! The actual correction tail has uniformly negligible non-archimedean cost.
The ordinary prime series converges absolutely and equals its Abel pairing.
The resulting `1/(n+1)` budget isolates the remaining archimedean energy. -/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.EvenSector
open _root_.Zeta23
noncomputable section
set_option autoImplicit false

def factorialMuntzTailCorrelationConstant : ℝ :=
  144*Real.exp (3/2)^2*(∫ t : ℝ, Real.exp (-((1/4 : ℝ)*|t|)))

theorem factorialMuntzTailCorrelationConstant_nonneg : 0 ≤ factorialMuntzTailCorrelationConstant := by
  unfold factorialMuntzTailCorrelationConstant
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => (Real.exp_pos _).le)

theorem factorialMuntzSmoothedTail_crossCorr_bound (n k : ℕ) (y : ℝ) :
    |crossCorr (factorialMuntzSmoothedTail n k) (factorialMuntzSmoothedTail n k) y| ≤
      (factorialMuntzTailCorrelationConstant/((n+1 : ℕ) : ℝ))*
        Real.exp (-((5/4 : ℝ)*|y|)) := by
  have h := abs_crossCorr_le_of_decay (b := (3/2 : ℝ)) (b₁ := (5/4 : ℝ))
    (by norm_num) (by norm_num) (by positivity)
      (factorialMuntzSmoothedTail_exp_bound n k) (factorialMuntzSmoothedTail_exp_bound n k) y
  rw [show (3/2 : ℝ)-5/4 = 1/4 by norm_num] at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ) by positivity)]
      unfold factorialMuntzTailCorrelationConstant
      ring

def factorialMuntzTailPrimeAtom (n k j : ℕ) : ℝ :=
  (if 2 ≤ j then (ArithmeticFunction.vonMangoldt j : ℝ)/Real.sqrt j else 0)*
    (crossCorr (factorialMuntzSmoothedTail n k) (factorialMuntzSmoothedTail n k) (Real.log j)+
      crossCorr (factorialMuntzSmoothedTail n k) (factorialMuntzSmoothedTail n k) (-Real.log j))

private theorem vonMangoldt_growth (j : ℕ) (hj : 2 ≤ j) :
    |(ArithmeticFunction.vonMangoldt j : ℝ)| ≤ 1*Real.sqrt j*(1+Real.log j) := by
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]
  have hlog : ArithmeticFunction.vonMangoldt j ≤ Real.log (j : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hsqrt : 1 ≤ Real.sqrt (j : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hj1
  have hlog0 := Real.log_natCast_nonneg j
  calc
    _ ≤ Real.log (j : ℝ) := hlog
    _ ≤ 1*(1+Real.log (j : ℝ)) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt (by positivity)

theorem factorialMuntzTailPrimeAtom_bound (n k j : ℕ) :
    |factorialMuntzTailPrimeAtom n k j| ≤
      (2*factorialMuntzTailCorrelationConstant/((n+1 : ℕ) : ℝ))*
        ((1+Real.log j)*(j : ℝ)^(-(5/4 : ℝ))) := by
  have hD := factorialMuntzTailCorrelationConstant_nonneg
  have hlog0 := Real.log_natCast_nonneg j
  unfold factorialMuntzTailPrimeAtom
  split_ifs with hj
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hs : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
    have hw : |(ArithmeticFunction.vonMangoldt j : ℝ)/Real.sqrt j| ≤ 1+Real.log j := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      simpa only [one_mul, mul_comm] using vonMangoldt_growth j hj
    have he : Real.exp (-((5/4 : ℝ)*|Real.log j|)) = (j : ℝ)^(-(5/4 : ℝ)) := by
      rw [abs_of_nonneg hlog0, Real.rpow_def_of_pos hj0]
      congr 1
      ring
    have h1 := factorialMuntzSmoothedTail_crossCorr_bound n k (Real.log j)
    have h2 := factorialMuntzSmoothedTail_crossCorr_bound n k (-Real.log j)
    rw [he] at h1
    rw [abs_neg, he] at h2
    have hsum : |crossCorr (factorialMuntzSmoothedTail n k) (factorialMuntzSmoothedTail n k) (Real.log j)+
        crossCorr (factorialMuntzSmoothedTail n k) (factorialMuntzSmoothedTail n k) (-Real.log j)| ≤
        2*(factorialMuntzTailCorrelationConstant/((n+1 : ℕ) : ℝ))*(j : ℝ)^(-(5/4 : ℝ)) :=
      (_root_.abs_add_le _ _).trans (by linarith)
    rw [abs_mul]
    calc
      _ ≤ (1+Real.log j)*(2*(factorialMuntzTailCorrelationConstant/((n+1 : ℕ) : ℝ))*
          (j : ℝ)^(-(5/4 : ℝ))) := mul_le_mul hw hsum (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [zero_mul, abs_zero]
    positivity

/-- This is ordinary absolute convergence, before identifying the Abel value. -/
theorem factorialMuntzTailPrimeAtom_abs_summable (n k : ℕ) :
    Summable (fun j : ℕ => |factorialMuntzTailPrimeAtom n k j|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (factorialMuntzTailPrimeAtom_bound n k)
      ((summable_one_add_log_mul_rpow (b₁ := 5/4) (by norm_num)).mul_left _)

def factorialMuntzTailPrimeBudget : ℝ :=
  2*factorialMuntzTailCorrelationConstant*
    ∑' j : ℕ, (1+Real.log j)*(j : ℝ)^(-(5/4 : ℝ))

theorem factorialMuntzTailPrimeBudget_nonneg : 0 ≤ factorialMuntzTailPrimeBudget := by
  unfold factorialMuntzTailPrimeBudget
  have hD := factorialMuntzTailCorrelationConstant_nonneg
  apply mul_nonneg (by positivity)
  apply tsum_nonneg
  intro j
  have hlog0 := Real.log_natCast_nonneg j
  positivity

theorem factorialMuntzTailPrimeSum_bound (n k : ℕ) :
    |∑' j : ℕ, factorialMuntzTailPrimeAtom n k j| ≤
      factorialMuntzTailPrimeBudget/((n+1 : ℕ) : ℝ) := by
  have hs := factorialMuntzTailPrimeAtom_abs_summable n k
  have hn : Summable (fun j : ℕ => ‖factorialMuntzTailPrimeAtom n k j‖) := by
    simpa only [Real.norm_eq_abs] using hs
  calc
    _ ≤ ∑' j : ℕ, |factorialMuntzTailPrimeAtom n k j| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, (2*factorialMuntzTailCorrelationConstant/((n+1 : ℕ) : ℝ))*
        ((1+Real.log j)*(j : ℝ)^(-(5/4 : ℝ))) :=
      hs.tsum_le_tsum (factorialMuntzTailPrimeAtom_bound n k)
        ((summable_one_add_log_mul_rpow (b₁ := 5/4) (by norm_num)).mul_left _)
    _ = _ := by
      rw [tsum_mul_left]
      unfold factorialMuntzTailPrimeBudget
      ring

/-- The two already justified truncation limits identify the ordinary prime
series with the complete Abel pairing, without discarding a boundary term. -/
theorem factorialMuntzSmoothedTail_abelPrimePairing_eq (n k : ℕ) :
    abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (factorialMuntzSmoothedTail n k) = ∑' j : ℕ, factorialMuntzTailPrimeAtom n k j := by
  have hE := factorialMuntzSmoothedTail_expDecayTest n k
  have h1 := tendsto_atomPairing_truncTest_of_growth vonMangoldt_growth hE
    (by norm_num : (1 : ℝ) < 3/2) (by positivity) (factorialMuntzSmoothedTail_exp_bound n k)
  have h2 := tendsto_atomPairing_truncTest_abelPrimePairing hE (A := 7)
    (w := fun j => (ArithmeticFunction.vonMangoldt j : ℝ)) abs_primeWeightPartialSum_vonMangoldt_le
  exact (tendsto_nhds_unique h1 h2).symm

theorem factorialMuntzSmoothedTail_abelPrimePairing_bound (n k : ℕ) :
    |abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
      (factorialMuntzSmoothedTail n k)| ≤ factorialMuntzTailPrimeBudget/((n+1 : ℕ) : ℝ) := by
  rw [factorialMuntzSmoothedTail_abelPrimePairing_eq]
  exact factorialMuntzTailPrimeSum_bound n k

/-- One threshold in `n` controls every smoothing choice, even a choice that
depends on `n`. Prime and pole costs are negligible at the logarithmic scale. -/
theorem factorialMuntzSmoothedTail_prime_polar_log_scale :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      |abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
          (factorialMuntzSmoothedTail n k)| + |factorialMuntzTailPolarTerm n k| ≤
        ε*Real.log ((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ) := by
  intro ε hε
  have hn : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hl := Real.tendsto_log_atTop.comp hn
  have hb := (tendsto_atTop.1 hl) ((factorialMuntzTailPrimeBudget+144*Real.exp 1^2)/ε)
  filter_upwards [hb] with n hn
  intro k
  calc
    _ ≤ factorialMuntzTailPrimeBudget/((n+1 : ℕ) : ℝ)+
        144*Real.exp 1^2/((n+1 : ℕ) : ℝ) := add_le_add
      (factorialMuntzSmoothedTail_abelPrimePairing_bound n k) (factorialMuntzTailPolarTerm_bound n k)
    _ = (factorialMuntzTailPrimeBudget+144*Real.exp 1^2)/((n+1 : ℕ) : ℝ) := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Function.comp_def, mul_comm] using (div_le_iff₀ hε).1 hn

/-- The actual full zero-side form differs from the actual archimedean
integral by at most a fixed `1/(n+1)` budget, uniformly in smoothing. -/
theorem factorialMuntzSmoothedTail_zero_arch_budget (n k : ℕ) :
    |(zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
      1/(2*Real.pi)*(∫ r : ℝ,
        ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) r‖^2*EF.gammaBracket r)| ≤
      (factorialMuntzTailPrimeBudget+144*Real.exp 1^2)/((n+1 : ℕ) : ℝ) := by
  have hi := archPoleEnergy_eq_re_W_add_abelPrimePairing
    (factorialMuntzSmoothedTail_expDecayTest n k)
  change factorialMuntzTailPolarTerm n k + _ = _ at hi
  have he : (zetaZeroConfig.W (fun x => (factorialMuntzSmoothedTail n k x : ℂ))
        (fun x => (factorialMuntzSmoothedTail n k x : ℂ))).re -
      1/(2*Real.pi)*(∫ r : ℝ,
        ‖paperFT (fun x => (factorialMuntzSmoothedTail n k x : ℂ)) r‖^2*EF.gammaBracket r) =
      factorialMuntzTailPolarTerm n k -
        abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
          (factorialMuntzSmoothedTail n k) := by linarith only [hi]
  rw [he]
  calc
    _ ≤ |factorialMuntzTailPolarTerm n k| +
        |abelPrimePairing (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
          (factorialMuntzSmoothedTail n k)| := abs_sub _ _
    _ ≤ 144*Real.exp 1^2/((n+1 : ℕ) : ℝ)+factorialMuntzTailPrimeBudget/((n+1 : ℕ) : ℝ) :=
      add_le_add (factorialMuntzTailPolarTerm_bound n k)
        (factorialMuntzSmoothedTail_abelPrimePairing_bound n k)
    _ = _ := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
