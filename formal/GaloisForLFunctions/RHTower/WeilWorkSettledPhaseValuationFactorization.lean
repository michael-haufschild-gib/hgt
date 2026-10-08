import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationExponential
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationLogarithm
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeRatio
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Splitting the actual source at one prime

The Dirichlet exponential splits into its coprime factor and the exponential
of its noncoprime logarithm. This is a convolution identity for the actual
source; no Euler product or multiplicativity is assumed.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSingularArithmetic
open IntegerMassRigidity WeilWorkSettledPhase

theorem nonCoprimePart_eq_zero_of_not_dvd {p : ℕ} (hp : p.Prime)
    (f : ℕ → ℂ) (n : ℕ) (hn : ¬p ∣ n) : nonCoprimePart p f n = 0 := by
  have hc : n.Coprime p := Nat.coprime_comm.mpr (hp.coprime_iff_not_dvd.mpr hn)
  simp only [nonCoprimePart, if_pos hc]

theorem valuationPart_nonCoprimePart_zero {p : ℕ} (hp : p.Prime) (f : ℕ → ℂ) :
    valuationPart p 0 (nonCoprimePart p f) = 0 := by
  rw [valuationPart_zero_eq_coprimePart hp]
  funext n
  by_cases hc : n.Coprime p <;> simp [coprimePart, coprimeMask, nonCoprimePart, hc]

theorem valuationPart_nonCoprimePart_succ {p : ℕ} (hp : p.Prime)
    (f : ℕ → ℂ) (k : ℕ) :
    valuationPart p (k + 1) (nonCoprimePart p f) = valuationPart p (k + 1) f := by
  funext n
  by_cases hv : p ^ (k + 1) ∣ n ∧ ¬p ^ (k + 1 + 1) ∣ n
  · have hd : p ∣ n := by
      apply (show p ∣ p ^ (k + 1) from ⟨p ^ k, by rw [pow_succ, mul_comm]⟩).trans hv.1
    have hc : ¬n.Coprime p := fun hc => (hp.coprime_iff_not_dvd.mp hc.symm) hd
    simp [valuationPart, valuationMask, nonCoprimePart, hv, hc]
  · simp [valuationPart, valuationMask, hv]

theorem valuationPart_lamLog (lam : ℕ → ℝ) (p k : ℕ) :
    valuationPart p k (lamLog lam) = logZetaCoeff (valuationSourceCoeff lam p k) := by
  funext n
  by_cases hn : 2 ≤ n <;> by_cases hv : p ^ k ∣ n ∧ ¬p ^ (k + 1) ∣ n <;>
    simp [valuationPart, valuationMask, lamLog, logZetaCoeff, valuationSourceCoeff, hn, hv]

/-- A genuine coefficient identity, established on the half-plane of absolute convergence. -/
theorem sourceCoeff_prime_factorization {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (p : ℕ) :
    sourceCoeff lam = LSeries.convolution
      (dirichletExp (nonCoprimePart p (lamLog lam))) (coprimePart p (sourceCoeff lam)) := by
  have hl {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (lamLog lam) s :=
    lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hs
  have ha {s : ℂ} (hs : 1 < s.re) :=
    LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam) (hl hs)
  have hb {s : ℂ} (hs : 1 < s.re) := LSeries_dirichletExp
    (show nonCoprimePart p (lamLog lam) 0 = 0 by simp [nonCoprimePart, lamLog_zero])
    (show nonCoprimePart p (lamLog lam) 1 = 0 by simp [nonCoprimePart])
    (summable_nonCoprimePart p (hl hs))
  have hc {s : ℂ} (hs : 1 < s.re) :
      LSeries (coprimePart p (dirichletExp (lamLog lam))) s =
        cexp (LSeries (coprimePart p (lamLog lam)) s) := by
    rw [coprimePart_dirichletExp]
    exact (LSeries_dirichletExp
      (show coprimePart p (lamLog lam) 0 = 0 by simp [coprimePart, lamLog_zero])
      (show coprimePart p (lamLog lam) 1 = 0 by simp [coprimePart, lamLog_one])
      (summable_coprimePart p (hl hs))).2
  have hsplit : nonCoprimePart p (lamLog lam) + coprimePart p (lamLog lam) = lamLog lam := by
    rw [nonCoprimePart_eq_sub]
    abel
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have habs := (ha h2).1
  have hconv := (hb h2).1.convolution (summable_coprimePart p habs)
  funext n
  by_cases hn : n = 0
  · subst n
    simp [sourceCoeff, dirichletExp_zero]
  apply LSeries.eq_of_LSeries_eventually_eq
    (lt_of_le_of_lt habs.abscissaOfAbsConv_le (by simp))
    (lt_of_le_of_lt hconv.abscissaOfAbsConv_le (by simp)) ?_ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  rw [LSeries_convolution' (hb hσ).1 (summable_coprimePart p (ha hσ).1),
    (ha hσ).2, (hb hσ).2, hc hσ, ← Complex.exp_add]
  rw [← LSeries_add (summable_nonCoprimePart p (hl hσ)) (summable_coprimePart p (hl hσ)), hsplit]

/-- The coprime factor is shared by every exact valuation component. -/
theorem valuation_source_ratio_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (p k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    LSeries (valuationPart p k (sourceCoeff lam)) (σ : ℂ) /
        LSeries (sourceCoeff lam) (σ : ℂ) =
      LSeries (valuationPart p k (dirichletExp (nonCoprimePart p (lamLog lam)))) (σ : ℂ) *
        (LSeries (coprimePart p (sourceCoeff lam)) (σ : ℂ) /
          LSeries (sourceCoeff lam) (σ : ℂ)) := by
  have hl : LSeriesSummable (lamLog lam) (σ : ℂ) :=
    lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ h => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW h) hσ
  have hb := (LSeries_dirichletExp
    (show nonCoprimePart p (lamLog lam) 0 = 0 by simp [nonCoprimePart, lamLog_zero])
    (show nonCoprimePart p (lamLog lam) 1 = 0 by simp [nonCoprimePart])
    (summable_nonCoprimePart p hl)).1
  have he : valuationPart p k (sourceCoeff lam) = LSeries.convolution
      (valuationPart p k (dirichletExp (nonCoprimePart p (lamLog lam))))
      (coprimePart p (sourceCoeff lam)) := by
    conv_lhs => rw [sourceCoeff_prime_factorization hW p]
    exact valuationPart_convolution_coprimePart p k _ _
  rw [he, LSeries_convolution' (summable_valuationPart p k hb)
    (summable_coprimePart p (sourceCoeff_LSeries hW (s := (σ : ℂ)) hσ).1)]
  ring

end RHTower.WeilSingularArithmetic
