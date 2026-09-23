import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionLogCoefficient
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Absolute summability of the differentiated Euler correction

`‖corr^{log}‖₁ < ∞`.  The quantitative content is already available: each local fibre has mass at
most `16 log p / p²` (`tsum_abs_selbergCorrectionLogLocal_le`), and `∑_p log p / p²` converges.
What remains is the regrouping, and for a nonnegative majorant an **injection** suffices — the
`p`-adic splitting `(m,n) ↦ ((v_p m, v_p n), (m/p^{v_p m}, n/p^{v_p n}))` is injective on positive
pairs because `m = p^{v_p m}·(m/p^{v_p m})`.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

theorem selbergCorrectionLogMajorant_nonneg' (p α β : ℕ) :
    0 ≤ selbergCorrectionLogMajorant p α β := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;>
      simp [selbergCorrectionLogMajorant, geomTailTwo, geomTailOne]
  · exact selbergCorrectionLogMajorant_nonneg hp α β

theorem summable_selbergCorrectionLogMajorant' (p : ℕ) :
    Summable (fun ab : ℕ × ℕ => selbergCorrectionLogMajorant p ab.1 ab.2) := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · refine summable_zero.congr ?_
    intro ab
    interval_cases p <;>
      simp [selbergCorrectionLogMajorant, geomTailTwo, geomTailOne]
  · exact summable_selbergCorrectionLogMajorant hp

theorem tsum_selbergCorrectionLogMajorant_le' (p : ℕ) :
    (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2) ≤
      16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ) := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · have hfun : ∀ ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2 = 0 := by
      intro ab
      interval_cases p <;>
        simp [selbergCorrectionLogMajorant, geomTailTwo, geomTailOne]
    have hzero : (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2) = 0 := by
      simp [hfun]
    rw [hzero]
    interval_cases p <;> simp
  · exact tsum_selbergCorrectionLogMajorant_le hp

theorem summable_sixteen_log_div_sq :
    Summable (fun p : ℕ => 16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) := by
  refine (summable_log_div_sq.mul_left 16).congr ?_
  intro p
  ring

/-- Absolute mass of the Euler correction. -/
theorem summable_abs_selbergEulerCorrectionCoeff :
    Summable (fun mn : ℕ × ℕ => |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
  have hnorm := summable_selbergEulerCorrectionCoeff.norm
  simpa [Real.norm_eq_abs] using hnorm

/-- The `p`-adic splitting of a pair. -/
def padicSplit (p : ℕ) (mn : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((mn.1.factorization p, mn.2.factorization p),
    (mn.1 / p ^ mn.1.factorization p, mn.2 / p ^ mn.2.factorization p))

theorem padicSplit_injective (p : ℕ) : Function.Injective (padicSplit p) := by
  intro x y hxy
  rw [padicSplit, padicSplit] at hxy
  have h1 : x.1.factorization p = y.1.factorization p := congrArg (fun z => z.1.1) hxy
  have h2 : x.2.factorization p = y.2.factorization p := congrArg (fun z => z.1.2) hxy
  have h3 : x.1 / p ^ x.1.factorization p = y.1 / p ^ y.1.factorization p :=
    congrArg (fun z => z.2.1) hxy
  have h4 : x.2 / p ^ x.2.factorization p = y.2 / p ^ y.2.factorization p :=
    congrArg (fun z => z.2.2) hxy
  have hx1 : p ^ x.1.factorization p * (x.1 / p ^ x.1.factorization p) = x.1 :=
    Nat.ordProj_mul_ordCompl_eq_self x.1 p
  have hy1 : p ^ y.1.factorization p * (y.1 / p ^ y.1.factorization p) = y.1 :=
    Nat.ordProj_mul_ordCompl_eq_self y.1 p
  have hx2 : p ^ x.2.factorization p * (x.2 / p ^ x.2.factorization p) = x.2 :=
    Nat.ordProj_mul_ordCompl_eq_self x.2 p
  have hy2 : p ^ y.2.factorization p * (y.2 / p ^ y.2.factorization p) = y.2 :=
    Nat.ordProj_mul_ordCompl_eq_self y.2 p
  refine Prod.ext ?_ ?_
  · rw [← hx1, ← hy1, h3, h1]
  · rw [← hx2, ← hy2, h4, h2]

/-- The `p`-fibre summand of the majorant. -/
def padicMajorantTerm (p : ℕ) (mn : ℕ × ℕ) : ℝ :=
  selbergCorrectionLogMajorant p (mn.1.factorization p) (mn.2.factorization p) *
    |selbergEulerCorrectionCoeff (mn.1 / p ^ mn.1.factorization p)
      (mn.2 / p ^ mn.2.factorization p)|

theorem padicMajorantTerm_nonneg (p : ℕ) (mn : ℕ × ℕ) :
    0 ≤ padicMajorantTerm p mn :=
  mul_nonneg (selbergCorrectionLogMajorant_nonneg' _ _ _) (abs_nonneg _)

/-- The product majorant on the split index set. -/
def splitMajorant (p : ℕ) (y : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  selbergCorrectionLogMajorant p y.1.1 y.1.2 *
    |selbergEulerCorrectionCoeff y.2.1 y.2.2|

theorem summable_splitMajorant (p : ℕ) :
    Summable (splitMajorant p) :=
  (summable_selbergCorrectionLogMajorant' p).mul_of_nonneg
    summable_abs_selbergEulerCorrectionCoeff
    (fun ab => selbergCorrectionLogMajorant_nonneg' p ab.1 ab.2)
    (fun _ => abs_nonneg _)

theorem tsum_splitMajorant_eq (p : ℕ) :
    (∑' y : (ℕ × ℕ) × (ℕ × ℕ), splitMajorant p y) =
      (∑' ab : ℕ × ℕ, selbergCorrectionLogMajorant p ab.1 ab.2) *
        (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|) :=
  ((summable_selbergCorrectionLogMajorant' p).tsum_mul_tsum
    summable_abs_selbergEulerCorrectionCoeff (summable_splitMajorant p)).symm

theorem splitMajorant_nonneg (p : ℕ) (y : (ℕ × ℕ) × (ℕ × ℕ)) :
    0 ≤ splitMajorant p y :=
  mul_nonneg (selbergCorrectionLogMajorant_nonneg' _ _ _) (abs_nonneg _)

theorem summable_padicMajorantTerm (p : ℕ) : Summable (padicMajorantTerm p) := by
  refine ((summable_splitMajorant p).comp_injective (padicSplit_injective p)).congr ?_
  intro mn
  rfl

theorem tsum_padicMajorantTerm_le (p : ℕ) :
    (∑' mn : ℕ × ℕ, padicMajorantTerm p mn) ≤
      (16 * Real.log (p : ℝ) / (p : ℝ) ^ (2 : ℕ)) *
        (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
  refine (summable_padicMajorantTerm p).tsum_le_of_sum_le ?_
  intro s
  have hinj : Set.InjOn (padicSplit p) ↑s := fun a _ b _ h => padicSplit_injective p h
  have hrw : ∀ i ∈ s, padicMajorantTerm p i = splitMajorant p (padicSplit p i) :=
    fun _ _ => rfl
  rw [Finset.sum_congr rfl hrw, ← Finset.sum_image hinj]
  refine le_trans ((summable_splitMajorant p).sum_le_tsum _
    (fun y _ => splitMajorant_nonneg p y)) ?_
  rw [tsum_splitMajorant_eq]
  exact mul_le_mul_of_nonneg_right (tsum_selbergCorrectionLogMajorant_le' p)
    (tsum_nonneg fun _ => abs_nonneg _)

theorem summable_padicMajorantProd :
    Summable (fun x : ℕ × (ℕ × ℕ) => padicMajorantTerm x.1 x.2) := by
  rw [summable_prod_of_nonneg (fun x => padicMajorantTerm_nonneg x.1 x.2)]
  refine ⟨fun p => summable_padicMajorantTerm p, ?_⟩
  exact Summable.of_nonneg_of_le
    (fun p => tsum_nonneg fun mn => padicMajorantTerm_nonneg p mn)
    (fun p => tsum_padicMajorantTerm_le p)
    (summable_sixteen_log_div_sq.mul_right _)

theorem summable_padicMajorantSwap :
    Summable (fun x : (ℕ × ℕ) × ℕ => padicMajorantTerm x.2 x.1) := by
  refine ((Equiv.prodComm (ℕ × ℕ) ℕ).summable_iff
    (f := fun x : ℕ × (ℕ × ℕ) => padicMajorantTerm x.1 x.2)).2
    summable_padicMajorantProd |>.congr ?_
  intro x
  rfl

theorem summable_padicMajorantTerm_fixed (mn : ℕ × ℕ) :
    Summable (fun p : ℕ => padicMajorantTerm p mn) :=
  ((summable_prod_of_nonneg
    (f := fun x : (ℕ × ℕ) × ℕ => padicMajorantTerm x.2 x.1)
    (fun x => padicMajorantTerm_nonneg x.2 x.1)).1 summable_padicMajorantSwap).1 mn

theorem summable_padicMajorantSum :
    Summable (fun mn : ℕ × ℕ => ∑' p : ℕ, padicMajorantTerm p mn) :=
  ((summable_prod_of_nonneg
    (f := fun x : (ℕ × ℕ) × ℕ => padicMajorantTerm x.2 x.1)
    (fun x => padicMajorantTerm_nonneg x.2 x.1)).1 summable_padicMajorantSwap).2

theorem abs_selbergEulerCorrectionLogCoeff_le (mn : ℕ × ℕ) :
    |selbergEulerCorrectionLogCoeff mn.1 mn.2| ≤
      ∑' p : ℕ, padicMajorantTerm p mn := by
  by_cases hz : mn.1 = 0 ∨ mn.2 = 0
  · rw [selbergEulerCorrectionLogCoeff, if_pos hz, abs_zero]
    exact tsum_nonneg fun p => padicMajorantTerm_nonneg p mn
  · rw [selbergEulerCorrectionLogCoeff, if_neg hz]
    have hstep : |∑ p ∈ (mn.1 * mn.2).primeFactors,
        selbergCorrectionLogLocal p (mn.1.factorization p) (mn.2.factorization p) *
          selbergEulerCorrectionCoeff (mn.1 / p ^ (mn.1.factorization p))
            (mn.2 / p ^ (mn.2.factorization p))| ≤
        ∑ p ∈ (mn.1 * mn.2).primeFactors, padicMajorantTerm p mn := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro p hp
      have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
      rw [abs_mul, padicMajorantTerm]
      exact mul_le_mul_of_nonneg_right
        (abs_selbergCorrectionLogLocal_le hprime.two_le _ _) (abs_nonneg _)
    refine hstep.trans ?_
    exact (summable_padicMajorantTerm_fixed mn).sum_le_tsum _
      (fun p _ => padicMajorantTerm_nonneg p mn)

/-- **Absolute summability of the differentiated Euler correction.** -/
theorem summable_abs_selbergEulerCorrectionLogCoeff :
    Summable (fun mn : ℕ × ℕ => |selbergEulerCorrectionLogCoeff mn.1 mn.2|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    abs_selbergEulerCorrectionLogCoeff_le summable_padicMajorantSum

end

end RHTower.Sieve
