import GaloisForLFunctions.RHTower.ThetaArithmeticWeightedAdmission
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionTerminalCusp
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Graded admission and escape of actual finite prime deletion

The sharp terminal-word theorem gives `q < 2 / P²` for the literal finite
Euler deletion, `q < 2 / p⁴` for the prime-square source, finiteness at each
fixed positive weight, and escape from every such carrier along a prime
exhaustion. No analytic admission or source asymptotic is a premise.
-/

open Filter Topology Set MeasureTheory ArithmeticFunction

namespace RHTower

noncomputable section

theorem thetaPrimeDeletionWordCoefficient_eq_moebius_div_sqrt (d : ℕ) (hd : 0 < d) :
    thetaPrimeDeletionWordCoefficient d = (moebius d : ℝ) / Real.sqrt (d : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  simp only [thetaPrimeDeletionWordCoefficient, Real.rpow_neg hdR.le,
    Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- The card's exact terminal coefficient, including its square-root normalization. -/
theorem thetaPrimeDeletion_terminal_ratio_moebius
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun x : ℝ => thetaPrimeDeletion S thetaCuspFullSource (-x) /
      thetaCuspFullSource (x - Real.log ((∏ p ∈ S, p : ℕ) : ℝ)))
      atTop (𝓝 ((moebius (∏ p ∈ S, p) : ℝ) /
        Real.sqrt ((∏ p ∈ S, p : ℕ) : ℝ))) := by
  rw [← thetaPrimeDeletionWordCoefficient_eq_moebius_div_sqrt _
    (Finset.prod_pos fun p hp => (hS p hp).pos)]
  exact thetaPrimeDeletion_terminal_ratio S hS

theorem continuous_thetaPrimeDeletion_source
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Continuous (thetaPrimeDeletion S thetaCuspFullSource) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  exact continuous_finiteArithmeticThetaShift _ _

/-- Literal real `L²(k⁻q dx)` admission, with its boundary excluded. -/
theorem thetaPrimeDeletion_memLp_iff
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℝ) (hq : 0 < q) :
    MemLp (thetaPrimeDeletion S thetaCuspFullSource) 2 (thetaPowerWeightedMeasure q) ↔
      q < 2 / (((∏ p ∈ S, p : ℕ) : ℝ) ^ 2) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  exact finiteArithmeticThetaShift_memLp_iff
    (thetaPrimeDeletionWords S) thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p)
    (thetaPrimeDeletionWords_top_mem S) (thetaPrimeDeletionWords_positive S hS)
    (thetaPrimeDeletionWords_le_top S hS) (thetaPrimeDeletionWordCoefficient_top_ne_zero S hS)
    q hq

/-- The same exact admission theorem in the complex Hilbert carrier. -/
theorem thetaPrimeDeletion_ofReal_memLp_iff
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (q : ℝ) (hq : 0 < q) :
    MemLp (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) 2
      (thetaPowerWeightedMeasure q) ↔ q < 2 / (((∏ p ∈ S, p : ℕ) : ℝ) ^ 2) := by
  rw [thetaPrimeDeletion_eq_arithmeticShift S hS]
  exact finiteArithmeticThetaShift_ofReal_memLp_iff
    (thetaPrimeDeletionWords S) thetaPrimeDeletionWordCoefficient (∏ p ∈ S, p)
    (thetaPrimeDeletionWords_top_mem S) (thetaPrimeDeletionWords_positive S hS)
    (thetaPrimeDeletionWords_le_top S hS) (thetaPrimeDeletionWordCoefficient_top_ne_zero S hS)
    q hq

/-- The actual prime-square source, with its shift and coefficient unchanged. -/
def thetaPrimeSquareDeletion (p : ℕ) (x : ℝ) : ℝ :=
  thetaCuspFullSource x - (1 / (p : ℝ)) * thetaCuspFullSource (x + 2 * Real.log (p : ℝ))

def thetaPrimeSquareWordCoefficient (p d : ℕ) : ℝ :=
  if d = 1 then 1 else -(1 / (p : ℝ))

theorem thetaPrimeSquareDeletion_eq_arithmeticShift (p : ℕ) (hp : p.Prime) :
    thetaPrimeSquareDeletion p =
      finiteArithmeticThetaShift {1, p ^ 2} (thetaPrimeSquareWordCoefficient p) := by
  have hp2 : p ^ 2 ≠ 1 := by have h := hp.one_lt; nlinarith
  funext x
  dsimp only [thetaPrimeSquareDeletion]
  rw [finiteArithmeticThetaShift, Finset.sum_pair hp2.symm]
  simp only [thetaPrimeSquareWordCoefficient, if_neg hp2,
    Nat.cast_one, Real.log_one, add_zero, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  norm_num [sub_eq_add_neg]

private theorem thetaPrimeSquare_word_data (p : ℕ) (hp : p.Prime) :
    (p ^ 2 ∈ ({1, p ^ 2} : Finset ℕ)) ∧
    (∀ d ∈ ({1, p ^ 2} : Finset ℕ), 0 < d) ∧
    (∀ d ∈ ({1, p ^ 2} : Finset ℕ), d ≤ p ^ 2) ∧
    thetaPrimeSquareWordCoefficient p (p ^ 2) ≠ 0 := by
  have hp0 := hp.pos
  have hp2 : p ^ 2 ≠ 1 := by have h := hp.one_lt; nlinarith
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · omega
    · positivity
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · have h := hp.one_lt
      nlinarith
    · exact le_rfl
  · rw [thetaPrimeSquareWordCoefficient, if_neg hp2]
    have h : 0 < 1 / (p : ℝ) := by positivity
    exact neg_ne_zero.mpr h.ne'

/-- Prime-square deletion has the sharp threshold `2 / p⁴`, including equality failure. -/
theorem thetaPrimeSquareDeletion_memLp_iff
    (p : ℕ) (hp : p.Prime) (q : ℝ) (hq : 0 < q) :
    MemLp (thetaPrimeSquareDeletion p) 2 (thetaPowerWeightedMeasure q) ↔
      q < 2 / (p : ℝ) ^ 4 := by
  obtain ⟨hb, hpositive, hmax, hc⟩ := thetaPrimeSquare_word_data p hp
  rw [thetaPrimeSquareDeletion_eq_arithmeticShift p hp]
  simpa [Nat.cast_pow, ← pow_mul] using finiteArithmeticThetaShift_memLp_iff
    {1, p ^ 2} (thetaPrimeSquareWordCoefficient p) (p ^ 2) hb hpositive hmax hc q hq

theorem thetaPrimeSquareDeletion_ofReal_memLp_iff
    (p : ℕ) (hp : p.Prime) (q : ℝ) (hq : 0 < q) :
    MemLp (fun x => (thetaPrimeSquareDeletion p x : ℂ)) 2 (thetaPowerWeightedMeasure q) ↔
      q < 2 / (p : ℝ) ^ 4 := by
  obtain ⟨hb, hpositive, hmax, hc⟩ := thetaPrimeSquare_word_data p hp
  rw [thetaPrimeSquareDeletion_eq_arithmeticShift p hp]
  simpa [Nat.cast_pow, ← pow_mul] using finiteArithmeticThetaShift_ofReal_memLp_iff
    {1, p ^ 2} (thetaPrimeSquareWordCoefficient p) (p ^ 2) hb hpositive hmax hc q hq

/-- Finite prime alphabets whose literal source belongs to the complex carrier. -/
def thetaAdmittedPrimeDeletions (q : ℝ) : Set (Finset ℕ) :=
  {S | (∀ p ∈ S, p.Prime) ∧
    MemLp (fun x => (thetaPrimeDeletion S thetaCuspFullSource x : ℂ)) 2
      (thetaPowerWeightedMeasure q)}

/-- A fixed positive weight admits only finitely many finite prime alphabets. -/
theorem thetaAdmittedPrimeDeletions_finite (q : ℝ) (hq : 0 < q) :
    (thetaAdmittedPrimeDeletions q).Finite := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_gt (2 / q)
  refine ((Finset.range B).powerset.finite_toSet).subset ?_
  intro S hS
  obtain ⟨hprime, hmem⟩ := hS
  have hadmit := (thetaPrimeDeletion_ofReal_memLp_iff S hprime q hq).mp hmem
  let P : ℕ := ∏ p ∈ S, p
  have hP0 : 0 < P := Finset.prod_pos fun p hp => (hprime p hp).pos
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (show 1 ≤ P from hP0)
  have hP2 : (P : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith [sq_nonneg ((P : ℝ) - 1)]
  have hbound : (P : ℝ) < 2 / q := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < (P : ℝ) ^ 2)).mp hadmit
    have hmul := mul_le_mul_of_nonneg_left hP2 hq.le
    apply (lt_div_iff₀ hq).mpr
    nlinarith
  have hPB : P < B := by exact_mod_cast hbound.trans hB
  apply Finset.mem_powerset.mpr
  intro p hp
  apply Finset.mem_range.mpr
  have hpP : p ≤ P :=
    Finset.single_le_prod' (fun p hp => (hprime p hp).one_lt.le) hp
  exact hpP.trans_lt hPB

/-- The terminal prime product diverges along every cofinal prime exhaustion. -/
theorem PrimeExhaustion.tendsto_primeProduct {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun j => ∏ p ∈ S j, p) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  filter_upwards [hS.eventually_mem p hp] with j hj
  exact hNp.trans (Finset.single_le_prod' (fun p hp => (hS.prime j p hp).one_lt.le) hj)

/-- Cofinal terminal-word admission thresholds shrink to zero. -/
theorem PrimeExhaustion.terminalThreshold_tendsto_zero
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun j => 2 / (((∏ p ∈ S j, p : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hprod : Tendsto (fun j => ((∏ p ∈ S j, p : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hS.tendsto_primeProduct
  exact ((tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)).comp hprod).const_div_atTop 2

/-- Any sequence of positive weights admitting cofinal finite deletions must tend to zero. -/
theorem PrimeExhaustion.admitting_weights_tendsto_zero
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (q : ℕ → ℝ) (hq : ∀ j, 0 < q j)
    (hadmit : ∀ j, MemLp (fun x => (thetaPrimeDeletion (S j) thetaCuspFullSource x : ℂ)) 2
      (thetaPowerWeightedMeasure (q j))) :
    Tendsto q atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hS.terminalThreshold_tendsto_zero (fun j => (hq j).le) ?_
  intro j
  exact ((thetaPrimeDeletion_ofReal_memLp_iff (S j) (hS.prime j) (q j) (hq j)).mp
    (hadmit j)).le

/-- Every fixed positive Hilbert carrier eventually excludes a cofinal finite deletion. -/
theorem PrimeExhaustion.eventually_not_memLp
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) (q : ℝ) (hq : 0 < q) :
    ∀ᶠ j in atTop, ¬ MemLp (fun x => (thetaPrimeDeletion (S j) thetaCuspFullSource x : ℂ)) 2
      (thetaPowerWeightedMeasure q) := by
  filter_upwards [hS.terminalThreshold_tendsto_zero.eventually (Iio_mem_nhds hq)] with j hj
  intro hmem
  have h := (thetaPrimeDeletion_ofReal_memLp_iff (S j) (hS.prime j) q hq).mp hmem
  linarith

end

end RHTower
