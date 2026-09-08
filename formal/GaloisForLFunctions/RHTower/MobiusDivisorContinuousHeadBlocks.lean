import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadMoment
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreBlockLimit

/-!
# Literal continuous head coefficients on every quotient block

Finite Mobius dilation carries the unit head's square-root interpolation
to each closed integer block. Its endpoint values identify the slope and
intercept with the actual discrete head coefficients. Integer dilations
retain the nested quotient, including inactive blocks and both endpoints.
-/

noncomputable section
open Finset Set
namespace RHTower

private lemma unit_head_block (n : ℕ) {x : ℝ} (hx : x∈Set.Icc (n:ℝ) (n+1:ℕ)) :
    divisorContinuousUnitHead x = divisorUnsignedDilationChannel n 1+
      (Real.sqrt x-Real.sqrt n)*primeFreeDivisorDefect n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [divisorContinuousUnitHead_eq_zero (by simpa using hx.2)]
    simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect]
  · exact divisorContinuousUnitHead_between hn hx.1 hx.2

private lemma quotient_block {n d : ℕ} (hd : 0<d) {x : ℝ}
    (hx : x∈Set.Icc (n:ℝ) (n+1:ℕ)) :
    x/(d:ℝ) ∈ Set.Icc ((n/d:ℕ):ℝ) (n/d+1:ℕ) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hdR]
    exact (show ((n/d:ℕ):ℝ)*d≤(n:ℝ) by exact_mod_cast Nat.div_mul_le_self n d).trans hx.1
  · rw [div_le_iff₀ hdR]
    apply hx.2.trans
    exact_mod_cast (show n+1≤(n/d+1)*d by
      have h : n<(n/d+1)*d := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ n hd
      omega)

private lemma weighted_unit_block {n d : ℕ} (hd : 0<d) {x : ℝ}
    (hx : x∈Set.Icc (n:ℝ) (n+1:ℕ)) :
    Real.sqrt d*divisorContinuousUnitHead (x/d) =
      primeFreeDivisorDefect (n/d)*Real.sqrt x+
        Real.sqrt d*(divisorUnsignedDilationChannel (n/d) 1-
          Real.sqrt (n/d:ℕ)*primeFreeDivisorDefect (n/d)) := by
  rw [unit_head_block (n/d) (quotient_block hd hx),
    Real.sqrt_div (le_trans (Nat.cast_nonneg n) hx.1)]
  have hs : Real.sqrt (d:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  field_simp
  ring

private lemma head_affine_exists (P : Finset ℕ) (n : ℕ) :
    ∃a b : ℝ, ∀x∈Set.Icc (n:ℝ) (n+1:ℕ),
      mobiusDivisorContinuousHead P x=a*Real.sqrt x+b := by
  let D := (∏p∈P,p).divisors
  let mu : ℕ→ℝ := fun d => ((ArithmeticFunction.moebius d:ℤ):ℝ)
  refine ⟨∑d∈D,mu d*primeFreeDivisorDefect (n/d),
    ∑d∈D,mu d*Real.sqrt d*(divisorUnsignedDilationChannel (n/d) 1-
      Real.sqrt (n/d:ℕ)*primeFreeDivisorDefect (n/d)),?_⟩
  intro x hx
  rw [sum_mul,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have h := weighted_unit_block (Nat.pos_of_mem_divisors hd) hx
  dsimp [mu]
  linear_combination (((ArithmeticFunction.moebius d:ℤ):ℝ))*h

/-- The literal continuous processed head uses exactly the discrete head's
square-root slope and intercept on every closed unit block. -/
theorem mobiusDivisorContinuousHead_eq_block_affine (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) (n : ℕ) {x : ℝ}
    (hx : x∈Set.Icc (n:ℝ) (n+1:ℕ)) :
    mobiusDivisorContinuousHead P x =
      mobiusDivisorHeadBlockSlope P n*Real.sqrt x+mobiusDivisorHeadBlockIntercept P n := by
  obtain ⟨a,b,hab⟩ := head_affine_exists P n
  have hn : (n:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.le_succ n
  have h0 := hab n ⟨le_rfl,hn⟩
  have h1 := hab (n+1:ℕ) ⟨hn,le_rfl⟩
  rw [mobiusDivisorContinuousHead_nat P hP] at h0 h1
  have hs : Real.sqrt (n+1:ℕ)-Real.sqrt n≠0 := by
    apply sub_ne_zero.mpr
    exact (Real.sqrt_lt_sqrt (Nat.cast_nonneg n) (by exact_mod_cast Nat.lt_succ_self n)).ne'
  have ha : mobiusDivisorHeadBlockSlope P n=a := by
    rw [mobiusDivisorHeadBlockSlope,h1,h0]
    field_simp
    ring
  rw [mobiusDivisorHeadBlockIntercept,ha,h0,hab x hx]
  ring

/-- Integer dilation retains the exact nested quotient block, including
the inactive zero block and both clipping endpoints. -/
theorem mobiusDivisorContinuousHead_div_eq_block_affine (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) (n : ℕ) {p : ℕ} (hp : 0<p) {x : ℝ}
    (hx : x∈Set.Icc (n:ℝ) (n+1:ℕ)) :
    Real.sqrt p*mobiusDivisorContinuousHead P (x/p) =
      mobiusDivisorHeadBlockSlope P (n/p)*Real.sqrt x+
        Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p) := by
  rw [mobiusDivisorContinuousHead_eq_block_affine P hP (n/p) (quotient_block hp hx),
    Real.sqrt_div (le_trans (Nat.cast_nonneg n) hx.1)]
  have hs : Real.sqrt (p:ℝ)≠0 := (Real.sqrt_pos.mpr (by exact_mod_cast hp)).ne'
  field_simp

end RHTower
