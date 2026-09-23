import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorDilationMean
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCorePrimeCorrelationLimit

/-!
# Physical integrals of the literal discrete prime-correlation blocks

The actual two-head kernel is absolutely integrable. Exact real-interval
head coefficients identify the derivative of the existing discrete block
primitive after inversion, including both endpoints. Each unit-block
integral therefore equals the original arithmetic mass's endpoint factor.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

/-- The physical product kernel of the complete discrete prime-release source. -/
def mobiusDivisorPrimeCorrelationKernel (P : Finset ℕ) (p : ℕ) (u : ℝ) : ℝ :=
  2*Real.sqrt p*mobiusDivisorContinuousHead P u*mobiusDivisorContinuousHead P (u/p)/u^(3 : ℕ)

/-- The literal prime-correlation kernel is absolutely integrable on its full ray. -/
theorem integrable_mobiusDivisorPrimeCorrelationKernel (P : Finset ℕ) {p : ℕ} (hp : 0<p) :
    IntegrableOn (mobiusDivisorPrimeCorrelationKernel P p) (Ioi 1) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have h := (integrable_mobiusDivisorDilationMean_kernel P (inv_pos.mpr hpR)).const_mul (2*Real.sqrt p)
  apply h.congr
  filter_upwards with u
  dsimp [mobiusDivisorPrimeCorrelationKernel]
  rw [div_eq_mul_inv u (p:ℝ),mul_comm (p:ℝ)⁻¹ u]
  ring

private lemma deriv_mul_sqrt {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun u : ℝ => u*Real.sqrt u) ((3/2)*Real.sqrt t) t := by
  convert! (hasDerivAt_id t).mul (Real.hasDerivAt_sqrt ht.ne') using 1
  have hs : Real.sqrt t≠0 := (Real.sqrt_pos.mpr ht).ne'
  have hsq := Real.sq_sqrt ht.le
  simp only [id_eq]
  field_simp
  nlinarith

private lemma primitive_deriv (P : Finset ℕ) (p n : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (mobiusDivisorPrimeCorrelationPrimitive P p n)
      (2*(mobiusDivisorHeadBlockSlope P n+mobiusDivisorHeadBlockIntercept P n*Real.sqrt t)*
        (mobiusDivisorHeadBlockSlope P (n/p)+Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p)*Real.sqrt t)) t := by
  let a := mobiusDivisorHeadBlockSlope P n
  let b := mobiusDivisorHeadBlockIntercept P n
  let c := mobiusDivisorHeadBlockSlope P (n/p)
  let d := Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p)
  have h := (((hasDerivAt_id t).const_mul (a*c)).add
    ((deriv_mul_sqrt ht).const_mul ((2/3:ℝ)*(a*d+b*c)))).add
      (((hasDerivAt_id t).pow 2).const_mul (b*d/2))
  have h' := h.const_mul 2
  convert! h' using 1
  · ext u
    dsimp [mobiusDivisorPrimeCorrelationPrimitive,a,b,c,d]
    ring
  · dsimp [a,b,c,d]
    have hsq := Real.sq_sqrt ht.le
    norm_num only [id_eq,Nat.cast_ofNat,pow_one]
    linear_combination (2*mobiusDivisorHeadBlockIntercept P n*
      (Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p)))*hsq

private lemma inverse_primitive_deriv (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {p n : ℕ} (hp : 0<p) {u : ℝ} (hu : 0<u)
    (hblock : u∈Icc (n:ℝ) (n+1:ℕ)) :
    HasDerivAt (fun x : ℝ => -mobiusDivisorPrimeCorrelationPrimitive P p n (1/x))
      (mobiusDivisorPrimeCorrelationKernel P p u) u := by
  have h := ((primitive_deriv P p n (inv_pos.mpr hu)).comp u (hasDerivAt_inv hu.ne')).neg
  have ha := mobiusDivisorContinuousHead_eq_block_affine P hP n hblock
  have hb := mobiusDivisorContinuousHead_div_eq_block_affine P hP n hp hblock
  have hsq := Real.sq_sqrt hu.le
  have hs : Real.sqrt u≠0 := (Real.sqrt_pos.mpr hu).ne'
  convert! h using 1
  · funext x
    simp only [Function.comp_apply,Pi.neg_apply,one_div]
  · rw [Real.sqrt_inv]
    dsimp [mobiusDivisorPrimeCorrelationKernel]
    have he : 2*Real.sqrt p*mobiusDivisorContinuousHead P u*
        mobiusDivisorContinuousHead P (u/p) =
        2*(mobiusDivisorHeadBlockSlope P n*Real.sqrt u+mobiusDivisorHeadBlockIntercept P n)*
          (mobiusDivisorHeadBlockSlope P (n/p)*Real.sqrt u+
            Real.sqrt p*mobiusDivisorHeadBlockIntercept P (n/p)) := by
      rw [← ha,← hb]
      ring
    rw [he]
    field_simp
    rw [hsq]
    ring

/-- Each already defined discrete block primitive is exactly the physical
prime-correlation integral on that closed quotient block. -/
theorem integral_mobiusDivisorPrimeCorrelationKernel_block (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) {p n : ℕ} (hp : 0<p) (hn : 0<n) :
    (∫u in Ioc (n:ℝ) (n+1:ℕ),mobiusDivisorPrimeCorrelationKernel P p u) =
      mobiusDivisorPrimeCorrelationPrimitive P p n (1/(n:ℝ))-
        mobiusDivisorPrimeCorrelationPrimitive P p n (1/((n:ℝ)+1)) := by
  have hab : (n:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.le_succ n
  have hi : IntegrableOn (mobiusDivisorPrimeCorrelationKernel P p) (Ioc (n:ℝ) (n+1:ℕ)) :=
    (integrable_mobiusDivisorPrimeCorrelationKernel P hp).mono_set (by
      intro u hu
      have hnR : (1:ℝ)≤n := by exact_mod_cast hn
      exact lt_of_le_of_lt hnR hu.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => inverse_primitive_deriv P hP hp
      (by rw [uIcc_of_le hab] at hu; exact lt_of_lt_of_le (by exact_mod_cast hn) hu.1)
      (by simpa only [uIcc_of_le hab] using hu))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hi)
  rw [intervalIntegral.integral_of_le hab] at h
  simpa only [Nat.cast_add,Nat.cast_one,neg_sub_neg] using h

end RHTower
