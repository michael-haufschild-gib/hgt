import GaloisForLFunctions.RHTower.CCMPrimeDeficitFluxBalance
import GaloisForLFunctions.RHTower.CCMPrimeDeficitPairEnergy
import GaloisForLFunctions.RHTower.WeilLagFunctionInteger

/-!
# The outgoing deficit flux is the actual Weil lag

Finite prime-entry integration identifies the constructed outgoing amplitude
with the existing arithmetic Weil lag, plus its explicit archimedean term.
Consequently the flux balance controls integrated critical deficit energy
by the squared actual lag with that correction. No cancellation estimate
for the latter is assumed or proved here.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace RHTower

theorem integral_exp_neg_mul_ccmPrimeEntryPrefix (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) =
      mertensSum ⌊Real.exp T⌋₊ - Real.exp (-T) *
        (ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ T + Chebyshev.psi (Real.exp T)) := by
  let S := Finset.Icc 1 ⌊Real.exp T⌋₊
  let f : ℕ → ℝ → ℝ := fun n t => ArithmeticFunction.vonMangoldt n *
    (Real.exp (-t) * ccmPrimeEntryTent (Real.log n) t)
  have hf (n : ℕ) : IntervalIntegrable (f n) volume 0 T := by
    apply Continuous.intervalIntegrable
    unfold f ccmPrimeEntryTent
    fun_prop
  have hp (t : ℝ) : Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t =
      ∑ n ∈ S, f n t := by
    unfold ccmPrimeEntryPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    ring
  have hpsi : Chebyshev.psi (Real.exp T) =
      ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    simp only [S, Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum (fun n _ => hf n), hpsi]
  unfold mertensSum ccmPrimeEntryPrefix
  change (∑ n ∈ S, ∫ t in (0 : ℝ)..T, f n t) =
    (∑ n ∈ S, ArithmeticFunction.vonMangoldt n / (n : ℝ)) - Real.exp (-T) *
      ((∑ n ∈ S, ArithmeticFunction.vonMangoldt n * ccmPrimeEntryTent (Real.log n) T) +
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n)
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos := zero_lt_one.trans_le hnR
  have hlog := Real.log_nonneg hnR
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)
  dsimp only [f]
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul_ccmPrimeEntryTent hlog hlogT,
    Real.exp_neg, Real.exp_log hnpos, ccmPrimeEntryTent, max_eq_left (sub_nonneg.mpr hlogT)]
  ring

private theorem integral_background (T : ℝ) :
    (∫ t in (0 : ℝ)..T, 1 - Real.exp (-t)) = T - 1 + Real.exp (-T) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => s + Real.exp (-s)) (1 - Real.exp (-t)) t := by
    convert! (hasDerivAt_id t).add (((hasDerivAt_id t).neg).exp) using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  exact h.trans (by simp only [neg_zero, Real.exp_zero]; ring)

/-- Weighted integration of the literal deficit retains both the endpoint
deficit and the endpoint Chebyshev sum. -/
theorem integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) =
      T - mertensSum ⌊Real.exp T⌋₊ + Real.exp (-T) *
        (Chebyshev.psi (Real.exp T) - ccmLogChebyshevDeficitPrimitive T) := by
  have hp (t : ℝ) (ht : t ∈ uIcc 0 T) :
      Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t =
        (1 - Real.exp (-t)) - Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t := by
    have ht' := uIcc_of_le hT ▸ ht
    rw [ccmLogChebyshevDeficitPrimitive_eq_entry_prefix ht'.1
      (Nat.floor_mono (Real.exp_le_exp.mpr ht'.2))]
    have he : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith only [he]
  have hb : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hs : IntervalIntegrable
      (fun t : ℝ => Real.exp (-t) * ccmPrimeEntryPrefix ⌊Real.exp T⌋₊ t) volume 0 T :=
    ((Real.continuous_exp.comp continuous_neg).mul
      (continuous_ccmPrimeEntryPrefix _)).intervalIntegrable 0 T
  rw [intervalIntegral.integral_congr hp, intervalIntegral.integral_sub hb hs,
    integral_background, integral_exp_neg_mul_ccmPrimeEntryPrefix,
    ccmLogChebyshevDeficitPrimitive_eq_entry_prefix hT le_rfl]
  have he : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith only [he]

theorem ccmPrimeDeficitOutgoing_eq_prime_side {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitOutgoing T = Real.exp (-T / 2) *
      ((Real.exp T - Chebyshev.psi (Real.exp T)) +
        Real.exp T * (mertensSum ⌊Real.exp T⌋₊ - T + Real.eulerMascheroniConstant)) := by
  unfold ccmPrimeDeficitOutgoing ccmPrimeDeficitFluxState ccmPrimeDeficitIncoming
  rw [integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive hT]
  have he : Real.exp (T / 2) * Real.exp (-T) = Real.exp (-T / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he' : Real.exp (-T / 2) * Real.exp T = Real.exp (T / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (T / 2) * (Real.eulerMascheroniConstant + 1 - T + mertensSum ⌊Real.exp T⌋₊) -
      (Real.exp (T / 2) * Real.exp (-T)) *
        (Chebyshev.psi (Real.exp T) - ccmLogChebyshevDeficitPrimitive T) -
          Real.exp (-T / 2) * ccmLogChebyshevDeficitPrimitive T := by ring
    _ = _ := by rw [he, ← he']; ring

/-- Exact identification with the existing Weil lag, with the full
archimedean correction retained. -/
theorem ccmPrimeDeficitOutgoing_eq_weilLag {T : ℝ} (hT : 0 < T) :
    ccmPrimeDeficitOutgoing T = weilLagFunctionReal T +
      Real.exp (-T / 2) * (Real.log (2 * Real.pi) - trivialZeroSeriesReal (Real.exp T)) := by
  rw [ccmPrimeDeficitOutgoing_eq_prime_side hT.le, weilLagFunctionReal_eq_prime_side hT]
  ring

end RHTower
