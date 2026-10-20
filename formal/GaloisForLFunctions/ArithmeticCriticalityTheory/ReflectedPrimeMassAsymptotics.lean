import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateInfinityFailure
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateReflectedCollarDefect
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePlateauPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSpanPlateauLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.TranslateGroundStateLorentzLaw
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPNT
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaFarTail
import GaloisForLFunctions.RHTower.RiemannKernelTruncationWeilPositive

/-!
# The reflected prime mass at infinity

For a profile `M` decaying on `[0, ∞)` with `M(0) = 0`, the reflected prime mass at `x` is
`P_M(x) = Σ_{log n > x} Λ(n) n^{−1/2} M(log n − x)`, the prime part of the folded collar. By the
prime number theorem (`tendsto_exp_neg_half_mul_reflectedPrimeMass`)

    e^{−x/2} P_M(x)  →  ∫_0^∞ e^{r/2} M(r) dr        (x → ∞).

Proof. With `G(r) = e^{−r/2} M(r)` and `ψ` Chebyshev's function, Abel summation and the substitution
`t = e^{x+r}` give the exact identity `e^{−x/2} P_M(x) = −∫_0^∞ G'(r) e^{−x} ψ(e^{x+r}) dr`; by the prime
number theorem `e^{−x} ψ(e^{x+r}) → e^r` with domination `2e^r`, and `−∫ G' e^r = ∫ e^{r/2} M`.

For the shifted ground states this is the exact form of the factor two in the collar
(`tendsto_shiftedCollarMass_div_source`): with `κ_a = ∫_0^∞ e^{r/2} m_a(r) dr = sinh(a/2) + ∫_0^∞ e^{−r/2} m_a`,

    C_a(x) / (sinh(a/2) sinh(x/2))  →  R(a) = 2 + 2 ∫_0^∞ e^{−r/2} m_a(r) dr / sinh(a/2)  >  2.

The collar sees the profile through `e^{r/2} = 2 sinh(r/2) + e^{−r/2}`: its sinh moment is twice the
source, and the excess is the moment at the other pole `s = 0`. `R(a) > 2` for every `a > 0`
(`two_lt_collarRatio`), `R(a) → 2` as `a → ∞` (`tendsto_collarRatio_atTop`) and
`R(a) → 1 + 8Φ(0) + 4σ` as `a → 0⁺`, `σ = ∫_0^∞ Φ sinh(u/2)` (`tendsto_collarRatio_nhdsGT_zero`). The folded defect
`2Φ(x)[sinh(a/2) sinh(x/2) − C_a(x)]` is asymptotic to `1 − R(a) < −1` times the source term
(`tendsto_foldedDefect_shiftedGroundState_div_source`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The weight `G(r) = e^{−r/2} M(r)` -/

section Weight

variable {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M)
include hM

/-- `G(r) = e^{−r/2} M(r)`. -/
def halfWeight (M : ℝ → ℝ) (r : ℝ) : ℝ := Real.exp (-r / 2) * M r

/-- `G'(r) = e^{−r/2} (M'(r) − M(r)/2)`. -/
def halfWeightDeriv (M : ℝ → ℝ) (r : ℝ) : ℝ := Real.exp (-r / 2) * (deriv M r - M r / 2)

theorem hasDerivAt_halfWeight (r : ℝ) : HasDerivAt (halfWeight M) (halfWeightDeriv M r) r := by
  have hd : HasDerivAt M (deriv M r) r :=
    (hM.differentiable one_ne_zero r).hasDerivAt
  have he : HasDerivAt (fun r => Real.exp (-r / 2)) (Real.exp (-r / 2) * (-1 / 2)) r := by
    have := ((hasDerivAt_id r).neg.div_const 2).exp
    simpa [neg_div] using this
  have h := he.mul hd
  have e1 : ((fun r => Real.exp (-r / 2)) * M) = halfWeight M := rfl
  rw [e1] at h
  refine h.congr_deriv ?_
  simp only [halfWeightDeriv]
  ring

theorem continuous_halfWeightDeriv : Continuous (halfWeightDeriv M) :=
  (Real.continuous_exp.comp (continuous_neg.div_const 2)).mul
    ((hM.continuous_deriv le_rfl).sub (hM.continuous.div_const 2))

theorem continuous_halfWeight : Continuous (halfWeight M) :=
  (Real.continuous_exp.comp (continuous_neg.div_const 2)).mul hM.continuous

end Weight

section Decay

variable {M : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hdec : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)))
  (hdec' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r)))

include hdec in
theorem abs_halfWeight_le {r : ℝ} (hr : 0 ≤ r) :
    |halfWeight M r| ≤ C * Real.exp (-(5 / 2 * r)) := by
  unfold halfWeight
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-r / 2) * |M r| ≤ Real.exp (-r / 2) * (C * Real.exp (-(2 * r))) :=
        mul_le_mul_of_nonneg_left (hdec r hr) (Real.exp_pos _).le
    _ = C * Real.exp (-(5 / 2 * r)) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf

include hC0 hdec hdec' in
theorem abs_halfWeightDeriv_le {r : ℝ} (hr : 0 ≤ r) :
    |halfWeightDeriv M r| ≤ 2 * C * Real.exp (-(5 / 2 * r)) := by
  unfold halfWeightDeriv
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |deriv M r - M r / 2| ≤ 2 * C * Real.exp (-(2 * r)) := by
    have := abs_sub (deriv M r) (M r / 2)
    rw [abs_div, abs_two] at this
    linarith [hdec r hr, hdec' r hr, Real.exp_pos (-(2 * r)),
      mul_nonneg hC0 (Real.exp_pos (-(2 * r))).le]
  calc Real.exp (-r / 2) * |deriv M r - M r / 2|
      ≤ Real.exp (-r / 2) * (2 * C * Real.exp (-(2 * r))) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 2 * C * Real.exp (-(5 / 2 * r)) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf

include hdec in
theorem abs_exp_half_mul_le {r : ℝ} (hr : 0 ≤ r) :
    |Real.exp (r / 2) * M r| ≤ C * Real.exp (-(3 / 2) * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (r / 2) * |M r| ≤ Real.exp (r / 2) * (C * Real.exp (-(2 * r))) :=
        mul_le_mul_of_nonneg_left (hdec r hr) (Real.exp_pos _).le
    _ = C * Real.exp (-(3 / 2) * r) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf

include hC0 hdec hdec' in
theorem abs_halfWeightDeriv_mul_exp_le {r : ℝ} (hr : 0 ≤ r) :
    |halfWeightDeriv M r * Real.exp r| ≤ 2 * C * Real.exp (-(3 / 2) * r) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |halfWeightDeriv M r| * Real.exp r ≤ (2 * C * Real.exp (-(5 / 2 * r))) * Real.exp r :=
        mul_le_mul_of_nonneg_right (abs_halfWeightDeriv_le hC0 hdec hdec' hr) (Real.exp_pos _).le
    _ = 2 * C * Real.exp (-(3 / 2) * r) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

theorem integrableOn_exp_neg_three_halves :
    IntegrableOn (fun r : ℝ => Real.exp (-(3 / 2) * r)) (Ioi 0) :=
  exp_neg_integrableOn_Ioi 0 (by norm_num)

include hdec in
theorem integrableOn_exp_half_mul (hMc : Continuous M) :
    IntegrableOn (fun r => Real.exp (r / 2) * M r) (Ioi 0) := by
  refine (integrableOn_exp_neg_three_halves.const_mul C).mono'
    (((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hMc).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  rw [Real.norm_eq_abs]
  exact abs_exp_half_mul_le hdec (le_of_lt hr)

include hC0 hdec hdec' in
theorem integrableOn_halfWeightDeriv_mul_exp (hM : ContDiff ℝ 1 M) :
    IntegrableOn (fun r => halfWeightDeriv M r * Real.exp r) (Ioi 0) := by
  refine ((integrableOn_exp_neg_three_halves.const_mul (2 * C))).mono'
    (((continuous_halfWeightDeriv hM).mul Real.continuous_exp).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  rw [Real.norm_eq_abs]
  exact abs_halfWeightDeriv_mul_exp_le hC0 hdec hdec' (le_of_lt hr)

include hC0 hdec hdec' in
/-- `−∫_0^∞ G'(r) e^r dr = ∫_0^∞ e^{r/2} M(r) dr` when `M(0) = 0`. -/
theorem integral_halfWeightDeriv_mul_exp (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) :
    (∫ r in Ioi (0 : ℝ), halfWeightDeriv M r * Real.exp r) =
      -∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * M r := by
  set f : ℝ → ℝ := fun r => Real.exp (r / 2) * M r with hf
  set f' : ℝ → ℝ := fun r => Real.exp (r / 2) * (deriv M r + M r / 2) with hf'
  have hderiv : ∀ r, HasDerivAt f (f' r) r := fun r => by
    have hd : HasDerivAt M (deriv M r) r := (hM.differentiable one_ne_zero r).hasDerivAt
    have he : HasDerivAt (fun r => Real.exp (r / 2)) (Real.exp (r / 2) * (1 / 2)) r := by
      simpa using ((hasDerivAt_id r).div_const 2).exp
    refine (he.mul hd).congr_deriv ?_
    simp only [hf']
    ring
  have hfi : IntegrableOn (fun r => Real.exp (r / 2) * M r) (Ioi 0) :=
    integrableOn_exp_half_mul hdec hM.continuous
  have hGi := integrableOn_halfWeightDeriv_mul_exp hC0 hdec hdec' hM
  have hf'i : IntegrableOn f' (Ioi 0) := by
    refine (hGi.add hfi).congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [hf', halfWeightDeriv, Pi.add_apply]
    have : Real.exp (-r / 2) * Real.exp r = Real.exp (r / 2) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (deriv M r - M r / 2) * this
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => C * Real.exp (-(3 / 2) * r)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 2))).const_mul C
      simpa [Function.comp_def, neg_mul] using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with r hr
    rw [Real.norm_eq_abs]
    exact abs_exp_half_mul_le hdec hr
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hderiv 0).continuousAt.continuousWithinAt) (fun r _ => hderiv r) hf'i hlim
  have hf0 : f 0 = 0 := by simp [hf, hM0]
  rw [hf0, sub_zero] at hFTC
  have e : (fun r => halfWeightDeriv M r * Real.exp r) = fun r => f' r - Real.exp (r / 2) * M r :=
    funext fun r => by
      simp only [hf', halfWeightDeriv]
      have : Real.exp (-r / 2) * Real.exp r = Real.exp (r / 2) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (deriv M r - M r / 2) * this
  rw [e, integral_sub hf'i hfi, hFTC]
  ring

end Decay

/-! ### Chebyshev's function and Abel summation -/

/-- Chebyshev's function `ψ(t) = Σ_{k ≤ t} Λ(k)`. -/
def psiSum (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)

theorem psiSum_nonneg (t : ℝ) : 0 ≤ psiSum t :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

theorem psiSum_le {t : ℝ} (ht : 0 ≤ t) : psiSum t ≤ (t + 1) ^ 2 := by
  unfold psiSum
  have hterm : ∀ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) ≤ t := fun k hk => by
    have hk' : (k : ℝ) ≤ t := (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans (Nat.floor_le ht)
    have h1 := ArithmeticFunction.vonMangoldt_le_log (n := k)
    have h2 : Real.log k ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · exact (Real.log_le_sub_one_of_pos (by exact_mod_cast h)).trans (by linarith)
    linarith
  calc _ ≤ ∑ _k ∈ Finset.Icc 0 ⌊t⌋₊, t := Finset.sum_le_sum hterm
    _ = ((⌊t⌋₊ : ℝ) + 1) * t := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (t + 1) ^ 2 := by nlinarith [Nat.floor_le ht]

theorem measurable_psiSum : Measurable psiSum := by
  have : psiSum = (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, (ArithmeticFunction.vonMangoldt k : ℝ)) ∘
      fun t : ℝ => ⌊t⌋₊ := rfl
  rw [this]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- The prime number theorem: `ψ(y)/y → 1`. -/
theorem tendsto_psiSum_div : Tendsto (fun y => psiSum y / y) atTop (𝓝 1) := by
  refine RHTower.Sieve.tendsto_sum_vonMangoldt_div.congr fun y => ?_
  unfold psiSum
  congr 2
  ext k
  simp

theorem hasDerivAt_halfWeight_log_sub {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (x : ℝ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun t => halfWeight M (Real.log t - x)) (halfWeightDeriv M (Real.log t - x) / t) t := by
  have h := (hasDerivAt_halfWeight hM (Real.log t - x)).comp t
    ((Real.hasDerivAt_log ht.ne').sub_const x)
  refine h.congr_deriv ?_
  field_simp

/-- **Abel summation for the reflected prime sum.** For `x ≥ 0` and `N ≥ e^x`,
`Σ_{e^x < k ≤ N} G(log k − x) Λ(k) = G(log N − x) ψ(N) − ∫_{e^x}^N G'(log t − x) ψ(t) dt/t`. -/
theorem sum_halfWeight_vonMangoldt_eq {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) {x : ℝ}
    {N : ℕ} (hN : Real.exp x ≤ N) :
    ∑ k ∈ Finset.Ioc ⌊Real.exp x⌋₊ N, halfWeight M (Real.log k - x) *
        (ArithmeticFunction.vonMangoldt k : ℝ) =
      halfWeight M (Real.log N - x) * psiSum N -
        ∫ t in Ioc (Real.exp x) N, halfWeightDeriv M (Real.log t - x) / t * psiSum t := by
  have hpos : ∀ t ∈ Icc (Real.exp x) (N : ℝ), 0 < t := fun t ht =>
    lt_of_lt_of_le (Real.exp_pos x) ht.1
  have hcont : ContinuousOn (fun t => halfWeightDeriv M (Real.log t - x) / t) (Icc (Real.exp x) N) :=
    (((continuous_halfWeightDeriv hM).comp_continuousOn
      ((Real.continuousOn_log.mono fun t ht => (hpos t ht).ne').sub continuousOn_const)).div
      continuousOn_id fun t ht => (hpos t ht).ne')
  have hint : IntegrableOn (deriv fun t => halfWeight M (Real.log t - x)) (Icc (Real.exp x) N) := by
    refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_halfWeight_log_sub hM x (hpos t ht)).deriv).symm
  have h := sum_mul_eq_sub_sub_integral_mul (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
    (f := fun t => halfWeight M (Real.log t - x)) (Real.exp_pos x).le hN
    (fun t ht => (hasDerivAt_halfWeight_log_sub hM x (hpos t ht)).differentiableAt) hint
  rw [Nat.floor_natCast] at h
  have hG0 : halfWeight M (Real.log (Real.exp x) - x) = 0 := by
    rw [Real.log_exp, sub_self, halfWeight, hM0, mul_zero]
  have hI : (∫ t in Ioc (Real.exp x) N, deriv (fun t => halfWeight M (Real.log t - x)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ)) =
      ∫ t in Ioc (Real.exp x) N, halfWeightDeriv M (Real.log t - x) / t * psiSum t := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hasDerivAt_halfWeight_log_sub hM x (lt_of_lt_of_le (Real.exp_pos x) ht.1.le)).deriv]
    rfl
  rw [h, hG0, zero_mul, sub_zero, hI]
  unfold psiSum
  rw [Nat.floor_natCast]

/-! ### The reflected sum as an integral against `ψ` -/

/-- The term `Λ(n) G(log n − x)` of the reflected sum, on `log n > x`. -/
def reflectedTerm (M : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) *
    (if x < Real.log n then halfWeight M (Real.log n - x) else 0)

theorem exp_neg_five_halves_log_sub (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(5 / 2 * (Real.log t - x))) = Real.exp (5 / 2 * x) * t ^ (-(5 / 2) : ℝ) := by
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  ring_nf

section Reflected

variable {M : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hdec : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)))
  (hdec' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r)))

include hC0 hdec in
theorem abs_reflectedTerm_le (x : ℝ) (n : ℕ) :
    |reflectedTerm M x n| ≤ C * Real.exp (5 / 2 * x) * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
  unfold reflectedTerm
  split_ifs with h
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, ArithmeticFunction.map_zero, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hn : (0 : ℝ) < n := by exact_mod_cast hpos
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛn : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ n :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_sub_one_of_pos hn).trans (by linarith))
    have hG := abs_halfWeight_le hdec (le_of_lt (sub_pos.mpr h))
    rw [exp_neg_five_halves_log_sub x hn] at hG
    rw [abs_mul, abs_of_nonneg hΛ]
    have hrp : (n : ℝ) * (n : ℝ) ^ (-(5 / 2) : ℝ) = (n : ℝ) ^ (-(3 / 2) : ℝ) := by
      rw [show (n : ℝ) * (n : ℝ) ^ (-(5 / 2) : ℝ) = (n : ℝ) ^ ((1 : ℝ) + (-(5 / 2))) by
        rw [Real.rpow_add hn, Real.rpow_one]]
      norm_num
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * |halfWeight M (Real.log n - x)|
        ≤ (n : ℝ) * (C * (Real.exp (5 / 2 * x) * (n : ℝ) ^ (-(5 / 2) : ℝ))) :=
          mul_le_mul hΛn hG (abs_nonneg _) (Nat.cast_nonneg n)
      _ = C * Real.exp (5 / 2 * x) * ((n : ℝ) * (n : ℝ) ^ (-(5 / 2) : ℝ)) := by ring
      _ = _ := by rw [hrp]
  · rw [mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

include hC0 hdec in
theorem summable_reflectedTerm (x : ℝ) : Summable (reflectedTerm M x) :=
  Summable.of_norm_bounded ((Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left
    (C * Real.exp (5 / 2 * x))) fun n => by
      rw [Real.norm_eq_abs]
      exact abs_reflectedTerm_le hC0 hdec x n

omit hC0 hdec hdec' in
/-- The partial sums of the reflected sum are the Abel sums. -/
theorem sum_range_reflectedTerm_eq {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), reflectedTerm M x n =
      ∑ k ∈ Finset.Ioc ⌊Real.exp x⌋₊ N, halfWeight M (Real.log k - x) *
        (ArithmeticFunction.vonMangoldt k : ℝ) := by
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun k hk => ?_) (fun n hn => ?_) (fun k hk => ?_)
  · rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2
  · obtain ⟨-, hn⟩ := Finset.mem_sdiff.mp hn
    have hle : n ≤ ⌊Real.exp x⌋₊ := by
      by_contra h
      exact hn (Finset.mem_Ioc.mpr ⟨not_le.mp h, by
        have := (Finset.mem_sdiff.mp ‹_›).1
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)⟩)
    unfold reflectedTerm
    rw [if_neg, mul_zero]
    rw [not_lt]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact hx
    · have hn' : (n : ℝ) ≤ Real.exp x :=
        (Nat.cast_le.mpr hle).trans (Nat.floor_le (Real.exp_pos x).le)
      calc Real.log n ≤ Real.log (Real.exp x) :=
            Real.log_le_log (by exact_mod_cast hpos) hn'
        _ = x := Real.log_exp x
  · have hk' := (Finset.mem_Ioc.mp hk).1
    have hgt : Real.exp x < k := by
      have := Nat.lt_floor_add_one (Real.exp x)
      have h2 : ((⌊Real.exp x⌋₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hk'
      linarith
    have hlog : x < Real.log k := by
      rw [← Real.log_exp x]
      exact Real.log_lt_log (Real.exp_pos x) hgt
    unfold reflectedTerm
    rw [if_pos hlog]
    ring

include hC0 hdec hdec' in
theorem integrableOn_halfWeightDeriv_log_mul_psiSum (hM : ContDiff ℝ 1 M) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => halfWeightDeriv M (Real.log t - x) / t * psiSum t)
      (Ioi (Real.exp x)) := by
  have hmaj : IntegrableOn (fun t : ℝ => 8 * C * Real.exp (5 / 2 * x) * t ^ (-(3 / 2) : ℝ))
      (Ioi (Real.exp x)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (Real.exp_pos x)).const_mul _
  refine hmaj.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  · exact ((((continuous_halfWeightDeriv hM).measurable.comp
      (Real.measurable_log.sub_const x)).div measurable_id).mul
      measurable_psiSum).aestronglyMeasurable
  · have ht1 : 1 ≤ t := (Real.one_le_exp hx).trans (le_of_lt ht)
    have ht0 : 0 < t := by linarith
    have hr : 0 ≤ Real.log t - x := by
      rw [sub_nonneg, ← Real.log_exp x]
      exact Real.log_le_log (Real.exp_pos x) (le_of_lt ht)
    have hG := abs_halfWeightDeriv_le hC0 hdec hdec' hr
    rw [exp_neg_five_halves_log_sub x ht0] at hG
    have hψ := psiSum_le ht0.le
    have hψ0 := psiSum_nonneg t
    have h4 : (t + 1) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
    have hrp : t ^ (-(5 / 2) : ℝ) * t ^ 2 / t = t ^ (-(3 / 2) : ℝ) := by
      rw [show (t ^ 2 : ℝ) = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_add ht0,
        div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
      norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos ht0, abs_of_nonneg hψ0]
    calc |halfWeightDeriv M (Real.log t - x)| / t * psiSum t
        ≤ (2 * C * (Real.exp (5 / 2 * x) * t ^ (-(5 / 2) : ℝ))) / t * (4 * t ^ 2) := by
          refine mul_le_mul (div_le_div_of_nonneg_right hG ht0.le) (hψ.trans h4) hψ0 ?_
          exact div_nonneg (by positivity) ht0.le
      _ = 8 * C * Real.exp (5 / 2 * x) * (t ^ (-(5 / 2) : ℝ) * t ^ 2 / t) := by ring
      _ = _ := by rw [hrp]

include hC0 hdec hdec' in
/-- **The reflected sum as an integral against `ψ`.** For `x ≥ 0`,
`Σ_{log n > x} Λ(n) G(log n − x) = −∫_{e^x}^∞ G'(log t − x) ψ(t) dt/t`. -/
theorem tsum_reflectedTerm_eq (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    ∑' n, reflectedTerm M x n =
      -∫ t in Ioi (Real.exp x), halfWeightDeriv M (Real.log t - x) / t * psiSum t := by
  have hgi := integrableOn_halfWeightDeriv_log_mul_psiSum hC0 hdec hdec' hM hx
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), reflectedTerm M x n) atTop
      (𝓝 (∑' n, reflectedTerm M x n)) :=
    ((summable_reflectedTerm hC0 hdec x).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun N : ℕ => halfWeight M (Real.log N - x) * psiSum N) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => 4 * C * Real.exp (5 / 2 * x) * (N : ℝ) ^ (-(1 / 2) : ℝ))
        atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul (4 * C * Real.exp (5 / 2 * x))
      simpa using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop (⌈Real.exp x⌉₊ + 1)] with N hN
    have hNx : Real.exp x < N := by
      have h1 : Real.exp x ≤ ⌈Real.exp x⌉₊ := Nat.le_ceil _
      have h2 : ((⌈Real.exp x⌉₊ : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hN
      linarith
    have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hx).trans hNx.le
    have hN0 : (0 : ℝ) < N := by linarith
    have hr : 0 ≤ Real.log N - x := sub_nonneg.mpr (by
      rw [← Real.log_exp x]
      exact Real.log_le_log (Real.exp_pos x) hNx.le)
    have hG := abs_halfWeight_le hdec hr
    rw [exp_neg_five_halves_log_sub x hN0] at hG
    have hψ := psiSum_le hN0.le
    have h4 : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    have hrp : (N : ℝ) ^ (-(5 / 2) : ℝ) * (N : ℝ) ^ 2 = (N : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [show ((N : ℝ) ^ 2 : ℝ) = (N : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hN0]
      norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psiSum_nonneg _)]
    calc |halfWeight M (Real.log N - x)| * psiSum N
        ≤ (C * (Real.exp (5 / 2 * x) * (N : ℝ) ^ (-(5 / 2) : ℝ))) * (4 * (N : ℝ) ^ 2) :=
          mul_le_mul hG (hψ.trans h4) (psiSum_nonneg _) (by positivity)
      _ = 4 * C * Real.exp (5 / 2 * x) * ((N : ℝ) ^ (-(5 / 2) : ℝ) * (N : ℝ) ^ 2) := by ring
      _ = _ := by rw [hrp]
  have hI : Tendsto (fun N : ℕ => ∫ t in Ioc (Real.exp x) N,
      halfWeightDeriv M (Real.log t - x) / t * psiSum t) atTop
      (𝓝 (∫ t in Ioi (Real.exp x), halfWeightDeriv M (Real.log t - x) / t * psiSum t)) := by
    refine (intervalIntegral_tendsto_integral_Ioi (Real.exp x) hgi
      tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with N hN
    exact intervalIntegral.integral_of_le (Nat.ceil_le.mp hN)
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), reflectedTerm M x n) atTop
      (𝓝 (0 - ∫ t in Ioi (Real.exp x), halfWeightDeriv M (Real.log t - x) / t * psiSum t)) := by
    refine (hB.sub hI).congr' ?_
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with N hN
    rw [sum_range_reflectedTerm_eq hx N, sum_halfWeight_vonMangoldt_eq hM hM0 (Nat.ceil_le.mp hN)]
  rw [tendsto_nhds_unique hS hlim, zero_sub]

omit hC0 hdec hdec' in
/-- The substitution `t = e^{x+r}`. -/
theorem integral_Ioi_exp_halfWeightDeriv_eq (x : ℝ) :
    (∫ t in Ioi (Real.exp x), halfWeightDeriv M (Real.log t - x) / t * psiSum t) =
      ∫ r in Ioi (0 : ℝ), halfWeightDeriv M r * psiSum (Real.exp (x + r)) := by
  have himage : (fun r => Real.exp (x + r)) '' Ioi 0 = Ioi (Real.exp x) := by
    rw [show (fun r => Real.exp (x + r)) = Real.exp ∘ fun r => x + r from rfl, Set.image_comp,
      Set.image_const_add_Ioi, add_zero, Real.image_exp_Ioi]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun r => Real.exp (x + r)) (f' := fun r => Real.exp (x + r)) measurableSet_Ioi
    (fun r _ => by
      have := ((hasDerivAt_id r).const_add x).exp
      simpa using this.hasDerivWithinAt)
    ((Real.exp_injective.comp (add_right_injective x)).injOn)
    (fun t => halfWeightDeriv M (Real.log t - x) / t * psiSum t)
  rw [himage] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [smul_eq_mul, Real.log_exp, abs_of_pos (Real.exp_pos _)]
  rw [show x + r - x = r by ring]
  field_simp

include hC0 hdec hdec' in
/-- **The limit.** `e^{−x} Σ_{log n > x} Λ(n) G(log n − x) → ∫_0^∞ e^{r/2} M(r) dr`. -/
theorem tendsto_exp_neg_mul_tsum_reflectedTerm (hM : ContDiff ℝ 1 M) (hM0 : M 0 = 0) :
    Tendsto (fun x => Real.exp (-x) * ∑' n, reflectedTerm M x n) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * M r)) := by
  have hrep : (fun x => -∫ r in Ioi (0 : ℝ), halfWeightDeriv M r *
      (Real.exp (-x) * psiSum (Real.exp (x + r)))) =ᶠ[atTop]
      fun x => Real.exp (-x) * ∑' n, reflectedTerm M x n := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [tsum_reflectedTerm_eq hC0 hdec hdec' hM hM0 hx, integral_Ioi_exp_halfWeightDeriv_eq,
      mul_neg, ← integral_const_mul]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun r => by simp only; ring)
  obtain ⟨Y, hY⟩ : ∃ Y, ∀ y ≥ Y, psiSum y / y ≤ 2 :=
    eventually_atTop.mp (tendsto_psiSum_div.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  have hDCT : Tendsto (fun x => ∫ r in Ioi (0 : ℝ), halfWeightDeriv M r *
      (Real.exp (-x) * psiSum (Real.exp (x + r)))) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), halfWeightDeriv M r * Real.exp r)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => 4 * C * Real.exp (-(3 / 2) * r)) ?_ ?_
      (integrableOn_exp_neg_three_halves.const_mul _) ?_
    · exact Eventually.of_forall fun x => ((continuous_halfWeightDeriv hM).measurable.mul
        (measurable_const.mul (measurable_psiSum.comp (Real.measurable_exp.comp
          (measurable_const.add measurable_id))))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (max 0 (Real.log (max Y 1)))] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
      have hr0 : 0 ≤ r := le_of_lt hr
      have hy : Y ≤ Real.exp (x + r) := by
        have h1 : Real.log (max Y 1) ≤ x + r := by linarith [le_max_right 0 (Real.log (max Y 1))]
        have h2 := Real.exp_le_exp.mpr h1
        rw [Real.exp_log (by positivity)] at h2
        exact (le_max_left Y 1).trans h2
      have hψ := hY _ hy
      rw [div_le_iff₀ (Real.exp_pos _)] at hψ
      have hψ0 := psiSum_nonneg (Real.exp (x + r))
      have hb := abs_halfWeightDeriv_mul_exp_le hC0 hdec hdec' hr0
      have hfac : Real.exp (-x) * psiSum (Real.exp (x + r)) ≤ 2 * Real.exp r := by
        have : Real.exp (-x) * Real.exp (x + r) = Real.exp r := by rw [← Real.exp_add]; ring_nf
        nlinarith [Real.exp_pos (-x)]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hψ0)]
      calc |halfWeightDeriv M r| * (Real.exp (-x) * psiSum (Real.exp (x + r)))
          ≤ |halfWeightDeriv M r| * (2 * Real.exp r) :=
            mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
        _ = 2 * |halfWeightDeriv M r * Real.exp r| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos r)]; ring
        _ ≤ 2 * (2 * C * Real.exp (-(3 / 2) * r)) := by linarith
        _ = 4 * C * Real.exp (-(3 / 2) * r) := by ring
    · refine Eventually.of_forall fun r => ?_
      have h1 : Tendsto (fun x => psiSum (Real.exp (x + r)) / Real.exp (x + r)) atTop (𝓝 1) :=
        tendsto_psiSum_div.comp (Real.tendsto_exp_atTop.comp
          (tendsto_id.atTop_add (tendsto_const_nhds (x := r))))
      have h2 : Tendsto (fun x => halfWeightDeriv M r *
          (psiSum (Real.exp (x + r)) / Real.exp (x + r) * Real.exp r)) atTop
          (𝓝 (halfWeightDeriv M r * (1 * Real.exp r))) :=
        (h1.mul_const _).const_mul _
      rw [one_mul] at h2
      refine h2.congr fun x => ?_
      have : Real.exp (x + r) = Real.exp x * Real.exp r := Real.exp_add x r
      rw [this, Real.exp_neg]
      field_simp
  have hval := integral_halfWeightDeriv_mul_exp hC0 hdec hdec' hM hM0
  have h := hDCT.neg.congr' hrep
  rwa [hval, neg_neg] at h

end Reflected


/-! ### The reflected prime mass -/

/-- **The reflected prime mass at infinity.** For `M ∈ C¹` with `M(0) = 0` and
`|M|, |M'| ≤ C e^{−2r}` on `[0, ∞)`,
`e^{−x/2} Σ_{log n > x} Λ(n) n^{−1/2} M(log n − x) → ∫_0^∞ e^{r/2} M(r) dr`. -/
theorem tendsto_exp_neg_half_mul_reflectedPrimeMass {M : ℝ → ℝ} (hM : ContDiff ℝ 1 M)
    (hM0 : M 0 = 0) {C : ℝ} (hC0 : 0 ≤ C) (hdec : ∀ r, 0 ≤ r → |M r| ≤ C * Real.exp (-(2 * r)))
    (hdec' : ∀ r, 0 ≤ r → |deriv M r| ≤ C * Real.exp (-(2 * r))) :
    Tendsto (fun x => Real.exp (-x / 2) * ∑' n : ℕ, vonMangoldtAtom n *
        (if x < Real.log n then M (Real.log n - x) else 0)) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * M r)) := by
  refine (tendsto_exp_neg_mul_tsum_reflectedTerm hC0 hdec hdec' hM hM0).congr fun x => ?_
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold reflectedTerm vonMangoldtAtom
  by_cases hlog : x < Real.log n
  · rw [if_pos hlog, if_pos hlog]
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2]
      have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n = Real.exp (Real.log n / 2) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
        ring_nf
      rw [hsq, halfWeight]
      have e1 : Real.exp (-x / 2) = Real.exp (-x) * Real.exp (x / 2) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (-(Real.log n - x) / 2) =
          Real.exp (x / 2) / Real.exp (Real.log n / 2) := by
        rw [← Real.exp_sub]; ring_nf
      rw [e1, e2]
      field_simp
    · rw [if_neg h2]
      have hn2 : n < 2 := by omega
      have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
        interval_cases n <;> simp
      rw [hΛ]
      simp
  · rw [if_neg hlog, if_neg hlog]
    simp

/-! ### The kernel and the shifted ground states -/

theorem hasDerivAt_riemannKernelReal (u : ℝ) :
    HasDerivAt riemannKernelReal (riemannKernelDeriv 1 u).re u := by
  have h := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_riemannKernelDeriv 0 u))
  have e : (⇑Complex.reCLM ∘ riemannKernelDeriv 0) = riemannKernelReal := by
    funext v
    simp only [Function.comp_apply, riemannKernelDeriv_zero_eq_ofReal]
    simp
  rw [e] at h
  simpa using h

theorem exp_mul_exp_neg_pi_exp_le_exp_neg {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (13 / 2 * v) * Real.exp (-Real.pi * Real.exp (2 * v)) ≤ Real.exp (-(2 * v)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 1 + v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have h2 : (1 + v) ^ 2 ≤ Real.exp (2 * v) := by
    rw [show 2 * v = v + v by ring, Real.exp_add]
    nlinarith
  have hπ := Real.pi_gt_three
  have h3 : 3 * (1 + v) ^ 2 ≤ Real.pi * Real.exp (2 * v) :=
    mul_le_mul hπ.le h2 (sq_nonneg _) Real.pi_pos.le
  nlinarith [sq_nonneg (v - 5 / 12)]

/-- `|Φ'(u)| ≤ C e^{−2|u|}`. -/
theorem exists_abs_deriv_riemannKernelReal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, |deriv riemannKernelReal u| ≤ C * Real.exp (-(2 * |u|)) := by
  refine ⟨cuspDecayConst (riemannKernelPoly 1), cuspDecayConst_nonneg _, fun u => ?_⟩
  rw [(hasDerivAt_riemannKernelReal u).deriv]
  refine (Complex.abs_re_le_norm _).trans ((norm_riemannKernelDeriv_le 1 u).trans ?_)
  have hC := cuspDecayConst_nonneg (riemannKernelPoly 1)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have h := exp_mul_exp_neg_pi_exp_le_exp_neg (abs_nonneg u)
  have e : (2 * ((1 : ℕ) : ℝ) + 9 / 2) = 13 / 2 := by norm_num
  rw [e]
  exact h

theorem hasDerivAt_shiftDifference (a y : ℝ) :
    HasDerivAt (shiftDifference a) (deriv riemannKernelReal (y - a) -
      deriv riemannKernelReal (y + a)) y := by
  have h1 := ((hasDerivAt_riemannKernelReal (y - a)).comp y ((hasDerivAt_id y).sub_const a))
  have h2 := ((hasDerivAt_riemannKernelReal (y + a)).comp y ((hasDerivAt_id y).add_const a))
  rw [(hasDerivAt_riemannKernelReal (y - a)).deriv, (hasDerivAt_riemannKernelReal (y + a)).deriv]
  have e : shiftDifference a = (fun x => riemannKernelReal (x - a)) - fun x => riemannKernelReal (x + a) :=
    funext fun x => rfl
  rw [e]
  simpa [Function.comp_def] using h1.sub h2

/-- Decay of the shifted ground state and its derivative on the half line. -/
theorem exists_shiftDifference_decay {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ r, 0 ≤ r → |shiftDifference a r| ≤ C * Real.exp (-(2 * r))) ∧
      ∀ r, 0 ≤ r → |deriv (shiftDifference a) r| ≤ C * Real.exp (-(2 * r)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨C₁, hC₁, hD⟩ := exists_abs_deriv_riemannKernelReal_le
  refine ⟨(C₀ + C₁) * (Real.exp (24 * a) + 1), by positivity, fun r hr => ?_, fun r hr => ?_⟩
  · have h1 := hC (r - a)
    have h2 := hC (r + a)
    have hp1 := riemannKernelReal_pos (r - a)
    have hp2 := riemannKernelReal_pos (r + a)
    have e1 : Real.exp (-(24 * |r - a|)) ≤ Real.exp (24 * a) * Real.exp (-(2 * r)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        have := abs_sub_abs_le_abs_sub r a
        rw [abs_of_nonneg hr, abs_of_nonneg ha] at this
        nlinarith [abs_nonneg (r - a)])
    have e2 : Real.exp (-(24 * |r + a|)) ≤ Real.exp (-(2 * r)) :=
      Real.exp_le_exp.mpr (by rw [abs_of_nonneg (by linarith)]; linarith)
    unfold shiftDifference
    have hE := Real.exp_pos (-(2 * r))
    calc |riemannKernelReal (r - a) - riemannKernelReal (r + a)|
        ≤ riemannKernelReal (r - a) + riemannKernelReal (r + a) := by
          rw [abs_le]; constructor <;> linarith
      _ ≤ C₀ * (Real.exp (24 * a) * Real.exp (-(2 * r))) + C₀ * Real.exp (-(2 * r)) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left e1 hC₀))
            (h2.trans (mul_le_mul_of_nonneg_left e2 hC₀))
      _ ≤ (C₀ + C₁) * (Real.exp (24 * a) + 1) * Real.exp (-(2 * r)) := by
          nlinarith [Real.exp_pos (24 * a), mul_nonneg hC₁ hE.le,
            mul_nonneg (mul_nonneg hC₁ (Real.exp_pos (24 * a)).le) hE.le]
  · rw [(hasDerivAt_shiftDifference a r).deriv]
    have h1 := hD (r - a)
    have h2 := hD (r + a)
    have e1 : Real.exp (-(2 * |r - a|)) ≤ Real.exp (24 * a) * Real.exp (-(2 * r)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        have := abs_sub_abs_le_abs_sub r a
        rw [abs_of_nonneg hr, abs_of_nonneg ha] at this
        nlinarith [abs_nonneg (r - a)])
    have e2 : Real.exp (-(2 * |r + a|)) ≤ Real.exp (-(2 * r)) :=
      Real.exp_le_exp.mpr (by rw [abs_of_nonneg (by linarith)]; linarith)
    have hE := Real.exp_pos (-(2 * r))
    calc |deriv riemannKernelReal (r - a) - deriv riemannKernelReal (r + a)|
        ≤ |deriv riemannKernelReal (r - a)| + |deriv riemannKernelReal (r + a)| := abs_sub _ _
      _ ≤ C₁ * (Real.exp (24 * a) * Real.exp (-(2 * r))) + C₁ * Real.exp (-(2 * r)) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left e1 hC₁))
            (h2.trans (mul_le_mul_of_nonneg_left e2 hC₁))
      _ ≤ (C₀ + C₁) * (Real.exp (24 * a) + 1) * Real.exp (-(2 * r)) := by
          nlinarith [Real.exp_pos (24 * a), mul_nonneg hC₀ hE.le,
            mul_nonneg (mul_nonneg hC₀ (Real.exp_pos (24 * a)).le) hE.le]

/-! ### The collar of the shifted ground states -/

theorem shiftDifference_zero (a : ℝ) : shiftDifference a 0 = 0 := by
  unfold shiftDifference
  rw [zero_sub, zero_add, riemannKernelReal_neg', sub_self]

theorem max_shiftDifference_eq_ite {a : ℝ} (ha : 0 < a) (y : ℝ) :
    max (shiftDifference a y) 0 = if 0 < y then shiftDifference a y else 0 := by
  split_ifs with hy
  · exact max_eq_left (shiftDifference_nonneg_of_nonneg ha.le hy.le)
  · refine max_eq_right ?_
    have h := shiftDifference_nonneg_of_nonneg ha.le (show 0 ≤ -y by linarith [not_lt.mp hy])
    rw [shiftDifference_neg] at h
    linarith

/-- The archimedean part of the collar is bounded: `0 ≤ ∫ ω(t) m_a(t − x)⁺ ≤ ω(x) ∫ Φ`. -/
theorem archCollar_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 ≤ (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) ∧
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) ≤
        archLevyDensity x * ∫ y, riemannKernelReal y := by
  have hint := integrableOn_archLevy_max_shiftDifference ha hx
  have hmaj : IntegrableOn (fun t => archLevyDensity x * riemannKernelReal (t - (x + a))) (Ioi 0) :=
    ((integrable_riemannKernelReal.comp_sub_right (x + a)).const_mul _).integrableOn
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _), ?_⟩
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0)
      ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity x * riemannKernelReal (t - (x + a)) := by
        refine setIntegral_mono_on hint hmaj measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        rw [max_shiftDifference_eq_ite ha]
        split_ifs with htx
        · have hle : archLevyDensity t ≤ archLevyDensity x :=
            strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hx) (mem_Ioi.mpr ht0) (by linarith)
          have hk := shiftDifference_le_kernel a (t - x)
          rw [show t - x - a = t - (x + a) by ring] at hk
          exact mul_le_mul hle hk (shiftDifference_nonneg_of_nonneg ha.le htx.le)
            (archLevyDensity_pos hx).le
        · rw [mul_zero]
          exact mul_nonneg (archLevyDensity_pos hx).le (riemannKernelReal_pos _).le
    _ ≤ archLevyDensity x * ∫ y, riemannKernelReal y := by
        rw [integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (archLevyDensity_pos hx).le
        calc (∫ t in Ioi (0 : ℝ), riemannKernelReal (t - (x + a)))
            ≤ ∫ t, riemannKernelReal (t - (x + a)) :=
              setIntegral_le_integral (integrable_riemannKernelReal.comp_sub_right (x + a))
                (Eventually.of_forall fun t => (riemannKernelReal_pos _).le)
          _ = ∫ y, riemannKernelReal y := integral_sub_right_eq_self _ _

/-- **The collar at infinity.** `e^{−x/2} C_a(x) → κ_a = ∫_0^∞ e^{r/2} m_a(r) dr`. -/
theorem tendsto_exp_neg_half_mul_shiftedCollarMass {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => Real.exp (-x / 2) * shiftedCollarMass a x) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * shiftDifference a r)) := by
  obtain ⟨C, hC0, hdec, hdec'⟩ := exists_shiftDifference_decay ha.le
  have hprime := tendsto_exp_neg_half_mul_reflectedPrimeMass (contDiff_shiftDifference a)
    (shiftDifference_zero a) hC0 hdec hdec'
  have harch : Tendsto (fun x => Real.exp (-x / 2) *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => Real.exp (-x / 2) * (archLevyDensity 1 *
        ∫ y, riemannKernelReal y)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).mul_const
        (archLevyDensity 1 * ∫ y, riemannKernelReal y)
      simpa [Function.comp_def, neg_div] using this
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg (Real.exp_pos _).le (archCollar_le ha hx).1
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hb := (archCollar_le ha (by linarith)).2
      have hω : archLevyDensity x ≤ archLevyDensity 1 :=
        strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr one_pos) (mem_Ioi.mpr (by linarith)) hx
      have hI : 0 ≤ ∫ y, riemannKernelReal y :=
        integral_nonneg fun y => (riemannKernelReal_pos y).le
      refine mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right hω hI
  have hsum := harch.add hprime
  rw [zero_add] at hsum
  refine hsum.congr fun x => ?_
  unfold shiftedCollarMass
  rw [mul_add]
  congr 2
  refine tsum_congr fun n => ?_
  rw [max_shiftDifference_eq_ite ha]
  by_cases h : x < Real.log n
  · rw [if_pos h, if_pos (sub_pos.mpr h)]
  · rw [if_neg h, if_neg (by rwa [sub_pos])]

/-- **The collar-to-source ratio at infinity** (README 3.4, made exact by the prime number theorem):
`C_a(x) / (sinh(a/2) sinh(x/2)) → R(a) = 2 + 2 ∫_0^∞ e^{−r/2} m_a(r) dr / sinh(a/2)`. -/
theorem tendsto_shiftedCollarMass_div_source {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => shiftedCollarMass a x / (Real.sinh (a / 2) * Real.sinh (x / 2))) atTop
      (𝓝 (2 + 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
        Real.sinh (a / 2))) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hκ := tendsto_exp_neg_half_mul_shiftedCollarMass ha
  have hsh : Tendsto (fun x : ℝ => Real.exp (-x / 2) * Real.sinh (x / 2)) atTop (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun x : ℝ => (1 - Real.exp (-x)) / 2) atTop (𝓝 ((1 - 0) / 2)) :=
      ((tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero).div_const 2)
    rw [sub_zero] at h1
    refine h1.congr fun x => ?_
    rw [Real.sinh_eq]
    have e1 : Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have e2 : Real.exp (-x / 2) * Real.exp (-(x / 2)) = Real.exp (-x) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (-1 / 2) * e1 + (1 / 2) * e2
  have hlim := hκ.div (hsh.const_mul (Real.sinh (a / 2)))
    (by positivity : Real.sinh (a / 2) * (1 / 2) ≠ 0)
  -- the value: κ_a = sinh(a/2) + ∫ e^{−r/2} m_a
  have hmi : IntegrableOn (fun r => shiftDifference a r * Real.sinh (r / 2)) (Ioi 0) :=
    (integrable_shiftDifference_mul_sinh_half a).integrableOn
  have hei : IntegrableOn (fun r => Real.exp (-r / 2) * shiftDifference a r) (Ioi 0) := by
    have hm : Integrable (shiftDifference a) :=
      (integrable_riemannKernelReal.comp_sub_right a).sub (integrable_riemannKernelReal.comp_add_right a)
    refine (hm.norm.integrableOn).mono' ((Real.continuous_exp.comp (continuous_neg.div_const 2)).mul
      (continuous_shiftDifference a)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    have : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hr])
    nlinarith [abs_nonneg (shiftDifference a r)]
  have hval : (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * shiftDifference a r) =
      Real.sinh (a / 2) + ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r := by
    have e : (fun r => Real.exp (r / 2) * shiftDifference a r) =
        fun r => 2 * (shiftDifference a r * Real.sinh (r / 2)) +
          Real.exp (-r / 2) * shiftDifference a r := funext fun r => by
      rw [Real.sinh_eq, neg_div]; ring
    rw [e, integral_add (hmi.const_mul 2) hei, integral_const_mul,
      integral_Ioi_shiftDifference_mul_sinh_half]
    ring
  rw [hval] at hlim
  have hfin : (Real.sinh (a / 2) + ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
      (Real.sinh (a / 2) * (1 / 2)) = 2 + 2 * (∫ r in Ioi (0 : ℝ),
        Real.exp (-r / 2) * shiftDifference a r) / Real.sinh (a / 2) := by
    field_simp
  rw [hfin] at hlim
  refine hlim.congr fun x => ?_
  have he : Real.exp (-x / 2) ≠ 0 := (Real.exp_pos _).ne'
  show Real.exp (-x / 2) * shiftedCollarMass a x /
      (Real.sinh (a / 2) * (Real.exp (-x / 2) * Real.sinh (x / 2))) = _
  rw [show Real.sinh (a / 2) * (Real.exp (-x / 2) * Real.sinh (x / 2)) =
    Real.exp (-x / 2) * (Real.sinh (a / 2) * Real.sinh (x / 2)) by ring, mul_div_mul_left _ _ he]

/-- The excess `∫_0^∞ e^{−r/2} m_a(r) dr` is positive: the collar exceeds twice the source. -/
theorem integral_exp_neg_half_mul_shiftDifference_pos {a : ℝ} (ha : 0 < a) :
    0 < ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r := by
  have hc : Continuous fun r => Real.exp (-r / 2) * shiftDifference a r :=
    (Real.continuous_exp.comp (continuous_neg.div_const 2)).mul (continuous_shiftDifference a)
  have hm : Integrable (shiftDifference a) :=
    (integrable_riemannKernelReal.comp_sub_right a).sub (integrable_riemannKernelReal.comp_add_right a)
  have hi : IntegrableOn (fun r => Real.exp (-r / 2) * shiftDifference a r) (Ioi 0) := by
    refine (hm.norm.integrableOn).mono' hc.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    have : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hr])
    nlinarith [abs_nonneg (shiftDifference a r)]
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi
    fun r hr => mul_nonneg (Real.exp_pos _).le
      (shiftDifference_nonneg_of_nonneg ha.le (le_of_lt hr))) hi]
  have hopen : IsOpen (Function.support (fun r => Real.exp (-r / 2) * shiftDifference a r) ∩ Ioi 0) :=
    (isOpen_ne_fun hc continuous_const).inter isOpen_Ioi
  exact hopen.measure_pos volume ⟨1, (mul_pos (Real.exp_pos _)
    (shiftDifference_pos ha one_pos)).ne', mem_Ioi.mpr one_pos⟩

/-- **The collar is more than twice the source at infinity:** `R(a) > 2`. -/
theorem two_lt_collarRatio {a : ℝ} (ha : 0 < a) :
    2 < 2 + 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) / Real.sinh (a / 2) := by
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have := integral_exp_neg_half_mul_shiftDifference_pos ha
  have : 0 < 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) / Real.sinh (a / 2) :=
    div_pos (by linarith) hs
  linarith

/-- **`R(a) → 2` as `a → ∞`:** the excess is bounded by `∫ Φ` while the source grows. -/
theorem tendsto_collarRatio_atTop :
    Tendsto (fun a => 2 + 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
      Real.sinh (a / 2)) atTop (𝓝 2) := by
  set I := ∫ y, riemannKernelReal y
  have hbound : ∀ a, 0 < a → |(∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r)| ≤
      2 * I := fun a ha => by
    have hm : Integrable (shiftDifference a) :=
      (integrable_riemannKernelReal.comp_sub_right a).sub
        (integrable_riemannKernelReal.comp_add_right a)
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc (∫ r in Ioi (0 : ℝ), ‖Real.exp (-r / 2) * shiftDifference a r‖)
        ≤ ∫ r in Ioi (0 : ℝ), (riemannKernelReal (r - a) + riemannKernelReal (r + a)) := by
          refine setIntegral_mono_on ?_ (((integrable_riemannKernelReal.comp_sub_right a).add
            (integrable_riemannKernelReal.comp_add_right a)).integrableOn) measurableSet_Ioi
            fun r hr => ?_
          · refine (hm.norm.integrableOn).mono' (((Real.continuous_exp.comp
              (continuous_neg.div_const 2)).mul (continuous_shiftDifference a)).norm.aestronglyMeasurable)
              (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
            rw [norm_norm, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
            have : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hr])
            nlinarith [norm_nonneg (shiftDifference a r)]
          · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
            have : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hr])
            have h1 := riemannKernelReal_pos (r - a)
            have h2 := riemannKernelReal_pos (r + a)
            have habs : |shiftDifference a r| ≤ riemannKernelReal (r - a) + riemannKernelReal (r + a) := by
              unfold shiftDifference; rw [abs_le]; constructor <;> linarith
            nlinarith [abs_nonneg (shiftDifference a r)]
      _ ≤ ∫ r, (riemannKernelReal (r - a) + riemannKernelReal (r + a)) :=
          setIntegral_le_integral ((integrable_riemannKernelReal.comp_sub_right a).add
            (integrable_riemannKernelReal.comp_add_right a))
            (Eventually.of_forall fun r => by
              have h1 := riemannKernelReal_pos (r - a)
              have h2 := riemannKernelReal_pos (r + a)
              show (0 : ℝ) ≤ riemannKernelReal (r - a) + riemannKernelReal (r + a)
              linarith)
      _ = 2 * I := by
          rw [integral_add (integrable_riemannKernelReal.comp_sub_right a)
            (integrable_riemannKernelReal.comp_add_right a), integral_sub_right_eq_self,
            integral_add_right_eq_self]
          ring
  have hsinh : Tendsto (fun a : ℝ => Real.sinh (a / 2)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [eventually_ge_atTop 0] with a ha
    exact Real.self_le_sinh_iff.mpr (by simp only [id]; linarith)
  have h0 : Tendsto (fun a => 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
      Real.sinh (a / 2)) atTop (𝓝 0) := by
    have hinv := hsinh.inv_tendsto_atTop
    have hb : Tendsto (fun a => 2 * (2 * I) * (Real.sinh (a / 2))⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul (2 * (2 * I))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_two, abs_of_pos hs, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith [hbound a ha]) (inv_nonneg.mpr hs.le)
  simpa using h0.const_add 2

/-- **The folded defect at infinity.** `(𝓛_N ω_a − Φ cosh(x/2) ω_a)/(2Φ(x) sinh(a/2) sinh(x/2))
→ 1 − R(a) < −1`: the shifted ground state is a folded subsolution by more than its own source. -/
theorem tendsto_foldedDefect_shiftedGroundState_div_source {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => (foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x) /
        (2 * riemannKernelReal x * (Real.sinh (a / 2) * Real.sinh (x / 2)))) atTop
      (𝓝 (1 - (2 + 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
        Real.sinh (a / 2)))) := by
  refine ((tendsto_shiftedCollarMass_div_source ha).const_sub 1).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : 0 < Real.sinh (a / 2) * Real.sinh (x / 2) :=
    mul_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.sinh_pos_iff.mpr (by linarith))
  have hΦ := riemannKernelReal_pos x
  rw [foldedGenerator_shiftedGroundState_sub_potential ha hx]
  field_simp

/-! ### Small shifts: `R(a) → 1 + 8Φ(0) + 4σ` -/

/-- The half-line sinh moment `σ = ∫_0^∞ Φ(u) sinh(u/2) du`. -/
def halfSinhMoment : ℝ := ∫ u in Ioi (0 : ℝ), riemannKernelReal u * Real.sinh (u / 2)

theorem integrable_riemannKernelReal_mul_cosh_half :
    Integrable fun x => riemannKernelReal x * Real.cosh (x / 2) := by
  simpa using integrable_riemannKernelReal_sub_mul_cosh_half 0

theorem integrable_riemannKernelReal_mul_sinh_half :
    Integrable fun x => riemannKernelReal x * Real.sinh (x / 2) := by
  simpa using integrable_riemannKernelReal_sub_mul_sinh_half 0

/-- `∫_0^∞ e^{−u/2} Φ(u) du = 1/4 − σ`. -/
theorem integral_Ioi_exp_neg_half_mul_riemannKernelReal :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u / 2) * riemannKernelReal u) = 1 / 4 - halfSinhMoment := by
  have hc : (∫ u in Ioi (0 : ℝ), riemannKernelReal u * Real.cosh (u / 2)) = 1 / 4 := by
    rw [integral_Ioi_eq_half_of_even integrable_riemannKernelReal_mul_cosh_half (fun x => by
      rw [riemannKernelReal_neg', show -x / 2 = -(x / 2) by ring, Real.cosh_neg])]
    have h := integral_riemannKernelReal_sub_mul_cosh_half 0
    simp only [sub_zero, zero_div, Real.cosh_zero] at h
    rw [h]
    norm_num
  have e : (fun u => Real.exp (-u / 2) * riemannKernelReal u) =
      fun u => riemannKernelReal u * Real.cosh (u / 2) - riemannKernelReal u * Real.sinh (u / 2) :=
    funext fun u => by rw [Real.cosh_eq, Real.sinh_eq, neg_div]; ring
  rw [e, integral_sub integrable_riemannKernelReal_mul_cosh_half.integrableOn
    integrable_riemannKernelReal_mul_sinh_half.integrableOn, hc]
  rfl

/-- Integration by parts: `∫_0^∞ e^{−u/2} (−Φ'(u)) du = Φ(0) − ½ ∫_0^∞ e^{−u/2} Φ(u) du`. -/
theorem integral_Ioi_exp_neg_half_mul_neg_deriv :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u / 2) * -deriv riemannKernelReal u) =
      riemannKernelReal 0 - 1 / 2 * ∫ u in Ioi (0 : ℝ), Real.exp (-u / 2) * riemannKernelReal u := by
  obtain ⟨C₁, hC₁, hD⟩ := exists_abs_deriv_riemannKernelReal_le
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  set f : ℝ → ℝ := fun u => Real.exp (-u / 2) * riemannKernelReal u with hf
  set f' : ℝ → ℝ := fun u => Real.exp (-u / 2) * (deriv riemannKernelReal u - riemannKernelReal u / 2)
    with hf'
  have hderiv : ∀ u, HasDerivAt f (f' u) u := fun u => by
    have he : HasDerivAt (fun u => Real.exp (-u / 2)) (Real.exp (-u / 2) * (-1 / 2)) u := by
      have := ((hasDerivAt_id u).neg.div_const 2).exp
      simpa [neg_div] using this
    have hΦ := hasDerivAt_riemannKernelReal u
    rw [← hΦ.deriv] at hΦ
    refine (he.mul hΦ).congr_deriv ?_
    simp only [hf']
    ring
  have hΦi : IntegrableOn (fun u => Real.exp (-u / 2) * riemannKernelReal u) (Ioi 0) := by
    refine integrable_riemannKernelReal.integrableOn.mono' ((Real.continuous_exp.comp
      (continuous_neg.div_const 2)).mul continuous_riemannKernelReal).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (riemannKernelReal_pos _)]
    have : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hu])
    nlinarith [riemannKernelReal_pos u]
  have hdc : Continuous (deriv riemannKernelReal) := contDiff_riemannKernelReal.continuous_deriv le_rfl
  have hDi : IntegrableOn (fun u => Real.exp (-u / 2) * deriv riemannKernelReal u) (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 2)).const_mul C₁).mono'
      ((Real.continuous_exp.comp (continuous_neg.div_const 2)).mul hdc).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := hD u
    rw [abs_of_nonneg hu0] at h1
    have : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-u / 2) * |deriv riemannKernelReal u| ≤ 1 * (C₁ * Real.exp (-(2 * u))) :=
          mul_le_mul this h1 (abs_nonneg _) zero_le_one
      _ = C₁ * Real.exp (-2 * u) := by ring_nf
  have hf'i : IntegrableOn f' (Ioi 0) := by
    refine (hDi.sub (hΦi.const_mul (1 / 2))).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [hf', Pi.sub_apply]
    ring
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h0 : Tendsto (fun u : ℝ => C₀ * Real.exp (-(24 * u))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 24))).const_mul C₀
      simpa [Function.comp_def, neg_mul] using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (riemannKernelReal_pos _)]
    have h1 := hC u
    rw [abs_of_nonneg hu] at h1
    have : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [riemannKernelReal_pos u, Real.exp_pos (-(24 * u))]
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto ((hderiv 0).continuousAt.continuousWithinAt)
    (fun u _ => hderiv u) hf'i hlim
  have hf0 : f 0 = riemannKernelReal 0 := by simp [hf]
  rw [hf0] at hFTC
  have e : (fun u => Real.exp (-u / 2) * -deriv riemannKernelReal u) =
      fun u => -f' u - (1 / 2) * (Real.exp (-u / 2) * riemannKernelReal u) := funext fun u => by
    simp only [hf']; ring
  have i1 : IntegrableOn (fun u => -f' u) (Ioi 0) := hf'i.neg
  have i2 : IntegrableOn (fun u => (1 / 2 : ℝ) * (Real.exp (-u / 2) * riemannKernelReal u)) (Ioi 0) :=
    hΦi.const_mul _
  rw [e, integral_sub i1 i2, integral_neg, hFTC, integral_const_mul]
  ring

/-- `m_a/a → −2Φ'` with domination `|e^{−r/2} m_a(r)/a| ≤ 2C₁e² e^{−2r}` for `0 < a ≤ 1`. -/
theorem tendsto_integral_exp_neg_half_mul_shiftDifference_div :
    Tendsto (fun a => (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) / a)
      (𝓝[>] 0) (𝓝 (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * (-2 * deriv riemannKernelReal r))) := by
  obtain ⟨C₁, hC₁, hD⟩ := exists_abs_deriv_riemannKernelReal_le
  have hdiff : ∀ y, DifferentiableAt ℝ riemannKernelReal y := fun y =>
    (hasDerivAt_riemannKernelReal y).differentiableAt
  -- the mean value bound
  have hmvt : ∀ a r, 0 < a → a ≤ 1 → |shiftDifference a r| ≤ 2 * a * (C₁ * Real.exp 2) *
      Real.exp (-(2 * |r|)) := fun a r ha ha1 => by
    have hbd : ∀ y ∈ Icc (r - a) (r + a), ‖deriv riemannKernelReal y‖ ≤
        C₁ * Real.exp 2 * Real.exp (-(2 * |r|)) := fun y hy => by
      rw [Real.norm_eq_abs]
      refine (hD y).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁
      have : |r| ≤ |y| + a := by
        have := abs_sub_abs_le_abs_sub r y
        have hyr : |r - y| ≤ a := abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
        linarith
      linarith
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hdiff y) hbd (convex_Icc _ _)
      (show r + a ∈ Icc (r - a) (r + a) from ⟨by linarith, le_rfl⟩)
      (show r - a ∈ Icc (r - a) (r + a) from ⟨le_rfl, by linarith⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show r - a - (r + a) = -(2 * a) by ring, abs_neg,
      abs_of_pos (by linarith : 0 < 2 * a)] at h
    unfold shiftDifference
    calc |riemannKernelReal (r - a) - riemannKernelReal (r + a)|
        ≤ C₁ * Real.exp 2 * Real.exp (-(2 * |r|)) * (2 * a) := h
      _ = 2 * a * (C₁ * Real.exp 2) * Real.exp (-(2 * |r|)) := by ring
  have hcont : ∀ a, Continuous fun r => Real.exp (-r / 2) * shiftDifference a r := fun a =>
    (Real.continuous_exp.comp (continuous_neg.div_const 2)).mul (continuous_shiftDifference a)
  have e : (fun a => (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) / a) =
      fun a => ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * (shiftDifference a r / a) := by
    funext a
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun r => by simp only; ring)
  rw [e]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun r => 2 * (C₁ * Real.exp 2) * Real.exp (-2 * r)) ?_ ?_
    ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 2)).const_mul _) ?_
  · exact Eventually.of_forall fun a => ((hcont a).div_const a).aestronglyMeasurable.congr
      (Eventually.of_forall fun r => by simp only; ring)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with a ha
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 ≤ r := le_of_lt hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos ha.1]
    have h1 := hmvt a r ha.1 ha.2.le
    rw [abs_of_nonneg hr0] at h1
    have he : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hq : |shiftDifference a r| / a ≤ 2 * (C₁ * Real.exp 2) * Real.exp (-(2 * r)) := by
      rw [div_le_iff₀ ha.1]; nlinarith [Real.exp_pos 2, Real.exp_pos (-(2 * r))]
    calc Real.exp (-r / 2) * (|shiftDifference a r| / a)
        ≤ 1 * (2 * (C₁ * Real.exp 2) * Real.exp (-(2 * r))) :=
          mul_le_mul he hq (div_nonneg (abs_nonneg _) ha.1.le) zero_le_one
      _ = 2 * (C₁ * Real.exp 2) * Real.exp (-2 * r) := by ring_nf
  · refine Eventually.of_forall fun r => ?_
    have hd := hasDerivAt_riemannKernelReal r
    rw [← hd.deriv] at hd
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝[≠] 0) :=
      tendsto_id'.mpr (nhdsWithin_mono _ fun a ha => ne_of_gt ha)
    have hneg : Tendsto (fun a : ℝ => -a) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_neg.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with a ha
        exact neg_ne_zero.mpr (ne_of_gt ha)
    have h1 := hd.tendsto_slope_zero.comp hid
    have h2 := hd.tendsto_slope_zero.comp hneg
    have h3 := (h1.neg.sub h2).const_mul (Real.exp (-r / 2))
    rw [show Real.exp (-r / 2) * (-deriv riemannKernelReal r - deriv riemannKernelReal r) =
      Real.exp (-r / 2) * (-2 * deriv riemannKernelReal r) by ring] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : a ≠ 0 := ne_of_gt ha
    simp only [Function.comp_def, smul_eq_mul, shiftDifference]
    field_simp
    ring_nf

/-- **`R(a) → 1 + 8Φ(0) + 4σ` as `a → 0⁺`** (README 3.4, small-shift end), `σ = ∫_0^∞ Φ sinh(u/2)`. -/
theorem tendsto_collarRatio_nhdsGT_zero :
    Tendsto (fun a => 2 + 2 * (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference a r) /
      Real.sinh (a / 2)) (𝓝[>] 0) (𝓝 (1 + 8 * riemannKernelReal 0 + 4 * halfSinhMoment)) := by
  have hE := tendsto_integral_exp_neg_half_mul_shiftDifference_div
  have hval : (∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * (-2 * deriv riemannKernelReal r)) =
      2 * riemannKernelReal 0 - 1 / 4 + halfSinhMoment := by
    have e : (fun r => Real.exp (-r / 2) * (-2 * deriv riemannKernelReal r)) =
        fun r => 2 * (Real.exp (-r / 2) * -deriv riemannKernelReal r) := funext fun r => by ring
    rw [e, integral_const_mul, integral_Ioi_exp_neg_half_mul_neg_deriv,
      integral_Ioi_exp_neg_half_mul_riemannKernelReal]
    ring
  rw [hval] at hE
  have hs : Tendsto (fun a : ℝ => Real.sinh (a / 2) / a) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    have hd : HasDerivAt (fun a : ℝ => Real.sinh (a / 2)) (Real.cosh (0 / 2) * (1 / 2)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).sinh
    have h := (hd.tendsto_slope_zero.comp (tendsto_id'.mpr
      (nhdsWithin_mono _ fun a (ha : (0 : ℝ) < a) => ne_of_gt ha)))
    simp only [zero_div, Real.cosh_zero, one_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    simp only [Function.comp_def, smul_eq_mul, zero_add, Real.sinh_zero, sub_zero, id]
    field_simp
  have hlim := ((hE.const_mul 2).div hs (by norm_num)).const_add 2
  have hfin : 2 + 2 * (2 * riemannKernelReal 0 - 1 / 4 + halfSinhMoment) / (1 / 2) =
      1 + 8 * riemannKernelReal 0 + 4 * halfSinhMoment := by ring
  rw [hfin] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  congr 1
  simp only [Pi.div_apply]
  rw [← mul_div_assoc, div_div_div_cancel_right₀ ha0]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
