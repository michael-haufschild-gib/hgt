import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheAveragedBudgetIsExactlyAdmission

/-!
# An adapted energy is exactly admission

The corrector architecture for backward continuation seeks a finite arithmetic cross term
`C_T(ε)` and the **adapted energy** `H_T = 1 + E_T + C_T`, comparable to the receiver with
horizon-free constants,

`m (1 + E_T) ≤ H_T ≤ M (1 + E_T)`  on `[a, c]`,

whose signed relative loss `−∂_ε H_T / H_T` has a horizon-free integral bound. The propagation is
routine (`Admits.of_adaptedEnergy`): `log H_T(a) − log H_T(c)` is the integrated loss, so admission
at `c` passes to `a` with the constant `(M/m) e^L`. The point of this file is the converse and its
consequence:

* `adaptedEnergy_iff_admits`: with the right end admitted, an adapted energy on `[a, c]` exists
  **if and only if** the receiver is admitted at `a` — the trivial corrector `C_T = 0` already
  works when admission holds. The comparability constraint is what keeps the notion honest:
  without it the constant family `H_T(ε) = 1 + E_T(c)` has zero loss for every receiver.
* `adaptedEnergy_of_pointwise`: a pointwise corrector budget `−∂H_T ≤ b H_T`, `b ∈ L¹`, is one way
  to produce an adapted energy, and it is a strictly stronger demand
  (`ArithmeticContinuationAndCriticalEnergy.exists_admits_everywhere_not_linearContinuation`).
* `riemannHypothesis_iff_cofinal_adaptedEnergy`: for the damped Möbius receiver, adapted energies
  on `[a, ½]` for a cofinal set of `a ↓ 0` are equivalent to RH.

So the corrector framework neither adds nor loses strength: its content is entirely in the
*construction* of `C_T` from arithmetic cross terms with independently proved constants. A
corrector read off from the desired bound, from the location of the zeros, or chosen to define the
energy away proves nothing.
-/

open Set Filter Finset MeasureTheory
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

variable {E : ℝ → ℕ → ℝ} {E' : ℕ → ℝ → ℝ} {a c : ℝ}

/-- **An adapted energy for `E` on `[a, c]`**: a family `H_T` comparable to `1 + E_T` with
horizon-free constants, differentiable in the parameter, whose signed relative loss `−∂H_T/H_T`
has a horizon-free integral bound. -/
def AdaptedEnergy (E : ℝ → ℕ → ℝ) (a c : ℝ) : Prop :=
  ∃ (H : ℝ → ℕ → ℝ) (H' : ℕ → ℝ → ℝ) (m M L : ℝ), 0 < m ∧
    (∀ T, ∀ ε ∈ Icc a c, m * (1 + E ε T) ≤ H ε T ∧ H ε T ≤ M * (1 + E ε T)) ∧
    (∀ T, ∀ ε ∈ Icc a c, HasDerivAt (fun x => H x T) (H' T ε) ε) ∧
    (∀ T, IntervalIntegrable (fun ε => -H' T ε / H ε T) volume a c) ∧
    (∀ T, ∫ ε in a..c, -H' T ε / H ε T ≤ L)

/-- **Propagation.** An adapted energy and admission at `c` give admission at `a`, with the bound
`(M/m) e^L (1 + B) − 1`. -/
theorem Admits.of_adaptedEnergy (hac : a ≤ c) (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hAE : AdaptedEnergy E a c) (hc : Admits E c) : Admits E a := by
  obtain ⟨H, H', m, M, L, hm, hcomp, hderiv, hint, hL⟩ := hAE
  obtain ⟨B, hB⟩ := hc
  refine ⟨M * Real.exp L * (1 + max B 0) / m - 1, fun T => ?_⟩
  have hpos : ∀ ε ∈ Icc a c, 0 < H ε T := fun ε hε => by
    have h1 := (hcomp T ε hε).1
    have h2 := hE0 ε hε T
    nlinarith
  -- the integrated loss is the logarithmic drop of the adapted energy
  have hlog : ∀ ε ∈ uIcc a c, HasDerivAt (fun x => Real.log (H x T)) (H' T ε / H ε T) ε := by
    intro ε hε
    rw [uIcc_of_le hac] at hε
    exact (hderiv T ε hε).log (hpos ε hε).ne'
  have hint' : IntervalIntegrable (fun ε => H' T ε / H ε T) volume a c := by
    have := (hint T).neg
    simpa [neg_div, neg_neg] using this
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog hint'
  have hneg : (∫ ε in a..c, -H' T ε / H ε T) = Real.log (H a T) - Real.log (H c T) := by
    simp only [neg_div, intervalIntegral.integral_neg, hFTC]
    ring
  have hLT := hL T
  rw [hneg] at hLT
  have ha := left_mem_Icc.mpr hac
  have hc' := right_mem_Icc.mpr hac
  have hHa := hpos a ha
  have hHc := hpos c hc'
  have hratio : H a T ≤ Real.exp L * H c T := by
    have h1 : Real.log (H a T) ≤ L + Real.log (H c T) := by linarith
    calc H a T = Real.exp (Real.log (H a T)) := (Real.exp_log hHa).symm
      _ ≤ Real.exp (L + Real.log (H c T)) := Real.exp_le_exp.mpr h1
      _ = Real.exp L * H c T := by rw [Real.exp_add, Real.exp_log hHc]
  have hHcM : H c T ≤ M * (1 + max B 0) := by
    have h1 := (hcomp T c hc').2
    have h2 : 1 + E c T ≤ 1 + max B 0 := by linarith [hB T, le_max_left B 0]
    have hM : 0 ≤ M := by
      have := (hcomp T c hc').1
      have h3 := hE0 c hc' T
      by_contra hneg
      push Not at hneg
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hM)
  have hlow := (hcomp T a ha).1
  rw [le_sub_iff_add_le, le_div_iff₀ hm]
  have hexp := Real.exp_pos L
  calc (E a T + 1) * m = m * (1 + E a T) := by ring
    _ ≤ H a T := hlow
    _ ≤ Real.exp L * H c T := hratio
    _ ≤ Real.exp L * (M * (1 + max B 0)) := mul_le_mul_of_nonneg_left hHcM hexp.le
    _ = M * Real.exp L * (1 + max B 0) := by ring

/-- **Admission is an adapted energy.** The trivial corrector `H_T = 1 + E_T` works. -/
theorem adaptedEnergy_of_admits (hac : a ≤ c) (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c) (ha : Admits E a) :
    AdaptedEnergy E a c := by
  obtain ⟨L, hL⟩ := AveragedContinuation.of_admits hac hE0 hEd hint ha
  refine ⟨fun ε T => 1 + E ε T, E', 1, 1, L, one_pos, fun T ε _ => ⟨by simp, by simp⟩,
    fun T ε hε => (hEd T ε hε).const_add 1, fun T => (hL T).1, fun T => (hL T).2⟩

/-- **An adapted energy is exactly admission.** With the right end admitted, an adapted energy on
`[a, c]` exists if and only if the receiver is admitted at `a`. -/
theorem adaptedEnergy_iff_admits (hac : a ≤ c) (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    (hEd : ∀ T : ℕ, ∀ ε ∈ Icc a c, HasDerivAt (fun x => E x T) (E' T ε) ε)
    (hint : ∀ T : ℕ, IntervalIntegrable (relativeLoss E E' T) volume a c) (hc : Admits E c) :
    AdaptedEnergy E a c ↔ Admits E a :=
  ⟨fun h => Admits.of_adaptedEnergy hac hE0 h hc, adaptedEnergy_of_admits hac hE0 hEd hint⟩

/-- **The pointwise corrector budget** `−∂H_T ≤ b H_T` with an integrable `b`, uniform in the
horizon, produces an adapted energy with loss `∫_a^c b`. -/
theorem adaptedEnergy_of_pointwise (hac : a ≤ c) (hE0 : ∀ ε ∈ Icc a c, ∀ T, 0 ≤ E ε T)
    {H : ℝ → ℕ → ℝ} {H' : ℕ → ℝ → ℝ} {m M : ℝ} {b : ℝ → ℝ} (hm : 0 < m)
    (hcomp : ∀ T, ∀ ε ∈ Icc a c, m * (1 + E ε T) ≤ H ε T ∧ H ε T ≤ M * (1 + E ε T))
    (hderiv : ∀ T, ∀ ε ∈ Icc a c, HasDerivAt (fun x => H x T) (H' T ε) ε)
    (hint : ∀ T, IntervalIntegrable (fun ε => -H' T ε / H ε T) volume a c)
    (hb : IntervalIntegrable b volume a c) (hpt : ∀ T, ∀ ε ∈ Icc a c, -H' T ε ≤ b ε * H ε T) :
    AdaptedEnergy E a c := by
  refine ⟨H, H', m, M, ∫ ε in a..c, b ε, hm, hcomp, hderiv, hint, fun T => ?_⟩
  refine intervalIntegral.integral_mono_on hac (hint T) hb fun ε hε => ?_
  have hpos : 0 < H ε T := by
    have h1 := (hcomp T ε hε).1
    have h2 := hE0 ε hε T
    nlinarith
  rw [div_le_iff₀ hpos]
  exact hpt T ε hε

/-- **The corrector target for the actual receiver is the Riemann hypothesis.** Adapted energies
on `[a, ½]` for dampings `a` arbitrarily close to `0` exist if and only if RH holds. -/
theorem riemannHypothesis_iff_cofinal_adaptedEnergy :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ a < δ ∧
      AdaptedEnergy dampedMobiusEnergy a (1 / 2) := by
  have hiff : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 →
      (AdaptedEnergy dampedMobiusEnergy a (1 / 2) ↔ Admits dampedMobiusEnergy a) := fun a ha hac =>
    adaptedEnergy_iff_admits hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (fun T _ hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T)
      (fun T => intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T)
      (admits_dampedMobiusEnergy_of_half_le le_rfl)
  rw [riemannHypothesis_iff_cofinal_averagedDampingContinuation]
  constructor
  · intro h δ hδ
    obtain ⟨a, ha, haδ, hav⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have hac : a ≤ 1 / 2 := (lt_of_lt_of_le haδ (min_le_right _ _)).le
    refine ⟨a, ha, lt_of_lt_of_le haδ (min_le_left _ _), (hiff a ha hac).mpr ?_⟩
    exact (averagedDampingContinuation_iff_admits ha hac
      (admits_dampedMobiusEnergy_of_half_le le_rfl)).mp hav
  · intro h δ hδ
    obtain ⟨a, ha, haδ, hAE⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have hac : a ≤ 1 / 2 := (lt_of_lt_of_le haδ (min_le_right _ _)).le
    refine ⟨a, ha, lt_of_lt_of_le haδ (min_le_left _ _), ?_⟩
    exact (averagedDampingContinuation_iff_admits ha hac
      (admits_dampedMobiusEnergy_of_half_le le_rfl)).mpr ((hiff a ha hac).mp hAE)

end GaloisForLFunctions.ArithmeticCompensationTheory
