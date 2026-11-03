import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheArchimedeanPlaceAloneIsNotWeilPositive

/-!
# Tate positivity does not descend

The shifted datum `ζ(s)ζ(s − ε)` (WTZ `shiftedDatum`) has Tate family `J_k · twist_{−ε}J_k`. This
module shows that its positivity in positive dimension carries nothing to dimension zero:

* **Positive in every real positive dimension** (`shiftedDatum_tateFamily_nonneg_real`): all its Tate
  pieces are `≥ 0` for every real `k ≥ 0`, as for `ζ`.
* **Its dimension-zero derivative is the shifted weight** (`hasDerivAt_shiftedDatum_tateFamily`):
  `∂_k|₀ = λ_ε(n) = Λ(n)(1 + n^ε)` (`shiftedWeight`), its von Mangoldt function.
* **That weight is not Weil positive** with `ζ`'s archimedean datum
  (`not_weilPositiveFull_shiftedWeight`), for every real `ε`: the Weil cone is `{Λ}` and
  `λ_ε(2) = (1 + 2^ε)log 2 ≠ log 2`.

Hence (`tatePositivity_does_not_descend`) no argument that uses only the positivity of the counts in
positive dimension can reach Weil positivity at `k = 0`: descent through the 1-jet
(`weilQuad_nonneg_of_dominates`) would apply verbatim to the shifted datum and prove a false
statement. The selection between `ζ` and its shifts happens at dimension zero, against the
archimedean data, never in positive dimension — the dimension-zero form of WTZ's "counting
coefficients do not select".
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ ArithmeticDegenerationTheory _root_.RHTower _root_.RHTower.WeilSpectral

/-- The **shifted weight** `λ_ε(n) = Λ(n)(1 + n^ε)`: the von Mangoldt function of `ζ(s)ζ(s − ε)`. -/
def shiftedWeight (ε : ℝ) (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * (1 + (n : ℝ) ^ ε)

/-- **The shifted datum is Tate positive in every real positive dimension.** -/
theorem shiftedDatum_tateFamily_nonneg_real (ε : ℝ) {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ tateFamily (shiftedDatum ε) (shiftedInverse ε) k n := by
  rw [tateFamily_shiftedDatum]
  exact mul_nonneg_af (fun m => jordanTotient_nonneg hk m)
    (tateTwist_nonneg fun m => jordanTotient_nonneg hk m) n

theorem jordanTotient_zero_dim (m : ℕ) : jordanTotient 0 m = if m = 1 then 1 else 0 := by
  rw [← jordanFun_apply, jordanFun_zero, ArithmeticFunction.one_apply]

/-- **The dimension-zero derivative of the shifted datum is its von Mangoldt function.** -/
theorem hasDerivAt_shiftedDatum_tateFamily (ε : ℝ) (n : ℕ) :
    HasDerivAt (fun k => tateFamily (shiftedDatum ε) (shiftedInverse ε) k n) (shiftedWeight ε n) 0 := by
  simp only [tateFamily_shiftedDatum, ArithmeticFunction.mul_apply, tateTwist_apply, jordanFun_apply,
    neg_neg]
  have h : HasDerivAt (fun k => ∑ x ∈ n.divisorsAntidiagonal,
      jordanTotient k x.1 * (jordanTotient k x.2 * (x.2 : ℝ) ^ ε))
      (∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.vonMangoldt x.1 *
        (jordanTotient 0 x.2 * (x.2 : ℝ) ^ ε) +
          jordanTotient 0 x.1 * (ArithmeticFunction.vonMangoldt x.2 * (x.2 : ℝ) ^ ε))) 0 :=
    HasDerivAt.fun_sum fun x _ =>
      (hasDerivAt_jordanTotient_zero x.1).mul ((hasDerivAt_jordanTotient_zero x.2).mul_const _)
  refine h.congr_deriv ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [shiftedWeight]
  have hn1 : (n, 1) ∈ n.divisorsAntidiagonal := by simp [hn.ne']
  have h1n : (1, n) ∈ n.divisorsAntidiagonal := by simp [hn.ne']
  simp only [jordanTotient_zero_dim, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single_of_mem (n, 1) hn1, Finset.sum_eq_single_of_mem (1, n) h1n]
  · simp [shiftedWeight]
    ring
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have : x.1 ≠ 1 := fun h1 => hne (Prod.ext h1 (by rw [← hx'.1, h1, one_mul]))
    simp [this]
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have : x.2 ≠ 1 := fun h1 => hne (Prod.ext (by rw [← hx'.1, h1, mul_one]) h1)
    simp [this]

/-- **The shifted weight is not Weil positive** (with `ζ`'s archimedean datum), for every `ε`. -/
theorem not_weilPositiveFull_shiftedWeight (ε : ℝ) : ¬ WeilPositiveFull (shiftedWeight ε) := by
  intro h
  have h2 := eq_vonMangoldt_of_weilPositiveFull h 2 le_rfl
  rw [shiftedWeight, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : 0 < ((2 : ℕ) : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) ε
  have : Real.log ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ ε = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · simp at h; linarith
  · linarith

/-- **Tate positivity does not descend.** For every `ε`, the shifted datum `ζ(s)ζ(s − ε)` is Tate
positive in every real dimension `k ≥ 0`, its Tate family has dimension-zero derivative `λ_ε`, and
`λ_ε` is not Weil positive. -/
theorem tatePositivity_does_not_descend (ε : ℝ) :
    (∀ k : ℝ, 0 ≤ k → ∀ n, 0 ≤ tateFamily (shiftedDatum ε) (shiftedInverse ε) k n) ∧
      (∀ n, HasDerivAt (fun k => tateFamily (shiftedDatum ε) (shiftedInverse ε) k n)
        (shiftedWeight ε n) 0) ∧
      ¬ WeilPositiveFull (shiftedWeight ε) :=
  ⟨fun _ hk n => shiftedDatum_tateFamily_nonneg_real ε hk n,
    hasDerivAt_shiftedDatum_tateFamily ε, not_weilPositiveFull_shiftedWeight ε⟩

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
