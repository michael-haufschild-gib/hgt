import GaloisForLFunctions.RHTower.DeningerMeyerOscillator
import GaloisForLFunctions.RHTower.DeningerMeyerTopology
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Strong continuity of the exponential gauge on Meyer's source

The adiabatic Möbius family is obtained from the critical preimage by the exact gauge

`M_a h(x) = x^a f_(exp(-a·)h)(x)`.

Using this identity at the singular endpoint requires convergence in the actual projective Meyer
topology, not pointwise convergence of the gauge.  This file proves the missing strong-continuity
statement directly from the defining exponentially weighted derivative seminorms.

* `deningerRealExp_sub_one_norm_le` is the uniform mean-value estimate.
* `deningerExpMul_sub_seminorm_le` is the load-bearing projective-seminorm estimate.
* `tendsto_deningerExpMul_neg_zero` is strong convergence of the adiabatic gauge to the identity.
-/

namespace RHTower

open Filter Topology SchwartzMap

open scoped ContDiff

noncomputable section

/-- Uniform mean-value estimate for the real exponential on the parameter interval `[-1,1]`.
The factor `exp |t|` is precisely what can be absorbed by one stronger Meyer weight. -/
theorem deningerRealExp_sub_one_norm_le {a t : ℝ} (ha : |a| ≤ 1) :
    |Real.exp (-a * t) - 1| ≤ |a| * |t| * Real.exp |t| := by
  let f : ℝ → ℝ := fun s => Real.exp (-s * t)
  have hdiff : ∀ s ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ f s := by
    intro s _
    dsimp [f]
    fun_prop
  have hderiv : ∀ s : ℝ, deriv f s = -t * Real.exp (-s * t) := by
    intro s
    have hs : HasDerivAt f (-t * Real.exp (-s * t)) s := by
      dsimp [f]
      convert (Real.hasDerivAt_exp (-s * t)).mul_const (-t) using 1 <;> ring
    exact hs.deriv
  have hbound : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      ‖deriv f s‖ ≤ |t| * Real.exp |t| := by
    intro s hs
    rw [hderiv, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg t)
    calc
      -s * t ≤ |-s * t| := le_abs_self _
      _ = |s| * |t| := by rw [abs_mul, abs_neg]
      _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right (by
        rw [abs_le]
        exact hs) (abs_nonneg t)
      _ = |t| := one_mul _
  have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hmem : a ∈ Set.Icc (-1 : ℝ) 1 := by rwa [← abs_le]
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc (-1 : ℝ) 1) hzero hmem
  dsimp [f] at hmvt
  rw [Real.exp_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_zero, sub_zero] at hmvt
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmvt

/-- The difference weight `exp(-a t)-1`, as a complex-valued smooth function. -/
def deningerAdiabaticWeightDifference (a : ℝ) (t : ℝ) : ℂ :=
  ((Real.exp (-a * t) - 1 : ℝ) : ℂ)

theorem deningerAdiabaticWeightDifference_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (deningerAdiabaticWeightDifference a) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => Real.exp (-a * t) - 1 :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).sub contDiff_const
  exact Complex.ofRealCLM.contDiff.comp h

/-- Every derivative of the difference weight is `O(|a| exp |t|)` uniformly for `|a| ≤ 1`.
At order zero the extra `|t|` is forced by the mean-value theorem. -/
theorem deningerAdiabaticWeightDifference_iteratedFDeriv_norm_le
    {a : ℝ} (ha : |a| ≤ 1) (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (deningerAdiabaticWeightDifference a) t‖ ≤
      |a| * (1 + |t|) * Real.exp |t| := by
  cases i with
  | zero =>
      rw [iteratedFDeriv_zero_apply]
      change ‖((Real.exp (-a * t) - 1 : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine le_trans (deningerRealExp_sub_one_norm_le ha) ?_
      have he : 0 < Real.exp |t| := Real.exp_pos _
      nlinarith [abs_nonneg a, abs_nonneg t]
  | succ i =>
      have hsub : deningerAdiabaticWeightDifference a =
          deningerRealExpWeight (-a) - fun _ : ℝ => (1 : ℂ) := by
        funext x
        simp [deningerAdiabaticWeightDifference, deningerRealExpWeight]
      rw [hsub, iteratedFDeriv_sub_apply
        (deningerRealExpWeight_contDiff (-a)).contDiffAt contDiff_const.contDiffAt,
        iteratedFDeriv_succ_const, sub_zero,
        deningerRealExpWeight_norm_iteratedFDeriv]
      rw [abs_neg]
      have hapow : |a| ^ (Nat.succ i) ≤ |a| := by
        have ha0 : 0 ≤ |a| := abs_nonneg _
        have := pow_le_pow_right₀ ha0 ha (Nat.succ_pos i)
        simpa using this
      have hexp : Real.exp ((-a) * t) ≤ Real.exp |t| := by
        apply Real.exp_le_exp.mpr
        calc
          -a * t ≤ |-a * t| := le_abs_self _
          _ = |a| * |t| := by rw [abs_mul, abs_neg]
          _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right ha (abs_nonneg t)
          _ = |t| := one_mul _
      have hprod : |a| ^ (Nat.succ i) * Real.exp ((-a) * t) ≤
          |a| * Real.exp |t| :=
        mul_le_mul hapow hexp (Real.exp_pos _).le (abs_nonneg _)
      exact le_trans hprod (by
        have he : 0 < Real.exp |t| := Real.exp_pos _
        nlinarith [abs_nonneg a, abs_nonneg t])

/-- Polynomial loss from the zeroth derivative is absorbed by two exponential weights. -/
theorem deninger_one_add_abs_mul_exp_le_two_exp_two (t : ℝ) :
    (1 + |t|) * Real.exp |t| ≤ 2 * Real.exp (2 * |t|) := by
  have ht : 0 ≤ |t| := abs_nonneg _
  have hone : 1 ≤ Real.exp |t| := by simpa using Real.one_le_exp ht
  have habs : |t| ≤ Real.exp |t| := Real.self_le_exp |t|
  calc
    (1 + |t|) * Real.exp |t| ≤
        (Real.exp |t| + Real.exp |t|) * Real.exp |t| := by gcongr
    _ = 2 * Real.exp (2 * |t|) := by
      rw [show (2 : ℝ) * |t| = |t| + |t| by ring, Real.exp_add]
      ring

/-- Pointwise derivative estimate for the adiabatic gauge difference. -/
theorem deningerExpMul_sub_iteratedFDeriv_norm_le
    (h : DeningerExpSchwartz) {a : ℝ} (ha : |a| ≤ 1) (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n
        ((((deningerExpMulLM (-a) h - h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (|a| * (1 + |t|) * Real.exp |t|) *
        ‖iteratedFDeriv ℝ (n - i)
          ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖ := by
  have hfun :
      ((((deningerExpMulLM (-a) h - h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) =
        fun x => deningerAdiabaticWeightDifference a x *
          (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
    funext x
    rw [Pi.sub_apply]
    change ((deningerExpMulLM (-a) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x -
        ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x = _
    rw [deningerExpMulLM_apply]
    simp [deningerAdiabaticWeightDifference, deningerRealExpWeight]
    ring
  rw [hfun]
  refine le_trans (norm_iteratedFDeriv_mul_le
    (deningerAdiabaticWeightDifference_contDiff a)
    (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth') t ENat.LEInfty.out) ?_
  exact Finset.sum_le_sum fun i _ => by
    gcongr
    exact deningerAdiabaticWeightDifference_iteratedFDeriv_norm_le ha i t

/-- **Projective Meyer estimate for the adiabatic gauge.**  Each output seminorm is `O(|a|)`
against finitely many two-weights-stronger input seminorms.  This is stronger than pointwise
convergence and is the strict source endpoint needed by the Euler--Möbius transgression. -/
theorem deningerExpMul_sub_seminorm_le
    (h : DeningerExpSchwartz) {a : ℝ} (ha : |a| ≤ 1) (A : ℕ) (n : ℕ) :
    deningerMeyerSeminormFun (A : ℝ) n (deningerExpMulLM (-a) h - h) ≤
      |a| * (2 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        deningerMeyerSeminormFun ((A + 2 : ℕ) : ℝ) (n - i) h) := by
  apply deningerMeyerSeminormFun_le
  intro t
  rw [deningerMeyerWeight]
  refine le_trans (mul_le_mul_of_nonneg_left
    (deningerExpMul_sub_iteratedFDeriv_norm_le h ha n t) (Real.exp_pos _).le) ?_
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_of_eq ?_)
  · have hq := deningerMeyerWeight_le ((A + 2 : ℕ) : ℝ) (n - i) h t
    rw [deningerMeyerWeight] at hq
    have habsorb := deninger_one_add_abs_mul_exp_le_two_exp_two t
    have hAcast : (((A + 2 : ℕ) : ℝ)) = (A : ℝ) + 2 := by push_cast; ring
    rw [hAcast] at hq
    have hweight : Real.exp ((A : ℝ) * |t|) *
          ((1 + |t|) * Real.exp |t|) ≤
        2 * Real.exp (((A : ℝ) + 2) * |t|) := by
      calc
        Real.exp ((A : ℝ) * |t|) * ((1 + |t|) * Real.exp |t|) ≤
            Real.exp ((A : ℝ) * |t|) * (2 * Real.exp (2 * |t|)) :=
          mul_le_mul_of_nonneg_left habsorb (Real.exp_pos _).le
        _ = 2 * Real.exp (((A : ℝ) + 2) * |t|) := by
          rw [show ((A : ℝ) + 2) * |t| = (A : ℝ) * |t| + 2 * |t| by ring,
            Real.exp_add]
          ring
    have hderiv : 0 ≤ ‖iteratedFDeriv ℝ (n - i)
        ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖ := norm_nonneg _
    calc
      Real.exp ((A : ℝ) * |t|) *
          ((n.choose i : ℝ) * (|a| * (1 + |t|) * Real.exp |t|) *
            ‖iteratedFDeriv ℝ (n - i)
              ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖)
        = |a| * (n.choose i : ℝ) *
          (Real.exp ((A : ℝ) * |t|) * ((1 + |t|) * Real.exp |t|) *
            ‖iteratedFDeriv ℝ (n - i)
              ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖) := by ring
      _ ≤ |a| * (n.choose i : ℝ) *
          (2 * Real.exp (((A : ℝ) + 2) * |t|) *
            ‖iteratedFDeriv ℝ (n - i)
              ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) t‖) := by
        gcongr
      _ ≤ |a| * (n.choose i : ℝ) *
          (2 * deningerMeyerSeminormFun ((A + 2 : ℕ) : ℝ) (n - i) h) := by
        gcongr
      _ = |a| * (2 * ((n.choose i : ℝ) *
          deningerMeyerSeminormFun ((A + 2 : ℕ) : ℝ) (n - i) h)) := by ring
  · ring

/-- **Strong adiabatic endpoint in Meyer's actual projective topology.** -/
theorem tendsto_deningerExpMul_neg_zero (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ =>
        DeningerMeyerSource.toSource.symm
          (deningerExpMulLM (-a) (DeningerMeyerSource.toSource h)))
      (𝓝 0) (𝓝 h) := by
  rw [← tendsto_sub_nhds_zero_iff,
    DeningerMeyerSource.withSeminorms.tendsto_nhds]
  rintro ⟨A, n⟩ ε hε
  let C : ℝ := 2 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    deningerMeyerSeminormFun ((A + 2 : ℕ) : ℝ) (n - i)
      (DeningerMeyerSource.toSource h)
  have hlim : Tendsto (fun a : ℝ => |a| * C) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto 0).mul_const C
  have hsmall : ∀ᶠ a : ℝ in 𝓝 0, |a| ≤ 1 :=
    (continuous_abs.tendsto 0).eventually_le_const (by norm_num)
  have hbound : ∀ᶠ a : ℝ in 𝓝 0, |a| * C < ε :=
    hlim.eventually_lt_const hε
  filter_upwards [hsmall, hbound] with a ha hC
  change deningerMeyerSeminormFun (A : ℝ) n
      (deningerExpMulLM (-a) (DeningerMeyerSource.toSource h) -
        DeningerMeyerSource.toSource h) < ε
  exact lt_of_le_of_lt (deningerExpMul_sub_seminorm_le
    (DeningerMeyerSource.toSource h) ha A n) hC

end

end RHTower
