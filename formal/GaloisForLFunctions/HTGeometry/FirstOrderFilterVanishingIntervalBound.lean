import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Compact

/-!
# Output of a first-order filter on an interval where it vanishes

Let `s` solve the first-order equation `b s′ = −Z − c s` on `I = [α, β]` with `b > 0`, `|c| ≤ C`
and `2C(β − α) ≤ b`, and suppose `s` vanishes somewhere in `I`. Then the output is controlled
locally by the input:

* `abs_le_of_firstOrderFilter`: `|s x| ≤ (2/b)∫_I |Z|` on `I`;
* `integral_sq_le_of_firstOrderFilter`: `∫_I s² ≤ (4/b²)(β − α)²∫_I Z²`.

The proof bounds `|s x| = |∫_{x₀}^x s′|` by `(1/b)∫_I(|Z| + C|s|)` and absorbs the `C`-term using
the length condition; Cauchy–Schwarz then gives the quadratic form.
-/

open MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions.HTGeometry

variable {s Z c : ℝ → ℝ} {α β b C : ℝ}

theorem abs_le_of_firstOrderFilter (hb : 0 < b) (hC : 0 ≤ C) (hαβ : α ≤ β)
    (hlen : 2 * C * (β - α) ≤ b)
    (hs : ∀ x ∈ Icc α β, HasDerivAt s (-(Z x + c x * s x) / b) x)
    (hZ : ContinuousOn Z (Icc α β)) (hcc : ContinuousOn c (Icc α β))
    (hc : ∀ x ∈ Icc α β, |c x| ≤ C) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc α β) (hzero : s x₀ = 0) :
    ∀ x ∈ Icc α β, |s x| ≤ 2 / b * ∫ y in α..β, |Z y| := by
  have hscont : ContinuousOn s (Icc α β) := fun x hx => (hs x hx).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmax⟩ := (isCompact_Icc (a := α) (b := β)).exists_isMaxOn
    (nonempty_Icc.mpr hαβ) (continuous_abs.comp_continuousOn hscont)
  set M := |s m| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hle_M : ∀ x ∈ Icc α β, |s x| ≤ M := fun x hx => hmax hx
  have hderiv_cont : ContinuousOn (fun x => -(Z x + c x * s x) / b) (Icc α β) :=
    ((hZ.add (hcc.mul hscont)).neg).div_const b
  -- the bound on the derivative
  have hderiv_le : ∀ x ∈ Icc α β, |-(Z x + c x * s x) / b| ≤ (|Z x| + C * M) / b := by
    intro x hx
    rw [abs_div, abs_of_pos hb, abs_neg]
    gcongr
    calc |Z x + c x * s x| ≤ |Z x| + |c x| * |s x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |Z x| + C * M := by
          gcongr
          · exact hc x hx
          · exact hle_M x hx
  have hint_abs : IntervalIntegrable (fun y => |Z y|) volume α β :=
    (continuous_abs.comp_continuousOn hZ).intervalIntegrable_of_Icc hαβ
  -- every value is bounded by the integral of the derivative bound
  have hpoint : ∀ x ∈ Icc α β, |s x| ≤ (∫ y in α..β, |Z y|) / b + C * M * (β - α) / b := by
    intro x hx
    have hsub : ∀ {u v : ℝ}, u ∈ Icc α β → v ∈ Icc α β → u ≤ v →
        |s v - s u| ≤ ∫ y in u..v, (|Z y| + C * M) / b := by
      intro u v hu hv huv
      have huvI : Icc u v ⊆ Icc α β := Icc_subset_Icc hu.1 hv.2
      have hFTC : ∫ y in u..v, -(Z y + c y * s y) / b = s v - s u := by
        refine integral_eq_sub_of_hasDerivAt (fun y hy => ?_) ?_
        · rw [uIcc_of_le huv] at hy
          exact hs y (huvI hy)
        · exact (hderiv_cont.mono huvI).intervalIntegrable_of_Icc huv
      rw [← hFTC]
      refine (abs_integral_le_integral_abs huv).trans ?_
      refine integral_mono_on huv ?_ ?_ (fun y hy => hderiv_le y (huvI hy))
      · exact (continuous_abs.comp_continuousOn (hderiv_cont.mono huvI)).intervalIntegrable_of_Icc
          huv
      · exact (((continuous_abs.comp_continuousOn (hZ.mono huvI)).add
          continuousOn_const).div_const b).intervalIntegrable_of_Icc huv
    have hfull : ∀ {u v : ℝ}, u ∈ Icc α β → v ∈ Icc α β → u ≤ v →
        ∫ y in u..v, (|Z y| + C * M) / b ≤
          (∫ y in α..β, |Z y|) / b + C * M * (β - α) / b := by
      intro u v hu hv huv
      have huvI : Icc u v ⊆ Icc α β := Icc_subset_Icc hu.1 hv.2
      have hnn : ∀ y, 0 ≤ (|Z y| + C * M) / b := fun y => by positivity
      have hint_full : IntervalIntegrable (fun y => (|Z y| + C * M) / b) volume α β :=
        (hint_abs.add intervalIntegrable_const).div_const b
      calc ∫ y in u..v, (|Z y| + C * M) / b ≤ ∫ y in α..β, (|Z y| + C * M) / b :=
            integral_mono_interval hu.1 huv hv.2 (Filter.Eventually.of_forall hnn) hint_full
        _ = (∫ y in α..β, |Z y|) / b + C * M * (β - α) / b := by
            rw [intervalIntegral.integral_div, integral_add hint_abs intervalIntegrable_const,
              intervalIntegral.integral_const, smul_eq_mul]
            ring
    rcases le_total x₀ x with h | h
    · have := (hsub hx₀ hx h).trans (hfull hx₀ hx h)
      rwa [hzero, sub_zero] at this
    · have := (hsub hx hx₀ h).trans (hfull hx hx₀ h)
      rwa [hzero, zero_sub, abs_neg] at this
  -- absorb the `C M` term
  have hMbound : M ≤ 2 / b * ∫ y in α..β, |Z y| := by
    have h1 := hpoint m hm
    rw [← hM] at h1
    have h2 : C * M * (β - α) / b ≤ M / 2 := by
      rw [div_le_iff₀ hb]
      nlinarith
    have hIZ : 0 ≤ ∫ y in α..β, |Z y| := integral_nonneg hαβ (fun y _ => abs_nonneg _)
    rw [show 2 / b * ∫ y in α..β, |Z y| = 2 * ((∫ y in α..β, |Z y|) / b) by ring]
    linarith
  exact fun x hx => (hle_M x hx).trans hMbound

/-- **Quadratic form.** `∫_I s² ≤ (4/b²)(β − α)²∫_I Z²`. -/
theorem integral_sq_le_of_firstOrderFilter (hb : 0 < b) (hC : 0 ≤ C) (hαβ : α ≤ β)
    (hlen : 2 * C * (β - α) ≤ b)
    (hs : ∀ x ∈ Icc α β, HasDerivAt s (-(Z x + c x * s x) / b) x)
    (hZ : ContinuousOn Z (Icc α β)) (hcc : ContinuousOn c (Icc α β))
    (hc : ∀ x ∈ Icc α β, |c x| ≤ C) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc α β) (hzero : s x₀ = 0) :
    ∫ x in α..β, s x ^ 2 ≤ 4 / b ^ 2 * (β - α) ^ 2 * ∫ x in α..β, Z x ^ 2 := by
  have hpt := abs_le_of_firstOrderFilter hb hC hαβ hlen hs hZ hcc hc hx₀ hzero
  set J := ∫ y in α..β, |Z y| with hJ
  have hJ0 : 0 ≤ J := integral_nonneg hαβ (fun y _ => abs_nonneg _)
  have hscont : ContinuousOn s (Icc α β) := fun x hx => (hs x hx).continuousAt.continuousWithinAt
  -- pointwise square bound and integration
  have hsq : ∫ x in α..β, s x ^ 2 ≤ (β - α) * (2 / b * J) ^ 2 := by
    have := integral_mono_on hαβ ((hscont.pow 2).intervalIntegrable_of_Icc hαβ)
      (intervalIntegrable_const (μ := volume) (c := (2 / b * J) ^ 2)) (fun x hx => by
        have h := hpt x hx
        have h0 : 0 ≤ 2 / b * J := by positivity
        calc s x ^ 2 = |s x| ^ 2 := (sq_abs _).symm
          _ ≤ (2 / b * J) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2)
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  -- Cauchy–Schwarz: `J² ≤ (β − α) ∫ Z²`
  have hCS : J ^ 2 ≤ (β - α) * ∫ x in α..β, Z x ^ 2 := by
    rcases eq_or_lt_of_le hαβ with h | h
    · subst h; simp [hJ]
    have hℓ : 0 < β - α := sub_pos.mpr h
    set μ := J / (β - α)
    have hintZ2 : IntervalIntegrable (fun x => Z x ^ 2) volume α β :=
      (hZ.pow 2).intervalIntegrable_of_Icc hαβ
    have hintA : IntervalIntegrable (fun x => |Z x|) volume α β :=
      (continuous_abs.comp_continuousOn hZ).intervalIntegrable_of_Icc hαβ
    have hnn : 0 ≤ ∫ x in α..β, (|Z x| - μ) ^ 2 :=
      integral_nonneg hαβ (fun x _ => sq_nonneg _)
    have hexp : ∫ x in α..β, (|Z x| - μ) ^ 2 =
        (∫ x in α..β, Z x ^ 2) - 2 * μ * J + μ ^ 2 * (β - α) := by
      have hpt' : (fun x => (|Z x| - μ) ^ 2) =
          fun x => Z x ^ 2 - 2 * μ * |Z x| + μ ^ 2 := by
        funext x; rw [sub_sq, sq_abs]; ring
      rw [hpt', integral_add (hintZ2.sub (hintA.const_mul _)) intervalIntegrable_const,
        integral_sub hintZ2 (hintA.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at hnn
    have hμ : μ * (β - α) = J := div_mul_cancel₀ J hℓ.ne'
    nlinarith [hμ]
  calc ∫ x in α..β, s x ^ 2 ≤ (β - α) * (2 / b * J) ^ 2 := hsq
    _ = 4 / b ^ 2 * (β - α) * J ^ 2 := by ring
    _ ≤ 4 / b ^ 2 * (β - α) * ((β - α) * ∫ x in α..β, Z x ^ 2) := by
        gcongr
    _ = 4 / b ^ 2 * (β - α) ^ 2 * ∫ x in α..β, Z x ^ 2 := by ring

end GaloisForLFunctions.HTGeometry
