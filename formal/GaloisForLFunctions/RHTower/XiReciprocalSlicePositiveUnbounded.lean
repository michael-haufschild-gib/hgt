import GaloisForLFunctions.RHTower.XiReciprocalSliceDominance
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Reciprocal slice positivity holds on intervals of arbitrarily large height

**Theorem** (`exists_interval_xiReciprocalSlicePositive_above`).  For every `T` there is an open
interval `(a, b)` with `T < a < b` such that at every height `t ∈ (a, b)` we have `Ξ(t) ≠ 0`, and
every Taylor coefficient of `1/(Ξ(t+σ)Ξ(t−σ))` at `0` is nonnegative.

Superlinearly many simple critical zeros (`eventually_superlinear_xiSimpleCriticalZeroCount`, from
the two-thirds theorem) give one above every height.  A simple critical zero `½ + iγ` is carried by
exactly one zero copy, at the real spectral point `γ`.  The dominance law
(`exists_xiReciprocalSlicePositive_near_simple_real_zero`) then gives positivity on a punctured
neighbourhood of `γ`.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A simple zero of `ξ` on the critical line is carried by exactly one zero copy, whose spectral
point is the real ordinate. -/
theorem exists_unique_xiZeroCopy_of_simple_critical {z : ℂ} (hre : z.re = 1 / 2)
    (hord : (analyticOrderAt xi z).toNat = 1) :
    ∃ q₀ : XiZeroCopy, xiSpectralPoint q₀ = (z.im : ℂ) ∧
      ∀ q, xiSpectralPoint q = (z.im : ℂ) → q = q₀ := by
  have hA : AnalyticAt ℂ xi z := xi_differentiable.analyticAt z
  have hord1 : analyticOrderAt xi z = 1 := by
    have hne : analyticOrderAt xi z ≠ ⊤ := by
      intro h
      rw [h] at hord
      simp at hord
    rw [← ENat.coe_toNat hne, hord]
    rfl
  have hdiv : (MeromorphicOn.divisor xi Set.univ) z = 1 := by
    rw [MeromorphicOn.divisor_apply (fun w _ => (xi_differentiable.analyticAt w).meromorphicAt)
      (Set.mem_univ z), hA.meromorphicOrderAt_eq, hord1]
    rfl
  have hsupp : z ∈ (MeromorphicOn.divisor xi Set.univ).support := by
    rw [Function.mem_support, hdiv]
    exact one_ne_zero
  set ρ : XiDivisorSupport := ⟨z, hsupp⟩ with hρ
  have hcard : Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) = 1 := by
    simp [hρ, hdiv]
  have hspec : ∀ q : XiZeroCopy, xiSpectralPoint q = (z.im : ℂ) → (q.1 : ℂ) = z := by
    intro q hq
    unfold xiSpectralPoint at hq
    have h1 : (q.1 : ℂ) = 1 / 2 + (z.im : ℂ) * I := by
      have : ((q.1 : ℂ) - 1 / 2) = (z.im : ℂ) * I := by
        have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
        calc ((q.1 : ℂ) - 1 / 2) = ((q.1 : ℂ) - 1 / 2) * (-I) * I := by
              rw [mul_assoc, hI, mul_one]
          _ = (z.im : ℂ) * I := by rw [hq]
      linear_combination this
    rw [h1]
    apply Complex.ext <;> simp [hre]
  refine ⟨⟨ρ, ⟨0, by rw [hcard]; norm_num⟩⟩, ?_, ?_⟩
  · unfold xiSpectralPoint
    simp only [hρ]
    apply Complex.ext <;> simp [hre]
  · intro q hq
    have hq1 : q.1 = ρ := Subtype.ext (hspec q hq)
    obtain ⟨q1, q2⟩ := q
    simp only at hq1
    subst hq1
    congr 1
    have : Subsingleton (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))) := by
      rw [hcard]
      infer_instance
    exact Subsingleton.elim _ _

/-- **Reciprocal slice positivity on intervals above every height.** -/
theorem exists_interval_xiReciprocalSlicePositive_above (T : ℝ) :
    ∃ a b : ℝ, T < a ∧ a < b ∧ ∀ t ∈ Set.Ioo a b, XiC t ≠ 0 ∧ XiReciprocalSlicePositive t := by
  classical
  -- a simple critical zero above height `T`
  obtain ⟨z, hzT, hre, hz, hord⟩ : ∃ z : ℂ, T < z.im ∧ z.re = 1 / 2 ∧ xi z = 0 ∧
      (analyticOrderAt xi z).toNat = 1 := by
    set c := xiSimpleCriticalZeroCount (max T 1) with hc
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
      ((eventually_superlinear_xiSimpleCriticalZeroCount).and
        (eventually_gt_atTop (max (max T 1) (Real.exp (72 * Real.pi * (c + 1))))))
    obtain ⟨hcount, hT₁big⟩ := hT₁ (T₁ + 1) (by linarith)
    have hT₁gt : max (max T 1) (Real.exp (72 * Real.pi * (c + 1))) < T₁ + 1 := hT₁big
    have hexp_lt : Real.exp (72 * Real.pi * (c + 1)) < T₁ + 1 :=
      lt_of_le_of_lt (le_max_right _ _) hT₁gt
    have hT1pos : 0 < T₁ + 1 := lt_trans (Real.exp_pos _) hexp_lt
    have hlog : 72 * Real.pi * (c + 1) < Real.log (T₁ + 1) := by
      rw [← Real.exp_lt_exp, Real.exp_log hT1pos]
      exact hexp_lt
    have h1 : 1 < T₁ + 1 := lt_of_le_of_lt (le_max_right T 1)
      (lt_of_le_of_lt (le_max_left _ _) hT₁gt)
    have hgrow : (c : ℝ) < xiSimpleCriticalZeroCount (T₁ + 1) := by
      have hpos : 0 < 1 / (72 * Real.pi) * (T₁ + 1) := by positivity
      calc (c : ℝ) < 1 / (72 * Real.pi) * (72 * Real.pi * (c + 1)) := by
            field_simp
            linarith
        _ ≤ 1 / (72 * Real.pi) * (T₁ + 1) * Real.log (T₁ + 1) := by
            have := hlog.le
            have h1' : (1 : ℝ) ≤ T₁ + 1 := h1.le
            have hp : 0 < 1 / (72 * Real.pi) := by positivity
            have hlogpos : 0 < Real.log (T₁ + 1) := Real.log_pos h1
            have h2 : 72 * Real.pi * (c + 1) ≤ (T₁ + 1) * Real.log (T₁ + 1) :=
              le_trans this (le_mul_of_one_le_left hlogpos.le h1')
            calc 1 / (72 * Real.pi) * (72 * Real.pi * (c + 1))
                ≤ 1 / (72 * Real.pi) * ((T₁ + 1) * Real.log (T₁ + 1)) :=
                  mul_le_mul_of_nonneg_left h2 hp.le
              _ = 1 / (72 * Real.pi) * (T₁ + 1) * Real.log (T₁ + 1) := by ring
        _ ≤ xiSimpleCriticalZeroCount (T₁ + 1) := hcount
    -- a counted zero that is not counted at `max T 1`
    by_contra hnone
    push Not at hnone
    have hsub : (stripFinsetPos (T₁ + 1)).filter
        (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) ⊆
        (stripFinsetPos (max T 1)).filter
          (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) := by
      intro w hw
      rw [Finset.mem_filter, mem_stripFinsetPos] at hw ⊢
      obtain ⟨⟨h1, h2, h3, _, h5⟩, h6, h7⟩ := hw
      refine ⟨⟨h1, h2, h3, ?_, h5⟩, h6, h7⟩
      by_contra hgt
      push Not at hgt
      have := hnone w (lt_of_le_of_lt (le_max_left T 1) hgt) h6 h5
      exact this h7
    have hle : xiSimpleCriticalZeroCount (T₁ + 1) ≤ c := by
      rw [hc]
      exact Finset.card_le_card hsub
    have : (xiSimpleCriticalZeroCount (T₁ + 1) : ℝ) ≤ c := by exact_mod_cast hle
    linarith
  obtain ⟨q₀, hq₀, huniq⟩ := exists_unique_xiZeroCopy_of_simple_critical hre hord
  obtain ⟨ε, hε, hpos⟩ := exists_xiReciprocalSlicePositive_near_simple_real_zero q₀ hq₀ huniq
  refine ⟨z.im, z.im + ε, hzT, by linarith, fun t ht => hpos t ?_ ?_⟩
  · rw [abs_pos, sub_ne_zero]
    exact ne_of_gt ht.1
  · rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]

end

end RHTower
