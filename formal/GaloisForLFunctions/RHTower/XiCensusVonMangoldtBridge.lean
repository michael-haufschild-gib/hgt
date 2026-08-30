import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging

/-!
# The census is the Riemann–von Mangoldt counting function

The horizontal-fibre census `N(T) = xiPosZeroCount T` sums the `ξ`-multiplicities over the strip
zeros with ordinate in `(0,T]`; the counting function `xiZeroCount T` sums the `ξ`-divisor over the
same region.  They are the same integer, because the divisor support is exactly the zero set and
every `ξ`-zero lies in the open strip.

Consequently the unconditional Riemann–von Mangoldt asymptotic applies to the census, and any
*positive* lower density of simple critical zeros upgrades to a *superlinear* lower bound on their
count:

```text
c ≤ liminf N₀,s(T)/N(T),  c > 0   ⟹   ∃ c' > 0, ∀ᶠ T,  c'·T log T ≤ N₀,s(T).
```

This is the exact statement consumed by the bounded-support Weil uniqueness theorem, produced from
the exact statement supplied by a positive-proportion theorem.  The two are therefore one gate.
-/

open Filter Topology Complex

noncomputable section

namespace RHTower

/-- The census index set is the divisor support with positive ordinate. -/
theorem stripFinsetPos_eq_image {T : ℝ} :
    stripFinsetPos T = (xiSupportsPos T).image (fun ρ : XiDivisorSupport => (ρ : ℂ)) := by
  classical
  ext z
  simp only [Finset.mem_image]
  constructor
  · intro hz
    rw [mem_stripFinsetPos] at hz
    obtain ⟨_, _, him0, himT, hzero⟩ := hz
    have hne : (MeromorphicOn.divisor xi Set.univ) z ≠ 0 := by
      rw [xi_divisor_apply_of_mem (Set.mem_univ z)]
      exact_mod_cast xi_order_toNat_ne_zero hzero
    refine ⟨⟨z, Function.mem_support.mpr hne⟩, ?_, rfl⟩
    rw [mem_xiSupportsPos]
    exact ⟨by rw [abs_of_pos him0]; exact himT, him0⟩
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mem_xiSupportsPos] at hρ
    have hzero : xi (ρ : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support ρ
    obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hzero
    rw [mem_stripFinsetPos]
    exact ⟨h0, h1, hρ.2, by have := (abs_le.mp hρ.1).2; linarith, hzero⟩

/-- **The census is the counting function.** -/
theorem xiPosZeroCount_eq_xiZeroCount {T : ℝ} (hT : 0 ≤ T) :
    (xiPosZeroCount T : ℤ) = xiZeroCount T := by
  classical
  rw [xiZeroCount_eq_pos_sum hT, xiPosZeroCount, stripFinsetPos_eq_image,
    Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
  push_cast
  exact Finset.sum_congr rfl fun ρ _ => by
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat]

/-- **The census grows superlinearly.**  An explicit unconditional lower bound. -/
theorem eventually_inv_four_pi_mul_le_xiPosZeroCount :
    ∀ᶠ T : ℝ in atTop, 1 / (4 * Real.pi) * (T * Real.log T) ≤ (xiPosZeroCount T : ℝ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨T₀, hT₀, hclose⟩ := exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (4 : ℝ)] with T hT hT4
  have hL : 0 ≤ T * Real.log T := by
    have hlog : (0 : ℝ) ≤ Real.log T := Real.log_nonneg (by linarith)
    have : (0 : ℝ) ≤ T := by linarith
    positivity
  have habs := abs_le.mp (hclose T hT)
  have hcast : ((xiPosZeroCount T : ℤ) : ℝ) = ((xiZeroCount T : ℤ) : ℝ) :=
    congrArg (fun n : ℤ => (n : ℝ)) (xiPosZeroCount_eq_xiZeroCount (by linarith))
  have hsplit : 1 / (2 * Real.pi) * (T * Real.log T)
      - 1 / (4 * Real.pi) * (T * Real.log T)
      = 1 / (4 * Real.pi) * (T * Real.log T) := by
    rw [← sub_mul]
    congr 1
    field_simp
    ring
  push_cast at hcast
  rw [hcast]
  linarith [habs.1, hsplit]

/-- **One gate for two cards.**  A positive lower density of simple critical zeros gives a
superlinear lower bound on their count, in exactly the form the bounded-support Weil uniqueness
theorem consumes. -/
theorem exists_superlinear_of_le_liminf_xiSimpleCriticalRatio {c : ℝ} (hc : 0 < c)
    (h : c ≤ liminf xiSimpleCriticalRatio atTop) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ T : ℝ in atTop,
      c' * T * Real.log T ≤ (xiSimpleCriticalZeroCount T : ℝ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨c / (8 * Real.pi), by positivity, ?_⟩
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSimpleCriticalRatio_nonneg T⟩
  have hlt : c / 2 < liminf xiSimpleCriticalRatio atTop := by linarith
  have e1 := eventually_lt_of_lt_liminf hlt hbdd
  filter_upwards [e1, eventually_inv_four_pi_mul_le_xiPosZeroCount,
    eventually_ge_atTop (4 : ℝ)] with T hT1 hT2 hT4
  have hlog : (0 : ℝ) < Real.log T := Real.log_pos (by linarith)
  have hT0 : (0 : ℝ) < T := by linarith
  have hL : (0 : ℝ) < T * Real.log T := by positivity
  have hlow : (0 : ℝ) < 1 / (4 * Real.pi) * (T * Real.log T) := by positivity
  have hN : (0 : ℝ) < (xiPosZeroCount T : ℝ) := lt_of_lt_of_le hlow hT2
  rw [xiSimpleCriticalRatio, lt_div_iff₀ hN] at hT1
  have hstep : c / 2 * (1 / (4 * Real.pi) * (T * Real.log T))
      ≤ c / 2 * (xiPosZeroCount T : ℝ) :=
    mul_le_mul_of_nonneg_left hT2 (by positivity)
  have heq : c / 2 * (1 / (4 * Real.pi) * (T * Real.log T))
      = c / (8 * Real.pi) * T * Real.log T := by
    field_simp
    ring
  rw [← heq]
  linarith

end RHTower
