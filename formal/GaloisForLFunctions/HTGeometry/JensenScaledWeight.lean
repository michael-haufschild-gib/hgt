import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass

/-!
# The rescaled Jensen polynomial and its weights

Substituting `X ↦ X/d` in the degree-`d` Jensen polynomial replaces the descending factorial
`d^{(i)}` by the weight `d^{(i)}/d^i = ∏_{k<i} (1 - k/d)`, which lies in `[0,1]` and tends to `1`
as `d → ∞`.  Real-rootedness survives the substitution.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Splitting is preserved by the substitution `X ↦ a·X` for `a ≠ 0`. -/
theorem splits_comp_C_mul_X {K : Type*} [Field K] {f : K[X]} (hf : f.Splits) {a : K} (ha : a ≠ 0) :
    (f.comp (C a * X)).Splits := by
  classical
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.1 hf
  have hprod : ∀ s : Multiset K,
      ((s.map fun r => X - C r).prod).comp (C a * X)
        = (s.map fun r => C a * X - C r).prod := by
    intro s
    refine Multiset.induction_on s (by simp) ?_
    intro r t ih
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, sub_comp, X_comp, C_comp, ih]
  have hsplits : ∀ s : Multiset K, ((s.map fun r => C a * X - C r).prod).Splits := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro r t ih
      rw [Multiset.map_cons, Multiset.prod_cons]
      refine Polynomial.Splits.mul ?_ ih
      have h2 : C a * X - C r = C a * (X - C (a⁻¹ * r)) := by
        rw [mul_sub, ← C_mul, mul_inv_cancel_left₀ ha]
      rw [h2]
      exact (Polynomial.Splits.C _).mul (Polynomial.Splits.X_sub_C _)
  rw [hm, mul_comp, C_comp, hprod]
  exact (Polynomial.Splits.C _).mul (hsplits m)

/-- The weight `d^{(i)}/d^i` attached to the degree-`i` coefficient of the rescaled Jensen
polynomial. -/
def jensenWeight (d i : ℕ) : ℝ := (d.descFactorial i : ℝ) / (d : ℝ) ^ i

theorem jensenWeight_eq_prod (d i : ℕ) :
    jensenWeight d i = ∏ k ∈ Finset.range i, ((d - k : ℕ) : ℝ) / (d : ℝ) := by
  have hcard : ((d : ℝ)) ^ i = ∏ _k ∈ Finset.range i, (d : ℝ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [jensenWeight, Nat.descFactorial_eq_prod_range, Nat.cast_prod, hcard,
    ← Finset.prod_div_distrib]

theorem jensenWeight_nonneg (d i : ℕ) : 0 ≤ jensenWeight d i := by
  rw [jensenWeight]
  positivity

theorem jensenWeight_le_one (d i : ℕ) : jensenWeight d i ≤ 1 := by
  rw [jensenWeight_eq_prod]
  refine Finset.prod_le_one (fun k _ => by positivity) fun k _ => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [div_le_one (by exact_mod_cast hd)]
    exact_mod_cast Nat.sub_le d k

theorem jensenWeight_eq_zero_of_lt {d i : ℕ} (h : d < i) : jensenWeight d i = 0 := by
  rw [jensenWeight, Nat.descFactorial_eq_zero_iff_lt.2 h]
  simp

theorem tendsto_natSub_div (k : ℕ) :
    Tendsto (fun d : ℕ => ((d - k : ℕ) : ℝ) / (d : ℝ)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun d : ℕ => (k : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun d : ℕ => 1 - (k : ℝ) / (d : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h0
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max k 1)] with d hd
  have hk : k ≤ d := le_trans (le_max_left _ _) hd
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) hd
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Nat.cast_sub hk]
  field_simp

theorem tendsto_jensenWeight (i : ℕ) :
    Tendsto (fun d : ℕ => jensenWeight d i) atTop (𝓝 1) := by
  have hprod : Tendsto (fun d : ℕ => ∏ k ∈ Finset.range i, ((d - k : ℕ) : ℝ) / (d : ℝ))
      atTop (𝓝 (∏ _k ∈ Finset.range i, (1 : ℝ))) :=
    tendsto_finsetProd _ fun k _ => tendsto_natSub_div k
  rw [Finset.prod_const_one] at hprod
  exact hprod.congr fun d => (jensenWeight_eq_prod d i).symm

/-- The degree-`d` Jensen polynomial rescaled by `1/d`. -/
def jensenScaled (c : ℕ → ℝ) (d : ℕ) : ℝ[X] := (jensenPoly c d).comp (C ((d : ℝ)⁻¹) * X)

theorem splits_jensenScaled {c : ℕ → ℝ} {d : ℕ} (hd : d ≠ 0) (h : (jensenPoly c d).Splits) :
    (jensenScaled c d).Splits :=
  splits_comp_C_mul_X h (inv_ne_zero (Nat.cast_ne_zero.2 hd))

theorem polyEvalC_jensenPoly (c : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    polyEvalC (jensenPoly c d) z
      = ∑ i ∈ Finset.range (d + 1), ((c i * (d.descFactorial i : ℝ) : ℝ) : ℂ) * z ^ i := by
  rw [polyEvalC, jensenPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem polyEvalC_jensenScaled (c : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    polyEvalC (jensenScaled c d) z
      = ∑ i ∈ Finset.range (d + 1), ((c i * jensenWeight d i : ℝ) : ℂ) * z ^ i := by
  have hcomp : polyEvalC (jensenScaled c d) z
      = polyEvalC (jensenPoly c d) ((((d : ℝ)⁻¹ : ℝ) : ℂ) * z) := by
    rw [polyEvalC, jensenScaled, Polynomial.aeval_comp, polyEvalC]
    simp
  rw [hcomp, polyEvalC_jensenPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, jensenWeight]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
