import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Infinite products near one

A product `∏ (1 + u_i)` differs from `1` by at most `exp(∑ ‖u_i‖) - 1`.  The finite statement is an
induction on the index set, the infinite one passes to the limit along the finite partial products.

This is the estimate that turns a summable family of small factors into a quantitative degeneration
statement: when the total mass `∑ ‖u_i‖` is `O(t)`, the whole product is `1 + O(t)`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite product of factors near one stays near one. -/
theorem norm_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hnorm : ‖∏ i ∈ s, (1 + u i)‖ ≤ ∏ i ∈ s, (1 + ‖u i‖) := by
        rw [norm_prod]
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        calc ‖1 + u i‖ ≤ ‖(1 : ℂ)‖ + ‖u i‖ := norm_add_le _ _
          _ = 1 + ‖u i‖ := by rw [norm_one]
      have hpos : (0 : ℝ) ≤ ∏ i ∈ s, (1 + ‖u i‖) :=
        Finset.prod_nonneg fun i _ => by positivity
      have hsplit : (1 + u a) * ∏ i ∈ s, (1 + u i) - 1
          = u a * ∏ i ∈ s, (1 + u i) + ((∏ i ∈ s, (1 + u i)) - 1) := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hfirst : ‖u a * ∏ i ∈ s, (1 + u i)‖ ≤ ‖u a‖ * ∏ i ∈ s, (1 + ‖u i‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      nlinarith [ih]

/-- A finite product of factors near one is bounded by the exponential of the total mass. -/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∏ i ∈ s, (1 + a i)) ≤ Real.exp (∑ i ∈ s, a i) := by
  classical
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun i hi => by linarith [ha i hi]) fun i _ => ?_
  have := Real.add_one_le_exp (a i)
  linarith

/-- **An infinite product of factors near one stays near one.**  The deviation is bounded by the
exponential of the total mass of the factors. -/
theorem norm_tprod_one_add_sub_one_le {ι : Type*} {u : ι → ℂ} {P : ℂ}
    (hP : HasProd (fun i => 1 + u i) P) (hsum : Summable fun i => ‖u i‖)
    {S : ℝ} (hS : ∑' i, ‖u i‖ ≤ S) : ‖P - 1‖ ≤ Real.exp S - 1 := by
  have htend : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + u i)) atTop (nhds P) := hP
  have hlim : Tendsto (fun s : Finset ι => ‖(∏ i ∈ s, (1 + u i)) - 1‖) atTop (nhds ‖P - 1‖) :=
    (htend.sub tendsto_const_nhds).norm
  refine le_of_tendsto hlim (Eventually.of_forall fun s => ?_)
  calc ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 :=
        norm_prod_one_add_sub_one_le s u
    _ ≤ Real.exp (∑ i ∈ s, ‖u i‖) - 1 := by
        have := prod_one_add_le_exp_sum s (fun i => ‖u i‖) fun i _ => norm_nonneg _
        linarith
    _ ≤ Real.exp S - 1 := by
        have hle : ∑ i ∈ s, ‖u i‖ ≤ S :=
          le_trans (hsum.sum_le_tsum s fun i _ => norm_nonneg _) hS
        have := Real.exp_le_exp.mpr hle
        linarith

/-- **An infinite product with one distinguished factor.**  Splitting off the factor at `b`, the
product differs from that factor by at most the exponential of the mass of the remaining ones.  The
argument runs on finite partial products, so no group structure on the target is needed. -/
theorem norm_hasProd_sub_single_le {ι : Type*} [DecidableEq ι] {u : ι → ℂ} {P : ℂ} (b : ι)
    (hP : HasProd (fun i => 1 + u i) P) (hsum : Summable fun i => ‖u i‖)
    {S : ℝ} (hS : ∑' i, (if i = b then 0 else ‖u i‖) ≤ S) :
    ‖P - (1 + u b)‖ ≤ ‖1 + u b‖ * (Real.exp S - 1) := by
  classical
  have hsumIte : Summable (fun i => if i = b then 0 else ‖u i‖) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsum
    · by_cases h : i = b
      · rw [if_pos h]
      · rw [if_neg h]
        exact norm_nonneg _
    · by_cases h : i = b
      · rw [if_pos h]
        exact norm_nonneg _
      · rw [if_neg h]
  have hev : ∀ s : Finset ι, b ∈ s →
      ‖(∏ i ∈ s, (1 + u i)) - (1 + u b)‖ ≤ ‖1 + u b‖ * (Real.exp S - 1) := by
    intro s hb
    rw [← Finset.mul_prod_erase s _ hb]
    have hfac : (1 + u b) * (∏ i ∈ s.erase b, (1 + u i)) - (1 + u b)
        = (1 + u b) * ((∏ i ∈ s.erase b, (1 + u i)) - 1) := by ring
    rw [hfac, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hmass : ∑ i ∈ s.erase b, ‖u i‖ ≤ S := by
      have hrw : ∑ i ∈ s.erase b, ‖u i‖
          = ∑ i ∈ s.erase b, (if i = b then 0 else ‖u i‖) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [if_neg (Finset.mem_erase.mp hi).1]
      rw [hrw]
      refine le_trans ?_ hS
      refine hsumIte.sum_le_tsum _ fun i _ => ?_
      by_cases h : i = b
      · rw [if_pos h]
      · rw [if_neg h]
        exact norm_nonneg _
    calc ‖(∏ i ∈ s.erase b, (1 + u i)) - 1‖
        ≤ (∏ i ∈ s.erase b, (1 + ‖u i‖)) - 1 := norm_prod_one_add_sub_one_le _ u
      _ ≤ Real.exp (∑ i ∈ s.erase b, ‖u i‖) - 1 := by
          have := prod_one_add_le_exp_sum (s.erase b) (fun i => ‖u i‖) fun i _ => norm_nonneg _
          linarith
      _ ≤ Real.exp S - 1 := by
          have := Real.exp_le_exp.mpr hmass
          linarith
  have htend : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + u i)) atTop (nhds P) := hP
  have hlim : Tendsto (fun s : Finset ι => ‖(∏ i ∈ s, (1 + u i)) - (1 + u b)‖) atTop
      (nhds ‖P - (1 + u b)‖) := (htend.sub tendsto_const_nhds).norm
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨{b}, fun s hs => ?_⟩)
  exact hev s (hs (Finset.mem_singleton_self b))

end

end GaloisForLFunctions.HTGeometry
