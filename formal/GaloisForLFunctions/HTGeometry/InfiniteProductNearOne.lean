import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable

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

/-! ## Comparing two products of factors near one -/

/-- A finite comparison of two products of factors near one. -/
theorem norm_prod_one_add_sub_prod_one_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖
      ≤ (∑ i ∈ s, ‖a i - b i‖) * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      have hmassnn : (0 : ℝ) ≤ ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) :=
        Finset.prod_nonneg fun i _ => by positivity
      have hprodA : ‖∏ i ∈ s, (1 + a i)‖ ≤ ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
        rw [norm_prod]
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        calc ‖1 + a i‖ ≤ ‖(1 : ℂ)‖ + ‖a i‖ := norm_add_le _ _
          _ = 1 + ‖a i‖ := by rw [norm_one]
          _ ≤ 1 + ‖a i‖ + ‖b i‖ := by linarith [norm_nonneg (b i)]
      have hdiffnn : (0 : ℝ) ≤ ∑ i ∈ s, ‖a i - b i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx,
        Finset.prod_insert hx]
      have hsplit : (1 + a x) * ∏ i ∈ s, (1 + a i) - (1 + b x) * ∏ i ∈ s, (1 + b i)
          = (a x - b x) * ∏ i ∈ s, (1 + a i)
            + (1 + b x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)) := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖(a x - b x) * ∏ i ∈ s, (1 + a i)‖
          ≤ ‖a x - b x‖ * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hprodA (norm_nonneg _)
      have h2 : ‖(1 + b x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i))‖
          ≤ (1 + ‖b x‖) * ((∑ i ∈ s, ‖a i - b i‖) * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) := by
        rw [norm_mul]
        refine mul_le_mul ?_ ih (norm_nonneg _) (by positivity)
        calc ‖1 + b x‖ ≤ ‖(1 : ℂ)‖ + ‖b x‖ := norm_add_le _ _
          _ = 1 + ‖b x‖ := by rw [norm_one]
      calc ‖(a x - b x) * ∏ i ∈ s, (1 + a i)‖
            + ‖(1 + b x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i))‖
          ≤ ‖a x - b x‖ * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)
            + (1 + ‖b x‖) * ((∑ i ∈ s, ‖a i - b i‖) * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) :=
            add_le_add h1 h2
        _ ≤ (‖a x - b x‖ + ∑ i ∈ s, ‖a i - b i‖)
              * ((1 + ‖a x‖ + ‖b x‖) * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) := by
            nlinarith [hmassnn, hdiffnn, norm_nonneg (a x), norm_nonneg (b x),
              norm_nonneg (a x - b x),
              mul_nonneg hmassnn (mul_nonneg (norm_nonneg (a x - b x)) (norm_nonneg (a x))),
              mul_nonneg hmassnn (mul_nonneg (norm_nonneg (a x - b x)) (norm_nonneg (b x))),
              mul_nonneg hmassnn (mul_nonneg hdiffnn (norm_nonneg (a x)))]

/-- **Comparing two infinite products of factors near one.**  The deviation is the total distance
between the factors, amplified by the exponential of the combined mass. -/
theorem norm_tprod_one_add_sub_tprod_one_add_le {ι : Type*} (a b : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (hb : Summable fun i => ‖b i‖) :
    ‖(∏' i, (1 + a i)) - ∏' i, (1 + b i)‖
      ≤ (∑' i, ‖a i - b i‖) * Real.exp (∑' i, (‖a i‖ + ‖b i‖)) := by
  have hdiff : Summable fun i => ‖a i - b i‖ :=
    (ha.add hb).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => norm_sub_le _ _
  have hmass : Summable fun i => ‖a i‖ + ‖b i‖ := ha.add hb
  have hA : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + a i)) Filter.atTop
      (nhds (∏' i, (1 + a i))) := (multipliable_one_add_of_summable ha).hasProd
  have hB : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + b i)) Filter.atTop
      (nhds (∏' i, (1 + b i))) := (multipliable_one_add_of_summable hb).hasProd
  have hleft : Filter.Tendsto (fun s : Finset ι =>
      ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖) Filter.atTop
      (nhds ‖(∏' i, (1 + a i)) - ∏' i, (1 + b i)‖) := (hA.sub hB).norm
  refine le_of_tendsto hleft (Filter.Eventually.of_forall fun s => ?_)
  refine (norm_prod_one_add_sub_prod_one_add_le s a b).trans ?_
  have hsum : (∑ i ∈ s, ‖a i - b i‖) ≤ ∑' i, ‖a i - b i‖ :=
    hdiff.sum_le_tsum s fun i _ => norm_nonneg _
  have hprod : (∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) ≤ Real.exp (∑' i, (‖a i‖ + ‖b i‖)) := by
    refine le_trans ?_ (Real.exp_le_exp.mpr (hmass.sum_le_tsum s fun i _ => by positivity))
    have h := prod_one_add_le_exp_sum s (fun i => ‖a i‖ + ‖b i‖) fun i _ => by positivity
    refine le_trans (le_of_eq ?_) h
    exact Finset.prod_congr rfl fun i _ => by ring
  have hnn1 : (0 : ℝ) ≤ ∑ i ∈ s, ‖a i - b i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) :=
    Finset.prod_nonneg fun i _ => by positivity
  exact mul_le_mul hsum hprod hnn2 (le_trans hnn1 hsum)

end

end GaloisForLFunctions.HTGeometry
