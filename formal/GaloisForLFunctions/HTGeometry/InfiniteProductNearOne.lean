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

/-! ## First-order control and the derivative at the origin -/

/-- A finite product of factors near one, to first order. -/
theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + u i)) - 1 - ∑ i ∈ s, u i‖
      ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 - ∑ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hnn : (0 : ℝ) ≤ ∏ i ∈ s, (1 + ‖u i‖) := Finset.prod_nonneg fun i _ => by positivity
      have hone : (1 : ℝ) ≤ ∏ i ∈ s, (1 + ‖u i‖) := by
        have h := Finset.prod_le_prod (s := s) (f := fun _ : ι => (1 : ℝ))
          (g := fun i => 1 + ‖u i‖) (fun i _ => zero_le_one)
          (fun i _ => by linarith [norm_nonneg (u i)])
        simpa using h
      have hpm : ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖u i‖)) - 1 :=
        norm_prod_one_add_sub_one_le s u
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        Finset.sum_insert ha]
      have hsplit : (1 + u a) * (∏ i ∈ s, (1 + u i)) - 1 - (u a + ∑ i ∈ s, u i)
          = u a * ((∏ i ∈ s, (1 + u i)) - 1)
            + ((∏ i ∈ s, (1 + u i)) - 1 - ∑ i ∈ s, u i) := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖u a * ((∏ i ∈ s, (1 + u i)) - 1)‖
          ≤ ‖u a‖ * ((∏ i ∈ s, (1 + ‖u i‖)) - 1) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hpm (norm_nonneg _)
      nlinarith [h1, ih]

/-- **First-order control of an infinite product of factors near one.** -/
theorem norm_tprod_one_add_sub_one_sub_tsum_le {ι : Type*} {u : ι → ℂ}
    (hu : Summable fun i => ‖u i‖) :
    ‖(∏' i, (1 + u i)) - 1 - ∑' i, u i‖
      ≤ (∑' i, ‖u i‖) ^ 2 * Real.exp (∑' i, ‖u i‖) := by
  set S : ℝ := ∑' i, ‖u i‖ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun i => norm_nonneg _
  have husum : Summable u := hu.of_norm
  have hA : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + u i)) atTop (𝓝 (∏' i, (1 + u i))) :=
    (multipliable_one_add_of_summable hu).hasProd
  have hB : Tendsto (fun s : Finset ι => ∑ i ∈ s, u i) atTop (𝓝 (∑' i, u i)) := husum.hasSum
  have hleft : Tendsto (fun s : Finset ι =>
      ‖(∏ i ∈ s, (1 + u i)) - 1 - ∑ i ∈ s, u i‖) atTop
      (𝓝 ‖(∏' i, (1 + u i)) - 1 - ∑' i, u i‖) :=
    ((hA.sub tendsto_const_nhds).sub hB).norm
  refine le_of_tendsto hleft (Eventually.of_forall fun s => ?_)
  refine (norm_prod_one_add_sub_one_sub_sum_le s u).trans ?_
  have hps : (∏ i ∈ s, (1 + ‖u i‖)) ≤ Real.exp (∑ i ∈ s, ‖u i‖) :=
    prod_one_add_le_exp_sum s (fun i => ‖u i‖) fun i _ => norm_nonneg _
  have hss : (∑ i ∈ s, ‖u i‖) ≤ S := hu.sum_le_tsum s fun i _ => norm_nonneg _
  have hssnn : (0 : ℝ) ≤ ∑ i ∈ s, ‖u i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  set t : ℝ := ∑ i ∈ s, ‖u i‖ with ht
  have hexp : Real.exp t - 1 - t ≤ t ^ 2 * Real.exp t := by
    rcases lt_or_ge t 1 with hlt | hge
    · have h1 : (0 : ℝ) < 1 - t := by linarith
      have h2 : (1 : ℝ) - t ≤ Real.exp (-t) := by
        have := Real.add_one_le_exp (-t)
        linarith
      have h3 : Real.exp (-t) * Real.exp t = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [Real.exp_pos t, h2, h3, hssnn]
    · have hsq : (0 : ℝ) ≤ t ^ 2 - 1 := by nlinarith
      nlinarith [Real.exp_pos t, mul_nonneg hsq (Real.exp_pos t).le]
  have hmono : t ^ 2 * Real.exp t ≤ S ^ 2 * Real.exp S := by
    have h1 : t ^ 2 ≤ S ^ 2 := by nlinarith
    have h2 : Real.exp t ≤ Real.exp S := Real.exp_le_exp.mpr hss
    nlinarith [Real.exp_pos t, sq_nonneg t]
  linarith [hps, hexp, hmono]

/-- **The derivative at the origin of a linear-family product.**  For a summable family of
coefficients the product `∏(1 + x q_i)` has derivative `∑ q_i` at the origin. -/
theorem hasDerivAt_tprod_one_add_mul {ι : Type*} {q : ι → ℂ} (hq : Summable fun i => ‖q i‖) :
    HasDerivAt (fun x : ℂ => ∏' i, (1 + x * q i)) (∑' i, q i) 0 := by
  set Q : ℝ := ∑' i, ‖q i‖ with hQdef
  have hQnn : 0 ≤ Q := tsum_nonneg fun i => norm_nonneg _
  have hqs : Summable q := hq.of_norm
  have hnorm : ∀ x : ℂ, Summable (fun i => ‖x * q i‖) := by
    intro x
    refine (hq.mul_left ‖x‖).congr fun i => ?_
    rw [norm_mul]
  have hmass : ∀ x : ℂ, (∑' i, ‖x * q i‖) = ‖x‖ * Q := by
    intro x
    rw [hQdef, ← tsum_mul_left]
    exact tsum_congr fun i => by rw [norm_mul]
  have hsum : ∀ x : ℂ, (∑' i, x * q i) = x * ∑' i, q i := fun x => tsum_mul_left
  have hbound : ∀ x : ℂ, ‖(∏' i, (1 + x * q i)) - 1 - x * ∑' i, q i‖
      ≤ (‖x‖ * Q) ^ 2 * Real.exp (‖x‖ * Q) := by
    intro x
    have h := norm_tprod_one_add_sub_one_sub_tsum_le (u := fun i => x * q i) (hnorm x)
    rw [hsum x, hmass x] at h
    exact h
  have hzero : (∏' i, (1 + (0 : ℂ) * q i)) = 1 := by
    simp
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hg : Tendsto (fun y : ℂ => ‖y‖ * Q ^ 2 * Real.exp (‖y‖ * Q)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hc : Continuous fun y : ℂ => ‖y‖ * Q ^ 2 * Real.exp (‖y‖ * Q) := by fun_prop
    have h0 : Tendsto (fun y : ℂ => ‖y‖ * Q ^ 2 * Real.exp (‖y‖ * Q)) (𝓝[≠] (0 : ℂ))
        (𝓝 (‖(0 : ℂ)‖ * Q ^ 2 * Real.exp (‖(0 : ℂ)‖ * Q))) :=
      (hc.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using h0
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hg
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y ≠ 0 := hy
  have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
  have hslope : slope (fun x : ℂ => ∏' i, (1 + x * q i)) 0 y
      = ((∏' i, (1 + y * q i)) - 1) / y := by
    rw [slope_def_field, hzero]
    field_simp
    ring
  rw [hslope]
  have hkey : ‖((∏' i, (1 + y * q i)) - 1) / y - ∑' i, q i‖
      = ‖(∏' i, (1 + y * q i)) - 1 - y * ∑' i, q i‖ / ‖y‖ := by
    rw [← norm_div]
    congr 1
    field_simp
  rw [hkey, div_le_iff₀ hyn]
  refine (hbound y).trans ?_
  have hexp : Real.exp (‖y‖ * Q) ≤ Real.exp (‖y‖ * Q) := le_rfl
  nlinarith [Real.exp_pos (‖y‖ * Q), sq_nonneg (‖y‖ * Q), hQnn, hyn]

end

end GaloisForLFunctions.HTGeometry
