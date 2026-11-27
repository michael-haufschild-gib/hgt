import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Occupations

/-! # Greedy energy minima in bounded occupation boxes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I] {c : I → ℕ} {m : ℕ}

def linearCost (e : I → ℝ) (v : I → ℕ) := ∑ i, (v i : ℝ)*e i

def Fits (L U : I → ℕ) (x : State c m) := ∀ i, L i ≤ count x i ∧ count x i ≤ U i

/-- Available slots of strictly smaller energy, counted with multiplicity. -/
def before (e : I → ℝ) (f : I → ℕ) (i : I) :=
  ∑ j ∈ (univ.erase i).filter (fun j => e j < e i), f j

def fillCount (e : I → ℝ) (L U : I → ℕ) (m : ℕ) (i : I) :=
  L i + min (U i-L i) (m-(∑ j, L j)-before e (fun j => U j-L j) i)

def boxCost (e : I → ℝ) (L U : I → ℕ) (m : ℕ) := linearCost e (fillCount e L U m)

private def unit (i j : I) : ℕ := if i = j then 1 else 0

private theorem sum_added (f : I → ℕ) (i : I) :
    (∑ j, (f j + unit i j)) = (∑ j, f j)+1 := by
  rw [sum_add_distrib]
  simp only [unit,sum_ite_eq,mem_univ,if_true]

private theorem cost_added (e : I → ℝ) (f : I → ℕ) (i : I) :
    linearCost e (fun j => f j+unit i j) = linearCost e f+e i := by
  simp only [linearCost,Nat.cast_add,add_mul,sum_add_distrib,unit,apply_ite Nat.cast,
    Nat.cast_one,Nat.cast_zero,ite_mul,one_mul,zero_mul,sum_ite_eq,mem_univ,if_true]

/-- Move one particle from a dearer occupied slot to a cheaper vacancy. -/
private theorem improve (e : I → ℝ) (L U : I → ℕ) (hc : ∀ i, U i ≤ c i) (x : State c m)
    (hx : Fits L U x) {i j : I} (hij : e i < e j) (hi : count x i < U i) (hj : L j < count x j) :
    ∃ y : State c m, Fits L U y ∧ linearCost e (count y) < linearCost e (count x) := by
  have hn : i ≠ j := fun h => hij.ne (congrArg e h)
  let f (t : I) := if j=t then count x t-1 else count x t
  have orig : (fun t => f t+unit j t) = count x := by
    funext t
    by_cases ht : j=t
    · subst t; simp [f,unit]; omega
    · simp only [f,unit,if_neg ht,add_zero]
  let v (t : I) := f t+unit i t
  have valid (t : I) : L t ≤ v t ∧ v t ≤ U t := by
    obtain ⟨h₁,h₂⟩ := hx t
    by_cases hit : i=t
    · subst t; simp [v,f,unit,hn.symm]; omega
    by_cases hjt : j=t
    · subst t; simp [v,f,unit,hn]; omega
    · simpa only [v,f,unit,if_neg hit,if_neg hjt,add_zero] using And.intro h₁ h₂
  have total : ∑ t, v t = m := by
    calc _ = (∑ t, f t)+1 := sum_added f i
         _ = ∑ t, (f t+unit j t) := (sum_added f j).symm
         _ = m := by rw [orig,count_sum]
  let y : State c m := ⟨fun t => ⟨v t,Nat.lt_succ_of_le ((valid t).2.trans (hc t))⟩,total⟩
  refine ⟨y,valid,?_⟩
  change linearCost e (fun t => f t+unit i t) < linearCost e (count x)
  rw [← orig,cost_added,cost_added]
  linarith only [hij]

private def after (e : I → ℝ) (f : I → ℕ) (i : I) :=
  ∑ j ∈ (univ.erase i).filter (fun j => ¬e j < e i), f j

private theorem split_mass (e : I → ℝ) (f : I → ℕ) (i : I) :
    before e f i + after e f i + f i = ∑ j, f j := by
  unfold before after
  rw [sum_filter_add_sum_filter_not,sum_erase_add _ _ (mem_univ i)]

/-- Every minimizer fills all lower-cost vacancies before using a higher-cost slot. -/
theorem minimizing_counts (e : I → ℝ) (hinj : Function.Injective e)
    (L U : I → ℕ) (hc : ∀ i, U i ≤ c i) (x : State c m) (hx : Fits L U x)
    (hmin : ∀ y : State c m, Fits L U y → linearCost e (count x) ≤ linearCost e (count y)) :
    count x = fillCount e L U m := by
  have no_swap {i j : I} (h : e i < e j) (hi : count x i < U i) : count x j ≤ L j := by
    by_contra! hj
    obtain ⟨y,hy,hlt⟩ := improve e L U hc x hx h hi hj
    exact hlt.not_ge (hmin y hy)
  let v (i : I) := count x i-L i
  let d (i : I) := U i-L i
  funext i
  have total := split_mass e v i
  have deg : (∑ j, v j) = m-(∑ j, L j) := by
    exact (sum_tsub_distrib _ (fun j _ => (hx j).1)).trans (by rw [count_sum])
  rw [deg] at total
  have hb : before e v i ≤ before e d i :=
    sum_le_sum (fun j _ => Nat.sub_le_sub_right (hx j).2 _)
  have full (hi : L i < count x i) : before e v i = before e d i := by
    apply sum_congr rfl
    intro j hj
    have sat : count x j = U j := by
      apply le_antisymm (hx j).2
      by_contra! h
      exact hi.not_ge (no_swap (mem_filter.mp hj).2 h)
    simp only [v,d,sat]
  have empty (hi : count x i < U i) : after e v i = 0 := by
    apply sum_eq_zero
    intro j hj
    obtain ⟨hm,he⟩ := mem_filter.mp hj
    have hne : j ≠ i := (mem_erase.mp hm).1
    have hij : e i < e j := lt_of_le_of_ne (le_of_not_gt he) (fun hh => hne (hinj hh.symm))
    exact Nat.sub_eq_zero_of_le (no_swap hij hi)
  have bounds := hx i
  change count x i = L i + min (d i) (m-(∑ j, L j)-before e d i)
  change before e v i + after e v i + (count x i-L i) = _ at total
  change count x i = L i + min (U i-L i) _
  by_cases h₁ : L i < count x i <;> by_cases h₂ : count x i < U i
  · have := full h₁; have := empty h₂; omega
  · have := full h₁; omega
  · have := empty h₂; omega
  · omega

/-- Every nonempty constrained box has an attained minimum given by the explicit prefix formula. -/
theorem greedy_minimum (e : I → ℝ) (hinj : Function.Injective e) (L U : I → ℕ)
    (hc : ∀ i, U i ≤ c i) (w : State c m) (hw : Fits L U w) :
    ∃ x : State c m, Fits L U x ∧ count x = fillCount e L U m ∧
      linearCost e (count x) = boxCost e L U m ∧
      ∀ y : State c m, Fits L U y → boxCost e L U m ≤ linearCost e (count y) := by
  classical
  let B := univ.filter (Fits L U : State c m → Prop)
  obtain ⟨x,hx,hm⟩ := exists_min_image B (fun z => linearCost e (count z)) ⟨w,mem_filter.mpr ⟨mem_univ _,hw⟩⟩
  have hoff : Fits L U x := (mem_filter.mp hx).2
  have opt (y : State c m) (hy : Fits L U y) := hm y (mem_filter.mpr ⟨mem_univ _,hy⟩)
  have hh := minimizing_counts e hinj L U hc x hoff opt
  exact ⟨x,hoff,hh,congrArg (linearCost e) hh,fun y hy => (congrArg (linearCost e) hh).symm.le.trans (opt y hy)⟩

#print axioms minimizing_counts
#print axioms greedy_minimum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
