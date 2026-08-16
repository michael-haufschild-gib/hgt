import GaloisForLFunctions.RHTower.ProlateRayleighForm

/-!
# The prolate action on a linear combination

The prolate Sturm–Liouville action is a linear differential operator, so on a finite linear
combination of twice differentiable functions it is the corresponding combination of the actions.
Stated through `HasDerivAt` families, so that no differentiability side condition survives into the
conclusion.

This is what lets a trial *space* — rather than a single trial function — be fed to the variational
extraction.
-/

open Filter Topology Set Finset

noncomputable section

namespace RHTower

variable {ι : Type*}

theorem intervalIntegrable_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) MeasureTheory.volume a b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i t)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem hasDerivAt_finsetSum_const_mul (s : Finset ι) (a : ι → ℝ) {F F' : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F i) (F' i x) x) (x : ℝ) :
    HasDerivAt (fun y => ∑ i ∈ s, a i * F i y) (∑ i ∈ s, a i * F' i x) x :=
  HasDerivAt.fun_sum fun i hi => ((h i hi x).const_mul (a i))

theorem deriv_finsetSum_const_mul (s : Finset ι) (a : ι → ℝ) {F F' : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F i) (F' i x) x) :
    deriv (fun y => ∑ i ∈ s, a i * F i y) = fun x => ∑ i ∈ s, a i * F' i x :=
  funext fun x => (hasDerivAt_finsetSum_const_mul s a h x).deriv

/-- **Linearity of the prolate action.**  On a finite linear combination the prolate
Sturm–Liouville action is the combination of the pointwise actions. -/
theorem prolateSLAction_finsetSum (s : Finset ι) (a : ι → ℝ) {F F' F'' : ι → ℝ → ℝ}
    (h1 : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F i) (F' i x) x)
    (h2 : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F' i) (F'' i x) x)
    (c x : ℝ) :
    prolateSLAction c (fun y => ∑ i ∈ s, a i * F i y) x
      = ∑ i ∈ s, a i * ((1 - x ^ 2) * F'' i x - 2 * x * F' i x - c ^ 2 * x ^ 2 * F i x) := by
  have hd1 : deriv (fun y => ∑ i ∈ s, a i * F i y) = fun y => ∑ i ∈ s, a i * F' i y :=
    deriv_finsetSum_const_mul s a h1
  have hd2 : deriv (fun y => ∑ i ∈ s, a i * F' i y) = fun y => ∑ i ∈ s, a i * F'' i y :=
    deriv_finsetSum_const_mul s a h2
  rw [prolateSLAction, hd1, hd2]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The prolate action of a single member of a `HasDerivAt` family. -/
theorem prolateSLAction_of_hasDerivAt {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x : ℝ, HasDerivAt f (f' x) x) (h2 : ∀ x : ℝ, HasDerivAt f' (f'' x) x) (c x : ℝ) :
    prolateSLAction c f x = (1 - x ^ 2) * f'' x - 2 * x * f' x - c ^ 2 * x ^ 2 * f x := by
  have hd1 : deriv f = f' := funext fun y => (h1 y).deriv
  have hd2 : deriv f' = f'' := funext fun y => (h2 y).deriv
  rw [prolateSLAction, hd1, hd2]

/-- **The pairing of the prolate action against a linear combination is bilinear.**  Both slots
expand over the family, so the Rayleigh numerator of a trial vector is the Gram-style double sum of
the pairwise numerators. -/
theorem integral_prolateSLAction_finsetSum_mul (s : Finset ι) (a : ι → ℝ)
    {F F' F'' : ι → ℝ → ℝ}
    (h1 : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F i) (F' i x) x)
    (h2 : ∀ i ∈ s, ∀ x : ℝ, HasDerivAt (F' i) (F'' i x) x)
    (hc : ∀ i ∈ s, Continuous (F i)) (hc' : ∀ i ∈ s, Continuous (F' i))
    (hc'' : ∀ i ∈ s, Continuous (F'' i)) (c : ℝ) :
    (∫ x in (-1 : ℝ)..1, prolateSLAction c (fun y => ∑ i ∈ s, a i * F i y) x
        * (∑ i ∈ s, a i * F i x))
      = ∑ i ∈ s, ∑ k ∈ s, a i * a k
          * ∫ x in (-1 : ℝ)..1,
              ((1 - x ^ 2) * F'' i x - 2 * x * F' i x - c ^ 2 * x ^ 2 * F i x) * F k x := by
  have hpt : ∀ x : ℝ,
      prolateSLAction c (fun y => ∑ i ∈ s, a i * F i y) x * (∑ i ∈ s, a i * F i x)
        = ∑ i ∈ s, ∑ k ∈ s, a i * a k
            * (((1 - x ^ 2) * F'' i x - 2 * x * F' i x - c ^ 2 * x ^ 2 * F i x) * F k x) := by
    intro x
    rw [prolateSLAction_finsetSum s a h1 h2 c x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ i ∈ s, ∀ k ∈ s, IntervalIntegrable
      (fun x => a i * a k
        * (((1 - x ^ 2) * F'' i x - 2 * x * F' i x - c ^ 2 * x ^ 2 * F i x) * F k x))
      MeasureTheory.volume (-1) 1 := by
    intro i hi k hk
    apply Continuous.intervalIntegrable
    have := hc i hi
    have := hc' i hi
    have := hc'' i hi
    have := hc k hk
    fun_prop
  rw [intervalIntegral.integral_congr (g := fun x => ∑ i ∈ s, ∑ k ∈ s, a i * a k
      * (((1 - x ^ 2) * F'' i x - 2 * x * F' i x - c ^ 2 * x ^ 2 * F i x) * F k x))
    (fun x _ => hpt x)]
  rw [intervalIntegral.integral_finsetSum (fun i hi =>
    intervalIntegrable_finsetSum s (fun k hk => hint i hi k hk))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum (fun k hk => hint i hi k hk)]
  exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _

/-- **Bilinearity of the aperture pairing.**  The squared aperture norm of a linear combination is
the Gram-style double sum. -/
theorem integral_finsetSum_mul_finsetSum (s : Finset ι) (a : ι → ℝ) {F : ι → ℝ → ℝ}
    (hc : ∀ i ∈ s, Continuous (F i)) :
    (∫ x in (-1 : ℝ)..1, (∑ i ∈ s, a i * F i x) * (∑ i ∈ s, a i * F i x))
      = ∑ i ∈ s, ∑ k ∈ s, a i * a k * ∫ x in (-1 : ℝ)..1, F i x * F k x := by
  have hpt : ∀ x : ℝ, (∑ i ∈ s, a i * F i x) * (∑ i ∈ s, a i * F i x)
      = ∑ i ∈ s, ∑ k ∈ s, a i * a k * (F i x * F k x) := by
    intro x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ i ∈ s, ∀ k ∈ s, IntervalIntegrable
      (fun x => a i * a k * (F i x * F k x)) MeasureTheory.volume (-1) 1 := by
    intro i hi k hk
    apply Continuous.intervalIntegrable
    have := hc i hi
    have := hc k hk
    fun_prop
  rw [intervalIntegral.integral_congr (g := fun x => ∑ i ∈ s, ∑ k ∈ s, a i * a k * (F i x * F k x))
    (fun x _ => hpt x)]
  rw [intervalIntegral.integral_finsetSum (fun i hi =>
    intervalIntegrable_finsetSum s (fun k hk => hint i hi k hk))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_finsetSum (fun k hk => hint i hi k hk)]
  exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _

end RHTower
