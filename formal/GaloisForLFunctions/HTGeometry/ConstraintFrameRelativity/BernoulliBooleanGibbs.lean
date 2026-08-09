import Mathlib

/-!
# The finite Boolean Gibbs law and its linear statistics

A finite index set `ι` carries the product Bernoulli law with occupation probabilities
`q : ι → ℝ`: the configuration `S : Finset ι` has weight `(∏_{p ∈ S} q p) * ∏_{p ∉ S} (1 - q p)`.

The whole second-order theory follows from one identity,
`bernoulliExp_prod`, which evaluates the expectation of a product observable
`S ↦ (∏_{p ∈ S} f p) * ∏_{p ∉ S} g p` as `∏_p (q p * f p + (1 - q p) * g p)`; it is
`Finset.prod_add` read backwards.  Specialising `f, g` to indicators gives the subset-occupation
law `E[1_{A ⊆ S}] = ∏_{p ∈ A} q p`, hence the marginals, the pair correlations, and finally

`Cov(∑_{p ∈ S} a p, ∑_{p ∈ S} b p) = ∑_p a p * b p * q p * (1 - q p)`,

the exact diagonal covariance of two linear statistics of the Boolean gas.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The product Bernoulli weight -/

/-- The product Bernoulli weight of a configuration `S`. -/
def bernoulliWeight (q : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ p ∈ S, q p) * ∏ p ∈ Sᶜ, (1 - q p)

/-- Expectation against the product Bernoulli law. -/
def bernoulliExp (q : ι → ℝ) (f : Finset ι → ℝ) : ℝ :=
  ∑ S : Finset ι, bernoulliWeight q S * f S

theorem bernoulliExp_add (q : ι → ℝ) (f g : Finset ι → ℝ) :
    bernoulliExp q (f + g) = bernoulliExp q f + bernoulliExp q g := by
  simp only [bernoulliExp, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

theorem bernoulliExp_smul (q : ι → ℝ) (c : ℝ) (f : Finset ι → ℝ) :
    bernoulliExp q (fun S => c * f S) = c * bernoulliExp q f := by
  simp only [bernoulliExp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

theorem bernoulliExp_sum {κ : Type*} (q : ι → ℝ) (s : Finset κ) (f : κ → Finset ι → ℝ) :
    bernoulliExp q (fun S => ∑ k ∈ s, f k S) = ∑ k ∈ s, bernoulliExp q (f k) := by
  simp only [bernoulliExp, Finset.mul_sum]
  exact Finset.sum_comm

/-- **The product observable law.**  The expectation of a product observable factorises. -/
theorem bernoulliExp_prod (q f g : ι → ℝ) :
    bernoulliExp q (fun S => (∏ p ∈ S, f p) * ∏ p ∈ Sᶜ, g p)
      = ∏ p, (q p * f p + (1 - q p) * g p) := by
  rw [Finset.prod_add]
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.compl_eq_univ_sdiff, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    bernoulliWeight]
  ring

/-- The Bernoulli law has total mass one. -/
theorem bernoulliExp_one (q : ι → ℝ) : bernoulliExp q (fun _ => 1) = 1 := by
  have h := bernoulliExp_prod q (fun _ => 1) (fun _ => 1)
  simpa using h

/-! ## Subset occupation -/

/-- **Subset occupation law.**  The probability that `A` is entirely occupied is `∏_{p ∈ A} q p`. -/
theorem bernoulliExp_subset (q : ι → ℝ) (A : Finset ι) :
    bernoulliExp q (fun S => if A ⊆ S then 1 else 0) = ∏ p ∈ A, q p := by
  have h := bernoulliExp_prod q (fun _ => 1) (fun p => if p ∈ A then 0 else 1)
  have hleft : ∀ S : Finset ι,
      (∏ _p ∈ S, (1 : ℝ)) * ∏ p ∈ Sᶜ, (if p ∈ A then (0 : ℝ) else 1)
        = if A ⊆ S then 1 else 0 := by
    intro S
    rw [Finset.prod_const_one, one_mul]
    by_cases hAS : A ⊆ S
    · rw [if_pos hAS]
      refine Finset.prod_eq_one fun p hp => ?_
      have hpA : p ∉ A := fun hpA => (Finset.mem_compl.mp hp) (hAS hpA)
      simp [hpA]
    · rw [if_neg hAS]
      obtain ⟨p, hpA, hpS⟩ := Finset.not_subset.mp hAS
      refine Finset.prod_eq_zero (Finset.mem_compl.mpr hpS) ?_
      simp [hpA]
  have hright : ∏ p, (q p * 1 + (1 - q p) * (if p ∈ A then (0 : ℝ) else 1))
      = ∏ p ∈ A, q p := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ A)]
    have h1 : ∀ p ∈ Finset.univ.filter (· ∈ A),
        q p * 1 + (1 - q p) * (if p ∈ A then (0 : ℝ) else 1) = q p := by
      intro p hp
      simp [(Finset.mem_filter.mp hp).2]
    have h2 : ∀ p ∈ Finset.univ.filter (fun p => ¬ (p ∈ A)),
        q p * 1 + (1 - q p) * (if p ∈ A then (0 : ℝ) else 1) = 1 := by
      intro p hp
      simp [(Finset.mem_filter.mp hp).2]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const_one, mul_one]
    congr 1
    ext p
    simp
  calc bernoulliExp q (fun S => if A ⊆ S then (1 : ℝ) else 0)
      = bernoulliExp q
          (fun S => (∏ _p ∈ S, (1 : ℝ)) * ∏ p ∈ Sᶜ, (if p ∈ A then (0 : ℝ) else 1)) :=
        congrArg (bernoulliExp q) (funext fun S => (hleft S).symm)
    _ = ∏ p, (q p * 1 + (1 - q p) * (if p ∈ A then (0 : ℝ) else 1)) := h
    _ = ∏ p ∈ A, q p := hright

/-- The occupation marginal. -/
theorem bernoulliExp_mem (q : ι → ℝ) (p : ι) :
    bernoulliExp q (fun S => if p ∈ S then (1 : ℝ) else 0) = q p := by
  have h := bernoulliExp_subset q {p}
  simpa [Finset.singleton_subset_iff] using h

/-- The pair correlation of two occupation indicators. -/
theorem bernoulliExp_mem_mul_mem (q : ι → ℝ) (p r : ι) :
    bernoulliExp q (fun S => (if p ∈ S then (1 : ℝ) else 0) * (if r ∈ S then (1 : ℝ) else 0))
      = if p = r then q p else q p * q r := by
  rcases eq_or_ne p r with rfl | hpr
  · have hobs : (fun S : Finset ι =>
        (if p ∈ S then (1 : ℝ) else 0) * (if p ∈ S then (1 : ℝ) else 0))
        = fun S => if p ∈ S then (1 : ℝ) else 0 := by
      funext S
      by_cases hp : p ∈ S <;> simp [hp]
    rw [hobs, bernoulliExp_mem, if_pos rfl]
  · have h := bernoulliExp_subset q {p, r}
    rw [Finset.prod_pair hpr] at h
    rw [if_neg hpr, ← h]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hp : p ∈ S <;> by_cases hr : r ∈ S <;>
      simp [hp, hr, Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-! ## Linear statistics -/

/-- The linear statistic `S ↦ ∑_{p ∈ S} a p`. -/
def linearStat (a : ι → ℝ) (S : Finset ι) : ℝ := ∑ p ∈ S, a p

theorem linearStat_eq_sum_indicator (a : ι → ℝ) (S : Finset ι) :
    linearStat a S = ∑ p, a p * (if p ∈ S then (1 : ℝ) else 0) := by
  rw [linearStat, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have h1 : ∀ p ∈ Finset.univ.filter (· ∈ S),
      a p * (if p ∈ S then (1 : ℝ) else 0) = a p := by
    intro p hp
    simp [(Finset.mem_filter.mp hp).2]
  have h2 : ∀ p ∈ Finset.univ.filter (fun p => ¬ (p ∈ S)),
      a p * (if p ∈ S then (1 : ℝ) else 0) = 0 := by
    intro p hp
    simp [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  refine (Finset.sum_congr ?_ fun _ _ => rfl)
  ext p
  simp

theorem bernoulliExp_linearStat (q a : ι → ℝ) :
    bernoulliExp q (linearStat a) = ∑ p, a p * q p := by
  have h : bernoulliExp q (linearStat a)
      = ∑ p, bernoulliExp q (fun S => a p * (if p ∈ S then (1 : ℝ) else 0)) := by
    rw [← bernoulliExp_sum]
    exact congrArg (bernoulliExp q) (funext fun S => linearStat_eq_sum_indicator a S)
  rw [h]
  exact Finset.sum_congr rfl fun p _ => by
    rw [bernoulliExp_smul, bernoulliExp_mem]

theorem bernoulliExp_linearStat_mul (q a b : ι → ℝ) :
    bernoulliExp q (fun S => linearStat a S * linearStat b S)
      = ∑ p, ∑ r, a p * b r * (if p = r then q p else q p * q r) := by
  have hobs : ∀ S : Finset ι, linearStat a S * linearStat b S
      = ∑ p, ∑ r, a p * b r *
          ((if p ∈ S then (1 : ℝ) else 0) * (if r ∈ S then (1 : ℝ) else 0)) := by
    intro S
    rw [linearStat_eq_sum_indicator, linearStat_eq_sum_indicator, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => by ring
  rw [congrArg (bernoulliExp q) (funext hobs), bernoulliExp_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bernoulliExp_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [bernoulliExp_smul, bernoulliExp_mem_mul_mem]

/-- The covariance of two observables under the Bernoulli law. -/
def bernoulliCov (q : ι → ℝ) (f g : Finset ι → ℝ) : ℝ :=
  bernoulliExp q (fun S => f S * g S) - bernoulliExp q f * bernoulliExp q g

/-- **Diagonal covariance of Boolean linear statistics.** -/
theorem bernoulliCov_linearStat (q a b : ι → ℝ) :
    bernoulliCov q (linearStat a) (linearStat b)
      = ∑ p, a p * b p * (q p * (1 - q p)) := by
  rw [bernoulliCov, bernoulliExp_linearStat_mul, bernoulliExp_linearStat,
    bernoulliExp_linearStat, Finset.sum_mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ r : ι,
      a p * b r * (if p = r then q p else q p * q r) - a p * q p * (b r * q r)
        = if p = r then a p * b p * (q p * (1 - q p)) else 0 := by
    intro r
    by_cases h : p = r
    · subst h
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun r _ => hterm r]
  simp

end HTGeometry.ConstraintFrameRelativity
