import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel

/-!
# The minimal constant-coefficient order of a finite exponential sum

A finite exponential sum with pairwise distinct frequencies and nonzero coefficients is annihilated
by the monic operator whose characteristic roots are exactly its frequencies, and by nothing of
smaller degree: applying a constant-coefficient operator `P(D)` multiplies each mode by `P(λ)`, and
independence of exponentials forces `P` to vanish at every frequency.  The linear spectral rank of a
finite exponential sum is therefore exactly its number of modes.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The constant-coefficient differential operator `P(D)` applied to `f`. -/
def constCoeffApply (P : Polynomial ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * iteratedDeriv j f z

variable {ι : Type*} [DecidableEq ι]

/-- `P(D)` acts on a finite exponential sum by multiplying each mode by `P(λ)`. -/
theorem constCoeffApply_expSum (s : Finset ι) (a lam : ι → ℂ) (P : Polynomial ℂ) (z : ℂ) :
    constCoeffApply P (fun x => ∑ i ∈ s, a i * Complex.exp (lam i * x)) z
      = ∑ i ∈ s, (a i * P.eval (lam i)) * Complex.exp (lam i * z) := by
  rw [constCoeffApply]
  simp_rw [iteratedDeriv_finset_expSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The spectral rank lower bound.**  A nonzero constant-coefficient operator annihilating a
finite exponential sum with distinct frequencies and nonzero coefficients has degree at least the
number of modes. -/
theorem card_le_natDegree_of_constCoeffApply_eq_zero (s : Finset ι) (lam : ι → ℂ)
    (hinj : Set.InjOn lam s) (a : ι → ℂ) (ha : ∀ i ∈ s, a i ≠ 0)
    {P : Polynomial ℂ} (hP : P ≠ 0)
    (hann : ∀ z, constCoeffApply P (fun x => ∑ i ∈ s, a i * Complex.exp (lam i * x)) z = 0) :
    s.card ≤ P.natDegree := by
  have hzero : ∀ i ∈ s, a i * P.eval (lam i) = 0 :=
    exp_coeff_eq_zero_of_sum_eq_zero s lam hinj (fun i => a i * P.eval (lam i))
      (fun z => by rw [← constCoeffApply_expSum s a lam P z]; exact hann z)
  have hroot : ∀ i ∈ s, P.IsRoot (lam i) := by
    intro i hi
    rcases mul_eq_zero.1 (hzero i hi) with h | h
    · exact absurd h (ha i hi)
    · exact h
  have hsub : s.image lam ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hP, hroot i hi⟩
  calc s.card = (s.image lam).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := P.card_roots'

theorem natDegree_expSumAnnihilator (s : Finset ι) (c : ι → ℂ) :
    (expSumAnnihilator s c).natDegree = s.card := by
  rw [expSumAnnihilator, Polynomial.natDegree_prod]
  · simp
  · intro i _
    exact Polynomial.X_sub_C_ne_zero (c i)

/-- **The minimal constant-coefficient order equals the number of modes.**  The monic operator with
the frequencies as characteristic roots annihilates the sum and has degree `s.card`, and no nonzero
operator of smaller degree annihilates it. -/
theorem minimal_constCoeffOrder_expSum (s : Finset ι) (lam : ι → ℂ) (hinj : Set.InjOn lam s)
    (a : ι → ℂ) (ha : ∀ i ∈ s, a i ≠ 0) :
    (expSumAnnihilator s lam).natDegree = s.card ∧
      (∀ z, constCoeffApply (expSumAnnihilator s lam)
        (fun x => ∑ i ∈ s, a i * Complex.exp (lam i * x)) z = 0) ∧
      ∀ P : Polynomial ℂ, P ≠ 0 →
        (∀ z, constCoeffApply P (fun x => ∑ i ∈ s, a i * Complex.exp (lam i * x)) z = 0) →
        s.card ≤ P.natDegree :=
  ⟨natDegree_expSumAnnihilator s lam, fun z => expSumAnnihilator_ode s a lam z,
    fun _ hP hann => card_le_natDegree_of_constCoeffApply_eq_zero s lam hinj a ha hP hann⟩

end

end GaloisForLFunctions.HTGeometry
