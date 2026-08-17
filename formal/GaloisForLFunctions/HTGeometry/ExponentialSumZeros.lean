import GaloisForLFunctions.HTGeometry.VanishingOrderProduct

/-!
# Exponential sums: derivatives, exponent shift, and the zero-multiplicity bound

An **exponential sum** is `t ↦ ∑ i, c i * exp (a i * t)`.  Three structural facts.

* Differentiating multiplies each coefficient by its exponent:
  `iteratedDeriv k (expSum c a) = expSum (c * a ^ k) a`.
* Multiplying by `e^{-α t}` shifts every exponent by `-α` and leaves the coefficients alone; since
  the factor never vanishes, the zero configurations are unchanged.
* Consequently the counting theorem of `ZeroMultisetRolle` applies: the total zero multiplicity of
  an exponential sum is at most `N` as soon as the `N`-th derivative sum `∑ c i * a i ^ N e^{a i t}`
  has no real zero.

The last statement is the multiplicity-carrying half of Descartes/Laguerre-type bounds; the missing
half is the combinatorial estimate of how large `N` must be taken, which is governed by the number of
sign changes of the coefficient sequence.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- An exponential sum with coefficients `c` and exponents `a`. -/
noncomputable def expSum {m : ℕ} (c a : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * Real.exp (a i * t)

theorem contDiff_expSum {m : ℕ} (c a : Fin m → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (expSum c a) := by
  unfold expSum
  fun_prop

theorem hasDerivAt_expSum {m : ℕ} (c a : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (expSum c a) (expSum (fun i => c i * a i) a t) t := by
  have h : ∀ i : Fin m, HasDerivAt (fun s : ℝ => c i * Real.exp (a i * s))
      (c i * a i * Real.exp (a i * t)) t := by
    intro i
    have hb : HasDerivAt (fun s : ℝ => a i * s) (a i) t := by
      simpa using (hasDerivAt_id t).const_mul (a i)
    have := (hb.exp).const_mul (c i)
    refine this.congr_deriv ?_
    ring
  have hsum := HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => h i)
  have heq : expSum c a = ∑ i, (fun s : ℝ => c i * Real.exp (a i * s)) := by
    funext s
    simp [expSum, Finset.sum_apply]
  rw [heq]
  refine hsum.congr_deriv ?_
  rw [expSum]

theorem deriv_expSum {m : ℕ} (c a : Fin m → ℝ) :
    deriv (expSum c a) = expSum (fun i => c i * a i) a := by
  funext t
  exact (hasDerivAt_expSum c a t).deriv

/-- Differentiating an exponential sum `k` times multiplies each coefficient by the `k`-th power of
its exponent. -/
theorem iteratedDeriv_expSum {m : ℕ} (c a : Fin m → ℝ) :
    ∀ k : ℕ, iteratedDeriv k (expSum c a) = expSum (fun i => c i * a i ^ k) a := by
  intro k
  induction k generalizing c with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', deriv_expSum, ih]
    congr 1
    funext i
    ring

theorem continuous_iteratedDeriv_expSum {m : ℕ} (c a : Fin m → ℝ) :
    ∀ j : ℕ, Continuous (iteratedDeriv j (expSum c a)) := by
  intro j
  rw [iteratedDeriv_expSum]
  exact (contDiff_expSum _ _).continuous

/-! ## Shifting the exponents -/

theorem expSum_shift {m : ℕ} (c a : Fin m → ℝ) (α : ℝ) :
    (fun t => Real.exp (-(α * t)) * expSum c a t) = expSum c (fun i => a i - α) := by
  funext t
  rw [expSum, expSum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← mul_assoc, mul_comm (Real.exp (-(α * t))) (c i), mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Shifting all exponents by a constant does not change the zero configurations. -/
theorem isZeroList_expSum_shift {m : ℕ} (c a : Fin m → ℝ) (α : ℝ) {l : List ℝ}
    (h : IsZeroList (expSum c a) l) : IsZeroList (expSum c (fun i => a i - α)) l := by
  obtain ⟨hs, hv⟩ := h
  refine ⟨hs, fun x => ?_⟩
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.exp (-(α * t))) := by fun_prop
  have := vanishesTo_mul_left (l.count x) hu (contDiff_expSum c a) (hv x)
  rwa [expSum_shift c a α] at this

/-! ## The zero-multiplicity bound -/

/-- **Zero multiplicity of an exponential sum.**  If the `N`-th derivative sum has no real zero,
then every zero configuration of the exponential sum has total order at most `N`. -/
theorem zeroList_length_le_expSum {m : ℕ} (c a : Fin m → ℝ) {N : ℕ}
    (hN : ∀ x : ℝ, expSum (fun i => c i * a i ^ N) a x ≠ 0) {l : List ℝ}
    (hl : IsZeroList (expSum c a) l) : l.length ≤ N := by
  refine zeroList_length_le (continuous_iteratedDeriv_expSum c a) ?_ hl
  intro x
  rw [iteratedDeriv_expSum]
  exact hN x

/-- A one-signed exponential sum has no zeros, hence no zero configuration of positive order. -/
theorem expSum_ne_zero_of_pos {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m)
    (hc : ∀ i, 0 < c i) (x : ℝ) : expSum c a x ≠ 0 := by
  have hpos : 0 < expSum c a x := by
    rw [expSum]
    refine Finset.sum_pos (fun i _ => ?_) ?_
    · exact mul_pos (hc i) (Real.exp_pos _)
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
  exact ne_of_gt hpos

end GaloisForLFunctions.HTGeometry
