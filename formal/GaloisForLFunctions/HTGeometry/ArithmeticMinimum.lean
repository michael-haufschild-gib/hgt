import GaloisForLFunctions.HTGeometry.PositiveDefiniteBounds

/-!
# The arithmetic minimum of a positive definite form

A positive definite form is proper on the integer lattice: only finitely many integer vectors take a
bounded value, because the form dominates a positive multiple of the squared norm.  Hence the
minimum over the nonzero integer vectors is **attained**.

This is the first step of reduction theory: Minkowski reduction is built by repeatedly choosing
vectors realising the minimum.

* `finite_latticePoints_le` : **finitely many integer vectors of bounded value.**
* `exists_arithmeticMinimum` : **the minimum over nonzero integer vectors is attained.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- An integer vector, read over `ℝ`. -/
def intVec (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

theorem intVec_injective : Function.Injective (intVec (n := n)) := by
  intro v w h
  funext i
  have hi : ((v i : ℤ) : ℝ) = ((w i : ℤ) : ℝ) := congrFun h i
  exact_mod_cast hi

theorem intVec_eq_zero_iff {v : Fin n → ℤ} : intVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi : ((v i : ℤ) : ℝ) = 0 := congrFun h i
    exact_mod_cast hi
  · intro h
    subst h
    funext i
    simp [intVec]

theorem finite_intVec_bounded (C : ℝ) :
    {v : Fin n → ℤ | ∀ i, |(v i : ℝ)| ≤ C}.Finite := by
  classical
  have hpi : {v : Fin n → ℤ | ∀ i, |(v i : ℝ)| ≤ C}
      ⊆ {v : Fin n → ℤ | ∀ i, |v i| ≤ ⌈C⌉} := by
    intro v hv i
    have h1 : ((|v i| : ℤ) : ℝ) ≤ C := by
      rw [Int.cast_abs]
      exact hv i
    have h2 : ((|v i| : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := le_trans h1 (Int.le_ceil C)
    exact_mod_cast h2
  refine Set.Finite.subset ?_ hpi
  have hbox : {v : Fin n → ℤ | ∀ i, |v i| ≤ ⌈C⌉}
      = Set.pi Set.univ (fun _ : Fin n => Set.Icc (-⌈C⌉) ⌈C⌉) := by
    ext v
    constructor
    · intro h i _
      exact abs_le.1 (h i)
    · intro h i
      exact abs_le.2 (h i (Set.mem_univ i))
  rw [hbox]
  exact Set.Finite.pi (fun _ => Set.finite_Icc _ _)

/-- **Finitely many integer vectors take a bounded value.** -/
theorem finite_latticePoints_le (A : posDefCone n) (hn : 0 < n) (C : ℝ) :
    {v : Fin n → ℤ | quadForm A (intVec v) ≤ C}.Finite := by
  classical
  obtain ⟨m, hm, hlow⟩ := exists_lower_bound_of_isCompact (K := {A}) isCompact_singleton hn
  have hlow' : ∀ y : Fin n → ℝ, m * ‖y‖ ^ 2 ≤ quadForm A y :=
    quadForm_ge_of_sphere_bound (hlow A rfl)
  refine Set.Finite.subset (finite_intVec_bounded (n := n) (Real.sqrt (C / m))) ?_
  intro v hv i
  have hq : m * ‖intVec v‖ ^ 2 ≤ C := le_trans (hlow' (intVec v)) hv
  have hnormsq : ‖intVec v‖ ^ 2 ≤ C / m := by
    rw [le_div_iff₀ hm, mul_comm]
    exact hq
  have hentry : |(v i : ℝ)| ≤ ‖intVec v‖ := by
    have := norm_le_pi_norm (intVec v) i
    simpa [intVec, Real.norm_eq_abs] using this
  refine le_trans hentry ?_
  rw [show ‖intVec v‖ = Real.sqrt (‖intVec v‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hnormsq

/-- **The minimum of a positive definite form over the nonzero integer vectors is attained.** -/
theorem exists_arithmeticMinimum (A : posDefCone n) (hn : 0 < n) :
    ∃ v : Fin n → ℤ, v ≠ 0 ∧ ∀ w : Fin n → ℤ, w ≠ 0 →
      quadForm A (intVec v) ≤ quadForm A (intVec w) := by
  classical
  set v₀ : Fin n → ℤ := Pi.single ⟨0, hn⟩ 1 with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    intro hcon
    have h1 : v₀ ⟨0, hn⟩ = 0 := congrFun hcon ⟨0, hn⟩
    rw [hv₀] at h1
    simp at h1
  set S : Set (Fin n → ℤ) :=
    {w | w ≠ 0 ∧ quadForm A (intVec w) ≤ quadForm A (intVec v₀)} with hS
  have hSfin : S.Finite :=
    (finite_latticePoints_le A hn (quadForm A (intVec v₀))).subset (fun w hw => hw.2)
  have hSne : S.Nonempty := ⟨v₀, hv₀ne, le_rfl⟩
  obtain ⟨v, hvS, hvmin⟩ := Set.exists_min_image S (fun w => quadForm A (intVec w)) hSfin hSne
  refine ⟨v, hvS.1, ?_⟩
  intro w hw
  by_cases hwS : w ∈ S
  · exact hvmin w hwS
  · have hnot : ¬ (quadForm A (intVec w) ≤ quadForm A (intVec v₀)) := fun h => hwS ⟨hw, h⟩
    have h1 : quadForm A (intVec v) ≤ quadForm A (intVec v₀) := hvS.2
    linarith [not_le.1 hnot]

end GaloisForLFunctions.HTGeometry
