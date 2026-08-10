import GaloisForLFunctions.HTGeometry.PermutationInvariantSubspace
import GaloisForLFunctions.HTGeometry.FiniteLindemannWeierstrass

/-!
# From a rigid relation space to independent exponentials

If the only rational linear relation among a finite family of algebraic numbers is the trace
relation, then deleting any one member leaves a rationally independent family, and
Lindemann–Weierstrass turns it into an algebraically independent family of exponentials.

That is the step which converts spectral rigidity into transcendence of the evolved state: the
spectrum has rational rank `D - 1`, so the `D` exponentials `exp(-i t Eⱼ)` generate a field of
transcendence degree `D - 1` — at least `D - 1` because `D - 1` of them are independent, at most
`D - 1` because tracelessness makes their product `1`.

Scaling by a nonzero rational or algebraic time does not change the relation space
(`ker_relationForm_smul`), so the same rigidity is available at every nonzero time.
-/

namespace GaloisForLFunctions.HTGeometry

namespace SpectralExp

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rational linear form attached to a family of complex numbers. -/
noncomputable def relationForm (E : ι → ℂ) : (ι → ℚ) →ₗ[ℚ] ℂ :=
  ∑ i, (LinearMap.proj i : (ι → ℚ) →ₗ[ℚ] ℚ).smulRight (E i)

omit [DecidableEq ι] in
@[simp]
theorem relationForm_apply (E : ι → ℂ) (a : ι → ℚ) :
    relationForm E a = ∑ i, (a i : ℚ) • E i := by
  simp [relationForm, LinearMap.sum_apply]

omit [DecidableEq ι] in
/-- Scaling the family by a nonzero constant does not change its relation space. -/
theorem ker_relationForm_smul {E : ι → ℂ} {t : ℂ} (ht : t ≠ 0) :
    LinearMap.ker (relationForm fun i => t * E i) = LinearMap.ker (relationForm E) := by
  ext a
  simp only [LinearMap.mem_ker, relationForm_apply]
  constructor
  · intro h
    have hmul : t * ∑ i, (a i : ℚ) • E i = 0 := by
      rw [Finset.mul_sum]
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Rat.smul_def, Rat.smul_def]; ring
    exact (mul_eq_zero.mp hmul).resolve_left ht
  · intro h
    have : ∑ i, (a i : ℚ) • (t * E i) = t * ∑ i, (a i : ℚ) • E i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Rat.smul_def, Rat.smul_def]; ring
    rw [this, h, mul_zero]

/-- **Deleting one member of a rigid family leaves an independent one.**  If the only rational
relation is the trace relation, then the family with one index removed is linearly independent. -/
theorem linearIndependent_subtype_of_ker_eq_constLine {E : ι → ℂ}
    (h : LinearMap.ker (relationForm E) = PermSubspace.constLine (K := ℚ) (ι := ι)) (i₀ : ι) :
    LinearIndependent ℚ (fun j : {j : ι // j ≠ i₀} => E j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  set a : ι → ℚ := fun i => if hi : i = i₀ then 0 else g ⟨i, hi⟩ with ha
  have hai₀ : a i₀ = 0 := by simp [ha]
  have hsum : ∑ i, (a i : ℚ) • E i = 0 := by
    have hsplit : ∑ i, (a i : ℚ) • E i
        = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i₀), (a i : ℚ) • E i := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      rw [hi, hai₀, zero_smul]
    rw [hsplit, Finset.sum_subtype (p := fun i => i ≠ i₀)
      (Finset.univ.filter (fun i => i ≠ i₀)) (fun x => by simp)
      (fun i => (a i : ℚ) • E i), ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [ha, j.2]
  have hmem : a ∈ LinearMap.ker (relationForm E) := by
    rw [LinearMap.mem_ker, relationForm_apply]
    exact hsum
  rw [h] at hmem
  obtain ⟨c, hc⟩ := PermSubspace.eq_const_of_mem_constLine hmem
  have hc0 : c = 0 := by
    have := congrFun hc i₀
    rw [hai₀] at this
    exact this.symm
  have : a j.1 = 0 := by rw [hc, hc0]
  rw [ha] at this
  simpa [j.2] using this

/-- **Rigid spectra give algebraically independent exponentials.** -/
theorem algebraicIndependent_exp_of_ker_eq_constLine {E : ι → ℂ}
    (halg : ∀ i, IsAlgebraic ℚ (E i))
    (h : LinearMap.ker (relationForm E) = PermSubspace.constLine (K := ℚ) (ι := ι)) (i₀ : ι) :
    AlgebraicIndependent ℚ (fun j : {j : ι // j ≠ i₀} => Complex.exp (E j)) :=
  GaloisForLFunctions.RHTower.exp_algebraicIndependent_of_linearIndependent (fun j : {j : ι // j ≠ i₀} => E j)
    (fun j => halg j.1) (linearIndependent_subtype_of_ker_eq_constLine h i₀)

omit [DecidableEq ι] in
/-- Tracelessness makes the exponentials multiply to one, so the deleted member is recovered from
the others: the transcendence degree cannot exceed `card ι - 1`. -/
theorem prod_exp_eq_one_of_sum_eq_zero {E : ι → ℂ} (hE : ∑ i, E i = 0) :
    ∏ i, Complex.exp (E i) = 1 := by
  rw [← Complex.exp_sum, hE, Complex.exp_zero]

/-- The deleted exponential is the inverse of the product of the others. -/
theorem exp_eq_inv_prod_of_sum_eq_zero {E : ι → ℂ} (hE : ∑ i, E i = 0) (i₀ : ι) :
    Complex.exp (E i₀) = (∏ j ∈ Finset.univ.erase i₀, Complex.exp (E j))⁻¹ := by
  have hall : (∏ j ∈ Finset.univ.erase i₀, Complex.exp (E j)) * Complex.exp (E i₀) = 1 := by
    rw [Finset.prod_erase_mul Finset.univ (fun i => Complex.exp (E i)) (Finset.mem_univ i₀)]
    exact prod_exp_eq_one_of_sum_eq_zero hE
  exact eq_inv_of_mul_eq_one_right hall

/-! ## From a symmetric Galois action to rigidity -/

omit [DecidableEq ι] in
/-- **A symmetric Galois action makes the relation space permutation invariant.**  If every
permutation of the family is realised by a ring endomorphism of `ℂ`, then a rational relation
transported along it is again a rational relation. -/
theorem isPermInvariant_ker_relationForm {E : ι → ℂ}
    (hgal : ∀ σ : Equiv.Perm ι, ∃ φ : ℂ →+* ℂ, ∀ i, φ (E i) = E (σ i)) :
    PermSubspace.IsPermInvariant (LinearMap.ker (relationForm E)) := by
  intro σ a ha
  obtain ⟨φ, hφ⟩ := hgal σ⁻¹
  rw [LinearMap.mem_ker, relationForm_apply] at ha ⊢
  have himg : ∑ i, (a i : ℚ) • E (σ⁻¹ i) = 0 := by
    have := congrArg φ ha
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Rat.smul_def, Rat.smul_def, map_mul, map_ratCast, hφ i]
  calc ∑ i, ((fun j => a (σ j)) i : ℚ) • E i
      = ∑ i, (a (σ i) : ℚ) • E i := rfl
    _ = ∑ i, (a i : ℚ) • E (σ⁻¹ i) := by
        refine Fintype.sum_equiv σ _ _ fun i => ?_
        simp
    _ = 0 := himg

/-- **The trace relation is the only one.**  A traceless family with a symmetric Galois action and
a nonzero member has relation space exactly the trace line. -/
theorem ker_relationForm_eq_constLine {E : ι → ℂ} [Nonempty ι]
    (hgal : ∀ σ : Equiv.Perm ι, ∃ φ : ℂ →+* ℂ, ∀ i, φ (E i) = E (σ i))
    (htrace : ∑ i, E i = 0) (hne : ∃ i, E i ≠ 0) :
    LinearMap.ker (relationForm E) = PermSubspace.constLine (K := ℚ) (ι := ι) := by
  classical
  refine PermSubspace.eq_constLine_of_le_of_ne_top _ (isPermInvariant_ker_relationForm hgal) ?_ ?_ ?_
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  · intro a ha
    obtain ⟨c, rfl⟩ := PermSubspace.eq_const_of_mem_constLine ha
    rw [LinearMap.mem_ker, relationForm_apply]
    have : ∑ i, (c : ℚ) • E i = (c : ℂ) * ∑ i, E i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Rat.smul_def]
    rw [this, htrace, mul_zero]
  · intro htop
    obtain ⟨i₀, hi₀⟩ := hne
    have hmem : (fun i => if i = i₀ then (1 : ℚ) else 0) ∈ LinearMap.ker (relationForm E) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, relationForm_apply] at hmem
    rw [Finset.sum_eq_single i₀] at hmem
    · simp only [Rat.smul_def] at hmem
      simp at hmem
      exact hi₀ hmem
    · intro b _ hb
      simp [hb]
    · intro hb
      exact absurd (Finset.mem_univ i₀) hb

end SpectralExp

end GaloisForLFunctions.HTGeometry
