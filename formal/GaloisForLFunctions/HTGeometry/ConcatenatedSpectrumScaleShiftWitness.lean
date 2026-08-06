import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw

/-!
# Making a concatenated component spectrum maximally projective

Independently scaling and shifting a finite family of maximally projective
component spectra can make their *concatenation* rationally independent — not
merely projectively independent inside each component.  A relation among the
concatenated levels splits into one linear form per component whose two
coefficients are the component energy pairing and the component total
multiplicity.  If a component multiplicity is nonzero the shift coefficient is
nonzero; if every component multiplicity vanishes the character is balanced in
each component, so maximal projectivity makes some energy pairing nonzero.
Either way the relation is a nonzero real polynomial in the scales and shifts,
and countable real-analytic avoidance produces one parameter outside all of
them.

The shift direction is realized on operators by adding a multiple of the
identity, which is a one-site term, so the witness stays inside every local
Hamiltonian space that contains one maximally projective component Hamiltonian.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]

/-- Value of one integer character on a scaled and shifted concatenated
spectrum. -/
def concatenatedScaleShiftRelation
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (p : C ⊕ C → ℝ) : ℝ :=
  ∑ c, (p (Sum.inl c) * ∑ i, (k c i : ℝ) * energy c i +
    p (Sum.inr c) * ∑ i, (k c i : ℝ))

/-- Linear polynomial in the scales and shifts representing one integer
character of the concatenated spectrum. -/
def concatenatedScaleShiftPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) :
    MvPolynomial (C ⊕ C) ℝ :=
  ∑ c, (MvPolynomial.X (Sum.inl c) *
      MvPolynomial.C (∑ i, (k c i : ℝ) * energy c i) +
    MvPolynomial.X (Sum.inr c) * MvPolynomial.C (∑ i, (k c i : ℝ)))

omit [DecidableEq C] in
theorem eval_concatenatedScaleShiftPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (p : C ⊕ C → ℝ) :
    MvPolynomial.eval p (concatenatedScaleShiftPolynomial energy k) =
      concatenatedScaleShiftRelation energy k p := by
  simp [concatenatedScaleShiftPolynomial, concatenatedScaleShiftRelation]

/-- Reading the energy pairing of one component off the relation. -/
theorem concatenatedScaleShiftRelation_scaleUnit
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (c : C) :
    concatenatedScaleShiftRelation energy k
        (Sum.elim (fun d => if d = c then (1 : ℝ) else 0) (fun _ => 0)) =
      ∑ i, (k c i : ℝ) * energy c i := by
  classical
  unfold concatenatedScaleShiftRelation
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    simp [hdc]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- Reading the total multiplicity of one component off the relation. -/
theorem concatenatedScaleShiftRelation_shiftUnit
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (c : C) :
    concatenatedScaleShiftRelation energy k
        (Sum.elim (fun _ => 0) (fun d => if d = c then (1 : ℝ) else 0)) =
      ∑ i, (k c i : ℝ) := by
  classical
  unfold concatenatedScaleShiftRelation
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    simp [hdc]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-- **Every nonzero character has a nonzero relation polynomial.**  The two
cases are an unbalanced component, where the shift coefficient survives, and a
balanced nonzero component, where maximal projectivity keeps the energy
pairing nonzero. -/
theorem concatenatedScaleShiftPolynomial_ne_zero
    (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c))
    (k : ∀ c, I c → ℤ) (hk : k ≠ 0) :
    concatenatedScaleShiftPolynomial energy k ≠ 0 := by
  classical
  obtain ⟨c, hkc⟩ : ∃ c, k c ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  intro hpoly
  by_cases hsum : (∑ i, k c i) = 0
  · have hvalue : (∑ i, (k c i : ℝ) * energy c i) ≠ 0 := fun hzero =>
      hkc (hmax c (k c) hsum hzero)
    refine hvalue ?_
    rw [← concatenatedScaleShiftRelation_scaleUnit energy k c,
      ← eval_concatenatedScaleShiftPolynomial, hpoly, map_zero]
  · have hvalue : (∑ i, (k c i : ℝ)) ≠ 0 := by
      rw [← Int.cast_sum]
      exact_mod_cast hsum
    refine hvalue ?_
    rw [← concatenatedScaleShiftRelation_shiftUnit energy k c,
      ← eval_concatenatedScaleShiftPolynomial, hpoly, map_zero]

/-- **Rationally independent concatenation.**  Any finite family of maximally
projective component spectra can be scaled and shifted so that the whole
concatenated level set carries no nonzero integer relation at all.  The
parameters are obtained by countable real-analytic avoidance. -/
theorem exists_scale_shift_concatenated_linearIndependent
    (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c)) :
    ∃ scale shift : C → ℝ,
      ∀ k : (Σ c, I c) → ℤ,
        (∑ x, (k x : ℝ) *
          (scale x.1 * energy x.1 x.2 + shift x.1)) = 0 → k = 0 := by
  classical
  let J := {k : ∀ c, I c → ℤ // k ≠ 0}
  let f : J → (C ⊕ C → ℝ) → ℝ :=
    fun j p => concatenatedScaleShiftRelation energy j.1 p
  have hf : ∀ j : J, AnalyticOnNhd ℝ (f j) Set.univ := by
    intro j
    have hfun : f j = fun p =>
        MvPolynomial.eval p (concatenatedScaleShiftPolynomial energy j.1) := by
      funext p
      exact (eval_concatenatedScaleShiftPolynomial energy j.1 p).symm
    rw [hfun]
    intro p hp
    exact (AnalyticOnNhd.eval_mvPolynomial
      (concatenatedScaleShiftPolynomial energy j.1)) p hp
  have hne : ∀ j : J, ∃ p ∈ (Set.univ : Set (C ⊕ C → ℝ)), f j p ≠ 0 := by
    intro j
    have hpoly := concatenatedScaleShiftPolynomial_ne_zero energy hmax j.1 j.2
    by_contra h
    push Not at h
    apply hpoly
    apply MvPolynomial.funext
    intro p
    have := h p (Set.mem_univ p)
    simpa [f, eval_concatenatedScaleShiftPolynomial] using this
  obtain ⟨p, -, hp⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      f Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty hf hne
  refine ⟨fun c => p (Sum.inl c), fun c => p (Sum.inr c), ?_⟩
  intro k hrelation
  by_contra hk
  have hkfun : (fun c i => k ⟨c, i⟩) ≠ 0 := by
    intro hzero
    exact hk (funext fun x => congrFun (congrFun hzero x.1) x.2)
  refine hp ⟨fun c i => k ⟨c, i⟩, hkfun⟩ ?_
  show concatenatedScaleShiftRelation energy (fun c i => k ⟨c, i⟩) p = 0
  unfold concatenatedScaleShiftRelation
  calc
    ∑ c, (p (Sum.inl c) * ∑ i, (k ⟨c, i⟩ : ℝ) * energy c i +
        p (Sum.inr c) * ∑ i, (k ⟨c, i⟩ : ℝ)) =
        ∑ c, ∑ i, (k ⟨c, i⟩ : ℝ) *
          (p (Sum.inl c) * energy c i + p (Sum.inr c)) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ x : Σ c, I c, (k x : ℝ) *
          (p (Sum.inl x.1) * energy x.1 x.2 + p (Sum.inr x.1)) :=
      (Fintype.sum_sigma (fun x : Σ c, I c => (k x : ℝ) *
        (p (Sum.inl x.1) * energy x.1 x.2 + p (Sum.inr x.1)))).symm
    _ = 0 := hrelation

/-- **Maximally projective concatenation.**  Scaling and shifting the component
spectra makes the concatenated spectrum maximally projective. -/
theorem exists_scale_shift_concatenated_maximallyProjective
    (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c)) :
    ∃ scale shift : C → ℝ,
      MaximallyProjectiveEnergy
        (fun x : Σ c, I c => scale x.1 * energy x.1 x.2 + shift x.1) := by
  obtain ⟨scale, shift, h⟩ :=
    exists_scale_shift_concatenated_linearIndependent energy hmax
  exact ⟨scale, shift, fun k _ hzero => h k hzero⟩

end

end GaloisForLFunctions.HTGeometry
