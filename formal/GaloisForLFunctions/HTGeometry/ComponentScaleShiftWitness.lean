import GaloisForLFunctions.HTGeometry.DisconnectedProjectiveGapModuleLaw

/-!
# Rationally transverse concatenation of component spectra

Independently rescaling *and shifting* a finite family of maximally projective
component spectra can make their concatenation maximally projective, so that no
nonzero balanced integer relation survives across components at all.

Scaling alone is not enough: a balanced relation whose restriction to a single
component is unbalanced is invisible to the scales.  Adding one shift per
component makes the obstruction a linear form whose coefficients are the
component relation values *and* the component balances, and a nonzero relation
cannot annihilate both.

Shifts are admissible network terms — the identity is a one-site operator — so
this supplies the witness required by the disconnected genericity law.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]

theorem finsuppSingle_ne_of_ne {ι : Type*} {a b : ι} (h : a ≠ b) :
    (Finsupp.single a 1 : ι →₀ ℕ) ≠ Finsupp.single b 1 := by
  classical
  intro heq
  have hval := congrArg (fun f => f a) heq
  simp [Ne.symm h] at hval

/-- Obstruction polynomial of one integer relation in the component scales and
shifts. -/
def componentScaleShiftRelationPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) :
    MvPolynomial (C ⊕ C) ℝ :=
  ∑ c, (MvPolynomial.C (∑ i, (k c i : ℝ) * energy c i) *
      MvPolynomial.X (Sum.inl c) +
    MvPolynomial.C (∑ i, (k c i : ℝ)) * MvPolynomial.X (Sum.inr c))

omit [DecidableEq C] in
theorem eval_componentScaleShiftRelationPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (p : C ⊕ C → ℝ) :
    MvPolynomial.eval p (componentScaleShiftRelationPolynomial energy k) =
      ∑ c, ((∑ i, (k c i : ℝ) * energy c i) * p (Sum.inl c) +
        (∑ i, (k c i : ℝ)) * p (Sum.inr c)) := by
  unfold componentScaleShiftRelationPolynomial
  simp

theorem coeff_inl_componentScaleShiftRelationPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (c : C) :
    MvPolynomial.coeff (Finsupp.single (Sum.inl c) 1)
        (componentScaleShiftRelationPolynomial energy k) =
      ∑ i, (k c i : ℝ) * energy c i := by
  classical
  unfold componentScaleShiftRelationPolynomial
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single c]
  · rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_X,
      if_pos rfl, if_neg (finsuppSingle_ne_of_ne (by simp))]
    ring
  · intro d _ hdc
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_X,
      if_neg (finsuppSingle_ne_of_ne (by simpa using hdc)),
      if_neg (finsuppSingle_ne_of_ne (by simp))]
    ring
  · simp

theorem coeff_inr_componentScaleShiftRelationPolynomial
    (energy : ∀ c, I c → ℝ) (k : ∀ c, I c → ℤ) (c : C) :
    MvPolynomial.coeff (Finsupp.single (Sum.inr c) 1)
        (componentScaleShiftRelationPolynomial energy k) =
      ∑ i, (k c i : ℝ) := by
  classical
  unfold componentScaleShiftRelationPolynomial
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single c]
  · rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_X,
      if_pos rfl, if_neg (finsuppSingle_ne_of_ne (by simp))]
    ring
  · intro d _ hdc
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_X,
      if_neg (finsuppSingle_ne_of_ne (by simp)),
      if_neg (finsuppSingle_ne_of_ne (by simpa using hdc))]
    ring
  · simp

/-- **Every nonzero relation survives the scale–shift family.**  If each
component spectrum is maximally projective, the obstruction polynomial of a
nonzero integer relation is not the zero polynomial. -/
theorem componentScaleShiftRelationPolynomial_ne_zero
    [∀ c, DecidableEq (I c)] (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c))
    (k : ∀ c, I c → ℤ) (hk : k ≠ 0) :
    componentScaleShiftRelationPolynomial energy k ≠ 0 := by
  classical
  intro hzero
  apply hk
  funext c
  refine hmax c (k c) ?_ ?_
  · show (∑ i, k c i) = 0
    have h := coeff_inr_componentScaleShiftRelationPolynomial energy k c
    rw [hzero, MvPolynomial.coeff_zero] at h
    exact_mod_cast h.symm
  · have h := coeff_inl_componentScaleShiftRelationPolynomial energy k c
    rw [hzero, MvPolynomial.coeff_zero] at h
    exact h.symm

/-- **Scale–shift transversality.**  Independently rescaling and shifting a
finite family of maximally projective component spectra can make the
concatenated spectrum maximally projective: no nonzero balanced integer
relation survives across components. -/
theorem exists_scaleShift_maximallyProjective_concat
    [∀ c, DecidableEq (I c)] (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c)) :
    ∃ p : C ⊕ C → ℝ,
      MaximallyProjectiveEnergy
        (fun x : Σ c, I c =>
          energy x.1 x.2 * p (Sum.inl x.1) + p (Sum.inr x.1)) := by
  classical
  let J := {k : ∀ c, I c → ℤ // k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  let f : J → (C ⊕ C → ℝ) → ℝ :=
    fun j p =>
      MvPolynomial.eval p
        (componentScaleShiftRelationPolynomial energy j.1)
  have hf : ∀ j : J, AnalyticOnNhd ℝ (f j) Set.univ := by
    intro j p hp
    exact (AnalyticOnNhd.eval_mvPolynomial
      (componentScaleShiftRelationPolynomial energy j.1)) p hp
  have hne : ∀ j : J, ∃ p ∈ (Set.univ : Set (C ⊕ C → ℝ)), f j p ≠ 0 := by
    intro j
    have hpoly := componentScaleShiftRelationPolynomial_ne_zero energy hmax
      j.1 j.2
    by_contra h
    push Not at h
    apply hpoly
    apply MvPolynomial.funext
    intro p
    have := h p (Set.mem_univ p)
    simpa [f] using this
  obtain ⟨p, -, hp⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      f Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty hf hne
  refine ⟨p, ?_⟩
  intro K _ hzero
  by_contra hK
  obtain ⟨x₀, hx₀⟩ : ∃ x : Σ c, I c, K x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hK (funext hcon)
  let k : ∀ c, I c → ℤ := fun c i => K ⟨c, i⟩
  have hkne : k ≠ 0 := by
    intro h
    exact hx₀ (congrFun (congrFun h x₀.1) x₀.2)
  refine hp ⟨k, hkne⟩ ?_
  show MvPolynomial.eval p
    (componentScaleShiftRelationPolynomial energy k) = 0
  rw [eval_componentScaleShiftRelationPolynomial]
  calc
    ∑ c, ((∑ i, (k c i : ℝ) * energy c i) * p (Sum.inl c) +
        (∑ i, (k c i : ℝ)) * p (Sum.inr c))
        = ∑ c, ∑ i, (K ⟨c, i⟩ : ℝ) *
            (energy c i * p (Sum.inl c) + p (Sum.inr c)) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [k]
      ring
    _ = 0 := by
      rw [Fintype.sum_sigma] at hzero
      simpa using hzero

end

end GaloisForLFunctions.HTGeometry
