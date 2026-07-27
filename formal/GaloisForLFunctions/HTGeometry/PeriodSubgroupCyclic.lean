import GaloisForLFunctions.HTGeometry.PeriodRankUniversalLaw

/-!
# The period group of a hypertranscendental function is cyclic

The period-rank law says any two periods of a hypertranscendental meromorphic function are
rationally dependent.  That already confines the period group to a single real line, but a subgroup
of a line can still be dense — and a dense period group produces arbitrarily small nonzero periods,
which forces the function to be constant.  Both ends are therefore excluded at once:

**the period group of a hypertranscendental meromorphic normal-form function on `ℂ` is trivial or
infinite cyclic.**

This subsumes the whole period layer: the rank-two lattice case (an elliptic function is
differentially algebraic), the rank-two `ℝ`-dependent case and the rank-three case (a non-discrete
period group forces constancy), and the entire case (Liouville).  Each of those says some
configuration of periods is impossible; this says exactly which configurations remain.

* `periodSubgroup` — the periods as an additive subgroup of `ℂ`;
* `exists_real_smul_of_mem_periodSubgroup` — every period is a real multiple of any fixed nonzero
  one;
* **`exists_periodSubgroup_eq_closure_singleton`** — the law.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The periods of a function, as an additive subgroup of `ℂ`. -/
def periodSubgroup (f : ℂ → ℂ) : AddSubgroup ℂ where
  carrier := {p | Function.Periodic f p}
  zero_mem' := by intro x; simp
  add_mem' := fun hp hq => Function.Periodic.add_period hp hq
  neg_mem' := fun hp => Function.Periodic.neg hp

@[simp]
theorem mem_periodSubgroup {f : ℂ → ℂ} {p : ℂ} :
    p ∈ periodSubgroup f ↔ Function.Periodic f p := Iff.rfl

/-! ### Every period is a real multiple of a fixed nonzero period -/

/-- **The period line.**  For a hypertranscendental function every period is a real — indeed
rational — multiple of any fixed nonzero period, since the two are rationally dependent. -/
theorem exists_real_smul_of_mem_periodSubgroup {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) {ω p : ℂ}
    (hω : ω ∈ periodSubgroup f) (hω0 : ω ≠ 0) (hp : p ∈ periodSubgroup f) :
    ∃ r : ℝ, p = r • ω := by
  have hdep : ¬ LinearIndependent ℚ ![p, ω] :=
    rat_dependent_periods_of_hypertranscendental hNF hHT hp hω
  rw [linearIndependent_fin2] at hdep
  push Not at hdep
  obtain ⟨a, ha⟩ := hdep (by simpa using hω0)
  have ha' : a • ω = p := by simpa using ha
  refine ⟨(a : ℝ), ?_⟩
  rw [← ha', Complex.real_smul, Rat.smul_def]
  norm_cast

/-! ### The coefficient subgroup -/

/-- The real coefficients of the periods relative to a fixed direction. -/
noncomputable def periodCoeffSubgroup (f : ℂ → ℂ) (ω : ℂ) : AddSubgroup ℝ :=
  AddSubgroup.comap (LinearMap.toSpanSingleton ℝ ℂ ω).toAddMonoidHom (periodSubgroup f)

@[simp]
theorem mem_periodCoeffSubgroup {f : ℂ → ℂ} {ω : ℂ} {r : ℝ} :
    r ∈ periodCoeffSubgroup f ω ↔ Function.Periodic f (r • ω) := Iff.rfl

/-! ### A dense coefficient group is impossible -/

/-- **A dense coefficient group forces constancy.**  Arbitrarily small nonzero real coefficients give
arbitrarily small nonzero periods, and a meromorphic normal-form function with those is constant. -/
theorem not_dense_periodCoeffSubgroup {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) {ω : ℂ} (hω0 : ω ≠ 0) :
    ¬ Dense ((periodCoeffSubgroup f ω : Set ℝ)) := by
  intro hdense
  have hstep : ∀ n : ℕ, ∃ r : ℝ, r ∈ periodCoeffSubgroup f ω ∧ 0 < r ∧ r < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨r, hrS, hrI⟩ := hdense.exists_mem_open isOpen_Ioo
      ⟨1 / (2 * (n + 1)), by
        constructor
        · positivity
        · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          exact one_div_lt_one_div_of_lt h1 (by linarith)⟩
    exact ⟨r, hrS, hrI.1, hrI.2⟩
  choose r hrS hrpos hrlt using hstep
  refine hHT (differentiallyAlgebraic_of_const
    (meromorphicNF_constant_of_small_periods f hNF (fun n => r n • ω) ?_ ?_ ?_))
  · have hbound : ∀ n : ℕ, ‖r n • ω‖ ≤ 1 / ((n : ℝ) + 1) * ‖ω‖ := by
      intro n
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hrpos n)]
      exact mul_le_mul_of_nonneg_right (le_of_lt (hrlt n)) (norm_nonneg ω)
    have htend : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖ω‖) atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖ω‖
    exact squeeze_zero_norm hbound htend
  · intro n
    exact smul_ne_zero (ne_of_gt (hrpos n)) hω0
  · intro n
    exact hrS n

/-! ### The law -/

/-- **The period group of a hypertranscendental meromorphic function is cyclic.**  Any two periods
are rationally dependent, so the group lies on one real line; a subgroup of a line is dense or
cyclic, and dense is excluded because arbitrarily small periods force constancy. -/
theorem exists_periodSubgroup_eq_closure_singleton {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) :
    ∃ ω : ℂ, periodSubgroup f = AddSubgroup.closure {ω} := by
  by_cases htriv : periodSubgroup f = ⊥
  · refine ⟨0, ?_⟩
    rw [htriv]
    refine (le_antisymm ?_ bot_le).symm
    rw [AddSubgroup.closure_le]
    rintro _ rfl
    exact AddSubgroup.zero_mem _
  have hex : ∃ ω ∈ periodSubgroup f, ω ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact htriv ((AddSubgroup.eq_bot_iff_forall _).mpr hcon)
  obtain ⟨ω, hω, hω0⟩ := hex
  rcases AddSubgroup.dense_or_cyclic (periodCoeffSubgroup f ω) with hdense | ⟨a, ha⟩
  · exact absurd hdense (not_dense_periodCoeffSubgroup hNF hHT hω0)
  refine ⟨a • ω, ?_⟩
  have hamem : a ∈ periodCoeffSubgroup f ω := by
    rw [ha]
    exact AddSubgroup.subset_closure rfl
  refine le_antisymm ?_ ?_
  · intro p hp
    obtain ⟨s, hs⟩ := exists_real_smul_of_mem_periodSubgroup hNF hHT hω hω0 hp
    have hsmem : s ∈ periodCoeffSubgroup f ω := by
      rw [mem_periodCoeffSubgroup, ← hs]
      exact hp
    rw [ha, AddSubgroup.mem_closure_singleton] at hsmem
    obtain ⟨k, hk⟩ := hsmem
    rw [AddSubgroup.mem_closure_singleton]
    refine ⟨k, ?_⟩
    rw [hs, ← hk]
    exact (smul_assoc k a ω).symm
  · rw [AddSubgroup.closure_le]
    rintro _ rfl
    exact hamem

/-- The period group is trivial or infinite cyclic: no hypertranscendental meromorphic function has
a period group of rank two, and none has a non-discrete one. -/
theorem periodSubgroup_eq_zmultiples {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) (hHT : Hypertranscendental f) :
    ∃ ω : ℂ, periodSubgroup f = AddSubgroup.zmultiples ω := by
  obtain ⟨ω, hω⟩ := exists_periodSubgroup_eq_closure_singleton hNF hHT
  refine ⟨ω, ?_⟩
  rw [hω]
  ext x
  simp [AddSubgroup.mem_closure_singleton, AddSubgroup.mem_zmultiples_iff]

end GaloisForLFunctions.HTGeometry
