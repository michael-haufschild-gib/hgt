import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierSelfMap
import GaloisForLFunctions.RHTower.CCMRationalFiniteAdeleNonarchimedean

/-!
# Simultaneous finite-level control on a finite product of p-adic fields

Every compactly supported locally constant function on a finite dependent
product of p-adic fields has coordinatewise denominator depths containing its
entire support and coordinatewise translation depths giving one global
product-lattice period.  This is the exact simultaneous finite quotient used
by finite-stage CCM Fourier analysis.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Set Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- Finite dependent product of literal p-adic fields. -/
abbrev FieldOnePadicProduct := (i : ι) → ℚ_[p i]

/-- Product of their integral unit balls. -/
abbrev FieldOnePadicIntProduct := (i : ι) → ℤ_[p i]

/-- Additive embedding into one coordinate of a p-adic product. -/
def fieldOnePadicProductSingle (i : ι) :
    ℚ_[p i] →+ FieldOnePadicProduct p where
  toFun z := Function.update 0 i z
  map_zero' := by
    ext j
    by_cases h : j = i <;> simp [h]
  map_add' x y := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update, h]

omit [Fintype ι] in
/-- Every coordinate embedding is continuous. -/
theorem fieldOnePadicProductSingle_continuous (i : ι) :
    Continuous (fieldOnePadicProductSingle p i) := by
  exact continuous_const.update i continuous_id

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinatewise denominator depths contain the entire topological support
of a p-adic product Bruhat function. -/
theorem fieldOnePadicProductBruhat_exists_supportDepth
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    ∃ n : ι → ℕ,
      ∀ x ∈ tsupport (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i) := by
  choose n hn using fun i =>
    fieldOnePadic_isCompact_exists_commonDenominatorStage
      (p i) (f.2.image (continuous_apply i))
  refine ⟨n, fun x hx i => hn i ?_⟩
  exact ⟨x, hx, rfl⟩

/-- The canonical topology on `ℚ_p` has a basis of open additive subgroups. -/
theorem fieldOnePadic_nonarchimedeanAddGroup
    (q : ℕ) [Fact q.Prime] : NonarchimedeanAddGroup ℚ_[q] where
  is_nonarchimedean U hU := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let H : AddSubgroup ℚ_[q] :=
      { carrier := Metric.ball 0 ε
        zero_mem' := by simpa using hε
        add_mem' := by
          intro x y hx hy
          rw [Metric.mem_ball, dist_zero_right] at hx hy ⊢
          exact (Padic.nonarchimedean x y).trans_lt (max_lt hx hy)
        neg_mem' := by
          intro x hx
          simpa [Metric.mem_ball, dist_zero_right] using hx }
    let V : OpenAddSubgroup ℚ_[q] :=
      { toAddSubgroup := H
        isOpen' := Metric.isOpen_ball }
    exact ⟨V, hball⟩

/-- Coordinatewise prime-power lattices combine to one global translation
period of every p-adic product Bruhat function. -/
theorem fieldOnePadicProductBruhat_exists_periodDepth
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    ∃ m : ι → ℕ,
      ∀ x : FieldOnePadicProduct p, ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ (m i) * (z i : ℚ_[p i])) = f.1 x := by
  letI (i : ι) : NonarchimedeanAddGroup ℚ_[p i] :=
    fieldOnePadic_nonarchimedeanAddGroup (p i)
  letI : NonarchimedeanAddGroup (FieldOnePadicProduct p) :=
    nonarchimedeanAddGroup_pi _
  obtain ⟨V, hV⟩ :=
    compactlySupportedLocallyConstant_exists_openAddSubgroup_stabilizer
      (FieldOnePadicProduct p) ℂ f.1 f.1.isLocallyConstant f.2
  let W (i : ι) : OpenAddSubgroup ℚ_[p i] :=
    V.comap (fieldOnePadicProductSingle p i)
      (fieldOnePadicProductSingle_continuous p i)
  choose m hm using fun i =>
    fieldOnePadicOpenAddSubgroup_exists_primePowerLattice (p i) (W i)
  refine ⟨m, fun x z => ?_⟩
  let t : FieldOnePadicProduct p :=
    fun i => (p i : ℚ_[p i]) ^ (m i) * (z i : ℚ_[p i])
  have ht : t ∈ V := by
    have htSum : t = ∑ i, fieldOnePadicProductSingle p i (t i) := by
      ext j
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · simp [fieldOnePadicProductSingle, t]
      · intro i _ hi
        have hji : j ≠ i := Ne.symm hi
        simp [fieldOnePadicProductSingle, Function.update, hji]
      · simp
    rw [htSum]
    apply sum_mem
    intro i _
    exact hm i (z i)
  exact hV x ⟨t, ht⟩

/-- Every p-adic product Bruhat function reduces globally to one finite
product of cyclic prime-power quotients. -/
theorem fieldOnePadicProductBruhat_exists_finiteLevel
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    ∃ n m : ι → ℕ,
      (∀ x ∈ tsupport (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i)) ∧
      (∀ x : FieldOnePadicProduct p, ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ (m i) * (z i : ℚ_[p i])) = f.1 x) := by
  obtain ⟨n, hn⟩ := fieldOnePadicProductBruhat_exists_supportDepth p f
  obtain ⟨m, hm⟩ := fieldOnePadicProductBruhat_exists_periodDepth p f
  exact ⟨n, m, hn, hm⟩

end

end GaloisForLFunctions.RHTower
