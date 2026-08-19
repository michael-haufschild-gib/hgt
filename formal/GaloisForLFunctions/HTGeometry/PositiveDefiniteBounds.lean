import GaloisForLFunctions.HTGeometry.PositiveDefiniteConeAction

/-!
# Uniform bounds for a compact family of positive definite forms

On a compact set of positive definite forms the quadratic form is uniformly bounded above and
uniformly bounded below by a positive constant, because it is continuous and positive on the compact
product with the unit sphere.

These bounds are what turns integrality into finiteness: a unimodular integer matrix carrying one
compact family of forms into another has bounded entries.

* `exists_lower_bound_of_isCompact` : **a positive uniform lower bound.**
* `exists_upper_bound_of_isCompact` : a uniform upper bound.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The quadratic form, as a function of the matrix and the vector. -/
noncomputable def quadForm (A : posDefCone n) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) *ᵥ x)

theorem continuous_quadForm :
    Continuous (fun p : (posDefCone n) × (Metric.sphere (0 : Fin n → ℝ) 1) =>
      quadForm p.1 (p.2 : Fin n → ℝ)) := by
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.mul ((continuous_apply i).comp
    (continuous_subtype_val.comp continuous_snd)) ?_
  refine continuous_finsetSum _ fun j _ => ?_
  refine Continuous.mul ?_
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  exact (continuous_apply j).comp ((continuous_apply i).comp
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)))

theorem quadForm_pos (A : posDefCone n) {x : Fin n → ℝ} (hx : ‖x‖ = 1) : 0 < quadForm A x :=
  (posDef_iff_sphere (isHermitian_of_mem_symmMatrices (A : symmMatrices n).2)).1 A.2 x hx

/-- **A positive uniform lower bound on a compact family of positive definite forms.** -/
theorem exists_lower_bound_of_isCompact {K : Set (posDefCone n)} (hK : IsCompact K)
    (hn : 0 < n) :
    ∃ m : ℝ, 0 < m ∧ ∀ A ∈ K, ∀ x : Fin n → ℝ, ‖x‖ = 1 → m ≤ quadForm A x := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → ℝ) := Function.nontrivial
  haveI : Nonempty (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  haveI : CompactSpace (Metric.sphere (0 : Fin n → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  have hKprod : IsCompact (K ×ˢ (Set.univ : Set (Metric.sphere (0 : Fin n → ℝ) 1))) :=
    hK.prod isCompact_univ
  obtain ⟨p, hp, hmin⟩ := hKprod.exists_isMinOn
    (hKne.prod ⟨Classical.arbitrary _, Set.mem_univ _⟩)
    (continuous_quadForm.continuousOn)
  refine ⟨quadForm p.1 (p.2 : Fin n → ℝ), quadForm_pos p.1
    (mem_sphere_zero_iff_norm.mp p.2.2), ?_⟩
  intro A hA x hx
  exact hmin ⟨hA, Set.mem_univ _⟩ (a := (A, ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩))

/-- A uniform upper bound on a compact family of positive definite forms. -/
theorem exists_upper_bound_of_isCompact {K : Set (posDefCone n)} (hK : IsCompact K)
    (hn : 0 < n) :
    ∃ M : ℝ, ∀ A ∈ K, ∀ x : Fin n → ℝ, ‖x‖ = 1 → quadForm A x ≤ M := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → ℝ) := Function.nontrivial
  haveI : Nonempty (Metric.sphere (0 : Fin n → ℝ) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  haveI : CompactSpace (Metric.sphere (0 : Fin n → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, by simp⟩
  have hKprod : IsCompact (K ×ˢ (Set.univ : Set (Metric.sphere (0 : Fin n → ℝ) 1))) :=
    hK.prod isCompact_univ
  obtain ⟨p, hp, hmax⟩ := hKprod.exists_isMaxOn
    (hKne.prod ⟨Classical.arbitrary _, Set.mem_univ _⟩)
    (continuous_quadForm.continuousOn)
  refine ⟨quadForm p.1 (p.2 : Fin n → ℝ), ?_⟩
  intro A hA x hx
  exact hmax ⟨hA, Set.mem_univ _⟩ (a := (A, ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩))

theorem quadForm_smul (A : posDefCone n) (c : ℝ) (x : Fin n → ℝ) :
    quadForm A (c • x) = c ^ 2 * quadForm A x := by
  unfold quadForm
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← pow_two]

theorem quadForm_zero (A : posDefCone n) : quadForm A 0 = 0 := by
  unfold quadForm
  rw [Matrix.mulVec_zero, dotProduct_zero]

/-- A uniform lower bound on the sphere is a uniform lower bound for the quadratic form. -/
theorem quadForm_ge_of_sphere_bound {A : posDefCone n} {m : ℝ}
    (h : ∀ x : Fin n → ℝ, ‖x‖ = 1 → m ≤ quadForm A x) (y : Fin n → ℝ) :
    m * ‖y‖ ^ 2 ≤ quadForm A y := by
  by_cases hy : y = 0
  · subst hy
    rw [quadForm_zero, norm_zero]
    simp
  · have hnorm : ‖y‖ ≠ 0 := by simpa using hy
    have hunit : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
    have hb := h _ hunit
    rw [quadForm_smul] at hb
    have hsq : (0 : ℝ) < ‖y‖ ^ 2 := by positivity
    have hinv : (‖y‖⁻¹) ^ 2 * ‖y‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hnorm, one_pow]
    calc m * ‖y‖ ^ 2 ≤ ((‖y‖⁻¹) ^ 2 * quadForm A y) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hb (le_of_lt hsq)
      _ = ((‖y‖⁻¹) ^ 2 * ‖y‖ ^ 2) * quadForm A y := by ring
      _ = quadForm A y := by rw [hinv, one_mul]

/-- The quadratic form of a congruent matrix. -/
theorem quadForm_smul_group (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : posDefCone n)
    (x : Fin n → ℝ) :
    quadForm (g • A) x = quadForm A ((slReal g)ᵀ *ᵥ x) := by
  unfold quadForm
  rw [posDefCone_smul_coe]
  rw [show ((slReal g * ((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ) * (slReal g)ᵀ) *ᵥ x)
      = slReal g *ᵥ ((((A : symmMatrices n) : Matrix (Fin n) (Fin n) ℝ)) *ᵥ ((slReal g)ᵀ *ᵥ x)) by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem norm_single_one (j : Fin n) : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
  refine le_antisymm (pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun i => ?_) ?_
  · by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · have := norm_le_pi_norm (Pi.single j (1 : ℝ) : Fin n → ℝ) j
    simpa using this

/-- **Entries of a group element carrying one bounded family of forms into another are bounded.** -/
theorem entry_bound {K : Set (posDefCone n)} {m M : ℝ} (hm : 0 < m)
    (hlow : ∀ A ∈ K, ∀ x : Fin n → ℝ, ‖x‖ = 1 → m ≤ quadForm A x)
    (hup : ∀ A ∈ K, ∀ x : Fin n → ℝ, ‖x‖ = 1 → quadForm A x ≤ M)
    {g : Matrix.SpecialLinearGroup (Fin n) ℤ} {A : posDefCone n} (hA : A ∈ K)
    (hgA : g • A ∈ K) (i j : Fin n) :
    |slReal g j i| ≤ Real.sqrt (M / m) := by
  have hx : ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ = 1 := norm_single_one j
  have hge := quadForm_ge_of_sphere_bound (hlow A hA) ((slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ)))
  have hle : quadForm A ((slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))) ≤ M := by
    rw [← quadForm_smul_group]
    exact hup _ hgA _ hx
  have hbound : m * ‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖ ^ 2 ≤ M := le_trans hge hle
  have hnormsq : ‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖ ^ 2 ≤ M / m := by
    rw [le_div_iff₀ hm, mul_comm]
    exact hbound
  have hentry : |slReal g j i| ≤ ‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖ := by
    have hval : ((slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))) i = slReal g j i := by
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    have := norm_le_pi_norm ((slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))) i
    rw [hval] at this
    simpa [Real.norm_eq_abs] using this
  have hnn : (0 : ℝ) ≤ ‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖ := norm_nonneg _
  refine le_trans hentry ?_
  rw [show ‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖
      = Real.sqrt (‖(slReal g)ᵀ *ᵥ (Pi.single j (1 : ℝ))‖ ^ 2) from
    (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hnormsq

theorem finite_entries_bounded (N : ℤ) :
    {g : Matrix.SpecialLinearGroup (Fin n) ℤ |
      ∀ i j, |(g : Matrix (Fin n) (Fin n) ℤ) i j| ≤ N}.Finite := by
  classical
  have hfin : {f : Fin n → Fin n → ℤ | ∀ i j, |f i j| ≤ N}.Finite := by
    have hpi : {f : Fin n → Fin n → ℤ | ∀ i j, |f i j| ≤ N}
        = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Set.Icc (-N) N)) := by
      ext f
      constructor
      · intro h i _ j _
        exact abs_le.1 (h i j)
      · intro h i j
        exact abs_le.2 (h i (Set.mem_univ i) j (Set.mem_univ j))
    rw [hpi]
    exact Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  refine Set.Finite.of_finite_image
    (f := fun g : Matrix.SpecialLinearGroup (Fin n) ℤ => (g : Matrix (Fin n) (Fin n) ℤ)) ?_ ?_
  · refine hfin.subset ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hg
  · exact Set.injOn_of_injective (fun a b hab => Subtype.ext hab)

/-- **The action of `SL(n, ℤ)` on the positive definite cone is properly discontinuous.**  A group
element carrying a compact family of forms into another has bounded entries, and there are finitely
many integer matrices with bounded entries. -/
theorem finite_meet_of_isCompact {K L : Set (posDefCone n)} (hK : IsCompact K) (hL : IsCompact L) :
    {g : Matrix.SpecialLinearGroup (Fin n) ℤ |
      (((fun A => g • A) '' K) ∩ L).Nonempty}.Finite := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℤ) := ⟨fun _ _ => funext fun i => i.elim0⟩
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) ℤ) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : Finite (Matrix.SpecialLinearGroup (Fin 0) ℤ) := Finite.of_subsingleton
    exact Set.toFinite _
  obtain ⟨m, hm, hlow⟩ := exists_lower_bound_of_isCompact (hK.union hL) hn
  obtain ⟨M, hup⟩ := exists_upper_bound_of_isCompact (hK.union hL) hn
  refine Set.Finite.subset (finite_entries_bounded (n := n) ⌈Real.sqrt (M / m)⌉) ?_
  rintro g ⟨z, ⟨A, hA, rfl⟩, hgA⟩
  intro i j
  have hbound := entry_bound hm hlow hup (Or.inl hA) (Or.inr hgA) j i
  have hcast : |slReal g i j| = ((|(g : Matrix (Fin n) (Fin n) ℤ) i j| : ℤ) : ℝ) := by
    show |((((g : Matrix (Fin n) (Fin n) ℤ) i j : ℤ)) : ℝ)| = _
    rw [← Int.cast_abs]
  rw [hcast] at hbound
  have hceil : ((|(g : Matrix (Fin n) (Fin n) ℤ) i j| : ℤ) : ℝ) ≤ ((⌈Real.sqrt (M / m)⌉ : ℤ) : ℝ) :=
    le_trans hbound (Int.le_ceil _)
  exact_mod_cast hceil

instance properlyDiscontinuousSMul_posDefCone :
    ProperlyDiscontinuousSMul (Matrix.SpecialLinearGroup (Fin n) ℤ) (posDefCone n) where
  finite_disjoint_inter_image hK hL := finite_meet_of_isCompact hK hL

end GaloisForLFunctions.HTGeometry
