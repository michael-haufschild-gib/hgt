import GaloisForLFunctions.HTGeometry.DifferentialOperatorCyclicDimension
import GaloisForLFunctions.HTGeometry.DifferentialOperatorPrincipalIdeal

/-!
# Torsion elements span finite-dimensional subspaces

An element of a module over the operator ring annihilated by a nonzero operator `b` generates a
subspace of dimension at most `deg b` over the coefficient field: the cyclic module it generates is
a quotient of `K[∂;δ] / K[∂;δ] b`.

This is the step that converts a torsion lattice quotient into a finite-dimensional one, which is
the constant appearing in the comparison of Cartan vectors.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {M : Type*} [AddCommGroup M] [Module (DiffOp K) M] [Module K M]
  [IsScalarTower K (DiffOp K) M]

/-- Multiplication of a fixed element by operators, as a `K`-linear map. -/
def smulRight (t : M) : DiffOp K →ₗ[K] M where
  toFun r := r • t
  map_add' r₁ r₂ := by rw [add_smul]
  map_smul' a r := by
    rw [RingHom.id_apply, smul_assoc]

@[simp] theorem smulRight_apply (t : M) (r : DiffOp K) : smulRight t r = r • t := rfl

theorem range_smulRight (t : M) :
    LinearMap.range (smulRight t) = (Submodule.span (DiffOp K) {t}).restrictScalars K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨r, rfl⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨r, hr⟩

/-- **A torsion element spans a finite-dimensional subspace.** -/
theorem finiteDimensional_span_singleton {t : M} {b : DiffOp K} (hb : b ≠ 0) (ht : b • t = 0) :
    FiniteDimensional K ((Submodule.span (DiffOp K) {t}).restrictScalars K) := by
  classical
  have hker : leftMultiples b ≤ LinearMap.ker (smulRight t) := by
    rintro _ ⟨q, rfl⟩
    show (q * b) • t = 0
    rw [mul_smul, ht, smul_zero]
  haveI := finiteDimensional_quotient_leftMultiples hb
  have hrange : (Submodule.span (DiffOp K) {t}).restrictScalars K
      = LinearMap.range (Submodule.liftQ (leftMultiples b) (smulRight t) hker) := by
    rw [Submodule.range_liftQ, range_smulRight]
  rw [hrange]
  exact (Submodule.liftQ (leftMultiples b) (smulRight t) hker).finiteDimensional_range


/-- **A finitely generated torsion module is finite-dimensional.**  If every element of a finitely
generated submodule is annihilated by some nonzero operator, the submodule has finite dimension
over the coefficient field. -/
theorem finiteDimensional_of_fg_torsion {N : Submodule (DiffOp K) M} (hfg : N.FG)
    (htors : ∀ t : M, t ∈ N → ∃ b : DiffOp K, b ≠ 0 ∧ b • t = 0) :
    FiniteDimensional K (N.restrictScalars K) := by
  classical
  have key : ∀ s : Finset M, (∀ t ∈ s, ∃ b : DiffOp K, b ≠ 0 ∧ b • t = 0) →
      FiniteDimensional K ((Submodule.span (DiffOp K) (↑s : Set M)).restrictScalars K) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.coe_empty, Submodule.span_empty, Submodule.restrictScalars_bot]
      infer_instance
    | insert a s ha ih =>
      intro htor
      have hins : (↑(insert a s) : Set M) = insert a (↑s : Set M) := by simp
      rw [hins, Submodule.span_insert, Submodule.restrictScalars_sup]
      haveI : FiniteDimensional K ((Submodule.span (DiffOp K) {a}).restrictScalars K) := by
        obtain ⟨b, hb, hba⟩ := htor a (Finset.mem_insert_self a s)
        exact finiteDimensional_span_singleton hb hba
      haveI := ih fun t ht => htor t (Finset.mem_insert_of_mem ht)
      infer_instance
  obtain ⟨s, hs⟩ := hfg
  have hsub : ∀ t ∈ s, ∃ b : DiffOp K, b ≠ 0 ∧ b • t = 0 := by
    intro t ht
    refine htors t ?_
    rw [← hs]
    exact Submodule.subset_span ht
  have hfin := key s hsub
  rw [hs] at hfin
  exact hfin


theorem C_smul (a : K) (t : M) : (C a : DiffOp K) • t = a • t := by
  have hC : (C a : DiffOp K) = a • (1 : DiffOp K) := by
    rw [one_def, smul_mono, mul_one]
    rfl
  rw [hC, smul_assoc, one_smul]

theorem mono_smul (k : ℕ) (a : K) (t : M) :
    (mono k a : DiffOp K) • t = a • ((X : DiffOp K) ^ k • t) := by
  rw [mono_eq_C_mul_X_pow, mul_smul, C_smul]

theorem truncLT_smul {n : ℕ} (c : Fin n → K) (t : M) :
    (truncLT c : DiffOp K) • t = ∑ k : Fin n, c k • ((X : DiffOp K) ^ (k : ℕ) • t) := by
  rw [truncLT, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mono_smul]

/-- **Finite dimension of a torsion lattice quotient.**  If `Λ` is finitely generated over the
operator ring and every element of `Λ` has a nonzero operator multiple inside `L ≤ Λ`, then the
image of `Λ` in the quotient by `L` is finite-dimensional over the coefficient field. -/
theorem finiteDimensional_map_mkQ_of_fg_torsion {L Λ : Submodule (DiffOp K) M}
    (hfg : Λ.FG) (htors : ∀ t ∈ Λ, ∃ b : DiffOp K, b ≠ 0 ∧ b • t ∈ L) :
    FiniteDimensional K ((Λ.restrictScalars K).map (L.restrictScalars K).mkQ) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hex : ∀ t : M, ∃ bt : DiffOp K, t ∈ Λ → (bt ≠ 0 ∧ bt • t ∈ L) := by
    intro t
    by_cases ht : t ∈ Λ
    · obtain ⟨bt, hbt, hbtL⟩ := htors t ht
      exact ⟨bt, fun _ => ⟨hbt, hbtL⟩⟩
    · exact ⟨1, fun h => absurd h ht⟩
  choose b hb using hex
  have hsmem : ∀ t ∈ s, t ∈ Λ := by
    intro t ht
    rw [← hs]
    exact Submodule.subset_span ht
  set T : Finset M :=
    s.biUnion fun t => (Finset.range (degree (b t))).image fun k => (X : DiffOp K) ^ k • t
    with hT
  have hspan : (Λ.restrictScalars K).map (L.restrictScalars K).mkQ
      ≤ Submodule.span K ((L.restrictScalars K).mkQ '' (↑T : Set M)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyΛ : y ∈ Λ := hy
    rw [← hs] at hyΛ
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hyΛ
    rw [← hf, map_sum]
    refine Submodule.sum_mem _ fun t ht => ?_
    obtain ⟨hbt0, hbtL⟩ := hb t (hsmem t ht)
    obtain ⟨q, rem, hqr, hrem⟩ := exists_right_div hbt0 (f t)
    have hsplit : f t • t = q • (b t • t) + rem • t := by
      rw [hqr, add_smul, mul_smul]
    have hkill : (L.restrictScalars K).mkQ (q • (b t • t)) = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      exact L.smul_mem q hbtL
    have hremtrunc : ∃ c : Fin (degree (b t)) → K, rem = truncLT c := by
      rcases hrem with hzero | hlt
      · exact ⟨0, by rw [hzero, truncLT_zero]⟩
      · exact ⟨fun k : Fin (degree (b t)) => coeff rem (k : ℕ), (truncLT_coeff rem hlt).symm⟩
    obtain ⟨c, hc⟩ := hremtrunc
    rw [hsplit, map_add, hkill, zero_add, hc, truncLT_smul, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨(X : DiffOp K) ^ (k : ℕ) • t, ?_, rfl⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩)
    exact Finset.mem_image.mpr ⟨(k : ℕ), Finset.mem_range.mpr k.isLt, rfl⟩
  haveI : FiniteDimensional K
      (Submodule.span K ((L.restrictScalars K).mkQ '' (↑T : Set M))) := by
    refine FiniteDimensional.span_of_finite K ?_
    exact (T.finite_toSet).image _
  exact Submodule.finiteDimensional_of_le hspan

end

end DiffOp

end GaloisForLFunctions.HTGeometry
