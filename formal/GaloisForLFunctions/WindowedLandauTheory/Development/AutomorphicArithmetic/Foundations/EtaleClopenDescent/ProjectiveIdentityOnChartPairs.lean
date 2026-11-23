import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveAffineIdentityTensor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates

/-! Move a regular identity family to two different chart rings by
cancelling reciprocal coordinate denominators in the contraction. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

private theorem IsFinCover.exists_chartPairIdentityFamily (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (i j : Fin (d + 1)) :
    ∃ (n : ℕ) (u : Fin n → ExteriorDifferentials k E q) (v : Fin n → ExteriorDifferentials k E p),
      (∀ a, u a ∈ regularExteriorLattice (rB k E x {i}) q) ∧
      (∀ a, v a ∈ regularExteriorLattice (rB k E x {j}) p) ∧
      ∀ b : ExteriorDifferentials k E p,
        (∑ a, traceWedgeLeftDual (F := F) τ (u a) b • v a) = (∏ l, x l / x i) • b := by
  by_cases hij : i = j
  · subst j
    exact h.exists_affineIdentityFamily τ hτ hpq i
  obtain ⟨n, u, v, hu, hv, hsum⟩ := h.exists_affineIdentityFamily τ hτ hpq i
  let I : Finset (Fin (d + 1)) := {i, j}
  have hj : j ∈ I := by simp [I]
  have hi : i ∈ I := by simp [I]
  have hden : (chartDenominator k x I j : F) = x i / x j := by
    change (∏ l ∈ I, x l / x j) = _
    simp [I, Finset.prod_insert, hij, div_self (h.pd.ne j)]
  have hlocal (a : Fin n) : (v a : DR k E) ∈ omB k E (rB k E x I) p :=
    (mem_omB_chartIntersection_iff (E := E) h.pd hi (v a)).mpr
      ⟨0, by simpa only [pow_zero, one_smul] using hv a⟩
  choose N hN using fun a => (mem_omB_chartIntersection_iff (E := E) h.pd hj (v a)).mp (hlocal a)
  let s (a : Fin n) := (x j / x i) ^ N a
  let t (a : Fin n) := (x i / x j) ^ N a
  have hst (a : Fin n) : s a * t a = 1 := by
    change (x j / x i) ^ N a * (x i / x j) ^ N a = 1
    rw [← mul_pow, div_mul_div_cancel₀ (h.pd.ne i), div_self (h.pd.ne j), one_pow]
  refine ⟨n, fun a => s a • u a, fun a => t a • v a, ?_, ?_, ?_⟩
  · intro a
    let z : rA k x {i} := ⟨x j / x i, Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩⟩
    have hz : algebraMap F E (s a) ∈ rB k E x {i} :=
      isIntegral_algebraMap (x := z ^ N a)
    change (algebraMap F E (s a) • (u a : DR k E)) ∈ omB k E (rB k E x {i}) q
    exact smul_mem_omB hz (hu a)
  · intro a
    change (algebraMap F E (t a) • (v a : DR k E)) ∈ omB k E (rB k E x {j}) p
    rw [show t a = (x i / x j) ^ N a from rfl, map_pow]
    simpa only [hden] using hN a
  · intro b
    rw [← hsum b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_right_comm (s a), hst, one_mul]

/-- The diagonal identity admits a tensor representative regular in
the left and right chart separately. -/
theorem IsFinCover.exists_chartPairIdentityTensor (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (i j : Fin (d + 1)) :
    ∃ t ∈ tensorChartLattice (regularExteriorLattice (rB k E x {i}) q)
        (regularExteriorLattice (rB k E x {j}) p),
      ∀ a : ExteriorDifferentials k E p,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) t =
          (∏ l, x l / x i) • a := by
  obtain ⟨n, u, v, hu, hv, hsum⟩ := h.exists_chartPairIdentityFamily τ hτ hpq i j
  refine ⟨∑ a, u a ⊗ₜ[k] v a, Submodule.sum_mem _ fun a _ =>
    Submodule.apply_mem_map₂ _ (hu a) (hv a), ?_⟩
  intro a
  simpa only [map_sum, tensorContraction_tmul, LinearMap.flip_apply] using hsum a

end GlobalTheory.PD
