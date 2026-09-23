import GaloisForLFunctions.HTGeometry.LidskiiSelfAdjoint
import GaloisForLFunctions.HTGeometry.CompactCommutingFlowDecomposition

/-!
# Multiplicity of signed-greedy eigenvalues

For a compact self-adjoint operator, the signed-greedy exhaustion lists every nonzero
eigenvalue with exactly its geometric multiplicity.  This is the multiplicity-strengthened
form of spectral exhaustion needed to pass from regularized determinant divisors to ordered
singular values.
-/

open Filter Set
open scoped InnerProductSpace

namespace ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero value has a finite fibre in the signed-greedy spectrum. -/
theorem finite_sgVal_fiber {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {c : ℝ} (hc : c ≠ 0) :
    {n : ℕ | sgVal S n = c}.Finite := by
  have hlim : Tendsto (fun n => |sgVal S n|) atTop (nhds 0) := by
    convert sgOrthSup_tendsto_zero hcpt hsym using 1
    ext n
    exact abs_sgVal hcpt hsym n
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually_lt_const (abs_pos.mpr hc))
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_Iio] at hn ⊢
  by_contra hnot
  have hlt := hN n (Nat.le_of_not_gt hnot)
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/-- Every nonzero signed-greedy eigenvalue occurs exactly as many times as the dimension of its
ordinary eigenspace. -/
theorem finrank_eigenspace_eq_ncard_sgVal_fiber
    {S : H →L[ℂ] H} (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric)
    {c : ℝ} (hc : c ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (S : H →ₗ[ℂ] H) (c : ℂ)) =
      Set.ncard {n : ℕ | sgVal S n = c} := by
  let I : Set ℕ := {n | sgVal S n = c}
  have hIfin : I.Finite := finite_sgVal_fiber hcpt hsym hc
  letI : Fintype I := hIfin.fintype
  let W := Module.End.eigenspace (S : H →ₗ[ℂ] H) (c : ℂ)
  letI : FiniteDimensional ℂ W :=
    GaloisForLFunctions.HTGeometry.finiteDimensional_eigenspace_of_isCompactOperator hcpt
      (Complex.ofReal_ne_zero.mpr hc)
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  let g : I → W := fun n =>
    ⟨sgVec S n.1, Module.End.mem_eigenspace_iff.mpr (by
      change S (sgVec S n.1) = (c : ℂ) • sgVec S n.1
      rw [apply_sgVec S n.1, n.2])⟩
  have hg : Orthonormal ℂ g := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      have hnorm : ‖sgVec S i.1‖ = 1 := by
        rcases norm_sgVec_zero_or_one S i.1 with hzero | hone
        · have hval := sgVal_zero_of_dead hzero
          rw [i.2] at hval
          exact (hc hval).elim
        · exact hone
      change ((‖sgVec S i.1‖ : ℝ) : ℂ) ^ (2 : ℕ) = 1
      rw [hnorm]
      norm_num
    · rw [if_neg hij]
      change inner ℂ (sgVec S i.1) (sgVec S j.1) = 0
      exact inner_sgVec_sgVec_of_ne S (fun h => hij (Subtype.ext h))
  have hspan : Submodule.span ℂ (Set.range g) = ⊤ := by
    letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
    rw [← Submodule.orthogonal_eq_bot_iff]
    apply bot_unique
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    have hxI : ∀ i : I, inner ℂ (sgVec S i.1) (x : H) = 0 := by
      intro i
      have horth := (Submodule.mem_orthogonal' _ _).mp hx (g i)
        (Submodule.subset_span ⟨i, rfl⟩)
      change inner ℂ (x : H) (sgVec S i.1) = 0 at horth
      rw [← inner_conj_symm, horth, map_zero]
    have hxall : ∀ n, inner ℂ (sgVec S n) (x : H) = 0 := by
      intro n
      by_cases hn : sgVal S n = c
      · exact hxI ⟨n, hn⟩
      · have h1 : inner ℂ (sgVec S n) (S (x : H)) =
            (c : ℂ) * inner ℂ (sgVec S n) (x : H) := by
          rw [show S (x : H) = (c : ℂ) • (x : H) from
            Module.End.mem_eigenspace_iff.mp x.2, inner_smul_right]
        have h2 : inner ℂ (sgVec S n) (S (x : H)) =
            ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) (x : H) := by
          calc
            inner ℂ (sgVec S n) (S (x : H)) =
                inner ℂ (S (sgVec S n)) (x : H) := (hsym _ _).symm
            _ = inner ℂ (((sgVal S n : ℝ) : ℂ) • sgVec S n) (x : H) := by
              rw [apply_sgVec]
            _ = ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) (x : H) := by
              rw [inner_smul_left]
              simp
        have hprod : ((c : ℂ) - ((sgVal S n : ℝ) : ℂ)) *
            inner ℂ (sgVec S n) (x : H) = 0 := by
          rw [sub_mul, ← h1, ← h2, sub_self]
        exact (mul_eq_zero.mp hprod).resolve_left (by
          exact sub_ne_zero.mpr (Complex.ofReal_injective.ne (Ne.symm hn)))
    have hzero := apply_eq_zero_of_forall_inner_sgVec hcpt hsym hxall
    have heig : S (x : H) = (c : ℂ) • (x : H) :=
      Module.End.mem_eigenspace_iff.mp x.2
    rw [heig] at hzero
    exact (smul_eq_zero.mp hzero).resolve_left (Complex.ofReal_ne_zero.mpr hc)
  have hdim := finrank_span_eq_card hg.linearIndependent
  rw [hspan] at hdim
  have hcard : Set.ncard I = Fintype.card I := by
    rw [Set.ncard_eq_toFinset_card I]
    exact Set.toFinset_card I
  change Module.finrank ℂ W = Set.ncard I
  calc
    Module.finrank ℂ W =
        Module.finrank ℂ (↥(⊤ : Submodule ℂ W)) :=
      Submodule.topEquiv.finrank_eq.symm
    _ = Fintype.card I := hdim
    _ = Set.ncard I := hcard.symm

end

end ContinuousLinearMap
