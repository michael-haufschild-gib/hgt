import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral

/-! Every projective coordinate chart is a polynomial algebra, with
the original field as its fraction field. -/

noncomputable section

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

/-- The (d) coordinate ratios on the chart with denominator (x_i). -/
def chartCoordinates (x : Fin (d + 1) → F) (i : Fin (d + 1)) : Fin d → F :=
  fun j => x (i.succAbove j) / x i

theorem rA_single_eq_adjoin (h : IsPd k x) (i : Fin (d + 1)) :
    rA k x {i} = Algebra.adjoin k (Set.range (chartCoordinates x i)) := by
  rw [rA]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨i', hi', j, rfl⟩
    have e : i' = i := Finset.mem_singleton.mp hi'
    subst i'
    rcases eq_or_ne j i with rfl | hn
    · rw [div_self (h.ne _)]
      exact one_mem _
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hn
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩

theorem IsPd.adjoin_chartCoordinates (h : IsPd k x) (i : Fin (d + 1)) :
    IntermediateField.adjoin k (Set.range (chartCoordinates x i)) = ⊤ := by
  let E := IntermediateField.adjoin k (Set.range (chartCoordinates x i))
  have hmem (j : Fin (d + 1)) : x j / x i ∈ E := by
    rcases eq_or_ne j i with rfl | hn
    · rw [div_self (h.ne _)]
      exact E.one_mem
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hn
      exact IntermediateField.subset_adjoin k _ ⟨l, rfl⟩
  rw [eq_top_iff, ← h.gen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  exact (div_div_div_cancel_right₀ (h.ne i)) ▸ E.div_mem (hmem j.succ) (hmem 0)

private theorem isFractionRing_adjoin_of_adjoin_eq_top (S : Set F)
    (h : IntermediateField.adjoin k S = ⊤) : IsFractionRing (Algebra.adjoin k S) F := by
  refine IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_
  have hz : z ∈ IntermediateField.adjoin k S := h.symm ▸ IntermediateField.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

theorem IsPd.isFractionRing_rA (h : IsPd k x) (i : Fin (d + 1)) :
    IsFractionRing (rA k x {i}) F := by
  rw [rA_single_eq_adjoin h i]
  exact isFractionRing_adjoin_of_adjoin_eq_top _ (h.adjoin_chartCoordinates i)

/-- The affine chart coordinates are algebraically independent since
they generate the field and have its transcendence degree. -/
theorem IsPd.independent_chartCoordinates (h : IsPd k x) (i : Fin (d + 1)) :
    AlgebraicIndependent k (chartCoordinates x i) := by
  let y := chartCoordinates x i
  let A := Algebra.adjoin k (Set.range y)
  letI : IsFractionRing A F := isFractionRing_adjoin_of_adjoin_eq_top _ (h.adjoin_chartCoordinates i)
  letI : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k y
    h.indep.cardinalMk_le_trdeg).1

/-- Identify the polynomial algebra by sending its variables to the
ratios regular on the chosen coordinate chart. -/
def IsPd.chartPolynomialEquiv (h : IsPd k x) (i : Fin (d + 1)) :
    MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i} :=
  (h.independent_chartCoordinates i).aevalEquiv.trans
    (Subalgebra.equivOfEq _ _ (rA_single_eq_adjoin h i).symm)

theorem IsPd.chartPolynomialEquiv_X (h : IsPd k x) (i : Fin (d + 1)) (j : Fin d) :
    (h.chartPolynomialEquiv i (MvPolynomial.X j) : F) = chartCoordinates x i j := by
  simp [IsPd.chartPolynomialEquiv, AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
