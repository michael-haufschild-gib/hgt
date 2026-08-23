import GaloisForLFunctions.RHTower.BurnolBiorthogonalJet
import GaloisForLFunctions.RHTower.BurnolMinimalWitness
import GaloisForLFunctions.HTGeometry.MinimalCompleteSystem

/-!
# The quotient system is minimal

Burnol's second system consists of the functions `ζ(s)/(s − ρ)^l`, one for every nontrivial zero
`ρ` and every index `1 ≤ l ≤ m_ρ`.  Each is the continued Mellin transform of a vector of the even
part of `L₁`, and the jet functionals of the previous file are biorthogonal to the family: the
functional attached to `(ρ, l)` reads the `(m_ρ − l)`-th Taylor coefficient of the transform
multiplied by the local unit of `ζ` at `ρ`, and this is a triangular combination of the evaluators
`Y_{ρ,k}`, `0 ≤ k < m_ρ`.  Biorthogonality gives minimality.

## Main results

* `isMinimalSystem_of_exists_functional`
* `IsZetaQuotientSystem`
* `IsZetaQuotientSystem.isMinimalSystem`
* `exists_zetaQuotientSystem`
* `burnol_theorem_three_three_minimal`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A system separated by bounded functionals is minimal: the closed span of the other members sits
inside a kernel on which the distinguished member does not vanish. -/
theorem isMinimalSystem_of_exists_functional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} {u : ι → E}
    (h : ∀ i, ∃ Λ : E →L[ℂ] ℂ, Λ (u i) = 1 ∧ ∀ j, j ≠ i → Λ (u j) = 0) :
    IsMinimalSystem ℂ u := by
  intro i hi
  obtain ⟨Λ, h1, h0⟩ := h i
  have hle : Submodule.span ℂ (u '' {j | j ≠ i}) ≤ LinearMap.ker (Λ : E →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro y ⟨j, hj, rfl⟩
    simpa using h0 j hj
  have hclosed : systemSpanOmit ℂ u i ≤ LinearMap.ker (Λ : E →ₗ[ℂ] ℂ) :=
    Submodule.topologicalClosure_minimal _ hle Λ.isClosed_ker
  have hzero : Λ (u i) = 0 := hclosed hi
  rw [h1] at hzero
  exact one_ne_zero hzero

/-- The data of a family of vectors of the even part of `L₁` realizing the functions
`ζ(s)/(s − ρ)^l` on the open critical strip, indexed injectively by the pairs `(ρ, l)`. -/
structure IsZetaQuotientSystem {ι : Type*} (u : ι → soninEvenExtended 1)
    (ρ : ι → ℂ) (l : ι → ℕ) : Prop where
  /-- Every index sits at a point of the open critical strip. -/
  re_pos : ∀ i, 0 < (ρ i).re
  /-- Every index sits at a point of the open critical strip. -/
  re_lt_one : ∀ i, (ρ i).re < 1
  /-- The exponents start at one. -/
  one_le : ∀ i, 1 ≤ l i
  /-- The exponent does not exceed the multiplicity of the zero. -/
  le_order : ∀ i, ((l i : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i)
  /-- Distinct indices carry distinct pairs. -/
  index_inj : ∀ i j, ρ i = ρ j → l i = l j → i = j
  /-- The continued Mellin transform of the `i`-th vector is `ζ(s)/(s − ρ_i)^{l_i}`. -/
  mellin : ∀ i, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    soninEval 1 ((u i : SoninL2)) s = zetaDivPowNF (ρ i) (l i) s

/-- **The quotient system is minimal.** -/
theorem IsZetaQuotientSystem.isMinimalSystem {ι : Type*} {u : ι → soninEvenExtended 1}
    {ρ : ι → ℂ} {l : ι → ℕ} (hu : IsZetaQuotientSystem u ρ l) :
    IsMinimalSystem ℂ u := by
  refine isMinimalSystem_of_exists_functional fun i => ?_
  obtain ⟨m, hmeq⟩ := ENat.ne_top_iff_exists.1
    (analyticOrderAt_riemannZeta_ne_top_of_strip (hu.re_pos i) (hu.re_lt_one i))
  have hm : analyticOrderAt riemannZeta (ρ i) = ((m : ℕ) : ℕ∞) := hmeq.symm
  have hlm : l i ≤ m := by
    have hle := hu.le_order i
    rw [hm] at hle
    exact_mod_cast hle
  obtain ⟨Λ, hΛ⟩ :=
    exists_zetaJetFunctional (hu.re_pos i) (hu.re_lt_one i) hm (hu.one_le i) hlm
  refine ⟨Λ, ?_, ?_⟩
  · rw [hΛ (u i) (ρ i) (l i) (hu.re_pos i) (hu.re_lt_one i) (hu.one_le i) (hu.le_order i)
      (hu.mellin i)]
    simp
  · intro j hj
    rw [hΛ (u j) (ρ j) (l j) (hu.re_pos j) (hu.re_lt_one j) (hu.one_le j) (hu.le_order j)
      (hu.mellin j)]
    have hne : ¬ (ρ j = ρ i ∧ l j = l i) := by
      rintro ⟨h1, h2⟩
      exact hj (hu.index_inj j i h1 h2)
    simp [hne]

/-- **The quotient system exists.**  Every admissible family of pairs `(ρ, l)` is realized by
vectors of the even part of `L₁`. -/
theorem exists_zetaQuotientSystem {ι : Type*} (ρ : ι → ℂ) (l : ι → ℕ)
    (hρ0 : ∀ i, 0 < (ρ i).re) (hρ1 : ∀ i, (ρ i).re < 1) (hl1 : ∀ i, 1 ≤ l i)
    (hlo : ∀ i, ((l i : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i))
    (hinj : ∀ i j, ρ i = ρ j → l i = l j → i = j) :
    ∃ u : ι → soninEvenExtended 1, IsZetaQuotientSystem u ρ l := by
  classical
  have key : ∀ i, ∃ v : soninEvenExtended 1, ∀ s : ℂ, 0 < s.re → s.re < 1 →
      soninEval 1 ((v : SoninL2)) s = zetaDivPowNF (ρ i) (l i) s := by
    intro i
    obtain ⟨v, c, d, hev, hmem, hc, hd, heq⟩ :=
      exists_extendedSonin_zetaDivPow (hρ0 i) (hρ1 i) (hl1 i) (hlo i)
    refine ⟨⟨v, Submodule.mem_inf.2 ⟨hmem, hev⟩⟩, fun s hs0 hs1 => ?_⟩
    have hcc : soninFourierBandConst 1 v = c := by
      rw [soninFourierBandConst]
      exact soninBandConst_eq one_pos hc
    have hdd : soninBandConst 1 v = d := soninBandConst_eq one_pos hd
    show soninEval 1 v s = _
    rw [soninEval, hcc, hdd]
    exact heq s hs0 hs1
  choose u hu using key
  refine ⟨u, ?_⟩
  exact
    { re_pos := hρ0
      re_lt_one := hρ1
      one_le := hl1
      le_order := hlo
      index_inj := hinj
      mellin := hu }

/-- **Theorem 3.3, minimality half.**  The functions `ζ(s)/(s − ρ)^l`, for `ρ` a nontrivial zero of
`ζ` and `1 ≤ l ≤ m_ρ`, are the continued Mellin transforms of vectors of the even part of `L₁`, and
that system of vectors is minimal. -/
theorem burnol_theorem_three_three_minimal {ι : Type*} (ρ : ι → ℂ) (l : ι → ℕ)
    (hρ0 : ∀ i, 0 < (ρ i).re) (hρ1 : ∀ i, (ρ i).re < 1) (hl1 : ∀ i, 1 ≤ l i)
    (hlo : ∀ i, ((l i : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ i))
    (hinj : ∀ i j, ρ i = ρ j → l i = l j → i = j) :
    ∃ u : ι → soninEvenExtended 1,
      (∀ i, ∀ s : ℂ, 0 < s.re → s.re < 1 →
        soninEval 1 ((u i : SoninL2)) s = zetaDivPowNF (ρ i) (l i) s) ∧
      IsMinimalSystem ℂ u := by
  obtain ⟨u, hu⟩ := exists_zetaQuotientSystem ρ l hρ0 hρ1 hl1 hlo hinj
  exact ⟨u, hu.mellin, hu.isMinimalSystem⟩

end

end RHTower
