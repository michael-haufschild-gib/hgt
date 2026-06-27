/-
# Generic sparse fibres for the relative Böttcher relation

The relative hRigid path uses sparse fibres
`fibrePoly a s z = ∑ i∈s, C (a i z) * X^i`, while the existing U0 squarefree-crossing lemma is
formulated for dense coefficients indexed by `Fin (d+1)`.  This file supplies the bridge: a sparse
fibre with support in `range (N+1)` is the dense degree-`N` polynomial whose missing coefficients are zero,
so the resultant/squarefree crossing theorem applies unchanged.
-/
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.U0.U0PhiCard

open Polynomial Filter Topology Set Metric
open U0PhiCard

namespace Bottcher

/-- Dense degree-`N` coefficient family associated to a sparse finite support `s`. -/
noncomputable def denseFibreCoeff (a : ℕ → ℂ → ℂ) (s : Finset ℕ) (N : ℕ) :
    Fin (N + 1) → ℂ → ℂ :=
  fun i z => if (i : ℕ) ∈ s then a i z else 0

/-- The top dense coefficient is the sparse top coefficient when `N ∈ s`. -/
theorem denseFibreCoeff_last {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} (hN : N ∈ s) (z : ℂ) :
    denseFibreCoeff a s N (Fin.last N) z = a N z := by
  simp [denseFibreCoeff, hN]

/-- A sparse fibre equals its dense degree-`N` presentation with zero-filled missing coefficients. -/
theorem fibrePoly_eq_denseFibreCoeff {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} (hsupp : s ⊆ Finset.range (N + 1))
    (z : ℂ) :
    fibrePoly a s z =
      ∑ i : Fin (N + 1), Polynomial.C (denseFibreCoeff a s N i z) * Polynomial.X ^ (i : ℕ) := by
  ext j
  rw [coeff_fibrePoly, Polynomial.finsetSum_coeff]
  by_cases hjs : j ∈ s
  · have hjlt : j < N + 1 := by
      exact Finset.mem_range.mp (hsupp hjs)
    have hmem : (⟨j, hjlt⟩ : Fin (N + 1)) ∈ (Finset.univ : Finset (Fin (N + 1))) := Finset.mem_univ _
    rw [if_pos hjs]
    rw [Finset.sum_eq_single (⟨j, hjlt⟩ : Fin (N + 1))]
    · simp [denseFibreCoeff, hjs]
    · intro i _hi hij
      have hne : (i : ℕ) ≠ j := by
        intro h
        exact hij (Fin.ext h)
      have hpow : ((Polynomial.X ^ (i : ℕ) : Polynomial ℂ).coeff j) = 0 := by
        rw [Polynomial.coeff_X_pow]
        exact if_neg (by simpa [eq_comm] using hne)
      rw [Polynomial.coeff_C_mul, hpow, mul_zero]
    · intro hnot
      exact (hnot hmem).elim
  · rw [if_neg hjs]
    symm
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hi : (i : ℕ) = j
    · have his : (i : ℕ) ∉ s := by simpa [hi] using hjs
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos hi.symm, mul_one]
      simp [denseFibreCoeff, his]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by simpa [eq_comm] using hi), mul_zero]

/-- Analyticity of the zero-filled dense coefficient family follows from analyticity of the sparse
coefficients on `s`. -/
theorem analyticOnNhd_denseFibreCoeff {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {Ω : Set ℂ}
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω) :
    ∀ i : Fin (N + 1), AnalyticOnNhd ℂ (denseFibreCoeff a s N i) Ω := by
  intro i z hz
  by_cases hi : (i : ℕ) ∈ s
  · have hfun : denseFibreCoeff a s N i = a i := by
      funext z
      simp [denseFibreCoeff, hi]
    rw [hfun]
    exact ha i hi z hz
  · have hfun : denseFibreCoeff a s N i = fun _ => (0 : ℂ) := by
      funext z
      simp [denseFibreCoeff, hi]
    rw [hfun]
    exact analyticAt_const

/-- **Sparse generic crossing.** If a sparse analytic fibre has support inside `range (N+1)`, contains the
top index `N`, and has one full-degree separable specialization somewhere on a preconnected analytic
region `Ω`, then every accumulating target set `S` in `Ω` contains a point where the sparse fibre is again
full-degree and separable.

This is the exact resultant/discriminant crossing lemma needed by the relative hRigid path, stated in the
native sparse `fibrePoly` language. -/
theorem exists_sparse_fibre_separable_crossing {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S) :
    ∃ z₀ ∈ S, a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable := by
  classical
  set b : Fin (N + 1) → ℂ → ℂ := denseFibreCoeff a s N with hb
  have hb_an : ∀ i, AnalyticOnNhd ℂ (b i) Ω := by
    intro i
    rw [hb]
    exact analyticOnNhd_denseFibreCoeff ha i
  have hleadw_b : b (Fin.last N) w ≠ 0 := by
    rw [hb, denseFibreCoeff_last hN]
    exact hleadw
  have hsepw_b :
      (∑ i : Fin (N + 1), Polynomial.C (b i w) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ).Separable := by
    rw [hb, ← fibrePoly_eq_denseFibreCoeff hsupp w]
    exact hsepw
  obtain ⟨z₀, hz₀S, hlead₀_b, hsep₀_b⟩ :=
    exists_separable_crossing hN1 hΩc b hb_an hw hleadw_b hsepw_b hz₁ haccum
  have hlead₀ : a N z₀ ≠ 0 := by
    rw [hb, denseFibreCoeff_last hN] at hlead₀_b
    exact hlead₀_b
  have hsep₀ : (fibrePoly a s z₀).Separable := by
    rw [hb, ← fibrePoly_eq_denseFibreCoeff hsupp z₀] at hsep₀_b
    exact hsep₀_b
  exact ⟨z₀, hz₀S, hlead₀, hsep₀⟩

/-- **Common-basin hRigid input from sparse generic crossing.** This is the payload form consumed by the
strongest natural-boundary common-basin endpoint: the fibre nondegeneracy is created by
`exists_sparse_fibre_separable_crossing`, while the remaining target-set geometry is supplied pointwise on
`S`.

The conclusion is exactly the per-relation tuple expected by
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable`, abstracted away from the
specific coefficient family `(Qᵢ)(z, γ z)`. -/
theorem exists_commonBasin_input_of_sparse_fibre_crossing {U : Set ℂ} {a : ℕ → ℂ → ℂ}
    {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hgeom : ∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
      V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    ∃ (N' : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
      s ⊆ Finset.range (N' + 1) ∧ N' ∈ s ∧ 1 ≤ N' ∧
      a N' z₀ ≠ 0 ∧
      (fibrePoly a s z₀).Separable ∧
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
      V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  obtain ⟨z₀, hz₀S, hlead₀, hsep₀⟩ :=
    exists_sparse_fibre_separable_crossing hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum
  obtain ⟨r, V, hz₀K₁, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
    hgeom z₀ hz₀S
  exact ⟨N, z₀, r, V, hsupp, hN, hN1, hlead₀, hsep₀, hz₀K₁, hz₀off₂, hr, hVo, hVc,
    hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩

/-- **Common-basin hRigid input from sparse generic crossing, frontier form.** This is the same
constructor as `exists_commonBasin_input_of_sparse_fibre_crossing`, but preserves the stronger target
geometry `z₀ ∈ frontier (filledJulia c₁)`.  It is the form consumed by the E-vS/natural-boundary route:
the resultant crossing still creates the nondegenerate target fibre, while the geometric callback supplies
the frontier and common-basin sector data for every target point. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_crossing {U : Set ℂ} {a : ℕ → ℂ → ℂ}
    {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hgeom : ∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
      V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    ∃ (N' : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
      s ⊆ Finset.range (N' + 1) ∧ N' ∈ s ∧ 1 ≤ N' ∧
      a N' z₀ ≠ 0 ∧
      (fibrePoly a s z₀).Separable ∧
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
      V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  obtain ⟨z₀, hz₀S, hlead₀, hsep₀⟩ :=
    exists_sparse_fibre_separable_crossing hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum
  obtain ⟨r, V, hz₀front, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
    hgeom z₀ hz₀S
  exact ⟨N, z₀, r, V, hsupp, hN, hN1, hlead₀, hsep₀, hz₀front, hz₀off₂, hr, hVo, hVc,
    hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩

end Bottcher
