/-
# Generic sparse fibres for the relative Böttcher relation

The relative hRigid path uses sparse fibres
`fibrePoly a s z = ∑ i∈s, C (a i z) * X^i`, while the existing U0 squarefree-crossing lemma is
formulated for dense coefficients indexed by `Fin (d+1)`.  This file supplies the bridge: a sparse
fibre with support in `range (N+1)` is the dense degree-`N` polynomial whose missing coefficients are zero,
so the resultant/squarefree crossing theorem applies unchanged.
-/
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.ZeroSet
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

/-- **Sparse generic crossing from countable avoidance.** This is the no-arc variant of
`exists_sparse_fibre_separable_crossing`: instead of requiring an accumulating target set, it is enough
that the target mechanism can avoid every countable bad set.  The bad locus is the zero set of the
analytic product "top coefficient times resultant", hence countable on the preconnected analytic
region. -/
theorem exists_sparse_fibre_separable_countableAvoidance {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) :
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
  set g : ℂ → ℂ := fun z =>
    b (Fin.last N) z *
      resultant (∑ i : Fin (N + 1), Polynomial.C (b i z) * Polynomial.X ^ (i : ℕ))
        (derivative (∑ i : Fin (N + 1), Polynomial.C (b i z) * Polynomial.X ^ (i : ℕ)))
        N (N - 1) with hg
  have hgan : AnalyticOnNhd ℂ g Ω := fun z hz => by
    rw [hg]
    exact (hb_an (Fin.last N) z hz).mul
      (resultant_specialize_analytic b z (fun i => hb_an i z hz))
  have hgw : g w ≠ 0 := by
    rw [hg]
    exact mul_ne_zero hleadw_b ((separable_iff_resultant_fixed hN1 b w hleadw_b).mp hsepw_b)
  have hbad : {z ∈ Ω | g z = 0}.Countable :=
    analyticOnNhd_zeros_countable hgan hΩc hw hgw
  obtain ⟨z₀, hz₀S, hz₀Ω, hz₀bad⟩ := havoid {z ∈ Ω | g z = 0} hbad
  have hgz₀ : g z₀ ≠ 0 := fun hz => hz₀bad ⟨hz₀Ω, hz⟩
  have hgz₀' :
      b (Fin.last N) z₀ *
        resultant (∑ i : Fin (N + 1), Polynomial.C (b i z₀) * Polynomial.X ^ (i : ℕ))
          (derivative (∑ i : Fin (N + 1), Polynomial.C (b i z₀) * Polynomial.X ^ (i : ℕ)))
          N (N - 1) ≠ 0 := by
    simpa [g] using hgz₀
  obtain ⟨hlead₀_b, hres₀_b⟩ := mul_ne_zero_iff.mp hgz₀'
  have hlead₀ : a N z₀ ≠ 0 := by
    rw [hb, denseFibreCoeff_last hN] at hlead₀_b
    exact hlead₀_b
  have hsep₀_b :
      (∑ i : Fin (N + 1), Polynomial.C (b i z₀) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ).Separable :=
    (separable_iff_resultant_fixed hN1 b z₀ hlead₀_b).mpr hres₀_b
  have hsep₀ : (fibrePoly a s z₀).Separable := by
    rw [hb, ← fibrePoly_eq_denseFibreCoeff hsupp z₀] at hsep₀_b
    exact hsep₀_b
  exact ⟨z₀, hz₀S, hlead₀, hsep₀⟩

/-- An uncountable target set inside `Ω` can avoid every countable exceptional set. -/
theorem countableAvoidance_of_uncountable_inter {S Ω : Set ℂ}
    (hunc : ¬ (S ∩ Ω).Countable) :
    ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T := by
  intro T hT
  by_contra hnone
  push Not at hnone
  have hsub : S ∩ Ω ⊆ T := by
    intro z hz
    exact hnone z hz.1 hz.2
  exact hunc (hT.mono hsub)

/-- **Sparse generic crossing from an uncountable target set.** This is the geometric form of
`exists_sparse_fibre_separable_countableAvoidance`: an uncountable supply of candidate targets inside
the analytic region can avoid the countable analytic bad locus. -/
theorem exists_sparse_fibre_separable_uncountable {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ} (hunc : ¬ (S ∩ Ω).Countable) :
    ∃ z₀ ∈ S, a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable :=
  exists_sparse_fibre_separable_countableAvoidance
    hN1 hsupp hN hΩc ha hw hleadw hsepw
    (countableAvoidance_of_uncountable_inter hunc)

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

/-- **Common-basin hRigid input from countable-avoidance sparse crossing.** This is the frontier form of
`exists_commonBasin_frontier_input_of_sparse_fibre_crossing` with the target-set hypothesis changed from
accumulation to countable avoidance.  It is designed for dynamical inputs of the form "for every
countable exceptional set, choose a frontier/common-basin target outside it". -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance {U : Set ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T)
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
    exists_sparse_fibre_separable_countableAvoidance hN1 hsupp hN hΩc ha hw hleadw hsepw havoid
  obtain ⟨r, V, hz₀front, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
    hgeom z₀ hz₀S
  exact ⟨N, z₀, r, V, hsupp, hN, hN1, hlead₀, hsep₀, hz₀front, hz₀off₂, hr, hVo, hVc,
    hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩

/-- **Common-basin hRigid input from an uncountable target set.** This is the geometric form of
`exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance`: an uncountable set of
frontier/common-basin targets inside the analytic region can avoid the countable sparse-fibre bad
locus. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_uncountable {U : Set ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ} (hunc : ¬ (S ∩ Ω).Countable)
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
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :=
  exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance
    hN1 hsupp hN hΩc ha hw hleadw hsepw
    (countableAvoidance_of_uncountable_inter hunc) hgeom

/-- **Empty-interior common-basin crossing, frontier form.** In the dendrite/empty-interior route,
target geometry only has to place the accumulating sparse-crossing set in `filledJulia c₁`: empty interior
promotes each such point to the Julia frontier internally.  This removes the caller's separate frontier
payload without weakening the natural-boundary endpoint. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior {U : Set ℂ}
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
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
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
      V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing
    hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum (by
      intro z₀ hz₀S
      obtain ⟨r, V, hz₀K₁, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV,
        htip⟩ := hgeom z₀ hz₀S
      have hz₀front : z₀ ∈ frontier (filledJulia c₁) := by
        rw [(isClosed_filledJulia c₁).frontier_eq]
        exact ⟨hz₀K₁, by simp [hempty]⟩
      exact ⟨r, V, hz₀front, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV,
        htip⟩)

/-- **Empty-interior common-basin crossing from one global common-basin region.** This is the same
frontier creator as `exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior`, but the
open/preconnected common-basin region `V` is supplied once.  The pointwise target geometry only has to give
membership of each target point, a local basin sector landing in `V`, and the punctured-sector
preconnectedness. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S V : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hUV : U ⊆ V) (hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ) (hVbasin₂ : V ⊆ (filledJulia c₂)ᶜ)
    (hgeom : ∀ z₀ ∈ S, ∃ r : ℝ,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    ∃ (N' : ℕ) (z₀ : ℂ) (r : ℝ) (V' : Set ℂ),
      s ⊆ Finset.range (N' + 1) ∧ N' ∈ s ∧ 1 ≤ N' ∧
      a N' z₀ ≠ 0 ∧
      (fibrePoly a s z₀).Separable ∧
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V' ∧ IsPreconnected V' ∧ U ⊆ V' ∧ V' ⊆ (filledJulia c₁)ᶜ ∧
      V' ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V' ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
    hempty hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum (by
      intro z₀ hz₀S
      obtain ⟨r, hz₀K₁, hz₀off₂, hr, hsectorV, htip⟩ := hgeom z₀ hz₀S
      exact ⟨r, V, hz₀K₁, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV,
        htip⟩)

/-- **Empty-interior common-basin crossing from the common-basin component containing `U`.** This
constructs the global open preconnected region `V` internally as the connected component of
`(filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ` containing the carrier `U`.

The caller no longer supplies `V` or the sector inclusion into it.  Instead, for each target point it
supplies filled/off-other membership, local punctured-sector preconnectedness, and the fact that the
target is in the closure of this common-basin component.  Openness of `(filledJulia c₂)ᶜ` gives a small
ball on the `c₂` basin side; preconnectedness plus closure contact then forces the whole `c₁` basin
sector into the common component. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (_hUo : IsOpen U) (hUc : IsPreconnected U) (_hUne : U.Nonempty)
    (hUbasin₁ : U ⊆ (filledJulia c₁)ᶜ) (hUbasin₂ : U ⊆ (filledJulia c₂)ᶜ)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S,
        z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
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
  obtain ⟨u, huU, hcl⟩ := hcomponent
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVo : IsOpen V := by
    simpa [V] using hCo.connectedComponentIn
  have hVc : IsPreconnected V := by
    simpa [V] using (isPreconnected_connectedComponentIn (x := u) (F := C))
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  have hVbasin₂ : V ⊆ (filledJulia c₂)ᶜ := fun z hz => (hVsubC hz).2
  have hUV : U ⊆ V := by
    have hUC : U ⊆ C := fun z hz => ⟨hUbasin₁ hz, hUbasin₂ hz⟩
    simpa [V] using hUc.subset_connectedComponentIn huU hUC
  exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) (V := V)
    hempty hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum
    hVo hVc hUV hVbasin₁ hVbasin₂ (by
      intro z₀ hz₀S
      obtain ⟨hz₀K₁, hz₀off₂, htip⟩ := hgeom z₀ hz₀S
      obtain ⟨r, hr, hball₂⟩ :=
        Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl z₀ hz₀off₂
      refine ⟨r, hz₀K₁, hz₀off₂, hr, ?_, htip⟩
      set W : Set ℂ := Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ with hW
      have hWc : IsPreconnected W := by
        simpa [W] using htip r hr
      have hWC : W ⊆ C := by
        intro z hz
        exact ⟨hz.2, hball₂ hz.1⟩
      have hz₀clV : z₀ ∈ closure V := by
        simpa [V, C] using hcl z₀ hz₀S
      have hmeet : (Metric.ball z₀ r ∩ V).Nonempty := by
        rw [_root_.mem_closure_iff] at hz₀clV
        exact hz₀clV (Metric.ball z₀ r) isOpen_ball (Metric.mem_ball_self hr)
      obtain ⟨y, hyball, hyV⟩ := hmeet
      have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
      have hWsubCompY : W ⊆ connectedComponentIn C y :=
        hWc.subset_connectedComponentIn hyW hWC
      have hcomp : connectedComponentIn C y = V := by
        have h := connectedComponentIn_eq (by simpa [V] using hyV)
        simpa [V] using h.symm
      intro z hz
      exact hcomp ▸ hWsubCompY (by simpa [W] using hz))

/-- **Empty-interior common-basin crossing from carrier-closure contact.** This is a creator for the
component-closure payload in
`exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent`: if all target
points lie in `closure U`, and `U` is preconnected inside the common basin
`(filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ`, then all target points automatically lie in the closure of the
common-basin component containing any point of `U`.

The caller no longer has to mention `connectedComponentIn` in this layer. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUbasin₁ : U ⊆ (filledJulia c₁)ᶜ) (hUbasin₂ : U ⊆ (filledJulia c₂)ᶜ)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hSclosure : ∀ z₀ ∈ S, z₀ ∈ closure U)
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
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
  obtain ⟨u, huU⟩ := hUne
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  have hUC : U ⊆ C := fun z hz => ⟨hUbasin₁ hz, hUbasin₂ hz⟩
  have hUcomponent : U ⊆ connectedComponentIn C u :=
    hUc.subset_connectedComponentIn huU hUC
  exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
    hempty hUo hUc ⟨u, huU⟩ hUbasin₁ hUbasin₂ hN1 hsupp hN hΩc ha hw hleadw hsepw
    hz₁ haccum
    (by
      refine ⟨u, huU, ?_⟩
      intro z₀ hz₀S
      exact closure_mono hUcomponent (hSclosure z₀ hz₀S))
    hgeom

/-- **Countable-avoidance empty-interior common-basin crossing from one global common-basin region.**
This is the countable-avoidance analogue of
`exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion`: the sparse
fibre point is chosen by avoiding an arbitrary countable bad set, while the common-basin region `V` is
supplied once. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_globalRegion
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S V : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hUV : U ⊆ V) (hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ) (hVbasin₂ : V ⊆ (filledJulia c₂)ᶜ)
    (hgeom : ∀ z₀ ∈ S, ∃ r : ℝ,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    ∃ (N' : ℕ) (z₀ : ℂ) (r : ℝ) (V' : Set ℂ),
      s ⊆ Finset.range (N' + 1) ∧ N' ∈ s ∧ 1 ≤ N' ∧
      a N' z₀ ≠ 0 ∧
      (fibrePoly a s z₀).Separable ∧
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ IsOpen V' ∧ IsPreconnected V' ∧ U ⊆ V' ∧ V' ⊆ (filledJulia c₁)ᶜ ∧
      V' ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V' ∧
      (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
    hN1 hsupp hN hΩc ha hw hleadw hsepw havoid (by
      intro z₀ hz₀S
      obtain ⟨r, hz₀K₁, hz₀off₂, hr, hsectorV, htip⟩ := hgeom z₀ hz₀S
      have hz₀front : z₀ ∈ frontier (filledJulia c₁) := by
        rw [(isClosed_filledJulia c₁).frontier_eq]
        exact ⟨hz₀K₁, by simp [hempty]⟩
      exact ⟨r, V, hz₀front, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂,
        hsectorV, htip⟩)

/-- **Countable-avoidance empty-interior common-basin crossing from the component containing `U`.**
This is the countable-avoidance analogue of
`exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent`.  The global
common-basin region is constructed internally as the connected component of
`(filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ` containing `U`. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (_hUo : IsOpen U) (hUc : IsPreconnected U) (_hUne : U.Nonempty)
    (hUbasin₁ : U ⊆ (filledJulia c₁)ᶜ) (hUbasin₂ : U ⊆ (filledJulia c₂)ᶜ)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S,
        z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
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
  obtain ⟨u, huU, hcl⟩ := hcomponent
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVo : IsOpen V := by
    simpa [V] using hCo.connectedComponentIn
  have hVc : IsPreconnected V := by
    simpa [V] using (isPreconnected_connectedComponentIn (x := u) (F := C))
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  have hVbasin₂ : V ⊆ (filledJulia c₂)ᶜ := fun z hz => (hVsubC hz).2
  have hUV : U ⊆ V := by
    have hUC : U ⊆ C := fun z hz => ⟨hUbasin₁ hz, hUbasin₂ hz⟩
    simpa [V] using hUc.subset_connectedComponentIn huU hUC
  exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_globalRegion
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) (V := V)
    hempty hN1 hsupp hN hΩc ha hw hleadw hsepw havoid
    hVo hVc hUV hVbasin₁ hVbasin₂ (by
      intro z₀ hz₀S
      obtain ⟨hz₀K₁, hz₀off₂, htip⟩ := hgeom z₀ hz₀S
      obtain ⟨r, hr, hball₂⟩ :=
        Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl z₀ hz₀off₂
      refine ⟨r, hz₀K₁, hz₀off₂, hr, ?_, htip⟩
      set W : Set ℂ := Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ with hW
      have hWc : IsPreconnected W := by
        simpa [W] using htip r hr
      have hWC : W ⊆ C := by
        intro z hz
        exact ⟨hz.2, hball₂ hz.1⟩
      have hz₀clV : z₀ ∈ closure V := by
        simpa [V, C] using hcl z₀ hz₀S
      have hmeet : (Metric.ball z₀ r ∩ V).Nonempty := by
        rw [_root_.mem_closure_iff] at hz₀clV
        exact hz₀clV (Metric.ball z₀ r) isOpen_ball (Metric.mem_ball_self hr)
      obtain ⟨y, hyball, hyV⟩ := hmeet
      have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
      have hWsubCompY : W ⊆ connectedComponentIn C y :=
        hWc.subset_connectedComponentIn hyW hWC
      have hcomp : connectedComponentIn C y = V := by
        have h := connectedComponentIn_eq (by simpa [V] using hyV)
        simpa [V] using h.symm
      intro z hz
      exact hcomp ▸ hWsubCompY (by simpa [W] using hz))

/-- **Countable-avoidance empty-interior common-basin crossing from carrier-closure contact.** This is
the countable-avoidance analogue of
`exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure`; it removes the
explicit connected-component closure payload from the countable-avoidance route. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_carrierClosure
    {U : Set ℂ} {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUbasin₁ : U ⊆ (filledJulia c₁)ᶜ) (hUbasin₂ : U ⊆ (filledJulia c₂)ᶜ)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T)
    (hSclosure : ∀ z₀ ∈ S, z₀ ∈ closure U)
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
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
  obtain ⟨u, huU⟩ := hUne
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  have hUC : U ⊆ C := fun z hz => ⟨hUbasin₁ hz, hUbasin₂ hz⟩
  have hUcomponent : U ⊆ connectedComponentIn C u :=
    hUc.subset_connectedComponentIn huU hUC
  exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
    hempty hUo hUc ⟨u, huU⟩ hUbasin₁ hUbasin₂ hN1 hsupp hN hΩc ha hw hleadw hsepw
    havoid
    (by
      refine ⟨u, huU, ?_⟩
      intro z₀ hz₀S
      exact closure_mono hUcomponent (hSclosure z₀ hz₀S))
    hgeom

end Bottcher
