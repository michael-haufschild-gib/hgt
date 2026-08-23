import GaloisForLFunctions.RHTower.BurnolQuotientContour
import GaloisForLFunctions.HTGeometry.CauchyKernelResidue

/-!
# The shape of the residue at a zero

Burnol's parenthetical remark in Theorem 5.2 — *"the exact expression is a linear combination of
`ζ(Z)/(Z − ρ)^l`, `1 ≤ l ≤ m_ρ`"* — made precise: the residue of

`G(s)·ζ(Z)/(ζ(s)(Z − s))`

at `ρ` is `ζ(Z)` times the principal part of `G/ζ` at `ρ`, evaluated at `Z`.  Since the principal
part is `Σ_{l=1}^{k} c_{-l}·(Z − ρ)^{-l}` with `c_{-l}` the Laurent coefficients of `G/ζ` at `ρ`,
this is exactly the asserted linear combination, and the number of terms is the pole order of `G/ζ`
at `ρ` — at most the multiplicity of `ρ` as a zero of `ζ`.

## Main results

* `laurentCoeff_burnolIntegrand_eq_zeta_mul_principalPart`
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem burnolIntegrand_eq_zeta_mul_quotient (G : ℂ → ℂ) (Z : ℂ) (s : ℂ) :
    burnolIntegrand G Z s = riemannZeta Z * (burnolQuotient G s * (Z - s)⁻¹) := by
  rw [burnolIntegrand, burnolQuotient, div_mul_eq_div_div, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- **The residue at `ρ` is `ζ(Z)` times the principal part of `G/ζ` at `ρ`.** -/
theorem laurentCoeff_burnolIntegrand_eq_zeta_mul_principalPart {G : ℂ → ℂ} {Z ρ : ℂ}
    (hZρ : Z ≠ ρ) {k : ℕ} (hk : AnalyticAt ℂ (laurentShift (burnolQuotient G) ρ k) 0) :
    laurentCoeff (burnolIntegrand G Z) ρ (-1)
      = riemannZeta Z * principalPart (burnolQuotient G) ρ k Z := by
  classical
  have hmero : MeromorphicAt (fun s : ℂ => burnolQuotient G s * (Z - s)⁻¹) ρ := by
    have h1 : MeromorphicAt (burnolQuotient G) ρ :=
      (meromorphicAt_iff_exists_analyticAt_laurentShift (burnolQuotient G) ρ).2 ⟨k, hk⟩
    have h2 : AnalyticAt ℂ (fun s : ℂ => (Z - s)⁻¹) ρ := by
      refine AnalyticAt.inv ?_ (sub_ne_zero.2 hZρ)
      fun_prop
    exact h1.mul h2.meromorphicAt
  have hsingle := laurentCoeff_sum (Finset.univ : Finset (Fin 1))
    (fun _ => fun s : ℂ => burnolQuotient G s * (Z - s)⁻¹)
    (fun _ => riemannZeta Z) ρ (-1) (fun i _ => hmero)
  have hfun : (fun s : ℂ => ∑ _i : Fin 1, riemannZeta Z * (burnolQuotient G s * (Z - s)⁻¹))
      = burnolIntegrand G Z := by
    funext s
    rw [Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin, one_smul]
    exact (burnolIntegrand_eq_zeta_mul_quotient G Z s).symm
  rw [hfun] at hsingle
  rw [hsingle, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fin, one_smul]
  rw [laurentCoeff_mul_inv_sub hZρ hk]

end

end RHTower
