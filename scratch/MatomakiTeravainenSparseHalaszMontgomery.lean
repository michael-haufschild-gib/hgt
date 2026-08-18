import GaloisForLFunctions.RHTower.Sieve.DirichletFiniteSetLargeValues
import GaloisForLFunctions.RHTower.Sieve.DyadicSecondEnvelopeClosed
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Halász--Montgomery for a dyadic Dirichlet block on an arbitrary finite subset of an ambient
separated ordinate sequence. -/
theorem halaszMontgomery_blockPoly_finset_explicit
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta U T : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1) :
    ∑ r ∈ S, ‖blockPoly N c 1 (lam r)‖ ^ 2 ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
          + (S.card : ℝ) *
            (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
        ‖blockCoeff N c 1‖ ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · let ext : ℕ → ℝ := finsetSeparatedExtension S hS lam delta
    have hextgap : ∀ i, ext i + delta ≤ ext (i + 1) :=
      finsetSeparatedExtension_gap S hS lam hdelta hgap
    have hextdiam : ∀ r ∈ Finset.range S.card, ∀ s ∈ Finset.range S.card,
        |ext s - ext r| ≤ T := by
      intro r hr s hs
      have hrlt : r < S.card := Finset.mem_range.1 hr
      have hslt : s < S.card := Finset.mem_range.1 hs
      have hrmem : S.orderEmbOfFin rfl ⟨r, hrlt⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have hsmem : S.orderEmbOfFin rfl ⟨s, hslt⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
      have hrband := hband _ hrmem
      have hsband := hband _ hsmem
      rw [show ext r = lam (S.orderEmbOfFin rfl ⟨r, hrlt⟩) by
          exact finsetSeparatedExtension_eq_of_lt S hS lam delta hrlt,
        show ext s = lam (S.orderEmbOfFin rfl ⟨s, hslt⟩) by
          exact finsetSeparatedExtension_eq_of_lt S hS lam delta hslt]
      rw [abs_le]
      constructor <;> linarith
    have hbase := halaszMontgomery_dyadic_explicit (K := S.card) hN (blockCoeff N c 1)
      hdelta hU hT hextgap hextdiam hnear hlamT
    rw [sum_finset_eq_sum_extension S hS lam delta
      (fun t => ‖blockPoly N c 1 t‖ ^ 2)]
    simpa only [inner_dyadicDirRow_blockCoeff] using hbase
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp
    positivity

/-- The `T₁` receiver: a pointwise bound for the first factor times the arbitrary-fibre
Halász--Montgomery mean square of the second factor. -/
theorem matomakiTeravainen_typeII_T1_sparse_energy
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta U T A D : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (hD : 0 ≤ D)
    (F₁ : ℕ → ℝ) (hF₁0 : ∀ r ∈ S, 0 ≤ F₁ r) (hF₁ : ∀ r ∈ S, F₁ r ≤ A)
    (hc : ∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D) :
    ∑ r ∈ S, F₁ r ^ 2 * ‖blockPoly N c 1 (lam r)‖ ^ 2 ≤
      A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
          (D ^ 2 / (N : ℝ))) := by
  have hpoint : ∀ r ∈ S,
      F₁ r ^ 2 * ‖blockPoly N c 1 (lam r)‖ ^ 2 ≤
        A ^ 2 * ‖blockPoly N c 1 (lam r)‖ ^ 2 := by
    intro r hr
    have hsquare : F₁ r ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (hF₁0 r hr) (hF₁ r hr) 2
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  calc
    ∑ r ∈ S, F₁ r ^ 2 * ‖blockPoly N c 1 (lam r)‖ ^ 2
        ≤ ∑ r ∈ S, A ^ 2 * ‖blockPoly N c 1 (lam r)‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = A ^ 2 * ∑ r ∈ S, ‖blockPoly N c 1 (lam r)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
          ‖blockCoeff N c 1‖ ^ 2) := by
      gcongr
      exact halaszMontgomery_blockPoly_finset_explicit N hN c hdelta hU hT hgap hband
        hnear hlamT
    _ ≤ A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
          (D ^ 2 / (N : ℝ))) := by
      gcongr
      exact norm_blockCoeff_one_sq_le hN c hD hc

end RHTower.Sieve
