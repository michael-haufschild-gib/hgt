import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# From a product law to two-sided bounds on each factor

Section 7 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), deduces the two-sided estimate

```text
C₀ / log|s|⁻¹ ≤ λ₁(s) ≤ … ≤ λ_{N−1}(s) ≤ C₁ / log|s|⁻¹
```

of Theorem 0.2 from the product law `∏_{k<N} λ_k(s) = (c+o(1)) (log|s|⁻¹)^{−(N−1)}` of Theorem 0.3
together with the individual upper bounds `λ_k(s) ≤ K(k)/log|s|⁻¹` of Proposition 6.1.

The paper runs a descending induction on `k`.  It is not needed: dividing the product law by the
upper bounds for the other factors bounds each single factor from below in one step,

```text
λ_j ≥ (∏ λ_i) / ∏_{i ≠ j} λ_i ≥ (c L^{−n}) / (∏_{i≠j} K_i · L^{−(n−1)}) = c / (L ∏_{i≠j} K_i),
```

and the constant produced is explicit.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **The product law forces every factor to be large.**

If `n+1` positive numbers have product at least `c L^{−(n+1)}` and each is at most `K i / L`, then
each single one is at least `c / (L ∏_{i ≠ j} K i)`. -/
theorem le_of_prod_le_of_le_div
    {m : ℕ} {lam K : Fin (m + 1) → ℝ} {c L : ℝ}
    (hL : 0 < L) (hlam : ∀ i, 0 < lam i) (hK : ∀ i, 0 < K i)
    (hprod : c / L ^ (m + 1) ≤ ∏ i, lam i)
    (hupper : ∀ i, lam i ≤ K i / L)
    (j : Fin (m + 1)) :
    c / ((∏ i ∈ Finset.univ.erase j, K i) * L) ≤ lam j := by
  have hKprod : 0 < ∏ i ∈ Finset.univ.erase j, K i :=
    Finset.prod_pos fun i _ => hK i
  have hcard : (Finset.univ.erase j).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega
  have hrest : (∏ i ∈ Finset.univ.erase j, lam i)
      ≤ (∏ i ∈ Finset.univ.erase j, K i) / L ^ m := by
    have hstep : (∏ i ∈ Finset.univ.erase j, lam i)
        ≤ ∏ i ∈ Finset.univ.erase j, (K i / L) :=
      Finset.prod_le_prod (fun i _ => (hlam i).le) (fun i _ => hupper i)
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard]
  have hj : (∏ i, lam i) = lam j * ∏ i ∈ Finset.univ.erase j, lam i :=
    (Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ j)).symm
  have h1 : c / L ^ (m + 1)
      ≤ lam j * ((∏ i ∈ Finset.univ.erase j, K i) / L ^ m) := by
    calc c / L ^ (m + 1) ≤ ∏ i, lam i := hprod
      _ = lam j * ∏ i ∈ Finset.univ.erase j, lam i := hj
      _ ≤ lam j * ((∏ i ∈ Finset.univ.erase j, K i) / L ^ m) :=
          mul_le_mul_of_nonneg_left hrest (hlam j).le
  rw [div_le_iff₀ (by positivity)]
  have hpow : (0 : ℝ) < L ^ (m + 1) := pow_pos hL _
  have h2 := mul_le_mul_of_nonneg_right h1 hpow.le
  rw [div_mul_cancel₀ _ (ne_of_gt hpow)] at h2
  have h3 : lam j * ((∏ i ∈ Finset.univ.erase j, K i) / L ^ m) * L ^ (m + 1)
      = lam j * ((∏ i ∈ Finset.univ.erase j, K i) * L) := by
    field_simp
    ring
  rw [h3] at h2
  exact h2

/-- **Section 7 of Dai–Yoshikawa, filter form.**

If the product `∏_i λ_i(x) · L(x)^{n+1}` converges to a positive constant `c` and each factor obeys
`λ_i(x) ≤ K i / L(x)`, then eventually each factor obeys the matching lower bound
`λ_j(x) ≥ (c/2) / (L(x) ∏_{i≠j} K i)`. -/
theorem eventually_le_of_tendsto_prod_mul_pow
    {m : ℕ} {α : Type*} {l : Filter α} {lam : Fin (m + 1) → α → ℝ} {K : Fin (m + 1) → ℝ}
    {Lf : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hlam : ∀ i, ∀ᶠ x in l, 0 < lam i x) (hK : ∀ i, 0 < K i)
    (hLf : ∀ᶠ x in l, 0 < Lf x)
    (hprod : Tendsto (fun x => (∏ i, lam i x) * Lf x ^ (m + 1)) l (𝓝 c))
    (hupper : ∀ i, ∀ᶠ x in l, lam i x ≤ K i / Lf x)
    (j : Fin (m + 1)) :
    ∀ᶠ x in l, c / 2 / ((∏ i ∈ Finset.univ.erase j, K i) * Lf x) ≤ lam j x := by
  have hhalf : ∀ᶠ x in l, c / 2 < (∏ i, lam i x) * Lf x ^ (m + 1) :=
    hprod.eventually (lt_mem_nhds (by linarith))
  have hlamAll : ∀ᶠ x in l, ∀ i, 0 < lam i x := by
    rw [eventually_all]
    exact hlam
  have hupperAll : ∀ᶠ x in l, ∀ i, lam i x ≤ K i / Lf x := by
    rw [eventually_all]
    exact hupper
  filter_upwards [hhalf, hlamAll, hupperAll, hLf] with x hx hpos hup hLx
  refine le_of_prod_le_of_le_div hLx hpos hK ?_ hup j
  rw [div_le_iff₀ (pow_pos hLx _)]
  exact hx.le

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
