/-
# Hurwitz N=2 — the assembled separation step (blocks vanish) and the conditional final theorem

Ties the committed components: the blocks `Φb / Ψb / Θb` (matching the eigenvector lemmas of
`Encoding`), the analytic continuation `split_extend`, and the eigenspace separation `n2_separation`.
The output `n2_blocks_vanish` (each block vanishes on the deep half-plane) feeds `quad_descent`,
`lin_descent` (`N2Descent`) and `survivor_q_eq_zero` (`N2Survivor`).

Two inputs are taken as hypotheses (the remaining analytic/arithmetic gaps):
* `hanalytic` — the block sum is analytic on the half-plane (proved separately for the Hurwitz tail in
  `N2TailAnalytic`);
* `hrel_split` — on the strip the genuine relation equals the block sum (the `Fk_zform → relation_collect
  → phi_block_form` substitution).
-/
import GaloisForLFunctions.Hurwitz.Encoding
import GaloisForLFunctions.Hurwitz.N2Descent
import GaloisForLFunctions.Hurwitz.N2Survivor

open Complex HurwitzEncoding HurwitzSpine

namespace HurwitzN2Main

/-- The quadratic (doubly-singular) block `∑_{w<5} A_w(−n+e^z)·e^{−(2s+w)z}`, `A_w = ∑_{i+j=w} q_{ij}`. -/
noncomputable def PhiB (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ w ∈ Finset.range 5, (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z)
    * Complex.exp (-(2 * s + (w : ℂ)) * z)

/-- The linear+cross block. -/
noncomputable def PsiB (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (R : Fin 3 → ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z)
      * (Complex.exp (-(s + (i : ℂ)) * z) * R j z + Complex.exp (-(s + (j : ℂ)) * z) * R i z))
    + ∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) * Complex.exp (-(s + (k : ℂ)) * z)

/-- The regular block. -/
noncomputable def ThetaB (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ)
    (cc : Polynomial ℂ) (R : Fin 3 → ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z) * (R i z * R j z))
    + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z) * R k z)
    + cc.eval (-(n : ℂ) + Complex.exp z)

/-- **Separation step (assembled).** Given the block sum is analytic on the half-plane `{Re z < B}` and
vanishes on the open strip-slice (where it equals the genuine relation), each of the three monodromy
blocks vanishes on the whole half-plane. Combines `split_extend` (strip → half-plane) with
`n2_separation` (eigenspace separation), the eigenvector inputs coming from `phi/psi/theta_block_eigen`
with periodicities from `coeff_periodic`/`hRper` and `2πi`-invariance from `halfplane_invariant`. -/
theorem n2_blocks_vanish (s : ℂ) (n : ℕ) (hs : ∀ k : ℤ, (k : ℂ) ≠ s) (h2s : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    (R : Fin 3 → ℂ → ℂ) (hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z)
    {B : ℝ} {z0 : ℂ} (h0re : z0.re < B) (h0im1 : -Real.pi < z0.im) (h0im2 : z0.im < Real.pi)
    (hanalytic : AnalyticOnNhd ℂ
      (fun z => PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z) {z : ℂ | z.re < B})
    (hrel_split : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
      PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z = 0) :
    (∀ z : ℂ, z.re < B → PhiB s n q z = 0) ∧ (∀ z : ℂ, z.re < B → PsiB s n q l R z = 0)
      ∧ (∀ z : ℂ, z.re < B → ThetaB s n q l cc R z = 0) := by
  have hg0 : ∀ z : ℂ, z.re < B → PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z = 0 :=
    fun z hz => split_extend hanalytic hrel_split h0re h0im1 h0im2 hz
  have hΦ : ∀ z ∈ {z : ℂ | z.re < B}, PhiB s n q (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-(2 * s))) * PhiB s n q z := fun z _ =>
    phi_block_eigen (s := s) (A := fun w z => (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z))
      (fun w z => coeff_periodic (HurwitzN2Descent.Aq q w) n z) z
  have hΨ : ∀ z ∈ {z : ℂ | z.re < B}, PsiB s n q l R (z + 2 * (Real.pi : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-s)) * PsiB s n q l R z := fun z _ =>
    psi_block_eigen (s := s) (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z) hRper z
  have hΘ : ∀ z ∈ {z : ℂ | z.re < B}, ThetaB s n q l cc R (z + 2 * (Real.pi : ℂ) * Complex.I)
      = ThetaB s n q l cc R z := fun z _ =>
    theta_block_eigen (q := fun i j z => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (l := fun k z => (l k).eval (-(n : ℂ) + Complex.exp z))
      (cc := fun z => cc.eval (-(n : ℂ) + Complex.exp z)) (R := R)
      (fun i j z => coeff_periodic (q i j) n z) (fun k z => coeff_periodic (l k) n z)
      (fun z => coeff_periodic cc n z) hRper z
  have hsep := n2_separation hs h2s
    (fun z (hz : z.re < B) => halfplane_invariant (B := B) (z := z) hz) hΦ hΨ hΘ
    (fun z hz => hg0 z hz)
  exact ⟨fun z hz => (hsep z hz).1, fun z hz => (hsep z hz).2.1, fun z hz => (hsep z hz).2.2⟩

/-- **Quadratic-coefficient extraction.** From the quadratic block vanishing (for all large `n`),
`quad_descent` zeroes every weight coefficient `A_w`, and `weight_filter_eval` reads off the triangular
system: `q₀₀ = 0`, `q₂₂ = 0`, and the survivor identity `q₀₂ + q₁₁ + q₂₀ = 0`. (The off-survivor
`q₀₁`, `q₁₂` come from `A_1 = A_3 = 0` the same way.) The lone surviving quadratic shape is then
`Q·(F₀F₂ − F₁²)`, killed by `N2Survivor.survivor_q_eq_zero`. -/
theorem n2_quad_coeffs (s : ℂ) (q : Fin 3 → Fin 3 → Polynomial ℂ) {N : ℕ} {Bregion : ℕ → ℝ}
    (hΦ0 : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n → PhiB s n q z = 0) :
    q 0 0 = 0 ∧ q 2 2 = 0 ∧ q 0 2 + q 1 1 + q 2 0 = 0 := by
  have hAq : ∀ w, w ≤ 4 → HurwitzN2Descent.Aq q w = 0 :=
    HurwitzN2Descent.quad_descent q (fun n hn z hz => hΦ0 n hn z hz)
  obtain ⟨h0, h4, h2⟩ := weight_filter_eval q
  refine ⟨?_, ?_, ?_⟩
  · rw [← h0]; exact hAq 0 (by norm_num)
  · rw [← h4]; exact hAq 4 (by norm_num)
  · rw [← h2]; exact hAq 2 (by norm_num)

/-- `PhiB` (the `block_descent` form `∑_w A_w·e^{−(2s+w)z}`, `A_w = ∑_{i+j=w} q_{ij}` a polynomial) equals
the product form `∑_{i,j} q_{ij}·E_iE_j` — `eval_finset_sum` distributes the polynomial filter-sum over
the evaluation, and `phi_block_form` regroups by weight. -/
theorem PhiB_eq_products (s : ℂ) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ) (z : ℂ) :
    PhiB s n q z = ∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z)
        * (Complex.exp (-(s + (i : ℂ)) * z) * Complex.exp (-(s + (j : ℂ)) * z)) := by
  rw [PhiB]
  have step1 : (∑ w ∈ Finset.range 5, (HurwitzN2Descent.Aq q w).eval (-(n : ℂ) + Complex.exp z)
        * Complex.exp (-(2 * s + (w : ℂ)) * z))
      = ∑ w ∈ Finset.range 5, (∑ ij ∈ Finset.univ.filter
          (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = w),
          (q ij.1 ij.2).eval (-(n : ℂ) + Complex.exp z)) * Complex.exp (-(2 * s + (w : ℂ)) * z) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [HurwitzN2Descent.Aq, Polynomial.eval_finsetSum]
  rw [step1]
  exact (phi_block_form (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z)) z).symm

/-- **`hrel_split` discharged.** On the strip, the genuine relation `∑ q_{ij}F_iF_j + ∑ l_k F_k + c = 0`
(`F_k = ζ(s+k,−n+e^z)`) equals the block sum `Φb + Ψb + Θb`: substitute `F_k = E_k + R_k` (`hFk`,
`= Fk_zform`), then `relation_collect` regroups into the three blocks and `PhiB_eq_products` matches the
quadratic block. So the block sum vanishes wherever the relation does — the substitution input of
`n2_blocks_vanish`. -/
theorem hrel_split_of_genuine (s : ℂ) (n : ℕ) {B : ℝ}
    (q : Fin 3 → Fin 3 → Polynomial ℂ) (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ)
    (R : Fin 3 → ℂ → ℂ)
    (hFk : ∀ (k : Fin 3) (z : ℂ), z.re < B → -Real.pi < z.im → z.im < Real.pi →
        HurwitzZetaShift.hzeta (s + (k : ℂ)) (-(n : ℂ) + Complex.exp z)
          = Complex.exp (-(s + (k : ℂ)) * z) + R k z)
    (hrel : ∀ z : ℂ, z.re < B → -Real.pi < z.im → z.im < Real.pi →
        (∑ i : Fin 3, ∑ j : Fin 3, (q i j).eval (-(n : ℂ) + Complex.exp z)
            * (HurwitzZetaShift.hzeta (s + (i : ℂ)) (-(n : ℂ) + Complex.exp z)
              * HurwitzZetaShift.hzeta (s + (j : ℂ)) (-(n : ℂ) + Complex.exp z)))
          + (∑ k : Fin 3, (l k).eval (-(n : ℂ) + Complex.exp z)
              * HurwitzZetaShift.hzeta (s + (k : ℂ)) (-(n : ℂ) + Complex.exp z))
          + cc.eval (-(n : ℂ) + Complex.exp z) = 0)
    (z : ℂ) (hz : z.re < B) (hz1 : -Real.pi < z.im) (hz2 : z.im < Real.pi) :
    PhiB s n q z + PsiB s n q l R z + ThetaB s n q l cc R z = 0 := by
  rw [PhiB_eq_products, PsiB, ThetaB]
  have hcollect := relation_collect (s := s)
    (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
    (fun k => (l k).eval (-(n : ℂ) + Complex.exp z))
    (cc.eval (-(n : ℂ) + Complex.exp z)) z (fun k => R k z)
  have hr := hrel z hz hz1 hz2
  simp only [Fin.sum_univ_three] at hr hcollect ⊢
  rw [hFk 0 z hz hz1 hz2, hFk 1 z hz hz1 hz2, hFk 2 z hz hz1 hz2] at hr
  linear_combination hr - hcollect

end HurwitzN2Main
