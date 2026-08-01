import GaloisForLFunctions.HTGeometry.GammaFieldSumBoundary
import GaloisForLFunctions.HTGeometry.DigammaFieldValuation

/-!
# Monomials in the full digamma tower

A general monomial of `ℂ(s)⟨Γ⟩` is `Γ^j · (p/q) · ∏ (ψ⁽ⁱ⁾)^{E i}`.  Splitting the jet product into
its order-zero factor and the rest, such a monomial is a pure monomial times a product of positive
order polygammas, and those vanish on a vertical line.

So the boundary datum of a full-tower monomial is that of its pure part when no derivative occurs,
and the monomial is negligible as soon as one does; finite sums behave termwise.  This extends the
projective boundary from the pure monomials to the whole monomial basis of the Gamma field.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- A Gamma-field monomial in the full digamma tower: `Γ^j · (p/q) · ∏ (ψ⁽ⁱ⁾)^{E i}`. -/
noncomputable def gammaFieldJetElt (m j : ℕ) (p q : Polynomial ℂ) {r : ℕ}
    (E : Fin (r + 1) → ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ j
    * (p.eval (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      / q.eval (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I))
    * ∏ i : Fin (r + 1), (digammaJetLine (1 / 2 + m) (i : ℕ) t) ^ (E i)

theorem gammaFieldJetElt_eq (m j : ℕ) (p q : Polynomial ℂ) {r : ℕ} (E : Fin (r + 1) → ℕ) (t : ℝ) :
    gammaFieldJetElt m j p q E t
      = gammaFieldElt m j p q (E 0) t
        * ∏ i : Fin r, (digammaJetLine (1 / 2 + m) ((i.succ : Fin (r + 1)) : ℕ) t) ^ (E i.succ) := by
  rw [gammaFieldJetElt, gammaFieldElt, gammaVerticalPoint, Fin.prod_univ_succ]
  have h0 : digammaJetLine (1 / 2 + m) ((0 : Fin (r + 1)) : ℕ) t
      = Complex.digamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    rw [digammaJetLine, Fin.val_zero, iteratedDeriv_zero]
  rw [h0]
  ring

/-- **Eq. (5) for monomials in the full digamma tower.**  A monomial carrying a derivative factor is
negligible against a pure one with the same datum; otherwise the boundary datum is the same. -/
theorem tendsto_ratio_gammaFieldJet (m : ℕ) {r : ℕ} (ja : ℕ) (pa qa : Polynomial ℂ)
    (Ea : Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa (Ea 0) jb pb qb Db) :
    Tendsto (fun t : ℝ => gammaFieldJetElt m ja pa qa Ea t / gammaFieldElt m jb pb qb Db t)
      atTop (nhds (gammaMonomialLimit ja pa qa (Ea 0) jb pb qb Db
        * ∏ i : Fin r, (0 : ℂ) ^ (Ea i.succ))) := by
  have hσ : (0 : ℝ) < 1 / 2 + m := by positivity
  have hmono := tendsto_monomial_ratio m (ja := ja) (pa := pa) (qa := qa) (Da := Ea 0)
    (jb := jb) (pb := pb) (qb := qb) (Db := Db) hqa hqb hpb hdom
  have htail := tendsto_tail_prod (σ := 1 / 2 + m) hσ Ea
  have hprod := hmono.mul htail
  refine hprod.congr fun t => ?_
  rw [gammaFieldJetElt_eq]
  ring

/-- A monomial with no derivative factor has the boundary datum of its pure part. -/
theorem tendsto_ratio_gammaFieldJet_pure (m : ℕ) {r : ℕ} (ja : ℕ) (pa qa : Polynomial ℂ)
    (Ea : Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa (Ea 0) jb pb qb Db)
    (hpure : ∀ i : Fin r, Ea i.succ = 0) :
    Tendsto (fun t : ℝ => gammaFieldJetElt m ja pa qa Ea t / gammaFieldElt m jb pb qb Db t)
      atTop (nhds (gammaMonomialLimit ja pa qa (Ea 0) jb pb qb Db)) := by
  have h := tendsto_ratio_gammaFieldJet m ja pa qa Ea jb pb qb Db hqa hqb hpb hdom
  have htail : (∏ i : Fin r, (0 : ℂ) ^ (Ea i.succ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hpure i, pow_zero]
  rwa [htail, mul_one] at h

/-- A monomial carrying a derivative factor is negligible. -/
theorem tendsto_ratio_gammaFieldJet_deriv (m : ℕ) {r : ℕ} (ja : ℕ) (pa qa : Polynomial ℂ)
    (Ea : Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : GammaMonomialDominates ja pa qa (Ea 0) jb pb qb Db)
    {i : Fin r} (hi : Ea i.succ ≠ 0) :
    Tendsto (fun t : ℝ => gammaFieldJetElt m ja pa qa Ea t / gammaFieldElt m jb pb qb Db t)
      atTop (nhds 0) := by
  classical
  have h := tendsto_ratio_gammaFieldJet m ja pa qa Ea jb pb qb Db hqa hqb hpb hdom
  have htail : (∏ k : Fin r, (0 : ℂ) ^ (Ea k.succ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi)
  rwa [htail, mul_zero] at h

/-- **Eq. (3) for a finite sum of full-tower monomials.** -/
theorem tendsto_sum_ratio_gammaFieldJet {ι : Type*} [Fintype ι] (m : ℕ) {r : ℕ} (j : ι → ℕ)
    (p q : ι → Polynomial ℂ) (E : ι → Fin (r + 1) → ℕ) (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ i, q i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ i, GammaMonomialDominates (j i) (p i) (q i) (E i 0) jb pb qb Db) :
    Tendsto (fun t : ℝ =>
      (∑ i, gammaFieldJetElt m (j i) (p i) (q i) (E i) t) / gammaFieldElt m jb pb qb Db t) atTop
      (nhds (∑ i, gammaMonomialLimit (j i) (p i) (q i) (E i 0) jb pb qb Db
        * ∏ k : Fin r, (0 : ℂ) ^ (E i k.succ))) := by
  classical
  have hterm := tendsto_finsetSum (Finset.univ : Finset ι)
    (fun i _ => tendsto_ratio_gammaFieldJet m (j i) (p i) (q i) (E i) jb pb qb Db
      (hq i) hqb hpb (hdom i))
  refine hterm.congr fun t => ?_
  rw [Finset.sum_div]

end GaloisForLFunctions
