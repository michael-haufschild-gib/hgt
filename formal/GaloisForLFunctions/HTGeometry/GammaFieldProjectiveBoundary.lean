import GaloisForLFunctions.HTGeometry.GammaVerticalSuperPolynomialDecay

/-!
# The projective boundary of the Gamma field

An element of `ℂ(s)⟨Γ⟩` in monomial form is `Γ^j · R(s) · ψ^D` on a vertical line.  Its boundary
datum is the triple `(j, deg R, D)`, ordered lexicographically: `Γ` decays exponentially, the rational
factor polynomially, and the digamma only logarithmically.

A strictly larger `Γ`-exponent in the numerator therefore makes the normalized ratio vanish whatever
the other data, and when the `Γ`-exponents agree the `Γ` factors cancel and the digamma-field
comparison takes over.  This is eq. (5) for the full Gamma field: a family normalized by a
lexicographically minimal member has a constant projective limit, nonzero exactly at the members
sharing the minimal datum.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The point of the vertical line `Re s = 1/2 + m` at height `t`. -/
noncomputable def gammaVerticalPoint (m : ℕ) (t : ℝ) : ℂ := ((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- An element of the Gamma field in monomial form: `Γ^j · (p/q) · ψ^D` on the line. -/
noncomputable def gammaFieldElt (m j : ℕ) (p q : Polynomial ℂ) (D : ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma (gammaVerticalPoint m t) ^ j
    * (p.eval (gammaVerticalPoint m t) / q.eval (gammaVerticalPoint m t))
    * Complex.digamma (gammaVerticalPoint m t) ^ D

/-- The algebraic identity behind the ratio decomposition, in atoms. -/
theorem key_ratio_identity (Gjb Gc zdu psiA psiB P Qa Pb Qb : ℂ)
    (hGjb : Gjb ≠ 0) (hz : zdu ≠ 0) (hQa : Qa ≠ 0) (hQb : Qb ≠ 0) (hPb : Pb ≠ 0)
    (hpsiB : psiB ≠ 0) :
    (Gjb * Gc * (P / Qa) * psiA) / (Gjb * (Pb / Qb) * psiB)
      = Gc * zdu * psiA * ((P * Qb) / zdu) * (1 / (Qa * Pb)) * (1 / psiB) := by
  field_simp

/-- **Eq. (5), the Gamma direction.**  A strictly larger power of `Γ` in the numerator makes the
ratio vanish, whatever the rational and digamma data. -/
theorem tendsto_ratio_gammaFieldElt_of_gamma_lt (m : ℕ) (pa qa pb qb : Polynomial ℂ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {ja jb Da Db : ℕ} (hj : jb < ja) :
    Tendsto (fun t : ℝ => gammaFieldElt m ja pa qa Da t / gammaFieldElt m jb pb qb Db t)
      atTop (nhds 0) := by
  classical
  have hσ : (0 : ℝ) ≤ 1 / 2 + m := by positivity
  have hv : qa * pb ≠ 0 := mul_ne_zero hqa hpb
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ja = jb + c := ⟨ja - jb, by omega⟩
  have hcpos : 0 < c := by omega
  have hF1 := tendsto_gamma_pow_mul_digamma_vertical m hcpos (pa * qb).natDegree Da
  have hF2 := tendsto_eval_div_pow_natDegree_vertical (1 / 2 + m : ℝ) (pa * qb)
  have hF3 := tendsto_ratio_poly_le (1 / 2 + m : ℝ) 1 (qa * pb) hv (by simp)
  have hF4 := tendsto_digamma_pow_ratio hσ (Da := 0) (Db := Db) (Nat.zero_le Db)
  have hprod := ((hF1.mul hF2).mul hF3).mul hF4
  rw [zero_mul, zero_mul, zero_mul] at hprod
  refine hprod.congr' ?_
  have hψ : ∀ᶠ t : ℝ in atTop,
      Complex.digamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical hσ).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_vertical_ne_zero (1 / 2 + m : ℝ),
    eventually_eval_ne_zero (1 / 2 + m : ℝ) hqa,
    eventually_eval_ne_zero (1 / 2 + m : ℝ) hqb,
    eventually_eval_ne_zero (1 / 2 + m : ℝ) hpb, hψ,
    eventually_gamma_ne_zero m] with t hs hqat hqbt hpbt hψt hΓt
  simp only [gammaFieldElt, gammaVerticalPoint, Polynomial.eval_mul, Polynomial.eval_one, pow_zero, hc,
    pow_add]
  set z : ℂ := ((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I with hzdef
  exact (key_ratio_identity (Complex.Gamma z ^ jb) (Complex.Gamma z ^ c)
    (z ^ (pa * qb).natDegree) (Complex.digamma z ^ Da) (Complex.digamma z ^ Db)
    (pa.eval z) (qa.eval z) (pb.eval z) (qb.eval z)
    (pow_ne_zero _ hΓt) (pow_ne_zero _ hs) hqat hqbt hpbt (pow_ne_zero _ hψt)).symm

/-- **Eq. (5) for the Gamma field, lexicographic form.**  With the boundary datum
`(Γ-exponent, degree, digamma exponent)` ordered lexicographically, a dominated numerator has a
convergent normalized ratio, and the limit is nonzero exactly when all three data agree. -/
theorem tendsto_ratio_gammaFieldElt_lex (m : ℕ) (pa qa pb qb : Polynomial ℂ)
    (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {ja jb Da Db : ℕ}
    (hlex : jb < ja ∨ (ja = jb ∧ ((pa * qb).natDegree < (qa * pb).natDegree ∨
      ((pa * qb).natDegree = (qa * pb).natDegree ∧ Da ≤ Db)))) :
    Tendsto (fun t : ℝ => gammaFieldElt m ja pa qa Da t / gammaFieldElt m jb pb qb Db t)
      atTop (nhds (if ja = jb ∧ (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)) := by
  classical
  rcases hlex with hj | ⟨hjeq, hrest⟩
  · rw [if_neg (fun h => absurd h.1 (Nat.ne_of_gt hj))]
    exact tendsto_ratio_gammaFieldElt_of_gamma_lt m pa qa pb qb hqa hqb hpb hj
  · subst hjeq
    have hσ : (0 : ℝ) < 1 / 2 + m := by positivity
    have hbase := tendsto_ratio_digammaField_lex (σ := 1 / 2 + m) hσ pa qa pb qb hqa hqb hpb
      (Da := Da) (Db := Db) hrest
    have hif : (if ja = ja ∧ (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)
        = (if (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
        then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0) := by
      by_cases h : (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
      · rw [if_pos ⟨rfl, h⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.2), if_neg h]
    rw [hif]
    refine hbase.congr' ?_
    filter_upwards [eventually_gamma_ne_zero m] with t hΓt
    have hG : Complex.Gamma (gammaVerticalPoint m t) ^ ja ≠ 0 := pow_ne_zero _ hΓt
    simp only [gammaFieldElt, gammaVerticalPoint]
    rw [mul_assoc, mul_assoc]
    exact (mul_div_mul_left _ _ hG).symm

end GaloisForLFunctions
