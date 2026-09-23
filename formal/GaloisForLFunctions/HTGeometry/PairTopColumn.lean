import GaloisForLFunctions.HTGeometry.PairHeadDegree

/-!
# The newest column of the two-coordinate law

At the newest coordinate the shifted operator is scalar, because no jet below the coordinate
responds to it.  On a logarithmic derivative that scalar operator is exact:

`E(∂_m Φ / Φ) = ∂_m(δΦ / Φ)`,

which is the mixed commutation law rearranged.  The border entry of the newest column is the
logarithmic derivative of the last placed factor times the head, and the identity turns its image
into a Wronskian over a square — two degrees below, in both summands:

* the factor contributes `(α'β − αβ')·∏_(i<m−1)p_i` over `p_(m−1)²`;
* the head contributes `α·P(g) + β·W(g)` over `g²`, and both `P(g)` and `W(g)` are two degrees
  below `g²`.

So every entry of the newest column below the border has degree `−2`, which is what the peel of the
determinant consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## The scalar operator at the newest coordinate -/

/-- The shifted operator at the newest coordinate. -/
noncomputable def pairTopShift (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ) :
    CascadeField → CascadeField :=
  fun G => pairDerivation p G + pairResponse p m m * G

/-- **At the newest coordinate the shifted operator is scalar.** -/
theorem pairGradShift_top (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ) (u : ℕ → CascadeField) :
    pairGradShift p m u m = pairTopShift p m (u m) := by
  rw [pairGradShift, pairTopShift, Finset.sum_range_succ]
  have hlow : ∀ l ∈ Finset.range m, pairResponse p m l * u l = 0 := by
    intro l hl
    rw [pairResponse_of_lt (Finset.mem_range.mp hl), zero_mul]
  rw [Finset.sum_eq_zero hlow, zero_add]

theorem iterate_pairGradShift_top (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (u : ℕ → CascadeField) (i : ℕ) :
    ((pairGradShift p m)^[i]) u m = ((pairTopShift p m)^[i]) (u m) := by
  induction i generalizing u with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, pairGradShift_top]

theorem pairTopShift_add (m : ℕ) (x y : CascadeField) :
    pairTopShift p m (x + y) = pairTopShift p m x + pairTopShift p m y := by
  simp only [pairTopShift, map_add]
  ring

/-! ## The image of a logarithmic derivative -/

theorem pairJetMix_top (m : ℕ) (Φ : CascadeField) :
    pairJetMix p m m Φ = pairResponse p m m * fpderiv m Φ := by
  rw [pairJetMix, Finset.sum_eq_single m]
  · intro l hl hlm
    have hlt : l < m := by
      have := Finset.mem_range.mp hl
      omega
    rw [pairResponse_of_lt hlt, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega : m < m + 1)) hnot

/-- **The scalar operator on a logarithmic derivative is a Wronskian over a square.** -/
theorem pairTopShift_logDeriv {m : ℕ} {Φ : CascadeField} (hmem : Φ ∈ coordField m) (hΦ : Φ ≠ 0) :
    pairTopShift p m (fpderiv m Φ / Φ)
      = (fpderiv m (pairDerivation p Φ) * Φ - fpderiv m Φ * pairDerivation p Φ) / Φ ^ (2 : ℕ) := by
  have hmix := fpderiv_pairDerivation_mixed_coordField (p := p) (m := m) (k := m) hmem
  rw [pairJetMix_top] at hmix
  have hsub : pairDerivation p (fpderiv m Φ)
      = fpderiv m (pairDerivation p Φ) - pairResponse p m m * fpderiv m Φ := by
    rw [hmix]
    ring
  rw [pairTopShift, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hsub]
  simp only [smul_eq_mul]
  field_simp
  ring

/-! ## The last placed factor -/

variable {α β : Polynomial ℂ} {m' : ℕ}

theorem pairFactor_top_eq (hp : p m' = affinePair α β) :
    pairFactor (p m') m' = fact α m' * fx (m' + 1) + fact β m' := by
  rw [hp]
  exact pairFactor_affinePair α β m'

theorem fpderiv_top_pairFactor (hp : p m' = affinePair α β) :
    fpderiv (m' + 1) (pairFactor (p m') m') = fact α m' := by
  rw [hp]
  exact fpderiv_pairFactor_affinePair_top α β m'

theorem pairFactor_top_ne_zero (hα : α ≠ 0) (hp : p m' = affinePair α β) :
    pairFactor (p m') m' ≠ 0 := by
  rw [hp]
  exact pairFactor_affinePair_ne_zero hα β m'

/-- **The response at the newest coordinate.** -/
theorem pairResponse_top (hp : p m' = affinePair α β) :
    pairResponse p (m' + 1) (m' + 1) = pairJet p m' * fact α m' := by
  rw [pairResponse, pairJet_succ, Derivation.leibniz, fpderiv_pairJet_of_gt p (by omega),
    fpderiv_top_pairFactor hp]
  simp only [smul_eq_mul]
  ring

theorem pairDerivation_pairFactor_top (hp : p m' = affinePair α β) :
    pairDerivation p (pairFactor (p m') m')
      = fact α m' * (pairJet p m' * pairFactor (p m') m')
        + fx (m' + 1) * (fact α.derivative m' * pairJet p m')
        + fact β.derivative m' * pairJet p m' := by
  rw [pairFactor_top_eq hp, map_add, Derivation.leibniz, derivation_fact, derivation_fact]
  simp only [pairDerivation_fx, smul_eq_mul]
  rw [pairJet_succ, pairFactor_top_eq hp]

theorem fpderiv_top_pairDerivation_pairFactor (hp : p m' = affinePair α β) :
    fpderiv (m' + 1) (pairDerivation p (pairFactor (p m') m'))
      = fact α m' * (pairJet p m' * fact α m') + fact α.derivative m' * pairJet p m' := by
  rw [pairDerivation_pairFactor_top hp]
  simp only [map_add, Derivation.leibniz, smul_eq_mul,
    fpderiv_fact_of_ne (by omega : m' ≠ m' + 1), fpderiv_pairJet_of_gt p (by omega : m' < m' + 1),
    fpderiv_top_pairFactor hp, fpderiv_fx_self]
  ring

/-- **The factor's contribution to the newest column is a Wronskian over the square.** -/
theorem pairTopShift_pairLogTerm (hα : α ≠ 0) (hp : p m' = affinePair α β) :
    pairTopShift p (m' + 1) (pairLogTerm p m' (m' + 1))
      = pairJet p m' * fact (α.derivative * β - α * β.derivative) m'
          / (pairFactor (p m') m') ^ (2 : ℕ) := by
  have hne : pairFactor (p m') m' ≠ 0 := pairFactor_top_ne_zero hα hp
  have hmem : pairFactor (p m') m' ∈ coordField (m' + 1) :=
    pairFactor_mem_coordField (le_refl (m' + 1)) (p m')
  have hlt : pairLogTerm p m' (m' + 1)
      = fpderiv (m' + 1) (pairFactor (p m') m') / pairFactor (p m') m' := rfl
  rw [hlt, pairTopShift_logDeriv hmem hne, fpderiv_top_pairDerivation_pairFactor hp,
    fpderiv_top_pairFactor hp, pairDerivation_pairFactor_top hp, pairFactor_top_eq hp,
    fact_sub, fact_mul, fact_mul]
  field_simp
  ring

/-! ## The head -/

theorem pairDerivation_fact_top (q : Polynomial ℂ) :
    pairDerivation p (fact q (m' + 1))
      = fact q.derivative (m' + 1) * pairJet p (m' + 1) := by
  rw [derivation_fact]
  simp only [pairDerivation_fx]

theorem fpderiv_top_pairDerivation_fact (q : Polynomial ℂ) (hp : p m' = affinePair α β) :
    fpderiv (m' + 1) (pairDerivation p (fact q (m' + 1)))
      = fact q.derivative.derivative (m' + 1) * pairJet p (m' + 1)
        + fact q.derivative (m' + 1) * (pairJet p m' * fact α m') := by
  rw [pairDerivation_fact_top, Derivation.leibniz, fpderiv_fact_self]
  simp only [smul_eq_mul]
  rw [show fpderiv (m' + 1) (pairJet p (m' + 1)) = pairResponse p (m' + 1) (m' + 1) from rfl,
    pairResponse_top hp]
  ring

/-- **The head's contribution to the newest column.**  Its two summands are the head's defect and
the head's Wronskian, both two degrees below `g²`. -/
theorem pairTopShift_logFactor_head {g : Polynomial ℂ} (hg : g ≠ 0)
    (hp : p m' = affinePair α β) :
    pairTopShift p (m' + 1) (logFactor g (m' + 1))
      = pairJet p m' * (fact α m' * fact (headDefect g) (m' + 1)
          + fact β m' * fact (headWr g) (m' + 1)) / (fact g (m' + 1)) ^ (2 : ℕ) := by
  have hne : fact g (m' + 1) ≠ 0 := fact_ne_zero hg (m' + 1)
  have hmem : fact g (m' + 1) ∈ coordField (m' + 1) :=
    fact_mem_coordField (le_refl (m' + 1)) g
  have hlf : logFactor g (m' + 1)
      = fpderiv (m' + 1) (fact g (m' + 1)) / fact g (m' + 1) := by
    rw [fpderiv_fact_self, logFactor]
  rw [hlf, pairTopShift_logDeriv hmem hne, fpderiv_top_pairDerivation_fact g hp,
    pairDerivation_fact_top, fpderiv_fact_self, pairJet_succ, pairFactor_top_eq hp,
    headDefect, headWr, fact_add, fact_mul, fact_sub, fact_mul, fact_mul, fact_mul, fact_X]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
