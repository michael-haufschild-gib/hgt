import GaloisForLFunctions.HTGeometry.BlockKaehlerPrincipalSymbol
import GaloisForLFunctions.HTGeometry.GeneralPrincipalSymbolHorizonIdeal
import GaloisForLFunctions.HTGeometry.IdealPowerSaturation
import Mathlib.Data.Fintype.EquivFin

/-!
# The Kähler scheme of a free hypertranscendence horizon

The finite free word packet has one lower row for every depth `r < d` and one terminal row.  Its
lower row coefficients are all ordered law monomials of degree `r`; its terminal coefficients are
an arbitrary family `P` of homogeneous horizon equations.  This file proves, unconditionally,
that the scalar maximal-minor ideal and the intrinsic Kähler coefficient ideal remember exactly

`idealOfVars ^ (d * (d - 1) / 2) * lawEquationIdeal P`.

Thus the actual Kähler principal symbol is the prescribed horizon ideal together with one
universal thickening at the affine cone vertex.  The thickness is the sum of all lower jet depths.
It records the state before a nonzero law direction has been selected and introduces no additional
projective component.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial
open scoped BigOperators Pointwise

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι] [Fintype η]

/-- Ordered lower words, tagged by depth, together with terminal horizon labels. -/
abbrev PretemporalRawPrincipalPayload (ι η : Type v) (d : ℕ) :=
  (Σ r : Fin d, Fin (r : ℕ) → ι) ⊕ η

/-- A finite canonical enumeration of the ordered-word and terminal payload. -/
abbrev PretemporalPrincipalPayload (ι η : Type v) [Fintype ι] [Fintype η] (d : ℕ) :=
  Fin (Fintype.card (PretemporalRawPrincipalPayload ι η d))

/-- Decode the finite enumeration back into its mathematical word-or-terminal payload. -/
def pretemporalPrincipalPayloadEquiv (d : ℕ) :
    PretemporalPrincipalPayload ι η d ≃ PretemporalRawPrincipalPayload ι η d :=
  (Fintype.equivFin (PretemporalRawPrincipalPayload ι η d)).symm

/-- The coefficient rows of the free pretemporal packet.  A lower row `r` sees precisely the law
monomials attached to words of length `r`; the last row sees precisely the terminal equations. -/
def pretemporalPrincipalRowCoefficient
    (P : η → MvPolynomial ι K) (d : ℕ) :
    Fin (d + 1) → PretemporalPrincipalPayload ι η d → MvPolynomial ι K :=
  Fin.lastCases
    (fun h => match pretemporalPrincipalPayloadEquiv d h with
      | Sum.inl _ => 0
      | Sum.inr j => P j)
    (fun r h => match pretemporalPrincipalPayloadEquiv d h with
      | Sum.inl q =>
          if hq : q.1 = r then
            ∏ t, MvPolynomial.X ((hq ▸ q.2) t)
          else 0
      | Sum.inr _ => 0)

/-- The coefficient ideal of lower row `r` is exactly the `r`-th power of the irrelevant ideal. -/
theorem pretemporalPrincipalLowerRowIdeal
    (P : η → MvPolynomial ι K) (d : ℕ) (r : Fin d) :
    Ideal.span (Set.range
        (pretemporalPrincipalRowCoefficient P d r.castSucc)) =
      MvPolynomial.idealOfVars ι K ^ (r : ℕ) := by
  rw [MvPolynomial.pow_idealOfVars_eq_span]
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro q ⟨h, rfl⟩
    rw [pretemporalPrincipalRowCoefficient, Fin.lastCases_castSucc]
    generalize he : pretemporalPrincipalPayloadEquiv d h = raw
    cases raw with
    | inr j => simp
    | inl q =>
        by_cases hq : q.1 = r
        · rcases q with ⟨s, w⟩
          dsimp at hq
          subst s
          simp only [dif_pos]
          rw [projectiveWordMonomial_eq_monomial]
          exact Ideal.subset_span ⟨projectiveWordExponent w,
            by
              change (projectiveWordExponent w).sum (fun _ e ↦ e) = (r : ℕ)
              exact projectiveWordExponent_sum w,
            rfl⟩
        · simp [hq]
  · apply Ideal.span_le.2
    rintro q ⟨s, hs, rfl⟩
    have hsdegree : s.sum (fun _ e ↦ e) = (r : ℕ) := by simpa using hs
    obtain ⟨w, hw⟩ := exists_projectiveWordExponent_eq s (r : ℕ) hsdegree
    rw [← hw]
    change MvPolynomial.monomial (projectiveWordExponent w) 1 ∈ _
    rw [← projectiveWordMonomial_eq_monomial]
    apply Ideal.subset_span
    refine ⟨(pretemporalPrincipalPayloadEquiv d).symm (Sum.inl ⟨r, w⟩), ?_⟩
    simp [pretemporalPrincipalRowCoefficient]

/-- The final coefficient row generates exactly the externally supplied horizon ideal. -/
theorem pretemporalPrincipalFinalRowIdeal
    (P : η → MvPolynomial ι K) (d : ℕ) :
    Ideal.span (Set.range
        (pretemporalPrincipalRowCoefficient P d (Fin.last d))) =
      lawEquationIdeal P := by
  rw [lawEquationIdeal]
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro q ⟨h, rfl⟩
    rw [pretemporalPrincipalRowCoefficient, Fin.lastCases_last]
    generalize he : pretemporalPrincipalPayloadEquiv d h = raw
    cases raw with
    | inl q => simp
    | inr j => exact Ideal.subset_span ⟨j, rfl⟩
  · apply Ideal.span_le.2
    rintro q ⟨j, rfl⟩
    apply Ideal.subset_span
    refine ⟨(pretemporalPrincipalPayloadEquiv d).symm (Sum.inr j), ?_⟩
    simp [pretemporalPrincipalRowCoefficient]

/-- Total lower-law degree accumulated before the terminal horizon row. -/
def pretemporalVertexThickness (d : ℕ) : ℕ := d * (d - 1) / 2

/-- The product of all row ideals is the external horizon ideal multiplied by the universal
pretemporal vertex thickness. -/
theorem pretemporalPrincipalRowIdealProduct
    (P : η → MvPolynomial ι K) (d : ℕ) :
    (∏ i, Ideal.span (Set.range (pretemporalPrincipalRowCoefficient P d i))) =
      MvPolynomial.idealOfVars ι K ^ pretemporalVertexThickness d *
        lawEquationIdeal P := by
  have hsum : (∑ i : Fin d, (i : ℕ)) = d * (d - 1) / 2 := by
    rw [Finset.sum_fin_eq_sum_range]
    calc
      (∑ i ∈ Finset.range d, if h : i < d then (⟨i, h⟩ : Fin d).val else 0) =
          ∑ i ∈ Finset.range d, i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_range.mp hi]
      _ = d * (d - 1) / 2 := Finset.sum_range_id d
  rw [Fin.prod_univ_castSucc]
  simp_rw [pretemporalPrincipalLowerRowIdeal]
  rw [pretemporalPrincipalFinalRowIdeal, Finset.prod_pow_eq_pow_sum, hsum]
  rfl

/-- **Exact free principal-symbol scheme theorem.**  The scalar maximal-minor ideal of the actual
ordered-word block packet is the general principal-symbol ideal. -/
theorem freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal
    (P : η → MvPolynomial ι K) (d : ℕ) :
    universalLinearJetMinorIdeal
        (blockDiagonalLinearJetCoefficient
          (pretemporalPrincipalRowCoefficient P d)) =
      generalPrincipalSymbolIdeal P (pretemporalVertexThickness d) := by
  rw [blockDiagonalLinearJetMinorIdeal_eq_prod_rowIdeals,
    pretemporalPrincipalRowIdealProduct,
    generalPrincipalSymbolIdeal_eq_irrelevantPow_mul]

/-- **Exact free Kähler horizon-scheme theorem.**  The intrinsic Kähler coefficient ideal is the
base change of the general principal-symbol ideal, hence of
`idealOfVars ^ pretemporalVertexThickness d * lawEquationIdeal P`. -/
theorem freePretemporalPrincipalKaehlerCoefficientIdeal_eq_map_generalPrincipalSymbolIdeal
    (P : η → MvPolynomial ι K) (d : ℕ) :
    universalLinearJetKaehlerCoefficientIdeal
        (blockDiagonalLinearJetCoefficient
          (pretemporalPrincipalRowCoefficient P d)) =
      Ideal.map
        (MvPolynomial.C : MvPolynomial ι K →+*
          MvPolynomial
            (LinearJetBlockColumn (d + 1) (PretemporalPrincipalPayload ι η d))
            (MvPolynomial ι K))
        (generalPrincipalSymbolIdeal P (pretemporalVertexThickness d)) := by
  rw [blockDiagonalLinearJetKaehlerCoefficientIdeal_eq_map_prod_rowIdeals,
    pretemporalPrincipalRowIdealProduct,
    ← generalPrincipalSymbolIdeal_eq_irrelevantPow_mul]

/-- **Projective scheme reconstruction.**  Saturating the scalar Kähler/minor symbol by the
irrelevant ideal recovers exactly the saturation of the externally supplied horizon ideal.  The
universal vertex thickness therefore loses no reduced or nonreduced projective structure. -/
theorem freePretemporalPrincipalMinorIdeal_saturation
    (P : η → MvPolynomial ι K) (d : ℕ) :
    idealPowerSaturation (MvPolynomial.idealOfVars ι K)
        (universalLinearJetMinorIdeal
          (blockDiagonalLinearJetCoefficient
            (pretemporalPrincipalRowCoefficient P d))) =
      idealPowerSaturation (MvPolynomial.idealOfVars ι K) (lawEquationIdeal P) := by
  rw [freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal,
    generalPrincipalSymbolIdeal_eq_irrelevantPow_mul,
    idealPowerSaturation_pow_mul]

/-- **Faithful reduction of saturated projective ideals.**  Two externally supplied horizon
presentations have the same saturated ideal exactly when their free Kähler/minor realizations do.
The depth and its affine vertex thickness cannot identify two distinct saturated horizon schemes. -/
theorem freePretemporalPrincipal_saturatedScheme_eq_iff
    {κ : Type v} [Fintype κ]
    (P : η → MvPolynomial ι K) (Q : κ → MvPolynomial ι K) (d e : ℕ) :
    idealPowerSaturation (MvPolynomial.idealOfVars ι K)
        (universalLinearJetMinorIdeal
          (blockDiagonalLinearJetCoefficient
            (pretemporalPrincipalRowCoefficient P d))) =
        idealPowerSaturation (MvPolynomial.idealOfVars ι K)
          (universalLinearJetMinorIdeal
            (blockDiagonalLinearJetCoefficient
              (pretemporalPrincipalRowCoefficient Q e))) ↔
      idealPowerSaturation (MvPolynomial.idealOfVars ι K) (lawEquationIdeal P) =
        idealPowerSaturation (MvPolynomial.idealOfVars ι K) (lawEquationIdeal Q) := by
  rw [freePretemporalPrincipalMinorIdeal_saturation,
    freePretemporalPrincipalMinorIdeal_saturation]

end

end GaloisForLFunctions.HTGeometry
