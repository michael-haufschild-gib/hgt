import GaloisForLFunctions.HTGeometry.HalfPlaneRational
import GaloisForLFunctions.RHTower.XiOddShiftArchimedeanIrrationality

/-!
# The parity-mass dichotomy for archimedean corrections

A natural-shift family carries exactly two digamma modes of the archimedean factor, weighted by the
even-shift and odd-shift coefficient masses.  Those two modes are independent over the rational
functions, so the family's archimedean correction is half-plane rational **exactly** when both parity
masses vanish.

The sufficient direction is the explicit rational telescope; the necessary direction is
half-translate digamma independence applied to the parity decomposition after subtracting that
telescope and the finitely many simple fractions contributed by the polynomial part of the
archimedean factor.
-/

namespace RHTower

open Complex

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The explicit even-shift telescope is half-plane rational at every base translation. -/
theorem isHalfPlaneRational_xiEvenShiftPrimeCorrection (m : ℕ) (β : ℂ) :
    IsHalfPlaneRational (fun s => xiEvenShiftPrimeCorrection m (s + β)) := by
  have hterm : ∀ j : ℕ, IsHalfPlaneRational
      (fun s : ℂ => 1 / (s + (β + ((2 * j : ℕ) : ℂ) + 2)) +
        1 / (s + (β + ((2 * j : ℕ) : ℂ) + 1)) -
        1 / (s + (β + ((2 * j : ℕ) : ℂ) - 1))) := fun j =>
    ((isHalfPlaneRational_simple _).add (isHalfPlaneRational_simple _)).sub
      (isHalfPlaneRational_simple _)
  have hsum := isHalfPlaneRational_finsetSum (Finset.range m) _ (fun j _ => hterm j)
  refine IsHalfPlaneRational.congr Set.finite_empty (fun z _ _ => ?_) hsum
  rw [xiEvenShiftPrimeCorrection]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show z + β + ((2 * j : ℕ) : ℂ) + 2 = z + (β + ((2 * j : ℕ) : ℂ) + 2) by ring,
    show z + β + ((2 * j : ℕ) : ℂ) + 1 = z + (β + ((2 * j : ℕ) : ℂ) + 1) by ring,
    show z + β + ((2 * j : ℕ) : ℂ) - 1 = z + (β + ((2 * j : ℕ) : ℂ) - 1) by ring]

/-- **Necessity of parity balance.** If a natural-shift family's archimedean correction is half-plane
rational, both parity masses vanish. -/
theorem archimedeanCorrection_family_parity_mass_eq_zero_of_rational {d : ℕ}
    (a : Fin d → ℕ) (c : Fin d → ℂ)
    (h : IsHalfPlaneRational (fun s => ∑ i, c i * logDeriv archFactor (s + (a i : ℂ)))) :
    (∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i) = 0 ∧
      (∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i) = 0 := by
  classical
  set E : ℂ := ∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i with hEdef
  set O : ℂ := ∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i with hOdef
  have hRat : IsHalfPlaneRational
      (fun s => ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ))) :=
    isHalfPlaneRational_finsetSum Finset.univ _
      (fun i _ => (isHalfPlaneRational_xiEvenShiftPrimeCorrection (a i / 2)
        ((a i % 2 : ℕ) : ℂ)).const_mul (c i))
  have hfrac : IsHalfPlaneRational (fun s : ℂ =>
      E * (1 / (s + 0)) + E * (1 / (s + (-1))) + (O * (1 / (s + 1)) + O * (1 / (s + 0)))) :=
    (((isHalfPlaneRational_simple (0 : ℂ)).const_mul E).add
        ((isHalfPlaneRational_simple (-1 : ℂ)).const_mul E)).add
      (((isHalfPlaneRational_simple (1 : ℂ)).const_mul O).add
        ((isHalfPlaneRational_simple (0 : ℂ)).const_mul O))
  have hconst : IsHalfPlaneRational
      (fun _ : ℂ => (E + O) * (((Real.log Real.pi : ℝ) : ℂ) / 2)) :=
    isHalfPlaneRational_const _
  have hmodes : IsHalfPlaneRational
      (fun s => (E / 2) * Complex.digamma (s / 2) + (O / 2) * Complex.digamma ((s + 1) / 2)) := by
    refine IsHalfPlaneRational.congr (Set.finite_singleton (1 : ℂ)) (fun s hs hs1 => ?_)
      (((h.sub hRat).sub hfrac).add hconst)
    have hsne1 : s ≠ 1 := by simpa using hs1
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hs
      norm_num at hs
    have hs1re : 0 < (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hs1ne0 : s + 1 ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      rw [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith
    have hs1ne1 : s + 1 ≠ 1 := fun h0 => hs0 (by linear_combination h0)
    have hdec := archimedeanCorrection_family_parity_decomposition a c hs hsne1
    have hg0 := logDeriv_archFactor_closed hs hs0 hsne1
    have hg1 := logDeriv_archFactor_closed hs1re hs1ne0 hs1ne1
    rw [gammaRealLogConnection] at hg0 hg1
    rw [← hEdef, ← hOdef] at hdec
    have hsm1 : s + 1 - 1 = s := by ring
    rw [hsm1] at hg1
    show (E / 2) * Complex.digamma (s / 2) + (O / 2) * Complex.digamma ((s + 1) / 2) =
      ((∑ i, c i * logDeriv archFactor (s + (a i : ℂ))) -
        (∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ))) -
        (E * (1 / (s + 0)) + E * (1 / (s + (-1))) +
          (O * (1 / (s + 1)) + O * (1 / (s + 0))))) +
        (E + O) * (((Real.log Real.pi : ℝ) : ℂ) / 2)
    rw [hdec, hg0, hg1, show s + 0 = s by ring, show s + (-1 : ℂ) = s - 1 by ring]
    ring
  have hzero := digamma_parity_modes_independent hmodes
  exact ⟨by linear_combination 2 * hzero.1, by linear_combination 2 * hzero.2⟩

/-- **Parity-mass dichotomy.** A natural-shift family's archimedean correction is half-plane
rational exactly when its even-shift and odd-shift coefficient masses both vanish. -/
theorem archimedeanCorrection_family_isHalfPlaneRational_iff {d : ℕ}
    (a : Fin d → ℕ) (c : Fin d → ℂ) :
    IsHalfPlaneRational (fun s => ∑ i, c i * logDeriv archFactor (s + (a i : ℂ))) ↔
      (∑ i ∈ Finset.univ.filter (fun i => a i % 2 = 0), c i) = 0 ∧
        (∑ i ∈ Finset.univ.filter (fun i => ¬ (a i % 2 = 0)), c i) = 0 := by
  classical
  refine ⟨archimedeanCorrection_family_parity_mass_eq_zero_of_rational a c, fun hbal => ?_⟩
  have hRat : IsHalfPlaneRational
      (fun s => ∑ i, c i * xiEvenShiftPrimeCorrection (a i / 2) (s + ((a i % 2 : ℕ) : ℂ))) :=
    isHalfPlaneRational_finsetSum Finset.univ _
      (fun i _ => (isHalfPlaneRational_xiEvenShiftPrimeCorrection (a i / 2)
        ((a i % 2 : ℕ) : ℂ)).const_mul (c i))
  refine IsHalfPlaneRational.congr (Set.finite_singleton (1 : ℂ)) (fun s hs hs1 => ?_) hRat
  have hsne1 : s ≠ 1 := by simpa using hs1
  exact archimedeanCorrection_family_of_parity_balanced a c hbal.1 hbal.2 hs hsne1

end

end RHTower
