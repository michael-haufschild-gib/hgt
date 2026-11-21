import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingInverse
import Mathlib.Algebra.Polynomial.Roots

/-!
# The common denominator of a probe response

Each supported nonzero Bohr frequency contributes one factor to the
denominator, independently of its multiplicity. The numerator omits
that factor on the corresponding matrix entry.
-/

open Matrix Polynomial Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

/-- The distinct nonzero frequencies carried by the probe. -/
def abelProbeBohrGaps (hH : H.IsHermitian) (X : Matrix ι ι ℂ) : Finset ℝ := by
  classical
  exact ((Finset.univ.filter fun p : ι × ι =>
    hamiltonianEnergyCoordinates hH X p.1 p.2 ≠ 0).image
      (fun p => hamiltonianGap hH p.1 p.2)).erase 0

theorem mem_abelProbeBohrGaps (hH : H.IsHermitian) (X : Matrix ι ι ℂ) (g : ℝ) :
    g ∈ abelProbeBohrGaps hH X ↔ g ≠ 0 ∧
      ∃ i j, hamiltonianGap hH i j = g ∧ hamiltonianEnergyCoordinates hH X i j ≠ 0 := by
  classical
  simp only [abelProbeBohrGaps, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hn, ⟨⟨i, j⟩, hx, hg⟩⟩
    exact ⟨hn, i, j, hg, hx⟩
  · rintro ⟨hn, i, j, hg, hx⟩
    exact ⟨hn, (i, j), hx, hg⟩

/-- Membership in the support can also be read from the gap projection. -/
theorem mem_abelProbeBohrGaps_iff_gapComponent_ne_zero (hH : H.IsHermitian)
    (X : Matrix ι ι ℂ) (g : ℝ) :
    g ∈ abelProbeBohrGaps hH X ↔ g ≠ 0 ∧ hamiltonianGapComponent hH g X ≠ 0 := by
  rw [mem_abelProbeBohrGaps]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨i, j, hg, hx⟩ h
    have he := congrArg (fun Y : Matrix ι ι ℂ => hamiltonianEnergyCoordinates hH Y i j) h
    rw [energyCoordinates_gapComponent_apply, if_pos hg, map_zero, Matrix.zero_apply] at he
    exact hx he
  · intro h
    by_contra hs
    apply h
    apply (hamiltonianEnergyCoordinates hH).injective
    rw [map_zero]
    refine Matrix.ext fun i j => ?_
    change hamiltonianEnergyCoordinates hH (hamiltonianGapComponent hH g X) i j = 0
    rw [energyCoordinates_gapComponent_apply]
    by_cases hg : hamiltonianGap hH i j = g
    · rw [if_pos hg]
      exact not_not.mp (fun hn => hs ⟨i, j, hg, hn⟩)
    · rw [if_neg hg]

/-- Only off-diagonal pairs can contribute to the nonzero gap count. -/
theorem card_abelProbeBohrGaps_le (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    (abelProbeBohrGaps hH X).card ≤ Fintype.card ι * Fintype.card ι - Fintype.card ι := by
  classical
  let s := (Finset.univ : Finset ι).offDiag
  let f := fun p : ι × ι => hamiltonianGap hH p.1 p.2
  have hs : abelProbeBohrGaps hH X ⊆ s.image f := by
    intro g hg
    obtain ⟨h0, i, j, he, _⟩ := (mem_abelProbeBohrGaps hH X g).mp hg
    have hij : i ≠ j := by
      intro h
      subst j
      rw [hamiltonianGap, sub_self] at he
      exact h0 he.symm
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩, he⟩
  calc
    _ ≤ (s.image f).card := Finset.card_le_card hs
    _ ≤ s.card := Finset.card_image_le
    _ = _ := by rw [show s = (Finset.univ : Finset ι).offDiag from rfl,
      Finset.offDiag_card, Finset.card_univ]

/-- The factor for frequency `g` in the inverse-shift variable. -/
def abelGapFactor (g : ℝ) : Polynomial ℂ := 1 - Polynomial.X * Polynomial.C (g : ℂ)

@[simp] theorem eval_abelGapFactor (g : ℝ) (γ : ℂ) :
    (abelGapFactor g).eval γ = 1 - γ * (g : ℂ) := by
  simp only [abelGapFactor, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C]

private theorem natDegree_abelGapFactor_le (g : ℝ) : (abelGapFactor g).natDegree ≤ 1 := by
  unfold abelGapFactor
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_one]
    exact Nat.zero_le 1
  · exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_X, Polynomial.natDegree_C,
      add_zero])

private theorem abelGapFactor_eval_ne_zero (ε : Ioi (0 : ℝ)) (g : ℝ) :
    (abelGapFactor g).eval (hamiltonianAbelShift ε)⁻¹ ≠ 0 := by
  rw [eval_abelGapFactor]
  intro he
  have he' := congrArg (fun z : ℂ => hamiltonianAbelShift ε * z) (sub_eq_zero.mp he)
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ (hamiltonianAbelShift_ne_zero ε), one_mul] at he'
  exact hamiltonianAbelShift_im_ne_zero ε
    ((congrArg Complex.im he').trans (Complex.ofReal_im g))

private theorem natDegree_prod_abelGapFactor_le (s : Finset ℝ) :
    (∏ g ∈ s, abelGapFactor g).natDegree ≤ s.card := by
  refine (Polynomial.natDegree_prod_le s abelGapFactor).trans ?_
  calc
    _ ≤ ∑ _g ∈ s, (1 : ℕ) := Finset.sum_le_sum (fun g _ => natDegree_abelGapFactor_le g)
    _ = _ := by simp

/-- Squarefree common denominator of an Abel response. -/
def abelBohrDenominator (hH : H.IsHermitian) (X : Matrix ι ι ℂ) : Polynomial ℂ :=
  ∏ g ∈ abelProbeBohrGaps hH X, abelGapFactor g

theorem natDegree_abelBohrDenominator_le (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    (abelBohrDenominator hH X).natDegree ≤ (abelProbeBohrGaps hH X).card :=
  natDegree_prod_abelGapFactor_le _

/-- The numerator in energy coordinates, with the entry's own gap factor removed. -/
def abelBohrNumerator (hH : H.IsHermitian) (X : Matrix ι ι ℂ) : Matrix ι ι (Polynomial ℂ) := by
  classical
  exact Matrix.of fun i j => Polynomial.C (hamiltonianEnergyCoordinates hH X i j) *
    ∏ g ∈ (abelProbeBohrGaps hH X).erase (hamiltonianGap hH i j), abelGapFactor g

theorem eval_abelBohrDenominator_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    (abelBohrDenominator hH X).eval 0 = 1 := by
  simp only [abelBohrDenominator, Polynomial.eval_prod, eval_abelGapFactor, zero_mul, sub_zero,
    Finset.prod_const_one]

theorem eval_abelBohrDenominator_ne_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (ε : Ioi (0 : ℝ)) : (abelBohrDenominator hH X).eval (hamiltonianAbelShift ε)⁻¹ ≠ 0 := by
  rw [abelBohrDenominator, Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun g _ => abelGapFactor_eval_ne_zero ε g

/-- The common numerator has degree at most the size of the gap support. -/
theorem natDegree_abelBohrNumerator_apply_le (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (i j : ι) : (abelBohrNumerator hH X i j).natDegree ≤ (abelProbeBohrGaps hH X).card := by
  classical
  rw [abelBohrNumerator, Matrix.of_apply]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact (natDegree_prod_abelGapFactor_le _).trans Finset.card_erase_le

theorem eval_abelBohrNumerator_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ) (i j : ι) :
    (abelBohrNumerator hH X i j).eval 0 = hamiltonianEnergyCoordinates hH X i j := by
  simp only [abelBohrNumerator, Matrix.of_apply, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, eval_abelGapFactor, zero_mul, sub_zero, Finset.prod_const_one, mul_one]

/-- Multiplication by the entry's factor gives the original probe coefficient. -/
theorem abelGapFactor_mul_response_energyEntry (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (X : Matrix ι ι ℂ) (i j : ι) :
    (abelGapFactor (hamiltonianGap hH i j)).eval (hamiltonianAbelShift ε)⁻¹ *
      hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH 0 ε X) i j =
      hamiltonianEnergyCoordinates hH X i j := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  have hy : hamiltonianAbelInverse H ε Y = X := hamiltonianAbelInverse_leftInverse hH ε X
  have he := congrArg (fun M : Matrix ι ι ℂ => hamiltonianEnergyCoordinates hH M i j) hy
  rw [hamiltonianAbelInverse_eq_sub, map_sub, Matrix.sub_apply, map_smul, Matrix.smul_apply,
      smul_eq_mul, energyCoordinates_commutator_apply] at he
  rw [eval_abelGapFactor, sub_mul, one_mul, mul_assoc]
  exact he

theorem eval_abelBohrNumerator (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (ε : Ioi (0 : ℝ)) (i j : ι) :
    (abelBohrNumerator hH X i j).eval (hamiltonianAbelShift ε)⁻¹ =
      (abelBohrDenominator hH X).eval (hamiltonianAbelShift ε)⁻¹ *
        hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH 0 ε X) i j := by
  classical
  let γ := (hamiltonianAbelShift ε)⁻¹
  let g := hamiltonianGap hH i j
  let x := hamiltonianEnergyCoordinates hH X i j
  let y := hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH 0 ε X) i j
  let s := abelProbeBohrGaps hH X
  let f := fun a => (abelGapFactor a).eval γ
  have he : f g * y = x := abelGapFactor_mul_response_energyEntry hH ε X i j
  rw [abelBohrNumerator, Matrix.of_apply, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, abelBohrDenominator, Polynomial.eval_prod]
  change x * (∏ a ∈ s.erase g, f a) = (∏ a ∈ s, f a) * y
  by_cases hx : x = 0
  · have hy : y = 0 := (mul_eq_zero.mp (he.trans hx)).resolve_left
      (abelGapFactor_eval_ne_zero ε g)
    rw [hx, hy, zero_mul, mul_zero]
  by_cases hg : g = 0
  · have hng : g ∉ s := fun hm => ((mem_abelProbeBohrGaps hH X g).mp hm).1 hg
    rw [Finset.erase_eq_of_notMem hng, mul_comm]
    have hf : f g = 1 := by simp only [f, hg, eval_abelGapFactor, Complex.ofReal_zero,
      mul_zero, sub_zero]
    rw [hf, one_mul] at he
    rw [he]
  · have hm : g ∈ s := (mem_abelProbeBohrGaps hH X g).mpr ⟨hg, i, j, rfl, hx⟩
    rw [← he, ← Finset.prod_erase_mul s f hm]
    ring

#print axioms mem_abelProbeBohrGaps_iff_gapComponent_ne_zero
#print axioms card_abelProbeBohrGaps_le
#print axioms eval_abelBohrNumerator

end

end GaloisForLFunctions.HTGeometry
