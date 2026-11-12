import GaloisForLFunctions.Bottcher.BottcherNotRational
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteRealRootDecomposition
import GaloisForLFunctions.FiniteFreeProbability.NonRealRootCount
import GaloisForLFunctions.GaloisTheoryOfZeros.CenteredJensenDiscriminant
import GaloisForLFunctions.GaloisTheoryOfZeros.JensenQuartetExhaustion

/-!
# The folded Jensen equations exhaust the off-line divisor

Squaring identifies the first-quadrant roots of the centered equation with
the upper-half-plane roots of its quotient, preserving algebraic multiplicity.
Conjugation supplies the other half of the quotient's non-real roots.

The quotient census is therefore exactly half the original non-real census.
It is monotone and exhausts the entire off-line ξ divisor, including infinity,
even though every full centered discriminant is nonnegative.
-/

noncomputable section
open Polynomial Complex FiniteFreeProbability RHTower Filter Topology
set_option autoImplicit false
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem exists_squareRoot_right (w : ℂ) :
    ∃ z : ℂ, z^2 = w ∧ 0 ≤ Complex.re z := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by decide)
  by_cases hr : 0 ≤ z.re
  · exact ⟨z, hz, hr⟩
  · refine ⟨-z, ?_, ?_⟩
    · calc (-z)^2 = z^2 := by ring
           _ = w := hz
    · simpa only [Complex.neg_re] using neg_nonneg.mpr (le_of_not_ge hr)

private def rightSquareRoot (w : ℂ) : ℂ := Classical.choose (exists_squareRoot_right w)

private theorem rightSquareRoot_sq (w : ℂ) : rightSquareRoot w ^ 2 = w :=
  (Classical.choose_spec (exists_squareRoot_right w)).1

private theorem rightSquareRoot_re_nonneg (w : ℂ) : 0 ≤ (rightSquareRoot w).re :=
  (Classical.choose_spec (exists_squareRoot_right w)).2

private theorem rightSquareRoot_injective : Function.Injective rightSquareRoot := by
  intro a b h
  calc a = rightSquareRoot a ^ 2 := (rightSquareRoot_sq a).symm
       _ = rightSquareRoot b ^ 2 := congrArg (fun z : ℂ => z^2) h
       _ = b := rightSquareRoot_sq b

private theorem rightSquareRoot_upper {w : ℂ} (hw : 0 < w.im) :
    0 < (rightSquareRoot w).re ∧ 0 < (rightSquareRoot w).im := by
  have h := congrArg Complex.im (rightSquareRoot_sq w)
  simp only [pow_two, Complex.mul_im] at h
  have hre := rightSquareRoot_re_nonneg w
  have hre' : 0 < (rightSquareRoot w).re := by
    by_contra hle
    have heq := le_antisymm (le_of_not_gt hle) hre
    rw [heq, zero_mul, mul_zero, zero_add] at h
    exact hw.ne' h.symm
  refine ⟨hre', ?_⟩
  by_contra him
  have hprod := mul_nonpos_of_nonneg_of_nonpos hre (le_of_not_gt him)
  nlinarith only [h, hw, hprod]

private theorem rightSquareRoot_square {z : ℂ} (hz : 0 < z.re) :
    rightSquareRoot (z^2) = z := by
  have hs := rightSquareRoot_sq (z^2)
  have hp : (rightSquareRoot (z^2)-z) * (rightSquareRoot (z^2)+z) = 0 := by
    calc _ = rightSquareRoot (z^2)^2-z^2 := by ring
         _ = 0 := sub_eq_zero.mpr hs
  rcases mul_eq_zero.mp hp with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith only [hre, hz, rightSquareRoot_re_nonneg (z^2)]

/-- Squaring is unramified away from zero, so algebraic multiplicity is retained. -/
private theorem rootMultiplicity_comp_square {Q : ℂ[X]} (hQ : Q ≠ 0) {z : ℂ}
    (hz : z ≠ 0) :
    Polynomial.rootMultiplicity z (Polynomial.comp Q ((X : ℂ[X])^2)) =
      Polynomial.rootMultiplicity (z^2) Q := by
  simpa only [C_0, add_zero, hz, if_false, one_mul] using
    BottcherNotRational.rootMultiplicity_comp_quadratic hQ 0 z

/-- Upper quotient roots correspond exactly to first-quadrant roots of the doubled equation. -/
private theorem upperRoots_map_rightSquareRoot {Q : ℂ[X]} (hQ : Q ≠ 0) :
    Multiset.map rightSquareRoot
        (Multiset.filter (fun z : ℂ => 0 < Complex.im z) (Polynomial.roots Q)) =
      Multiset.filter (fun z : ℂ => 0 < Complex.re z ∧ 0 < Complex.im z)
        (Polynomial.roots (Polynomial.comp Q ((X : ℂ[X])^2))) := by
  classical
  ext z
  by_cases hz : 0 < z.re ∧ 0 < z.im
  · have hzsq : 0 < (z^2).im := by
      simp only [pow_two, Complex.mul_im]
      nlinarith only [mul_pos hz.1 hz.2]
    have hz0 : z ≠ 0 := by intro h; simpa [h] using hz.1
    conv_lhs => rw [← rightSquareRoot_square hz.1]
    rw [Multiset.count_map_eq_count' _ _ rightSquareRoot_injective,
      Multiset.count_filter_of_pos (p := fun w : ℂ => 0 < w.im) hzsq,
      Multiset.count_filter_of_pos (p := fun w : ℂ => 0 < w.re ∧ 0 < w.im) hz,
      Polynomial.count_roots, Polynomial.count_roots,
      rootMultiplicity_comp_square hQ hz0]
  · have hr : z ∉ (Q.comp (X^2)).roots.filter (fun z : ℂ => 0 < z.re ∧ 0 < z.im) :=
      fun h => hz (Multiset.mem_filter.mp h).2
    have hl : z ∉ (Q.roots.filter fun z : ℂ => 0 < z.im).map rightSquareRoot := by
      intro h
      obtain ⟨w, hw, hweq⟩ := Multiset.mem_map.mp h
      exact hz (hweq ▸ rightSquareRoot_upper (Multiset.mem_filter.mp hw).2)
    rw [Multiset.count_eq_zero_of_notMem hl, Multiset.count_eq_zero_of_notMem hr]

theorem upperRoot_count_comp_square {Q : ℂ[X]} (hQ : Q ≠ 0) :
    Multiset.card (Multiset.filter (fun z : ℂ => 0 < Complex.im z) (Polynomial.roots Q)) =
      Multiset.card (Multiset.filter (fun z : ℂ => 0 < Complex.re z ∧ 0 < Complex.im z)
        (Polynomial.roots (Polynomial.comp Q ((X : ℂ[X])^2)))) := by
  have h := congrArg Multiset.card (upperRoots_map_rightSquareRoot hQ)
  simpa only [Multiset.card_map] using h

/-- The forced odd-degree root at zero contributes no first-quadrant multiplicity. -/
theorem quadrantRoots_X_mul {P : ℂ[X]} (hP : P ≠ 0) :
    Multiset.filter (fun z : ℂ => 0 < Complex.re z ∧ 0 < Complex.im z)
        (Polynomial.roots ((X : ℂ[X])*P)) =
      Multiset.filter (fun z : ℂ => 0 < Complex.re z ∧ 0 < Complex.im z)
        (Polynomial.roots P) := by
  classical
  ext z
  by_cases hz : 0 < z.re ∧ 0 < z.im
  · have hz0 : z ≠ 0 := by intro h; simpa [h] using hz.1
    rw [Multiset.count_filter_of_pos (p := fun w : ℂ => 0 < w.re ∧ 0 < w.im) hz,
      Multiset.count_filter_of_pos (p := fun w : ℂ => 0 < w.re ∧ 0 < w.im) hz,
      Polynomial.count_roots, Polynomial.count_roots,
      rootMultiplicity_mul (mul_ne_zero X_ne_zero hP),
      rootMultiplicity_eq_zero (by simpa only [IsRoot.def, eval_X] using hz0), zero_add]
  · have hzero (Q : ℂ[X]) :
        Multiset.count z (Q.roots.filter fun z : ℂ => 0 < z.re ∧ 0 < z.im) = 0 :=
      Multiset.count_eq_zero_of_notMem (fun h => hz (Multiset.mem_filter.mp h).2)
    rw [hzero, hzero]

/-- The nonreal multiplicity of a real equation is twice its upper-half-plane count. -/
theorem real_polynomial_nonreal_count (P : ℝ[X]) :
    Multiset.card (Multiset.filter (fun z : ℂ => Complex.im z ≠ 0)
        (Polynomial.roots (Polynomial.map Complex.ofRealHom P))) =
      2 * Multiset.card (Multiset.filter (fun z : ℂ => 0 < Complex.im z)
        (Polynomial.roots (Polynomial.map Complex.ofRealHom P))) := by
  have hfull := FiniteFreeProbability.card_nonreal_roots_map P
  have hsplit := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card P
  have hreal := congrArg Multiset.card (FiniteFreeProbability.filter_im_eq_zero_roots_map P)
  have hmap : algebraMap ℝ ℂ = Complex.ofRealHom := by ext x; rfl
  rw [hmap] at hfull hreal
  simp only [not_not, Multiset.card_map] at hreal
  simp only [RiemannGaussian.realPolynomialRealRootMultiset,
    RiemannGaussian.realPolynomialUpperRootMultiset] at hsplit
  omega

/-- The centered equation after identifying opposite nonzero roots. -/
def foldedCenteredJensen (d : ℕ) : ℝ[X] :=
  if d % 2 = 0 then evenCenteredQuotient (d / 2) else oddCenteredQuotient (d / 2)

private theorem foldedCenteredJensen_even (n : ℕ) :
    foldedCenteredJensen (2*n) = evenCenteredQuotient n := by
  rw [foldedCenteredJensen, if_pos (by omega), show (2*n)/2 = n by omega]

private theorem foldedCenteredJensen_odd (n : ℕ) :
    foldedCenteredJensen (2*n+1) = oddCenteredQuotient n := by
  rw [foldedCenteredJensen, if_neg (by omega), show (2*n+1)/2 = n by omega]

/-- The quotient equation counts the original non-real symmetry orbits, with multiplicity. -/
theorem foldedCenteredJensen_upper_count (d : ℕ) :
    Multiset.card (Multiset.filter (fun z : ℂ => 0 < Complex.im z)
      (Polynomial.roots (Polynomial.map Complex.ofRealHom (foldedCenteredJensen d)))) =
        jensenQuartetCount d := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, d = 2*n ∨ d = 2*n+1 := ⟨d/2, by omega⟩
  · rw [foldedCenteredJensen_even]
    have hne : (evenCenteredQuotient n).map Complex.ofRealHom ≠ 0 :=
      ((evenCenteredQuotient_monic n).map Complex.ofRealHom).ne_zero
    have he := congrArg (Polynomial.map Complex.ofRealHom) (evenCenteredQuotient_factor n)
    simp only [Polynomial.map_comp, Polynomial.map_pow, map_X] at he
    rw [upperRoot_count_comp_square hne, he, roots_monicCenteredJensen]
    rfl
  · rw [foldedCenteredJensen_odd]
    have hne : (oddCenteredQuotient n).map Complex.ofRealHom ≠ 0 :=
      ((oddCenteredQuotient_monic n).map Complex.ofRealHom).ne_zero
    have hcomp : ((oddCenteredQuotient n).map Complex.ofRealHom).comp (X^2) ≠ 0 :=
      (((oddCenteredQuotient_monic n).map Complex.ofRealHom).comp
        (monic_X_pow 2) (by simp)).ne_zero
    have he := congrArg (Polynomial.map Complex.ofRealHom) (oddCenteredQuotient_factor n)
    simp only [Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow, map_X] at he
    rw [upperRoot_count_comp_square hne, ← quadrantRoots_X_mul hcomp, he,
      roots_monicCenteredJensen]
    rfl

/-- Non-real algebraic multiplicity in the quotient equation. -/
def foldedJensenNonrealCount (d : ℕ) : ℕ :=
  Multiset.card (Multiset.filter (fun z : ℂ => Complex.im z ≠ 0)
    (Polynomial.roots (Polynomial.map Complex.ofRealHom (foldedCenteredJensen d))))

/-- Folding retains exactly half the non-real multiplicity. -/
theorem foldedJensenNonrealCount_eq_two_mul (d : ℕ) :
    foldedJensenNonrealCount d = 2 * jensenQuartetCount d := by
  rw [foldedJensenNonrealCount, real_polynomial_nonreal_count,
    foldedCenteredJensen_upper_count]

theorem jensenNonrealCount_eq_two_mul_folded (d : ℕ) :
    jensenNonrealCount d = 2 * foldedJensenNonrealCount d := by
  rw [jensenNonrealCount_eq_four_mul, foldedJensenNonrealCount_eq_two_mul]
  omega

/-- Both parity subsequences fit into one monotone quotient census. -/
theorem foldedJensenNonrealCount_mono : Monotone foldedJensenNonrealCount := by
  intro d e hde
  simpa only [foldedJensenNonrealCount_eq_two_mul] using
    Nat.mul_le_mul_left 2 (jensenQuartetCount_mono hde)

/-- The quotient equations exhaust the entire off-line divisor, including infinity. -/
theorem iSup_two_mul_foldedJensenNonrealCount :
    (⨆ d : ℕ, ((2 * foldedJensenNonrealCount d : ℕ) : ℕ∞)) =
      Set.encard {q : XiZeroCopy | Complex.im (xiSpectralPoint q) ≠ 0} := by
  simp only [← jensenNonrealCount_eq_two_mul_folded]
  exact iSup_jensenNonrealCount

/-- A finite quotient-census bound controls every off-line zero occurrence. -/
theorem offLine_count_le_iff_folded_count (m : ℕ) :
    Set.encard {q : XiZeroCopy | Complex.im (xiSpectralPoint q) ≠ 0} ≤ (2*m : ℕ) ↔
      ∀ d : ℕ, foldedJensenNonrealCount d ≤ m := by
  rw [encard_offLine_le_iff_forall]
  simp only [jensenNonrealCount_eq_two_mul_folded]
  constructor <;> intro h d <;> have hd := h d <;> omega

/-- Despite nonnegative full discriminants, the quotient census retains the complete
finite-versus-infinite alternative for off-line multiplicity. -/
theorem folded_exhaustion_dichotomy :
    (∀ d : ℕ, 0 ≤ Polynomial.discr (xiJensenReal d)) ∧
    ((∃ m : ℕ,
        Set.encard {q : XiZeroCopy | Complex.im (xiSpectralPoint q) ≠ 0} = (4*m : ℕ) ∧
        ∀ᶠ d : ℕ in atTop, foldedJensenNonrealCount d = 2*m) ∨
      (Set.Infinite {q : XiZeroCopy | Complex.im (xiSpectralPoint q) ≠ 0} ∧
        Tendsto foldedJensenNonrealCount atTop atTop)) := by
  refine ⟨xiJensenReal_discr_nonneg, ?_⟩
  rcases quartet_exhaustion_dichotomy.2 with ⟨m, hm, hev⟩ | ⟨hinf, ht⟩
  · exact Or.inl ⟨m, hm, hev.mono (fun d hd => by
      rw [foldedJensenNonrealCount_eq_two_mul, hd])⟩
  · refine Or.inr ⟨hinf, tendsto_atTop.2 (fun m => ?_)⟩
    filter_upwards [ht.eventually_ge_atTop m] with d hd
    rw [foldedJensenNonrealCount_eq_two_mul]
    omega


end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.upperRoot_count_comp_square
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.real_polynomial_nonreal_count
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.foldedCenteredJensen_upper_count
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.iSup_two_mul_foldedJensenNonrealCount
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.folded_exhaustion_dichotomy
