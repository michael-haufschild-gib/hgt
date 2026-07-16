import GaloisForLFunctions.HTGeometry.DiscreteMomentHankel
import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank
import GaloisForLFunctions.HTGeometry.FiniteStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.LinearRecurrenceStateSpace
import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue

/-!
# Shifted equilibrium polygamma jets as infinite positive spectral clocks

The positive-order digamma derivatives at every real `a > 0` are not merely isolated Hurwitz-zeta
values.  After removing their alternating factorial scale, the complete jet is the moment sequence
of the reciprocal shifted-energy ladder

`E_j = j + a`, `x_j = E_j⁻¹`, `w_j = E_j⁻²`.

Thus the normalized observable jet is `sum_j w_j x_j^m = ζ(m+2,a)`.  The spectral support is
infinite and every weight is positive, so every finite Hankel block is positive definite and has
positive determinant.  Consequently no uniformly bounded finite spectral palette, finite linear
state-space model, or positive-order linear recurrence can reproduce the all-order equilibrium
jet.  The positive content is the exact infinite-support spectral representation; the finite-model
obstructions are its consequences.

The observation label `m` is derivative order, not temporal evolution.  In quantum-statistical
language the same discrete Hamiltonian spectrum determines the heat trace and partition function;
here its reciprocal spectral moments are being reported by the Gamma/digamma observable.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- Reciprocal energy of the `j`-th level of the unit-spaced ladder shifted by `a`. -/
def gammaBoseNode (a : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) + a)⁻¹

/-- Positive reciprocal-square spectral weight used by the normalized polygamma jet. -/
def gammaBoseWeight (a : ℝ) (j : ℕ) : ℝ :=
  gammaBoseNode a j ^ 2

/-- The reciprocal-energy spectral moment of order `m`. -/
def gammaBoseMoment (a : ℝ) (m : ℕ) : ℝ :=
  ∑' j : ℕ, gammaBoseWeight a j * gammaBoseNode a j ^ m

/-- The reciprocal-energy moment is exactly the Hurwitz-zeta value `ζ(m+2,a)`. -/
theorem gammaBoseMoment_ofReal_eq_hzeta (a : ℝ) (m : ℕ) :
    (gammaBoseMoment a m : ℂ) =
      HurwitzZetaShift.hzeta ((m + 2 : ℕ) : ℂ) (a : ℂ) := by
  rw [gammaBoseMoment, Complex.ofReal_tsum, HurwitzZetaShift.hzeta]
  apply tsum_congr
  intro j
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  simp only [Complex.ofReal_pow, Complex.ofReal_inv,
    gammaBoseWeight, gammaBoseNode]
  rw [← inv_pow, ← pow_add]
  congr 1
  · push_cast
    rfl
  · omega

/-- At shift `a=1`, the reciprocal-energy moment specializes to `ζ(m+2)`. -/
theorem gammaBoseMoment_one_ofReal_eq_riemannZeta (m : ℕ) :
    (gammaBoseMoment 1 m : ℂ) =
      riemannZeta ((m + 2 : ℕ) : ℂ) := by
  rw [gammaBoseMoment_ofReal_eq_hzeta,
    GaloisForLFunctions.hzeta_one_eq_riemannZeta (by
      rw [Complex.natCast_re]
      exact_mod_cast (show 1 < m + 2 by omega))]

/-- Exact value relation between the digamma jet at equilibrium and the positive spectral
moment: `ψ⁽ᵐ⁺¹⁾(a)=(-1)^(m+2)(m+1)!·M_m(a)`. -/
theorem iteratedDeriv_digamma_eq_gammaBoseMoment
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    iteratedDeriv (m + 1) Complex.digamma (a : ℂ) =
      (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) *
        (gammaBoseMoment a m : ℂ) := by
  rw [GaloisForLFunctions.polygamma_eq_hzeta m (by simpa using ha),
    gammaBoseMoment_ofReal_eq_hzeta]

/-- The real equilibrium susceptibility after removing the alternating factorial scale. -/
def signedNormalizedDigammaJet (a : ℝ) (m : ℕ) : ℝ :=
  (((-1 : ℂ) ^ (m + 2) * iteratedDeriv (m + 1) Complex.digamma (a : ℂ)) /
    ((m + 1).factorial : ℂ)).re

/-- The signed normalized digamma jet is exactly the positive reciprocal-energy moment clock. -/
theorem signedNormalizedDigammaJet_eq_gammaBoseMoment
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    signedNormalizedDigammaJet a m = gammaBoseMoment a m := by
  rw [signedNormalizedDigammaJet,
    iteratedDeriv_digamma_eq_gammaBoseMoment ha]
  have hfac : ((m + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  field_simp
  rw [← pow_mul, show (m + 2) * 2 = 2 * (m + 2) by omega, pow_mul]
  norm_num

/-- Every reciprocal-square ladder weight is nonnegative. -/
theorem gammaBoseWeight_nonneg (a : ℝ) (j : ℕ) :
    0 ≤ gammaBoseWeight a j := by
  dsimp [gammaBoseWeight, gammaBoseNode]
  exact sq_nonneg _

/-- Positive shift makes every reciprocal-square ladder weight strictly positive. -/
theorem gammaBoseWeight_pos {a : ℝ} (ha : 0 < a) (j : ℕ) :
    0 < gammaBoseWeight a j := by
  dsimp [gammaBoseWeight, gammaBoseNode]
  exact pow_pos (by positivity) _

/-- Every absolute spectral moment of the reciprocal-energy ladder is summable. -/
theorem summable_gammaBoseWeight_mul_node_abs_pow
    {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Summable (fun j : ℕ ↦
      gammaBoseWeight a j * |gammaBoseNode a j| ^ m) := by
  have hs := (Real.summable_one_div_nat_add_rpow a (m + 2)).mpr (by
    exact_mod_cast (show 1 < m + 2 by omega))
  refine hs.congr ?_
  intro j
  have hexp : (m : ℝ) + 2 = ((m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_natCast]
  rw [abs_of_pos (by positivity : 0 < (j : ℝ) + a)]
  dsimp [gammaBoseWeight, gammaBoseNode]
  rw [abs_of_pos (by positivity : 0 < ((j : ℝ) + a)⁻¹)]
  simp only [one_div]
  rw [← inv_pow, ← pow_add]
  congr 1
  omega

/-- Distinct ladder energies give distinct reciprocal-energy nodes. -/
theorem gammaBoseNode_injective (a : ℝ) :
    Function.Injective (gammaBoseNode a) := by
  intro j k hjk
  have hcast : (j : ℝ) + a = (k : ℝ) + a := by
    apply inv_injective
    exact hjk
  exact_mod_cast (by linarith : (j : ℝ) = k)

/-- The positive reciprocal-energy spectrum escapes every finite set of reported values. -/
theorem gammaBose_infiniteSupport
    {a : ℝ} (ha : 0 < a) (F : Finset ℝ) :
    ∃ j : ℕ, gammaBoseNode a j ∉ F ∧ 0 < gammaBoseWeight a j := by
  have hrange : (Set.range (gammaBoseNode a)).Infinite :=
    Set.infinite_range_of_injective (gammaBoseNode_injective a)
  have hex : ∃ j : ℕ, gammaBoseNode a j ∉ F := by
    by_contra h
    apply hrange
    apply F.finite_toSet.subset
    rintro _ ⟨j, rfl⟩
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, gammaBoseWeight_pos ha j⟩

/-- Every finite Hankel block of the Gamma/Bose spectral moment clock is positive definite. -/
theorem gammaBoseHankel_posDef
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (momentHankelMatrix (gammaBoseMoment a) n).PosDef := by
  exact discreteMomentHankel_posDef (gammaBoseWeight a) (gammaBoseNode a)
    (gammaBoseWeight_nonneg a)
    (summable_gammaBoseWeight_mul_node_abs_pow ha)
    (gammaBose_infiniteSupport ha) n

/-- Every finite Hankel determinant of the Gamma/Bose spectral moment clock is positive. -/
theorem det_gammaBoseHankel_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < (momentHankelMatrix (gammaBoseMoment a) n).det :=
  (gammaBoseHankel_posDef ha n).det_pos

/-- Every finite Hankel block of the actual signed normalized digamma jet is positive definite. -/
theorem signedNormalizedDigammaJet_hankel_posDef
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (momentHankelMatrix (signedNormalizedDigammaJet a) n).PosDef := by
  simpa only [signedNormalizedDigammaJet_eq_gammaBoseMoment ha] using
    gammaBoseHankel_posDef ha n

/-- Every finite Hankel determinant of the actual signed normalized digamma jet is positive. -/
theorem det_signedNormalizedDigammaJet_hankel_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < (momentHankelMatrix (signedNormalizedDigammaJet a) n).det :=
  (signedNormalizedDigammaJet_hankel_posDef ha n).det_pos

/-- No fixed finite spectral width can reproduce arbitrarily long normalized digamma-jet
windows, even if the approximating spectrum changes with the window. -/
theorem signedNormalizedDigammaJet_not_fixedSpectralWidthLocalClosure
    {a : ℝ} (ha : 0 < a) (d : ℕ) :
    ¬ FixedSpectralWidthLocalClosure d (signedNormalizedDigammaJet a) := by
  apply not_fixedSpectralWidthLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_signedNormalizedDigammaJet_hankel_pos ha (d + 1))

/-- No fixed-dimensional linear hidden-state model can reproduce arbitrarily long normalized
digamma-jet windows. -/
theorem signedNormalizedDigammaJet_not_fixedStateSpaceDimensionLocalClosure
    {a : ℝ} (ha : 0 < a) (d : ℕ) :
    ¬ FixedStateSpaceDimensionLocalClosure d (signedNormalizedDigammaJet a) := by
  apply not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero
  exact ne_of_gt (det_signedNormalizedDigammaJet_hankel_pos ha (d + 1))

/-- The normalized equilibrium digamma jet satisfies no positive-order linear recurrence. -/
theorem signedNormalizedDigammaJet_not_linearRecurrence
    {a : ℝ} (ha : 0 < a)
    (E : LinearRecurrence ℝ) (horder : E.order ≠ 0) :
    ¬ E.IsSolution (signedNormalizedDigammaJet a) := by
  intro hsolution
  have hzero := det_algebraicHankelMatrix_succ_eq_zero_of_linearRecurrence
    E hsolution horder
  exact (ne_of_gt
    (det_signedNormalizedDigammaJet_hankel_pos ha (E.order + 1))) (by
      simpa [algebraicHankelMatrix, momentHankelMatrix] using hzero)

end

end HTGeometry
