import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesSeeReducedCriticalJets

/-!
# Real square positivity depends only on the Hermitian part of a degree

Every actual complex-linear degree splits uniquely into two Hermitian degrees.
Its real sharp-square reading is exactly the square reading of the first part.
Thus the finite critical-value classification applies without assuming that the
original complex degree itself is Hermitian.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Conjugation of a degree by the actual arithmetic involution is again complex-linear. -/
def meyerDegreeConjugate (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ where
  toFun u := conj (d (meyerCohomologySharp u))
  map_add' u v := by rw [map_add, map_add, map_add]
  map_smul' c u := by
    rw [LinearMap.map_smulₛₗ, map_smul]
    simp only [smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply]

/-- The Hermitian part controlling the real intersection reading. -/
def meyerDegreeHermitianPart (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  (1 / 2 : ℂ) • (d + meyerDegreeConjugate d)

/-- The second Hermitian degree records the imaginary reading. -/
def meyerDegreeImaginaryPart (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ := meyerDegreeHermitianPart (-I • d)

theorem meyerDegreeHermitianPart_hermitian
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreeHermitianPart d (meyerCohomologySharp u) =
      conj (meyerDegreeHermitianPart d u) := by
  change (1 / 2 : ℂ) * (d (meyerCohomologySharp u) +
      conj (d (meyerCohomologySharp (meyerCohomologySharp u)))) =
    conj ((1 / 2 : ℂ) * (d u + conj (d (meyerCohomologySharp u))))
  rw [meyerCohomologySharp_sq, map_mul, map_add, Complex.conj_conj,
    show conj (1 / 2 : ℂ) = 1 / 2 by norm_num]
  ring

theorem meyerDegreeImaginaryPart_hermitian
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreeImaginaryPart d (meyerCohomologySharp u) =
      conj (meyerDegreeImaginaryPart d u) :=
  meyerDegreeHermitianPart_hermitian (-I • d) u

/-- Every complex degree splits into its two actual Hermitian readings. -/
theorem meyerDegree_hermitian_decomposition
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    d = meyerDegreeHermitianPart d + I • meyerDegreeImaginaryPart d := by
  apply LinearMap.ext
  intro u
  change d u = (1 / 2 : ℂ) * (d u + conj (d (meyerCohomologySharp u))) +
    I * ((1 / 2 : ℂ) * (-I * d u + conj (-I * d (meyerCohomologySharp u))))
  rw [map_mul, map_neg, Complex.conj_I]
  ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- The Hermitian decomposition is unique. -/
theorem meyerDegree_hermitian_decomposition_unique
    (d h k : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hh : ∀ u, h (meyerCohomologySharp u) = conj (h u))
    (hk : ∀ u, k (meyerCohomologySharp u) = conj (k u))
    (he : d = h + I • k) :
    meyerDegreeHermitianPart d = h ∧ meyerDegreeImaginaryPart d = k := by
  have hhpart : meyerDegreeHermitianPart d = h := by
    apply LinearMap.ext
    intro u
    rw [he]
    change (1 / 2 : ℂ) *
      (h u + I * k u + conj (h (meyerCohomologySharp u) + I * k (meyerCohomologySharp u))) = h u
    rw [hh, hk, map_add, map_mul, Complex.conj_conj, Complex.conj_conj, Complex.conj_I]
    ring
  refine ⟨hhpart, ?_⟩
  have hsplit := meyerDegree_hermitian_decomposition d
  rw [hhpart] at hsplit
  have hs : I • k = I • meyerDegreeImaginaryPart d := add_left_cancel (he.symm.trans hsplit)
  apply LinearMap.ext
  intro u
  have hv := congrArg (fun L : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ => L u) hs
  exact (mul_left_cancel₀ I_ne_zero hv).symm

private theorem meyer_sharp_square_fixed (u : DeningerMeyerStrongLogCohomology) :
    meyerCohomologySharp (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u)) =
      deningerMeyerCohomologyConvolution u (meyerCohomologySharp u) := by
  rw [meyerCohomologySharp_convolution, meyerCohomologySharp_sq,
    deningerMeyerCohomologyConvolution_comm]

/-- Hermitian projection converts every square reading into its exact real part. -/
theorem meyerDegreeHermitianPart_square
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair (meyerDegreeHermitianPart d) u u = ((meyerDegreePair d u u).re : ℂ) := by
  change (1 / 2 : ℂ) *
    (meyerDegreePair d u u + conj (d (meyerCohomologySharp
      (deningerMeyerCohomologyConvolution u (meyerCohomologySharp u))))) = _
  rw [meyer_sharp_square_fixed]
  change (1 / 2 : ℂ) * (meyerDegreePair d u u + conj (meyerDegreePair d u u)) = _
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

/-- The second Hermitian component reads the exact imaginary part of every square. -/
theorem meyerDegreeImaginaryPart_square
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) :
    meyerDegreePair (meyerDegreeImaginaryPart d) u u = ((meyerDegreePair d u u).im : ℂ) := by
  rw [meyerDegreeImaginaryPart, meyerDegreeHermitianPart_square]
  change ((-I * meyerDegreePair d u u).re : ℂ) = _
  congr 1
  norm_num [Complex.mul_re]

/-- Real square positivity makes no demand on the anti-Hermitian part. -/
theorem meyerDegree_real_positive_iff_hermitianPart_positive
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    (∀ u, 0 ≤ (meyerDegreePair d u u).re) ↔
      ∀ u, 0 ≤ (meyerDegreePair (meyerDegreeHermitianPart d) u u).re := by
  simp only [meyerDegreeHermitianPart_square, Complex.ofReal_re]

/-- Every real-positive degree has the exact critical-value Hermitian restriction on finite packets. -/
theorem meyerRealPositiveDegree_finite_causal_hermitian_formula
    (d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (hpos : ∀ u, 0 ≤ (meyerDegreePair d u u).re)
    (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) :
    meyerDegreeHermitianPart d (deningerMeyerFiniteXiCausalSection S c) =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        if meyerLineReflect q.1.1 = q.1.1 ∧ q.2.val = 0 then
          c q * ((meyerDegreeHermitianPart d (meyerHasseJetClass q.1.1 q.2)).re : ℂ) else 0 :=
  meyerPositiveDegree_finite_causal_formula (meyerDegreeHermitianPart d)
    (meyerDegreeHermitianPart_hermitian d)
    ((meyerDegree_real_positive_iff_hermitianPart_positive d).mp hpos) S c

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeHermitianPart_hermitian
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeImaginaryPart_hermitian
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegree_hermitian_decomposition
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegree_hermitian_decomposition_unique
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeHermitianPart_square
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeImaginaryPart_square
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegree_real_positive_iff_hermitianPart_positive
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerRealPositiveDegree_finite_causal_hermitian_formula
