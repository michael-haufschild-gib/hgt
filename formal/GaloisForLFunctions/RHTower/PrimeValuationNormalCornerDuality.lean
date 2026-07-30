import GaloisForLFunctions.RHTower.PrimeSupportBoundaryJets
import GaloisForLFunctions.RHTower.HighExponentShellHypertranscendence
import GaloisForLFunctions.RHTower.XiTransverseGammaValuationCoherence
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.HTGeometry.GammaClockPacketCoronaCodimension
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Prime-valuation normal-corner duality

Largest prime-exponent depth and distinct-prime normal codimension are not merely two unrelated
integer statistics.  On every finite packet of distinct primes they are exact dual ranks.

The actual Gamma-normalized valuation coordinates form a rectangular weighted Vandermonde:

`H_e(p) = sqrt(p⁻¹) * (1 - p⁻¹) * p⁻ᵉ`.

The first `N` valuation rows reconstruct arbitrary amplitudes on every injective `N`-prime packet.
No packet map with fewer than `N` scalar valuation rows can be injective.  Since the Wold boundary
jet of order `N - 1` selects exactly support cardinality `N`, normal order plus one is the exact
minimal valuation tomography depth.

Gamma Schur elimination is already known to delete the first valuation row and translate this
same frame by one depth.  The all-prime Wold boundary is already known to make the reflected
irregular pair simultaneously moderate exactly on the critical line.  The capstone below joins
these facts on one source-normal corner without selecting or assuming any Xi zero.
-/

open Complex

namespace RHTower

noncomputable section

open Matrix Polynomial
open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- One coefficient cell of the joint largest-exponent/support-cardinality grid. -/
def primeValuationNormalIncidenceCell (m k n : ℕ) : ℤ :=
  if shellIndicator m n = 1 ∧ n.primeFactors.card = k then 1 else 0

@[simp]
theorem primeValuationNormalIncidenceCell_eq_one_iff (m k n : ℕ) :
    primeValuationNormalIncidenceCell m k n = 1 ↔
      shellIndicator m n = 1 ∧ n.primeFactors.card = k := by
  by_cases h : shellIndicator m n = 1 ∧ n.primeFactors.card = k
  · simp [primeValuationNormalIncidenceCell, h]
  · simp [primeValuationNormalIncidenceCell]

/-- Summing the normal-codimension cells recovers exactly the positive depth shell coefficient. -/
theorem sum_primeValuationNormalIncidenceCell_support
    (m n : ℕ) :
    ∑ k ∈ Finset.range (n.primeFactors.card + 1),
        primeValuationNormalIncidenceCell m k n =
      shellIndicator m n := by
  classical
  rcases shellIndicator_eq_zero_or_one m n with hzero | hone
  · have hzero' :
        mFreeIndicator (m + 1) n - mFreeIndicator m n = 0 := by
      simpa only [shellIndicator_apply] using hzero
    rw [hzero]
    simp [primeValuationNormalIncidenceCell, hzero']
  · have hone' :
        mFreeIndicator (m + 1) n - mFreeIndicator m n = 1 := by
      simpa only [shellIndicator_apply] using hone
    rw [hone]
    simp [primeValuationNormalIncidenceCell, hone']

/-- Summing a fixed support-codimension column over all possible positive valuation shells recovers
that support stratum exactly.  Together with the row marginal above, the bivariate cells are a
lossless partition of every integer `n ≥ 2`. -/
theorem sum_primeValuationNormalIncidenceCell_depth
    {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (k : ℕ) :
    ∑ m ∈ Finset.range (Ω n),
        primeValuationNormalIncidenceCell (m + 1) k n =
      if n.primeFactors.card = k then 1 else 0 := by
  classical
  by_cases hcard : n.primeFactors.card = k
  · rw [if_pos hcard]
    calc
      (∑ m ∈ Finset.range (Ω n),
          primeValuationNormalIncidenceCell (m + 1) k n) =
          ∑ m ∈ Finset.range (Ω n), shellIndicator (m + 1) n := by
            apply Finset.sum_congr rfl
            intro m hm
            rcases shellIndicator_eq_zero_or_one (m + 1) n with hzero | hone
            · simp [primeValuationNormalIncidenceCell, hzero]
            · simp [primeValuationNormalIncidenceCell, hone, hcard]
      _ = mFreeIndicator (Ω n + 1) n - mFreeIndicator 1 n :=
        sum_range_shellIndicator (Ω n) n
      _ = 1 := by
        rw [mFreeIndicator_apply, if_pos (mFree_cardFactors_succ hn0),
          mFreeIndicator_one]
        simp [hn1]
  · rw [if_neg hcard]
    apply Finset.sum_eq_zero
    intro m hm
    simp [primeValuationNormalIncidenceCell, hcard]

/-- The first `M` valuation-depth coordinates sampled on an `N`-prime normal packet. -/
def xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix
    (M : ℕ) {N : ℕ} (p : Fin N → Nat.Primes) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun e j => xiTransversePrimeHalfShiftedValuationCoordinate (p j) e

/-- At equal depth and support cardinality, the rectangular sampler is the existing square
Gamma--valuation sampling matrix. -/
theorem xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_self
    {N : ℕ} (p : Fin N → Nat.Primes) :
    xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N p =
      xiTransversePrimeHalfShiftedValuationSamplingMatrix p :=
  rfl

/-- `N` valuation rows reconstruct every injective `N`-prime normal packet. -/
theorem xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_mulVec_injective
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    Function.Injective
      (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N p).mulVec := by
  rw [xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_self,
    Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  exact xiTransversePrimeHalfShiftedValuationSamplingMatrix_det_ne_zero hp

/-- Fewer valuation rows than prime-normal directions can never be faithful.  This lower bound is
independent of the entries: it is the exact finite-dimensional obstruction behind normal
codimension. -/
theorem xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_not_injective_of_lt
    {M N : ℕ} (hMN : M < N) (p : Fin N → Nat.Primes) :
    ¬ Function.Injective
      (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M p).mulVec := by
  intro hinjective
  have hfinrank :=
    LinearMap.finrank_le_finrank_of_injective
      (f :=
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M p).mulVecLin)
      hinjective
  simp only [Module.finrank_pi, Fintype.card_fin] at hfinrank
  omega

/-- **Exact depth--codimension duality.**  For an injective `N`-prime packet, `N` is exactly the
least number of initial valuation rows that can reconstruct arbitrary normal amplitudes. -/
theorem xiTransversePrimeHalfShiftedValuation_exact_minimal_tomography
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N p).mulVec ∧
      ∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M p).mulVec := by
  exact
    ⟨xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_mulVec_injective hp,
      fun M hMN =>
        xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix_not_injective_of_lt
          hMN p⟩

/-! ## The reciprocal-prime recurrence spectrum -/

/-- Gamma valuation translation on a finite prime-normal packet.  Its diagonal entries are the
reciprocal-prime aperture nodes. -/
def xiTransversePrimeValuationTranslation
    {N : ℕ} (p : Fin N → Nat.Primes) :
    Module.End ℝ (Fin N → ℝ) :=
  Matrix.toLin'
    (Matrix.diagonal
      (fun j => xiTransversePrimeApertureDiskNode 1 (p j)))

/-- The depth-zero Gamma-normal valuation packet. -/
def xiTransversePrimeValuationVacuum
    {N : ℕ} (p : Fin N → Nat.Primes) : Fin N → ℝ :=
  fun j => xiTransversePrimeHalfShiftedValuationCoordinate (p j) 0

/-- The complete valuation tower is the orbit of the depth-zero packet under reciprocal-prime
Gamma translation. -/
theorem xiTransversePrimeValuationTranslation_orbit_eq_coordinate
    {N : ℕ} (p : Fin N → Nat.Primes) (e : ℕ) (j : Fin N) :
    ((xiTransversePrimeValuationTranslation p) ^ e)
        (xiTransversePrimeValuationVacuum p) j =
      xiTransversePrimeHalfShiftedValuationCoordinate (p j) e := by
  induction e with
  | zero =>
      simp [xiTransversePrimeValuationVacuum]
  | succ e ih =>
      rw [pow_succ', Module.End.mul_apply]
      change
        (Matrix.diagonal
          (fun j => xiTransversePrimeApertureDiskNode 1 (p j)) *ᵥ
            ((xiTransversePrimeValuationTranslation p) ^ e)
              (xiTransversePrimeValuationVacuum p)) j =
          xiTransversePrimeHalfShiftedValuationCoordinate (p j) (e + 1)
      rw [Matrix.mulVec_diagonal, ih,
        xiTransversePrimeHalfShiftedValuationCoordinate_succ]

/-- **Reciprocal-prime spectral law.**  On an injective finite prime packet, the minimal
polynomial of Gamma valuation translation equals its characteristic polynomial and factors into
the distinct reciprocal-prime modes. -/
theorem xiTransversePrimeValuationTranslation_minpoly_eq_charpoly
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    minpoly ℝ (xiTransversePrimeValuationTranslation p) =
      (Matrix.diagonal
        (fun j => xiTransversePrimeApertureDiskNode 1 (p j))).charpoly := by
  let q : Fin N → ℝ :=
    fun j => xiTransversePrimeApertureDiskNode 1 (p j)
  let T : Module.End ℝ (Fin N → ℝ) :=
    Matrix.toLin' (Matrix.diagonal q)
  have hq : Function.Injective q :=
    xiTransversePrimeApertureDiskNode_one_injective.comp hp
  have hminne : minpoly ℝ T ≠ 0 :=
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  have hroot (j : Fin N) : (minpoly ℝ T).IsRoot (q j) := by
    apply Module.End.isRoot_of_hasEigenvalue
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (hasEigenvector_toLin'_diagonal q j)
  have hsubset :
      Finset.image q Finset.univ ⊆ (minpoly ℝ T).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hminne]
    exact hroot j
  have hN_le_roots : N ≤ (minpoly ℝ T).roots.card := by
    calc
      N = (Finset.image q Finset.univ).card := by
        rw [Finset.card_image_of_injective _ hq, Finset.card_univ,
          Fintype.card_fin]
      _ ≤ (minpoly ℝ T).roots.toFinset.card :=
        Finset.card_le_card hsubset
      _ ≤ (minpoly ℝ T).roots.card :=
        Multiset.toFinset_card_le _
  have hroots_le :
      (minpoly ℝ T).roots.card ≤ (minpoly ℝ T).natDegree :=
    Polynomial.card_roots' _
  have hdvd : minpoly ℝ T ∣ T.charpoly :=
    LinearMap.minpoly_dvd_charpoly T
  have hcharDegree : T.charpoly.natDegree = N := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      LinearMap.charpoly_natDegree T
  have hmin_le : (minpoly ℝ T).natDegree ≤ N := by
    have hle := Polynomial.natDegree_le_of_dvd
      hdvd (LinearMap.charpoly_monic T).ne_zero
    omega
  have hminDegree : (minpoly ℝ T).natDegree = N := by omega
  have hEq : T.charpoly = minpoly ℝ T :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral T))
      (LinearMap.charpoly_monic T) hdvd (by omega)
  simpa [xiTransversePrimeValuationTranslation, T, q] using hEq.symm

/-- The reciprocal-prime factorization of the exact recurrence polynomial. -/
theorem xiTransversePrimeValuationTranslation_minpoly_eq_primeProduct
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    minpoly ℝ (xiTransversePrimeValuationTranslation p) =
      ∏ j, (Polynomial.X -
        Polynomial.C (xiTransversePrimeApertureDiskNode 1 (p j))) := by
  rw [xiTransversePrimeValuationTranslation_minpoly_eq_charpoly hp,
    Matrix.charpoly_diagonal]

/-- The prime-normal recurrence order is exactly the packet support cardinality. -/
theorem xiTransversePrimeValuationTranslation_minpoly_natDegree
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    (minpoly ℝ (xiTransversePrimeValuationTranslation p)).natDegree = N := by
  rw [xiTransversePrimeValuationTranslation_minpoly_eq_charpoly hp,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- **Exact recurrence-order law.**  Every nonzero polynomial annihilating Gamma valuation
translation on an injective `N`-prime normal packet has degree at least `N`.  The characteristic
polynomial attains that bound, so support cardinality is exactly the recurrence order. -/
theorem xiTransversePrimeValuationTranslation_annihilator_degree_lower_bound
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p)
    (Q : ℝ[X])
    (hQ : aeval (xiTransversePrimeValuationTranslation p) Q = 0) :
    Q = 0 ∨ N ≤ Q.natDegree := by
  by_cases hzero : Q = 0
  · exact Or.inl hzero
  right
  have hdvd : minpoly ℝ (xiTransversePrimeValuationTranslation p) ∣ Q :=
    minpoly.dvd ℝ (xiTransversePrimeValuationTranslation p) hQ
  have hle := Polynomial.natDegree_le_of_dvd hdvd hzero
  rw [xiTransversePrimeValuationTranslation_minpoly_eq_charpoly hp,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hle
  exact hle

/-- The Wold support stratum selected at normal order `N - 1` is exactly the stratum whose
prime-normal amplitudes require `N` valuation rows for lossless reconstruction. -/
theorem primeSupportNormalOrder_valuationDepth_duality
    {N : ℕ} (hN : 0 < N) {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    (∀ k : ℕ,
        ((derivative^[N - 1])
          (GaloisForLFunctions.RHTower.primeSupportMarkedDeformation k)).eval 1 =
          if k = N then
            (k : ℤ) * (-1 : ℤ) ^ (N - 1) * ((N - 1).factorial : ℤ)
          else 0) ∧
      Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N p).mulVec ∧
      ∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M p).mulVec := by
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hN
  refine ⟨?_, xiTransversePrimeHalfShiftedValuation_exact_minimal_tomography hp⟩
  intro k
  simpa only [hsucc] using
    (GaloisForLFunctions.RHTower.primeSupportMarkedDeformation_boundaryJet k (N - 1))

/-- **Triple rank identity.**  Prime-normal support cardinality `N` is simultaneously the Gamma
corona conormal rank and the exact minimal valuation tomography depth. -/
theorem primeNormalCodimension_eq_coronaRank_eq_minimalValuationDepth
    {N : ℕ} {p : Fin N → Nat.Primes} (hp : Function.Injective p) :
    Module.finrank ℝ
        (LinearMap.ker
          (GaloisForLFunctions.HTGeometry.packetStreamCoronaConstraint ℝ (Fin N))) = N ∧
      Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N p).mulVec ∧
      ∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M p).mulVec := by
  exact
    ⟨GaloisForLFunctions.HTGeometry.finrank_ker_finPacketStreamCoronaConstraint ℝ N,
      xiTransversePrimeHalfShiftedValuation_exact_minimal_tomography hp⟩

/-- **Prime-valuation normal-corner law.**  Normal order, minimal valuation tomography, Gamma
translation, Gamma Schur residual, and the cofinal Wold critical-line selector are five exact
projections of one source-normal corner.

No divisor point is selected.  In particular, the theorem does not assert that a Xi zero belongs
to the bi-moderate locus. -/
theorem primeValuationNormalCorner_law
    {N : ℕ} (hN : 0 < N) {packet : Fin N → Nat.Primes}
    (hpacket : Function.Injective packet) :
    (∀ k : ℕ,
        ((derivative^[N - 1])
          (GaloisForLFunctions.RHTower.primeSupportMarkedDeformation k)).eval 1 =
          if k = N then
            (k : ℤ) * (-1 : ℤ) ^ (N - 1) * ((N - 1).factorial : ℤ)
          else 0) ∧
      Module.finrank ℝ
        (LinearMap.ker
          (GaloisForLFunctions.HTGeometry.packetStreamCoronaConstraint ℝ (Fin N))) = N ∧
      Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N packet).mulVec ∧
      (∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M packet).mulVec) ∧
      (∀ (p : Nat.Primes) (e : ℕ),
        xiTransversePrimeHalfShiftedValuationCoordinate p (e + 1) =
          xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeHalfShiftedValuationCoordinate p e) ∧
      (∀ p q : Nat.Primes,
        xiTransverseGammaValuationSzegoKernel p q -
            (gammaValuationHardyRenormalizer p *
                gammaConductorPrimeNormalizedCross p) *
              (gammaValuationHardyRenormalizer q *
                gammaConductorPrimeNormalizedCross q) / (9 / 8 : ℝ) =
          xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeApertureDiskNode 1 q *
              xiTransverseGammaValuationSzegoKernel p q) ∧
      (∀ s : ℂ,
        GaloisForLFunctions.reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary
            (s - (1 / 2 : ℂ)) ↔
          s.re = 1 / 2) := by
  obtain ⟨hjet, htomo, hminimal⟩ :=
    primeSupportNormalOrder_valuationDepth_duality hN hpacket
  exact
    ⟨hjet,
      GaloisForLFunctions.HTGeometry.finrank_ker_finPacketStreamCoronaConstraint ℝ N,
      htomo, hminimal,
      xiTransversePrimeHalfShiftedValuationCoordinate_succ,
      xiTransverseGammaValuationSzegoKernel_schurResidual_eq_shift,
      GaloisForLFunctions.centeredReflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary_iff⟩

/-- **Prime-normal recurrence correspondence.**  The same integer `N` is:

* successor of the Wold normal-jet order selecting the support stratum;
* rank of the finite-blind Gamma-corona conormal;
* degree of the reciprocal-prime Gamma-translation minimal polynomial;
* least valuation-tomography depth.

The exact recurrence polynomial records the prime identities through its distinct roots.  Gamma
Schur elimination advances the resulting orbit by one depth, while the cofinal reflected Wold
boundary is bi-moderate exactly on the critical line. -/
theorem primeNormalRecurrenceCorrespondence_law
    {N : ℕ} (hN : 0 < N) {packet : Fin N → Nat.Primes}
    (hpacket : Function.Injective packet) :
    (∀ k : ℕ,
        ((derivative^[N - 1])
          (GaloisForLFunctions.RHTower.primeSupportMarkedDeformation k)).eval 1 =
          if k = N then
            (k : ℤ) * (-1 : ℤ) ^ (N - 1) * ((N - 1).factorial : ℤ)
          else 0) ∧
      Module.finrank ℝ
        (LinearMap.ker
          (GaloisForLFunctions.HTGeometry.packetStreamCoronaConstraint ℝ (Fin N))) = N ∧
      minpoly ℝ (xiTransversePrimeValuationTranslation packet) =
        ∏ j, (Polynomial.X -
          Polynomial.C (xiTransversePrimeApertureDiskNode 1 (packet j))) ∧
      (minpoly ℝ
        (xiTransversePrimeValuationTranslation packet)).natDegree = N ∧
      Function.Injective
        (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix N packet).mulVec ∧
      (∀ M : ℕ, M < N →
        ¬ Function.Injective
          (xiTransversePrimeHalfShiftedValuationRectangularSamplingMatrix M packet).mulVec) ∧
      (∀ (p : Nat.Primes) (e : ℕ),
        xiTransversePrimeHalfShiftedValuationCoordinate p (e + 1) =
          xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeHalfShiftedValuationCoordinate p e) ∧
      (∀ p q : Nat.Primes,
        xiTransverseGammaValuationSzegoKernel p q -
            (gammaValuationHardyRenormalizer p *
                gammaConductorPrimeNormalizedCross p) *
              (gammaValuationHardyRenormalizer q *
                gammaConductorPrimeNormalizedCross q) / (9 / 8 : ℝ) =
          xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeApertureDiskNode 1 q *
              xiTransverseGammaValuationSzegoKernel p q) ∧
      (∀ s : ℂ,
        GaloisForLFunctions.reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary
            (s - (1 / 2 : ℂ)) ↔
          s.re = 1 / 2) := by
  obtain ⟨hjet, hcorona, htomo, hminimal, hshift, hschur, hcritical⟩ :=
    primeValuationNormalCorner_law hN hpacket
  exact
    ⟨hjet, hcorona,
      xiTransversePrimeValuationTranslation_minpoly_eq_primeProduct hpacket,
      xiTransversePrimeValuationTranslation_minpoly_natDegree hpacket,
      htomo, hminimal, hshift, hschur, hcritical⟩

end

end RHTower
