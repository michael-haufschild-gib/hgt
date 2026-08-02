import GaloisForLFunctions.RHTower.HellingerBetaCovariantCofaceTransgression
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalSourceToXiLanding

/-!
# Hellinger--Beta coface on the physical Möbius--theta exponent chain

Using the already proved identification of the direct prime-normal rung with the target-free
`mPart` rung, the Hellinger--Beta covariant coface acts on the actual physical Möbius--theta
exponent chain.  After normalization it is exactly the adjacent physical difference, its finite
codiagonal telescopes, and its partial sums converge strongly to the canonical theta source.  The
Fourier image of a normalized coface is the adjacent reciprocal-zeta multiplier difference times
Xi.

This is a source-side cofinal coface and Xi transport theorem.  It does not assert convergence in
the unbounded Calderón--Witt Gamma/Hardy graph norm or labelled incidence landing.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Filter Topology
open scoped BigOperators LSeries.notation Moebius FourierTransform SchwartzMap

noncomputable section
namespace RHTower
/-- Hellinger--Beta gauge applied before taking the exponent codiagonal. -/
def hellingerBetaMobiusThetaGaugedRung (m : ℕ) : MobiusThetaSourceL2 :=
  hellingerHodgeBetaColumnComplex (m : ℂ) • mobiusThetaDirectPhysicalRung m

/-- Source-forced Hellinger--Beta covariant coface on adjacent physical exponent grades. -/
def hellingerBetaMobiusThetaCovariantCoface (m : ℕ) : MobiusThetaSourceL2 :=
  hellingerBetaMobiusThetaGaugedRung (m + 1) -
    ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) •
      hellingerBetaMobiusThetaGaugedRung m

/-- The covariant coface factors as shifted Hellinger gauge times physical adjacent difference. -/
theorem hellingerBetaMobiusThetaCovariantCoface_eq (m : ℕ) :
    hellingerBetaMobiusThetaCovariantCoface m =
      hellingerHodgeBetaColumnComplex (((m + 1 : ℕ) : ℝ) : ℂ) •
        (mobiusThetaDirectPhysicalRung (m + 1) -
          mobiusThetaDirectPhysicalRung m) := by
  have hrec := hellingerHodgeBetaColumnComplex_real_add_one
    (a := (m : ℝ))
      (lt_of_lt_of_le (by norm_num : -(1 / 2 : ℝ) < 0) (Nat.cast_nonneg m))
  unfold hellingerBetaMobiusThetaCovariantCoface
    hellingerBetaMobiusThetaGaugedRung
  have hrec' :
      hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) =
        ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) *
          hellingerHodgeBetaColumnComplex (m : ℂ) := by
    convert hrec using 1 <;> norm_num
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show ((((m : ℝ) + 1 : ℝ) : ℂ)) = (m : ℂ) + 1 by norm_num]
  change
    hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) •
          mobiusThetaDirectPhysicalRung (m + 1) -
        ((((m : ℝ) + 1 / 2) / ((m : ℝ) + 2) : ℝ) : ℂ) •
          (hellingerHodgeBetaColumnComplex (m : ℂ) •
            mobiusThetaDirectPhysicalRung m) =
      hellingerHodgeBetaColumnComplex ((m : ℂ) + 1) •
        (mobiusThetaDirectPhysicalRung (m + 1) -
          mobiusThetaDirectPhysicalRung m)
  rw [hrec']
  module

/-- Normalizing by the nonzero real Hellinger gauge recovers the physical adjacent difference. -/
theorem hellingerBetaMobiusThetaCovariantCoface_normalized (m : ℕ) :
    (hellingerHodgeBetaColumnComplex (((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ •
        hellingerBetaMobiusThetaCovariantCoface m =
      mobiusThetaDirectPhysicalRung (m + 1) -
        mobiusThetaDirectPhysicalRung m := by
  rw [hellingerBetaMobiusThetaCovariantCoface_eq]
  rw [inv_smul_smul₀]
  exact hellingerHodgeBetaColumnComplex_real_ne_zero
    (a := ((m + 1 : ℕ) : ℝ))
      (lt_of_lt_of_le (by norm_num : -(1 / 2 : ℝ) < 0)
        (Nat.cast_nonneg (m + 1)))

/-- Completed physical coface based at grade `K`; grade zero retains the base rung and positive
grades are normalized covariant boundaries. -/
def hellingerBetaMobiusThetaCompletePhysicalCoface
    (K : ℕ) : ℕ → MobiusThetaSourceL2
  | 0 => mobiusThetaDirectPhysicalRung K
  | j + 1 =>
      (hellingerHodgeBetaColumnComplex
        (((K + j + 1 : ℕ) : ℝ) : ℂ))⁻¹ •
          hellingerBetaMobiusThetaCovariantCoface (K + j)

/-- The source-forced Hellinger coface is exactly the existing complete physical codiagonal. -/
theorem hellingerBetaMobiusThetaCompletePhysicalCoface_eq
    (K j : ℕ) :
    hellingerBetaMobiusThetaCompletePhysicalCoface K j =
      mobiusThetaCompletePhysicalChannel K j := by
  cases j with
  | zero => rfl
  | succ j =>
      simp only [hellingerBetaMobiusThetaCompletePhysicalCoface,
        mobiusThetaCompletePhysicalChannel]
      simpa [Nat.add_assoc] using
        hellingerBetaMobiusThetaCovariantCoface_normalized (K + j)

/-- Every finite Hellinger--Beta boundary telescope is its terminal direct physical rung. -/
theorem sum_range_hellingerBetaMobiusThetaCompletePhysicalCoface
    (K N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
        hellingerBetaMobiusThetaCompletePhysicalCoface K j =
      mobiusThetaDirectPhysicalRung (K + N) := by
  rw [show (fun j => hellingerBetaMobiusThetaCompletePhysicalCoface K j) =
      mobiusThetaCompletePhysicalChannel K by
    funext j
    exact hellingerBetaMobiusThetaCompletePhysicalCoface_eq K j]
  exact sum_range_mobiusThetaCompletePhysicalChannel K N

/-- **Cofinal physical source landing.**  Finite normalized Hellinger--Beta boundaries converge
strongly to the canonical theta source. -/
theorem tendsto_sum_range_hellingerBetaMobiusThetaCompletePhysicalCoface
    (K : ℕ) :
    Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range (N + 1),
        hellingerBetaMobiusThetaCompletePhysicalCoface K j)
      atTop (nhds xiThetaSourceL2) := by
  convert tendsto_sum_range_mobiusThetaCompletePhysicalChannel K using 1
  funext N
  apply Finset.sum_congr rfl
  intro j hj
  exact hellingerBetaMobiusThetaCompletePhysicalCoface_eq K j

/-- Fourier transform carries the cofinal physical source landing strongly to the displayed Xi
`L²` profile. -/
theorem tendsto_fourier_sum_range_hellingerBetaMobiusThetaCompletePhysicalCoface
    (K : ℕ) :
    Tendsto
      (fun N : ℕ => 𝓕 (∑ j ∈ Finset.range (N + 1),
        hellingerBetaMobiusThetaCompletePhysicalCoface K j))
      atTop (nhds xiThetaFourierSourceL2) := by
  have h := ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto
    xiThetaSourceL2).comp
      (tendsto_sum_range_hellingerBetaMobiusThetaCompletePhysicalCoface K)
  rw [← fourier_xiThetaSourceL2]
  exact h

/-- Spectral boundary of one normalized physical Hellinger--Beta coface.  It is the adjacent
reciprocal-zeta multiplier difference times Xi, derived after physical source construction. -/
theorem fourier_hellingerBetaMobiusThetaCovariantCoface_normalized_ae
    {m : ℕ} (hm : 3 ≤ m) :
    ((𝓕 ((hellingerHodgeBetaColumnComplex
        (((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ •
          hellingerBetaMobiusThetaCovariantCoface m) :
          MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
      fun t : ℝ =>
        ((riemannZeta (((m + 1 : ℕ) : ℂ) *
            ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹ -
          (riemannZeta ((m : ℂ) *
            ((1 / 2 : ℂ) + (t : ℂ) * I)))⁻¹) * XiC (t : ℂ) := by
  rw [hellingerBetaMobiusThetaCovariantCoface_normalized]
  change
    ((((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
      (mobiusThetaDirectPhysicalRung (m + 1) -
        mobiusThetaDirectPhysicalRung m) : MobiusThetaSourceL2)) : ℝ → ℂ) =ᵐ[volume] _
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (mobiusThetaDirectPhysicalRung (m + 1)))
      ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        (mobiusThetaDirectPhysicalRung m)),
    fourier_mobiusThetaPrimeNormalPhysicalRung_ae (show 3 ≤ m + 1 by omega),
    fourier_mobiusThetaPrimeNormalPhysicalRung_ae hm] with t hsub hnext hm
  calc
    _ = ((((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
            (mobiusThetaDirectPhysicalRung (m + 1)) : MobiusThetaSourceL2) :
          ℝ → ℂ) t) -
        ((((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
            (mobiusThetaDirectPhysicalRung m) : MobiusThetaSourceL2) :
          ℝ → ℂ) t) := by
      rw [hsub, Pi.sub_apply]
    _ = _ := by
      change
        (((𝓕 (mobiusThetaDirectPhysicalRung (m + 1)) : MobiusThetaSourceL2) :
            ℝ → ℂ) t) -
          (((𝓕 (mobiusThetaDirectPhysicalRung m) : MobiusThetaSourceL2) :
            ℝ → ℂ) t) = _
      rw [hnext, hm]
      ring

end RHTower
