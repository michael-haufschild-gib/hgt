import GaloisForLFunctions.RHTower.SteinhausFiniteNodeCovariance
import GaloisForLFunctions.RHTower.Sieve.DirichletPowerConvolution

/-!
# Literal conditional Gram determinants and cofactor-product fibres

Expanding a conditional channel minor produces products of small-prime phases. Different
cofactor tuples can have the same product, so their signed determinants must be combined
before Parseval. This file performs that grouping for the literal reflected-primal AFE
coefficients, identifies the full conditional Gram determinant as a finite sum of carrier
energies, and applies the existing subpower fourth-moment bound to its minors.

These are exact source identities. They do not assert a lower bound for the grouped
coefficient mass or a simultaneous target probability.
-/

open Finset Matrix MeasureTheory
namespace RHTower
open SteinhausModel
noncomputable section

private theorem X_finset_prod {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0) (omega : Omega) :
    X (∏ i ∈ s, n i) omega = ∏ i ∈ s, X (n i) omega := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      X_mul (hn i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hn j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hn j (Finset.mem_insert_of_mem hj))]

private def channelDeterminantFibre {J M : ℕ}
    (a : Fin J → Fin J → Fin M → ℂ) (q : Fin (M ^ J)) : ℂ :=
  ∑ m ∈ Sieve.powFibre J M q, (Matrix.of fun i j => a i j (m i)).det

private theorem determinant_finCarrier_eq {J M : ℕ}
    (a : Fin J → Fin J → Fin M → ℂ) (omega : Omega) :
    (Matrix.of fun i j => steinhausFinCarrier M (a i j) omega).det =
      steinhausFinCarrier (M ^ J) (channelDeterminantFibre a) omega := by
  classical
  have hexpand : (Matrix.of fun i j => steinhausFinCarrier M (a i j) omega).det =
      ∑ m : Fin J → Fin M,
        (Matrix.of fun i j => a i j (m i) * X ((m i : ℕ) + 1) omega).det := by
    have h := (Matrix.detRowAlternating (n := Fin J) (R := ℂ)).toMultilinearMap.map_sum
      (fun (i : Fin J) (m : Fin M) (j : Fin J) => a i j m * X ((m : ℕ) + 1) omega)
    change (Matrix.of (fun i => ∑ m : Fin M,
      (fun j => a i j m * X ((m : ℕ) + 1) omega))).det = _ at h
    have hleft : (Matrix.of (fun i => ∑ m : Fin M,
        (fun j => a i j m * X ((m : ℕ) + 1) omega))) =
        Matrix.of (fun i j => steinhausFinCarrier M (a i j) omega) := by
      ext i j
      simp [steinhausFinCarrier]
    rw [hleft] at h
    exact h
  have hterm : ∀ m : Fin J → Fin M,
      (Matrix.of fun i j => a i j (m i) * X ((m i : ℕ) + 1) omega).det =
        (Matrix.of fun i j => a i j (m i)).det *
          X ((Sieve.dirichletPowerConvolutionPowIdx m : ℕ) + 1) omega := by
    intro m
    have hmat : (Matrix.of fun i j => a i j (m i) * X ((m i : ℕ) + 1) omega) =
        Matrix.of (fun i j => X ((m i : ℕ) + 1) omega * a i j (m i)) := by
      ext i j; exact mul_comm _ _
    rw [hmat, Matrix.det_mul_column, Sieve.dirichletPowerConvolutionPowIdx_val_add_one,
      X_finset_prod _ _ (fun i _ => Nat.succ_ne_zero _) omega]
    exact mul_comm _ _
  rw [hexpand]
  simp_rw [hterm]
  unfold steinhausFinCarrier channelDeterminantFibre
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin J → Fin M))
    Sieve.dirichletPowerConvolutionPowIdx
    (fun m => (Matrix.of fun i j => a i j (m i)).det *
      X ((Sieve.dirichletPowerConvolutionPowIdx m : ℕ) + 1) omega)]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_mul]
  unfold Sieve.powFibre
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

/-- Product-frequency coefficient of a literal reflected-primal channel determinant.
All cofactor tuples sharing a product are summed with their determinant signs intact. -/
def reflectedPrimalChannelDeterminantCoefficient {J : ℕ}
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (p : Fin J → ℕ)
    (q : Fin (N ^ J)) : ℂ :=
  ∑ m ∈ Sieve.powFibre J N q,
    (Matrix.of fun i j =>
      smoothAFEZetaRightReflectedPrimalChannelFinCoeff (d j) (tau j) r N (p i) (m i)).det

/-- The actual conditional channel determinant is exactly its cofactor-product carrier. -/
theorem reflectedPrimalChannelDeterminant_eq_carrier {J : ℕ}
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (p : Fin J → ℕ) (omega : Omega) :
    (Matrix.of fun i j => steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N)
      N (p i) omega).det =
    steinhausFinCarrier (N ^ J)
      (reflectedPrimalChannelDeterminantCoefficient d tau r N p) omega := by
  have h := determinant_finCarrier_eq
    (fun i j => smoothAFEZetaRightReflectedPrimalChannelFinCoeff
      (d j) (tau j) r N (p i)) omega
  simp_rw [steinhausFinCarrier_reflectedPrimalChannel_eq] at h
  exact h

/-- Exact conditional-minor second moment for the literal coefficients. Parseval acts on
product-frequency fibres, not on individual cofactor tuples. -/
theorem integral_normSq_reflectedPrimalChannelDeterminant {J : ℕ}
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (p : Fin J → ℕ) :
    (∫ omega, ‖(Matrix.of fun i j => steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N)
      N (p i) omega).det‖ ^ 2 ∂steinhausMeasure) =
      ∑ q : Fin (N ^ J), ‖reflectedPrimalChannelDeterminantCoefficient d tau r N p q‖ ^ 2 := by
  simp_rw [reflectedPrimalChannelDeterminant_eq_carrier]
  exact integral_normSq_steinhausFinCarrier _ _

open GaloisForLFunctions.HTGeometry

/-- Conditional covariance of the literal reflected-primal node packet after the
small-prime phases are frozen. -/
def reflectedPrimalConditionalGram {J : ℕ} (P : Finset ℕ)
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (omega : Omega) : Matrix (Fin J) (Fin J) ℂ :=
  hermFeatureGram (fun j (p : ↥P) => steinhausLargePrimeChannel
    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N) N p omega)

/-- The product-frequency coefficients of every canonical prime-channel minor. -/
def reflectedPrimalConditionalGramCoefficient {J : ℕ} (P : Finset ℕ)
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ)
    (s : Set.powersetCard (↥P) J) (q : Fin (N ^ J)) : ℂ :=
  reflectedPrimalChannelDeterminantCoefficient d tau r N
    (fun j => (Set.powersetCard.ofFinEmbEquiv.symm s j : ℕ)) q

/-- The conditional determinant is exactly a sum of squared cofactor-product carriers. -/
theorem reflectedPrimalConditionalGram_det_eq_energy {J : ℕ} (P : Finset ℕ)
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (omega : Omega) :
    (reflectedPrimalConditionalGram P d tau r N omega).det.re =
      steinhausFinEnergy (Finset.univ : Finset (Set.powersetCard (↥P) J)) (N ^ J)
        (reflectedPrimalConditionalGramCoefficient P d tau r N) omega := by
  rw [reflectedPrimalConditionalGram, det_hermFeatureGram_eq_pluckerNormSq]
  simp only [Complex.ofReal_re, hermPluckerNormSq, steinhausFinEnergy]
  apply Finset.sum_congr rfl
  intro s _
  have hminor : hermFeatureMinor
      (fun j (p : ↥P) => steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N) N p omega) s =
      (Matrix.of fun i j => steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N)
        N (Set.powersetCard.ofFinEmbEquiv.symm s i : ℕ) omega).det := by
    exact (Matrix.det_transpose _).symm
  rw [hminor, reflectedPrimalChannelDeterminant_eq_carrier]
  rfl

/-- The mean conditional covariance determinant retains every signed product-frequency
collision inside each prime-channel minor. -/
theorem integral_reflectedPrimalConditionalGram_det {J : ℕ} (P : Finset ℕ)
    (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) :
    (∫ omega, (reflectedPrimalConditionalGram P d tau r N omega).det.re ∂steinhausMeasure) =
      ∑ s : Set.powersetCard (↥P) J, ∑ q : Fin (N ^ J),
        ‖reflectedPrimalConditionalGramCoefficient P d tau r N s q‖ ^ 2 := by
  simp_rw [reflectedPrimalConditionalGram_det_eq_energy]
  exact integral_steinhausFinEnergy_eq_totalVariance _ _ _

/-- Subpower fourth-moment control for each literal conditional determinant carrier. -/
theorem exists_integral_norm_four_reflectedPrimalChannelDeterminant_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ} (d tau : Fin J → ℝ) (r : ℝ) (N : ℕ) (p : Fin J → ℕ),
      (∫ omega, ‖(Matrix.of fun i j => steinhausLargePrimeChannel
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau j) r N)
        N (p i) omega).det‖ ^ 4 ∂steinhausMeasure) ≤
      C * (((N ^ J * N ^ J : ℕ) : ℝ) ^ epsilon) *
        (∑ q : Fin (N ^ J), ‖reflectedPrimalChannelDeterminantCoefficient d tau r N p q‖ ^ 2) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_integral_norm_four_steinhausFinCarrier_le_rpow hepsilon
  refine ⟨C, hC, ?_⟩
  intro J d tau r N p
  simp_rw [reflectedPrimalChannelDeterminant_eq_carrier]
  exact hbound _ _

end
end RHTower
