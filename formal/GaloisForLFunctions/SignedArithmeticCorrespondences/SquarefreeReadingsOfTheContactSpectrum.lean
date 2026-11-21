import GaloisForLFunctions.SignedArithmeticCorrespondences.CountingTheTrianglesOfThePrimeContactMatrix
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal

/-!
# Squarefree density and Laurent constant from cubic spectra

El Kaouni's Abel summation step in Proposition F.2 identifies the
constant retained by a harmonic readout. Here its data consist only of
successive cubic traces of the unit-spaced Mangoldt contact matrices.
-/
noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open _root_.RHTower.Sieve
namespace GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments

/-- The positive sites at which adding the next coordinate preserves the cubic trace. -/
def flatSites (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n =>
    Matrix.trace ((primeContactMatrix 0 n)^3) = Matrix.trace ((primeContactMatrix 0 (n-1))^3)

theorem flatSites_eq (N : ℕ) : flatSites N=(Icc 1 N).filter Squarefree := by
  ext n
  simp only [flatSites,mem_filter]
  constructor
  · rintro ⟨hn,he⟩
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
    exact ⟨hn,(squarefree_iff_cubic_prefix_unchanged m).mpr (by rw [Nat.add_sub_cancel] at he; exact he)⟩
  · rintro ⟨hn,h⟩
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
    exact ⟨hn,by rw [Nat.add_sub_cancel]; exact (squarefree_iff_cubic_prefix_unchanged m).mp h⟩

/-- Proportion of consecutive cubic spectra which agree, with square-root error. -/
theorem flat_site_count (N : ℕ) : |((flatSites N).card:ℝ)-(N:ℝ)*(6/Real.pi^2)|≤2*Real.sqrt N+1 := by
  have he : ((flatSites N).card:ℝ)=∑ n∈Icc 1 N,((moebius n:ℤ):ℝ)^2 := by
    rw [flatSites_eq,←sum_boole]
    exact sum_congr rfl fun n _ => (moebius_sq_eq_indicator n).symm
  rw [he,←squarefreeDensity_eq]
  exact abs_sum_moebius_sq_Icc_sub_le N

/-- Harmonic density of the flat spectral steps recovers the Laurent finite
part of ζ(s)/ζ(2s), with a uniform remainder at every real cutoff X≥1. -/
theorem flat_site_laurent_reading {X : ℝ} (hX : 1≤X) :
    |(∑ n∈flatSites ⌊X⌋₊,(n:ℝ)⁻¹)-
      squarefreeDensity*Real.log X-squarefreeHarmonicConstant|≤12*X^(-(1/2:ℝ)) := by
  have he : (∑ n∈flatSites ⌊X⌋₊,(n:ℝ)⁻¹)=harmonicMoebiusDiagonal X := by
    rw [flatSites_eq,sum_filter,harmonicMoebiusDiagonal]
    refine sum_congr rfl fun n _ => ?_
    rw [moebius_sq_eq_indicator]
    by_cases hn : Squarefree n <;> simp [hn,one_div]
  rw [he]
  exact squarefree_harmonic_finite_part hX

end GaloisForLFunctions.SignedArithmeticCorrespondences.PrimeContactMoments
