import GaloisForLFunctions.RHTower.Sieve.KloostermanSourceFourierParseval

/-!
# Hilbert--Schmidt receiver for terminal Kloosterman source Fourier forms

Finite Cauchy--Schwarz bounds the exact source-Fourier/orbit factorization by the two source
Fourier energies and the entrywise terminal-orbit energy. The source Parseval bound then replaces
both Fourier energies by their exact residue-collision energies. This is an unconditional receiver;
it does not supply or assume the still-missing spectral saving in the orbit kernel.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem norm_bilinearKernel_sq_le_hilbertSchmidt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) (K : ι → κ → ℂ) :
    ‖∑ i, ∑ j, star (a i) * b j * K i j‖ ^ 2 ≤
      (∑ i, ‖a i‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) *
        ∑ i, ∑ j, ‖K i j‖ ^ 2 := by
  classical
  let row : ι → ℝ := fun i => ∑ j, ‖b j‖ * ‖K i j‖
  have htri :
      ‖∑ i, ∑ j, star (a i) * b j * K i j‖ ≤
        ∑ i, ‖a i‖ * row i := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    calc
      ‖∑ j, star (a i) * b j * K i j‖ ≤
          ∑ j, ‖star (a i) * b j * K i j‖ := norm_sum_le _ _
      _ = ‖a i‖ * row i := by
        unfold row
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [norm_mul, norm_star]
        ring
  have hsum0 : 0 ≤ ∑ i, ‖a i‖ * row i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j hj =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq :
      ‖∑ i, ∑ j, star (a i) * b j * K i j‖ ^ 2 ≤
        (∑ i, ‖a i‖ * row i) ^ 2 := by
    nlinarith [norm_nonneg (∑ i, ∑ j, star (a i) * b j * K i j)]
  have hrow (i : ι) :
      row i ^ 2 ≤ (∑ j, ‖b j‖ ^ 2) * ∑ j, ‖K i j‖ ^ 2 := by
    simpa [row] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun j : κ => ‖b j‖) (fun j : κ => ‖K i j‖)
  have hrowSum :
      (∑ i, row i ^ 2) ≤
        (∑ j, ‖b j‖ ^ 2) * ∑ i, ∑ j, ‖K i j‖ ^ 2 := by
    calc
      (∑ i, row i ^ 2) ≤
          ∑ i, (∑ j, ‖b j‖ ^ 2) * ∑ j, ‖K i j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hrow i
      _ = (∑ j, ‖b j‖ ^ 2) * ∑ i, ∑ j, ‖K i j‖ ^ 2 := by
        rw [Finset.mul_sum]
  calc
    ‖∑ i, ∑ j, star (a i) * b j * K i j‖ ^ 2 ≤
        (∑ i, ‖a i‖ * row i) ^ 2 := hsq
    _ ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, row i ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
        (fun i : ι => ‖a i‖) row
    _ ≤ (∑ i, ‖a i‖ ^ 2) *
        ((∑ j, ‖b j‖ ^ 2) * ∑ i, ∑ j, ‖K i j‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left hrowSum
        (Finset.sum_nonneg fun i hi => sq_nonneg _)
    _ = (∑ i, ‖a i‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) *
        ∑ i, ∑ j, ‖K i j‖ ^ 2 := by ring

/-- Fixed terminal source quadratic bounded by source Fourier energies and terminal-orbit
Hilbert--Schmidt energy. -/
theorem norm_sourceQuadratic_terminalBlock_sq_le_fourier_hilbertSchmidt
    (M q r : ℕ) [NeZero q] [NeZero r]
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M q r
        (n : ZMod q) (k : ZMod r)‖ ^ 2 ≤
      (∑ x : (ZMod q)ˣ, ‖kloostermanSourceFourier q B b x‖ ^ 2) *
        (∑ y : (ZMod r)ˣ, ‖kloostermanSourceFourier r B b y‖ ^ 2) *
          ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
            ‖kloostermanTerminalOrbit M q r x y‖ ^ 2 := by
  rw [sourceQuadratic_terminalBlock_eq_fourierOrbits]
  exact norm_bilinearKernel_sq_le_hilbertSchmidt
    (kloostermanSourceFourier q B b) (kloostermanSourceFourier r B b)
    (kloostermanTerminalOrbit M q r)

/-- Fixed terminal source quadratic bounded by exact source residue-collision energies and the
terminal-orbit Hilbert--Schmidt energy. -/
theorem norm_sourceQuadratic_terminalBlock_sq_le_residue_hilbertSchmidt
    (M q r : ℕ) [NeZero q] [NeZero r]
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M q r
        (n : ZMod q) (k : ZMod r)‖ ^ 2 ≤
      ((q : ℝ) * ∑ z : ZMod q, Complex.normSq (kloostermanSourceResidue q B b z)) *
        ((r : ℝ) * ∑ z : ZMod r, Complex.normSq (kloostermanSourceResidue r B b z)) *
          ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
            ‖kloostermanTerminalOrbit M q r x y‖ ^ 2 := by
  calc
    _ ≤ (∑ x : (ZMod q)ˣ, ‖kloostermanSourceFourier q B b x‖ ^ 2) *
        (∑ y : (ZMod r)ˣ, ‖kloostermanSourceFourier r B b y‖ ^ 2) *
          ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
            ‖kloostermanTerminalOrbit M q r x y‖ ^ 2 :=
      norm_sourceQuadratic_terminalBlock_sq_le_fourier_hilbertSchmidt M q r B b
    _ ≤ ((q : ℝ) * ∑ z : ZMod q,
          Complex.normSq (kloostermanSourceResidue q B b z)) *
        ((r : ℝ) * ∑ z : ZMod r,
          Complex.normSq (kloostermanSourceResidue r B b z)) *
          ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
            ‖kloostermanTerminalOrbit M q r x y‖ ^ 2 := by
      have hq := sum_normSq_kloostermanSourceFourier_le_residueEnergy q B b
      have hr := sum_normSq_kloostermanSourceFourier_le_residueEnergy r B b
      simp_rw [Complex.sq_norm]
      gcongr
      · exact Finset.sum_nonneg fun x hx =>
          Finset.sum_nonneg fun y hy => Complex.normSq_nonneg _
      · exact Finset.sum_nonneg fun y hy => Complex.normSq_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) <|
          Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _

end

end RHTower.Sieve
