import GaloisForLFunctions.RHTower.WeilPaperPacketHermitianRepair
import Zeta23.GammaFacts
import Zeta23.Taper.Fourier

/-!
# Real packet coefficients preserve the WP01 observables

Split every complex column into its real and imaginary columns. Their covariance
is the entrywise real part of the original covariance. The full archimedean
kernel is real, so this preserves both the energy and all integer defects.
Discarding imaginary covariance also decreases the Crouzeix distance budget.
-/

open Matrix Complex MeasureTheory Zeta23 GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

/-- The gamma multiplier is even on the real Fourier axis. -/
theorem packet_gammaBracket_neg (r : ℝ) : EF.gammaBracket (-r) = EF.gammaBracket r := by
  have harg : (1 / 4 + I * ((-r : ℝ) : ℂ) / 2 : ℂ) = conj (1 / 4 + I * (r : ℂ) / 2) := by
    apply Complex.ext <;> simp [map_ofNat]
  rw [EF.gammaBracket, harg, Zeta23.digamma_conj, Complex.conj_re]
  rfl

/-- The full Weil functional with any real arithmetic weights takes real values on real tests. -/
theorem weilFullFunctional_ofReal_im (lam : ℕ → ℝ) (f : ℝ → ℝ) :
    (weilFullFunctional lam (fun x => (f x : ℂ))).im = 0 := by
  have hint : conj (∫ r : ℝ, paperFT (fun x => (f x : ℂ)) r * (EF.gammaBracket r : ℂ)) =
      ∫ r : ℝ, paperFT (fun x => (f x : ℂ)) r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_conj]
    simp_rw [map_mul, Taper.conj_paperFT_ofReal, Complex.conj_ofReal]
    simpa only [Complex.ofReal_neg, packet_gammaBracket_neg] using
      integral_neg_eq_self (fun r : ℝ =>
        paperFT (fun x => (f x : ℂ)) r * (EF.gammaBracket r : ℂ)) volume
  have hprime : conj (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      ((f (Real.log n) : ℂ) + (f (-Real.log n) : ℂ))) =
      ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        ((f (Real.log n) : ℂ) + (f (-Real.log n) : ℂ)) := by
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro n
    simp
  have hc : conj (weilFullFunctional lam (fun x => (f x : ℂ))) =
      weilFullFunctional lam (fun x => (f x : ℂ)) := by
    unfold weilFullFunctional
    rw [map_add, map_sub, map_add, map_mul, hint, hprime]
    simp [Taper.conj_paperFT_ofReal, map_ofNat, neg_div]
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

/-- The full translated-bump kernel, including both pole terms, is real. -/
theorem packetArchKernel_im (N L : ℕ) (m k : PacketIndex N) :
    (packetArchKernel N L m k).im = 0 := by
  let r (y : ℝ) := ∫ t : ℝ, narrowBump (N * L) t * narrowBump (N * L) (t - y)
  have hcorr : EF.weilTest (narrowBumpC (N * L)) (narrowBumpC (N * L)) =
      fun y => (r y : ℂ) := by
    funext y
    rw [weilTest_apply, ← integral_complex_ofReal]
    simp only [narrowBumpC, Complex.conj_ofReal, Complex.ofReal_mul]
  simp only [packetArchKernel, hcorr]
  exact weilFullFunctional_ofReal_im 0 (fun y => r (y - (resPt N m - resPt N k)))

/-- The doubled family of real and imaginary coefficient columns. -/
def realPacketColumns {N : ℕ} {ι : Type*} (A : Matrix (PacketIndex N) ι ℂ) :
    Matrix (PacketIndex N) (ι ⊕ ι) ℂ :=
  fun m => Sum.elim (fun i => ((A m i).re : ℂ)) (fun i => ((A m i).im : ℂ))

/-- Every coefficient in the doubled family is real. -/
theorem realPacketColumns_im {N : ℕ} {ι : Type*}
    (A : Matrix (PacketIndex N) ι ℂ) (m : PacketIndex N) (i : ι ⊕ ι) :
    (realPacketColumns A m i).im = 0 := by
  cases i <;> simp [realPacketColumns]

/-- Its covariance is exactly the real part of the original covariance. -/
theorem realPacketColumns_covariance {N : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (PacketIndex N) ι ℂ) (m k : PacketIndex N) :
    (realPacketColumns A * (realPacketColumns A)ᴴ) m k = ((A * Aᴴ) m k).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_def,
    Fintype.sum_sum_type, realPacketColumns, Sum.elim_inl, Sum.elim_inr,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
    ← Complex.ofReal_add, Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The full energy sees only the real part of covariance. -/
theorem packetArchPairing_real_covariance {N : ℕ} (L : ℕ)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    packetArchPairing L (fun m k => ((C m k).re : ℂ)) = packetArchPairing L C := by
  unfold packetArchPairing
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    packetArchKernel_im, mul_zero, sub_zero]

/-- Splitting the columns preserves the exact full archimedean energy. -/
theorem packetArchEnergy_realPacketColumns {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    packetArchEnergy L (realPacketColumns A) = packetArchEnergy L A := by
  rw [packetArchEnergy_eq_covariance, packetArchEnergy_eq_covariance]
  have h : realPacketColumns A * (realPacketColumns A)ᴴ =
      fun m k => (((A * Aᴴ) m k).re : ℂ) := by
    ext m k
    exact realPacketColumns_covariance A m k
  rw [h, packetArchPairing_real_covariance]

/-- The real part of every integer trace is unchanged. -/
theorem divisibilityTrace_realPacketColumns_re {N : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (PacketIndex N) ι ℂ) (n : ℕ) :
    (divisibilityTrace (realPacketColumns A * (realPacketColumns A)ᴴ) n).re =
      (divisibilityTrace (A * Aᴴ) n).re := by
  unfold divisibilityTrace
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp only [realPacketColumns_covariance, Complex.ofReal_re]

/-- Exact equality of the actual finite integer-defect vectors. -/
theorem defect_realPacketColumns {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    defect (packetColumnMixture L (realPacketColumns A)) = defect (packetColumnMixture L A) := by
  ext j
  rw [defect_packetColumnMixture, defect_packetColumnMixture, divisibilityTrace_realPacketColumns_re]

/-- Canonical null repair also preserves the full energy exactly under realification. -/
theorem nullRepair_realPacketColumns_energy {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    energy (nullRepair (packetColumnMixture L (realPacketColumns A))) =
      energy (nullRepair (packetColumnMixture L A)) := by
  simp only [nullRepair, map_add, energy_packetColumnMixture,
    packetArchEnergy_realPacketColumns, defect_realPacketColumns]

/-- Removing imaginary covariance can only decrease the Crouzeix squared distance. -/
theorem realPacketColumns_crouzeix_gap_le {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    finiteMatrixHilbertSchmidtSq ((realPacketColumns A)ᴴ * realPacketColumns A) +
        finiteMatrixHilbertSchmidtSq ((realPacketColumns B)ᴴ * realPacketColumns B) -
          2 * finiteMatrixHilbertSchmidtSq ((realPacketColumns A)ᴴ * realPacketColumns B) ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B) := by
  classical
  rw [crouzeix_gram_energy_identity, crouzeix_gram_energy_identity,
    finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  apply Finset.sum_le_sum
  intro m _
  apply Finset.sum_le_sum
  intro k _
  simp only [Matrix.sub_apply, realPacketColumns_covariance, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.sub_re]
  have h := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm ((A * Aᴴ) m k - (B * Bᴴ) m k)) 2
  simpa only [sq_abs] using h

/-- Realification preserves the energy of exact defect transport as well. -/
theorem packetTransferRepair_realPacketColumns_energy {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    energy (packetTransferRepair L (realPacketColumns A) (realPacketColumns B)) =
      energy (packetTransferRepair L A B) := by
  simp only [packetTransferRepair, map_add, energy_packetColumnMixture,
    packetArchEnergy_realPacketColumns, defect_realPacketColumns]

/-- The original positive correction already benefits from the smaller real covariance gap. -/
theorem packetRepairBudget_twice_sq_le_real_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    2 * repairBudget (defect (packetColumnMixture L B) - defect (packetColumnMixture L A)) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq ((realPacketColumns A)ᴴ * realPacketColumns A) +
        finiteMatrixHilbertSchmidtSq ((realPacketColumns B)ᴴ * realPacketColumns B) -
          2 * finiteMatrixHilbertSchmidtSq ((realPacketColumns A)ᴴ * realPacketColumns B)) *
            packetRepairSensitivity N L := by
  classical
  simpa only [defect_realPacketColumns] using
    packetRepairBudget_twice_sq_le_crouzeix L (realPacketColumns A) (realPacketColumns B)

/-- The actual integer-null mixture pays only for the real covariance energy. -/
theorem nullRepair_packetColumnMixture_energy_sub_twice_sq_le_real {N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    2 * (energy (nullRepair (packetColumnMixture L A)) - packetArchEnergy (L + 1) A) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq ((realPacketColumns A)ᴴ * realPacketColumns A) *
        packetRepairSensitivity N L := by
  classical
  simpa only [nullRepair_realPacketColumns_energy, packetArchEnergy_realPacketColumns] using
    nullRepair_packetColumnMixture_energy_sub_twice_sq_le L (realPacketColumns A)

end RHTower.WeilWorkPBAP
