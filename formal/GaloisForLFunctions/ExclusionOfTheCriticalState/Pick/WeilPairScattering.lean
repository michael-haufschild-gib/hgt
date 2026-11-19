import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeCauchyDephasing
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss

/-!
# Pairwise loss of Weil probe mass and repair of two-point determinants

The two-body KdV scattering factor from Shi, arXiv:2611.22194,
Theorem 6.2(a), gives the fraction of squared entry mass removed in each
step of Cauchy dephasing. For two probes the entire lost cross mass is
added to the determinant.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open HilbertMetric.CauchyDephasing
open Matrix

private abbrev raw {n : ℕ} (p : Fin n → {x : ℝ // 1 ≤ x}) := probeGram (fun i => (p i).val)

/-- The signed Weil matrix has strictly positive entries throughout the
real probe domain used by the dephasing channel. -/
theorem safe_probeGram_entry_pos {n : ℕ} (p : Fin n → {x : ℝ // 1 ≤ x}) (i j : Fin n) :
    0 < (probeGram (fun k => (p k).val) i j).re := by
  have hdom (k : Fin n) : 1/2 < (p k).val := by linarith only [(p k).property]
  have hs (k : Fin n) : 0 < probeSymbol (p k).val := by
    have h := congrArg Complex.re (probeSymbol_eq_logDeriv_xiCent (hdom k))
    simp only [Complex.ofReal_re] at h
    rw [h]
    exact _root_.RHTower.re_logDeriv_xiCent_pos (by simpa only [Complex.ofReal_re] using hdom k)
  change 0 < bareMixedEnergy (probe (p i).val) (probe (p j).val)
  rw [bareMixedEnergy_probe (hdom i) (hdom j)]
  exact div_pos (add_pos (hs i) (hs j)) (by linarith only [hdom i,hdom j])

theorem safe_probeGram_entry_ne_zero {n : ℕ} (p : Fin n → {x : ℝ // 1 ≤ x}) (i j : Fin n) :
    probeGram (fun k => (p k).val) i j ≠ 0 := by
  intro h
  have hp := safe_probeGram_entry_pos p i j
  rw [h,Complex.zero_re] at hp
  exact hp.false

/-- The surviving squared mass at all finite iteration counts. -/
theorem dephased_entry_mass {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) (i j : Fin n) :
    ‖dephasedProbeGram k r p i j‖^2 =
      (1-contrast (r i) (r j)^2)^k * ‖raw p i j‖^2 := by
  rw [contrast_sq_eq_coherence_loss, sub_sub_cancel]
  change ‖(coherence (r i) (r j) : ℂ)^k * raw p i j‖^2 = _
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (coherence_pos _ _),
    mul_pow,pow_right_comm]

/-- A phase factor is the exact loss of squared mass in the next step. -/
theorem dephased_entry_loss {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) (i j : Fin n) :
    ‖dephasedProbeGram k r p i j‖^2 - ‖dephasedProbeGram (k+1) r p i j‖^2 =
      contrast (r i) (r j)^2 * ‖dephasedProbeGram k r p i j‖^2 := by
  rw [dephased_entry_mass,dephased_entry_mass,pow_succ]
  ring

/-- Across the full matrix the scattering factors are weighted by the
current entry masses, including all off-diagonal arithmetic data. -/
theorem dephased_total_loss {n : ℕ} (k : ℕ) (r : Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (∑ i, ∑ j, ‖dephasedProbeGram k r p i j‖^2) -
      (∑ i, ∑ j, ‖dephasedProbeGram (k+1) r p i j‖^2) =
      ∑ i, ∑ j, contrast (r i) (r j)^2 * ‖dephasedProbeGram k r p i j‖^2 := by
  simp only [← dephased_entry_loss,Finset.sum_sub_distrib]

/-- Complete characterization of the support on which loss stops. -/
theorem dephased_entry_lossless_iff {n : ℕ} (k : ℕ) (r : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) (i j : Fin n) :
    ‖dephasedProbeGram k r p i j‖^2 = ‖dephasedProbeGram (k+1) r p i j‖^2 ↔
      r i = r j := by
  rw [← sub_eq_zero,dephased_entry_loss,mul_eq_zero,sq_eq_zero_iff,contrast_eq_zero_iff,
    sq_eq_zero_iff,norm_eq_zero]
  change (_ ∨ (coherence (r i) (r j) : ℂ)^k * raw p i j = 0) ↔ _
  have h : (coherence (r i) (r j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coherence_pos _ _).ne'
  rw [mul_eq_zero,or_iff_right (pow_ne_zero _ h),or_iff_left (safe_probeGram_entry_ne_zero p i j)]

private theorem raw_pair_symm (p : Fin 2 → {x : ℝ // 1 ≤ x}) :
    raw p 1 0 = raw p 0 1 := by
  apply congrArg Complex.ofReal
  apply bareMixedEnergy_probe_symm <;> linarith only [(p 0).property,(p 1).property]

/-- The determinant rises by exactly the lost cross mass for any pair,
regardless of the initial determinant sign. -/
theorem dephased_pair_determinant (k : ℕ) (r : Fin 2 → ℝ) (p : Fin 2 → {x : ℝ // 1 ≤ x}) :
    (dephasedProbeGram k r p).det =
      (raw p).det + ((1-(1-contrast (r 0) (r 1)^2)^k : ℝ) : ℂ) * (raw p 0 1)^2 := by
  rw [Matrix.det_fin_two,Matrix.det_fin_two,dephasedProbeGram_diagonal,dephasedProbeGram_diagonal,
    contrast_sq_eq_coherence_loss,sub_sub_cancel]
  change raw p 0 0 * raw p 1 1 -
    ((coherence (r 0) (r 1) : ℂ)^k * raw p 0 1) * ((coherence (r 1) (r 0) : ℂ)^k * raw p 1 0) = _
  rw [coherence_symm (r 1) (r 0),raw_pair_symm]
  push_cast
  rw [pow_right_comm (coherence (r 0) (r 1) : ℂ) 2 k]
  ring

#print axioms safe_probeGram_entry_pos
#print axioms safe_probeGram_entry_ne_zero
#print axioms dephased_entry_mass
#print axioms dephased_entry_loss
#print axioms dephased_total_loss
#print axioms dephased_entry_lossless_iff
#print axioms dephased_pair_determinant
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
