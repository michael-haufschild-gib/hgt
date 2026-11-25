import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # A deterministic bandwidth floor at fixed Pauli coefficient norm -/

open Matrix Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes WeakBonds
noncomputable section

/-- A centered spectrum in [L,U] has second moment at most −LU.
The two-point spectrum at symmetric endpoints attains the resulting
factor of two between bandwidth and standard deviation. -/
private theorem twice_deviation_le_width {I : Type*} [Fintype I] [Nonempty I]
    (E : I→ℝ) {r : ℝ} (hr : 0≤r) (hcenter : ∑ i, E i=0)
    (hvar : ∑ i, E i^2=(Fintype.card I:ℝ)*r^2) :
    2*r ≤ univ.sup' univ_nonempty E-univ.inf' univ_nonempty E := by
  let L := univ.inf' univ_nonempty E
  let U := univ.sup' univ_nonempty E
  have hl (i : I) : L≤E i := inf'_le E (mem_univ i)
  have hu (i : I) : E i≤U := le_sup' E (mem_univ i)
  have hterm (i : I) : E i^2 ≤ (L+U)*E i-L*U := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hl i)) (sub_nonneg.mpr (hu i))]
  have h := sum_le_sum (fun i (_ : i∈(univ:Finset I)) => hterm i)
  rw [sum_sub_distrib,←mul_sum,hcenter,mul_zero,zero_sub,sum_const,card_univ,nsmul_eq_mul,hvar] at h
  have hD : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hlim : r^2≤ -(L*U) := (le_of_mul_le_mul_left (by simpa only [mul_neg] using h) hD)
  have hw : 0≤U-L := sub_nonneg.mpr ((hl (Classical.arbitrary I)).trans (hu _))
  apply (sq_le_sq₀ (mul_nonneg zero_le_two hr) hw).mp
  nlinarith only [hlim,sq_nonneg (U+L)]

/-- Pauli orthogonality identifies the spectral standard deviation exactly
with the Euclidean coupling norm. Hence every prefix has bandwidth at
least twice that norm, even on the weak-bond events. -/
theorem twice_coefficientNorm_le_width (n : ℕ) (x : PrefixIndex n→ℝ) :
    2*coefficientNorm x ≤ circuitHamiltonianSpectralWidth (prefixGenerator n x) := by
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
    ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have heq : prefixGenerator n x=H := by
    apply Subtype.ext
    change numberedGenerator n x=pathHamiltonian u
    simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
  have hmass : (∑ l : PathLabel n, (u l)^2)=(coefficientNorm x)^2 := by
    rw [coefficientNorm,EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs,sq_abs] using (Equiv.sum_comp (pathCoeffEquiv n).symm (fun i => x i^2))
  obtain ⟨hc,hm⟩ := FluxOccupation.path_spectral_moments u
  rw [heq]
  apply twice_deviation_le_width (r:=coefficientNorm x) H.2.isHermitian.eigenvalues (norm_nonneg _) hc
  rw [hmass] at hm
  rw [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  exact hm

#print axioms twice_coefficientNorm_le_width
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
