import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoundedField.PhysicalSector
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.RadiusNormalization
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.IncrementClock

/-! # Delayed first excursions with every normalized coupling bounded below -/
open Set Filter MeasureTheory Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds AccuracyScales.TenthPlateau
open private rms_le_hundred_norm from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.RadiusNormalization
noncomputable section

private theorem norm_le_scaled_rms {n : ℕ} (x : PrefixIndex n→ℝ) (hx : ∀ i, |x i|≤27) :
    coefficientNorm x ≤ 27*sqrt (Fintype.card (PrefixIndex n):ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (PrefixIndex n))‖^2 ≤ _
  rw [EuclideanSpace.norm_sq_eq,mul_pow,sq_sqrt (Nat.cast_nonneg _)]
  have h := sum_le_sum (s:=Finset.univ) (fun (i : PrefixIndex n) _ =>
    pow_le_pow_left₀ (abs_nonneg _) (hx i) 2)
  simpa only [sum_const,card_univ,nsmul_eq_mul,Real.norm_eq_abs,mul_comm (27^2:ℝ)] using h

/-- On one draw the original and unit-RMS trajectories both retain
their first half-budget waits and a linear-in-dimension all-time cap.
Even after normalization, every laboratory coefficient stays strong. -/
theorem unit_rms_strong_excursion :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let R := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let J := fun (x : PrefixIndex n→ℝ) (T : ℝ) =>
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x
      ∀ T ≥ (1:ℝ), ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ (100*T)^7*pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          let y := atRadius R x
          x ∈ allCoordStrongEvent n (1/100) ∧ (∀ i, |x i| ≤ 27) ∧
          y ∈ allCoordStrongEvent n (1/2700) ∧ (∀ i, |y i| ≤ 2700) ∧
          coefficientNorm y=R ∧ J x (100*T) ∧ J y T ∧
          (∀ t : ℝ, pathGateDistance n (2^K*3) x t ≤ 1/10) ∧
          ∀ t : ℝ, pathGateDistance n (2^K*3) y t ≤ 1/10 := by
  obtain ⟨C,hC,hsector⟩ := bounded_physical_sector
  refine ⟨C,hC,?_⟩
  filter_upwards [hsector,delay_of_cheap] with k hk hd
  intro n K P R J T hT
  have hT' : 1 ≤ 100*T := by linarith only [hT]
  obtain ⟨B,E,hB,hE,hprob,hfit⟩ := hk _ hT'
  refine ⟨E,hE,hprob,?_⟩
  filter_upwards [hd] with ω hdelay
  intro he u x y
  obtain ⟨hstrong,hupper,hglobal,hinc⟩ := hfit ω he
  obtain ⟨ho,hr⟩ := hdelay (100*T) (zero_lt_one.trans_le hT') B hB hinc
  letI : Nonempty (PrefixIndex n) := ⟨(pathCoeffEquiv n).symm (.inl (0,2))⟩
  have hR : 0<R := sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have h₁ := rms_le_hundred_norm hstrong
  have h₂ := norm_le_scaled_rms x hupper
  change R≤100*coefficientNorm x at h₁
  change coefficientNorm x≤27*R at h₂
  have hn : 0<coefficientNorm x := by linarith only [hR,h₁]
  let q := R/coefficientNorm x
  have hq : 0<q := div_pos hR hn
  have hu : q≤100 := (div_le_iff₀ hn).mpr h₁
  have hl : 1/27≤q := (le_div_iff₀ hn).mpr (by linarith only [h₂])
  have hqT := mul_le_mul_of_nonneg_right hu (zero_le_one.trans hT)
  have hraw (t : ℝ) : pathGateDistance n (2^K*3) x t ≤ 1/10 := by
    change pathGateDistance n _ (fun i => u (pathCoeffEquiv n i)) _ ≤ _
    rw [pathGateDistance,numberedGenerator_shell]
    exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp (hglobal t)
  refine ⟨hstrong,hupper,?_,?_,coefficientNorm_atRadius x hR.le hn,⟨ho,hr⟩,⟨?_,?_⟩,hraw,?_⟩
  · intro i
    change 1/2700 ≤ |q*x i|
    rw [abs_mul,abs_of_pos hq]
    exact (by norm_num : (1/2700:ℝ)=(1/27)*(1/100)).le.trans
      (mul_le_mul hl (hstrong i) (by norm_num) hq.le)
  · intro i
    change |q*x i| ≤ 2700
    rw [abs_mul,abs_of_pos hq]
    exact (mul_le_mul hu (hupper i) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show y=q • x from rfl,smul_crossingOrigin _ _ _ hq]
    exact hqT.trans_lt ho
  · intro s hs
    apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show y=q • x from rfl,smul_crossingWait _ _ _ hq]
    exact hqT.trans_lt (hr s hs)
  · intro t
    rw [show y=q • x from rfl,distance_dilate]
    exact hraw (q*t)

#print axioms unit_rms_strong_excursion
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
