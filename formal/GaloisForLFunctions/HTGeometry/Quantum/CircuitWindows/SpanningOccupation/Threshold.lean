import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpanningOccupation.ExactCount
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ScalarStability

/-! # The first budget changing the precision order of return occupation -/
open Filter MeasureTheory Set Real Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningOccupation
noncomputable section
open SharpOccupation

/-- Below the spanning-tree budget, occupation has scalar order ε^(D−1).
The dates of exact cost N−1 already occupy at least c√ε · ε^(D−2).
Both bounds hold on the same observation interval and at the same error. -/
theorem gaussian_spanning_occupation_threshold :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ A B c : ℝ, 0 < A ∧ 0 < B ∧ 0 < c ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          (∀ s : ℕ, s+1 < N → A*ε^(D-1) ≤ visitFraction H s ε a T ∧
            visitFraction H s ε a T ≤ B*ε^(D-1)) ∧
          c*sqrt ε*ε^(D-2) ≤ volume.real (exactCount H ε (N-1)∩Icc a T)/(T-a) := by
  filter_upwards [gaussian_exact_spanning_occupation,DisconnectedReturns.gaussian_disconnected_scalar_return,
    gaussian_path_all_prefixes_maximally_projective] with ω he hc hspec k
  intro N D H
  obtain ⟨c,hcpos,hocc⟩ := he k
  obtain ⟨K,hK,hcontrol⟩ := hc (k+1)
  have hD : (0:ℝ)<D := by dsimp [D]; positivity
  let A := (D:ℝ)/2*(1/π)^(D-1)
  let B := 2*(D:ℝ)*(K/2)^(D-1)
  refine ⟨A,B,c,by dsimp [A]; positivity,by dsimp [B]; positivity,hcpos,?_⟩
  have hroot : 0 < sqrt 2 := by positivity
  filter_upwards [hocc,Ioo_mem_nhdsGT hroot,Ioo_mem_nhdsGT (div_pos hroot hK)] with ε hex hε hKε
  have hepos : 0 < ε := hε.1
  intro a
  have hs := (lt_div_iff₀ hK).mp hKε.2
  rw [mul_comm ε K] at hs
  have hL := ShortTimeProducts.scalar_fraction H (hspec k) hε.1 hε.2 a
  have hU := ShortTimeProducts.scalar_fraction H (hspec k) (mul_pos hK hε.1) hs a
  have hl := (ShortTimeProducts.physical_arc_bounds hε.1 hε.2).1
  have hu := (ShortTimeProducts.physical_arc_bounds (mul_pos hK hε.1) hs).2
  have lower : A*ε^(D-1)<(D:ℝ)*(physicalArc ε)^(D-1) := by
    have hp := pow_le_pow_left₀ (div_nonneg hε.1.le pi_pos.le) hl (D-1)
    have hpos : 0 < (ε/π)^(D-1) := by positivity
    dsimp only [A]
    rw [mul_assoc,←mul_pow,show (1/π)*ε=ε/π by ring]
    nlinarith only [mul_le_mul_of_nonneg_left hp hD.le,mul_pos hD hpos]
  have upper : (D:ℝ)*(physicalArc (K*ε))^(D-1)<B*ε^(D-1) := by
    have hp := pow_le_pow_left₀ (physicalArc_spec (mul_pos hK hε.1) hs).1.1.le hu (D-1)
    have hpos : 0 < (K*ε/2)^(D-1) := by positivity
    dsimp only [B]
    rw [mul_assoc (2*(D:ℝ)),←mul_pow,show (K/2)*ε=K*ε/2 by ring]
    nlinarith only [mul_le_mul_of_nonneg_left hp hD.le,mul_pos hD hpos]
  filter_upwards [hex a,hL.eventually_const_lt lower,hU.eventually_lt_const upper,
    eventually_ge_atTop a] with T hband hlow hhigh hT
  refine ⟨?_,hband⟩
  intro s hs'
  refine ⟨hlow.le.trans (visitFraction_mono H (Nat.zero_le s) ε a T hT),le_trans ?_ hhigh.le⟩
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  exact inter_subset_inter_left _ fun t ht => hcontrol t ε s (by dsimp [N] at hs'; omega) ht

#print axioms gaussian_spanning_occupation_threshold

/-- On every time tail, a uniform linear comparison with scalar error
exists exactly for the budgets below N−1. The counterexamples at and
above N−1 occur at arbitrarily small positive precision. -/
theorem gaussian_scalar_comparison_iff :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ (a η : ℝ), 0 < η → ∀ s : ℕ,
        (∃ L > (0:ℝ), ∀ t ≥ a, ∀ ε ∈ Ioo 0 η,
          t ∈ visitSet H s ε → t ∈ visitSet H 0 (L*ε)) ↔ s+1 < N := by
  filter_upwards [gaussian_two_tolerance_spanning_occupation,
    DisconnectedReturns.gaussian_disconnected_scalar_return] with ω hocc hstab k
  intro N H a η hη s
  constructor
  · rintro ⟨L,hL,h⟩
    by_contra! hbig
    obtain ⟨B,C,hB,hC,hband⟩ := hocc k
    have hsqrt : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using (continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have heta : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 η := Ioo_mem_nhdsGT hη
    obtain ⟨ε,hε,he⟩ := (hband.and (heta.and
      (hsqrt.eventually_lt_const (div_pos hB hL)))).exists
    have hsmall : L*ε ≤ B*sqrt ε := by
      have hb := (lt_div_iff₀ hL).mp he.2
      have hh := mul_le_mul_of_nonneg_right hb.le (sqrt_nonneg ε)
      rw [mul_comm (sqrt ε) L,mul_assoc,←sq,Real.sq_sqrt he.1.1.le] at hh
      exact hh
    obtain ⟨T,hT⟩ := (hε a).exists
    let E := (exactCount H ε (N-1)∩exactCount H (B*sqrt ε) (N-1))∩Icc a T
    have hne : E.Nonempty := by
      by_contra hn
      have hzero : volume.real E=0 := by rw [Set.not_nonempty_iff_eq_empty.mp hn,measureReal_empty]
      change C*sqrt ε*ε^(2^N-2:ℕ) ≤ volume.real E/(T-a) at hT
      rw [hzero,zero_div] at hT
      exact (show 0 < C*sqrt ε*ε^(2^N-2:ℕ) from by have := he.1.1; positivity).not_ge hT
    obtain ⟨t,⟨ht,hweak⟩,hat,_⟩ := hne
    have hit := h t hat ε he.1 ((ht s).mpr (by omega))
    obtain ⟨z,hz,Q,hQ,hfit⟩ := hit
    have hbad := (hweak 0).mp ⟨z,hz,Q,hQ,hfit.trans hsmall⟩
    dsimp [N] at hbad
    omega
  · intro hs
    obtain ⟨A,hA,h⟩ := hstab (k+1)
    exact ⟨A,hA,fun t _ ε _ => h t ε s (by dsimp [N] at hs; omega)⟩

#print axioms gaussian_scalar_comparison_iff
end
end GaloisForLFunctions.HTGeometry.SpanningOccupation
