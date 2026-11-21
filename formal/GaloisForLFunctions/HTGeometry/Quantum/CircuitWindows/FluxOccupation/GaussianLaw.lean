import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.ScaleChoice
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.WindowFraction

/-! # Exponentially many more linear-budget than scalar visits at fixed error -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open SharpOccupation EmptyVisitFlux

/-- At every physical error up to 1/4, the ratio of time affordable with
one path product step to empty-circuit time is eventually at least
√(2ᴺ)/(128πJ), where J=12N−9. The same draw works for every prefix. -/
theorem gaussian_fixed_error_occupation_gain :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let D : ℕ := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let J := Fintype.card (PathLabel (k+1))
      ∀ ε : ℝ, 0<ε → ε≤1/4 → ∀ᶠ T : ℝ in atTop,
        sqrt (D:ℝ)*visitFraction H 0 ε 0 T ≤ 128*π*(J:ℝ)*visitFraction H J ε 0 T := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro N D H J ε hε heps
  let u := pathPauliDisorderShell ω (k+1)
  let E := fun j => -H.2.isHermitian.eigenvalues j
  let M := ∑ l : PathLabel (k+1), |u l|
  let x := physicalArc ε
  let y := x-x/(2*(D:ℝ))
  let h := x*sqrt (D:ℝ)/(2*(D:ℝ)*M)
  let R := pairTurnRate E
  let p := (D:ℝ)*x^(D-1)
  have hi := hω k
  have hi' := maximallyProjectiveEnergy_neg hi
  have hR : 0<R := pair_rate_pos E hi'
  have hM : 0<M := by
    by_contra! hzero
    obtain ⟨i,j,hij⟩ := exists_pair_ne (Fin N → Bool)
    have ha := abs_le.mp (path_abs_energy u i)
    have hb := abs_le.mp (path_abs_energy u j)
    exact (hi.injective.ne hij) (by linarith only [hzero,ha.1,ha.2,hb.1,hb.2])
  have hD : 2≤D := by
    change 2≤2^(k+3)
    simpa only [pow_one] using (Nat.pow_le_pow_right (by decide : 0<2) (show 1≤k+3 by omega))
  have hd : (0:ℝ)<D := Nat.cast_pos.mpr (by omega)
  have hsqrt : ε<sqrt 2 := by nlinarith only [heps,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  obtain ⟨hx,hxtol⟩ := physicalArc_spec hε hsqrt
  have hxsmall : x≤1/4 := by linarith only [(ShortTimeProducts.physical_arc_bounds hε hsqrt).2,heps]
  obtain ⟨hy,hyx,hh,hsep,hmargin⟩ := scale_choice hD hx.1 hxsmall hM
  let δ := zeroGateArcTolerance y
  have hy' : y ∈ Icc (0:ℝ) (1/2) := ⟨hy.le,(hyx.trans hx.2).le⟩
  have hx' : x ∈ Icc (0:ℝ) (1/2) := Ioo_subset_Icc_self hx
  have hδ : 0<δ := by
    change 0 < zeroGateArcTolerance y
    rw [show (0:ℝ)=zeroGateArcTolerance 0 by simp [zeroGateArcTolerance]]
    exact strictMonoOn_zeroGateArcTolerance (show (0:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num) hy' hy
  have hδε : δ<ε := (strictMonoOn_zeroGateArcTolerance hy' hx' hyx).trans_eq hxtol
  have hsmall := hδε.trans hsqrt
  obtain ⟨hδx,hδe⟩ := physicalArc_spec hδ hsmall
  have hxy : physicalArc δ=y := strictMonoOn_zeroGateArcTolerance.injOn (Ioo_subset_Icc_self hδx) hy' hδe
  have hrate : 0<y^(D-2)*R := mul_pos (pow_pos hy _) hR
  have hprod := product_fraction_of_flux u hδ hsmall hh.le hi'
    (by rwa [hxy]) (by rwa [hxy]) (hmargin.trans_eq hxtol)
  rw [hxy] at hprod
  have hG := flux_gain hD hx.1 hM (Nat.cast_nonneg J) hR.le (path_pair_turn_lower u)
  have hp : 0<p := mul_pos hd (pow_pos hx.1 _)
  have hscalar := (ShortTimeProducts.scalar_fraction H hi hε hsqrt 0).eventually_lt_const
    (show p<2*p by linarith only [hp])
  filter_upwards [hprod,hscalar] with T hT h0
  have h1 := mul_le_mul_of_nonneg_left h0.le (Real.sqrt_nonneg (D:ℝ))
  have h2 := mul_le_mul_of_nonneg_left hT (show 0 ≤ 64*π*(J:ℝ) by positivity)
  change sqrt (D:ℝ)*p ≤ _ at hG
  linarith only [h1,h2,hG]

#print axioms gaussian_fixed_error_occupation_gain
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
