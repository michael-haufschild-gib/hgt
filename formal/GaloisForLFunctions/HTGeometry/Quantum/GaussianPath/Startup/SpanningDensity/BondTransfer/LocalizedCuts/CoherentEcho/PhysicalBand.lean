import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.Balance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.Scales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.ContinuousRadius
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.FourthPower.PhysicalBand

/-! # A fourth-power physical gate excess from order K⁻⁹⁄⁴⁹ -/
open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- On all sufficiently long prefixes of one Gaussian draw, the true
quarter-error complexity exceeds (1+b t⁴)(K−1) whenever t≤1 and
(K−1)⁹ t⁴⁹ exceeds a fixed constant. -/
theorem gaussian_coherent_quartic_band :
    ∃ b>(0:ℝ), ∃ L>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ t∈Ioc (0:ℝ) 1, L≤N^9*t^49 → ∀ k : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1+b*t^4)*N<(k:ℝ) := by
  obtain ⟨c,hc,hrep⟩ := gaussian_fourth_power_repeats
  obtain ⟨d,hd,C,hC,hweak⟩ := gaussian_relative_weak_upper
  obtain ⟨a,ha,D,hD,hbalance⟩ := coherent_quartic_balance hc hC
  obtain ⟨B,_,hcap⟩ := gaussian_coordinate_window
  obtain ⟨b,hb,hband⟩ := gaussian_polynomial_fourth_power_band
  refine ⟨min (c/2) b,lt_min (half_pos hc) hb,D^9,pow_pos hD 9,?_⟩
  filter_upwards [hrep,hweak,hcap,hband] with ω hr hw hx he
  filter_upwards [hr,hw,hx,he,eventual_coherent_scales ha hd hD] with n hr hw hx he hs
  intro N t ht htime k hk
  have hN : 0≤N := Nat.cast_nonneg _
  have mono (x y : ℝ) (h : x≤y) : (1+x*t^4)*N≤(1+y*t^4)*N :=
    mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right h (pow_nonneg ht.1.le 4))) hN
  by_cases h : (1/(prefixIndex n:ℝ))^12≤t
  · exact (mono _ _ (min_le_right ..)).trans_lt (he.2.2.2.2 t ⟨h,ht.2⟩ k hk)
  let y := t^(1/9:ℝ)
  have hy : 0<y := rpow_pos_of_pos ht.1 _
  have hy9 : y^9=t := by dsimp only [y]; rw [←rpow_natCast,←rpow_mul ht.1.le]; norm_num
  have hy₁ : y≤1 := by
    by_contra! hg
    exact ht.2.not_gt (hy9 ▸ one_lt_pow₀ hg (by decide : 9≠0))
  have hdate : D≤N*y^49 := by
    have heq : (N*y^49)^9=N^9*t^49 := by rw [←hy9]; ring
    by_contra! hh
    exact htime.not_gt (heq ▸ pow_lt_pow_left₀ hh (mul_nonneg hN (pow_nonneg hy.le 49)) (by decide : 9≠0))
  obtain ⟨hm,hlog,hvar⟩ := hs y ⟨hy,hy₁⟩ (by rw [hy9]; exact (lt_of_not_ge h).le) hdate
  let g := a*y^4
  have hg : g∈Ioc (0:ℝ) 1 := ⟨mul_pos ha.1 (pow_pos hy 4),
    (mul_le_mul ha.2 (pow_le_one₀ hy.le hy₁) (pow_nonneg hy.le 4) zero_le_one).trans_eq (one_mul 1)⟩
  have hw' := hw g hg hm hlog
  obtain ⟨z,hz,F,hF,hfit⟩ := hk
  have hr' := hr t ht F z hz hfit
  have hB : 0≤coordinateCap B n := by unfold coordinateCap; positivity
  have hcap' : 43*coordinateCap B n≤(prefixIndex n:ℝ) := by linarith only [hx.2,hB]
  have htail : 2000000*(43*coordinateCap B n)^2*y^5≤a := by
    have hh := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤43) hB) hcap' 2
    linarith only [mul_le_mul_of_nonneg_right hh (pow_nonneg hy.le 5),hvar]
  have hcost := hbalance (pathPauliDisorderShell ω n) y (coordinateCap B n) F z hy hy₁ hB hx.1
    hdate htail hw' hz (by rw [hy9]; exact hfit) (by rw [hy9]; exact hr')
  rw [hy9] at hcost
  exact (mono _ _ (min_le_left ..)).trans_lt (hcost.trans_le (Nat.cast_le.mpr hF))

#print axioms gaussian_coherent_quartic_band
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
