import GaloisForLFunctions.RHTower.SteinhausSuperConstant
import GaloisForLFunctions.RHTower.SteinhausRatePowerAsymptotic

/-!
# The super-critical regime

For `1/2 < α < 1` the scaling identity turns the small-tilt behaviour of the cumulant into the
convergence of a truncated integral:

`Λ_α(λ)/λ^{1/α} = ∫₀^{λ^{−1/α}} log I₀(w_α(u)) du → K_α`.

Feeding this into the Legendre power law gives the card's third regime,

`I_α(q)/q^{1/(1−α)} → (1−α) α^{α/(1−α)} K_α^{−α/(1−α)} = C_α`.
-/

open MeasureTheory Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The constant is strictly positive. -/
theorem rvSuperConst_pos {α : ℝ} (hα2 : 1 / 2 < α) (hα : α < 1) : 0 < rvSuperConst α := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ hx3
    exact absurd hx3 (not_lt.2 hx2)
  have hunion : rvSuperConst α
      = (∫ u in Ioc (0 : ℝ) 1, steinhausLogLaplace (weightProfile α u))
        + ∫ u in Ioi (1 : ℝ), steinhausLogLaplace (weightProfile α u) := by
    rw [rvSuperConst, hsplit]
    exact setIntegral_union hdisj measurableSet_Ioi
      (integrableOn_profileCumulant_Ioc hα) (integrableOn_profileCumulant_Ioi_one hα2)
  have htail : 0 ≤ ∫ u in Ioi (1 : ℝ), steinhausLogLaplace (weightProfile α u) :=
    setIntegral_nonneg measurableSet_Ioi fun u _ => steinhausLogLaplace_nonneg _
  have hhead : 0 < ∫ u in Ioc (0 : ℝ) 1, steinhausLogLaplace (weightProfile α u) := by
    have hint : IntervalIntegrable
        (fun u : ℝ => steinhausLogLaplace (weightProfile α u)) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact integrableOn_profileCumulant_Ioc hα
    have hpos : 0 < ∫ u in (0:ℝ)..1, steinhausLogLaplace (weightProfile α u) := by
      refine intervalIntegral.intervalIntegral_pos_of_pos_on hint ?_ (by norm_num)
      intro u hu
      exact steinhausLogLaplace_pos (weightProfile_pos hα hu.1).ne'
    rwa [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] at hpos
  rw [hunion]
  linarith

/-- **The super-critical cumulant asymptotic**, the card's `(25)`. -/
theorem tendsto_rvCumulant_div_rpow_super {α : ℝ} (hα2 : 1 / 2 < α) (hα : α < 1) :
    Tendsto (fun lam : ℝ => rvCumulant α lam / lam ^ (1 / α)) (𝓝[>] (0 : ℝ))
      (𝓝 (rvSuperConst α)) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hmain := tendsto_rvTailIntegral hα2 hα (b := fun lam : ℝ => lam ^ (-(1 / α)))
    (tendsto_rpow_neg_inv_atTop hα0)
  refine Tendsto.congr' ?_ hmain
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam0 : (0 : ℝ) < lam := hlam
  have hp : (0 : ℝ) < lam ^ (1 / α) := Real.rpow_pos_of_pos hlam0 _
  rw [rvCumulant_eq_rpow_mul_tail hα0 hlam0]
  field_simp

/-- The card's super-critical constant `C_α`. -/
def rvSuperRateConst (α : ℝ) : ℝ :=
  (1 - α) * α ^ (α / (1 - α)) * rvSuperConst α ^ (-(α / (1 - α)))

/-- The Legendre constant at exponent `1/α` is the card's `C_α`. -/
theorem rvLegConst_inv_eq {α : ℝ} (hα0 : 0 < α) (hα : α < 1) {A : ℝ} (hA : 0 < A) :
    rvLegConst (1 / α) A = (1 - α) * α ^ (α / (1 - α)) * A ^ (-(α / (1 - α))) := by
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  have h1 : (1 : ℝ) / α - 1 = (1 - α) / α := by field_simp
  have h2 : (1 : ℝ) / α / (1 / α - 1) = 1 / (1 - α) := by
    rw [h1]; field_simp
  have h3 : (1 : ℝ) / (1 / α - 1) = α / (1 - α) := by
    rw [h1]; field_simp
  rw [rvLegConst, h2, h3, h1]
  have hinv : ((1 : ℝ) / α) ^ (-(1 / (1 - α))) = α ^ (1 / (1 - α)) := by
    rw [one_div α, Real.inv_rpow hα0.le, Real.rpow_neg hα0.le, inv_inv]
  rw [hinv]
  have hsplit : α ^ (α / (1 - α)) * α = α ^ (1 / (1 - α)) := by
    have hadd := (Real.rpow_add hα0 (α / (1 - α)) 1).symm
    rw [Real.rpow_one] at hadd
    rw [hadd]
    congr 1
    field_simp
    ring
  rw [← hsplit]
  have hAk : (0 : ℝ) < A ^ (-(α / (1 - α))) := Real.rpow_pos_of_pos hA _
  field_simp

/-- **The super-critical regime of the rate function**, the card's `(6)` third line. -/
theorem tendsto_rvRate_div_rpow_super {α : ℝ} (hα2 : 1 / 2 < α) (hα : α < 1) :
    Tendsto (fun q : ℝ => rvRate α q / q ^ (1 / (1 - α))) (𝓝[>] (0 : ℝ))
      (𝓝 (rvSuperRateConst α)) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hα1 : (0 : ℝ) < 1 - α := by linarith
  have hp : (1 : ℝ) < 1 / α := by
    rw [lt_div_iff₀ hα0]; linarith
  have hA := rvSuperConst_pos hα2 hα
  have hmain := tendsto_rvRate_div_rpow (α := α) (p := 1 / α) (A := rvSuperConst α) hα hp hA
    (tendsto_rvCumulant_div_rpow_super hα2 hα)
  have h1 : (1 : ℝ) / α - 1 = (1 - α) / α := by field_simp
  have h2 : (1 : ℝ) / α / (1 / α - 1) = 1 / (1 - α) := by rw [h1]; field_simp
  rw [h2, rvLegConst_inv_eq hα0 hα hA] at hmain
  exact hmain

end

end HTGeometry
