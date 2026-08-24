import GaloisForLFunctions.HTGeometry.MultiplicativeTheta
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# Uniform zero-nome control for q-Pochhammer and multiplicative theta
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact total norm mass of the q-Pochhammer defect. -/
theorem tsum_norm_qPochhammer_defect (a : ℂ) (q : EulerNome) :
    ∑' n : ℕ, ‖-(a * (q : ℂ) ^ n)‖ =
      ‖a‖ * (1 - ‖(q : ℂ)‖)⁻¹ := by
  simp only [norm_neg, norm_mul, norm_pow, tsum_mul_left]
  have hgeom : ∑' n : ℕ, ‖(q : ℂ)‖ ^ n = (1 - ‖(q : ℂ)‖)⁻¹ := by
    apply tsum_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using q.norm_lt_one
  rw [hgeom]

/-- Global quantitative zero-nome estimate for one q-Pochhammer product. -/
theorem norm_qPochhammerInf_sub_one_le (a : ℂ) (q : EulerNome) :
    ‖qPochhammerInf a q - 1‖ ≤
      Real.exp (‖a‖ * (1 - ‖(q : ℂ)‖)⁻¹) - 1 := by
  have hprod : HasProd (fun n : ℕ => 1 + -(a * (q : ℂ) ^ n))
      (qPochhammerInf a q) := by
    simpa only [sub_eq_add_neg, qPochhammerInf] using
      (qPochhammer_multipliable a q).hasProd
  have hsum : Summable (fun n : ℕ => ‖-(a * (q : ℂ) ^ n)‖) := by
    simpa only [norm_neg] using (qPochhammer_summable_defect a q).norm
  exact norm_tprod_one_add_sub_one_le
    (u := fun n : ℕ => -(a * (q : ℂ) ^ n))
    (P := qPochhammerInf a q) hprod hsum
    (by rw [tsum_norm_qPochhammer_defect])

/-- Moving-parameter q-Pochhammer products converge to one whenever both the parameter and nome
converge to zero. -/
theorem tendsto_qPochhammerInf_one_of_tendsto_zero
    {ι : Type*} {l : Filter ι} (a : ι → ℂ) (q : ι → EulerNome)
    (ha : Tendsto a l (nhds 0))
    (hq : Tendsto (fun i => ((q i : EulerNome) : ℂ)) l (nhds 0)) :
    Tendsto (fun i => qPochhammerInf (a i) (q i)) l (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hqnorm : Tendsto (fun i => ‖((q i : EulerNome) : ℂ)‖) l (nhds 0) := by
    simpa using hq.norm
  have hden : Tendsto (fun i => (1 - ‖((q i : EulerNome) : ℂ)‖)⁻¹) l (nhds 1) := by
    have hsub : Tendsto (fun i => 1 - ‖((q i : EulerNome) : ℂ)‖) l (nhds (1 : ℝ)) := by
      convert (tendsto_const_nhds.sub hqnorm) using 1 <;> norm_num
    simpa using hsub.inv₀ one_ne_zero
  have hmass : Tendsto
      (fun i => ‖a i‖ * (1 - ‖((q i : EulerNome) : ℂ)‖)⁻¹) l (nhds 0) := by
    convert ha.norm.mul hden using 1 <;> norm_num
  have hexp : Tendsto
      (fun i => Real.exp (‖a i‖ * (1 - ‖((q i : EulerNome) : ℂ)‖)⁻¹) - 1)
      l (nhds 0) := by
    have hone : Tendsto (fun _ : ι => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
    convert (Real.continuous_exp.continuousAt.tendsto.comp hmass).sub hone using 1 <;> norm_num
  exact squeeze_zero (fun i => norm_nonneg _)
    (fun i => norm_qPochhammerInf_sub_one_le (a i) (q i)) hexp

/-- Multiplicative theta converges to one when both q-Pochhammer arguments and the nome vanish. -/
theorem tendsto_multiplicativeTheta_one_of_tendsto_zero
    {ι : Type*} {l : Filter ι} (a : ι → ℂ) (b : ι → ℂ) (q : ι → EulerNome)
    (ha : Tendsto a l (nhds 0)) (hb : Tendsto b l (nhds 0))
    (hq : Tendsto (fun i => ((q i : EulerNome) : ℂ)) l (nhds 0))
    (hab : ∀ i, ((q i : EulerNome) : ℂ) / a i = b i) :
    Tendsto (fun i => multiplicativeTheta (q i) (a i)) l (nhds 1) := by
  have hfirst := tendsto_qPochhammerInf_one_of_tendsto_zero a q ha hq
  have hsecond := tendsto_qPochhammerInf_one_of_tendsto_zero b q hb hq
  simpa only [multiplicativeTheta, hab, one_mul] using hfirst.mul hsecond

end

end GaloisForLFunctions.HTGeometry
