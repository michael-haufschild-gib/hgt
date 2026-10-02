import GaloisForLFunctions.RHTower.ThetaCuspImaginaryEndpoint
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# All-order flatness of the complete source at the imaginary odd cusp

The modular odd-cusp estimate survives the finite higher chain rule, the
potential's exponential factor, and the source Ward operator. No source
atom is discarded. The result applies at every derivative order.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.ThetaImaginaryArc

private def cuspMap (z : ℂ) : ℂ := 1 + Complex.I * Complex.exp (2*z)

private theorem contDiff_cuspMap (n : ℕ) : ContDiff ℂ n cuspMap := by
  unfold cuspMap
  fun_prop

private theorem potential_cuspMap :
    Potential = fun z => Complex.exp (z/2) * (oddTheta ∘ cuspMap) z := by
  funext z
  simp only [Potential, oddTheta, cuspMap, Function.comp_apply]
  congr 1
  simpa only [show (1:ℂ)+(1+Complex.I*Complex.exp (2*z)) =
    2+Complex.I*Complex.exp (2*z) by ring]
    using (jacobiTheta_two_add (Complex.I*Complex.exp (2*z))).symm

private theorem tendsto_axis_point :
    Tendsto (fun t : ℝ => (t:ℂ)*Complex.I) (𝓝[<] arcEnd)
      (𝓝 ((arcEnd:ℂ)*Complex.I)) :=
  (by fun_prop : Continuous (fun t : ℝ => (t:ℂ)*Complex.I)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

private theorem tendsto_cusp_composite_jet (m : ℕ) :
    Tendsto (fun t : ℝ => iteratedDeriv m (oddTheta ∘ cuspMap) ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
  have hlim (c : OrderedFinpartition m) :
      Tendsto (fun t : ℝ => iteratedDeriv c.length oddTheta (cuspMap ((t:ℂ)*Complex.I)) *
        ∏ j, iteratedDeriv (c.partSize j) cuspMap ((t:ℂ)*Complex.I))
        (𝓝[<] arcEnd) (𝓝 0) := by
    have hodd := tendsto_oddTheta_axis c.length
    have hprod := tendsto_finsetProd Finset.univ (fun j _ =>
      ((contDiff_cuspMap (c.partSize j)).continuous_iteratedDeriv _ le_rfl).continuousAt.tendsto.comp
        tendsto_axis_point)
    simpa only [arcOffset_eq, cuspMap, zero_mul, Function.comp_apply] using hodd.mul hprod
  have hs := tendsto_finsetSum Finset.univ (fun c _ => hlim c)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  have hc : 0 < (cuspMap ((t:ℂ)*Complex.I)).im := by
    simpa only [cuspMap, ← arcOffset_eq] using (arcOffset_cone ht).1
  exact (iteratedDeriv_comp_eq_sum_orderedFinpartition
    (n := (m:ℕ)) (analytic_oddTheta _ hc).contDiffAt
    (contDiff_cuspMap m).contDiffAt le_rfl).symm

/-- Every complex potential derivative vanishes at the imaginary odd-cusp endpoint. -/
theorem tendsto_potential_iteratedDeriv_axis_zero (m : ℕ) :
    Tendsto (fun t : ℝ => iteratedDeriv m Potential ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
  let E : ℂ → ℂ := fun z => Complex.exp (z/2)
  have hE (n : ℕ) : ContDiff ℂ n E := by dsimp [E]; fun_prop
  have hlim (j : ℕ) : Tendsto (fun t : ℝ => (m.choose j:ℂ) *
      iteratedDeriv j E ((t:ℂ)*Complex.I) *
      iteratedDeriv (m-j) (oddTheta ∘ cuspMap) ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
    have he := ((hE j).continuous_iteratedDeriv j le_rfl).continuousAt.tendsto.comp
      tendsto_axis_point
    simpa only [mul_zero, Function.comp_apply] using (he.const_mul (m.choose j:ℂ)).mul
      (tendsto_cusp_composite_jet (m-j))
  have hs := tendsto_finsetSum (Finset.range (m+1)) (fun j _ => hlim j)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  have hc : 0 < (cuspMap ((t:ℂ)*Complex.I)).im := by
    simpa only [cuspMap, ← arcOffset_eq] using (arcOffset_cone ht).1
  rw [potential_cuspMap]
  exact (iteratedDeriv_fun_mul (hE m).contDiffAt
    ((analytic_oddTheta _ hc).contDiffAt.comp _ (contDiff_cuspMap m).contDiffAt)).symm

/-- Every derivative of the complete theta source vanishes at the odd cusp. -/
theorem tendsto_source_iteratedDeriv_axis_zero (m : ℕ) :
    Tendsto (fun t : ℝ => iteratedDeriv m thetaCuspStripSource ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
  have heq : EqOn thetaCuspStripSource
      (fun z => (1/2:ℂ) * (deriv (deriv Potential) z - (1/4:ℂ)*Potential z))
      thetaCuspStrip := by
    intro z hz
    rw [source_complex_ward hz]
    ring
  have hid {z : ℂ} (hz : z ∈ thetaCuspStrip) :
      iteratedDeriv m thetaCuspStripSource z =
        (1/2:ℂ) * (iteratedDeriv (m+2) Potential z - (1/4:ℂ)*iteratedDeriv m Potential z) := by
    rw [heq.iteratedDeriv_of_isOpen isOpen_thetaCuspStrip m hz,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_sub (analytic_potential.deriv.deriv _ hz).contDiffAt
        (contDiffAt_const.mul (analytic_potential _ hz).contDiffAt),
      iteratedDeriv_const_mul_field]
    simp only [show m+2 = (m+1)+1 by omega, iteratedDeriv_succ']
  have ht := ((tendsto_potential_iteratedDeriv_axis_zero (m+2)).sub
    ((tendsto_potential_iteratedDeriv_axis_zero m).const_mul (1/4:ℂ))).const_mul (1/2:ℂ)
  simp only [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  exact (hid (axis_mem_strip ht.1.le ht.2)).symm

/-- Flatness is retained by the full reflection product at the center. -/
theorem tendsto_sourceSquare_iteratedDeriv_axis_zero (m : ℕ) :
    Tendsto (fun t : ℝ => iteratedDeriv m
      (fun z => thetaCuspStripSource z * thetaCuspStripSource z) ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
  have hlim (j : ℕ) : Tendsto (fun t : ℝ => (m.choose j:ℂ) *
      iteratedDeriv j thetaCuspStripSource ((t:ℂ)*Complex.I) *
      iteratedDeriv (m-j) thetaCuspStripSource ((t:ℂ)*Complex.I))
      (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_source_iteratedDeriv_axis_zero j).const_mul (m.choose j:ℂ)).mul
        (tendsto_source_iteratedDeriv_axis_zero (m-j))
  have hs := tendsto_finsetSum (Finset.range (m+1)) (fun j _ => hlim j)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  have ha : ContDiffAt ℂ m thetaCuspStripSource ((t:ℂ)*Complex.I) :=
    (analyticOnNhd_thetaCuspStripSource _ (axis_mem_strip ht.1.le ht.2)).contDiffAt
  exact (iteratedDeriv_fun_mul ha ha).symm

end RHTower.ThetaImaginaryArc
