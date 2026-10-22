import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceBoundaryValues

/-! The actual weighted derivative limits fixing the physical radial Wronskian. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem normalizable_weightedFirst (w chi : ℂ) {z : ℝ} (hz : z < 1) :
    (Real.sqrt (1-z):ℂ)*normalizableFirst w chi z =
      powerFirst (w/2) z*(1-z:ℂ)*gaussFactor w chi true (1-z)-
      (1/2:ℂ)*power (w/2) z*gaussFactor w chi true (1-z)-
      power (w/2) z*(1-z:ℂ)*gaussFirst w chi true (1-z) := by
  have hx : 0 ≤ 1-z := sub_nonneg.mpr hz.le
  have hx0 : (1-(z:ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz))
  have hs : (Real.sqrt (1-z):ℂ)^(2 : ℕ)=(1-z:ℂ) := by exact_mod_cast Real.sq_sqrt hx
  dsimp [normalizableFirst,dressFirst,outerFactor,outerFirst]
  rw [show powerFirst (1/2) (1-z)=(1/2:ℂ)*power (1/2) (1-z)/((1-z:ℝ):ℂ) from rfl,
    power_half_eq_sqrt hx]
  push_cast
  field_simp [hx0]
  ring_nf
  simp only [hs]
  ring

/-- The physical normalizable derivative has the exact nonzero square-root
edge -1/2, including differentiation of the horizon dressing. -/
theorem normalizableFirst_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => (Real.sqrt (1-z):ℂ)*normalizableFirst w chi z)
      (𝓝[<] (1:ℝ)) (𝓝 (-1/2:ℂ)) := by
  have hP := power_tendsto_one (w/2)
  have hD := powerFirst_tendsto_one (w/2)
  have hF := reversedGauss_boundary h
  have hF1 := reversedGaussFirst_boundary h
  have hx : Tendsto (fun z : ℝ => (1-z:ℂ)) (𝓝 (1:ℝ)) (𝓝 (0:ℂ)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℂ)) (𝓝 1) (𝓝 1)).sub
      (Complex.continuous_ofReal.tendsto (1:ℝ)))
  have hhalf : Tendsto (fun _ : ℝ => (1/2:ℂ)) (𝓝 1) (𝓝 (1/2:ℂ)) := tendsto_const_nhds
  have ht := (((hD.mul hx).mul hF).sub ((hhalf.mul hP).mul hF)).sub ((hP.mul hx).mul hF1)
  have ht' : Tendsto
      (fun z : ℝ => powerFirst (w/2) z*(1-z:ℂ)*gaussFactor w chi true (1-z)-
        (1/2:ℂ)*power (w/2) z*gaussFactor w chi true (1-z)-
        power (w/2) z*(1-z:ℂ)*gaussFirst w chi true (1-z))
      (𝓝[<] (1:ℝ)) (𝓝 (-1/2:ℂ)) := by
    convert! ht.mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left) using 1
    norm_num
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (normalizable_weightedFirst w chi hz).symm

/-- The physical horizon derivative has a finite weighted boundary limit;
the derivative of its dressing contributes zero to that edge. -/
theorem horizonFirst_boundary_weighted {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (fun z : ℝ => (Real.sqrt (1-z):ℂ)*horizonFirst w chi z)
      (𝓝[<] (1:ℝ))
      (𝓝 ((Real.sqrt Real.pi:ℂ)*(Complex.Gamma (gaussC w)/
        (Complex.Gamma (gaussA w chi)*Complex.Gamma (gaussB w chi))))) := by
  have hD := (powerFirst_tendsto_one (w/2)).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)
  have hP := (power_tendsto_one (w/2)).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)
  have hs : Tendsto (fun z : ℝ => (Real.sqrt (1-z):ℂ)) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ => (Real.sqrt (1-z):ℂ)) := by fun_prop
    simpa using (hc.tendsto 1).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)
  have he := horizonFirst_boundary h
  rw [nhdsWithin_Ico_eq_nhdsLT (show (0:ℝ)<1 by norm_num)] at he
  have ht := ((hD.mul hs).mul (horizonFactor_boundary h)).add (hP.mul he)
  simp only [mul_zero,zero_mul,one_mul,zero_add] at ht
  convert! ht using 1
  funext z
  dsimp [horizonFirst,dressFirst]
  ring

end
end RHTower.D4BMLaplaceRadial
