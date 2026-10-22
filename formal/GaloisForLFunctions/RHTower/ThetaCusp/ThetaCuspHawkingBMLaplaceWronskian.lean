import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceBoundaryDerivatives

/-! Exact nonzero physical radial Wronskian in the independent-frequency chamber. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def integratingFactor (z : ℝ) : ℂ := (z:ℂ)*power (1/2) (1-z)

def wronskian (w chi : ℂ) (z : ℝ) : ℂ := integratingFactor z*
  (horizon w chi z*normalizableFirst w chi z-horizonFirst w chi z*normalizable w chi z)

private theorem integratingFactor_derivative {z : ℝ} (hz : z < 1) :
    HasDerivAt integratingFactor (power (1/2) (1-z)-(z:ℂ)*powerFirst (1/2) (1-z)) z := by
  have hp := (power_derivatives (1/2) (sub_pos.mpr hz)).1.scomp z ((hasDerivAt_id z).const_sub (1:ℝ))
  convert! ((hasDerivAt_id z).ofReal_comp.mul hp) using 1
  simp [sub_eq_add_neg]

/-- Abel's identity for the actual physical radial solutions. -/
theorem wronskian_derivative {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (wronskian w chi) 0 z := by
  obtain ⟨hH,hH1⟩ := horizon_derivatives h hz
  obtain ⟨hV,hV1⟩ := normalizable_derivatives h hz
  have hp := integratingFactor_derivative hz.2
  have hW := hp.mul ((hH.mul hV1).sub (hH1.mul hV))
  apply hW.congr_deriv
  have hHode := horizon_equation h hz
  have hVode := normalizable_equation h hz
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have hx0 : (1-(z:ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz.2))
  dsimp [D4BMPhysicalMaster.radialJet] at hHode hVode
  dsimp [integratingFactor,powerFirst]
  push_cast
  field_simp [hz0,hx0]
  linear_combination
    2*power (1/2) (1-z)*horizon w chi z*hVode-
      2*power (1/2) (1-z)*normalizable w chi z*hHode

private theorem wronskian_constant {w chi : ℂ} (h : Chamber w chi) {x y : ℝ}
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) : wronskian w chi x=wronskian w chi y := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro z hz
    exact (wronskian_derivative h hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (wronskian_derivative h hz).deriv
  · exact hx
  · exact hy

private theorem wronskian_boundary {w chi : ℂ} (h : Chamber w chi) :
    Tendsto (wronskian w chi) (𝓝[<] (1:ℝ)) (𝓝 (-connection w chi/2)) := by
  have hz : Tendsto (fun z : ℝ => (z:ℂ)) (𝓝[<] (1:ℝ)) (𝓝 (1:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hV := (normalizable_boundary h).mono_left (show 𝓝[<] (1:ℝ) ≤ 𝓝 1 from inf_le_left)
  have ht := hz.mul (((horizon_boundary h).mul (normalizableFirst_boundary h)).sub
    ((horizonFirst_boundary_weighted h).mul hV))
  have ht' : Tendsto
      (fun z : ℝ => (z:ℂ)*(horizon w chi z*((Real.sqrt (1-z):ℂ)*normalizableFirst w chi z)-
        ((Real.sqrt (1-z):ℂ)*horizonFirst w chi z)*normalizable w chi z))
      (𝓝[<] (1:ℝ)) (𝓝 (-connection w chi/2)) := by
    convert! ht using 1
    congr 1
    ring
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  dsimp [wronskian,integratingFactor]
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.le)]
  ring

/-- The actual solution Wronskian equals its Gamma-normalized endpoint value
at every interior radius; no denominator premise is supplied. -/
theorem wronskian_eq {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    wronskian w chi z = -connection w chi/2 := by
  have he : wronskian w chi =ᶠ[𝓝[<] (1:ℝ)] fun _ => wronskian w chi z := by
    have hp : ∀ᶠ t in 𝓝[<] (1:ℝ), 0 < t :=
      (show ∀ᶠ t : ℝ in 𝓝 1, 0 < t from Ioi_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hp] with t ht hp
    exact wronskian_constant h ⟨hp,ht⟩ hz
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' he.symm) (wronskian_boundary h)

theorem wronskian_ne_zero {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    wronskian w chi z ≠ 0 := by
  rw [wronskian_eq h hz]
  exact div_ne_zero (neg_ne_zero.mpr (connection_ne_zero h)) (by norm_num)

end
end RHTower.D4BMLaplaceRadial
