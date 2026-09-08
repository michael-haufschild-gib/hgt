import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRadialBracket

/-! The exact Wronskian of the two original horizon branches at every nonreal frequency. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Both signs of the actual original horizon solution solve the same radial equation. -/
theorem oppositeHorizon_equation (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (I*w) chi b (horizon (-w) chi b)
      (horizonFirst (-w) chi b) (horizonSecond (-w) chi b) = 0 := by
  have hm : (-w).im ≠ 0 := by simpa using hw
  simpa only [D4BMPhysicalMaster.radialJet,mul_neg,neg_sq] using
    horizon_equation_continued hm hb (chi:=chi)

private theorem horizon_pair_factor (w chi : ℂ) {b : ℝ} (hb : 0 < b) :
    radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon (-w) chi) (horizonFirst (-w) chi) b =
    power (1/2) (1-b) *
      (-w*gaussFactor w chi false b*gaussFactor (-w) chi false b +
        (b:ℂ)*(gaussFactor w chi false b*gaussFirst (-w) chi false b -
          gaussFirst w chi false b*gaussFactor (-w) chi false b)) := by
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hc : power (w/2) b * power (-w/2) b = 1 := by
    rw [power,power,← Complex.cpow_add _ _ hb0,show w/2+-w/2=0 by ring,Complex.cpow_zero]
  calc
    _ = power (1/2) (1-b) * (power (w/2) b * power (-w/2) b) *
      (-w*gaussFactor w chi false b*gaussFactor (-w) chi false b +
        (b:ℂ)*(gaussFactor w chi false b*gaussFirst (-w) chi false b -
          gaussFirst w chi false b*gaussFactor (-w) chi false b)) := by
      dsimp [radialBracket,integratingFactor,horizon,horizonFirst,dress,dressFirst,powerFirst]
      field_simp [hb0]
      ring
    _ = _ := by rw [hc,mul_one]

private theorem horizon_pair_boundary (w chi : ℂ) :
    Tendsto (radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon (-w) chi) (horizonFirst (-w) chi)) (𝓝[>] (0:ℝ)) (𝓝 (-w)) := by
  have hf (v : ℂ) : ContinuousAt (fun b : ℝ => gaussFactor v chi false b) 0 := by
    have hd := (gaussFactor_derivatives_continued (w:=v) (chi:=chi) (z:=0) false (by simp)).1
    exact hd.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hd (v : ℂ) : ContinuousAt (fun b : ℝ => gaussFirst v chi false b) 0 := by
    have h := (gaussFactor_derivatives_continued (w:=v) (chi:=chi) (z:=0) false (by simp)).2
    exact h.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hp : ContinuousAt (fun b : ℝ => power (1/2) (1-b)) 0 := by
    have h := (power_derivatives (1/2) (by norm_num : (0:ℝ)<1)).1.continuousAt
    exact h.comp_of_eq (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hc := hp.mul ((((hf w).const_mul (-w)).mul (hf (-w))).add
    (Complex.continuous_ofReal.continuousAt.mul
      (((hf w).mul (hd (-w))).sub ((hd w).mul (hf (-w))))))
  have ht := hc.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Complex.ofReal_zero,gaussFactor_zero,mul_one,zero_mul,add_zero,
    sub_zero,power,Complex.ofReal_one,Complex.one_cpow,one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (horizon_pair_factor w chi hb).symm

/-- The actual horizon determinant is exactly minus frequency, with no connection premise. -/
theorem original_horizon_wronskian (w chi : ℂ) (hw : w.im ≠ 0)
    {b : ℝ} (hb : b ∈ Ioo 0 1) :
    radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon (-w) chi) (horizonFirst (-w) chi) b = -w := by
  have hc {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :=
    radialBracket_constant w chi
      (fun z hz => (horizon_derivatives_continued hz).1)
      (fun z hz => (horizon_derivatives_continued hz).2)
      (fun z hz => (horizon_derivatives_continued hz).1)
      (fun z hz => (horizon_derivatives_continued hz).2)
      (fun z hz => horizon_equation_continued hw hz)
      (fun z hz => oppositeHorizon_equation w chi hw hz) hx hy
  have he : (radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon (-w) chi) (horizonFirst (-w) chi)) =ᶠ[𝓝[>] (0:ℝ)]
      fun _ => radialBracket (horizon w chi) (horizonFirst w chi)
        (horizon (-w) chi) (horizonFirst (-w) chi) b := by
    have hlt : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x < 1 :=
      (show ∀ᶠ x : ℝ in 𝓝 0, x < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hlt] with x hx hx1
    exact hc ⟨hx,hx1⟩ hb
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' he.symm) (horizon_pair_boundary w chi)

end
end RHTower.D4BMLaplaceRadial
