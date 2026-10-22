import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNonstationaryMoment

/-! Integration by parts for the same original finite part and its monotone physical phase. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationaryMultiplier (x : ℝ) : ℂ := (2-(x:ℂ))/(2+3*(x:ℂ))

theorem nonstationaryMultiplier_hasDerivAt {x : ℝ} (hx : -(1/2) < x) :
    HasDerivAt nonstationaryMultiplier (-8/(2+3*(x:ℂ))^(2 : ℕ)) x := by
  have hb : (2+3*(x:ℂ)) ≠ 0 := by
    exact_mod_cast (show (2+3*x:ℝ) ≠ 0 by linarith)
  have h2 : HasDerivAt (fun z : ℂ => 2-z) (-1) (x:ℂ) := by
    simpa only [zero_sub,Pi.sub_apply,id_eq] using! (hasDerivAt_const (x:ℂ) (2:ℂ)).sub (hasDerivAt_id (x:ℂ))
  have h3 : HasDerivAt (fun z : ℂ => 2+3*z) 3 (x:ℂ) := by
    simpa only [zero_add,mul_one,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (x:ℂ) (2:ℂ)).add ((hasDerivAt_id (x:ℂ)).const_mul 3)
  exact ((h2.div h3 hb).comp_ofReal).congr_deriv (by ring)

def nonstationaryPrimitiveCore (P : ℂ[X]) (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  power (-4*w) (2-x)*nonstationaryMultiplier x*nonstationaryWeight P j x

def nonstationaryPrimitiveCoreFirst (P : ℂ[X]) (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  (-powerFirst (-4*w) (2-x)*nonstationaryMultiplier x+
    power (-4*w) (2-x)*(-8/(2+3*(x:ℂ))^(2 : ℕ)))*nonstationaryWeight P j x+
    power (-4*w) (2-x)*nonstationaryMultiplier x*nonstationaryWeightFirst P j x

theorem nonstationaryPrimitiveCore_hasDerivAt (P : ℂ[X]) (j : ℕ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) 2) :
    HasDerivAt (nonstationaryPrimitiveCore P j w) (nonstationaryPrimitiveCoreFirst P j w x) x := by
  have hp : HasDerivAt (fun y : ℝ => power (-4*w) (2-y)) (-powerFirst (-4*w) (2-x)) x := by
    simpa only [zero_sub,neg_one_smul,Function.comp_apply,Pi.sub_apply,id_eq] using!
      (power_derivatives (-4*w) (by linarith [hx.2] : 0 < 2-x)).1.scomp x
        ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x))
  exact (hp.mul (nonstationaryMultiplier_hasDerivAt hx.1)).mul (nonstationaryWeight_hasDerivAt P j hx)

theorem nonstationaryPrimitiveCore_zero (P : ℂ[X]) (j : ℕ) (w : ℂ) :
    nonstationaryPrimitiveCore P j w 0=nonstationaryCore P j w 0 := by
  norm_num [nonstationaryPrimitiveCore,nonstationaryCore,nonstationaryMultiplier]

def nonstationaryPrimitive (P : ℂ[X]) (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  power (w+1) x*nonstationaryPrimitiveCore P j w x

theorem nonstationaryPrimitive_hasDerivAt (P : ℂ[X]) (j : ℕ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Ioc (0:ℝ) 1) :
    HasDerivAt (nonstationaryPrimitive P j w)
      ((w+1)*((x:ℂ)^w*nonstationaryCore P j w x)+
        (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x) x := by
  have hxR : x ∈ Ioo (-(1/2):ℝ) 2 := by constructor <;> linarith [hx.1,hx.2]
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  have ha : (2-(x:ℂ)) ≠ 0 := by exact_mod_cast (show (2-x:ℝ) ≠ 0 by linarith [hx.2])
  have hb : (2+3*(x:ℂ)) ≠ 0 := by exact_mod_cast (show (2+3*x:ℝ) ≠ 0 by linarith [hx.1])
  have hb' : (2+(x:ℂ)*3) ≠ 0 := by simpa only [mul_comm] using hb
  have hp : (x:ℂ)^(w+1)=(x:ℂ)^w*(x:ℂ) := by
    rw [Complex.cpow_add _ _ hx0,Complex.cpow_one]
  have h := (power_derivatives (w+1) hx.1).1.mul (nonstationaryPrimitiveCore_hasDerivAt P j w hxR)
  apply h.congr_deriv
  dsimp only [nonstationaryCore]
  rw [nonstationaryWeight_step P j hxR]
  dsimp only [nonstationaryPrimitiveCore,nonstationaryPrimitiveCoreFirst,nonstationaryMultiplier,powerFirst,power]
  simp only [hp,Complex.ofReal_sub,Complex.ofReal_ofNat]
  field_simp [hx0,ha,hb,hb']
  ring

theorem nonstationaryPrimitive_one (P : ℂ[X]) (j : ℕ) (w : ℂ) :
    nonstationaryPrimitive P j w 1=nonstationaryWeight P j 1/5 := by
  norm_num [nonstationaryPrimitive,nonstationaryPrimitiveCore,nonstationaryMultiplier,power]
  ring

/-- Exact recurrence of the original finite part, with its boundary normalization retained. -/
theorem nonstationaryMoment_recurrence (P : ℂ[X]) (j : ℕ) (w : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    (w+1)*nonstationaryMoment P j w+
      nonstationaryMoment (nonstationaryWeightStep P j) (j+2) w=nonstationaryWeight P j 1/5 := by
  have hz : nonstationaryCore (nonstationaryWeightStep P j) (j+2) w 0=0 := by
    simp only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,nonstationaryWeightStep_zero,zero_div,mul_zero]
  have hs := nonstationaryMoment_cutoff (nonstationaryWeightStep P j) (j+2) w hw hw1
  simp only [hz,zero_mul,zero_div,add_zero] at hs
  have hl := ((nonstationaryMoment_cutoff P j w hw hw1).const_mul (w+1)).add hs
  have hg := nonstationaryPrimitiveCore_hasDerivAt P j w (by constructor <;> norm_num : (0:ℝ) ∈ Ioo (-(1/2):ℝ) 2)
  have hr := ((fundamentalMoment_cpow_mul_sub_tendsto hg hw).neg).const_add (nonstationaryWeight P j 1/5)
  simp only [neg_zero,add_zero] at hr
  apply tendsto_nhds_unique hl
  apply hr.congr'
  have he1 : ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin,he1.filter_mono nhdsWithin_le_nhds] with e he he1
  have hi (Q : ℂ[X]) (k : ℕ) : IntervalIntegrable (fun x : ℝ => (x:ℂ)^w*nonstationaryCore Q k w x) volume e 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc he1.le
    intro x hx
    exact ((power_derivatives w (he.trans_le hx.1)).1.continuousAt.mul
      (nonstationaryCore_hasDerivAt Q k w
        (by constructor <;> linarith [show 0 < e from he,hx.1,hx.2])).continuousAt).continuousWithinAt
  have hf : (∫ x in e..1, (w+1)*((x:ℂ)^w*nonstationaryCore P j w x)+
      (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x) =
      nonstationaryPrimitive P j w 1-nonstationaryPrimitive P j w e := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le he1.le] at hx
      exact nonstationaryPrimitive_hasDerivAt P j w ⟨he.trans_le hx.1,hx.2⟩
    · exact ((hi P j).const_mul (w+1)).add (hi (nonstationaryWeightStep P j) (j+2))
  rw [intervalIntegral.integral_add ((hi P j).const_mul (w+1)) (hi (nonstationaryWeightStep P j) (j+2)),
    intervalIntegral.integral_const_mul,nonstationaryPrimitive_one,nonstationaryPrimitive,power] at hf
  rw [nonstationaryPrimitiveCore_zero]
  calc
    _ = (nonstationaryWeight P j 1/5-(e:ℂ)^(w+1)*nonstationaryPrimitiveCore P j w e)+
        nonstationaryCore P j w 0*(e:ℂ)^(w+1) := by ring
    _ = ((w+1)*(∫ x in e..1, (x:ℂ)^w*nonstationaryCore P j w x)+
        (∫ x in e..1, (x:ℂ)^w*nonstationaryCore (nonstationaryWeightStep P j) (j+2) w x))+
        nonstationaryCore P j w 0*(e:ℂ)^(w+1) := by rw [hf]
    _ = _ := by field_simp [hw1]; ring

end
end RHTower.D4BMJointSource
