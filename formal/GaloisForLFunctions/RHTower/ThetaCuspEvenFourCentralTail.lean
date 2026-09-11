import GaloisForLFunctions.RHTower.ThetaCuspScaleEightReflectionError
import GaloisForLFunctions.RHTower.ThetaCuspNativeEvenFourTail

/-!
# Complete fixed compensated source positivity from one half

The exact central-coordinate first-atom reserve absorbs all sixteen complete
reflection-entry errors and the complete compensation error. Four explicit
positive reserves remain. The fixed coefficient is 10^12 and the physical domain
is x >= 1/2; the inner interval and all-rank extension remain open.
-/

namespace RHTower
noncomputable section

/-- The central change of coordinates recovers every physically scaled polynomial coefficient. -/
theorem centralUnscaledCoefficients_firstAtomCentralCoordinates (v s : ℝ)
    (c : Fin 4 → ℝ) (i : Fin 4) :
    HTGeometry.centralUnscaledCoefficients v (firstAtomCentralCoordinates v s c) i = s^i.val*c i := by
  fin_cases i <;> norm_num [HTGeometry.centralUnscaledCoefficients,firstAtomCentralCoordinates] <;>
    split_ifs <;> try omega
  all_goals ring_nf <;> rfl

/-- The complete source error fits the four-coordinate budget without discarding any entry. -/
theorem abs_nativeEvenEnergy_sub_first_le_central_budget {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
    |(∑ i : Fin 4, ∑ j : Fin 4, c i*c j*
      ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x))-
      firstAtomEvenEnergy x c| ≤
    thetaCuspSourceTerm x 1^2*((1/8)*(y 0)^2+(1/8)*(y 1)^2+2*(y 2)^2+70*(y 3)^2) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let s := 8*q
  let v := (2*q)⁻¹
  let y := firstAtomCentralCoordinates v s c
  let f := thetaCuspSourceTerm x 1
  let err := fun k : ℕ => (-1 : ℝ)^k*thetaCuspNativeReflectionJet (2*k) x-firstAtomSignedMoment k x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hsp : 0 ≤ s := by dsimp [s]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvU : v ≤ 1/8 := by
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2*q)).mpr
    dsimp [q]; linarith
  have hi (i : Fin 4) : HTGeometry.centralUnscaledCoefficients v y i = s^i.val*c i :=
    centralUnscaledCoefficients_firstAtomCentralCoordinates v s c i
  have ht (i j : Fin 4) : |c i*c j*err (i.val+j.val)| ≤
      f^2*(HTGeometry.centralErrorCeiling (i.val+j.val)*
        |HTGeometry.centralUnscaledCoefficients v y i| * |HTGeometry.centralUnscaledCoefficients v y j|) := by
    have hb := abs_native_even_sub_first_le_centralErrorCeiling hq
      (⟨i.val+j.val,by omega⟩ : Fin 7)
    change |err (i.val+j.val)| ≤ f^2*s^(i.val+j.val)*HTGeometry.centralErrorCeiling (i.val+j.val) at hb
    calc
      _ = |c i| * |c j| * |err (i.val+j.val)| := by rw [abs_mul,abs_mul]
      _ ≤ |c i| * |c j| * (f^2*s^(i.val+j.val)*HTGeometry.centralErrorCeiling (i.val+j.val)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [hi i,hi j,abs_mul,abs_mul,abs_pow,abs_pow,abs_of_nonneg hsp,pow_add]; ring
  have hid : (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*
      ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x))-
      firstAtomEvenEnergy x c = ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*err (i.val+j.val) := by
    simp only [firstAtomEvenEnergy,err,mul_sub,Finset.sum_sub_distrib]
  rw [hid]
  change |∑ i : Fin 4, ∑ j : Fin 4, c i*c j*err (i.val+j.val)| ≤
    f^2*((1/8)*(y 0)^2+(1/8)*(y 1)^2+2*(y 2)^2+70*(y 3)^2)
  calc
    _ ≤ ∑ i : Fin 4, |∑ j : Fin 4, c i*c j*err (i.val+j.val)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |c i*c j*err (i.val+j.val)| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, f^2*(HTGeometry.centralErrorCeiling (i.val+j.val)*
        |HTGeometry.centralUnscaledCoefficients v y i| * |HTGeometry.centralUnscaledCoefficients v y j|) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact ht i j
    _ = f^2*(∑ i : Fin 4, ∑ j : Fin 4, HTGeometry.centralErrorCeiling (i.val+j.val)*
        |HTGeometry.centralUnscaledCoefficients v y i| * |HTGeometry.centralUnscaledCoefficients v y j|) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (HTGeometry.centralError_quadratic_le hv hvU y) (sq_nonneg f)

/-- Four explicit positive reserves survive the complete source and its fixed compensation. -/
theorem nativeCompensatedEvenEnergy_central_lower_of_eight_le {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) (c : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let h := 6/(2*q-3)^2
    let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
    thetaCuspSourceTerm x 1^2*((3/4)*(y 0+h*y 1)^2+(47/64)*(y 1)^2+(y 2)^2+11*(y 3)^2) ≤
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*
        ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x))+
      1000000000000*thetaCuspCenterCompensationSource x*(c 3)^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let h := 6/(2*q-3)^2
  let y := firstAtomCentralCoordinates ((2*q)⁻¹) (8*q) c
  let f := thetaCuspSourceTerm x 1
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have he := abs_nativeEvenEnergy_sub_first_le_central_budget hq c
  have hg := abs_fullCompensation_sub_first_le_last_unit hq
  have hf := firstAtomCompensatedEvenEnergy_coordinate_lower hx.le (by linarith) c
  have hd : 24 ≤ (2*q-3)^2 := by dsimp [q]; nlinarith
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1/4 := by
    apply (div_le_iff₀ (by linarith : 0 < (2*q-3)^2)).mpr
    linarith
  have hhsq : h^2 ≤ 1/16 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  have hy0 : (y 0)^2 ≤ 2*(y 0+h*y 1)^2+(1/8)*(y 1)^2 := by
    have hm := mul_le_mul_of_nonneg_right hhsq (sq_nonneg (y 1))
    nlinarith [sq_nonneg (y 0+2*h*y 1)]
  have hy3 : y 3 = (8*q)^3*c 3 := rfl
  have hy3sq : f^2*(y 3)^2 = f^2*(8*q)^6*(c 3)^2 := by rw [hy3]; ring
  have hge := mul_le_mul_of_nonneg_right hg (sq_nonneg (c 3))
  have hgl := neg_le_abs (thetaCuspCenterCompensationSource x-firstAtomCompensationSource x)
  have hglm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgl (by norm_num : (0 : ℝ) ≤ 1000000000000)) (sq_nonneg (c 3))
  have hentry := (abs_le.mp he).1
  have hy0m := mul_le_mul_of_nonneg_left hy0 (sq_nonneg f)
  change f^2*((y 0+h*y 1)^2+(7/8)*(y 1)^2+3*(y 2)^2+82*(y 3)^2) ≤ _ at hf
  change -(f^2*((1/8)*(y 0)^2+(1/8)*(y 1)^2+2*(y 2)^2+70*(y 3)^2)) ≤ _ at hentry
  change _ ≤ f^2*(8*q)^6*(c 3)^2 at hge
  change f^2*((3/4)*(y 0+h*y 1)^2+(47/64)*(y 1)^2+(y 2)^2+11*(y 3)^2) ≤ _
  nlinarith only [hf,hentry,hge,hglm,hy3sq,hy0m]

/-- The literal fixed compensated source is positive definite on the complete scale-eight ray. -/
theorem thetaCuspNativeEvenFourFixed_posDef_of_eight_le {x : ℝ}
    (hq : 8 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeEvenFourCompensated,add_comm,and_comm]
  · intro c hc
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let h := 6/(2*q-3)^2
    let s := 8*q
    let v := (2*q)⁻¹
    let y := firstAtomCentralCoordinates v s c
    have hqp : 0 < q := by dsimp [q]; linarith
    have hs : s ≠ 0 := by dsimp [s]; positivity
    have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
    have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
    have hreserve : 0 < (3/4 : ℝ)*(y 0+h*y 1)^2+(47/64)*(y 1)^2+(y 2)^2+11*(y 3)^2 := by
      by_contra hn
      have h0 := sq_nonneg (y 0+h*y 1)
      have h1 := sq_nonneg (y 1)
      have h2 := sq_nonneg (y 2)
      have h3 := sq_nonneg (y 3)
      have hy3 : y 3 = 0 := by nlinarith
      have hy2 : y 2 = 0 := by nlinarith
      have hy1 : y 1 = 0 := by nlinarith
      have hy0 : y 0 = 0 := by rw [hy1] at hn; nlinarith
      have hcz (i : Fin 4) : s^i.val*c i = 0 := by
        rw [← centralUnscaledCoefficients_firstAtomCentralCoordinates v s c i]
        change HTGeometry.centralUnscaledCoefficients v y i = 0
        fin_cases i <;> simp [HTGeometry.centralUnscaledCoefficients,hy0,hy1,hy2,hy3]
      apply hc
      funext i
      exact (mul_eq_zero.mp (hcz i)).resolve_left (pow_ne_zero _ hs)
    have hp := mul_pos (sq_pos_of_pos hf) hreserve
    have hl := nativeCompensatedEvenEnergy_central_lower_of_eight_le hq c
    have heq : star c ⬝ᵥ (thetaCuspNativeEvenFourCompensated 1000000000000 x).mulVec c =
      (∑ i : Fin 4, ∑ j : Fin 4, c i*c j*
        ((-1 : ℝ)^(i.val+j.val)*thetaCuspNativeReflectionJet (2*(i.val+j.val)) x))+
        1000000000000*thetaCuspCenterCompensationSource x*(c 3)^2 := by
      simp [thetaCuspNativeEvenFourCompensated,dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
      ring
    rw [heq]
    exact hp.trans_le hl

/-- One half is an explicit physical endpoint for the fixed compensated source. -/
theorem eight_le_firstAtomScale_of_half_le {x : ℝ} (hx : 1/2 ≤ x) :
    8 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
  have h1 : 1 ≤ 2*x := by linarith
  have he := Real.exp_le_exp.mpr h1
  have hlow : (8/3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpi := Real.pi_gt_three
  have hp : 0 < Real.exp (2*x) := Real.exp_pos _
  have hm := mul_lt_mul_of_pos_right hpi hp
  unfold thetaCuspSingleAtomReflectionScale
  norm_num only [Nat.cast_one,one_pow,mul_one]
  nlinarith only [he,hlow,hm]

/-- Complete compensated source positivity for every physical center at least one half. -/
theorem thetaCuspNativeEvenFourFixed_posDef_of_half_le {x : ℝ} (hx : 1/2 ≤ x) :
    (thetaCuspNativeEvenFourCompensated 1000000000000 x).PosDef :=
  thetaCuspNativeEvenFourFixed_posDef_of_eight_le (eight_le_firstAtomScale_of_half_le hx)

end
end RHTower
