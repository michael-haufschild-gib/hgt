import GaloisForLFunctions.RHTower.ThetaCuspOddFourGaussianFlow
import GaloisForLFunctions.RHTower.ThetaCuspNativeOddSchurFarTail
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Gaussian limit at every fixed native reflection order

The literal first-atom reflection profile has a jointly smooth extension in
inverse square-root scale. Differentiating this extension gives every fixed
jet limit. The all-order complete-source remainder then transfers the limit
without truncating the theta sum. There is no uniform-in-order assertion.
-/

open Filter Topology
open scoped ContDiff
namespace RHTower.ThetaCuspGaussianLimit
noncomputable section

private def sinhc (x : ℝ) : ℝ := (dslope Complex.sinh 0 (x : ℂ)).re

private theorem sinhc_smooth : ContDiff ℝ ∞ sinhc := by
  have hd : Differentiable ℂ (dslope Complex.sinh 0) := by
    apply differentiableOn_univ.mp
    rw [Complex.differentiableOn_dslope Filter.univ_mem]
    exact Complex.differentiable_sinh.differentiableOn
  exact hd.contDiff.real_of_complex

private theorem sinhc_zero : sinhc 0 = 1 := by
  simp [sinhc, dslope_same, Complex.deriv_sinh]

private theorem sinhc_mul (x : ℝ) : sinhc x*x = Real.sinh x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hz : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    simp only [sinhc, dslope_of_ne _ hz, slope_def_field, sub_zero,
      Complex.sinh_zero, ← Complex.ofReal_sinh, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_mul_cancel₀ _ hx

private theorem smooth_param_jet {F : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry F)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (F p.1) p.2) := by
  induction n with
  | zero =>
    have he : (fun p : ℝ × ℝ => iteratedDeriv 0 (F p.1) p.2) =
        Function.uncurry F := by funext p; rfl
    rw [he]
    exact hf
  | succ n ih =>
    have hh : ContDiff ℝ ∞ (Function.uncurry
        (fun p : ℝ × ℝ => fun t : ℝ => iteratedDeriv n (F p.1) t)) := by
      convert ih.comp (contDiff_fst.fst.prodMk contDiff_snd) using 1
      funext p
      rfl
    have h := hh.fderiv_apply contDiff_snd
      (show ContDiff ℝ ∞ (fun _ : ℝ × ℝ => (1 : ℝ)) from contDiff_const) (by simp)
    simpa only [iteratedDeriv_succ, deriv] using h

/-- The limiting reflected profile at inverse scale zero. -/
def profile (t : ℝ) : ℝ := Real.exp (-4*t^(2 : ℕ))

private def extension (u t : ℝ) : ℝ :=
  let z := t*sinhc (u*t)
  Real.exp (-4*z^(2 : ℕ))*((2-3*u^(2 : ℕ))^(2 : ℕ)-24*u^(4 : ℕ)*z^(2 : ℕ))

private theorem extension_smooth : ContDiff ℝ ∞ (Function.uncurry extension) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sinhc (p.1*p.2)) :=
    sinhc_smooth.comp (contDiff_fst.mul contDiff_snd)
  unfold extension Function.uncurry
  fun_prop

private theorem extension_zero : extension 0 = fun t => 4*profile t := by
  funext t
  norm_num [extension, sinhc_zero, profile, mul_comm]

private theorem extension_jet_tendsto (n : ℕ) :
    Tendsto (fun u => iteratedDeriv n (extension u) 0) (𝓝 0)
      (𝓝 (4*iteratedDeriv n profile 0)) := by
  have hc := (smooth_param_jet extension_smooth n).continuous.comp
    (show Continuous (fun u : ℝ => (u, (0 : ℝ))) by fun_prop)
  have hz : iteratedDeriv n (extension 0) 0 = 4*iteratedDeriv n profile 0 := by
    rw [extension_zero, iteratedDeriv_const_mul_field]
  simpa only [Function.comp_def, hz] using (hc.continuousAt (x := 0)).tendsto

private theorem extension_eq_affine {u : ℝ} (hu : u ≠ 0) (t : ℝ) :
    extension u t = u^(4 : ℕ)*ThetaCuspOddFour.affine (u⁻¹^(2 : ℕ))
      ((2*u⁻¹^(2 : ℕ)-3)^(2 : ℕ)) (u*t) := by
  have hs := sinhc_mul (u*t)
  have hc : Real.cosh (2*(u*t))-1 = 2*(u*t*sinhc (u*t))^(2 : ℕ) := by
    have h := Real.cosh_add (u*t) (u*t)
    have hsq := Real.cosh_sq_sub_sinh_sq (u*t)
    rw [show u*t+u*t=2*(u*t) by ring] at h
    calc
      _ = 2*Real.sinh (u*t)^(2 : ℕ) := by nlinarith only [h, hsq]
      _ = _ := by rw [← hs]; ring
  have he : -2*(u⁻¹^(2 : ℕ))*(Real.cosh (2*(u*t))-1) =
      -4*(t*sinhc (u*t))^(2 : ℕ) := by
    rw [hc]
    field_simp
    ring
  unfold extension ThetaCuspOddFour.affine ThetaCuspOddFour.gaussian
    ThetaCuspOddFour.factor
  rw [he, hc]
  field_simp
  ring

private theorem extension_even_jet {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    iteratedDeriv (2*k) (extension u) 0 =
      u^(2*k+4)*iteratedDeriv (2*k)
        (ThetaCuspOddFour.affine (u⁻¹^(2 : ℕ))
          ((2*u⁻¹^(2 : ℕ)-3)^(2 : ℕ))) 0 := by
  have hf := funext (extension_eq_affine hu)
  have hc : ContDiff ℝ (2*k : ℕ)
      (ThetaCuspOddFour.affine (u⁻¹^(2 : ℕ))
        ((2*u⁻¹^(2 : ℕ)-3)^(2 : ℕ))) := by
    unfold ThetaCuspOddFour.affine ThetaCuspOddFour.gaussian ThetaCuspOddFour.factor
    fun_prop
  rw [hf, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hc u]
  simp only [mul_zero]
  rw [pow_add]
  ring

private theorem firstAtom_normalized_jet (k : ℕ) (x : ℝ) :
    thetaCuspFirstAtomReflectionJet (2*k) x /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k) =
      iteratedDeriv (2*k)
        (ThetaCuspOddFour.affine (thetaCuspSingleAtomReflectionScale 1 x)
          ((2*thetaCuspSingleAtomReflectionScale 1 x-3)^(2 : ℕ))) 0 /
        (((2*thetaCuspSingleAtomReflectionScale 1 x-3)^(2 : ℕ))*
          thetaCuspSingleAtomReflectionScale 1 x^k) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let C := 4*q^(2 : ℕ)*Real.exp (x-2*q)
  have hc : C ≠ 0 := by
    dsimp [C, q, thetaCuspSingleAtomReflectionScale]
    positivity
  have hfun : (fun t => thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1) =
      fun t => C*ThetaCuspOddFour.affine q ((2*q-3)^(2 : ℕ)) t := by
    funext t
    exact ThetaCuspOddFour.firstAtomPair_eq_affine x t
  have hmass : thetaCuspSourceTerm x 1^(2 : ℕ) = C*(2*q-3)^(2 : ℕ) := by
    have h := congrFun hfun 0
    simpa [ThetaCuspOddFour.affine, ThetaCuspOddFour.gaussian,
      ThetaCuspOddFour.factor, pow_two] using h
  unfold thetaCuspFirstAtomReflectionJet
  rw [hfun, iteratedDeriv_const_mul_field, hmass]
  let A := iteratedDeriv (2*k) (ThetaCuspOddFour.affine q ((2*q-3)^(2 : ℕ))) 0
  let B := (2*q-3)^(2 : ℕ)
  change C*A/(C*B*q^k) = A/(B*q^k)
  rw [show C*B*q^k=C*(B*q^k) by ring]
  exact mul_div_mul_left _ _ hc

/-- Every fixed first-atom jet converges to its Gaussian jet in the literal source normalization. -/
theorem firstAtom_scaled_jet_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => (-1 : ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k))
      atTop (𝓝 ((-1 : ℝ)^k*iteratedDeriv (2*k) profile 0)) := by
  let q := fun x => thetaCuspSingleAtomReflectionScale 1 x
  let u := fun x => Real.sqrt ((q x)⁻¹)
  have hq (x : ℝ) : 0 < q x := by
    dsimp [q, thetaCuspSingleAtomReflectionScale]
    positivity
  have hsq (x : ℝ) : u x^(2 : ℕ) = (q x)⁻¹ :=
    Real.sq_sqrt (inv_nonneg.mpr (hq x).le)
  have hu (x : ℝ) : u x ≠ 0 :=
    (Real.sqrt_pos.mpr (inv_pos.mpr (hq x))).ne'
  have hi (x : ℝ) : (u x)⁻¹^(2 : ℕ) = q x := by
    rw [inv_pow, hsq, inv_inv]
  have hulim : Tendsto u atTop (𝓝 0) := by
    simpa [u, q, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
      thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hd : Tendsto (fun x => (2-3*u x^(2 : ℕ))^(2 : ℕ)) atTop (𝓝 (4 : ℝ)) := by
    convert ((tendsto_const_nhds.sub ((hulim.pow 2).const_mul 3)).pow 2) using 1
    norm_num
  have hn := (extension_jet_tendsto (2*k)).comp hulim
  have h := (hn.div hd (by norm_num : (4 : ℝ) ≠ 0)).const_mul ((-1 : ℝ)^k)
  apply (show Tendsto _ atTop (𝓝 ((-1 : ℝ)^k*iteratedDeriv (2*k) profile 0))
    from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have he := extension_even_jet (hu x) k
  rw [hi] at he
  rw [show 2*k+4=2*(k+2) by omega, pow_mul, hsq, pow_add, inv_pow, inv_pow] at he
  have hD : (2-3*u x^(2 : ℕ))^(2 : ℕ) =
      (q x^(2 : ℕ))⁻¹*(2*q x-3)^(2 : ℕ) := by
    rw [hsq]
    field_simp [(hq x).ne']
  rw [he, hD]
  rw [show (-1 : ℝ)^k*thetaCuspFirstAtomReflectionJet (2*k) x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*q x^k) =
      (-1 : ℝ)^k*(thetaCuspFirstAtomReflectionJet (2*k) x /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*q x^k)) by ring,
    firstAtom_normalized_jet k x]
  have hqn := (hq x).ne'
  change (-1 : ℝ)^k * ((q x^k)⁻¹*(q x^2)⁻¹ *
    iteratedDeriv (2*k) (ThetaCuspOddFour.affine (q x) ((2*q x-3)^2)) 0 /
    ((q x^2)⁻¹*(2*q x-3)^2)) =
    (-1 : ℝ)^k*(iteratedDeriv (2*k)
      (ThetaCuspOddFour.affine (q x) ((2*q x-3)^2)) 0 / ((2*q x-3)^2*q x^k))
  field_simp [hqn]

/-- All complete native signed reflection jets have their Gaussian limit.
The infinite theta remainder is retained through its proved all-order error law. -/
theorem native_scaled_jet_tendsto (k : ℕ) :
    Tendsto (thetaCuspNativeScaledEvenJet k) atTop
      (𝓝 ((-1 : ℝ)^k*iteratedDeriv (2*k) profile 0)) := by
  have herr := ((thetaCuspNativeReflectionJet_firstAtom_error_scaled_tendsto_zero 0 (2*k)).mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow k)).const_mul ((-1 : ℝ)^k)
  have h := (firstAtom_scaled_jet_tendsto k).add herr
  apply (show Tendsto _ atTop (𝓝 ((-1 : ℝ)^k*iteratedDeriv (2*k) profile 0))
    from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne'
  unfold thetaCuspNativeScaledEvenJet
  field_simp [hq, hf]
  ring

end
end RHTower.ThetaCuspGaussianLimit
