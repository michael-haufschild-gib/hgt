import GaloisForLFunctions.RHTower.ThetaCuspOddFourGaussianFlow
import GaloisForLFunctions.RHTower.ThetaCuspNativeTwelfthJetLimit
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.RHTower.ThetaCuspAffineScaleAlgebra

open Filter Topology
namespace RHTower.ThetaCuspOddFour
noncomputable section

private theorem atom_jet_eq_affine (n : ℕ) (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    thetaCuspFirstAtomReflectionJet n x =
      4*q^(2 : ℕ)*Real.exp (x-2*q)*
        iteratedDeriv n (affine q ((2*q-3)^(2 : ℕ))) 0 := by
  dsimp only
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hfun : (fun t : ℝ =>
      thetaCuspSourceTerm (x+t) 1*thetaCuspSourceTerm (x-t) 1) =
      fun t => (4*q^(2 : ℕ)*Real.exp (x-2*q))*
        affine q ((2*q-3)^(2 : ℕ)) t := by
    funext t
    simpa [q] using firstAtomPair_eq_affine x t
  unfold thetaCuspFirstAtomReflectionJet
  rw [hfun, iteratedDeriv_const_mul_field]

private theorem first_scaled_lower_exists (j : Fin 6) :
    ∃ c : ℝ, Tendsto (thetaCuspFirstAtomScaledEvenJet j.val) atTop (𝓝 c) := by
  fin_cases j
  · refine ⟨1, ?_⟩
    have hEq : ∀ᶠ x : ℝ in atTop,
        thetaCuspFirstAtomScaledEvenJet 0 x = 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
        (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
      simp only [thetaCuspFirstAtomScaledEvenJet, Nat.mul_zero, pow_zero,
        one_mul, mul_one, thetaCuspFirstAtomReflectionJet_zero,
        div_self (pow_ne_zero 2 hf)]
    exact (tendsto_congr' hEq).mpr tendsto_const_nhds
  · exact ⟨8, thetaCuspFirstAtomReflectionJet_2_scaled_tendsto⟩
  · exact ⟨192, thetaCuspFirstAtomReflectionJet_4_scaled_tendsto⟩
  · exact ⟨7680, thetaCuspFirstAtomReflectionJet_6_scaled_tendsto⟩
  · exact ⟨430080, thetaCuspFirstAtomReflectionJet_8_scaled_tendsto⟩
  · exact ⟨30965760, thetaCuspFirstAtomReflectionJet_10_scaled_tendsto⟩

private theorem lower_factor_tendsto_zero (j : Fin 6) :
    Tendsto (fun x : ℝ =>
      (-1 : ℝ)^j.val *
        ((4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹)^2/4) *
        ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)^(6-j.val))
      atTop (𝓝 0) := by
  let R (u : ℝ) := (-1 : ℝ)^j.val * ((4-6*u)^2/4) * u^(6-j.val)
  have hc : ContinuousAt R 0 := by
    dsimp [R]
    fun_prop
  have h := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hz : R 0 = 0 := by
    dsimp [R]
    have hp : 6-j.val ≠ 0 := by omega
    simp [hp]
  rw [hz] at h
  simpa [R, Function.comp_def] using h

theorem affine_twelve_scaled_eight_tendsto :
    Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv 12 (affine q ((2*q-3)^(2 : ℕ))) 0 / q^(8 : ℕ))
      atTop (𝓝 (10899947520 : ℝ)) := by
  let R (u : ℝ) := (4-6*u)^(2 : ℕ)/4
  have hc : ContinuousAt R 0 := by
    dsimp [R]
    fun_prop
  have hR := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hR' : Tendsto (fun x : ℝ =>
      R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)) atTop (𝓝 (4 : ℝ)) := by
    rw [show R 0 = 4 by norm_num [R]] at hR
    exact hR
  have h := thetaCuspFirstAtomReflectionJet_12_scaled_tendsto.mul hR'
  have h' : Tendsto (fun x : ℝ =>
      ((-1 : ℝ)^(6 : ℕ)*thetaCuspFirstAtomReflectionJet 12 x /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*
          thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ))) *
        R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (10899947520 : ℝ)) := by
    convert h using 1 <;> norm_num
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq3 : 3 < q :=
    three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hq : q ≠ 0 := by linarith
  have hb : 4*q^(2 : ℕ)-6*q ≠ 0 := by nlinarith [sq_nonneg (q-3)]
  have he : Real.exp (x-2*q) = Real.exp (x/2-q)^(2 : ℕ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [atom_jet_eq_affine 12 x, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp only [R]
  rw [he]
  let E := Real.exp (x/2-q)
  let J := iteratedDeriv 12 (affine q ((2*q-3)^(2 : ℕ))) 0
  have hE : E ≠ 0 := Real.exp_ne_zero _
  have ha := affine_twelve_algebra q E J hq hE hb
  norm_num only at ⊢
  simp only [one_mul] at ⊢
  change (4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^6) *
    ((4-6*q⁻¹)^2/4) = J/q^8
  exact ha.symm

theorem affine_lower_scaled_eight_tendsto_zero (j : Fin 6) :
    Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv (2*j.val) (affine q ((2*q-3)^(2 : ℕ))) 0 / q^(8 : ℕ))
      atTop (𝓝 0) := by
  obtain ⟨c, hfirst⟩ := first_scaled_lower_exists j
  have h := hfirst.mul (lower_factor_tendsto_zero j)
  have h' : Tendsto (fun x : ℝ =>
      thetaCuspFirstAtomScaledEvenJet j.val x *
        ((-1 : ℝ)^j.val *
          ((4-6*(thetaCuspSingleAtomReflectionScale 1 x)⁻¹)^2/4) *
          ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹)^(6-j.val)))
      atTop (𝓝 0) := by
    convert h using 1 <;> norm_num
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq3 : 3 < q :=
    three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
  have hq : q ≠ 0 := by linarith
  have hb : 4*q^(2 : ℕ)-6*q ≠ 0 := by nlinarith [sq_nonneg (q-3)]
  have he : Real.exp (x-2*q) = Real.exp (x/2-q)^(2 : ℕ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  dsimp only
  unfold thetaCuspFirstAtomScaledEvenJet
  rw [atom_jet_eq_affine (2*j.val) x, thetaCuspSourceTerm_one_eq_scale_profile]
  rw [he]
  let E := Real.exp (x/2-q)
  let J := iteratedDeriv (2*j.val) (affine q ((2*q-3)^(2 : ℕ))) 0
  have hE : E ≠ 0 := Real.exp_ne_zero _
  have ha := affine_lower_signed_algebra j q E J hq hE hb
  change ((-1 : ℝ)^j.val * (4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^j.val)) *
    ((-1 : ℝ)^j.val * ((4-6*q⁻¹)^2/4) * (q⁻¹)^(6-j.val)) = J/q^8
  exact ha.symm

end
end RHTower.ThetaCuspOddFour
