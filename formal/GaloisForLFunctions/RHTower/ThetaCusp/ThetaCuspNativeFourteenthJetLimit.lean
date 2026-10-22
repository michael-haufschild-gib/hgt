import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAffineTwelfthSourceLimit
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGaussianFourteenJetTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomFourteenthRecurrence

/-!
# Source-faithful cofinal fourteenth reflection limit

The exact affine first-atom recurrence and finite Gaussian tail give the
fourteenth first-atom limit. The all-order higher-atom error transfers the
same coefficient to the literal complete theta source. This is a local
cofinal coefficient, not an integrated odd-four sign theorem.
-/

open Filter Topology
namespace RHTower.ThetaCuspOddFour
noncomputable section

private theorem combined_jet_eq (n : ℕ) (q B : ℝ) :
    iteratedDeriv n (fun t : ℝ => affine q B t+6*gaussian q t) 0 =
      iteratedDeriv n (affine q B) 0+6*iteratedDeriv n (gaussian q) 0 := by
  have ha : ContDiffAt ℝ n (affine q B) 0 := by
    change ContDiffAt ℝ n (fun t : ℝ => gaussian q t * factor q B t) 0
    dsimp [gaussian, factor]
    fun_prop
  have hg : ContDiffAt ℝ n (fun t : ℝ => 6*gaussian q t) 0 := by
    dsimp [gaussian]
    fun_prop
  change iteratedDeriv n (affine q B + fun t : ℝ => 6*gaussian q t) 0 = _
  rw [iteratedDeriv_add ha hg, iteratedDeriv_const_mul_field]

private theorem combined_lower_scaled_eight_tendsto_zero (j : Fin 6) :
    Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv (2*j.val)
        (fun t : ℝ => affine q ((2*q-3)^(2 : ℕ)) t+6*gaussian q t) 0 / q^8)
      atTop (𝓝 0) := by
  have ha := affine_lower_scaled_eight_tendsto_zero j
  have hg := (gaussian_lower_scaled_eight_tendsto_zero j).comp
    thetaCuspC5FarTail_scale_tendsto_atTop
  have h := ha.add (hg.const_mul 6)
  have h' : Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv (2*j.val) (affine q ((2*q-3)^(2 : ℕ))) 0 / q^8+
        6*(iteratedDeriv (2*j.val) (gaussian q) 0 / q^8))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using h
  apply h'.congr'
  filter_upwards [] with x
  dsimp only
  rw [combined_jet_eq]
  ring

private theorem combined_twelve_scaled_eight_tendsto :
    Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv 12
        (fun t : ℝ => affine q ((2*q-3)^(2 : ℕ)) t+6*gaussian q t) 0 / q^8)
      atTop (𝓝 (10899947520 : ℝ)) := by
  have ha := affine_twelve_scaled_eight_tendsto
  have hg := gaussian_twelve_scaled_eight_tendsto_zero.comp
    thetaCuspC5FarTail_scale_tendsto_atTop
  have h := ha.add (hg.const_mul 6)
  have h' : Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv 12 (affine q ((2*q-3)^(2 : ℕ))) 0 / q^8+
        6*(iteratedDeriv 12 (gaussian q) 0 / q^8))
      atTop (𝓝 (10899947520 : ℝ)) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using h
  apply h'.congr'
  filter_upwards [] with x
  dsimp only
  rw [combined_jet_eq]
  ring

private def combinedScaled (k : ℕ) (x : ℝ) : ℝ :=
  let q := thetaCuspSingleAtomReflectionScale 1 x
  iteratedDeriv (2*k)
    (fun t : ℝ => affine q ((2*q-3)^(2 : ℕ)) t+6*gaussian q t) 0 / q^8

theorem affine_fourteen_scaled_nine_tendsto :
    Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      iteratedDeriv 14 (affine q ((2*q-3)^(2 : ℕ))) 0 / q^9)
      atTop (𝓝 (-1133594542080 : ℝ)) := by
  have h6 : Tendsto (combinedScaled 6) atTop (𝓝 (10899947520 : ℝ)) := by
    exact combined_twelve_scaled_eight_tendsto
  have h5 : Tendsto (combinedScaled 5) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨5, by omega⟩
  have h4 : Tendsto (combinedScaled 4) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨4, by omega⟩
  have h3 : Tendsto (combinedScaled 3) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨3, by omega⟩
  have h2 : Tendsto (combinedScaled 2) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨2, by omega⟩
  have h1 : Tendsto (combinedScaled 1) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨1, by omega⟩
  have h0 : Tendsto (combinedScaled 0) atTop (𝓝 (0 : ℝ)) :=
    combined_lower_scaled_eight_tendsto_zero ⟨0, by omega⟩
  have hs1 := (h6.const_mul 26).add (h5.const_mul 2288)
  have hs2 := hs1.add (h4.const_mul 41184)
  have hs3 := hs2.add (h3.const_mul 219648)
  have hs4 := hs3.add (h2.const_mul 366080)
  have hs5 := hs4.add (h1.const_mul 159744)
  have hsum := (hs5.add (h0.const_mul 8192)).const_mul (-4)
  have hsum' : Tendsto (fun x : ℝ => -4*(26*combinedScaled 6 x+
      2288*combinedScaled 5 x+41184*combinedScaled 4 x+
      219648*combinedScaled 3 x+366080*combinedScaled 2 x+
      159744*combinedScaled 1 x+8192*combinedScaled 0 x))
      atTop (𝓝 (-1133594542080 : ℝ)) := by
    convert hsum using 1
    norm_num
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq : q ≠ 0 := by
    unfold q thetaCuspSingleAtomReflectionScale
    positivity
  dsimp only [combinedScaled]
  rw [affine_jet_fourteen]
  dsimp only
  field_simp [hq]

private theorem atom_fourteen_eq_affine (x : ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    thetaCuspFirstAtomReflectionJet 14 x =
      4*q^(2 : ℕ)*Real.exp (x-2*q)*
        iteratedDeriv 14 (affine q ((2*q-3)^(2 : ℕ))) 0 := by
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

theorem first_atom_fourteen_scaled_tendsto :
    Tendsto (fun x : ℝ =>
      (-1 : ℝ)^(7 : ℕ)*thetaCuspFirstAtomReflectionJet 14 x /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*
          thetaCuspSingleAtomReflectionScale 1 x^(7 : ℕ)))
      atTop (𝓝 (283398635520 : ℝ)) := by
  let R (u : ℝ) := 4/(4-6*u)^(2 : ℕ)
  have hc : ContinuousAt R 0 := by
    dsimp [R]
    apply ContinuousAt.div <;> first | fun_prop | norm_num
  have hR := hc.tendsto.comp thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hR' : Tendsto (fun x : ℝ =>
      R ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹))
      atTop (𝓝 (1/4 : ℝ)) := by
    rw [show R 0 = 1/4 by norm_num [R]] at hR
    exact hR
  have h := affine_fourteen_scaled_nine_tendsto.neg.mul hR'
  have h' : Tendsto (fun x : ℝ =>
      let q := thetaCuspSingleAtomReflectionScale 1 x
      (-iteratedDeriv 14 (affine q ((2*q-3)^(2 : ℕ))) 0 / q^9) *
        R (q⁻¹)) atTop (𝓝 (283398635520 : ℝ)) := by
    convert h using 1 <;> (try norm_num)
    all_goals
      funext x
      ring
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
  rw [atom_fourteen_eq_affine x, thetaCuspSourceTerm_one_eq_scale_profile, he]
  dsimp only [R]
  let E := Real.exp (x/2-q)
  let J := iteratedDeriv 14 (affine q ((2*q-3)^(2 : ℕ))) 0
  have hE : E ≠ 0 := Real.exp_ne_zero _
  change (-J/q^9) * (4/(4-6*q⁻¹)^2) =
    (-1 : ℝ)^7*(4*q^2*E^2*J)/((E*(4*q^2-6*q))^2*q^7)
  exact (affine_fourteen_source_algebra q E J hq hE hb).symm

theorem native_seven_scaled_tendsto :
    Tendsto (thetaCuspNativeScaledEvenJet 7) atTop
      (𝓝 (283398635520 : ℝ)) := by
  have herr := ((thetaCuspNativeReflectionJet_firstAtom_error_scaled_tendsto_zero 0 14).mul
    (thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero.pow 7)).const_mul
      ((-1 : ℝ)^(7 : ℕ))
  have h := first_atom_fourteen_scaled_tendsto.add herr
  apply (show Tendsto _ atTop (𝓝 (283398635520 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hq : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hf : thetaCuspSourceTerm x 1 ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  unfold thetaCuspNativeScaledEvenJet
  norm_num
  field_simp [hq, hf]
  ring

end
end RHTower.ThetaCuspOddFour
