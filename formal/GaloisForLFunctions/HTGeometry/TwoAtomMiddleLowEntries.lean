import GaloisForLFunctions.HTGeometry.TwoAtomOddAlgebra

/-! # Uniform entry and cofactor bounds for the complete retained two-atom middle model -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- Positive polynomial reserves for the actual middle entry 1. -/
theorem twoAtomOddProfile1_middle_bounds {q z : ℝ} (hq0 : 37/10 ≤ q) (hq1 : q ≤ 7)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1/65000) :
    8 ≤ twoAtomOddProfile1 q z ∧ twoAtomOddProfile1 q z ≤ 11 := by
  let u := (10*q-37)/33
  let v := 65000*z
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hu' : 0 ≤ 1-u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv' : 0 ≤ 1-v := by dsimp [v]; linarith
  have hqp : 0 < q := by linarith
  have hdp : 0 < 2*q-3 := by linarith
  have hlower : 0 ≤ twoAtomOddNumerator1 q z-8*(q^0*(2*q-3)^2) := by
    have heq : twoAtomOddNumerator1 q z-8*(q^0*(2*q-3)^2) =
      (2/1650390625 : ℝ)*(
      ((39609375000 : ℝ)*u^0*(1-u)^3 +
        (118828125000 : ℝ)*u^1*(1-u)^2 +
        (118828125000 : ℝ)*u^2*(1-u)^1 +
        (39609375000 : ℝ)*u^3*(1-u)^0)*v^0*(1-v)^2 +
      ((77723005750 : ℝ)*u^0*(1-u)^3 +
        (228258200625 : ℝ)*u^1*(1-u)^2 +
        (217824384375 : ℝ)*u^2*(1-u)^1 +
        (65186875000 : ℝ)*u^3*(1-u)^0)*v^1*(1-v)^1 +
      ((38113702106 : ℝ)*u^0*(1-u)^3 +
        (109430430141 : ℝ)*u^1*(1-u)^2 +
        (98996824035 : ℝ)*u^2*(1-u)^1 +
        (25577781500 : ℝ)*u^3*(1-u)^0)*v^2*(1-v)^0) := by
      unfold twoAtomOddNumerator1
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  have hupper : 0 ≤ 11*(q^0*(2*q-3)^2)-twoAtomOddNumerator1 q z := by
    have heq : 11*(q^0*(2*q-3)^2)-twoAtomOddNumerator1 q z =
      (1/1650390625 : ℝ)*(
      ((16635937500 : ℝ)*u^0*(1-u)^3 +
        (337471875000 : ℝ)*u^1*(1-u)^2 +
        (840708984375 : ℝ)*u^2*(1-u)^1 +
        (519873046875 : ℝ)*u^3*(1-u)^0)*v^0*(1-v)^2 +
      ((36263363500 : ℝ)*u^0*(1-u)^3 +
        (693739848750 : ℝ)*u^1*(1-u)^2 +
        (1721081700000 : ℝ)*u^2*(1-u)^1 +
        (1067809843750 : ℝ)*u^3*(1-u)^0)*v^1*(1-v)^1 +
      ((19627283288 : ℝ)*u^0*(1-u)^3 +
        (356267264718 : ℝ)*u^1*(1-u)^2 +
        (880371586305 : ℝ)*u^2*(1-u)^1 +
        (547936233875 : ℝ)*u^3*(1-u)^0)*v^2*(1-v)^0) := by
      unfold twoAtomOddNumerator1
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  unfold twoAtomOddProfile1
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < q^0*(2*q-3)^2)).mpr
    linarith only [hlower]
  · apply (div_le_iff₀ (by positivity : 0 < q^0*(2*q-3)^2)).mpr
    linarith only [hupper]

/-- Positive polynomial reserves for the actual middle entry 2. -/
theorem twoAtomOddProfile2_middle_bounds {q z : ℝ} (hq0 : 37/10 ≤ q) (hq1 : q ≤ 7)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1/65000) :
    180 ≤ twoAtomOddProfile2 q z ∧ twoAtomOddProfile2 q z ≤ 310 := by
  let u := (10*q-37)/33
  let v := 65000*z
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hu' : 0 ≤ 1-u := by dsimp [u]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hv' : 0 ≤ 1-v := by dsimp [v]; linarith
  have hqp : 0 < q := by linarith
  have hdp : 0 < 2*q-3 := by linarith
  have hlower : 0 ≤ twoAtomOddNumerator2 q z-180*(q^1*(2*q-3)^2) := by
    have heq : twoAtomOddNumerator2 q z-180*(q^1*(2*q-3)^2) =
      (2/8251953125 : ℝ)*(
      ((35371435937500 : ℝ)*u^0*(1-u)^5 +
        (214362504687500 : ℝ)*u^1*(1-u)^4 +
        (515453894921875 : ℝ)*u^2*(1-u)^3 +
        (621018226562500 : ℝ)*u^3*(1-u)^2 +
        (376267607421875 : ℝ)*u^4*(1-u)^1 +
        (91712207031250 : ℝ)*u^5*(1-u)^0)*v^0*(1-v)^2 +
      ((71814601663350 : ℝ)*u^0*(1-u)^5 +
        (441738995953125 : ℝ)*u^1*(1-u)^4 +
        (1092651256831875 : ℝ)*u^2*(1-u)^3 +
        (1386200011706250 : ℝ)*u^3*(1-u)^2 +
        (918927526968750 : ℝ)*u^4*(1-u)^1 +
        (259575334687500 : ℝ)*u^5*(1-u)^0)*v^1*(1-v)^1 +
      ((36443292092586 : ℝ)*u^0*(1-u)^5 +
        (227377483704297 : ℝ)*u^1*(1-u)^4 +
        (577200412853136 : ℝ)*u^2*(1-u)^3 +
        (765186357406950 : ℝ)*u^3*(1-u)^2 +
        (542663249164875 : ℝ)*u^4*(1-u)^1 +
        (167864069882250 : ℝ)*u^5*(1-u)^0)*v^2*(1-v)^0) := by
      unfold twoAtomOddNumerator2
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  have hupper : 0 ≤ 310*(q^1*(2*q-3)^2)-twoAtomOddNumerator2 q z := by
    have heq : 310*(q^1*(2*q-3)^2)-twoAtomOddNumerator2 q z =
      (1/8251953125 : ℝ)*(
      ((6100635937500 : ℝ)*u^0*(1-u)^5 +
        (254559154687500 : ℝ)*u^1*(1-u)^4 +
        (1312299985546875 : ℝ)*u^2*(1-u)^3 +
        (2610523195312500 : ℝ)*u^3*(1-u)^2 +
        (2271879873046875 : ℝ)*u^4*(1-u)^1 +
        (725198144531250 : ℝ)*u^5*(1-u)^0)*v^0*(1-v)^2 +
      ((10057812298300 : ℝ)*u^0*(1-u)^5 +
        (483090336218750 : ℝ)*u^1*(1-u)^4 +
        (2501113037117500 : ℝ)*u^2*(1-u)^3 +
        (4932719273462500 : ℝ)*u^3*(1-u)^2 +
        (4210975121843750 : ℝ)*u^4*(1-u)^1 +
        (1298094447812500 : ℝ)*u^5*(1-u)^0)*v^1*(1-v)^1 +
      ((3956923627328 : ℝ)*u^0*(1-u)^5 +
        (228529196653906 : ℝ)*u^1*(1-u)^4 +
        (1188806949684353 : ℝ)*u^2*(1-u)^3 +
        (2322186933623600 : ℝ)*u^3*(1-u)^2 +
        (1939088589560875 : ℝ)*u^4*(1-u)^1 +
        (572894418829250 : ℝ)*u^5*(1-u)^0)*v^2*(1-v)^0) := by
      unfold twoAtomOddNumerator2
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  unfold twoAtomOddProfile2
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < q^1*(2*q-3)^2)).mpr
    linarith only [hlower]
  · apply (div_le_iff₀ (by positivity : 0 < q^1*(2*q-3)^2)).mpr
    linarith only [hupper]

end
end HTGeometry
