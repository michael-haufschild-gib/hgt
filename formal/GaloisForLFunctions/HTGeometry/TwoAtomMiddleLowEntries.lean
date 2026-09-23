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
  have hlower : 0 ≤ twoAtomOddNumerator1 q z-8*(q^(0 : ℕ)*(2*q-3)^(2 : ℕ)) := by
    have heq : twoAtomOddNumerator1 q z-8*(q^(0 : ℕ)*(2*q-3)^(2 : ℕ)) =
      (2/1650390625 : ℝ)*(
      ((39609375000 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (118828125000 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (118828125000 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (39609375000 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(0 : ℕ)*(1-v)^(2 : ℕ) +
      ((77723005750 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (228258200625 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (217824384375 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (65186875000 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(1 : ℕ)*(1-v)^(1 : ℕ) +
      ((38113702106 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (109430430141 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (98996824035 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (25577781500 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(2 : ℕ)*(1-v)^(0 : ℕ)) := by
      unfold twoAtomOddNumerator1
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  have hupper : 0 ≤ 11*(q^(0 : ℕ)*(2*q-3)^(2 : ℕ))-twoAtomOddNumerator1 q z := by
    have heq : 11*(q^(0 : ℕ)*(2*q-3)^(2 : ℕ))-twoAtomOddNumerator1 q z =
      (1/1650390625 : ℝ)*(
      ((16635937500 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (337471875000 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (840708984375 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (519873046875 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(0 : ℕ)*(1-v)^(2 : ℕ) +
      ((36263363500 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (693739848750 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (1721081700000 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (1067809843750 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(1 : ℕ)*(1-v)^(1 : ℕ) +
      ((19627283288 : ℝ)*u^(0 : ℕ)*(1-u)^(3 : ℕ) +
        (356267264718 : ℝ)*u^(1 : ℕ)*(1-u)^(2 : ℕ) +
        (880371586305 : ℝ)*u^(2 : ℕ)*(1-u)^(1 : ℕ) +
        (547936233875 : ℝ)*u^(3 : ℕ)*(1-u)^(0 : ℕ))*v^(2 : ℕ)*(1-v)^(0 : ℕ)) := by
      unfold twoAtomOddNumerator1
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  unfold twoAtomOddProfile1
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < q^(0 : ℕ)*(2*q-3)^(2 : ℕ))).mpr
    linarith only [hlower]
  · apply (div_le_iff₀ (by positivity : 0 < q^(0 : ℕ)*(2*q-3)^(2 : ℕ))).mpr
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
  have hlower : 0 ≤ twoAtomOddNumerator2 q z-180*(q^(1 : ℕ)*(2*q-3)^(2 : ℕ)) := by
    have heq : twoAtomOddNumerator2 q z-180*(q^(1 : ℕ)*(2*q-3)^(2 : ℕ)) =
      (2/8251953125 : ℝ)*(
      ((35371435937500 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (214362504687500 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (515453894921875 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (621018226562500 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (376267607421875 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (91712207031250 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(0 : ℕ)*(1-v)^(2 : ℕ) +
      ((71814601663350 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (441738995953125 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (1092651256831875 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (1386200011706250 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (918927526968750 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (259575334687500 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(1 : ℕ)*(1-v)^(1 : ℕ) +
      ((36443292092586 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (227377483704297 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (577200412853136 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (765186357406950 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (542663249164875 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (167864069882250 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(2 : ℕ)*(1-v)^(0 : ℕ)) := by
      unfold twoAtomOddNumerator2
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  have hupper : 0 ≤ 310*(q^(1 : ℕ)*(2*q-3)^(2 : ℕ))-twoAtomOddNumerator2 q z := by
    have heq : 310*(q^(1 : ℕ)*(2*q-3)^(2 : ℕ))-twoAtomOddNumerator2 q z =
      (1/8251953125 : ℝ)*(
      ((6100635937500 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (254559154687500 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (1312299985546875 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (2610523195312500 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (2271879873046875 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (725198144531250 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(0 : ℕ)*(1-v)^(2 : ℕ) +
      ((10057812298300 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (483090336218750 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (2501113037117500 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (4932719273462500 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (4210975121843750 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (1298094447812500 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(1 : ℕ)*(1-v)^(1 : ℕ) +
      ((3956923627328 : ℝ)*u^(0 : ℕ)*(1-u)^(5 : ℕ) +
        (228529196653906 : ℝ)*u^(1 : ℕ)*(1-u)^(4 : ℕ) +
        (1188806949684353 : ℝ)*u^(2 : ℕ)*(1-u)^(3 : ℕ) +
        (2322186933623600 : ℝ)*u^(3 : ℕ)*(1-u)^(2 : ℕ) +
        (1939088589560875 : ℝ)*u^(4 : ℕ)*(1-u)^(1 : ℕ) +
        (572894418829250 : ℝ)*u^(5 : ℕ)*(1-u)^(0 : ℕ))*v^(2 : ℕ)*(1-v)^(0 : ℕ)) := by
      unfold twoAtomOddNumerator2
      dsimp [u,v]
      ring
    rw [heq]
    positivity
  unfold twoAtomOddProfile2
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < q^(1 : ℕ)*(2*q-3)^(2 : ℕ))).mpr
    linarith only [hlower]
  · apply (div_le_iff₀ (by positivity : 0 < q^(1 : ℕ)*(2*q-3)^(2 : ℕ))).mpr
    linarith only [hupper]

end
end HTGeometry
