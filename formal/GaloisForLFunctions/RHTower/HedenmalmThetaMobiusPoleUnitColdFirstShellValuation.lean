import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitColdVacuumSaturationNoGo
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoSeam

/-!
# Cold first-shell valuation of the pole-unit source Gram

P-G43 shows that every positive two-aperture squarefree source Gram saturates at the cold vacuum,
even when apertures differ. This module blows up that vanishing defect at its first possible
Dirichlet scale.

For `0 < x < z`, the slower aperture controls the first non-vacuum shell:

`2^(x n) * (1 - G_n(x,z)) -> 1/2`.

The residue `1/2` is universal. Adjacent defect ratios recover exactly the prime-two character
`2^(-x)`. Thus vacuum orthogonalization does retain the smaller aperture, but only as the same
cofinal prime-two valuation already known to be a faithful Route-P detector. It supplies no
independent neutrality or saturation law. A successful cold continuation must retain a coupled
Euler--Gamma charge beyond the one-shell tropical valuation.
-/

open Complex Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

theorem tendsto_two_cpow_mul_squarefreePartition_sub_one
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) *
        (_root_.GaloisForLFunctions.squarefreePartition
          (1 + (x : ℂ) * (n : ℂ)) - 1))
      atTop (nhds (1 / 2 : ℂ)) := by
  let t : ℕ → ℝ := fun n => x * (n : ℝ)
  have ht : Tendsto t atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hx
  have hzeta :=
    (RHTower.tendsto_two_cpow_mul_riemannZeta_shift_sub_one (1 : ℂ)).comp ht
  have hzeta2 :=
    (RHTower.tendsto_two_cpow_mul_riemannZeta_shift_sub_one (2 : ℂ)).comp
      (ht.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hdecay : Tendsto (fun n : ℕ => (2 : ℂ) ^ (-(t n : ℂ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => Real.exp (-(Real.log 2) * t n)) atTop (nhds 0) := by
      exact Real.tendsto_exp_atBot.comp
        (ht.const_mul_atTop_of_neg (by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith : -(Real.log 2) < 0))
    convert hreal.ofReal using 1
    · funext n
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      rw [show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) by
        rw [← Complex.ofReal_ofNat]
        rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]]
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    · norm_num
  have hzeta2small : Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ ((t n : ℝ) : ℂ) *
        (riemannZeta (2 + ((2 * t n : ℝ) : ℂ)) - 1))
      atTop (nhds 0) := by
    have hprod := hdecay.mul hzeta2
    convert hprod using 1
    · funext n
      dsimp only [Function.comp_apply]
      have hpow : (2 : ℂ) ^ (-(t n : ℂ)) *
          (2 : ℂ) ^ ((2 * t n : ℝ) : ℂ) =
          (2 : ℂ) ^ ((t n : ℝ) : ℂ) := by
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
        congr 2
        push_cast
        ring
      calc
        (2 : ℂ) ^ ((t n : ℝ) : ℂ) *
            (riemannZeta (2 + ((2 * t n : ℝ) : ℂ)) - 1) =
            ((2 : ℂ) ^ (-(t n : ℂ)) *
              (2 : ℂ) ^ ((2 * t n : ℝ) : ℂ)) *
                (riemannZeta (2 + ((2 * t n : ℝ) : ℂ)) - 1) := by rw [hpow]
        _ = (2 : ℂ) ^ (-(t n : ℂ)) *
            ((2 : ℂ) ^ ((2 * t n : ℝ) : ℂ) *
              (riemannZeta (2 + ((2 * t n : ℝ) : ℂ)) - 1)) := by ring
    · norm_num
  have hden : Tendsto (fun n : ℕ =>
      riemannZeta (2 + ((2 * t n : ℝ) : ℂ))) atTop (nhds 1) := by
    apply RHTower.tendsto_riemannZeta_of_re_atTop
    have h2t : Tendsto (fun n : ℕ => 2 * t n) atTop atTop :=
      ht.const_mul_atTop (by norm_num)
    simpa using Filter.tendsto_atTop_add_const_left atTop 2 h2t
  have hnum : Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ ((t n : ℝ) : ℂ) *
        ((riemannZeta (1 + ((t n : ℝ) : ℂ)) - 1) -
          (riemannZeta (2 + ((2 * t n : ℝ) : ℂ)) - 1)))
      atTop (nhds (1 / 2 : ℂ)) := by
    have h := hzeta.sub hzeta2small
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      ring
    · norm_num [Complex.cpow_neg]
  have hquot := hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)
  convert hquot using 1
  · funext n
    simp only [_root_.GaloisForLFunctions.squarefreePartition, Pi.div_apply]
    simp only [t, Complex.ofReal_mul, Complex.ofReal_natCast]
    have hz : riemannZeta (2 + (x : ℂ) * (n : ℂ) * 2) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by
        norm_num [Complex.mul_re]
        have hn : (0 : ℝ) ≤ n := by positivity
        nlinarith)
    norm_num
    have hz' : riemannZeta ((1 + (x : ℂ) * (n : ℂ)) * 2) ≠ 0 := by
      rw [show (1 + (x : ℂ) * (n : ℂ)) * 2 =
        2 + (x : ℂ) * (n : ℂ) * 2 by ring]
      exact hz
    ring_nf
    field_simp [hz']
    ring
  · norm_num

private theorem tendsto_two_cpow_neg_real_mul_nat
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ (-((c : ℂ) * (n : ℂ)))) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hreal : Tendsto
      (fun n : ℕ => Real.exp (-(Real.log 2) * (c * (n : ℝ))))
      atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (ht.const_mul_atTop_of_neg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith : -(Real.log 2) < 0))
  convert hreal.ofReal using 1
  · funext n
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) by
      rw [← Complex.ofReal_ofNat]
      rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · norm_num

private theorem tendsto_squarefreePartition_one_add_real_mul_nat
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ =>
      _root_.GaloisForLFunctions.squarefreePartition
        (1 + (x : ℂ) * (n : ℂ))) atTop (nhds 1) := by
  have hscaled := tendsto_two_cpow_mul_squarefreePartition_sub_one hx
  have hdecay := tendsto_two_cpow_neg_real_mul_nat hx
  have hprod := hdecay.mul hscaled
  have hsub : Tendsto (fun n : ℕ =>
      _root_.GaloisForLFunctions.squarefreePartition
        (1 + (x : ℂ) * (n : ℂ)) - 1) atTop (nhds 0) := by
    convert hprod using 1
    · funext n
      have hpow : (2 : ℂ) ^ (-((x : ℂ) * (n : ℂ))) *
          (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) = 1 := by
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
        simp
      rw [← mul_assoc, hpow, one_mul]
    · norm_num
  simpa using hsub.add_const 1

private theorem tendsto_slower_two_cpow_mul_squarefreePartition_sub_one_zero
    {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) *
        (_root_.GaloisForLFunctions.squarefreePartition
          (1 + (z : ℂ) * (n : ℂ)) - 1)) atTop (nhds 0) := by
  have hgap : 0 < z - x := sub_pos.mpr hxz
  have hdecay := tendsto_two_cpow_neg_real_mul_nat hgap
  have hscaled := tendsto_two_cpow_mul_squarefreePartition_sub_one (lt_trans hx hxz)
  have hprod := hdecay.mul hscaled
  convert hprod using 1
  · funext n
    have hpow : (2 : ℂ) ^ (-(((z - x : ℝ) : ℂ) * (n : ℂ))) *
        (2 : ℂ) ^ ((z : ℂ) * (n : ℂ)) =
        (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 2
      push_cast
      ring
    rw [← mul_assoc, hpow]
  · norm_num

/-- First non-vacuum cold shell of a split normalized squarefree Gram. -/
theorem tendsto_two_cpow_mul_squarefreeMobiusFiniteUnitHardyGramSq_defect_of_lt
    {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    Tendsto (fun n : ℕ =>
      (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) *
        (1 - squarefreeMobiusFiniteUnitHardyGramSq
          (n : ℂ) (x : ℂ) (z : ℂ))) atTop (nhds (1 / 2 : ℂ)) := by
  let y : ℝ := (x + z) / 2
  let X : ℕ → ℂ := fun n =>
    _root_.GaloisForLFunctions.squarefreePartition
      (1 + (x : ℂ) * (n : ℂ))
  let Y : ℕ → ℂ := fun n =>
    _root_.GaloisForLFunctions.squarefreePartition
      (1 + (y : ℂ) * (n : ℂ))
  let Z : ℕ → ℂ := fun n =>
    _root_.GaloisForLFunctions.squarefreePartition
      (1 + (z : ℂ) * (n : ℂ))
  let A : ℕ → ℂ := fun n => X n - 1
  let B : ℕ → ℂ := fun n => Y n - 1
  let C : ℕ → ℂ := fun n => Z n - 1
  let scale : ℕ → ℂ := fun n => (2 : ℂ) ^ ((x : ℂ) * (n : ℂ))
  have hxy : x < y := by dsimp [y]; linarith
  have hyz : y < z := by dsimp [y]; linarith
  have hy : 0 < y := lt_trans hx hxy
  have hA : Tendsto (fun n => scale n * A n) atTop (nhds (1 / 2 : ℂ)) := by
    simpa [scale, A, X] using tendsto_two_cpow_mul_squarefreePartition_sub_one hx
  have hB : Tendsto (fun n => scale n * B n) atTop (nhds 0) := by
    simpa [scale, B, Y] using
      tendsto_slower_two_cpow_mul_squarefreePartition_sub_one_zero hx hxy
  have hC : Tendsto (fun n => scale n * C n) atTop (nhds 0) := by
    simpa [scale, C, Z] using
      tendsto_slower_two_cpow_mul_squarefreePartition_sub_one_zero hx hxz
  have hX : Tendsto X atTop (nhds 1) := by
    simpa [X] using tendsto_squarefreePartition_one_add_real_mul_nat hx
  have hY : Tendsto Y atTop (nhds 1) := by
    simpa [Y] using tendsto_squarefreePartition_one_add_real_mul_nat hy
  have hZ : Tendsto Z atTop (nhds 1) := by
    simpa [Z] using
      tendsto_squarefreePartition_one_add_real_mul_nat (lt_trans hx hxz)
  have hA0 : Tendsto A atTop (nhds 0) := by simpa [A] using hX.sub_const 1
  have hB0 : Tendsto B atTop (nhds 0) := by simpa [B] using hY.sub_const 1
  have hC0 : Tendsto C atTop (nhds 0) := by simpa [C] using hZ.sub_const 1
  have hnum : Tendsto (fun n => scale n * (X n * Z n - Y n ^ 2))
      atTop (nhds (1 / 2 : ℂ)) := by
    have h := (((hA.add hC).add (hA.mul hC0)).sub (hB.const_mul 2)).sub
      (hB.mul hB0)
    convert h using 1
    · funext n
      simp only [A, B, C]
      ring
    · norm_num
  have hden : Tendsto (fun n => X n * Z n) atTop (nhds 1) := by
    simpa using hX.mul hZ
  have hquot := hnum.div hden (by norm_num : (1 : ℂ) ≠ 0)
  have hquot' : Tendsto
      ((fun n => scale n * (X n * Z n - Y n ^ 2)) /
        fun n => X n * Z n) atTop (nhds (1 / 2 : ℂ)) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hxarg : 1 < (1 + (x : ℂ) * (n : ℂ)).re := by
    norm_num [Complex.mul_re]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hzarg : 1 < (1 + (z : ℂ) * (n : ℂ)).re := by
    norm_num [Complex.mul_re]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hz : 0 < z := lt_trans hx hxz
    positivity
  have hX0 : X n ≠ 0 := by
    exact _root_.GaloisForLFunctions.squarefreePartition_ne_zero hxarg
  have hZ0 : Z n ≠ 0 := by
    exact _root_.GaloisForLFunctions.squarefreePartition_ne_zero hzarg
  have hX0' : _root_.GaloisForLFunctions.squarefreePartition
      (1 + (x : ℂ) * (n : ℂ)) ≠ 0 := by simpa [X] using hX0
  have hZ0' : _root_.GaloisForLFunctions.squarefreePartition
      (1 + (z : ℂ) * (n : ℂ)) ≠ 0 := by simpa [Z] using hZ0
  have hZ0'' : _root_.GaloisForLFunctions.squarefreePartition
      (1 + (n : ℂ) * (z : ℂ)) ≠ 0 := by
    rw [show 1 + (n : ℂ) * (z : ℂ) =
      1 + (z : ℂ) * (n : ℂ) by ring]
    exact hZ0'
  simp only [squarefreeMobiusFiniteUnitHardyGramSq, Pi.div_apply,
    scale, X, Y, Z, y]
  push_cast
  field_simp [hX0', hZ0', hZ0'']

/-- Adjacent cold defects recover the slower aperture as an exact prime-two character. -/
theorem tendsto_squarefreeMobiusFiniteUnitHardyGramSq_defect_ratio_of_lt
    {x z : ℝ} (hx : 0 < x) (hxz : x < z) :
    Tendsto (fun n : ℕ =>
      (1 - squarefreeMobiusFiniteUnitHardyGramSq
          ((n + 1 : ℕ) : ℂ) (x : ℂ) (z : ℂ)) /
        (1 - squarefreeMobiusFiniteUnitHardyGramSq
          (n : ℂ) (x : ℂ) (z : ℂ)))
      atTop (nhds ((2 : ℂ) ^ (-(x : ℂ)))) := by
  let D : ℕ → ℂ := fun n =>
    1 - squarefreeMobiusFiniteUnitHardyGramSq
      (n : ℂ) (x : ℂ) (z : ℂ)
  let A : ℕ → ℂ := fun n => (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) * D n
  have hA : Tendsto A atTop (nhds (1 / 2 : ℂ)) := by
    simpa [A, D] using tendsto_two_cpow_mul_squarefreeMobiusFiniteUnitHardyGramSq_defect_of_lt hx hxz
  have hsucc : Tendsto (fun n : ℕ => A (n + 1)) atTop (nhds (1 / 2 : ℂ)) :=
    hA.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => A (n + 1) / A n)
      atTop (nhds 1) := by
    have hdiv := hsucc.div hA (by norm_num : (1 / 2 : ℂ) ≠ 0)
    convert hdiv using 1
    · funext n
      rfl
    · norm_num
  have hscaled := hratio.const_mul ((2 : ℂ) ^ (-(x : ℂ)))
  convert hscaled using 1
  · funext n
    change D (n + 1) / D n =
      (2 : ℂ) ^ (-(x : ℂ)) * (A (n + 1) / A n)
    have hpow : (2 : ℂ) ^ (-(x : ℂ)) *
        (2 : ℂ) ^ ((x : ℂ) * ((n + 1 : ℕ) : ℂ)) =
        (2 : ℂ) ^ ((x : ℂ) * (n : ℂ)) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 2
      push_cast
      ring
    simp only [A]
    by_cases hD : D n = 0
    · simp [hD]
    · field_simp [hD]
      rw [← hpow]
      ring
  · simp

end
end RHTower.HedenmalmThetaSource
