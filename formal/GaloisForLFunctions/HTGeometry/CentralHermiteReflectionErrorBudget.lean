import Mathlib.Tactic

namespace HTGeometry
noncomputable section

/-- Normalized entry ceilings for the complete scale-eight reflection error. -/
def centralErrorCeiling (k : ℕ) : ℝ :=
  match k with
  | 0 => 1/200000000 | 1 => 1/5000000 | 2 => 1/100000
  | 3 => 1/3000 | 4 => 1/70 | 5 => 3/4 | _ => 40

/-- Gaussian moments used only as an explicit ceiling for the source moments. -/
def centralGaussianMomentCeiling (k : ℕ) : ℝ :=
  match k with
  | 0 => 1 | 1 => 1 | 2 => 3 | 3 => 15 | 4 => 105 | 5 => 945 | _ => 10395

/-- Exact finite convolution ceiling at q = 8 after polynomial-exponential monotonicity. -/
def scaleEightReflectionErrorMajorant (k : Fin 7) : ℝ :=
  ∑ j ∈ Finset.range (k.val+1), ((2*k.val).choose (2*j) : ℝ)*
    ((3/2 : ℝ)*centralGaussianMomentCeiling j)*
    (2*(36 : ℝ)^(k.val-j)/(800000000 : ℝ)+
      (144 : ℝ)^(k.val-j)/(800000000 : ℝ)^2)

/-- Each finite convolution fits the entry ceiling exactly. -/
theorem scaleEightReflectionErrorMajorant_le (k : Fin 7) :
    scaleEightReflectionErrorMajorant k ≤ centralErrorCeiling k.val := by
  fin_cases k <;> norm_num [scaleEightReflectionErrorMajorant,centralGaussianMomentCeiling,
    centralErrorCeiling,Finset.sum_range_succ,Nat.choose]

/-- Uniform coefficient majorants for the inverse central-Hermite change of coordinates. -/
def centralCoefficientMajorant (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![|y 0|+|y 1|+3*|y 2|+15*|y 3|,
    |y 1|+6*|y 2|+45*|y 3|, |y 2|+15*|y 3|, |y 3|]

/-- All sixteen propagated entry errors fit in a diagonal four-coordinate budget. -/
theorem centralError_majorant_le (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      centralErrorCeiling (i.val+j.val)*centralCoefficientMajorant y i*
        centralCoefficientMajorant y j) ≤
      (1/8 : ℝ)*(y 0)^2+(1/8 : ℝ)*(y 1)^2+2*(y 2)^2+70*(y 3)^2 := by
  have h01 := sq_nonneg (|y 0|-|y 1|)
  have h02 := sq_nonneg (|y 0|-|y 2|)
  have h03 := sq_nonneg (|y 0|-|y 3|)
  have h12 := sq_nonneg (|y 1|-|y 2|)
  have h13 := sq_nonneg (|y 1|-|y 3|)
  have h23 := sq_nonneg (|y 2|-|y 3|)
  have h0 := sq_nonneg (y 0)
  have h1 := sq_nonneg (y 1)
  have h2 := sq_nonneg (y 2)
  have h3 := sq_nonneg (y 3)
  have ha0 : |y 0|^2 = (y 0)^2 := sq_abs _
  have ha1 : |y 1|^2 = (y 1)^2 := sq_abs _
  have ha2 : |y 2|^2 = (y 2)^2 := sq_abs _
  have ha3 : |y 3|^2 = (y 3)^2 := sq_abs _
  norm_num [Fin.sum_univ_succ,centralErrorCeiling,centralCoefficientMajorant]
  nlinarith only [h01,h02,h03,h12,h13,h23,h0,h1,h2,h3,ha0,ha1,ha2,ha3]

/-- Inverse central coordinates before division by their physical powers of eight q. -/
def centralUnscaledCoefficients (v : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![y 0-y 1+3*y 2-15*y 3,
    y 1+(v-6)*y 2+(4*v^2-15*v+45)*y 3,
    y 2+(5*v-15)*y 3, y 3]

/-- The physical central-coordinate map has the coefficient majorant used above. -/
theorem centralUnscaledCoefficients_abs_le {v : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/8)
    (y : Fin 4 → ℝ) (i : Fin 4) :
    |centralUnscaledCoefficients v y i| ≤ centralCoefficientMajorant y i := by
  have hv6 : |v-6| ≤ 6 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hv15 : |5*v-15| ≤ 15 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hv45 : |4*v^2-15*v+45| ≤ 45 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg v,mul_nonneg hv (show 0 ≤ 1/8-v by linarith)]
  fin_cases i
  · change |y 0-y 1+3*y 2-15*y 3| ≤ |y 0|+|y 1|+3*|y 2|+15*|y 3|
    calc
      _ ≤ |y 0-y 1+3*y 2|+|15*y 3| := abs_sub _ _
      _ ≤ (|y 0-y 1|+|3*y 2|)+|15*y 3| := by gcongr; exact abs_add_le _ _
      _ ≤ (|y 0|+|y 1|)+|3*y 2|+|15*y 3| := by gcongr; exact abs_sub _ _
      _ = _ := by norm_num [abs_mul]
  · change |y 1+(v-6)*y 2+(4*v^2-15*v+45)*y 3| ≤ |y 1|+6*|y 2|+45*|y 3|
    calc
      _ ≤ |y 1+(v-6)*y 2|+|(4*v^2-15*v+45)*y 3| := abs_add_le _ _
      _ ≤ |y 1|+|(v-6)*y 2|+|(4*v^2-15*v+45)*y 3| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by simp only [abs_mul]; gcongr
  · change |y 2+(5*v-15)*y 3| ≤ |y 2|+15*|y 3|
    exact (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
  · exact le_rfl

/-- The complete coordinate error budget retains every off-diagonal contribution. -/
theorem centralError_quadratic_le {v : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/8)
    (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      centralErrorCeiling (i.val+j.val)*|centralUnscaledCoefficients v y i| *
        |centralUnscaledCoefficients v y j|) ≤
      (1/8 : ℝ)*(y 0)^2+(1/8 : ℝ)*(y 1)^2+2*(y 2)^2+70*(y 3)^2 := by
  apply le_trans ?_ (centralError_majorant_le y)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have he : 0 ≤ centralErrorCeiling (i.val+j.val) := by
    unfold centralErrorCeiling
    split <;> norm_num
  have hb (k : Fin 4) := centralUnscaledCoefficients_abs_le hv hvU y k
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (hb i) he) (hb j) (abs_nonneg _)
      (mul_nonneg he ((abs_nonneg _).trans (hb i)))

end
end HTGeometry
