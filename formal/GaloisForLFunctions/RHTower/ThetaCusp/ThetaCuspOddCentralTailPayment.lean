import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedCauchyTail

/-!
# Complete reflected tail in odd central coordinates

Contracting the all-order Cauchy estimate with the exact odd central basis
controls the native-minus-two-atom quadratic uniformly on the scale-five
ray. Weighted double sums keep every cross term and give a bound for every
coefficient vector, not only a selected direction.
-/

namespace RHTower.ThetaCuspOddCentralTail
noncomputable section
open Matrix

/-- Native odd-polynomial coefficients from normalized central coordinates, with inverse scale v. -/
def centralBasis (v : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1-v/6, 5/4-5*v/12+v^2/12, 5/4-5*v/8+v^2/4-3*v^3/56;
    0, -v/24, -5*v/48+5*v^2/192, -5*v/32+5*v^2/64-7*v^3/384;
    0, 0, v^2/768, v^2/256-v^3/768;
    0, 0, 0, -v^3/43008]

private def coefficientMajorant : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,5/4,5/4;0,1/120,1/48,1/32;0,0,1/19200,1/6400;0,0,0,1/5376000]

private theorem centralBasis_abs_le {v : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/5)
    (i j : Fin 4) : |centralBasis v i j| ≤ coefficientMajorant i j := by
  have h2 : v^2 ≤ v/5 := by nlinarith
  have h3 : v^3 ≤ v^2/5 := by
    nlinarith only [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hvU)]
  have h3L : 0 ≤ v^3 := pow_nonneg hv _
  fin_cases i <;> fin_cases j <;> norm_num [centralBasis, coefficientMajorant]
  all_goals apply abs_le.mpr; constructor <;> nlinarith only [hv, hvU, h2, h3, h3L, sq_nonneg v]

private def envelope (y : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  ∑ k : Fin 4, coefficientMajorant i k*|y k|

private theorem envelope_nonneg (y : Fin 4 → ℝ) (i : Fin 4) : 0 ≤ envelope y i := by
  fin_cases i <;> norm_num [envelope, Fin.sum_univ_succ, coefficientMajorant] <;> positivity

private theorem coefficients_abs_le {v : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1/5)
    (y : Fin 4 → ℝ) (i : Fin 4) : |(centralBasis v).mulVec y i| ≤ envelope y i := by
  change |∑ j : Fin 4, centralBasis v i j*y j| ≤ envelope y i
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (centralBasis_abs_le hv hvU i j) (abs_nonneg _)

private def jetMajorant (i j : Fin 4) : ℝ :=
  ((2*(i.val+j.val+1)).factorial:ℝ)/500000000/(3/20)^(2*(i.val+j.val+1))

private def simpleJet (i j : Fin 4) : ℝ :=
  ![1/5000000,1/10000,13/100,320,1300000,7500000000,60000000000000]
    ⟨i.val+j.val, by omega⟩

private theorem jetMajorant_le (i j : Fin 4) : jetMajorant i j ≤ simpleJet i j := by
  fin_cases i <;> fin_cases j <;> norm_num [jetMajorant, simpleJet]

private theorem simpleJet_nonneg (i j : Fin 4) : 0 ≤ simpleJet i j := by
  fin_cases i <;> fin_cases j <;> norm_num [simpleJet]

private theorem coefficientMajorant_nonneg (i j : Fin 4) : 0 ≤ coefficientMajorant i j := by
  fin_cases i <;> fin_cases j <;> norm_num [coefficientMajorant]

private def rowMass (i : Fin 4) : ℝ := ∑ k : Fin 4, coefficientMajorant i k

private def diagonalPayment (k : Fin 4) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, simpleJet i j*
    (coefficientMajorant i k*rowMass j+rowMass i*coefficientMajorant j k)/2

private theorem diagonalPayment_le (k : Fin 4) : diagonalPayment k ≤ 4 := by
  fin_cases k <;> norm_num [diagonalPayment, rowMass, simpleJet, coefficientMajorant,
    Fin.sum_univ_succ]

private theorem envelope_product_le (y : Fin 4 → ℝ) (i j : Fin 4) :
    envelope y i*envelope y j ≤
      ∑ k : Fin 4, (coefficientMajorant i k*rowMass j+rowMass i*coefficientMajorant j k)/2*y k^2 := by
  have hpair (k l : Fin 4) : |y k| * |y l| ≤ (y k^2+y l^2)/2 := by
    nlinarith only [sq_nonneg (|y k|-|y l|), sq_abs (y k), sq_abs (y l)]
  calc
    _ = ∑ k : Fin 4, ∑ l : Fin 4,
        (coefficientMajorant i k*coefficientMajorant j l)*(|y k| * |y l|) := by
      simp only [envelope, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ ∑ k : Fin 4, ∑ l : Fin 4,
        (coefficientMajorant i k*coefficientMajorant j l)*((y k^2+y l^2)/2) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (hpair k l)
        (mul_nonneg (coefficientMajorant_nonneg i k) (coefficientMajorant_nonneg j l))
    _ = _ := by
      have he (k l : Fin 4) :
          (coefficientMajorant i k*coefficientMajorant j l)*((y k^2+y l^2)/2)=
            coefficientMajorant j l*(coefficientMajorant i k/2*y k^2)+
            coefficientMajorant i k*(coefficientMajorant j l/2*y l^2) := by ring
      simp_rw [he, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k l : Fin 4 =>
        coefficientMajorant i k*(coefficientMajorant j l/2*y l^2))]
      simp only [← Finset.sum_mul, ← Finset.sum_add_distrib, rowMass]
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem envelope_payment (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, envelope y i*envelope y j*jetMajorant i j) ≤
      4*(∑ k : Fin 4, y k^2) := by
  calc
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, simpleJet i j*
        (∑ k : Fin 4, (coefficientMajorant i k*rowMass j+rowMass i*coefficientMajorant j k)/2*y k^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ envelope y i*envelope y j*simpleJet i j :=
          mul_le_mul_of_nonneg_left (jetMajorant_le i j)
            (mul_nonneg (envelope_nonneg y i) (envelope_nonneg y j))
        _ ≤ _ := by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_right
            (envelope_product_le y i j) (simpleJet_nonneg i j)
    _ = ∑ k : Fin 4, diagonalPayment k*y k^2 := by
      simp only [Finset.mul_sum]
      have he (i : Fin 4) :
          (∑ j : Fin 4, ∑ k : Fin 4, simpleJet i j*
            ((coefficientMajorant i k*rowMass j+rowMass i*coefficientMajorant j k)/2*y k^2))=
          ∑ k : Fin 4, ∑ j : Fin 4, simpleJet i j*
            ((coefficientMajorant i k*rowMass j+rowMass i*coefficientMajorant j k)/2*y k^2) :=
        Finset.sum_comm
      simp_rw [he]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [diagonalPayment, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ k : Fin 4, 4*y k^2 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (diagonalPayment_le k) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- The complete omitted source quadratic costs at most one tenth of the normalized central energy. -/
theorem native_central_tail_payment {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    |∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
      (thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)| ≤
      (8*q*thetaCuspSourceTerm x 1^2)/10*(∑ k : Fin 4, y k^2) := by
  dsimp only
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let c := (centralBasis (1/q)).mulVec y
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hv : 0 ≤ 1/q := by positivity
  have hvU : 1/q ≤ (1/5:ℝ) := by
    apply (div_le_iff₀ hq0).mpr
    dsimp [q]
    linarith
  have hc := coefficients_abs_le hv hvU y
  have hj (i j : Fin 4) :
      |thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x-
        thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x| ≤ jetMajorant i j*f^2 := by
    convert ThetaCuspReflectedCauchyTail.native_twoAtom_cauchy_error (2*(i.val+j.val+1)) hq using 1
    dsimp [jetMajorant, f]
    ring
  calc
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, (envelope y i*envelope y j*jetMajorant i j)*f^2 := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      have hm := mul_le_mul (hc i) (hc j) (abs_nonneg _) (envelope_nonneg y i)
      have h := mul_le_mul hm (hj i j) (abs_nonneg _)
        (mul_nonneg (envelope_nonneg y i) (envelope_nonneg y j))
      convert h using 1; ring
    _ = f^2*(∑ i : Fin 4, ∑ j : Fin 4, envelope y i*envelope y j*jetMajorant i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ f^2*(4*(∑ k : Fin 4, y k^2)) :=
      mul_le_mul_of_nonneg_left (envelope_payment y) (sq_nonneg _)
    _ ≤ _ := by
      have hs : 0 ≤ ∑ k : Fin 4, y k^2 := Finset.sum_nonneg fun k _ => sq_nonneg _
      have h := mul_nonneg (show 0 ≤ q-5 by dsimp [q]; linarith)
        (mul_nonneg (sq_nonneg f) hs)
      change f^2*(4*(∑ k : Fin 4, y k^2)) ≤ (8*q*f^2)/10*(∑ k : Fin 4, y k^2)
      nlinarith only [h]

end
end RHTower.ThetaCuspOddCentralTail
