import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralEntries
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourThreeAtomModel

/-!
# The native odd fibre in moving central coordinates

Combining the three-atom lower bound with the four pair energies: for `c = B(1/q) y`,
`Σ c_i c_j (-1)^m J_{2m} ≥ K(q) q⁻⁶ Σ y_i y_j E_{ij}(q) − tail`, where
`E = N¹¹ + 8e^{-3q}N¹² + 18e^{-8q}N¹³ + 72e^{-11q}N²³` is the explicit numerator matrix. A
nonnegative majorant of the basis turns the tail into a diagonal form in `y`.
-/

open Polynomial
namespace RHTower.ThetaCuspOddFourCentralBound
noncomputable section
open ThetaCuspOddCentralTail ThetaCuspOddFourCentralEntries ThetaCuspOddFourThreeAtom

/-- The moving-frame three-atom entry matrix. -/
def centralEntryMat (q : ℝ) (i j : Fin 4) : ℝ :=
  centralNumMat11 q i j + 8*Real.exp (-3*q)*centralNumMat12 q i j +
    18*Real.exp (-8*q)*centralNumMat13 q i j + 72*Real.exp (-11*q)*centralNumMat23 q i j

theorem threeAtomEnergy_eq_central {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, (centralBasis (1/q)).mulVec y i * (centralBasis (1/q)).mulVec y j *
      threeAtomOddEntry q (i.val+j.val+1)) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j) / q^6 := by
  have h11 := centralEnergy11 hq y
  have h12 := centralEnergy12 hq y
  have h13 := centralEnergy13 hq y
  have h23 := centralEnergy23 hq y
  have hsplit : (∑ i : Fin 4, ∑ j : Fin 4, (centralBasis (1/q)).mulVec y i *
      (centralBasis (1/q)).mulVec y j * threeAtomOddEntry q (i.val+j.val+1)) =
      (∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r * (centralBasis (1/q)).mulVec y s *
        (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) +
      8*Real.exp (-3*q)*(∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r *
        (centralBasis (1/q)).mulVec y s *
        (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) +
      18*Real.exp (-8*q)*(∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r *
        (centralBasis (1/q)).mulVec y s *
        (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) +
      72*Real.exp (-11*q)*(∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r *
        (centralBasis (1/q)).mulVec y s *
        (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) := by
    simp only [threeAtomOddEntry, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hsplit, h11, h12, h13, h23]
  simp only [centralEntryMat, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A nonnegative majorant of a basis turns the absolute quadratic form into a diagonal form. -/
theorem abs_form_le_diag (B G T : Matrix (Fin 4) (Fin 4) ℝ) (hG : ∀ i k, |B i k| ≤ G i k)
    (hT : ∀ i j, 0 ≤ T i j) (y : Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, |B.mulVec y i| * |B.mulVec y j| * T i j) ≤
      ∑ k : Fin 4, ((∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, G i k * T i j * G j l) +
        (∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, G i l * T i j * G j k))/2 * y k^2 := by
  have hG0 : ∀ i k, 0 ≤ G i k := fun i k => (abs_nonneg _).trans (hG i k)
  have he (i : Fin 4) : |B.mulVec y i| ≤ ∑ k : Fin 4, G i k * |y k| := by
    simp only [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hG i k) (abs_nonneg _)
  calc (∑ i : Fin 4, ∑ j : Fin 4, |B.mulVec y i| * |B.mulVec y j| * T i j)
      ≤ ∑ i : Fin 4, ∑ j : Fin 4, (∑ k : Fin 4, G i k * |y k|) * (∑ l : Fin 4, G j l * |y l|) * T i j := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul (he i) (he j) (abs_nonneg _)
          (Finset.sum_nonneg fun k _ => mul_nonneg (hG0 i k) (abs_nonneg _))) (hT i j)
    _ = ∑ k : Fin 4, ∑ l : Fin 4, (∑ i : Fin 4, ∑ j : Fin 4, G i k * T i j * G j l) * (|y k| * |y l|) := by
        simp only [Fin.sum_univ_four]
        ring
    _ ≤ ∑ k : Fin 4, ∑ l : Fin 4, (∑ i : Fin 4, ∑ j : Fin 4, G i k * T i j * G j l) *
          ((y k^2 + y l^2)/2) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hG0 i k) (hT i j)) (hG0 j l))
        nlinarith [sq_nonneg (|y k| - |y l|), sq_abs (y k), sq_abs (y l)]
    _ = _ := by
        simp only [Fin.sum_univ_four]
        ring


/-- An entrywise majorant of the central basis for `v = 1/q ≤ 1/3`. -/
def basisMajorant : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 5/4, 5/4; 0, 1/72, 5/144, 5/96; 0, 0, 1/6912, 1/2304; 0, 0, 0, 1/1161216]

theorem abs_centralBasis_le {q : ℝ} (hq : 3 ≤ q) (i k : Fin 4) :
    |centralBasis (1/q) i k| ≤ basisMajorant i k := by
  have hv0 : 0 ≤ 1/q := by positivity
  have hv : 1/q ≤ 1/3 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  set v := 1/q
  have h2 : v^2 ≤ v/3 := by nlinarith
  have h3 : v^3 ≤ v^2/3 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)]
  have h2' : v^2 ≤ 1/9 := by nlinarith
  have h3' : v^3 ≤ 1/27 := by nlinarith
  have h3L : 0 ≤ v^3 := pow_nonneg hv0 _
  have h2L : 0 ≤ v^2 := sq_nonneg _
  fin_cases i <;> fin_cases k <;> norm_num [centralBasis, basisMajorant] <;>
    (try apply abs_le.mpr) <;> (try constructor) <;> nlinarith

/-- Factorial weights of the Cauchy tail in units of `f₁²`. -/
def tailFactor (i j : Fin 4) : ℝ :=
  ((2*(i.val+j.val+1)).factorial : ℝ)/(3/20)^(2*(i.val+j.val+1))

/-- Diagonal tail weights in central coordinates. -/
def tailWeight (k : Fin 4) : ℝ :=
  ((∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, basisMajorant i k * tailFactor i j * basisMajorant j l) +
    (∑ l : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, basisMajorant i l * tailFactor i j * basisMajorant j k))/2

theorem sourceTerm_one_sq (x : ℝ) :
    thetaCuspSourceTerm x 1^2 = 4*thetaCuspSingleAtomReflectionScale 1 x^2*
      Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)*
      (2*thetaCuspSingleAtomReflectionScale 1 x-3)^2 := by
  rw [thetaCuspSourceTerm_one_eq_scale_profile]
  have he : Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 =
      Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, he]
  ring

/-- **Native odd fibre in moving central coordinates.** On `q ≥ 3`, with `c = B(1/q) y`,
the native odd form is at least `K(q)` times `q⁻⁶ yᵀE(q)y` minus a diagonal tail. -/
theorem nativeOddForm_ge_central {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (y : Fin 4 → ℝ) :
    let q := thetaCuspSingleAtomReflectionScale 1 x
    let c := (centralBasis (1/q)).mulVec y
    4*q^2*Real.exp (x-2*q)*((∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralEntryMat q i j)/q^6 -
        8000*(2*q-3)^2*Real.exp (-(529/50)*q)*∑ k : Fin 4, tailWeight k * y k^2) ≤
      ∑ i : Fin 4, ∑ j : Fin 4, c i*c j*(-1:ℝ)^(i.val+j.val+1)*
        thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x := by
  intro q c
  have hq0 : q ≠ 0 := by positivity
  have h := nativeOddForm_ge_threeAtom hq c
  rw [threeAtomEnergy_eq_central hq0 y] at h
  -- the tail as a diagonal form
  have hT : (∑ i : Fin 4, ∑ j : Fin 4, |c i| * |c j| * threeAtomTailBound x (i.val+j.val+1)) ≤
      4*q^2*Real.exp (x-2*q)*(8000*(2*q-3)^2*Real.exp (-(529/50)*q)*
        ∑ k : Fin 4, tailWeight k * y k^2) := by
    have hfac : ∀ i j : Fin 4, threeAtomTailBound x (i.val+j.val+1) =
        (8000*thetaCuspSourceTerm x 1^2*Real.exp (-(529/50)*q))*tailFactor i j := by
      intro i j
      unfold threeAtomTailBound tailFactor
      ring
    have hpos : 0 ≤ 8000*thetaCuspSourceTerm x 1^2*Real.exp (-(529/50)*q) := by positivity
    have hd := abs_form_le_diag (centralBasis (1/q)) basisMajorant tailFactor
      (abs_centralBasis_le hq) (fun i j => by unfold tailFactor; positivity) y
    calc (∑ i : Fin 4, ∑ j : Fin 4, |c i| * |c j| * threeAtomTailBound x (i.val+j.val+1))
        = (8000*thetaCuspSourceTerm x 1^2*Real.exp (-(529/50)*q)) *
            ∑ i : Fin 4, ∑ j : Fin 4, |c i| * |c j| * tailFactor i j := by
          simp only [hfac, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (8000*thetaCuspSourceTerm x 1^2*Real.exp (-(529/50)*q)) *
            ∑ k : Fin 4, tailWeight k * y k^2 := by
          refine mul_le_mul_of_nonneg_left (hd.trans_eq ?_) hpos
          refine Finset.sum_congr rfl fun k _ => ?_
          rfl
      _ = _ := by
          rw [sourceTerm_one_sq]
          ring
  have hK : 0 ≤ 4*q^2*Real.exp (x-2*q) := by positivity
  nlinarith [h, hT]

end
end RHTower.ThetaCuspOddFourCentralBound
