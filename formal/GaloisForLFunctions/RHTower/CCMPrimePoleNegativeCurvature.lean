import GaloisForLFunctions.RHTower.CCMPrimePoleJumpRates

/-!
# A smooth negative-curvature witness for the cutoff prime generator

At aperture `log (21/10)` the actual signed prime indices are `2, 3, 4`.
Four exact row evaluations reduce the iterated energy of an explicit smooth
function to a polynomial in `log 2` and `log 3`, which is strictly negative.
This concerns the prime jump generator, not the full Weil form.
The quantitative lower-curvature estimate is in `CCMPrimePoleCurvatureBounds`.
-/

noncomputable section
open scoped BigOperators ContDiff
namespace RHTower.PrimeCurvatureCounterexample
open HTGeometry.JumpBochner

def aperture : SuzukiPositiveAperture :=
  ⟨Real.log (21/10), Real.log_pos (by norm_num)⟩

theorem aperture_exp : Real.exp (2 * aperture.1) = (441/100 : ℝ) := by
  change Real.exp (2 * Real.log (21/10)) = _
  rw [show 2 * Real.log (21/10) = Real.log (21/10) + Real.log (21/10) by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 21/10)]
  norm_num

theorem aperture_indices : ccmPrimePoleJumpIndices aperture =
    {(2,false), (2,true), (3,false), (3,true), (4,false), (4,true)} := by
  have hf : ⌊(441/100 : ℝ)⌋₊ = 4 := by norm_num
  rw [ccmPrimePoleJumpIndices, aperture_exp, hf]
  decide

theorem rate_at_log {q : ℝ} (hq : 0 < q) {n : ℕ} (hn : 0 < n) (b : Bool) :
    ccmPrimePoleJumpRate aperture (n,b) (Real.log q) =
      if (10/21 : ℝ) ≤ q ∧ q ≤ 21/10 then
        if (10/21 : ℝ) ≤ ccmPrimePoleMultiplicativeTarget (n,b) q ∧
            ccmPrimePoleMultiplicativeTarget (n,b) q ≤ 21/10 then
          ArithmeticFunction.vonMangoldt n * (if b then q*n+1 else q+n) / ((n : ℝ)*(q+1))
        else 0
      else 0 := by
  convert ccmPrimePoleJumpRate_log_cutoff aperture (by norm_num : (0 : ℝ) < 21/10)
    rfl hq hn b using 1 <;> norm_num

def polynomial (q : ℝ) : ℝ :=
  1946 - (156596/15)*q + (42369/2)*q^2 - (122059/6)*q^3 + 9258*q^4 - (7998/5)*q^5

def witness (x : ℝ) : ℝ := polynomial (Real.exp x)

theorem witness_smooth : ContDiff ℝ ∞ witness := by
  unfold witness polynomial
  fun_prop

private theorem mangoldt_two : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
  ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
private theorem mangoldt_three : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
  ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
private theorem mangoldt_four : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
  change ArithmeticFunction.vonMangoldt (2^2) = _
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), mangoldt_two]

def row (F : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∑ j ∈ ccmPrimePoleJumpIndices aperture,
    ccmPrimePoleJumpRate aperture j (Real.log q) * F (ccmPrimePoleJumpShift j (Real.log q))

private theorem row_expansion (F : ℝ → ℝ) (q : ℝ) : row F q =
    ccmPrimePoleJumpRate aperture (2,false) (Real.log q) * F (ccmPrimePoleJumpShift (2,false) (Real.log q)) +
    ccmPrimePoleJumpRate aperture (2,true) (Real.log q) * F (ccmPrimePoleJumpShift (2,true) (Real.log q)) +
    ccmPrimePoleJumpRate aperture (3,false) (Real.log q) * F (ccmPrimePoleJumpShift (3,false) (Real.log q)) +
    ccmPrimePoleJumpRate aperture (3,true) (Real.log q) * F (ccmPrimePoleJumpShift (3,true) (Real.log q)) +
    ccmPrimePoleJumpRate aperture (4,false) (Real.log q) * F (ccmPrimePoleJumpShift (4,false) (Real.log q)) +
    ccmPrimePoleJumpRate aperture (4,true) (Real.log q) * F (ccmPrimePoleJumpShift (4,true) (Real.log q)) := by simp [row, aperture_indices, add_assoc]

theorem row_two (F : ℝ → ℝ) : row F (2) =
    (2*Real.log 2/3)*F (Real.log 1) + (5*Real.log 3/9)*F (Real.log (2/3)) + (Real.log 2/2)*F (Real.log (1/2)) := by
  norm_num [row, aperture_indices, rate_at_log, ccmPrimePoleJumpShift_log,
    ccmPrimePoleMultiplicativeTarget, mangoldt_two, mangoldt_three, mangoldt_four]
  ring

theorem row_one (F : ℝ → ℝ) : row F 1 =
    (3*Real.log 2/4)*F (Real.log (1/2)) + (3*Real.log 2/4)*F (Real.log 2) := by
  rw [row_expansion]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (2 : ℕ)) false,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (2 : ℕ)) false]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (2 : ℕ)) true,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (2 : ℕ)) true]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (3 : ℕ)) false,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (3 : ℕ)) false]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (3 : ℕ)) true,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (3 : ℕ)) true]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (4 : ℕ)) false,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (4 : ℕ)) false]
  rw [rate_at_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (4 : ℕ)) true,
    ccmPrimePoleJumpShift_log (by norm_num : (0 : ℝ) < 1) (by norm_num : 0 < (4 : ℕ)) true]
  norm_num [ccmPrimePoleMultiplicativeTarget, mangoldt_two, mangoldt_three, mangoldt_four]
  ring

theorem row_two_thirds (F : ℝ → ℝ) : row F (2/3) =
    (7*Real.log 2/10)*F (Real.log (4/3)) + (3*Real.log 3/5)*F (Real.log 2) := by
  norm_num [row, aperture_indices, rate_at_log, ccmPrimePoleJumpShift_log,
    ccmPrimePoleMultiplicativeTarget, mangoldt_two, mangoldt_three, mangoldt_four]
  ring

theorem row_half (F : ℝ → ℝ) : row F (1/2) =
    (2*Real.log 2/3)*F (Real.log 1) + (5*Real.log 3/9)*F (Real.log (3/2)) + (Real.log 2/2)*F (Real.log 2) := by
  norm_num [row, aperture_indices, rate_at_log, ccmPrimePoleJumpShift_log,
    ccmPrimePoleMultiplicativeTarget, mangoldt_two, mangoldt_three, mangoldt_four]
  ring

private theorem generator_as_row (f : ℝ → ℝ) (q : ℝ) :
    generator (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f (Real.log q) = row (fun y => f y - f (Real.log q)) q := rfl

private theorem energy_as_row (f g : ℝ → ℝ) (q : ℝ) :
    energyDensity (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift f g (Real.log q) =
        row (fun y => (f y - f (Real.log q)) * (g y - g (Real.log q))) q / 2 := by
  simp only [energyDensity, row, difference, mul_assoc]

theorem gammaTwo_witness_eq :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift witness (Real.log 2) =
        (125/3 : ℝ)*(Real.log 2)^2 - (13805/216 : ℝ)*Real.log 2*Real.log 3 +
          (1696/81 : ℝ)*(Real.log 3)^2 := by
  simp only [gammaTwo, generator_as_row, energy_as_row, row_two, row_one,
    row_two_thirds, row_half]
  norm_num [witness, polynomial, Real.exp_log]
  ring

theorem gammaTwo_witness_neg :
    gammaTwo (ccmPrimePoleJumpIndices aperture) (ccmPrimePoleJumpRate aperture)
      ccmPrimePoleJumpShift witness (Real.log 2) < 0 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : 3*Real.log 2 ≤ 2*Real.log 3 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2^3)
      (by norm_num : (2 : ℝ)^3 < 3^2)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h.le
  have hhi : 5*Real.log 3 ≤ 8*Real.log 2 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^5)
      (by norm_num : (3 : ℝ)^5 < 2^8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    exact h.le
  rw [gammaTwo_witness_eq]
  have hp : 0 ≤ (2*Real.log 3-3*Real.log 2)*(8*Real.log 2-5*Real.log 3) :=
    mul_nonneg (by linarith) (by linarith)
  have hc : 0 ≤ Real.log 2*(8*Real.log 2-5*Real.log 3) :=
    mul_nonneg hl.le (by linarith)
  nlinarith [sq_pos_of_pos hl]

theorem witness_point_mem : Real.log 2 ∈ centralInterval aperture.1 := by
  change Real.log 2 ∈ centralInterval (Real.log (21/10))
  rw [log_mem_centralInterval_log_iff (by norm_num : (0 : ℝ) < 21/10)
    (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Nonnegative pointwise curvature fails even for smooth functions at an interior
cutoff point. This statement does not impose the Weil source-core conditions. -/
theorem exists_smooth_negative_curvature :
    ∃ (a : SuzukiPositiveAperture) (f : ℝ → ℝ), ContDiff ℝ ∞ f ∧
      ∃ x ∈ centralInterval a.1,
        gammaTwo (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a)
          ccmPrimePoleJumpShift f x < 0 :=
  ⟨aperture, witness, witness_smooth, Real.log 2, witness_point_mem, gammaTwo_witness_neg⟩

end RHTower.PrimeCurvatureCounterexample
