import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.CountingHolography.Sections.TheSignedDegreeAtTheNearestUpperSquare

/-!
# Variation of the smooth part of the square-generator logarithm

At each positive conductor the bounded correction costs a quadratic
allowance. The leading signed reading has subcubic total variation.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset SquareRootThreshold SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticScatteringHolography RenormalizedIntersectionTheory Zeta23

/-- Logarithm of the ordinary generator at its original diagonal multiplicity. -/
def diagonalOrdinaryLog (n : ℕ) := Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)

/-- The leading, smooth, signed part of minus the diagonal log generator. -/
def squareLongReading (n : ℕ) := (n:ℝ)^2*squareLongTrace (2*Real.log n)

private theorem log_two_shift {x : ℝ} (hx : 0 < x) : 2*Real.log x+Real.log 4=2*Real.log (2*x) := by
  rw [Real.log_mul two_ne_zero hx.ne',show (4:ℝ)=2^2 by norm_num,Real.log_pow]
  push_cast
  ring

/-- The strip estimate bounds the long trace by a three-quarter power of the root. -/
theorem squareLongTrace_root_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ {x : ℝ}, 1 ≤ x →
    |squareLongTrace (2*Real.log x)| ≤ C*x^(3/4:ℝ) := by
  have hw : zetaZeroWidth ≤ 3/8 := ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans (by norm_num)
  obtain ⟨B,hB⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le (by norm_num : (0:ℝ) ≤ 3/8)).mpr hw
  have h {y : ℝ} (hy : 1 ≤ y) : |realSplineTrace (2*Real.log y)| ≤ |B| * y^(3/4:ℝ) := by
    have hh := hB (2*Real.log y) (mul_nonneg two_pos.le (Real.log_nonneg hy))
    rw [orbitCorr_splineCycle_eq] at hh
    have he : Real.exp ((3/8)*(2*Real.log y))=y^(3/4:ℝ) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hy)]; congr 1; ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (zero_le_one.trans hy) _))
  refine ⟨4*|B|+2*|B| * (2:ℝ)^(3/4:ℝ),by positivity,fun {x} hx => ?_⟩
  have hx₀ := zero_lt_one.trans_le hx
  have h₁ := h hx
  have h₂ := h (show 1 ≤ 2*x by linarith only [hx])
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx₀.le] at h₂
  have hh := abs_sub_le (4*realSplineTrace (2*Real.log x)) 0 (2*realSplineTrace (2*Real.log (2*x)))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  norm_num at hh
  rw [squareLongTrace,log_two_shift hx₀]
  linarith only [hh,h₁,h₂]

/-- Moving either root by at most one changes the complete long-lag trace by O(x^(-1/4)). -/
theorem squareLongTrace_unit_root_step : ∃ C : ℝ, 0 ≤ C ∧ ∀ {x y : ℝ}, 1 ≤ x → x ≤ y → y ≤ x+1 →
    |squareLongTrace (2*Real.log y)-squareLongTrace (2*Real.log x)| ≤ C*x^(-(1/4):ℝ) := by
  obtain ⟨C,hC,h⟩ := realSplineTrace_square_power_gap (β := 0) zero_le_one
  have he : 2*zetaZeroWidth+0-1 ≤ -(1/4) := by linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]
  refine ⟨6*C,mul_nonneg (by norm_num) hC,fun {x y} hx hxy hy => ?_⟩
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  have hx₂ : 1 ≤ 2*x := by linarith only [hx]
  have h₁ := (h hx hxy (by rw [Real.rpow_zero,mul_one]; linarith only [hy])).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx he) hC)
  have h₂ := (h hx₂ (show 2*x ≤ 2*y from mul_le_mul_of_nonneg_left hxy two_pos.le)
    (by rw [Real.rpow_zero,mul_one]; linarith only [hy])).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx₂ he) hC)
  have hp : (2*x)^(-(1/4):ℝ) ≤ x^(-(1/4):ℝ) := Real.rpow_le_rpow_of_nonpos hx₀
    (by linarith only [hx₀]) (by norm_num)
  have H := abs_sub_le
    (4*(realSplineTrace (2*Real.log y)-realSplineTrace (2*Real.log x))) 0
    (2*(realSplineTrace (2*Real.log (2*y))-realSplineTrace (2*Real.log (2*x))))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at H
  norm_num at H
  unfold squareLongTrace
  rw [log_two_shift hx₀,log_two_shift hy₀]
  rw [show 4*realSplineTrace (2*Real.log y)-2*realSplineTrace (2*Real.log (2*y))-
    (4*realSplineTrace (2*Real.log x)-2*realSplineTrace (2*Real.log (2*x))) =
    4*(realSplineTrace (2*Real.log y)-realSplineTrace (2*Real.log x))-
    2*(realSplineTrace (2*Real.log (2*y))-realSplineTrace (2*Real.log (2*x))) by ring]
  linarith only [H,h₁,h₂,mul_le_mul_of_nonneg_left hp hC]

/-- Quadratically weighted long readings have subcubic total variation
through every initial set of square conductors. -/
theorem squareLongReading_variation : ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
    |squareLongReading (M+2)|+∑ i ∈ range M, |squareLongReading (i+3)-squareLongReading (i+2)| ≤
      C*((M:ℝ)+2)^(11/4:ℝ) := by
  obtain ⟨A,hA,hg⟩ := squareLongTrace_root_growth
  obtain ⟨B,hB,hi⟩ := squareLongTrace_unit_root_step
  let C := 3*A+4*B
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpow (x : ℝ) (hx : 0 < x) :
      x^2*x^(3/4:ℝ)=x^(11/4:ℝ) ∧ x*x^(3/4:ℝ)=x^(7/4:ℝ) ∧
      x^2*x^(-(1/4):ℝ)=x^(7/4:ℝ) ∧ x*x^(7/4:ℝ)=x^(11/4:ℝ) := by
    have hp₁ (r : ℝ) : x*x^r=x^(1+r) := by rw [Real.rpow_add hx,Real.rpow_one]
    have hp₂ (r : ℝ) : x^2*x^r=x^((2:ℝ)+r) := by rw [Real.rpow_add hx]; norm_num
    exact ⟨by convert hp₂ (3/4) using 1; norm_num,by convert hp₁ (3/4) using 1; norm_num,
      by convert hp₂ (-(1/4)) using 1; norm_num,by convert hp₁ (7/4) using 1; norm_num⟩
  have step (i : ℕ) : |squareLongReading (i+3)-squareLongReading (i+2)| ≤ C*((i:ℝ)+2)^(7/4:ℝ) := by
    let x := (i:ℝ)+2
    have hx : 1 ≤ x := by dsimp only [x]; linarith only [Nat.cast_nonneg (α := ℝ) i]
    have hx₀ := zero_lt_one.trans_le hx
    let f := fun y : ℝ => squareLongTrace (2*Real.log y)
    have he : squareLongReading (i+3)-squareLongReading (i+2)=
        (2*x+1)*f x+(x+1)^2*(f (x+1)-f x) := by
      unfold squareLongReading
      push_cast
      rw [show (i:ℝ)+3=x+1 by dsimp only [x]; ring]
      change (x+1)^2*f (x+1)-x^2*f x=_
      ring
    have h₁ := hg hx
    have h₂ := hi hx (show x ≤ x+1 by linarith) le_rfl
    have hcoef : (x+1)^2 ≤ 4*x^2 := by nlinarith only [mul_nonneg (show 0 ≤ x-1 by linarith only [hx]) (show 0 ≤ 3*x+1 by positivity)]
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*x+1),abs_of_nonneg (sq_nonneg (x+1))]
    change (2*x+1)*|f x|+(x+1)^2*|f (x+1)-f x| ≤ C*x^(7/4:ℝ)
    have hlow := mul_le_mul (show 2*x+1 ≤ 3*x by linarith only [hx]) h₁ (abs_nonneg _) (by positivity)
    have hhigh := mul_le_mul hcoef h₂ (abs_nonneg _) (by positivity)
    dsimp only [f,C]
    linarith only [hlow,hhigh,congrArg (fun u : ℝ => 3*A*u) (hpow x hx₀).2.1,
      congrArg (fun u : ℝ => 4*B*u) (hpow x hx₀).2.2.1]
  refine ⟨A+C,add_nonneg hA hC,fun M => ?_⟩
  let y := (M:ℝ)+2
  have hy : 1 ≤ y := by dsimp only [y]; linarith only [Nat.cast_nonneg (α := ℝ) M]
  have hy₀ := zero_lt_one.trans_le hy
  have hsum : (∑ i ∈ range M, |squareLongReading (i+3)-squareLongReading (i+2)|) ≤ M*(C*y^(7/4:ℝ)) := by
    calc _ ≤ ∑ _i ∈ range M, C*y^(7/4:ℝ) := by
              refine sum_le_sum fun i hi' => (step i).trans (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (by positivity) ?_ (by norm_num : (0:ℝ) ≤ 7/4)) hC)
              exact add_le_add (Nat.cast_le.mpr (mem_range.mp hi').le) le_rfl
         _ = _ := by simp
  have htop : |squareLongReading (M+2)| ≤ A*y^(11/4:ℝ) := by
    unfold squareLongReading
    push_cast
    change |y^2*squareLongTrace (2*Real.log y)| ≤ _
    rw [abs_mul,abs_of_nonneg (sq_nonneg _),← (hpow y hy₀).1]
    exact (mul_le_mul_of_nonneg_left (hg hy) (sq_nonneg _)).trans_eq (by ring)
  have hm : (M:ℝ) ≤ y := by dsimp only [y]; linarith
  linarith only [htop,hsum,mul_le_mul_of_nonneg_right hm (show 0 ≤ C*y^(7/4:ℝ) by positivity),
    congrArg (fun u : ℝ => C*u) (hpow y hy₀).2.2.2]

/-- On the integer roots the degree differs from its smooth long reading
by the limiting stationary and short lags. -/
theorem squareLongTrace_integer_degree_limit :
    Tendsto (fun n : ℕ => integerProbe _ (successorSquareTriple n)-squareLongTrace (2*Real.log n)) atTop
      (𝓝 (6*realSplineTrace 0-4*realSplineTrace (Real.log 4))) := by
  have hT := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop two_pos
  have hlim := upperSquareIndex_signed_degree.comp hT
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he : upperSquareIndex (2*Real.log n)=n := by
    rw [upperSquareIndex,show 2*Real.log n/2=Real.log n by ring,Real.exp_log (Nat.cast_pos.mpr hn),Nat.ceil_natCast]
  change integerProbe _ (successorSquareTriple (upperSquareIndex (2*Real.log n)))-squareLongTrace (2*Real.log n)=_
  rw [he]

/-- The difference between minus the smooth reading and the actual log
generator is bounded by one common quadratic allowance. -/
theorem diagonalOrdinaryLog_smooth_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    |diagonalOrdinaryLog n+squareLongReading n| ≤ C*(n:ℝ)^2 := by
  let Q := fun n : ℕ => integerProbe _ (successorSquareTriple n)
  have hs := squareLongTrace_integer_degree_limit
  obtain ⟨K,hK⟩ := hs.abs.bddAbove_range
  obtain ⟨A,hA,ha⟩ := successorSquare_contact_error
  obtain ⟨B,hB,hb⟩ := successorSquare_contact_degree
  refine ⟨A+B+|K|,by positivity,fun {n} hn => ?_⟩
  let P := ordinaryPrimeContact (successorSquareTriple n)
  let t := (n:ℝ)^2
  have ht := sq_nonneg (n:ℝ)
  have h₁ : |diagonalOrdinaryLog n-t*P| ≤ A*t := ha hn le_rfl
  have h₂ : |t*(P+Q n)| ≤ t*B := by
    rw [abs_mul,abs_of_nonneg ht]; exact mul_le_mul_of_nonneg_left (hb hn) ht
  have h₃ : |t*(Q n-squareLongTrace (2*Real.log n))| ≤ t*|K| := by
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left ((hK ⟨n,rfl⟩).trans (le_abs_self _)) ht
  have he : diagonalOrdinaryLog n+squareLongReading n =
      ((diagonalOrdinaryLog n-t*P)+t*(P+Q n))-t*(Q n-squareLongTrace (2*Real.log n)) := by
    dsimp only [t,squareLongReading]; ring
  rw [he]
  have hh := abs_sub_le ((diagonalOrdinaryLog n-t*P)+t*(P+Q n)) 0 (t*(Q n-squareLongTrace (2*Real.log n)))
  simp only [sub_zero,zero_sub,abs_neg] at hh
  linarith only [hh,abs_add_le (diagonalOrdinaryLog n-t*P) (t*(P+Q n)),h₁,h₂,h₃]

#print axioms squareLongReading_variation
#print axioms diagonalOrdinaryLog_smooth_error

end GaloisForLFunctions.CountingHolography.Sections
