import GaloisForLFunctions.RHTower.EulerDeletionJointExponentialRemainder
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Word expansion of a chronological exponential product, and low-degree shuffle relations

A finite list of plane velocities `(x m, y m)` determines a piecewise-linear polygon.  Its
chronological exponential product `prod_m exp(z (x m X + y m Y))` is expanded here as a formal
power series whose degree-`k` coefficient is an explicit finite combination of the `2^k`
ordered words in two arbitrary noncommuting generators.  The scalar coefficient attached to a
word is the literal iterated-integral coefficient of the polygon, defined by appending one
straight segment at a time; no path-signature theorem is imported.

The integer-normalized jet used by `EulerDeletionJointExponentialRemainder` is identified with
the factorial multiple of that coefficient, so vanishing word coefficients force a vanishing
jet in **every** ring and for arbitrary generators.

The second half proves, for an arbitrary velocity list, every shuffle relation of total degree
at most four among these coefficients.  Each is an exact identity valid after every number of
segments, proved by induction on the number of segments from the single-segment expansion.
These are the classical grouplike relations of an iterated-integral signature, specialized to
the finitely many words needed downstream; they carry no arithmetic input and no RH content.
-/

open scoped BigOperators
namespace RHTower.SignatureWords
noncomputable section

abbrev Word := List Bool

/-- Every Boolean word of a fixed length, each listed once. -/
def words : ℕ → List Word
  | 0 => [[]]
  | n+1 => (words n).map (fun w => false :: w) ++ (words n).map (fun w => true :: w)

/-- Sum of a function over all words of a fixed length. -/
def wsum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Word → M) : M := ((words n).map f).sum

section Monoid
variable {M : Type*} [AddCommMonoid M]

theorem wsum_zero (f : Word → M) : wsum 0 f = f [] := by simp [wsum, words]

theorem wsum_succ (n : ℕ) (f : Word → M) :
    wsum (n+1) f = wsum n (fun w => f (false :: w)) + wsum n (fun w => f (true :: w)) := by
  simp [wsum, words, List.map_map, Function.comp_def]

theorem wsum_add (n : ℕ) (f g : Word → M) :
    wsum n (fun w => f w + g w) = wsum n f + wsum n g := by
  induction n generalizing f g with
  | zero => simp [wsum_zero]
  | succ n ih =>
    simp only [wsum_succ]
    rw [ih (fun w => f (false :: w)) (fun w => g (false :: w)),
      ih (fun w => f (true :: w)) (fun w => g (true :: w))]
    abel

theorem wsum_zero_fun (n : ℕ) : wsum n (fun _ => (0 : M)) = 0 := by
  induction n with
  | zero => simp [wsum_zero]
  | succ n ih => simp [wsum_succ, ih]

theorem wsum_congr (n : ℕ) {f g : Word → M} (h : ∀ w, w.length = n → f w = g w) :
    wsum n f = wsum n g := by
  induction n generalizing f g with
  | zero => simpa [wsum_zero] using h [] rfl
  | succ n ih =>
    simp only [wsum_succ]
    congr 1
    · exact ih (fun w hw => h _ (by simp [hw]))
    · exact ih (fun w hw => h _ (by simp [hw]))

/-- Splitting a word at a fixed position is a bijection onto pairs of shorter words. -/
theorem wsum_append (i j : ℕ) (f : Word → M) :
    wsum i (fun u => wsum j (fun v => f (u ++ v))) = wsum (i+j) f := by
  induction i generalizing f with
  | zero => simp [wsum_zero]
  | succ i ih =>
    have h1 := ih (fun w => f (false :: w))
    have h2 := ih (fun w => f (true :: w))
    simp only [wsum_succ, List.cons_append, h1, h2]
    rw [show i+1+j = (i+j)+1 by ring, wsum_succ]

end Monoid

section Eval
variable {A : Type*} [Ring A]

/-- Ordered product of the two generators selected by a word. -/
def evalWord (X Y : A) : Word → A
  | [] => 1
  | b :: w => (if b then Y else X) * evalWord X Y w

theorem evalWord_append (X Y : A) (u v : Word) :
    evalWord X Y (u ++ v) = evalWord X Y u * evalWord X Y v := by
  induction u with
  | nil => simp [evalWord]
  | cons b u ih => simp [evalWord, ih, mul_assoc]

theorem mul_wsum (a : A) (n : ℕ) (f : Word → A) :
    a * wsum n f = wsum n (fun w => a * f w) := by
  induction n generalizing f with
  | zero => simp [wsum_zero]
  | succ n ih => rw [wsum_succ, mul_add, ih, ih, wsum_succ]

end Eval

/-- The component of a plane velocity selected by one letter. -/
def letterVal (x y : ℝ) (b : Bool) : ℝ := if b then y else x

@[simp] theorem letterVal_false (a b : ℝ) : letterVal a b false = a := rfl

@[simp] theorem letterVal_true (a b : ℝ) : letterVal a b true = b := rfl

/-- The product of the velocity components selected by a word. -/
def letterProd (x y : ℝ) : Word → ℝ
  | [] => 1
  | b :: w => letterVal x y b * letterProd x y w

/-- Signature coefficient of one straight segment with the given velocity. -/
def segCoef (x y : ℝ) (w : Word) : ℝ := letterProd x y w / (w.length.factorial : ℝ)

section Expansion
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem velocity_pow (x y : ℝ) (X Y : A) (n : ℕ) :
    ((x:ℂ) • X + (y:ℂ) • Y)^n = wsum n (fun w => (letterProd x y w : ℂ) • evalWord X Y w) := by
  induction n with
  | zero => simp [wsum_zero, evalWord, letterProd]
  | succ n ih =>
    rw [pow_succ', ih, mul_wsum, wsum_succ]
    have hstep : ∀ w : Word,
        ((x:ℂ) • X + (y:ℂ) • Y) * ((letterProd x y w : ℂ) • evalWord X Y w) =
          (letterProd x y (false :: w) : ℂ) • evalWord X Y (false :: w) +
          (letterProd x y (true :: w) : ℂ) • evalWord X Y (true :: w) := by
      intro w
      simp only [evalWord, letterProd, letterVal, if_true, add_mul,
        mul_smul_comm, smul_mul_assoc, Complex.ofReal_mul, mul_smul, smul_add]
      rw [smul_comm ((letterProd x y w : ℂ)) ((x:ℂ)),
        smul_comm ((letterProd x y w : ℂ)) ((y:ℂ))]
      simp
    simp only [hstep]
    exact wsum_add n _ _

end Expansion

section Series
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem smul_wsum (c : ℂ) (n : ℕ) (f : Word → A) :
    c • wsum n f = wsum n (fun w => c • f w) := by
  induction n generalizing f with
  | zero => simp [wsum_zero]
  | succ n ih => rw [wsum_succ, smul_add, ih, ih, wsum_succ]

omit [Algebra ℂ A] in
theorem wsum_mul (a : A) (n : ℕ) (f : Word → A) :
    wsum n f * a = wsum n (fun w => f w * a) := by
  induction n generalizing f with
  | zero => simp [wsum_zero]
  | succ n ih => rw [wsum_succ, add_mul, ih, ih, wsum_succ]

omit [Algebra ℂ A] in
theorem wsum_finsetSum {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → Word → A) :
    ∑ i ∈ s, wsum n (f i) = wsum n (fun w => ∑ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wsum_zero_fun]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ih, ← wsum_add]
    exact wsum_congr n (fun w _ => by rw [Finset.sum_insert hi])

/-- Exponential series of one velocity. -/
def expSeries (v : A) : PowerSeries A := PowerSeries.mk (fun i => ((i.factorial : ℂ)⁻¹) • v ^ i)

theorem coeff_expSeries (v : A) (j : ℕ) :
    PowerSeries.coeff j (expSeries v) = ((j.factorial : ℂ)⁻¹) • v ^ j := by
  simp [expSeries]

theorem coeff_expSeries_velocity (x y : ℝ) (X Y : A) (j : ℕ) :
    PowerSeries.coeff j (expSeries ((x:ℂ) • X + (y:ℂ) • Y)) =
      wsum j (fun w => (segCoef x y w : ℂ) • evalWord X Y w) := by
  rw [coeff_expSeries, velocity_pow, smul_wsum]
  refine wsum_congr j (fun w hw => ?_)
  rw [smul_smul]
  congr 1
  rw [segCoef, hw]
  push_cast
  rw [inv_mul_eq_div]

/-- Chronological product of the exponentials of the first `n` plane velocities. -/
def pathSeries (x y : ℕ → ℝ) (X Y : A) (n : ℕ) : PowerSeries A :=
  ((List.range n).map (fun m => expSeries ((x m : ℂ) • X + (y m : ℂ) • Y))).prod

theorem pathSeries_zero (x y : ℕ → ℝ) (X Y : A) : pathSeries x y X Y 0 = 1 := by
  simp [pathSeries]

theorem pathSeries_succ (x y : ℕ → ℝ) (X Y : A) (n : ℕ) :
    pathSeries x y X Y (n+1) =
      pathSeries x y X Y n * expSeries ((x n : ℂ) • X + (y n : ℂ) • Y) := by
  simp [pathSeries, List.range_succ, List.map_append, List.prod_append]

/-- Signature coefficients of the polygon made by the first `n` plane velocities. -/
def pathCoef (x y : ℕ → ℝ) : ℕ → Word → ℝ
  | 0, w => if w = [] then 1 else 0
  | n+1, w => ∑ i ∈ Finset.range (w.length + 1),
      pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i)

theorem pathCoef_succ (x y : ℕ → ℝ) (n : ℕ) (w : Word) :
    pathCoef x y (n+1) w = ∑ i ∈ Finset.range (w.length + 1),
      pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i) := rfl

/-- The exact word expansion of a chronological exponential product. -/
theorem coeff_pathSeries (x y : ℕ → ℝ) (X Y : A) (n k : ℕ) :
    PowerSeries.coeff k (pathSeries x y X Y n) =
      wsum k (fun w => (pathCoef x y n w : ℂ) • evalWord X Y w) := by
  induction n generalizing k with
  | zero =>
    rw [pathSeries_zero]
    cases k with
    | zero => simp [wsum_zero, pathCoef, evalWord]
    | succ k =>
      rw [show ((1 : PowerSeries A)) = PowerSeries.C 1 by simp, PowerSeries.coeff_C]
      simp only [Nat.succ_ne_zero, if_false]
      rw [← wsum_zero_fun (M := A) (k+1)]
      refine wsum_congr _ (fun w hw => ?_)
      have hne : w ≠ [] := by
        intro h; rw [h] at hw; simp at hw
      simp [pathCoef, hne]
  | succ n ih =>
    rw [pathSeries_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm : ∀ i ∈ Finset.range (k+1),
        PowerSeries.coeff i (pathSeries x y X Y n) *
          PowerSeries.coeff (k-i) (expSeries ((x n : ℂ) • X + (y n : ℂ) • Y)) =
        wsum k (fun w => ((pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i) : ℝ) : ℂ)
          • evalWord X Y w) := by
      intro i hi
      have hik : i + (k - i) = k := by
        have := Finset.mem_range.mp hi; omega
      rw [ih, coeff_expSeries_velocity, wsum_mul]
      calc wsum i (fun u => (pathCoef x y n u : ℂ) • evalWord X Y u *
              wsum (k-i) (fun v => (segCoef (x n) (y n) v : ℂ) • evalWord X Y v))
          = wsum i (fun u => wsum (k-i) (fun v =>
              ((pathCoef x y n u * segCoef (x n) (y n) v : ℝ) : ℂ) •
                evalWord X Y (u ++ v))) := by
            refine wsum_congr _ (fun u _ => ?_)
            rw [mul_wsum]
            refine wsum_congr _ (fun v _ => ?_)
            rw [smul_mul_smul_comm, evalWord_append]
            push_cast
            rfl
        _ = wsum i (fun u => wsum (k-i) (fun v =>
              (fun w => ((pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i) : ℝ) : ℂ) •
                evalWord X Y w) (u ++ v))) := by
            refine wsum_congr _ (fun u hu => ?_)
            refine wsum_congr _ (fun v hv => ?_)
            simp only []
            rw [List.take_left' hu, List.drop_left' hu]
        _ = wsum (i + (k-i)) (fun w =>
              ((pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i) : ℝ) : ℂ) •
                evalWord X Y w) :=
            wsum_append i (k-i) (fun w =>
              ((pathCoef x y n (w.take i) * segCoef (x n) (y n) (w.drop i) : ℝ) : ℂ) •
                evalWord X Y w)
        _ = wsum k _ := by rw [hik]
    rw [Finset.sum_congr rfl hterm, wsum_finsetSum]
    refine wsum_congr _ (fun w hw => ?_)
    rw [pathCoef_succ, hw]
    push_cast
    rw [Finset.sum_smul]

open DeletionJointExponential in
/-- The integer-normalized chronological jet is the factorial multiple of the
formal exponential-product coefficient. -/
theorem jet_eq_coeff (vs : List A) (n : ℕ) :
    jet vs n = ((n.factorial : ℂ)) • PowerSeries.coeff n ((vs.map expSeries).prod) := by
  induction vs generalizing n with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [show ((1 : PowerSeries A)) = PowerSeries.C 1 by simp, PowerSeries.coeff_C]
    cases n with
    | zero => simp [jet]
    | succ n => simp [jet]
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.smul_sum]
    show (∑ i ∈ Finset.range (n+1), (n.choose i : A) * v^i * jet vs (n-i)) = _
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    dsimp only
    rw [coeff_expSeries, ih]
    have hnat : ∀ (m : ℕ) (W : A), (m : A) * W = (m : ℂ) • W := by
      intro m W
      rw [Algebra.smul_def, map_natCast]
    have hfac : (n.choose i : ℂ) * ((n-i).factorial : ℂ) =
        (n.factorial : ℂ) * ((i.factorial : ℂ))⁻¹ := by
      have h2 : ((i.factorial : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hc : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n-i).factorial : ℂ) =
          (n.factorial : ℂ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℂ))
          (Nat.choose_mul_factorial_mul_factorial hin)
      field_simp
      linear_combination hc
    calc (n.choose i : A) * v^i * (((n-i).factorial : ℂ) •
            PowerSeries.coeff (n-i) ((vs.map expSeries).prod))
        = ((n.choose i : ℂ)) • (v^i * (((n-i).factorial : ℂ) •
            PowerSeries.coeff (n-i) ((vs.map expSeries).prod))) := by
          rw [mul_assoc, hnat]
      _ = ((n.choose i : ℂ) * ((n-i).factorial : ℂ)) •
            (v^i * PowerSeries.coeff (n-i) ((vs.map expSeries).prod)) := by
          rw [mul_smul_comm, smul_smul]
      _ = ((n.factorial : ℂ) * ((i.factorial : ℂ))⁻¹) •
            (v^i * PowerSeries.coeff (n-i) ((vs.map expSeries).prod)) := by rw [hfac]
      _ = (n.factorial : ℂ) • ((((i.factorial : ℂ))⁻¹ • v^i) *
            PowerSeries.coeff (n-i) ((vs.map expSeries).prod)) := by
          rw [smul_mul_assoc, smul_smul]

end Series

section Unfolding
variable (x y : ℕ → ℝ)

theorem segCoef_nil (a b : ℝ) : segCoef a b [] = 1 := by
  simp [segCoef, letterProd]

theorem pathCoef_nil (n : ℕ) : pathCoef x y n [] = 1 := by
  induction n with
  | zero => simp [pathCoef]
  | succ n ih => simp [pathCoef_succ, ih, segCoef, letterProd]

theorem pathCoef_succ_one (n : ℕ) (a : Bool) :
    pathCoef x y (n+1) [a] =
      letterVal (x n) (y n) a + pathCoef x y n [a] := by
  rw [pathCoef_succ]
  norm_num [Finset.sum_range_succ, pathCoef_nil, segCoef, letterProd, Nat.factorial]

theorem pathCoef_succ_two (n : ℕ) (a b : Bool) :
    pathCoef x y (n+1) [a, b] =
      letterVal (x n) (y n) a * letterVal (x n) (y n) b / 2 +
      pathCoef x y n [a] * letterVal (x n) (y n) b + pathCoef x y n [a, b] := by
  rw [pathCoef_succ]
  norm_num [Finset.sum_range_succ, pathCoef_nil, segCoef, letterProd, Nat.factorial]

theorem pathCoef_succ_three (n : ℕ) (a b c : Bool) :
    pathCoef x y (n+1) [a, b, c] =
      letterVal (x n) (y n) a * letterVal (x n) (y n) b * letterVal (x n) (y n) c / 6 +
      pathCoef x y n [a] * (letterVal (x n) (y n) b * letterVal (x n) (y n) c) / 2 +
      pathCoef x y n [a, b] * letterVal (x n) (y n) c + pathCoef x y n [a, b, c] := by
  rw [pathCoef_succ]
  norm_num [Finset.sum_range_succ, pathCoef_nil, segCoef, letterProd, Nat.factorial]
  ring

theorem pathCoef_succ_four (n : ℕ) (a b c d : Bool) :
    pathCoef x y (n+1) [a, b, c, d] =
      letterVal (x n) (y n) a * letterVal (x n) (y n) b * letterVal (x n) (y n) c *
        letterVal (x n) (y n) d / 24 +
      pathCoef x y n [a] *
        (letterVal (x n) (y n) b * letterVal (x n) (y n) c * letterVal (x n) (y n) d) / 6 +
      pathCoef x y n [a, b] * (letterVal (x n) (y n) c * letterVal (x n) (y n) d) / 2 +
      pathCoef x y n [a, b, c] * letterVal (x n) (y n) d + pathCoef x y n [a, b, c, d] := by
  rw [pathCoef_succ]
  norm_num [Finset.sum_range_succ, pathCoef_nil, segCoef, letterProd, Nat.factorial]
  ring

theorem pathCoef_zero_of_ne_nil {w : Word} (hw : w ≠ []) : pathCoef x y 0 w = 0 := by
  simp [pathCoef, hw]

end Unfolding

section Shuffle
variable (x y : ℕ → ℝ)

/-- Displacement of the polygon after `n` segments, in the first coordinate. -/
def prefixSum (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ Finset.range n, x m

theorem prefixSum_zero (x : ℕ → ℝ) : prefixSum x 0 = 0 := rfl

theorem prefixSum_succ (x : ℕ → ℝ) (n : ℕ) :
    prefixSum x (n+1) = prefixSum x n + x n := Finset.sum_range_succ _ _

theorem coef_x (n : ℕ) : pathCoef x y n [false] = prefixSum x n := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih => rw [pathCoef_succ_one, ih, prefixSum_succ, letterVal_false]; ring

theorem coef_y (n : ℕ) : pathCoef x y n [true] = prefixSum y n := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih => rw [pathCoef_succ_one, ih, prefixSum_succ, letterVal_true]; ring

theorem coef_xx (n : ℕ) : pathCoef x y n [false, false] = (prefixSum x n)^(2 : ℕ)/2 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_two, ih, coef_x, prefixSum_succ, letterVal_false]; ring

theorem coef_yy (n : ℕ) : pathCoef x y n [true, true] = (prefixSum y n)^(2 : ℕ)/2 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_two, ih, coef_y, prefixSum_succ, letterVal_true]; ring

theorem coef_xxx (n : ℕ) : pathCoef x y n [false, false, false] = (prefixSum x n)^(3 : ℕ)/6 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_three, ih, coef_x, coef_xx, prefixSum_succ, letterVal_false]; ring

theorem coef_yyy (n : ℕ) : pathCoef x y n [true, true, true] = (prefixSum y n)^(3 : ℕ)/6 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_three, ih, coef_y, coef_yy, prefixSum_succ, letterVal_true]; ring

theorem coef_xxxx (n : ℕ) :
    pathCoef x y n [false, false, false, false] = (prefixSum x n)^(4 : ℕ)/24 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_four, ih, coef_x, coef_xx, coef_xxx, prefixSum_succ, letterVal_false]; ring

theorem coef_yyyy (n : ℕ) :
    pathCoef x y n [true, true, true, true] = (prefixSum y n)^(4 : ℕ)/24 := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    rw [pathCoef_succ_four, ih, coef_y, coef_yy, coef_yyy, prefixSum_succ, letterVal_true]; ring

theorem shuffle_x_y (n : ℕ) :
    pathCoef x y n [false, true] + pathCoef x y n [true, false] =
      prefixSum x n * prefixSum y n := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_two, coef_x, coef_y, prefixSum_succ,
      letterVal_false, letterVal_true]
    linear_combination ih

theorem shuffle_x_xy (n : ℕ) :
    2 * pathCoef x y n [false, false, true] + pathCoef x y n [false, true, false] =
      prefixSum x n * pathCoef x y n [false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, pathCoef_succ_two, coef_x, coef_y, coef_xx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih

theorem shuffle_x_yx (n : ℕ) :
    pathCoef x y n [false, true, false] + 2 * pathCoef x y n [true, false, false] =
      prefixSum x n * pathCoef x y n [true, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, pathCoef_succ_two, coef_x, coef_y, coef_xx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + x n * shuffle_x_y x y n

theorem shuffle_y_xx (n : ℕ) :
    pathCoef x y n [true, false, false] + pathCoef x y n [false, true, false] +
        pathCoef x y n [false, false, true] =
      prefixSum y n * ((prefixSum x n)^(2 : ℕ)/2) := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, coef_x, coef_y, coef_xx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + x n * shuffle_x_y x y n

theorem shuffle_y_yx (n : ℕ) :
    2 * pathCoef x y n [true, true, false] + pathCoef x y n [true, false, true] =
      prefixSum y n * pathCoef x y n [true, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, pathCoef_succ_two, coef_x, coef_y, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih

theorem shuffle_y_xy (n : ℕ) :
    pathCoef x y n [true, false, true] + 2 * pathCoef x y n [false, true, true] =
      prefixSum y n * pathCoef x y n [false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, pathCoef_succ_two, coef_x, coef_y, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_x_y x y n

theorem shuffle_x_yy (n : ℕ) :
    pathCoef x y n [false, true, true] + pathCoef x y n [true, false, true] +
        pathCoef x y n [true, true, false] =
      prefixSum x n * ((prefixSum y n)^(2 : ℕ)/2) := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_three, coef_x, coef_y, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_x_y x y n

theorem shuffle_x_xxy (n : ℕ) :
    3 * pathCoef x y n [false, false, false, true] +
        pathCoef x y n [false, false, true, false] =
      prefixSum x n * pathCoef x y n [false, false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_xxx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih

theorem shuffle_x_xyx (n : ℕ) :
    2 * pathCoef x y n [false, false, true, false] +
        2 * pathCoef x y n [false, true, false, false] =
      prefixSum x n * pathCoef x y n [false, true, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_xxx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + x n * shuffle_x_xy x y n

theorem shuffle_x_yxx (n : ℕ) :
    pathCoef x y n [false, true, false, false] +
        3 * pathCoef x y n [true, false, false, false] =
      prefixSum x n * pathCoef x y n [true, false, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_xxx,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + x n * shuffle_x_yx x y n + ((x n)^(2 : ℕ)/2) * shuffle_x_y x y n

theorem shuffle_y_yyx (n : ℕ) :
    3 * pathCoef x y n [true, true, true, false] +
        pathCoef x y n [true, true, false, true] =
      prefixSum y n * pathCoef x y n [true, true, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_yy, coef_yyy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih

theorem shuffle_y_yxy (n : ℕ) :
    2 * pathCoef x y n [true, true, false, true] +
        2 * pathCoef x y n [true, false, true, true] =
      prefixSum y n * pathCoef x y n [true, false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_yy, coef_yyy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_y_yx x y n

theorem shuffle_y_xyy (n : ℕ) :
    pathCoef x y n [true, false, true, true] +
        3 * pathCoef x y n [false, true, true, true] =
      prefixSum y n * pathCoef x y n [false, true, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_yy, coef_yyy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_y_xy x y n + ((y n)^(2 : ℕ)/2) * shuffle_x_y x y n

theorem shuffle_xy_xy (n : ℕ) :
    2 * pathCoef x y n [false, true, false, true] +
        4 * pathCoef x y n [false, false, true, true] =
      pathCoef x y n [false, true] * pathCoef x y n [false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, pathCoef_succ_two,
      coef_x, coef_y, coef_xx, coef_yy, prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + 2 * y n * shuffle_x_xy x y n

theorem shuffle_x_xyy (n : ℕ) :
    2 * pathCoef x y n [false, false, true, true] +
        pathCoef x y n [false, true, false, true] + pathCoef x y n [false, true, true, false] =
      prefixSum x n * pathCoef x y n [false, true, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_x_xy x y n

theorem shuffle_y_xxy (n : ℕ) :
    pathCoef x y n [true, false, false, true] +
        pathCoef x y n [false, true, false, true] +
        2 * pathCoef x y n [false, false, true, true] =
      prefixSum y n * pathCoef x y n [false, false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_y_xx x y n + (x n * y n / 2) * shuffle_x_y x y n

theorem shuffle_x_yxy (n : ℕ) :
    pathCoef x y n [false, true, false, true] +
        2 * pathCoef x y n [true, false, false, true] +
        pathCoef x y n [true, false, true, false] =
      prefixSum x n * pathCoef x y n [true, false, true] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + y n * shuffle_x_yx x y n + (x n * y n / 2) * shuffle_x_y x y n

theorem shuffle_x_yyx (n : ℕ) :
    pathCoef x y n [false, true, true, false] +
        pathCoef x y n [true, false, true, false] +
        2 * pathCoef x y n [true, true, false, false] =
      prefixSum x n * pathCoef x y n [true, true, false] := by
  induction n with
  | zero => simp [pathCoef, prefixSum]
  | succ n ih =>
    simp only [pathCoef_succ_four, pathCoef_succ_three, coef_x, coef_y, coef_xx, coef_yy,
      prefixSum_succ, letterVal_false, letterVal_true]
    linear_combination ih + x n * shuffle_x_yy x y n + (x n * y n / 2) * shuffle_x_y x y n

end Shuffle


section Vanishing
variable {A : Type*} [Ring A] [Algebra ℂ A]

open DeletionJointExponential in
/-- Vanishing word coefficients force the corresponding chronological jet to vanish
in every ring, for arbitrary noncommuting generators. -/
theorem jet_eq_zero_of_pathCoef (x y : ℕ → ℝ) (X Y : A) (n k : ℕ)
    (h : ∀ w : Word, w.length = k → pathCoef x y n w = 0) :
    jet ((List.range n).map (fun m => (x m : ℂ) • X + (y m : ℂ) • Y)) k = 0 := by
  have hmap : (((List.range n).map (fun m => ((x m : ℂ) • X + (y m : ℂ) • Y))).map expSeries)
      = (List.range n).map (fun m => expSeries ((x m : ℂ) • X + (y m : ℂ) • Y)) := by
    simp [List.map_map, Function.comp_def]
  rw [jet_eq_coeff, hmap]
  have hprod : ((List.range n).map (fun m => expSeries ((x m : ℂ) • X + (y m : ℂ) • Y))).prod
      = pathSeries x y X Y n := rfl
  rw [hprod, coeff_pathSeries]
  have hz : (wsum k fun w => ((pathCoef x y n w : ℝ) : ℂ) • evalWord X Y w)
      = wsum k (fun _ => (0:A)) :=
    wsum_congr k (fun w hw => by rw [h w hw]; simp)
  rw [hz, wsum_zero_fun, smul_zero]

end Vanishing

section CoefficientBound
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

/-- Absolute expansion of a chronological exponential product: the degree-`r` coefficient is
dominated by `M^r/r!`, with `M` the total velocity norm.  This is the finite multinomial
estimate, proved by induction on the factor list. -/
theorem norm_coeff_expProd_le (vs : List A) (r : ℕ) :
    ‖PowerSeries.coeff r ((vs.map expSeries).prod)‖ ≤ ((vs.map norm).sum)^r / r.factorial := by
  induction vs generalizing r with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    rw [show ((1 : PowerSeries A)) = PowerSeries.C 1 by simp, PowerSeries.coeff_C]
    cases r with
    | zero => simp
    | succ r => simp
  | cons v vs ih =>
    have hMnn : (0:ℝ) ≤ (vs.map norm).sum :=
      List.sum_nonneg (fun z hz => by
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
        exact norm_nonneg w)
    rw [List.map_cons, List.prod_cons, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (r+1),
        ‖PowerSeries.coeff i (expSeries v) *
            PowerSeries.coeff (r-i) ((vs.map expSeries).prod)‖
          ≤ (r.choose i : ℝ) * (‖v‖^i * ((vs.map norm).sum)^(r-i)) / r.factorial := by
      intro i hi
      have hin : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hc : (r.choose i : ℝ) * (i.factorial : ℝ) * ((r-i).factorial : ℝ)
          = (r.factorial : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m:ℝ)) (Nat.choose_mul_factorial_mul_factorial hin)
      have key : (1:ℝ) / ((i.factorial : ℝ) * ((r-i).factorial : ℝ))
          = (r.choose i : ℝ) / (r.factorial : ℝ) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linarith [hc]
      calc ‖PowerSeries.coeff i (expSeries v) *
              PowerSeries.coeff (r-i) ((vs.map expSeries).prod)‖
          ≤ ‖PowerSeries.coeff i (expSeries v)‖ *
              ‖PowerSeries.coeff (r-i) ((vs.map expSeries).prod)‖ := norm_mul_le _ _
        _ ≤ (‖v‖^i / i.factorial) * (((vs.map norm).sum)^(r-i) / (r-i).factorial) := by
            refine mul_le_mul ?_ (ih (r-i)) (norm_nonneg _) (by positivity)
            rw [coeff_expSeries, norm_smul]
            have hn : ‖((i.factorial : ℂ))⁻¹‖ = 1 / (i.factorial : ℝ) := by
              rw [norm_inv]
              simp
            rw [hn, one_div, ← div_eq_inv_mul]
            gcongr
            exact norm_pow_le v i
        _ = (‖v‖^i * ((vs.map norm).sum)^(r-i)) *
              ((1:ℝ) / ((i.factorial : ℝ) * ((r-i).factorial : ℝ))) := by ring
        _ = (‖v‖^i * ((vs.map norm).sum)^(r-i)) *
              ((r.choose i : ℝ) / (r.factorial : ℝ)) := by rw [key]
        _ = (r.choose i : ℝ) * (‖v‖^i * ((vs.map norm).sum)^(r-i)) / r.factorial := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_div, List.map_cons, List.sum_cons]
    gcongr
    rw [add_pow]
    apply le_of_eq
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring

end CoefficientBound


section RemainderBound
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]

open DeletionJointExponential

/-- Total velocity norm of a chronological factor list. -/
def velocityMass (vs : List A) : ℝ := (vs.map norm).sum

theorem velocityMass_nonneg (vs : List A) : 0 ≤ velocityMass vs :=
  List.sum_nonneg (fun z hz => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact norm_nonneg w)

theorem summable_norm_wordSeries (vs : List A) (z : ℂ) :
    Summable (fun n => ‖z^n • PowerSeries.coeff n ((vs.map expSeries).prod)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_pow_div_factorial (‖z‖ * velocityMass vs))
  rw [norm_smul, norm_pow]
  have hcoef := norm_coeff_expProd_le vs n
  calc ‖z‖^n * ‖PowerSeries.coeff n ((vs.map expSeries).prod)‖
      ≤ ‖z‖^n * ((velocityMass vs)^n / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = (‖z‖ * velocityMass vs)^n / (n.factorial : ℝ) := by
        rw [mul_pow]; ring

theorem coeff_zero_expProd (vs : List A) :
    PowerSeries.coeff 0 ((vs.map expSeries).prod) = 1 := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.prod_cons, PowerSeries.coeff_mul]
    simp [coeff_expSeries, ih]

/-- The chronological exponential product is the sum of its word-expansion series. -/
theorem tsum_exponentialWord (vs : List A) (z : ℂ) :
    exponentialWord vs z = ∑' n, z^n • PowerSeries.coeff n ((vs.map expSeries).prod) := by
  induction vs with
  | nil =>
    have h0 : exponentialWord ([] : List A) z = 1 := by simp [exponentialWord]
    rw [h0, tsum_eq_single 0]
    · simp
    · intro n hn
      simp only [List.map_nil, List.prod_nil]
      rw [show ((1 : PowerSeries A)) = PowerSeries.C 1 by simp, PowerSeries.coeff_C, if_neg hn,
        smul_zero]
  | cons v vs ih =>
    have hE : NormedSpace.exp (z • v) = ∑' i, z^i • PowerSeries.coeff i (expSeries v) := by
      rw [NormedSpace.exp_eq_tsum ℂ]
      refine tsum_congr (fun i => ?_)
      rw [coeff_expSeries, smul_pow, smul_comm]
    have hfE : Summable (fun i => ‖z^i • PowerSeries.coeff i (expSeries v)‖) := by
      simpa using summable_norm_wordSeries [v] z
    have hfP : Summable (fun j => ‖z^j • PowerSeries.coeff j ((vs.map expSeries).prod)‖) :=
      summable_norm_wordSeries vs z
    have hmul : exponentialWord (v :: vs) z
        = NormedSpace.exp (z • v) * exponentialWord vs z := by
      simp [exponentialWord]
    rw [hmul, ih, hE, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfE hfP]
    refine tsum_congr (fun n => ?_)
    rw [List.map_cons, List.prod_cons, PowerSeries.coeff_mul, Finset.smul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [smul_mul_smul_comm, ← pow_add]
    congr 2
    omega

private theorem real_exp_tsum (x : ℝ) : Real.exp x = ∑' n : ℕ, x^n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  refine tsum_congr (fun n => ?_)
  rw [smul_eq_mul]
  ring

private theorem factorial_shift_le (n : ℕ) :
    (120 : ℝ) * (n.factorial : ℝ) ≤ (((n+5).factorial : ℕ) : ℝ) := by
  have hd : (Nat.factorial 5) * n.factorial ∣ (5 + n).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add 5 n
  have hle : (Nat.factorial 5) * n.factorial ≤ (5 + n).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) hd
  have hcomm : (5 + n) = (n + 5) := by omega
  rw [hcomm] at hle
  have hcast : ((Nat.factorial 5 * n.factorial : ℕ) : ℝ) ≤ (((n+5).factorial : ℕ) : ℝ) := by
    exact_mod_cast hle
  have h5 : Nat.factorial 5 = 120 := by norm_num [Nat.factorial]
  rw [h5] at hcast
  push_cast at hcast
  linarith

/-- The explicit fifth-order remainder bound for a chronological exponential product whose
jets vanish through order four: `‖B(z)-1‖ ≤ (M‖z‖)^(5 : ℕ) exp(M‖z‖)/5!`. -/
theorem norm_exponentialWord_sub_one_le (vs : List A)
    (h : ∀ n, 1 ≤ n → n ≤ 4 → PowerSeries.coeff n ((vs.map expSeries).prod) = 0) (z : ℂ) :
    ‖exponentialWord vs z - 1‖ ≤
      (velocityMass vs * ‖z‖)^(5 : ℕ) * Real.exp (velocityMass vs * ‖z‖) / 120 := by
  have hM : 0 ≤ velocityMass vs := velocityMass_nonneg vs
  have hnorm := summable_norm_wordSeries vs z
  have hsum : Summable (fun n => z^n • PowerSeries.coeff n ((vs.map expSeries).prod)) :=
    hnorm.of_norm
  have hsplit := hsum.sum_add_tsum_nat_add 5
  have hhead : (∑ i ∈ Finset.range 5,
      z^i • PowerSeries.coeff i ((vs.map expSeries).prod)) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, coeff_zero_expProd,
      h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) (by norm_num), h 4 (by norm_num) (by norm_num)]
    simp
  rw [hhead] at hsplit
  have he : exponentialWord vs z
      = 1 + ∑' n, z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod) := by
    rw [tsum_exponentialWord vs z]
    exact hsplit.symm
  have hval : exponentialWord vs z - 1
      = ∑' n, z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod) := by
    rw [he]
    abel
  have hshift : Summable (fun n =>
      ‖z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod)‖) :=
    (summable_nat_add_iff 5).mpr hnorm
  have hbound : ∀ n : ℕ,
      ‖z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod)‖
        ≤ ((velocityMass vs * ‖z‖)^(5 : ℕ) / 120) *
          ((velocityMass vs * ‖z‖)^n / (n.factorial : ℝ)) := by
    intro n
    rw [norm_smul, norm_pow]
    have hc := norm_coeff_expProd_le vs (n+5)
    have h1 : ‖z‖^(n+5) * ‖PowerSeries.coeff (n+5) ((vs.map expSeries).prod)‖
        ≤ ‖z‖^(n+5) * ((velocityMass vs)^(n+5) / (((n+5).factorial : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    refine h1.trans ?_
    have hf := factorial_shift_le n
    have hx : (0:ℝ) ≤ velocityMass vs * ‖z‖ := by positivity
    have hkey : ‖z‖^(n+5) * ((velocityMass vs)^(n+5) / (((n+5).factorial : ℕ) : ℝ))
        = (velocityMass vs * ‖z‖)^(n+5) / (((n+5).factorial : ℕ) : ℝ) := by
      rw [mul_pow]
      ring
    have hrhs : ((velocityMass vs * ‖z‖)^(5 : ℕ) / 120) *
          ((velocityMass vs * ‖z‖)^n / (n.factorial : ℝ))
        = (velocityMass vs * ‖z‖)^(n+5) / (120 * (n.factorial : ℝ)) := by
      rw [pow_add]
      ring
    rw [hkey, hrhs]
    gcongr
  calc ‖exponentialWord vs z - 1‖
      = ‖∑' n, z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod)‖ := by rw [hval]
    _ ≤ ∑' n, ‖z^(n+5) • PowerSeries.coeff (n+5) ((vs.map expSeries).prod)‖ :=
        norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' n, ((velocityMass vs * ‖z‖)^(5 : ℕ) / 120) *
          ((velocityMass vs * ‖z‖)^n / (n.factorial : ℝ)) :=
        Summable.tsum_le_tsum hbound hshift
          ((Real.summable_pow_div_factorial (velocityMass vs * ‖z‖)).mul_left _)
    _ = ((velocityMass vs * ‖z‖)^(5 : ℕ) / 120) * Real.exp (velocityMass vs * ‖z‖) := by
        rw [tsum_mul_left, ← real_exp_tsum]
    _ = (velocityMass vs * ‖z‖)^(5 : ℕ) * Real.exp (velocityMass vs * ‖z‖) / 120 := by ring

end RemainderBound

end
end RHTower.SignatureWords
