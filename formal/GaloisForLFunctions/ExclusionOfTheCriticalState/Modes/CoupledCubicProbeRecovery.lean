import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.PrimeProbeHankelInterpolation

/-!
# Recovering coupled cubic sources from finite probe data

The two nonlinearities in Kumar–Senapati–Vashisth, arXiv:2611.23133,
equation (3.36), have the forms x²(cx+dy) and y²(cx+dy). On an
exponential probe bank their linear and cubic coefficients can be
recovered together from four amplitude choices on any square bank of
distinct sample times. The reconstruction first polarizes the amplitude
response and then inverts the actual Hankel minor.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery
open Matrix

/-- A single output row, with independent coefficient vectors for each
of its two linear and two cubic terms. -/
structure Row (V : Type*) where
  linearX : V
  linearY : V
  cubicX : V
  cubicY : V

/-- Apply a common observation map to each coefficient. -/
def Row.map {V W : Type*} (f : V → W) (r : Row V) : Row W :=
  ⟨f r.linearX, f r.linearY, f r.cubicX, f r.cubicY⟩

/-- The first output is coupled through x², the second through y². -/
def response (second : Bool) (r : Row ℝ) (x y : ℝ) : ℝ :=
  x*r.linearX + y*r.linearY + (if second then y^2 else x^2)*(x*r.cubicX+y*r.cubicY)

/-- Four simultaneous readings, in the directions (1,±1) at scales one and two. -/
structure Readings (V : Type*) where
  plusOne : V
  minusOne : V
  plusTwo : V
  minusTwo : V

def measureRow (second : Bool) (r : Row ℝ) : Readings ℝ :=
  ⟨response second r 1 1, response second r 1 (-1),
   response second r 2 2, response second r 2 (-2)⟩

/-- Even and odd direction combinations, followed by separation of
the first and third powers of amplitude. -/
def recover (z : Readings ℝ) : Row ℝ :=
  ⟨(8*(z.plusOne+z.minusOne)-(z.plusTwo+z.minusTwo))/12,
   (8*(z.plusOne-z.minusOne)-(z.plusTwo-z.minusTwo))/12,
   (z.plusTwo+z.minusTwo-2*(z.plusOne+z.minusOne))/12,
   (z.plusTwo-z.minusTwo-2*(z.plusOne-z.minusOne))/12⟩

theorem recover_measure (second : Bool) (r : Row ℝ) : recover (measureRow second r) = r := by
  cases r
  cases second <;> unfold recover measureRow response <;> congr 1 <;> ring

theorem measure_recover (second : Bool) (z : Readings ℝ) : measureRow second (recover z) = z := by
  cases z
  cases second <;> unfold recover measureRow response <;> congr 1 <;> ring

/-- Three-direction mixed polarization of the cubic term, valid even in
the presence of the unknown linear coupling. -/
theorem third_response (second : Bool) (r : Row ℝ) (x y z : ℝ × ℝ) :
    let F := fun v : ℝ × ℝ => response second r v.1 v.2
    let u := fun v : ℝ × ℝ => if second then v.2 else v.1
    let c := fun v : ℝ × ℝ => v.1*r.cubicX + v.2*r.cubicY
    F (x+y+z) - F (x+y) - F (x+z) - F (y+z) + F x + F y + F z =
      2*(u x*u y*c z + u x*u z*c y + u y*u z*c x) := by
  cases second <;> simp only [response, Bool.false_eq_true, if_false, if_true,
    Prod.fst_add,Prod.snd_add] <;> ring

/-- An actual bank of Laplace probe readings with arbitrary distinct
sample times and distinct integer translates. -/
def bank {n : ℕ} (s : ℝ) (time shift : Fin n ↪ ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  probeHankelMinor (probe (Real.exp s)) time shift

private theorem bank_bijective {n : ℕ} (s : ℝ) (time shift : Fin n ↪ ℕ) :
    Function.Bijective (bank s time shift).mulVec := by
  have h := exponentialProbeHankel_isUnit (t := Real.exp s)
    (by linarith only [Real.exp_pos s]) time shift
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr h, Matrix.mulVec_surjective_iff_isUnit.mpr h⟩

/-- Joint response at every retained sample time. -/
def sample {n : ℕ} (s : ℝ) (time shift : Fin n ↪ ℕ) (second : Bool)
    (r : Row (Fin n → ℝ)) (i : Fin n) : Readings ℝ :=
  measureRow second (r.map fun v => (bank s time shift).mulVec v i)

/-- For every set of four readings at each time there is exactly one set
of spatial coefficient vectors, also for nonconsecutive prime times. -/
theorem sample_bijective {n : ℕ} (s : ℝ) (time shift : Fin n ↪ ℕ) (second : Bool) :
    Function.Bijective (sample s time shift second) := by
  let e := Equiv.ofBijective (bank s time shift).mulVec (bank_bijective s time shift)
  let inverse := fun z : Fin n → Readings ℝ =>
    Row.mk (e.symm fun i => (recover (z i)).linearX) (e.symm fun i => (recover (z i)).linearY)
      (e.symm fun i => (recover (z i)).cubicX) (e.symm fun i => (recover (z i)).cubicY)
  have he (v : Fin n → ℝ) : (bank s time shift).mulVec (e.symm v) = v := e.apply_symm_apply v
  have hrev (v : Fin n → ℝ) : e.symm ((bank s time shift).mulVec v) = v := e.symm_apply_apply v
  constructor
  · apply Function.LeftInverse.injective (g := inverse)
    intro r
    cases r
    simp only [inverse,sample,recover_measure,Row.map,hrev]
  · apply Function.RightInverse.surjective (g := inverse)
    intro z
    funext i
    simp only [inverse,sample,Row.map,he,measure_recover]

/-- Diagonal trials alone cannot tell which component carries the square. -/
theorem diagonal_model_ambiguity (r : Row ℝ) (x : ℝ) (sign : Bool) :
    response false r x (if sign then x else -x) =
      response true r x (if sign then x else -x) := by
  cases sign <;> simp [response]

/-- Off the diagonals, a model swap is detected unless the cubic
coefficient vanishes along the chosen input direction. -/
theorem model_distinction_iff (r : Row ℝ) (x y : ℝ) :
    response false r x y = response true r x y ↔
      x = y ∨ x = -y ∨ x*r.cubicX+y*r.cubicY = 0 := by
  have he : response false r x y - response true r x y =
      ((x-y)*(x+y))*(x*r.cubicX+y*r.cubicY) := by simp only [response,if_false,if_true]; ring
  rw [← sub_eq_zero,he]
  simp only [mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg,or_assoc]

#print axioms recover_measure
#print axioms measure_recover
#print axioms third_response
#print axioms sample_bijective
#print axioms diagonal_model_ambiguity
#print axioms model_distinction_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery
