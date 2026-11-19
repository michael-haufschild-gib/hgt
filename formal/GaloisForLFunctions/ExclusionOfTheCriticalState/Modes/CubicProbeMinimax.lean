import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.CubicProbeExperimentDesign

/-!
# Sharp error constants for four cubic source trials

For a known squared component, four inputs in the unit square achieve the
coordinatewise error constants 3, 1, 4 and 2 under bounded additive noise.
Even observing the whole square cannot improve a constant. The extremizers
are the longitudinal Chebyshev cubic and the transverse quadratic times y.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design.Minimax

/-- Longitudinal and transverse linear coefficients, then cubic coefficients. -/
def coord (r : Row ℝ) : Fin 4 → ℝ := ![r.linearX,r.linearY,r.cubicX,r.cubicY]

def shots : Fin 4 → ℝ × ℝ := ![(1,1),(1,-1),(1/2,0),(0,1)]

def sample (r : Row ℝ) (i : Fin 4) := signal false r (shots i)

def decode (z : Fin 4 → ℝ) : Row ℝ :=
  let L := (z 0+z 1)/2
  ⟨(8*z 2-L)/3,z 3,(4*L-8*z 2)/3,(z 0-z 1)/2-z 3⟩

def gain : Fin 4 → ℝ := ![3,1,4,2]

theorem decode_exact (r : Row ℝ) : decode (sample r)=r := by
  cases r
  simp only [decode,sample,shots,signal,response,Bool.false_eq_true,if_false,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  congr 1 <;> ring

private theorem perturbed (r : Row ℝ) (e : Fin 4 → ℝ) (i : Fin 4) :
    coord (decode (sample r+e)) i-coord r i=coord (decode e) i := by
  calc
    _ = coord (decode (sample r+e)) i-coord (decode (sample r)) i := by rw [decode_exact]
    _ = _ := by
      generalize sample r=z
      fin_cases i <;> simp [coord,decode] <;> ring

private theorem noise_bound (e : Fin 4 → ℝ) (ε : ℝ) (he : ∀ i, |e i|≤ε) (i : Fin 4) :
    |coord (decode e) i|≤gain i*ε := by
  have h0 := abs_le.mp (he 0)
  have h1 := abs_le.mp (he 1)
  have h2 := abs_le.mp (he 2)
  have h3 := abs_le.mp (he 3)
  apply abs_le.mpr
  fin_cases i <;> constructor <;> simp [coord,decode,gain] <;>
    linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

/-- Sharp coordinatewise propagation of four independently bounded trial errors. -/
theorem four_shot_error (r : Row ℝ) (e : Fin 4 → ℝ) (ε : ℝ) :
    (∀ i, |e i|≤ε) → ∀ i, |coord (decode (sample r+e)) i-coord r i|≤gain i*ε := by
  intro he i
  rw [perturbed]
  exact noise_bound e ε he i

/-- All measurements on the full square are compatible with a zero record
at unit error. -/
def invisible (r : Row ℝ) := ∀ x y : ℝ, |x|≤1 → |y|≤1 → |response false r x y|≤1

private theorem sample_invisible {r : Row ℝ} (h : invisible r) (j : Fin 4) : |sample r j|≤1 := by
  apply h <;> fin_cases j <;> norm_num [shots]

private theorem cubic (x : ℝ) (h : |x|≤1) : |4*x^3-3*x|≤1 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have h1 := mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg (2*x+1))
  have h2 := mul_nonneg (show 0≤1+x by linarith only [hl]) (sq_nonneg (2*x-1))
  exact abs_le.mpr ⟨by linarith only [h2],by linarith only [h1]⟩

private theorem transverse (x y : ℝ) (hx : |x|≤1) (hy : |y|≤1) : |y*(2*x^2-1)|≤1 := by
  have hx' := abs_le.mp hx
  have hs := mul_nonneg (sub_nonneg.mpr hx'.2) (show 0≤1+x by linarith only [hx'.1])
  have ha : |2*x^2-1|≤1 := abs_le.mpr ⟨by linarith only [sq_nonneg x],by linarith only [hs]⟩
  rw [abs_mul]
  exact (mul_le_mul hy ha (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

private def extremal : Fin 4 → Row ℝ :=
  ![⟨3,0,-4,0⟩,⟨0,1,0,-2⟩,⟨-3,0,4,0⟩,⟨0,-1,0,2⟩]

private theorem extrema (j : Fin 4) : invisible (extremal j) ∧ coord (extremal j) j=gain j := by
  constructor
  · intro x y hx hy
    have hp := cubic x hx
    have hq := transverse x y hx hy
    have hw : response false (extremal j) x y =
        ![-(4*x^3-3*x),-(y*(2*x^2-1)),4*x^3-3*x,y*(2*x^2-1)] j := by
      fin_cases j <;> simp [extremal,response] <;> ring
    rw [hw]
    fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,abs_neg] <;> assumption
  · fin_cases j <;> rfl

/-- Each gain is attained by a signal bounded on the entire unit square.
It is already forced by the four noisy measurements. -/
theorem exact_coordinate_gain (j : Fin 4) :
    IsGreatest {v : ℝ | ∃ r : Row ℝ, invisible r ∧ |coord r j|=v} (gain j) := by
  have hg : 0≤gain j := by fin_cases j <;> norm_num [gain]
  refine ⟨⟨extremal j,(extrema j).1,by rw [(extrema j).2,abs_of_nonneg hg]⟩,?_⟩
  rintro v ⟨r,hr,rfl⟩
  simpa only [decode_exact,mul_one] using noise_bound (sample r) 1 (sample_invisible hr) j

/-- An arbitrary estimate at the zero record incurs the stated error for
some compatible true signal, even if it can use every input in the square. -/
theorem unavoidable_error (j : Fin 4) (estimate : ℝ) :
    ∃ r : Row ℝ, invisible r ∧ gain j≤|estimate-coord r j| := by
  obtain ⟨hr,he⟩ := extrema j
  by_cases h : estimate≤0
  · refine ⟨extremal j,hr,?_⟩
    rw [he]
    linarith only [neg_abs_le (estimate-gain j),h]
  let r := (extremal j).map Neg.neg
  have hh (x y : ℝ) : response false r x y = -response false (extremal j) x y := by
    simp only [r,Row.map,response,Bool.false_eq_true,if_false]
    ring
  have hc : coord r j = -gain j := by
    rw [← he]
    fin_cases j <;> rfl
  refine ⟨r,fun x y hx hy => by rw [hh,abs_neg]; exact hr x y hx hy,?_⟩
  rw [hc]
  linarith only [le_abs_self (estimate- -gain j),lt_of_not_ge h]

#print axioms decode_exact
#print axioms four_shot_error
#print axioms exact_coordinate_gain
#print axioms unavoidable_error
end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery.Design.Minimax
