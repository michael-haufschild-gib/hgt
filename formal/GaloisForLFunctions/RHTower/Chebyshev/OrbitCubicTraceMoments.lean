import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceGeometry

/-!
# The positive trace law of the anharmonic cubic

Division by the derivative at three simple roots extracts the leading
coefficient of the quadratic interpolation polynomial. Multiplication
by X(X−1) makes these three residues positive. Reduction modulo the
orbit cubic then gives all centered moments without solving the cubic.
-/

noncomputable section
namespace RHTower.OrbitCubic

/-- Derivative denominator at the first of three simple roots. -/
def weight (a b c : ℝ) : ℝ := a*(a-1)/((a-b)*(a-c))

/-- A centered moment of the three codifferent residues. -/
def moment (a b c m : ℝ) (k : ℕ) : ℝ :=
  weight a b c * (a-m)^k + weight b c a * (b-m)^k + weight c a b * (c-m)^k

private def traceDual (a b c : ℝ) (f : ℝ → ℝ) : ℝ :=
  f a / ((a-b)*(a-c)) + f b / ((b-c)*(b-a)) + f c / ((c-a)*(c-b))

private theorem quadratic_trace {a b c : ℝ} (hab : a < b) (hbc : b < c) (A B C : ℝ) :
    traceDual a b c (fun x => A*x^2+B*x+C) = A := by
  unfold traceDual
  field_simp [sub_ne_zero.mpr hab.ne, sub_ne_zero.mpr hbc.ne, sub_ne_zero.mpr (hab.trans hbc).ne,
    sub_ne_zero.mpr hab.ne', sub_ne_zero.mpr hbc.ne', sub_ne_zero.mpr (hab.trans hbc).ne']
  ring

/-- Three coefficients, ordered by descending degree, for the remainder
of X(X−1)(X−m)^k modulo the orbit cubic at m = q+1/2. -/
def remainder (m : ℝ) : ℕ → ℝ × ℝ × ℝ
  | 0 => (1,-1,0)
  | k+1 =>
    let (A,B,C) := remainder m k
    (A+B, C-(m-2)*A-m*B, -A-m*C)

private def value (v : ℝ × ℝ × ℝ) (x : ℝ) : ℝ := v.1*x^2+v.2.1*x+v.2.2

private theorem reduce_at_root {q x : ℝ} (h : binary q x 1 = 0) (k : ℕ) :
    value (remainder (q+1/2) k) x = x*(x-1)*(x-(q+1/2))^k := by
  have hc := (arrowhead_secular q x).symm.trans h
  induction k with
  | zero => simp [value,remainder]; ring
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ← ih]
    simp only [remainder]
    generalize remainder (q+1/2) k = v
    rcases v with ⟨A,B,C⟩
    unfold value
    linear_combination (norm := ring) -A * hc

private theorem moment_leading {q a b c : ℝ} (hab : a < b) (hbc : b < c)
    (ha : binary q a 1 = 0) (hb : binary q b 1 = 0) (hc : binary q c 1 = 0) (k : ℕ) :
    moment a b c (q+1/2) k = (remainder (q+1/2) k).1 := by
  let v := remainder (q+1/2) k
  calc
    _ = traceDual a b c (value v) := by
      unfold moment weight traceDual v
      rw [reduce_at_root ha, reduce_at_root hb, reduce_at_root hc]
      ring
    _ = _ := quadratic_trace hab hbc v.1 v.2.1 v.2.2

/-- Value of an affine numerator divided by the derivative at a simple root. -/
def affineResidue (a b c A B : ℝ) : ℝ := (A*a+B) / ((a-b)*(a-c))

/-- An affine numerator cannot yield three strictly positive residues.
Their sum vanishes because a linear polynomial has zero quadratic coefficient. -/
theorem affine_trace_obstruction (x h k A B : ℝ) :
    let y := x+Real.exp h
    let z := y+Real.exp k
    ¬ (0 < affineResidue x y z A B ∧ 0 < affineResidue y z x A B ∧
        0 < affineResidue z x y A B) := by
  intro y z
  rintro ⟨h₁,h₂,h₃⟩
  have hs := quadratic_trace (lt_add_of_pos_right x (Real.exp_pos h))
    (lt_add_of_pos_right y (Real.exp_pos k)) 0 A B
  change traceDual x y z (fun t => 0*t^2+A*t+B) = 0 at hs
  simp only [traceDual, zero_mul, zero_add] at hs
  unfold affineResidue at h₁ h₂ h₃
  linarith only [h₁,h₂,h₃,hs]

/-- Every member has a positive, normalized three-root law whose complete
moment sequence is given by quadratic remainders. -/
theorem exists_positive_trace_law (q : ℝ) :
    ∃ a b c : ℝ, a < 0 ∧ 0 < b ∧ b < 1 ∧ 1 < c ∧
      binary q a 1 = 0 ∧ binary q b 1 = 0 ∧ binary q c 1 = 0 ∧
      0 < weight a b c ∧ 0 < weight b c a ∧ 0 < weight c a b ∧
      ∀ k, moment a b c (q+1/2) k = (remainder (q+1/2) k).1 := by
  obtain ⟨a,b,c,ha,hb,hb',hc,ea,eb,ec⟩ := roots_straddle_poles q
  have hab := ha.trans hb
  have hbc := hb'.trans hc
  have hac := hab.trans hbc
  refine ⟨a,b,c,ha,hb,hb',hc,ea,eb,ec,?_,?_,?_,moment_leading hab hbc ea eb ec⟩
  · exact div_pos (mul_pos_of_neg_of_neg ha (by linarith only [ha]))
      (mul_pos_of_neg_of_neg (sub_neg.mpr hab) (sub_neg.mpr hac))
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hb (sub_neg.mpr hb'))
      (mul_neg_of_neg_of_pos (sub_neg.mpr hbc) (sub_pos.mpr hab))
  · exact div_pos (mul_pos (by linarith only [hc]) (sub_pos.mpr hc))
      (mul_pos (sub_pos.mpr hac) (sub_pos.mpr hbc))

/-- The variance is fixed at two while the third centered moment retains
the full parameter. The fourth moment gives unit order-three Hankel determinant. -/
theorem centered_trace_invariants (q : ℝ) :
    ∃ a b c : ℝ, binary q a 1 = 0 ∧ binary q b 1 = 0 ∧ binary q c 1 = 0 ∧
      0 < weight a b c ∧ 0 < weight b c a ∧ 0 < weight c a b ∧
      let M := moment a b c (q+1/2)
      M 0 = 1 ∧ M 1 = 0 ∧ M 2 = 2 ∧ M 3 = -2*q ∧ M 4 = 2*q^2+9/2 ∧
        M 2 * M 4 - M 3 ^ 2 - M 2 ^ 3 = 1 := by
  obtain ⟨a,b,c,_,_,_,_,ea,eb,ec,pa,pb,pc,hm⟩ := exists_positive_trace_law q
  refine ⟨a,b,c,ea,eb,ec,pa,pb,pc,?_⟩
  dsimp only
  simp only [hm, remainder]
  exact ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

#print axioms affine_trace_obstruction
#print axioms exists_positive_trace_law
#print axioms centered_trace_invariants
end RHTower.OrbitCubic
