import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositiveMatrixCoding
import Mathlib.NumberTheory.Real.Irrational

/-!
# Arbitrarily narrow unimodular cones around irrational rays

Mediant subdivision preserves adjacent rational boundary columns. Their positive
denominators have growing sum, so the determinant-one identity bounds the bracket
width by `1/(n+1)`. Integer translation then surrounds every irrational real slope
by arbitrarily narrow positively oriented integral unimodular cones.
-/

set_option autoImplicit false
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding

/-- Adjacent rational boundary columns, ordered from the lower slope to the upper slope. -/
def Adjacent (A : NatMatrix) : Prop := A 0 0*A 1 1+1 = A 0 1*A 1 0

noncomputable def lowerSlope (A : NatMatrix) : ℝ := (A 0 0 : ℝ)/A 1 0

noncomputable def upperSlope (A : NatMatrix) : ℝ := (A 0 1 : ℝ)/A 1 1

noncomputable def mediantSlope (A : NatMatrix) : ℝ := ((A 0 0+A 0 1 : ℕ) : ℝ)/((A 1 0+A 1 1 : ℕ) : ℝ)

private theorem mul_generator_true (A : NatMatrix) :
    A*generator true = !![A 0 0,A 0 0+A 0 1;A 1 0,A 1 0+A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator,Matrix.mul_apply,Fin.sum_univ_two]

private theorem mul_generator_false (A : NatMatrix) :
    A*generator false = !![A 0 0+A 0 1,A 0 1;A 1 0+A 1 1,A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator,Matrix.mul_apply,Fin.sum_univ_two]

/-- Replace the boundary opposite the irrational slope by the mediant column. -/
noncomputable def mediantStep (x : ℝ) (A : NatMatrix) : NatMatrix :=
  if x < mediantSlope A then A*generator true else A*generator false

private theorem mediantStep_spec {x : ℝ} (hx : Irrational x) {A : NatMatrix}
    (hA : Adjacent A) (hc : 0 < A 1 0) (hd : 0 < A 1 1)
    (hlo : lowerSlope A < x) (hhi : x < upperSlope A) :
    Adjacent (mediantStep x A) ∧
    0 < mediantStep x A 1 0 ∧ 0 < mediantStep x A 1 1 ∧
    lowerSlope (mediantStep x A) < x ∧ x < upperSlope (mediantStep x A) ∧
    A 1 0+A 1 1+1 ≤ mediantStep x A 1 0+mediantStep x A 1 1 := by
  have hne : x ≠ mediantSlope A := by
    simpa only [mediantSlope,Int.cast_add,Int.cast_natCast,Nat.cast_add] using
      hx.ne_rational ((A 0 0+A 0 1 : ℕ) : ℤ) ((A 1 0+A 1 1 : ℕ) : ℤ)
  dsimp [Adjacent] at hA
  by_cases hm : x < mediantSlope A
  · rw [mediantStep,if_pos hm,mul_generator_true]
    change A 0 0*(A 1 0+A 1 1)+1 = (A 0 0+A 0 1)*A 1 0 ∧
      0 < A 1 0 ∧ 0 < A 1 0+A 1 1 ∧
      lowerSlope A < x ∧ x < mediantSlope A ∧
      A 1 0+A 1 1+1 ≤ A 1 0+(A 1 0+A 1 1)
    exact ⟨by nlinarith only [hA],hc,by omega,hlo,hm,by omega⟩
  · have hm' : mediantSlope A < x := lt_of_le_of_ne (le_of_not_gt hm) hne.symm
    rw [mediantStep,if_neg hm,mul_generator_false]
    change (A 0 0+A 0 1)*A 1 1+1 = A 0 1*(A 1 0+A 1 1) ∧
      0 < A 1 0+A 1 1 ∧ 0 < A 1 1 ∧
      mediantSlope A < x ∧ x < upperSlope A ∧
      A 1 0+A 1 1+1 ≤ (A 1 0+A 1 1)+A 1 1
    exact ⟨by nlinarith only [hA],by omega,hd,hm',hhi,by omega⟩

/-- Successive adjacent rational brackets of an irrational slope in the unit interval. -/
noncomputable def rationalBracket (x : ℝ) : ℕ → NatMatrix
  | 0 => !![0,1;1,1]
  | n+1 => mediantStep x (rationalBracket x n)

theorem rationalBracket_spec {x : ℝ} (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) :
    Adjacent (rationalBracket x n) ∧
    0 < rationalBracket x n 1 0 ∧ 0 < rationalBracket x n 1 1 ∧
    lowerSlope (rationalBracket x n) < x ∧ x < upperSlope (rationalBracket x n) ∧
    n+2 ≤ rationalBracket x n 1 0+rationalBracket x n 1 1 := by
  induction n with
  | zero =>
      norm_num [rationalBracket,Adjacent,lowerSlope,upperSlope]
      exact ⟨hx0,hx1⟩
  | succ n ih =>
      obtain ⟨ha,hc,hd,hlo,hhi,hs⟩ := ih
      obtain ⟨ha',hc',hd',hlo',hhi',hs'⟩ := mediantStep_spec hx ha hc hd hlo hhi
      have ht : n+1+2 ≤ mediantStep x (rationalBracket x n) 1 0+
          mediantStep x (rationalBracket x n) 1 1 := by omega
      exact ⟨ha',hc',hd',hlo',hhi',ht⟩

private theorem adjacent_width {A : NatMatrix} (hA : Adjacent A)
    (hc : 0 < A 1 0) (hd : 0 < A 1 1) :
    upperSlope A-lowerSlope A = 1/((A 1 0 : ℝ)*A 1 1) := by
  have hc' : (A 1 0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have hd' : (A 1 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have he : (A 0 0 : ℝ)*A 1 1+1 = (A 0 1 : ℝ)*A 1 0 := by exact_mod_cast hA
  dsimp [upperSlope,lowerSlope]
  field_simp [hc',hd']
  nlinarith only [he]

/-- The determinant identity and denominator growth give an explicit shrinking-cone bound. -/
theorem rationalBracket_width {x : ℝ} (hx : Irrational x) (hx0 : 0 < x) (hx1 : x < 1)
    (n : ℕ) :
    upperSlope (rationalBracket x n)-lowerSlope (rationalBracket x n) ≤ 1/(n+1 : ℝ) := by
  obtain ⟨ha,hc,hd,_,_,hs⟩ := rationalBracket_spec hx hx0 hx1 n
  rw [adjacent_width ha hc hd]
  have hm : n+1 ≤ rationalBracket x n 1 0*rationalBracket x n 1 1 := by
    have hc' : rationalBracket x n 1 0-1+1 = rationalBracket x n 1 0 :=
      Nat.sub_add_cancel (by omega)
    have hd' : rationalBracket x n 1 1-1+1 = rationalBracket x n 1 1 :=
      Nat.sub_add_cancel (by omega)
    have hp : rationalBracket x n 1 0+rationalBracket x n 1 1 ≤
        rationalBracket x n 1 0*rationalBracket x n 1 1+1 := by
      rw [← hc',← hd']
      nlinarith only [Nat.zero_le ((rationalBracket x n 1 0-1)*(rationalBracket x n 1 1-1))]
    omega
  have hm' : (n+1 : ℝ) ≤
      (rationalBracket x n 1 0 : ℝ)*rationalBracket x n 1 1 := by exact_mod_cast hm
  exact one_div_le_one_div_of_le (by positivity) hm'

#print axioms rationalBracket_spec
#print axioms rationalBracket_width


private theorem shifted_slope (a c : ℕ) (hc : 0 < c) (m : ℤ) :
    (((a : ℤ)+m*c : ℤ) : ℝ)/(c : ℝ) = (a : ℝ)/c+(m : ℝ) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  push_cast
  field_simp [hc']

/-- Every irrational real ray lies in arbitrarily narrow positively oriented unimodular rational cones. -/
theorem exists_unimodular_rational_cone (x : ℝ) (hx : Irrational x) (ε : ℝ) (hε : 0 < ε) :
    ∃ p q r s : ℤ, 0 < q ∧ 0 < s ∧ p*s-r*q = 1 ∧
      (r : ℝ)/s < x ∧ x < (p : ℝ)/q ∧ (p : ℝ)/q-(r : ℝ)/s < ε := by
  let m : ℤ := ⌊x⌋
  let y : ℝ := x-(m : ℝ)
  have hy : Irrational y := by
    rintro ⟨q,hq⟩
    apply hx
    refine ⟨q+(m : ℚ),?_⟩
    push_cast
    dsimp [y] at hq
    linarith only [hq]
  have hy0 : 0 < y := by
    have hfloor : (m : ℝ) ≤ x := Int.floor_le x
    have hnon : 0 ≤ y := sub_nonneg.mpr hfloor
    have hne : y ≠ 0 := fun h => not_irrational_zero (h ▸ hy)
    exact lt_of_le_of_ne hnon hne.symm
  have hy1 : y < 1 := by
    change x-(m : ℝ) < 1
    exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using Int.lt_floor_add_one x)
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
  have hn' : 1 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp hn
  have hsmall : 1/(n+1 : ℝ) < ε :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr (by nlinarith only [hn',hε])
  let A := rationalBracket y n
  obtain ⟨ha,hc,hd,hlo,hhi,_⟩ := rationalBracket_spec hy hy0 hy1 n
  have hwidth : upperSlope A-lowerSlope A < ε :=
    (rationalBracket_width hy hy0 hy1 n).trans_lt hsmall
  have hadj : (A 0 0 : ℤ)*A 1 1+1 = (A 0 1 : ℤ)*A 1 0 := by exact_mod_cast ha
  refine ⟨(A 0 1 : ℤ)+m*A 1 1,A 1 1,(A 0 0 : ℤ)+m*A 1 0,A 1 0,
    ?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hd
  · exact_mod_cast hc
  · nlinarith only [hadj]
  · simp only [Int.cast_natCast]
    rw [shifted_slope _ _ hc]
    change lowerSlope A+(m : ℝ) < x
    have hxy : y = x-(m : ℝ) := rfl
    linarith only [hlo,hxy]
  · simp only [Int.cast_natCast]
    rw [shifted_slope _ _ hd]
    change x < upperSlope A+(m : ℝ)
    have hxy : y = x-(m : ℝ) := rfl
    linarith only [hhi,hxy]
  · simp only [Int.cast_natCast]
    rw [shifted_slope _ _ hd,shifted_slope _ _ hc]
    change upperSlope A+(m : ℝ)-(lowerSlope A+(m : ℝ)) < ε
    linarith only [hwidth]

#print axioms exists_unimodular_rational_cone

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
