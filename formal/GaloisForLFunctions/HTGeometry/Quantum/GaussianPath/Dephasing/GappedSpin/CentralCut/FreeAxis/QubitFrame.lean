import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Single-qubit frames parametrized by the two slopes of their spin axis -/
open Matrix Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
noncomputable section

/-- The same spatial rotation in the qubit and the real Pauli representations. -/
structure SpinFrame where
  U : Matrix Bool Bool ℂ
  R : Matrix (Fin 3) (Fin 3) ℝ
  unitary : star U * U = 1 ∧ U * star U = 1
  orthogonal : Rᵀ * R = 1
  conjugates : ∀ j, U * finiteQubitPauli j * star U =
    ∑ i, (R i j : ℂ) • finiteQubitPauli i

private def spinor (a b c : ℝ) : Matrix Bool Bool ℂ
  | false, false | true, true => a
  | false, true => ⟨-b,c⟩
  | true, false => ⟨b,c⟩

private def rotation (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ
  | 0,0 => a^2-b^2+c^2 | 0,1 => -2*b*c | 0,2 => 2*a*b
  | 1,0 => -2*b*c | 1,1 => a^2+b^2-c^2 | 1,2 => 2*a*c
  | 2,0 => -2*a*b | 2,1 => -2*a*c | 2,2 => a^2-b^2-c^2

private theorem spinor_unitary (a b c : ℝ) (h : a^2+b^2+c^2=1) :
    star (spinor a b c)*spinor a b c=1 ∧ spinor a b c*star (spinor a b c)=1 := by
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [spinor,Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      Complex.ext_iff,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] <;>
    constructor <;> first | (solve | ring) | linear_combination h

private theorem rotation_orthogonal (a b c : ℝ) (h : a^2+b^2+c^2=1) :
    (rotation a b c)ᵀ * rotation a b c=1 := by
  have hs : (a^2+b^2+c^2)^2=1 := by rw [h,one_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rotation,Matrix.mul_apply,Fin.sum_univ_three,Matrix.one_apply] <;>
    first | (solve | ring) | linear_combination hs

private theorem spinor_conjugates (a b c : ℝ) (j : Fin 3) :
    spinor a b c * finiteQubitPauli j * star (spinor a b c) =
      ∑ i, (rotation a b c i j : ℂ) • finiteQubitPauli i := by
  fin_cases j <;> ext x y <;> cases x <;> cases y <;>
    simp [spinor,rotation,finiteQubitPauli,Matrix.mul_apply,Fin.sum_univ_three,
      Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.smul_apply,
      Complex.ext_iff,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im] <;>
    first | (solve | ring) | (constructor <;> ring)

/-- For slopes in the unit square translated by (1,1), the third column
is parallel to (p,q,1) and every component is at least one third. -/
theorem slope_frame (p q : ℝ) (hp : p∈Set.Icc (1:ℝ) 2) (hq : q∈Set.Icc (1:ℝ) 2) :
    ∃ F : SpinFrame, 1/3 ≤ F.R 2 2 ∧ F.R 0 2 = p*F.R 2 2 ∧
      F.R 1 2=q*F.R 2 2 ∧ ∀ i : Fin 3, 1/3 ≤ F.R i 2 := by
  let d := sqrt (1+p^2+q^2)
  have hd : 0<d := sqrt_pos.mpr (by positivity)
  have hds : d^2=1+p^2+q^2 := sq_sqrt (by positivity)
  have hd₃ : d≤3 := (sq_le_sq₀ hd.le (by norm_num)).mp (by
    rw [hds]; linarith only [pow_le_pow_left₀ (zero_le_one.trans hp.1) hp.2 2,
      pow_le_pow_left₀ (zero_le_one.trans hq.1) hq.2 2])
  let z := 1/d
  let a := sqrt ((1+z)/2)
  let b := p*z/(2*a)
  let c := q*z/(2*a)
  have hz : 0<z := one_div_pos.mpr hd
  have ha : 0<a := sqrt_pos.mpr (by positivity)
  have ha₂ : a^2=(1+z)/2 := sq_sqrt (by positivity)
  have hdir : (p*z)^2+(q*z)^2+z^2=1 := by
    calc _ = (1+p^2+q^2)*z^2 := by ring
         _ = 1 := by rw [←hds,←mul_pow,show d*z=1 by dsimp only [z]; field_simp,one_pow]
  have hbc : b^2+c^2=(1-z)/2 := by
    calc _ = ((p*z)^2+(q*z)^2)/(2*a)^2 := by simp only [b,c,div_pow,add_div]
         _ = _ := by
           apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) ha.ne'))).mpr
           rw [mul_pow (2:ℝ) a,ha₂]
           linarith only [hdir]
  have hnorm : a^2+b^2+c^2=1 := by linarith only [ha₂,hbc]
  let F : SpinFrame := ⟨spinor a b c,rotation a b c,spinor_unitary a b c hnorm,
    rotation_orthogonal a b c hnorm,spinor_conjugates a b c⟩
  have hzz : F.R 2 2=z := by change a^2-b^2-c^2=z; linarith only [ha₂,hbc]
  have hx : F.R 0 2=p*z := by change 2*a*(p*z/(2*a))=p*z; field_simp
  have hy : F.R 1 2=q*z := by change 2*a*(q*z/(2*a))=q*z; field_simp
  have hl : 1/3≤z := (le_div_iff₀ hd).mpr (by linarith only [hd₃])
  refine ⟨F,hl.trans_eq hzz.symm,by rw [hx,hzz],by rw [hy,hzz],?_⟩
  intro i
  fin_cases i
  · exact (hl.trans (le_mul_of_one_le_left hz.le hp.1)).trans_eq hx.symm
  · exact (hl.trans (le_mul_of_one_le_left hz.le hq.1)).trans_eq hy.symm
  · exact hl.trans_eq hzz.symm

#print axioms slope_frame
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
