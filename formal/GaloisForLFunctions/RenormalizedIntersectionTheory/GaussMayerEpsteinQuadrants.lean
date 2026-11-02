import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerQuadraticCone
import GaloisForLFunctions.LatticeSectionTheory.TheRectangularLatticeCount
import GaloisForLFunctions.RHTower.ThetaPrimePowerBernsteinGauge

/-! The actual completed rectangular Epstein function splits into two zeta
axes and four copies of the strictly positive quadratic cone. The lattice
series comes from its independent Poisson–Mellin construction. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinQuadrants

/-- Half the uncompleted Epstein field, retaining both axes; zero outside positive heights. -/
def epsteinField (w : ℂ) (a : ℝ) : ℂ :=
  if ha : 0 < a then
    (Real.pi : ℂ)^(w/2)/(2*Complex.Gamma (w/2))*epsteinLambda a ha (w/2)
  else 0

private def latticeTerm (w : ℂ) (a : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p=0 then 0 else (rectForm a p : ℂ)^(-w/2)

private theorem gamma_ne_zero {w : ℂ} (hw : 2 < w.re) : Complex.Gamma (w/2) ≠ 0 :=
  Complex.Gamma_ne_zero (fun n hn => by
    have hr := congrArg Complex.re hn
    simp at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n])

/-- The Poisson-defined Epstein field has the literal nonzero integer-lattice series. -/
private theorem lattice_hasSum {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    HasSum (latticeTerm w a) (2*epsteinField w a) := by
  have hs : 1 < (w/2).re := by norm_num [Complex.div_re]; linarith only [hw]
  have h := (hasSum_epsteinLambda ha hs).mul_left
    ((Real.pi : ℂ)^(w/2)/Complex.Gamma (w/2))
  have hg := gamma_ne_zero hw
  have hp : (Real.pi : ℂ)^(w/2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  refine (h.congr_fun fun p => ?_).trans_eq ?_
  · by_cases hz : p=0
    · simp [latticeTerm,hz]
    · have hq := rectForm_pos ha.ne' hz
      have hqn : (rectForm a p : ℂ)^(w/2) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hq.ne'))
      simp only [latticeTerm,if_neg hz,mul_one,Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hq.le,
        show -w/2= -(w/2) by ring,Complex.cpow_neg]
      field_simp [hg,hp,hqn]
  · rw [epsteinField,dif_pos ha]
    ring

private theorem even_int_sum {f : ℤ → ℂ} (hf : Summable f)
    (he : ∀ n, f (-n)=f n) :
    (∑' n : ℤ, f n)=f 0+2*∑' n : ℕ, f ((n : ℤ)+1) := by
  rw [_root_.RHTower.tsum_int_eq_zero_add_pairs hf]
  simp_rw [he,← two_mul]
  rw [tsum_mul_left]

private theorem lattice_even_first (w : ℂ) (a : ℝ) (m n : ℤ) :
    latticeTerm w a (-m,n)=latticeTerm w a (m,n) := by
  simp only [latticeTerm,show (0 : ℤ × ℤ)=(0,0) from rfl,Prod.mk.injEq,neg_eq_zero,rectForm,Int.cast_neg,neg_sq]

private theorem lattice_even_second (w : ℂ) (a : ℝ) (m n : ℤ) :
    latticeTerm w a (m,-n)=latticeTerm w a (m,n) := by
  simp only [latticeTerm,show (0 : ℤ × ℤ)=(0,0) from rfl,Prod.mk.injEq,neg_eq_zero,rectForm,Int.cast_neg,neg_sq]

private theorem lattice_decomposition {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    (∑' p : ℤ × ℤ, latticeTerm w a p)=
      2*(∑' n : ℕ, latticeTerm w a (0,(n : ℤ)+1))+
      2*(∑' m : ℕ, latticeTerm w a ((m : ℤ)+1,0))+
      4*(∑' p : ℕ × ℕ, latticeTerm w a ((p.1 : ℤ)+1,(p.2 : ℤ)+1)) := by
  have hf := (lattice_hasSum hw ha).summable
  have haxis : Summable (fun m : ℕ => latticeTerm w a ((m : ℤ)+1,0)) :=
    (hf.prod_symm.prod_factor 0).comp_injective (fun m n h => by exact_mod_cast add_right_cancel h)
  have hquad : Summable (fun p : ℕ × ℕ => latticeTerm w a ((p.1 : ℤ)+1,(p.2 : ℤ)+1)) := by
    apply hf.comp_injective
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    dsimp only at h1 h2
    exact Prod.ext (by omega) (by omega)
  have hrow (m : ℤ) := even_int_sum (hf.prod_factor m) (lattice_even_second w a m)
  have houter := even_int_sum hf.prod (fun m =>
    tsum_congr (fun n => lattice_even_first w a m n))
  have hsum : (∑' m : ℕ, ∑' n : ℤ, latticeTerm w a ((m : ℤ)+1,n))=
      (∑' m : ℕ, latticeTerm w a ((m : ℤ)+1,0))+
        2*(∑' p : ℕ × ℕ, latticeTerm w a ((p.1 : ℤ)+1,(p.2 : ℤ)+1)) := by
    calc
      _ = ∑' m : ℕ, (latticeTerm w a ((m : ℤ)+1,0)+
          2*∑' n : ℕ, latticeTerm w a ((m : ℤ)+1,(n : ℤ)+1)) :=
        tsum_congr fun m => hrow ((m : ℤ)+1)
      _ = _ := by
        rw [haxis.tsum_add (hquad.prod.mul_left 2),tsum_mul_left,← hquad.tsum_prod]
  have hzero : latticeTerm w a (0,0)=0 := by simp [latticeTerm]
  rw [hf.tsum_prod,houter,hrow 0,hzero,zero_add,hsum]
  ring

private theorem square_cpow (x : ℝ) (hx : 0 ≤ x) (w : ℂ) :
    ((x^2 : ℝ) : ℂ)^(-w/2)=(x : ℂ)^(-w) := by
  have h := Complex.cpow_mul_ofReal_nonneg hx (2 : ℝ) (-w/2)
  rw [show x^(2 : ℝ)=x^2 from Real.rpow_natCast x 2] at h
  have he : ((2 : ℝ) : ℂ)*(-w/2)= -w := by push_cast; ring
  simpa only [he] using h.symm

private theorem first_axis_term (w : ℂ) (a : ℝ) (n : ℕ) :
    latticeTerm w a ((n : ℤ)+1,0)=((n : ℂ)+1)^(-w) := by
  have hn : (n : ℤ)+1 ≠ 0 := by omega
  simp only [latticeTerm,show (0 : ℤ × ℤ)=(0,0) from rfl,Prod.mk.injEq,hn,false_and,if_false,rectForm,
    Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero]
  rw [square_cpow _ (by positivity)]
  push_cast
  rfl

private theorem second_axis_term {a : ℝ} (ha : 0 < a) (w : ℂ) (n : ℕ) :
    latticeTerm w a (0,(n : ℤ)+1)=(a : ℂ)^(-w)*((n : ℂ)+1)^(-w) := by
  have hn : (n : ℤ)+1 ≠ 0 := by omega
  simp only [latticeTerm,show (0 : ℤ × ℤ)=(0,0) from rfl,Prod.mk.injEq,hn,and_false,if_false,rectForm,
    Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add]
  rw [← mul_pow,square_cpow _ (by positivity),Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (by positivity)]
  push_cast
  rfl

private theorem quadrant_term (w : ℂ) (a : ℝ) (p : ℕ × ℕ) :
    latticeTerm w a ((p.1 : ℤ)+1,(p.2 : ℤ)+1)=
      (quadraticWeight a (p.2,p.1) : ℂ)^(-w/2) := by
  have hn : (p.1 : ℤ)+1 ≠ 0 := by omega
  simp only [latticeTerm,show (0 : ℤ × ℤ)=(0,0) from rfl,Prod.mk.injEq,hn,false_and,if_false]
  congr 2
  simp only [rectForm,quadraticWeight,Int.cast_add,Int.cast_natCast,Int.cast_one]
  ring

/-- Exact two-axis, four-quadrant decomposition of the independent Epstein field. -/
theorem epsteinField_eq {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    epsteinField w a=riemannZeta w*(1+(a : ℂ)^(-w))+2*quadraticCone w a := by
  have hz : (∑' n : ℕ, ((n : ℂ)+1)^(-w))=riemannZeta w := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith only [hw])]
    simp only [Complex.cpow_neg,one_div]
  have hq : (∑' p : ℕ × ℕ, (quadraticWeight a (p.2,p.1) : ℂ)^(-w/2))=
      quadraticCone w a := by
    exact (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => (quadraticWeight a p : ℂ)^(-w/2))
  have h := lattice_decomposition hw ha
  simp_rw [first_axis_term,second_axis_term ha,quadrant_term] at h
  rw [tsum_mul_left,hz,hq,(lattice_hasSum hw ha).tsum_eq] at h
  linear_combination h/2

#print axioms lattice_hasSum
#print axioms lattice_decomposition
#print axioms epsteinField_eq
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinQuadrants
