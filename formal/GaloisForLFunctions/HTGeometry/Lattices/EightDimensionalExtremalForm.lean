import GaloisForLFunctions.HTGeometry.Lattices.EightDimensionalEvenShell
import GaloisForLFunctions.HTGeometry.Lattices.IntegralRootParityFibers
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An extremal integral quadratic form in eight variables

Six successive difference coordinates and one terminal parity coordinate
parametrize the doubled E₈ lattice over the integers. Its squared
Euclidean norm is eight times an integral quadratic form. The resulting
norm-one shell has 240 roots, attaining the cubic line bound in rank eight.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.EightShell
open Finset IntegralZeroSum IntegralRootShell

private theorem sum_eight (f : Fin 8 → ℤ) :
    ∑ i, f i = f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7 := by
  simp [Fin.sum_univ_succ,add_assoc]

/-- Successive differences encode the six middle coordinates. -/
def encode (a : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![a 0, a 0+2*a 1, a 0+2*(a 2-a 1), a 0+2*(a 3-a 2),
    a 0+2*(a 4-a 3), a 0+2*(a 5-a 4), a 0+2*(a 6-a 5), a 0+2*(2*a 7-a 6)]

private theorem encode_sum (a : Fin 8 → ℤ) : (∑ i, encode a i)=8*a 0+4*a 7 := by
  rw [sum_eight]
  change a 0+(a 0+2*a 1)+(a 0+2*(a 2-a 1))+(a 0+2*(a 3-a 2))+
    (a 0+2*(a 4-a 3))+(a 0+2*(a 5-a 4))+(a 0+2*(a 6-a 5))+
    (a 0+2*(2*a 7-a 6))=_
  ring

private theorem encode_compatible (a : Fin 8 → ℤ) : compatible (encode a) := by
  refine ⟨fun i => ?_,by rw [encode_sum]; omega⟩
  fin_cases i <;> simp [encode,Int.add_emod]

private def half (x : Fin 8 → ℤ) (i : Fin 8) := (x i-x 0)/2

/-- Partial sums integrate the successive differences. The terminal
coordinate records the total divided by four, after subtracting the base. -/
def decode (x : Fin 8 → ℤ) : Fin 8 → ℤ :=
  let b := half x
  let u₂ := b 1+b 2
  let u₃ := u₂+b 3
  let u₄ := u₃+b 4
  let u₅ := u₄+b 5
  ![x 0,b 1,u₂,u₃,u₄,u₅,u₅+b 6,((∑ i, x i)-8*x 0)/4]

theorem decode_encode (a : Fin 8 → ℤ) : decode (encode a)=a := by
  have h (b c : ℤ) : (b+2*c-b)/2=c := by omega
  funext i
  fin_cases i <;> simp [decode,half,encode_sum,encode,h] <;> omega

theorem encode_decode (x : Fin 8 → ℤ) (hx : compatible x) : encode (decode x)=x := by
  have h (i : Fin 8) : 2*half x i=x i-x 0 := by
    have e := hx.1 i
    unfold half
    omega
  have hs := hx.2
  rw [sum_eight] at hs
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  have h₅ := h 5
  have h₆ := h 6
  funext i
  fin_cases i <;> simp [encode,decode,sum_eight] <;> omega

private def mon (i j : Fin 8) : Form (Fin 8) :=
  QuadraticMap.linMulLin (LinearMap.proj i) (LinearMap.proj j)

/-- Gram form in integral coordinates. Its mixed coefficients are essential. -/
def form : Form (Fin 8) :=
  mon 0 0 + mon 0 7 + (2:ℤ) • mon 7 7 - (2:ℤ) • mon 7 6 +
    mon 1 1 + mon 2 2 + mon 3 3 + mon 4 4 + mon 5 5 + mon 6 6 -
    (mon 1 2 + mon 2 3 + mon 3 4 + mon 4 5 + mon 5 6)

theorem energy_encode (a : Fin 8 → ℤ) : energy (encode a)=8*form a := by
  rw [energy,sum_eight]
  change (a 0)^2+(a 0+2*a 1)^2+(a 0+2*(a 2-a 1))^2+(a 0+2*(a 3-a 2))^2+
    (a 0+2*(a 4-a 3))^2+(a 0+2*(a 5-a 4))^2+(a 0+2*(a 6-a 5))^2+
    (a 0+2*(2*a 7-a 6))^2 = 8*(_)
  simp only [form,mon,QuadraticMap.add_apply,QuadraticMap.sub_apply,QuadraticMap.smul_apply,
    QuadraticMap.linMulLin_apply,LinearMap.proj_apply,smul_eq_mul]
  ring

theorem form_positive : form.PosDef := by
  intro a ha
  have hn : encode a≠0 := by
    intro he
    apply ha
    rw [← decode_encode a,he]
    funext i
    fin_cases i <;> simp [decode,half]
  obtain ⟨j,hj⟩ : ∃ j, encode a j≠0 := by
    by_contra! h
    exact hn (funext h)
  have he := (sq_pos_of_ne_zero hj).trans_le
    (single_le_sum (f:=fun i => (encode a i)^2) (fun i _ => sq_nonneg _) (mem_univ j))
  change 0<energy (encode a) at he
  rw [energy_encode] at he
  omega

/-- The parity and sign classification describes precisely the roots of
the quadratic form on the full free integer lattice. -/
def rootEquiv : Root form ≃ Shell where
  toFun a := ⟨encode a.val,encode_compatible a.val,by rw [energy_encode,a.property]; norm_num⟩
  invFun x := ⟨decode x.val,by
    have he := energy_encode (decode x.val)
    rw [encode_decode x.val x.property.1,x.property.2] at he
    omega⟩
  left_inv a := Subtype.ext (decode_encode _)
  right_inv x := Subtype.ext (encode_decode _ x.property.1)

theorem root_card : Nat.card (Root form)=240 := (Nat.card_congr rootEquiv).trans shell_card

theorem line_card : Nat.card (Occupied form)=120 := by
  have h := card_roots form form_positive
  rw [root_card] at h
  omega

abbrev CubicCoordinates := Sym (Fin 8) 3 → ℚ

/-- Values of the degree-three monomials at one root on each antipodal line. -/
def feature (a : Occupied form) : CubicCoordinates :=
  fun p => (cubicFeatures (lift form a).val p : ℚ)

private theorem feature_independent : LinearIndependent ℚ feature := by
  classical
  letI := Fintype.ofFinite (Occupied form)
  have hi := independent_cubic_features form form_positive (lift form) (fun a b h =>
    Subtype.ext ((parity_lift form a).symm.trans
      (((root_parity_iff form form_positive _ _).mpr h).trans (parity_lift form b))))
  rw [← LinearIndependent.iff_fractionRing (R:=ℤ) (K:=ℚ),Fintype.linearIndependent_iff]
  intro c hc
  apply Fintype.linearIndependent_iff.mp hi c
  funext p
  have h := congrFun hc p
  simp only [Finset.sum_apply,Pi.smul_apply,zsmul_eq_mul,Pi.zero_apply,feature] at h ⊢
  exact_mod_cast h

/-- Root evaluation is a basis of the rational symmetric cube in rank eight. -/
def cubicBasis : Module.Basis (Occupied form) ℚ CubicCoordinates := by
  classical
  letI := Fintype.ofFinite (Occupied form)
  apply basisOfLinearIndependentOfCardEqFinrank' feature feature_independent
  rw [← Nat.card_eq_fintype_card,line_card,Module.finrank_pi,Sym.card_sym_eq_choose,Fintype.card_fin]
  norm_num [Nat.choose]

/-- Arbitrary signed values on the 120 chosen roots have a unique homogeneous
cubic interpolant. Its value on an input is linear in the cubic monomials. -/
theorem cubic_interpolation (v : Occupied form → ℚ) :
    ∃! F : Module.Dual ℚ CubicCoordinates, ∀ a, F (feature a)=v a := by
  have hb (a : Occupied form) : cubicBasis a=feature a := rfl
  refine ⟨cubicBasis.constr ℚ v,fun a => by rw [← hb,Module.Basis.constr_basis],?_⟩
  intro G hG
  apply cubicBasis.ext
  intro a
  rw [Module.Basis.constr_basis,hb,hG]

#print axioms encode_decode
#print axioms energy_encode
#print axioms form_positive
#print axioms root_card
#print axioms line_card
#print axioms cubicBasis
#print axioms cubic_interpolation
end GaloisForLFunctions.HTGeometry.EightShell
