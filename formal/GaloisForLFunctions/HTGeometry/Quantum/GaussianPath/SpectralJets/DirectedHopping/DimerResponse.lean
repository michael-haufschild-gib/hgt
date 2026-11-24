import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! # Walsh components of a directed dimer response -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.DirectedHopping
noncomputable section

/-- Sign of a computational spin or a ladder direction. -/
def spin : Bool → ℝ
  | false => 1
  | true => -1

/-- Rational energy-denominator response of a dimer with onsite fields
one and two. The overlap term is present precisely when the initial
spin product differs from the product of the two ladder directions. -/
def dimer (q a b : Bool) (x : ℝ) : ℝ :=
  let u := spin a
  let v := spin b
  let c := u*v
  (1+x*(c-spin q)/(u+2*v))/(4*(u+x*c)*(2*v+x*c))

/-- The common denominator is independent of the two spins. Each
coefficient of the numerator belongs to the traceless Walsh subspace. -/
theorem dimer_cleared (q a b : Bool) {x : ℝ} (hx : |x|<1) :
    let u := spin a
    let v := spin b
    let k := spin q
    12*(1-x^2)*(4-x^2)*dimer q a b x =
      6*u*v + x*(-(8+4*k)*u+(1+2*k)*v) + x^2*(3*k*u*v)
        + x^3*((2+k)*u-(1+2*k)*v) := by
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hx
  have h₁ : 1+x ≠ 0 := by linarith
  have h₂ : 1-x ≠ 0 := by linarith
  have h₃ : 2+x ≠ 0 := by linarith
  have h₄ : 2-x ≠ 0 := by linarith
  cases q <;> cases a <;> cases b <;> dsimp [dimer,spin] <;>
    ring_nf at h₁ h₂ h₃ h₄ ⊢ <;>
    field_simp <;> first | ring | linarith

/-- The four diagonal responses have zero sum at every interior coupling. -/
theorem dimer_trace (q : Bool) {x : ℝ} (hx : |x|<1) :
    dimer q false false x+dimer q false true x+
      dimer q true false x+dimer q true true x=0 := by
  let W := 12*(1-x^2)*(4-x^2)
  have hp : x^2<1 := by
    obtain ⟨hn,hp⟩ := abs_lt.mp hx
    nlinarith only [mul_pos (sub_pos.mpr hp) (show 0<1+x by linarith only [hn])]
  have hW : W ≠ 0 := by
    dsimp only [W]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by linarith only [hp])) (by linarith only [hp])
  apply (mul_eq_zero.mp (show W*(dimer q false false x+dimer q false true x+
      dimer q true false x+dimer q true true x)=0 from ?_)).resolve_left hW
  dsimp only [W]
  rw [mul_add,mul_add,mul_add,dimer_cleared q false false hx,dimer_cleared q false true hx,
    dimer_cleared q true false hx,dimer_cleared q true true hx]
  dsimp only [spin]
  ring

/-- Constant and linear responses resolve the individual spins and their
product. Coupling is differentiated in units of the smaller onsite field. -/
theorem dimer_walsh (a b : Bool) :
    let p := deriv (dimer false a b) 0
    let m := deriv (dimer true a b) 0
    spin a*spin b = 8*dimer false a b 0 ∧
    spin a = -2*(p+3*m) ∧ spin b = 8*(p-3*m) := by
  have hs (q : Bool) : HasDerivAt (dimer q a b)
      ((-(8+4*spin q)*spin a+(1+2*spin q)*spin b)/48) 0 := by
    let u := spin a
    let v := spin b
    let c := u*v
    let f (x : ℝ) := 1+x*((c-spin q)/(u+2*v))
    let g (x : ℝ) := (4:ℝ)*(u+x*c)*(2*v+x*c)
    have hf : HasDerivAt f ((c-spin q)/(u+2*v)) 0 := by
      simpa [f] using (((hasDerivAt_id (0:ℝ)).mul_const ((c-spin q)/(u+2*v))).const_add 1)
    have h₁ : HasDerivAt (fun x : ℝ => u+x*c) c 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).mul_const c).const_add u)
    have h₂ : HasDerivAt (fun x : ℝ => 2*v+x*c) c 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).mul_const c).const_add (2*v))
    have hg := (h₁.const_mul 4).mul h₂
    have hn : g 0 ≠ 0 := by cases a <;> cases b <;> norm_num [g,u,v,spin]
    have h := hf.div hg hn
    have heq : dimer q a b = fun x => f x/g x := by
      funext x
      simp only [dimer,f,g,u,v,c,div_eq_mul_inv,mul_assoc]
    rw [heq]
    convert h using 1 <;> cases q <;> cases a <;> cases b <;> norm_num [f,g,u,v,c,spin]
  dsimp only
  rw [(hs false).deriv,(hs true).deriv]
  cases a <;> cases b <;> norm_num [dimer,spin]

#print axioms dimer_trace
#print axioms dimer_walsh
end
end GaloisForLFunctions.HTGeometry.SpectralJets.DirectedHopping
