import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Numerators
import GaloisForLFunctions.HTGeometry.MvPolynomialSmooth
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Mixed spectral derivatives evaluated on a simple root branch -/
open MvPolynomial Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [DecidableEq ι]

/-- Vary one coupling along a complex line through the base point. -/
def coordLine (x : ι → ℂ) (i : ι) (t : ℂ) (j : ι) := x j + if j = i then t else 0

@[simp] theorem coordLine_zero (x : ι → ℂ) (i : ι) : coordLine x i 0 = x := by
  funext j
  simp [coordLine]

private theorem line_cont (x : ι → ℂ) (i : ι) : Continuous (coordLine x i) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i <;> simp [coordLine,hj] <;> fun_prop

/-- The list is ordered with the outermost derivative first. -/
def mixed : List ι → ((ι → ℂ) → ℂ) → (ι → ℂ) → ℂ
  | [], f => f
  | i :: w, f => fun x => deriv (fun t => mixed w f (coordLine x i t)) 0

/-- Evaluation with the root in the distinguished variable. -/
def onRoot (b : MvPolynomial (Option ι) ℂ) (f : (ι → ℂ) → ℂ) (x : ι → ℂ) :=
  eval (fun j => j.elim (f x) x) b

variable [Fintype ι]

private theorem eval_line_deriv (b : MvPolynomial (Option ι) ℂ) (f : (ι → ℂ) → ℂ)
    (i : ι) (x : ι → ℂ) (u : ℂ)
    (hu : HasDerivAt (fun t => f (coordLine x i t)) u 0) :
    HasDerivAt (fun t => onRoot b f (coordLine x i t))
      (onRoot (pderiv none b) f x * u + onRoot (pderiv (some i) b) f x) 0 := by
  let v (t : ℂ) (j : Option ι) := j.elim (f (coordLine x i t)) (coordLine x i t)
  let v' (j : Option ι) : ℂ := j.elim u (fun k => if k=i then 1 else 0)
  have hv : HasDerivAt v v' 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    cases j with
    | none => exact hu
    | some j =>
      by_cases hj : j=i
      · subst j
        simpa [v,v',coordLine] using (hasDerivAt_id (0:ℂ)).const_add (x i)
      · simpa [v,v',coordLine,hj] using (hasDerivAt_const (0:ℂ) (x j))
  simpa [v,v',onRoot,Fintype.sum_option,mul_ite] using hasDerivAt_mvPolynomial_eval_comp b hv

/-- On a neighborhood of simple roots, formal tangent differentiation
divided by the root partial is ordinary differentiation along each coordinate. -/
private theorem tangent_hasDerivAt (p b : MvPolynomial (Option ι) ℂ) (f : (ι → ℂ) → ℂ)
    (i : ι) (x : ι → ℂ) (hd : DifferentiableAt ℂ f x)
    (hroot : onRoot p f =ᶠ[𝓝 x] fun _ => 0) (hs : onRoot (pderiv none p) f x ≠ 0) :
    HasDerivAt (fun t => onRoot b f (coordLine x i t))
      (onRoot (tangent p i b) f x / onRoot (pderiv none p) f x) 0 := by
  have hline : DifferentiableAt ℂ (coordLine x i) 0 := by
    apply differentiableAt_pi.mpr
    intro j
    by_cases hj : j=i
    · simpa [coordLine,hj] using ((differentiableAt_id (x := (0:ℂ))).const_add (x j))
    · simp [coordLine,hj]
  have hdf : DifferentiableAt ℂ f (coordLine x i 0) := by simpa using hd
  have hf := (hdf.comp 0 hline).hasDerivAt
  let u := deriv (fun t => f (coordLine x i t)) 0
  have hu : HasDerivAt (fun t => f (coordLine x i t)) u 0 := hf
  have hnear : (fun t => onRoot p f (coordLine x i t)) =ᶠ[𝓝 0] fun _ => 0 :=
    hroot.comp_tendsto (by simpa only [coordLine_zero] using ((line_cont x i).continuousAt (x := 0)).tendsto)
  have hz := (eval_line_deriv p f i x u hu).unique ((hasDerivAt_const 0 (0:ℂ)).congr_of_eventuallyEq hnear)
  convert eval_line_deriv b f i x u hu using 1
  rw [div_eq_iff hs]
  simp only [onRoot,tangent,map_sub,map_mul] at *
  linear_combination -(eval (fun j : Option ι => j.elim (f x) x) (pderiv none b)) * hz

private theorem clear_quotient_derivative (H B T S : ℂ) (hH : H ≠ 0) (n : ℕ) :
    H*T - (n:ℂ)*(B*S) =
      H^(n+2)*((T/H*H^n-B*((n:ℂ)*H^(n-1)*(S/H)))/(H^n)^2) := by
  cases n with
  | zero => simp [pow_two]
            field_simp
  | succ n =>
    simp only [Nat.succ_sub_one,pow_succ]
    field_simp [hH]

/-- At every simple root branch the polynomial numerator evaluates to the
mixed derivative times the root partial raised to twice its order. -/
theorem onRoot_numerator (p : MvPolynomial (Option ι) ℂ) (f : (ι → ℂ) → ℂ)
    {U : Set (ι → ℂ)} (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hroot : ∀ x ∈ U, onRoot p f x = 0) (hs : ∀ x ∈ U, onRoot (pderiv none p) f x ≠ 0)
    (w : List ι) (x : ι → ℂ) (hx : x ∈ U) :
    onRoot (numerator p w) f x = (onRoot (pderiv none p) f x)^(2*w.length)*mixed w f x := by
  induction w generalizing x with
  | nil => simp [numerator,mixed,onRoot]
  | cons i w ih =>
    let h := pderiv none p
    let b := numerator p w
    let e := 2*w.length
    let E := fun q => onRoot q f x
    have diff := hd.differentiableAt (hU.mem_nhds hx)
    have root : onRoot p f =ᶠ[𝓝 x] fun _ => 0 := Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hroot y hy)
    have hh := tangent_hasDerivAt p h f i x diff root (hs x hx)
    have hb := tangent_hasDerivAt p b f i x diff root (hs x hx)
    have hden : onRoot h f (coordLine x i 0)^e ≠ 0 := by
      simpa only [coordLine_zero] using pow_ne_zero e (hs x hx)
    have hq := hb.div (hh.pow e) hden
    have hnear : (fun t => mixed w f (coordLine x i t)) =ᶠ[𝓝 0]
        fun t => onRoot b f (coordLine x i t) / onRoot h f (coordLine x i t)^e := by
      have ht : Tendsto (coordLine x i) (𝓝 0) (𝓝 x) := by simpa only [coordLine_zero] using ((line_cont x i).continuousAt (x := 0)).tendsto
      filter_upwards [ht (hU.mem_nhds hx)] with t ht
      exact (eq_div_iff (pow_ne_zero _ (hs _ ht))).mpr (by rw [ih _ ht,mul_comm])
    have hv := (hq.congr_of_eventuallyEq hnear).deriv
    simp only [Pi.pow_apply,coordLine_zero] at hv
    change mixed (i::w) f x = (E (tangent p i b)/E h * E h^e -
      E b * ((e:ℂ)*E h^(e-1)*(E (tangent p i h)/E h))) / (E h^e)^2 at hv
    rw [hv]
    change E (h * tangent p i b - e • (b * tangent p i h)) = E h^(2*(w.length+1)) * _
    have hup : 2*(w.length+1) = e+2 := by dsimp [e]; omega
    rw [hup]
    simpa only [E,onRoot,map_sub,map_mul,map_nsmul,nsmul_eq_mul,map_natCast] using
      clear_quotient_derivative (E h) (E b) (E (tangent p i b)) (E (tangent p i h)) (hs x hx) e

#print axioms onRoot_numerator
end
end GaloisForLFunctions.HTGeometry.SpectralJets
