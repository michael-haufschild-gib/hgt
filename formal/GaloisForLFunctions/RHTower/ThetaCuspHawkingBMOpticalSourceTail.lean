import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleRiemannKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact radial primitive for the original two-source optical tail, with the actual
native circle field and its full angular jets. No angular eigenvalue is supplied. -/
open Set MeasureTheory
namespace RHTower.D4BMOpticalSourceTail
open D4BMNativeCircle D4BMHorizon
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private def basis (i : Fin 7) (x : ℝ) : ℝ :=
  ![(-1/5)*(x^(5 : ℕ))⁻¹,(-1/4)*(x^(4 : ℕ))⁻¹,(-1/3)*(x^(3 : ℕ))⁻¹,
    (-1/2)*(x^(2 : ℕ))⁻¹,-x⁻¹,Real.log x,x] i

private theorem basis_derivative (i : Fin 7) (x : Ioi (0:ℝ)) :
    HasDerivAt (basis i) (x.val^i.val/x.val^(6 : ℕ)) x.val := by
  have hx : x.val ≠ 0 := ne_of_gt x.property
  fin_cases i
  · convert (((hasDerivAt_id x.val).pow 5).inv (pow_ne_zero 5 hx)).const_mul (-1/5) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 4).inv (pow_ne_zero 4 hx)).const_mul (-1/4) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 3).inv (pow_ne_zero 3 hx)).const_mul (-1/3) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 2).inv (pow_ne_zero 2 hx)).const_mul (-1/2) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · change HasDerivAt (fun y : ℝ => -y⁻¹) (x.val^(4 : ℕ)/x.val^(6 : ℕ)) x.val
    convert ((hasDerivAt_id x.val).inv hx).neg using 1 <;>
      first | rfl | (norm_num only [id_eq]; field_simp [hx])
  · change HasDerivAt Real.log (x.val^(5 : ℕ)/x.val^(6 : ℕ)) x.val
    convert Real.hasDerivAt_log hx using 1
    field_simp [hx]
  · change HasDerivAt (fun y : ℝ => y) (x.val^(6 : ℕ)/x.val^(6 : ℕ)) x.val
    convert hasDerivAt_id x.val using 1 <;>
      first | rfl | exact div_self (pow_ne_zero 6 hx)

private def polynomialPrimitive (c : Fin 7 → ℂ) (x : ℝ) : ℂ :=
  ∑ i, c i*(basis i x:ℂ)

private theorem polynomialPrimitive_derivative (c : Fin 7 → ℂ) (x : Ioi (0:ℝ)) :
    HasDerivAt (polynomialPrimitive c)
      (∑ i, c i*(x.val^i.val/x.val^(6 : ℕ):ℝ)) x.val := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (basis_derivative i x).ofReal_comp.const_mul (c i))

private def coefficients11 (L d : ℂ) : Fin 7 → ℂ := ![L*d,-(L+d),1,0,0,0,0]
private def coefficients13 (L d : ℂ) : Fin 7 → ℂ :=
  ![L*d^(3 : ℕ),-(3*L*d^(2 : ℕ)+d^(3 : ℕ)),3*L*d+3*d^(2 : ℕ),-(L+3*d),1,0,0]
private def coefficients33 (L d : ℂ) : Fin 7 → ℂ :=
  let H := L+d
  let J := L*d
  ![J^(3 : ℕ),-3*H*J^(2 : ℕ),3*H^(2 : ℕ)*J+3*J^(2 : ℕ),-(H^(3 : ℕ)+6*H*J),3*H^(2 : ℕ)+3*J,-3*H,1]

/-- Four actual angular coefficients of the two original quadratic source polynomials.
The slots multiply `1`, target radius squared, source radius squared, and their product. -/
def sourceCoefficients (q : XiZeroCopy) (L z X k : ℝ) : Fin 4 → ℂ :=
  let s := (q.1:ℂ)-2
  let t := -(q.1:ℂ)-1
  let lam := (q.1:ℂ)*((q.1:ℂ)-1)
  let a := (5*lam-6)/4
  let αs := s*(s-1)/4*((s+2)*(2*s+3))
  let αt := t*(t-1)/4*((t+2)*(2*t+3))
  let βs := -s*(s-1)/8
  let βt := -t*(t-1)/8
  let U := fun p : Point => angularKernel q ((L^(2 : ℕ)+1-z^(2 : ℕ))/(2*L)) (p 0) (Real.log (p 1))
  let p : Point := ![X,Real.exp k]
  let M := U p
  let D := scalarLaplacian U p
  let D2 := scalarLaplacian (scalarLaplacian U) p
  ![a^(2 : ℕ)*M,a*(αs*M+βs*D),a*(αt*M+βt*D),
    αs*αt*M+(αs*βt+βs*αt)*D+βs*βt*D2]

/-- The literal radial integrand after the optical and reflected-domain substitutions. -/
def sourceDensity (q : XiZeroCopy) (L z X k x : ℝ) : ℂ :=
  let c := sourceCoefficients q L z X k
  let y : ℂ := x-L
  let u : ℂ := x-(L-z)
  y*u/(x:ℂ)^(6 : ℕ)*(c 0+c 1*u^(2 : ℕ)+c 2*y^(2 : ℕ)/(L:ℂ)^(2 : ℕ)+c 3*u^(2 : ℕ)*y^(2 : ℕ)/(L:ℂ)^(2 : ℕ))

private def sourcePolynomial (q : XiZeroCopy) (L z X k : ℝ) (i : Fin 7) : ℂ :=
  let c := sourceCoefficients q L z X k
  c 0*coefficients11 L (L-z) i+c 1*coefficients13 L (L-z) i+
    c 2/(L:ℂ)^(2 : ℕ)*coefficients13 (L-z) L i+c 3/(L:ℂ)^(2 : ℕ)*coefficients33 L (L-z) i

/-- An explicit rational/logarithmic primitive of the complete original radial density. -/
def sourcePrimitive (q : XiZeroCopy) (L z X k x : ℝ) : ℂ :=
  polynomialPrimitive (sourcePolynomial q L z X k) x

/-- Actual differentiation evaluates the full two-source radial integrand, including
the native circle mean's first and second angular Laplacians. -/
theorem sourcePrimitive_derivative (q : XiZeroCopy) (L z X k : ℝ) (x : Ioi (0:ℝ)) :
    HasDerivAt (sourcePrimitive q L z X k) (sourceDensity q L z X k x.val) x.val := by
  convert polynomialPrimitive_derivative (sourcePolynomial q L z X k) x using 1
  · rfl
  · simp only [sourceDensity,sourcePolynomial,coefficients11,coefficients13,coefficients33,
      Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Matrix.cons_val_zero,Matrix.cons_val_succ]
    norm_num
    ring

/-- The entire radial integral is the difference of two explicit endpoint values.
Positive endpoints are data; no field equation, spectral assumption or cancellation
premise is supplied. -/
theorem sourceDensity_integral (q : XiZeroCopy) (L z X k : ℝ) (a b : Ioi (0:ℝ)) :
    (∫ x in a.val..b.val, sourceDensity q L z X k x) =
      sourcePrimitive q L z X k b.val-sourcePrimitive q L z X k a.val := by
  have hp (x : ℝ) (hx : x ∈ uIcc a.val b.val) : 0 < x :=
    lt_of_lt_of_le (lt_min a.property b.property) hx.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => sourcePrimitive_derivative q L z X k ⟨x,hp x hx⟩)
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hn : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hp x hx))
  have hc : ContinuousAt (fun y : ℝ => (y:ℂ)) x := Complex.ofRealCLM.continuous.continuousAt
  have hy := hc.sub (continuousAt_const (y := (L:ℂ)))
  have hu := hc.sub (continuousAt_const (y := ((L:ℂ)-z)))
  let c := sourceCoefficients q L z X k
  exact ((hy.mul hu).div (hc.pow 6) (pow_ne_zero 6 hn) |>.mul
    (((continuousAt_const.add (continuousAt_const.mul (hu.pow 2))).add
      ((continuousAt_const.mul (hy.pow 2)).div_const ((L:ℂ)^(2 : ℕ)))).add
      (((continuousAt_const.mul (hu.pow 2)).mul (hy.pow 2)).div_const ((L:ℂ)^(2 : ℕ))))).continuousWithinAt

/-- The sole logarithmic coefficient is a fixed fourth-order angular channel of
the actual native circle field, with both source branches retained. -/
theorem sourceCoefficients_log_channel (q : XiZeroCopy) (L z X k : ℝ) :
    sourceCoefficients q L z X k 3 =
      let lam := (q.1:ℂ)*((q.1:ℂ)-1)
      let U := fun p : Point => angularKernel q ((L^(2 : ℕ)+1-z^(2 : ℕ))/(2*L)) (p 0) (Real.log (p 1))
      let p : Point := ![X,Real.exp k]
      (lam-2)*(lam-6)/64*(scalarLaplacian (scalarLaplacian U) p-
        2*(4*lam+1)*scalarLaplacian U p+4*lam*(4*lam+1)*U p) := by
  dsimp [sourceCoefficients]
  ring

end
end RHTower.D4BMOpticalSourceTail
