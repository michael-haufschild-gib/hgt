import GaloisForLFunctions.RHTower.BarnesRemainderJetBridge
import GaloisForLFunctions.HTGeometry.BarnesRemainderDATransfer
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# The Barnes remainder inherits differential algebraicity from the product

The right half-plane is a domain carrying `W_s`, its reciprocal, the branch `z^{1/s}` and the
ascending polynomial part, so the whole Barnes decomposition lives in one meromorphic differential
field.  The leading term is the solution of the Euler eigen-equation `z u' = (1/s) u`, the
polynomial part is rational, and the remaining closure properties are the corpus's; so a
differentially algebraic `W_s` forces a differentially algebraic remainder.
-/

open Complex Filter Set
open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

namespace RHTower

noncomputable section

variable {s : ℝ}

local notation "RHP" => HTGeometry.rightHalfPlane

local instance rhpDomain : IsDomain (analyticSubring HTGeometry.rightHalfPlane) :=
  Bottcher.isDomain_analyticSubring _ HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty

local instance rhpAlgebra : Algebra (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane) :=
  (ratfuncToMero _ HTGeometry.isOpen_rightHalfPlane HTGeometry.isPreconnected_rightHalfPlane
    HTGeometry.rightHalfPlane_nonempty HTGeometry.rightHalfPlane_infinite).toAlgebra

local instance rhpDifferential : Differential (meroField HTGeometry.rightHalfPlane) :=
  meroFieldDifferential HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty

local instance rhpCharZero : CharZero (meroField HTGeometry.rightHalfPlane) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane)).injective

local instance rhpRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance rhpDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField HTGeometry.rightHalfPlane) :=
  meroFieldRatFuncDifferentialAlgebra HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty
    HTGeometry.rightHalfPlane_infinite

/-! ### Realizations -/

theorem analyticOnNhd_id_rightHalfPlane :
    AnalyticOnNhd ℂ (fun z : ℂ => z) HTGeometry.rightHalfPlane := fun _ _ => analyticAt_id

/-- The germ of the derivative is the derivative of the germ. -/
theorem deriv_analyticMeroElement_rhp {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f RHP) :
    (analyticMeroElement f hf)′ = analyticMeroElement (deriv f) hf.deriv := by
  have h := differentialJet_analyticMeroElement HTGeometry.isOpen_rightHalfPlane
    HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty f hf 1
  rw [differentialJet_succ, differentialJet_zero] at h
  rw [h, analyticMeroElement, analyticJetElement, analyticFunctionElement]
  congr 1
  apply Subtype.ext
  change ((iteratedDeriv 1 f : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
    = ((deriv f : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
  rw [iteratedDeriv_one]

theorem analyticMeroElement_ne_zero_of_ne {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f RHP)
    {z₀ : ℂ} (hz₀ : z₀ ∈ RHP) (hval : f z₀ ≠ 0) : analyticMeroElement f hf ≠ 0 := by
  intro hzero
  exact hval ((analyticMeroElement_eq_zero_iff hf).mp hzero z₀ hz₀)

/-- The meromorphic realization depends only on the values on the domain. -/
theorem analyticMeroElement_congr_eqOn {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f RHP)
    (hg : AnalyticOnNhd ℂ g RHP) (h : Set.EqOn f g RHP) :
    analyticMeroElement f hf = analyticMeroElement g hg := by
  rw [analyticMeroElement, analyticMeroElement]
  congr 1
  apply Subtype.ext
  change ((f : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
    = ((g : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
  rw [Germ.coe_eq]
  exact Filter.eventually_principal.mpr h

/-- A quotient of analytic functions with nonvanishing denominator is realized by the quotient. -/
theorem analyticMeroElement_div {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f RHP)
    (hg : AnalyticOnNhd ℂ g RHP) (hgne : ∀ z ∈ RHP, g z ≠ 0) :
    analyticMeroElement (fun z => f z / g z) (hf.div hg hgne)
      = analyticMeroElement f hf / analyticMeroElement g hg := by
  have hgne0 : analyticMeroElement g hg ≠ 0 :=
    analyticMeroElement_ne_zero_of_ne hg (z₀ := 1) (by simp [HTGeometry.rightHalfPlane])
      (hgne 1 (by simp [HTGeometry.rightHalfPlane]))
  rw [eq_div_iff hgne0, ← analyticMeroElement_mul]
  refine analyticMeroElement_congr_eqOn ((hf.div hg hgne).mul hg) hf ?_
  intro z hz
  exact div_mul_cancel₀ (f z) (hgne z hz)

/-! ### The base elements -/

theorem analyticMeroElement_id_eq_algebraMap :
    analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane
      = algebraMap (RatFunc ℂ) (meroField RHP) RatFunc.X := by
  have hpoly : algebraMap (RatFunc ℂ) (meroField RHP) RatFunc.X
      = polyToMero RHP Polynomial.X := by
    rw [show (RatFunc.X : RatFunc ℂ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X from (RatFunc.algebraMap_X).symm]
    exact ratfuncToMero_algebraMap_polynomial RHP HTGeometry.isOpen_rightHalfPlane
      HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty
      HTGeometry.rightHalfPlane_infinite Polynomial.X
  rw [hpoly, polyToMero, RingHom.comp_apply, analyticMeroElement]
  congr 1
  apply Subtype.ext
  change ((fun z : ℂ => z : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
    = ((fun z : ℂ => (Polynomial.X : Polynomial ℂ).eval z : ℂ → ℂ) :
        Germ (Filter.principal RHP) ℂ)
  congr 1
  funext z
  rw [Polynomial.eval_X]

theorem analyticMeroElement_id_ne_zero :
    analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane ≠ 0 :=
  analyticMeroElement_ne_zero_of_ne _ (z₀ := 1) (by simp [HTGeometry.rightHalfPlane]) one_ne_zero

/-! ### The leading term -/

theorem deriv_barnesLeadingTermC (s : ℝ) {z : ℂ} (hz : z ∈ RHP) :
    deriv (barnesLeadingTermC s) z
      = ((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ))
        * ((1 / (s : ℂ)) * z ^ (1 / (s : ℂ) - 1)) := by
  have hslit : z ∈ Complex.slitPlane := HTGeometry.rightHalfPlane_subset_slitPlane hz
  have hpow := (Complex.hasStrictDerivAt_cpow_const (c := 1 / (s : ℂ)) hslit).hasDerivAt
  have h := hpow.const_mul
    (((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ)))
  exact h.deriv

/-- **The leading term solves the Euler eigen-equation.** -/
theorem eulerEigen_barnesLeadingTermC (s : ℝ) :
    analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane
        * (analyticMeroElement (barnesLeadingTermC s) (analyticOnNhd_barnesLeadingTermC s))′
      = algebraMap (RatFunc ℂ) (meroField RHP) (RatFunc.C (1 / (s : ℂ)))
        * analyticMeroElement (barnesLeadingTermC s) (analyticOnNhd_barnesLeadingTermC s) := by
  have hLead := analyticOnNhd_barnesLeadingTermC s
  rw [deriv_analyticMeroElement_rhp hLead, ← analyticMeroElement_mul]
  have hconst : algebraMap (RatFunc ℂ) (meroField RHP) (RatFunc.C (1 / (s : ℂ)))
      = polyToMero RHP (Polynomial.C (1 / (s : ℂ))) := by
    rw [show (RatFunc.C (1 / (s : ℂ)) : RatFunc ℂ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (1 / (s : ℂ))) from
      (RatFunc.algebraMap_C _).symm]
    exact ratfuncToMero_algebraMap_polynomial RHP HTGeometry.isOpen_rightHalfPlane
      HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty
      HTGeometry.rightHalfPlane_infinite _
  have hcm : polyToMero RHP (Polynomial.C (1 / (s : ℂ)))
      = analyticMeroElement (fun _ : ℂ => 1 / (s : ℂ)) (fun _ _ => analyticAt_const) := by
    rw [polyToMero, RingHom.comp_apply, analyticMeroElement]
    congr 1
    apply Subtype.ext
    change ((fun z : ℂ => (Polynomial.C (1 / (s : ℂ))).eval z : ℂ → ℂ) :
        Germ (Filter.principal RHP) ℂ)
      = ((fun _ : ℂ => 1 / (s : ℂ) : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
    congr 1
    funext z
    rw [Polynomial.eval_C]
  rw [hconst, hcm, ← analyticMeroElement_mul]
  refine analyticMeroElement_congr_eqOn _ _ ?_
  intro z hz
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp [HTGeometry.rightHalfPlane] at hz
  show z * deriv (barnesLeadingTermC s) z = 1 / (s : ℂ) * barnesLeadingTermC s z
  rw [deriv_barnesLeadingTermC s hz, barnesLeadingTermC]
  have hstep : z * z ^ (1 / (s : ℂ) - 1) = z ^ (1 / (s : ℂ)) := by
    conv_rhs => rw [show (1 / (s : ℂ)) = 1 + (1 / (s : ℂ) - 1) from by ring]
    rw [Complex.cpow_add _ _ hzne, Complex.cpow_one]
  calc z * (((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ))
        * ((1 / (s : ℂ)) * z ^ (1 / (s : ℂ) - 1)))
      = (1 / (s : ℂ)) * (((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ))
          * (z * z ^ (1 / (s : ℂ) - 1))) := by ring
    _ = (1 / (s : ℂ)) * (((Real.pi : ℂ) / (s : ℂ)) / Complex.sin ((Real.pi : ℂ) / (s : ℂ))
          * z ^ (1 / (s : ℂ))) := by rw [hstep]

theorem differentialAlgebraicOver_barnesLeadingTermC (s : ℝ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (barnesLeadingTermC s) (analyticOnNhd_barnesLeadingTermC s)) := by
  have heig := eulerEigen_barnesLeadingTermC s
  have hxne0 : analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane ≠ 0 :=
    analyticMeroElement_id_ne_zero
  have hxmap := analyticMeroElement_id_eq_algebraMap
  set xm := analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane with hxmdef
  set um := analyticMeroElement (barnesLeadingTermC s) (analyticOnNhd_barnesLeadingTermC s)
    with humdef
  set A := algebraMap (RatFunc ℂ) (meroField RHP) (RatFunc.C (1 / (s : ℂ))) with hAdef
  refine differentialAlgebraicOver_eulerEigen (RatFunc.C (1 / (s : ℂ)) / RatFunc.X) ?_
  have hdiv : algebraMap (RatFunc ℂ) (meroField RHP) (RatFunc.C (1 / (s : ℂ)) / RatFunc.X)
      = A * xm⁻¹ := by
    rw [map_div₀, ← hAdef, ← hxmap, div_eq_mul_inv]
  rw [hdiv]
  calc um′ = xm⁻¹ * (xm * um′) := by rw [← mul_assoc, inv_mul_cancel₀ hxne0, one_mul]
    _ = xm⁻¹ * (A * um) := by rw [heig]
    _ = A * xm⁻¹ * um := by ring


/-! ### The polynomial part -/

/-- The ascending part of the Barnes expansion, as a polynomial. -/
def barnesPolyPartPoly (s : ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
    Polynomial.C (((-1 : ℂ)) ^ ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ))
        * riemannZeta (-(s : ℂ) * ((((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) : ℤ) : ℂ)))
      * Polynomial.X ^ (HTGeometry.powerGenus s - k)

theorem barnesPolyPartPoly_eval (s : ℝ) (z : ℂ) :
    (barnesPolyPartPoly s).eval z
      = ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
          barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z := by
  rw [barnesPolyPartPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkle : k ≤ HTGeometry.powerGenus s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcast : -((((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) : ℤ) : ℂ)
      = (((HTGeometry.powerGenus s - k : ℕ)) : ℂ) := by
    rw [Nat.cast_sub hkle]
    push_cast
    ring
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    barnesTermC, hcast, Complex.cpow_natCast]

theorem analyticOnNhd_barnesPolyPartFun (s : ℝ) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z)
      HTGeometry.rightHalfPlane :=
  Finset.analyticOnNhd_fun_sum _ fun _ _ => analyticOnNhd_barnesTermC s _

theorem analyticMeroElement_barnesPolyPart (s : ℝ) :
    analyticMeroElement _ (analyticOnNhd_barnesPolyPartFun s)
      = algebraMap (RatFunc ℂ) (meroField RHP)
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesPolyPartPoly s)) := by
  have hbase : algebraMap (RatFunc ℂ) (meroField RHP)
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesPolyPartPoly s))
      = polyToMero RHP (barnesPolyPartPoly s) :=
    ratfuncToMero_algebraMap_polynomial RHP HTGeometry.isOpen_rightHalfPlane
      HTGeometry.isPreconnected_rightHalfPlane HTGeometry.rightHalfPlane_nonempty
      HTGeometry.rightHalfPlane_infinite _
  rw [hbase, polyToMero, RingHom.comp_apply, analyticMeroElement]
  congr 1
  apply Subtype.ext
  change ((fun z : ℂ => ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
      barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z : ℂ → ℂ) :
        Germ (Filter.principal RHP) ℂ)
    = ((fun z : ℂ => (barnesPolyPartPoly s).eval z : ℂ → ℂ) : Germ (Filter.principal RHP) ℂ)
  congr 1
  funext z
  rw [barnesPolyPartPoly_eval]

theorem differentialAlgebraicOver_barnesPolyPart (s : ℝ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement _ (analyticOnNhd_barnesPolyPartFun s)) := by
  rw [analyticMeroElement_barnesPolyPart s]
  exact differentialAlgebraicOver_algebraMap _

/-! ### The decomposition -/

theorem analyticMeroElement_barnesRemainderC_eq (hs : 0 < s) :
    analyticMeroElement (barnesRemainderC s) (analyticOnNhd_barnesRemainderC hs)
      = analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane
          * ((analyticMeroElement (HTGeometry.powerCanonicalProduct s)
              (analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs))′
            / analyticMeroElement (HTGeometry.powerCanonicalProduct s)
              (analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs))
        - (analyticMeroElement (barnesLeadingTermC s) (analyticOnNhd_barnesLeadingTermC s)
          + analyticMeroElement _ (analyticOnNhd_barnesPolyPartFun s)) := by
  have hW := analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs
  have hWne : ∀ z ∈ RHP, HTGeometry.powerCanonicalProduct s z ≠ 0 :=
    fun z hz => HTGeometry.powerCanonicalProduct_ne_zero_of_re_pos hs hz
  rw [deriv_analyticMeroElement_rhp hW, ← analyticMeroElement_div hW.deriv hW hWne,
    ← analyticMeroElement_mul, ← analyticMeroElement_add, ← analyticMeroElement_sub]
  refine analyticMeroElement_congr_eqOn _ _ ?_
  intro z hz
  show barnesRemainderC s z
    = z * (deriv (HTGeometry.powerCanonicalProduct s) z / HTGeometry.powerCanonicalProduct s z)
      - (barnesLeadingTermC s z
        + ∑ k ∈ Finset.range (HTGeometry.powerGenus s + 1),
            barnesTermC s ((k : ℤ) - ((HTGeometry.powerGenus s : ℕ) : ℤ)) z)
  rw [barnesRemainderC, sub_sub,
    show logDeriv (HTGeometry.powerCanonicalProduct s) z
      = deriv (HTGeometry.powerCanonicalProduct s) z
        / HTGeometry.powerCanonicalProduct s z from rfl]

/-- **The Barnes remainder is differentially algebraic when the product is.** -/
theorem differentialAlgebraicOver_barnesRemainderC (hs : 0 < s)
    (hW : DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (HTGeometry.powerCanonicalProduct s)
        (analyticOnNhd_powerCanonicalProduct_rightHalfPlane hs))) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (barnesRemainderC s) (analyticOnNhd_barnesRemainderC hs)) := by
  have hx : DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (fun z : ℂ => z) analyticOnNhd_id_rightHalfPlane) := by
    rw [analyticMeroElement_id_eq_algebraMap]
    exact differentialAlgebraicOver_algebraMap _
  exact differentialAlgebraicOver_barnesRemainder hx hW
    (differentialAlgebraicOver_barnesLeadingTermC s)
    (differentialAlgebraicOver_barnesPolyPart s)
    (analyticMeroElement_barnesRemainderC_eq hs)

end

end RHTower
