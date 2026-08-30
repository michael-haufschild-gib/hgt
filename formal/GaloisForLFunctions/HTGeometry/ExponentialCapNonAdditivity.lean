import GaloisForLFunctions.HTGeometry.GaussianOrderLedger

/-!
# The exponential cap and the failure of order additivity

The exponential is autonomous of first order, its jet field is `ℂ(z, exp z)` and its shadow field is
the same, so it has differential rank two and primitive defect zero.  Composing it with the Gaussian
primitive `G` gives, by the shadow law, differential rank `shadow rank of G` plus one, that is three
— the same rank as `G` itself.

In the card's normalization `ord_DA u = daRank u − 1`, so `ord_DA (exp) = 1`, `ord_DA G = 2` and
`ord_DA (exp ∘ G) = 2`, while additivity would demand three.  The single compressed state is the
primitive defect of `G`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### The exponential inside the meromorphic field -/

theorem analyticOnNhd_cexp : AnalyticOnNhd ℂ Complex.exp (Set.univ : Set ℂ) :=
  Complex.differentiable_exp.differentiableOn.analyticOnNhd isOpen_univ

/-- The exponential as an element of the meromorphic field. -/
def expElem : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement Complex.exp analyticOnNhd_cexp

theorem deriv_expElem : expElem′ = expElem := by
  rw [expElem, deriv_analyticMeroElement']
  exact analyticMeroElement_congr _ _ Complex.deriv_exp

theorem expElem_ne_zero : expElem ≠ 0 := by
  rw [expElem]
  intro h
  have := (analyticMeroElement_eq_zero_iff analyticOnNhd_cexp).mp h 0 (Set.mem_univ 0)
  exact Complex.exp_ne_zero 0 this

theorem iteratedDeriv_cexp (n : ℕ) : iteratedDeriv n Complex.exp = Complex.exp := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]

theorem jetElem_exp (k : ℕ) : jetElem Complex.differentiable_exp k = expElem := by
  rw [jetElem, expElem]
  exact analyticMeroElement_congr _ _ (iteratedDeriv_cexp k)

/-! ### The exponential is transcendental over the rational functions -/

theorem one_mem_ratField : (1 : meroField (Set.univ : Set ℂ)) ∈ ratField := one_mem _

theorem natCast_ratFunc_eq (k : ℕ) :
    (k : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C ((k : ℕ) : ℂ)) := by
  rw [← map_natCast (algebraMap (Polynomial ℂ) (RatFunc ℂ)) k]
  congr 1

/-- **No nonzero rational function solves the scaled exponential equation.** -/
theorem hker_exp_ratField (k : ℕ) (hk : 1 ≤ k) (w : meroField (Set.univ : Set ℂ))
    (hw : w ∈ ratField)
    (h : meroComplexDerivation w = (k : meroField (Set.univ : Set ℂ)) * 1 * w) :
    w = 0 := by
  obtain ⟨r, rfl⟩ := hw
  have hk0 : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnat : (k : meroField (Set.univ : Set ℂ))
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (k : RatFunc ℂ) :=
    (map_natCast _ k).symm
  have hleft : meroComplexDerivation (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r)
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r′ := deriv_algebraMap r
  rw [hleft, mul_one, hnat, ← map_mul] at h
  have hr : r′ = (k : RatFunc ℂ) * r := algebraMap_ratFunc_injective h
  have hzero : r = 0 := by
    refine GaloisForLFunctions.RationalShadow.eq_zero_of_deriv_eq_const_mul hk0 ?_
    have hd : ratFuncCoordinateDerivation ℂ r = r′ := rfl
    rw [hd, hr, natCast_ratFunc_eq k]
  rw [hzero, map_zero]

/-- **The exponential is transcendental over the rational functions.** -/
theorem transcendental_expElem : Transcendental ↥ratField expElem := by
  refine transcendental_of_hyperexponential meroComplexDerivation ratField
    derivationClosed_ratField' expElem_ne_zero one_mem_ratField ?_ ?_
  · rw [one_mul]
    simpa using deriv_expElem
  · intro k hk w hw hrel
    exact hker_exp_ratField k hk w hw (by simpa using hrel)

/-! ### The two ranks of the exponential -/

theorem jetSet_exp_eq :
    insert coordElem (Set.range fun k : ℕ => jetElem Complex.differentiable_exp k)
      = insert expElem ({coordElem} : Set (meroField (Set.univ : Set ℂ))) := by
  ext y
  constructor
  · rintro (rfl | ⟨k, rfl⟩)
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert_iff.mpr (Or.inl (jetElem_exp k))
  · rintro (rfl | rfl)
    · exact Set.mem_insert_of_mem _ ⟨0, jetElem_exp 0⟩
    · exact Set.mem_insert _ _

theorem shadowSet_exp_eq :
    insert coordElem (Set.range fun j : ℕ => jetElem Complex.differentiable_exp (j + 1))
      = insert expElem ({coordElem} : Set (meroField (Set.univ : Set ℂ))) := by
  ext y
  constructor
  · rintro (rfl | ⟨j, rfl⟩)
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert_iff.mpr (Or.inl (jetElem_exp (j + 1)))
  · rintro (rfl | rfl)
    · exact Set.mem_insert_of_mem _ ⟨0, jetElem_exp 1⟩
    · exact Set.mem_insert _ _

theorem trdeg_adjoin_coordElem_expElem :
    Algebra.trdeg ℂ ↥(IntermediateField.adjoin ℂ
      (insert expElem ({coordElem} : Set (meroField (Set.univ : Set ℂ))))) = 2 := by
  have hle : IntermediateField.adjoin ℂ ({coordElem} : Set (meroField (Set.univ : Set ℂ)))
      ≤ ratField := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y rfl
    exact coordElem_mem_ratField
  have htr : ¬ IsAlgebraic ↥(IntermediateField.adjoin ℂ
      ({coordElem} : Set (meroField (Set.univ : Set ℂ)))) expElem := fun h =>
    transcendental_expElem (isAlgebraic_of_le hle h)
  have h1 := trdeg_adjoin_insert_eq_add_one htr
  exact h1.trans
    ((congrArg (fun c : Cardinal => c + 1) trdeg_adjoin_coordElem).trans (by norm_num))

/-- **The exponential has differential rank two.** -/
theorem daRank_exp : daRank Complex.differentiable_exp = 2 := by
  rw [daRank, jetSet_exp_eq]
  exact trdeg_adjoin_coordElem_expElem

/-- **The exponential has shadow rank two: its primitive defect vanishes.** -/
theorem shadowRank_exp : shadowRank' Complex.differentiable_exp = 2 := by
  rw [shadowRank', shadowSet_exp_eq]
  exact trdeg_adjoin_coordElem_expElem

/-! ### The exponential is an autonomous first-order cap -/

/-- **The exponential satisfies an autonomous first-order equation**, namely `f′ = f`. -/
theorem autonomousFirstOrder_exp : AutonomousFirstOrder Complex.exp := by
  refine ⟨1, fun k => if k = 0 then -Polynomial.X else 1, ⟨1, le_refl 1, by simp⟩, ?_⟩
  intro w
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [Complex.deriv_exp]

/-! ### The side conditions of the shadow law -/

theorem not_exists_poly_of_zeroFree {f : ℂ → ℂ} (hne : ∀ z : ℂ, f z ≠ 0)
    (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c) :
    ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z := by
  rintro ⟨p, hp⟩
  by_cases hd : p.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hd
    refine hnc ⟨c, fun z => ?_⟩
    rw [hp z, ← hc, Polynomial.eval_C]
  · have hdeg : 0 < p.degree := by
      have hp0 : p ≠ 0 := by
        intro h
        exact hd (by rw [h, Polynomial.natDegree_zero])
      rw [Polynomial.degree_eq_natDegree hp0]
      exact_mod_cast Nat.pos_of_ne_zero hd
    obtain ⟨z₀, hz₀⟩ := Complex.exists_root hdeg
    exact hne z₀ (by rw [hp z₀]; exact hz₀)

theorem not_const_of_deriv_ne_zero {f : ℂ → ℂ} {z₀ : ℂ} (h : deriv f z₀ ≠ 0) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c := by
  rintro ⟨c, hc⟩
  refine h ?_
  have hf : f = fun _ : ℂ => c := funext hc
  rw [hf, deriv_const]

theorem not_const_cexp : ¬ ∃ c : ℂ, ∀ z : ℂ, Complex.exp z = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 0) ?_
  rw [Complex.deriv_exp]
  exact Complex.exp_ne_zero 0

/-- The exponential is not a polynomial. -/
theorem not_poly_cexp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, Complex.exp z = p.eval z :=
  not_exists_poly_of_zeroFree (fun z => Complex.exp_ne_zero z) not_const_cexp

theorem not_const_gaussianExp : ¬ ∃ c : ℂ, ∀ z : ℂ, Complex.exp (-z ^ 2) = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 1) ?_
  have h2 : HasDerivAt (fun w : ℂ => -(w ^ 2)) (-((2 : ℕ) * (1 : ℂ) ^ (2 - 1))) 1 :=
    (hasDerivAt_pow 2 1).neg
  have hd := h2.cexp
  rw [hd.deriv]
  simp

theorem not_poly_gaussianExp :
    ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, Complex.exp (-z ^ 2) = p.eval z :=
  not_exists_poly_of_zeroFree (fun _ => Complex.exp_ne_zero _) not_const_gaussianExp

/-- The Gaussian primitive is not a polynomial: its derivative is not one. -/
theorem not_poly_gaussPrimitive :
    ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, gaussPrimitive z = p.eval z := by
  rintro ⟨p, hp⟩
  refine not_poly_gaussianExp ⟨p.derivative, fun z => ?_⟩
  have hfun : gaussPrimitive = fun z : ℂ => p.eval z := funext hp
  have hd : deriv gaussPrimitive z = p.derivative.eval z := by
    rw [hfun]
    exact Polynomial.deriv p
  rw [← hd, deriv_gaussPrimitive]

theorem not_const_gaussPrimitive : ¬ ∃ c : ℂ, ∀ z : ℂ, gaussPrimitive z = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 0) ?_
  rw [deriv_gaussPrimitive]
  exact Complex.exp_ne_zero _

theorem differentiable_expGauss :
    Differentiable ℂ (fun w : ℂ => Complex.exp (gaussPrimitive w)) :=
  Complex.differentiable_exp.comp differentiable_gaussPrimitive

theorem not_const_expGauss :
    ¬ ∃ c : ℂ, ∀ z : ℂ, Complex.exp (gaussPrimitive z) = c := by
  refine not_const_of_deriv_ne_zero (z₀ := 0) ?_
  have hd := (hasDerivAt_gaussPrimitive 0).cexp
  rw [hd.deriv]
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-! ### The order law for the Gaussian primitive under the exponential cap -/

/-- **The exponential of the Gaussian primitive has differential rank three.** -/
theorem daRank_expGauss : daRank differentiable_expGauss = 3 := by
  have h := daRank_comp Complex.differentiable_exp differentiable_gaussPrimitive
    autonomousFirstOrder_exp differentiable_expGauss not_poly_cexp not_poly_gaussPrimitive
    not_const_expGauss not_const_gaussPrimitive
  exact h.trans
    ((congrArg (fun c : Cardinal => c + 1) shadowRank_gaussPrimitive).trans (by norm_num))

/-- **Differential order is not additive under composition.**  With `ord_DA u = daRank u − 1` the
identity `ord_DA (f ∘ g) = ord_DA f + ord_DA g` would read `daRank (f ∘ g) + 1 = daRank f + daRank g`,
and the exponential cap applied to the Gaussian primitive violates it. -/
theorem order_not_additive_expGauss :
    daRank differentiable_expGauss + 1
      ≠ daRank Complex.differentiable_exp + daRank differentiable_gaussPrimitive := by
  rw [daRank_expGauss, daRank_exp, daRank_gaussPrimitive]
  norm_num

end

end GaloisForLFunctions.HTGeometry
