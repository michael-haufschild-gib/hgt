import GaloisForLFunctions.HTGeometry.RatFuncUpperEndGerm
import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIncrement

/-!
# Negligible germs at the upper end

Vertical negligibility only sees the behaviour above a height, so it descends to germs at the upper
end.  On germs the closure properties become algebraic: negligible germs are stable under
subtraction, under the translation action, and under multiplication by the germ of a rational
function, while a nonzero rational function is never negligible.

These are the four hypotheses the Hölder eliminator needs, transported to the ring where the
evaluation of jet polynomials lives.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Negligibility transfers along germ equality. -/
theorem IsVerticallyNegligible.germ_congr {f f' : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (h : (f : Germ upperEndFilter ℂ) = (f' : Germ upperEndFilter ℂ)) :
    IsVerticallyNegligible f' := by
  have hev : f =ᶠ[upperEndFilter] f' := Germ.coe_eq.mp h
  obtain ⟨H, -, hsub⟩ := upperEndFilter_basis.mem_iff.mp hev
  refine hf.congr_eventually (max H 2 + 1) fun σ t hσ ht => ?_
  have hHt : H < t := by
    have : H ≤ max H 2 := le_max_left _ _
    linarith
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ upperTail H := by
    show H < ((σ : ℂ) + (t : ℂ) * Complex.I).im
    simpa using hHt
  exact (hsub hmem).symm

/-- A germ is negligible when some representative is. -/
def IsGermNegligible (g : Germ upperEndFilter ℂ) : Prop :=
  ∃ f : ℂ → ℂ, (f : Germ upperEndFilter ℂ) = g ∧ IsVerticallyNegligible f

theorem isGermNegligible_coe {f : ℂ → ℂ} :
    IsGermNegligible (f : Germ upperEndFilter ℂ) ↔ IsVerticallyNegligible f := by
  constructor
  · rintro ⟨f', hf', hneg⟩
    exact hneg.germ_congr hf'
  · intro hf
    exact ⟨f, rfl, hf⟩

theorem IsGermNegligible.sub {g h : Germ upperEndFilter ℂ} (hg : IsGermNegligible g)
    (hh : IsGermNegligible h) : IsGermNegligible (g - h) := by
  obtain ⟨f, hf, hfneg⟩ := hg
  obtain ⟨f', hf', hf'neg⟩ := hh
  refine ⟨fun z => f z - f' z, ?_, hfneg.sub hf'neg⟩
  rw [← hf, ← hf']
  rfl

theorem IsGermNegligible.shift {g : Germ upperEndFilter ℂ} (hg : IsGermNegligible g) :
    IsGermNegligible (upperEndTranslateGerm 1 g) := by
  obtain ⟨f, hf, hfneg⟩ := hg
  refine ⟨fun z => f (z + 1), ?_, hfneg.shift⟩
  rw [← hf, upperEndTranslateGerm_coe]

/-- The germ of a rational function is the germ of the quotient of its numerator and denominator. -/
theorem ratFuncFun_eq (k : RatFunc ℂ) (z : ℂ) :
    ratFuncFun k z = k.num.eval z / k.denom.eval z := by
  rw [ratFuncFun, RatFunc.eval]
  simp [Polynomial.eval₂_eq_eval_map]

theorem hasTubePolyGrowth_ratFuncFun (k : RatFunc ℂ) : HasTubePolyGrowth (ratFuncFun k) := by
  have hgrow := hasTubePolyGrowth_ratEval k.num (RatFunc.denom_ne_zero k)
  intro M hM
  obtain ⟨m, C, T, hC, hT, hb⟩ := hgrow M hM
  refine ⟨m, C, T, hC, hT, fun σ t hσ hσM ht => ?_⟩
  rw [ratFuncFun_eq]
  exact hb σ t hσ hσM ht

theorem IsGermNegligible.mul_ratFuncGerm {g : Germ upperEndFilter ℂ} (hg : IsGermNegligible g)
    (k : RatFunc ℂ) : IsGermNegligible (ratFuncGerm k * g) := by
  obtain ⟨f, hf, hfneg⟩ := hg
  refine ⟨fun z => ratFuncFun k z * f z, ?_, hfneg.mul_polyGrowth (hasTubePolyGrowth_ratFuncFun k)⟩
  rw [← hf, ratFuncGerm_apply]
  rfl

/-- **A nonzero rational function is not a negligible germ.** -/
theorem not_isGermNegligible_ratFuncGerm {k : RatFunc ℂ} (hk : k ≠ 0) :
    ¬ IsGermNegligible (ratFuncGerm k) := by
  intro hneg
  rw [ratFuncGerm_apply] at hneg
  have hfun : IsVerticallyNegligible (ratFuncFun k) := by
    rw [← isGermNegligible_coe]
    exact hneg
  have hnum : k.num ≠ 0 := RatFunc.num_ne_zero hk
  refine not_isVerticallyNegligible_ratEval hnum (RatFunc.denom_ne_zero k) ?_
  refine hfun.congr_eventually 2 fun σ t hσ ht => ?_
  rw [ratFuncFun_eq]


/-- The germ of a polynomial regarded as a rational function. -/
theorem ratFuncGerm_algebraMap (p : Polynomial ℂ) :
    ratFuncGerm (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyGermHom p := by
  rw [ratFuncGerm_apply, polyGermHom_apply]
  refine Germ.coe_eq.mpr ?_
  filter_upwards with z
  rw [ratFuncFun_eq, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- The germ of a quotient of polynomials. -/
theorem ratFuncGerm_div {p q : Polynomial ℂ} (hq : q ≠ 0) :
    ratFuncGerm (algebraMap (Polynomial ℂ) (RatFunc ℂ) p
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
      = ((fun z : ℂ => p.eval z / q.eval z) : Germ upperEndFilter ℂ) := by
  have hunit := isUnit_polyGermHom hq
  have hqne : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 := by
    intro h0
    exact hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hmulRat : (algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) q) * algebraMap (Polynomial ℂ) (RatFunc ℂ) q
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := div_mul_cancel₀ _ hqne
  have hmulGerm := congrArg ratFuncGerm hmulRat
  rw [map_mul, ratFuncGerm_algebraMap, ratFuncGerm_algebraMap] at hmulGerm
  have hfun : (((fun z : ℂ => p.eval z / q.eval z) : Germ upperEndFilter ℂ)) * polyGermHom q
      = polyGermHom p := by
    rw [polyGermHom_apply, polyGermHom_apply]
    obtain ⟨H, hH⟩ := exists_upperTail_polyEval_ne_zero hq
    have hmem : upperTail H ∈ upperEndFilter :=
      upperEndFilter_basis.mem_of_mem (i := H) trivial
    refine Germ.coe_eq.mpr ?_
    filter_upwards [hmem] with z hz
    have hne : q.eval z ≠ 0 := hH z hz
    field_simp
  have hcancel : ratFuncGerm (algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) q) * polyGermHom q
      = ((fun z : ℂ => p.eval z / q.eval z) : Germ upperEndFilter ℂ) * polyGermHom q := by
    rw [hmulGerm, hfun]
  exact hunit.mul_right_cancel hcancel

variable {r : ℕ}

/-- The germ of a digamma jet at a real shift. -/
def jetGerm (lam : Fin r → ℝ) (p : Fin r × ℕ) : Germ upperEndFilter ℂ :=
  ((fun z : ℂ => iteratedDeriv p.2 Complex.digamma (z + ((lam p.1 : ℝ) : ℂ)))
    : Germ upperEndFilter ℂ)

/-- **The unit shift moves each jet germ by its rational increment.** -/
theorem upperEndTranslateGerm_jetGerm (lam : Fin r → ℝ) (p : Fin r × ℕ) :
    upperEndTranslateGerm 1 (jetGerm lam p)
      = jetGerm lam p
        + ratFuncGerm (familyIncrement (fun i => ((lam i : ℝ) : ℂ)) p.1 p.2) := by
  have hincr : familyIncrement (fun i => ((lam i : ℝ) : ℂ)) p.1 p.2
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C ((-1 : ℂ) ^ p.2 * ((p.2.factorial : ℕ) : ℂ)))
        / algebraMap (Polynomial ℂ) (RatFunc ℂ)
          ((Polynomial.X + Polynomial.C ((lam p.1 : ℝ) : ℂ)) ^ (p.2 + 1)) := by
    rw [familyIncrement]
    simp [map_pow, map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hqne : ((Polynomial.X + Polynomial.C ((lam p.1 : ℝ) : ℂ)) ^ (p.2 + 1)) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_add_C_ne_zero _)
  rw [hincr, ratFuncGerm_div hqne, jetGerm, upperEndTranslateGerm_coe]
  refine Germ.coe_eq.mpr ?_
  have hmem : upperTail 0 ∈ upperEndFilter :=
    upperEndFilter_basis.mem_of_mem (i := (0 : ℝ)) trivial
  filter_upwards [hmem] with z hz
  have hzim : 0 < z.im := hz
  have hpole : ∀ m : ℕ, z + ((lam p.1 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have him : (z + ((lam p.1 : ℝ) : ℂ)).im = 0 := by
      rw [hm]
      simp
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at him
    linarith
  have hrec := _root_.HTGeometry.iteratedDeriv_digamma_add_nat p.2
    (z + ((lam p.1 : ℝ) : ℂ)) hpole 1
  simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at hrec
  have hshift : z + 1 + ((lam p.1 : ℝ) : ℂ) = (z + ((lam p.1 : ℝ) : ℂ)) + 1 := by ring
  rw [hshift, hrec]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

end

end GaloisForLFunctions.HTGeometry
