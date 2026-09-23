import GaloisForLFunctions.HTGeometry.TorusCharacterMean

/-!
# Trigonometric polynomials on a product torus

A finitely supported family of coefficients gives a finite combination of
characters.  Its Fourier coefficients are the coefficients themselves, by the
delta law for characters.

Every continuous function on the product torus is a uniform limit of such
combinations: the characters span a star subalgebra separating points, so the
Stone--Weierstrass theorem applies.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance isProbabilityMeasureCircleTorusTrig : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance isAddHaarMeasureCircleTorusTrig : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Integrability on the product torus -/

omit [DecidableEq d] in
theorem integrable_torus_of_continuous {g : UnitAddTorus d → ℂ} (hg : Continuous g) :
    Integrable g (volume : Measure (UnitAddTorus d)) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

omit [DecidableEq d] in
theorem mFourierCoeff_sub_torusTrigPolynomial {g h : UnitAddTorus d → ℂ} (hg : Continuous g)
    (hh : Continuous h) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => g x - h x) n =
      UnitAddTorus.mFourierCoeff g n - UnitAddTorus.mFourierCoeff h n := by
  have hchar : Continuous fun x : UnitAddTorus d => UnitAddTorus.mFourier (-n) x :=
    (UnitAddTorus.mFourier (-n)).continuous
  have hsplit : (fun x : UnitAddTorus d =>
      UnitAddTorus.mFourier (-n) x • (g x - h x))
      = fun x => UnitAddTorus.mFourier (-n) x • g x
        - UnitAddTorus.mFourier (-n) x • h x := by
    funext x
    rw [smul_sub]
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.mFourierCoeff, hsplit]
  exact integral_sub (integrable_torus_of_continuous (hchar.smul hg))
    (integrable_torus_of_continuous (hchar.smul hh))

/-! ### Trigonometric polynomials -/

/-- The trigonometric polynomial with finitely supported coefficient family. -/
def torusTrigPoly (c : (d → ℤ) →₀ ℂ) : UnitAddTorus d → ℂ :=
  fun x => ∑ m ∈ c.support, c m * UnitAddTorus.mFourier m x

omit [DecidableEq d] in
theorem continuous_torusTrigPoly (c : (d → ℤ) →₀ ℂ) :
    Continuous (torusTrigPoly c) :=
  continuous_finsetSum _ fun m _ =>
    continuous_const.mul (UnitAddTorus.mFourier m).continuous

/-- **The Fourier coefficients of a trigonometric polynomial are its
coefficients.** -/
theorem mFourierCoeff_torusTrigPoly (c : (d → ℤ) →₀ ℂ) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusTrigPoly c) n = c n := by
  classical
  have hsplit : (fun x : UnitAddTorus d =>
      UnitAddTorus.mFourier (-n) x • torusTrigPoly c x)
      = fun x => ∑ m ∈ c.support,
        c m • (UnitAddTorus.mFourier (-n) x • UnitAddTorus.mFourier m x) := by
    funext x
    rw [torusTrigPoly, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [UnitAddTorus.mFourierCoeff, hsplit]
  rw [integral_finsetSum]
  · have hterm : ∀ m ∈ c.support,
        (∫ x : UnitAddTorus d,
          c m • (UnitAddTorus.mFourier (-n) x • UnitAddTorus.mFourier m x))
          = c m * (if n = m then 1 else 0) := by
      intro m _
      rw [integral_smul, smul_eq_mul, ← UnitAddTorus.mFourierCoeff,
        mFourierCoeff_mFourier]
    rw [Finset.sum_congr rfl hterm]
    by_cases hn : n ∈ c.support
    · have hone : ∀ m ∈ c.support, c m * (if n = m then 1 else 0)
          = if m = n then c n else 0 := by
        intro m _
        by_cases hm : n = m
        · rw [if_pos hm, mul_one, if_pos hm.symm, hm]
        · rw [if_neg hm, mul_zero, if_neg fun h => hm h.symm]
      rw [Finset.sum_congr rfl hone, Finset.sum_ite_eq' c.support n
        (fun _ => c n), if_pos hn]
    · have hzero : ∀ m ∈ c.support, c m * (if n = m then 1 else 0) = 0 := by
        intro m hm
        by_cases hnm : n = m
        · exact absurd (hnm ▸ hm) hn
        · rw [if_neg hnm, mul_zero]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      exact (Finsupp.notMem_support_iff.1 hn).symm
  · intro m _
    exact integrable_torus_of_continuous (by fun_prop)

/-! ### Uniform approximation -/

omit [DecidableEq d] in
/-- **Stone--Weierstrass on the product torus.**  Every continuous function is
uniformly approximated by trigonometric polynomials. -/
theorem exists_torusTrigPoly_approx (G : C(UnitAddTorus d, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : (d → ℤ) →₀ ℂ, ∀ x, ‖G x - torusTrigPoly c x‖ ≤ ε := by
  classical
  have hmem : G ∈ closure
      ((Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d)))) : Set _) := by
    have htop := UnitAddTorus.span_mFourier_closure_eq_top (d := d)
    have hin : G ∈ ((Submodule.span ℂ
        (Set.range (UnitAddTorus.mFourier (d := d)))).topologicalClosure :
          Set C(UnitAddTorus d, ℂ)) := by
      rw [htop]
      trivial
    rwa [Submodule.topologicalClosure_coe] at hin
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hP
  refine ⟨c, fun x => ?_⟩
  have hPx : P x = torusTrigPoly c x := by
    rw [← hc, Finsupp.sum]
    show (∑ m ∈ c.support, c m • UnitAddTorus.mFourier m) x = _
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun m _ => rfl
  have hnorm : ‖G x - P x‖ ≤ ‖G - P‖ := by
    have := ContinuousMap.norm_coe_le_norm (G - P) x
    rwa [ContinuousMap.sub_apply] at this
  rw [← hPx]
  refine le_trans hnorm ?_
  rw [← dist_eq_norm]
  exact le_of_lt hdist

end

end GaloisForLFunctions.HTGeometry
