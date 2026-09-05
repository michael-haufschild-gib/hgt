import GaloisForLFunctions.HTGeometry.MeroDiscRatEval
import GaloisForLFunctions.HTGeometry.RittTreeChannelNoRelation

/-!
# The Poincaré germ of an interior tree channel admits no Ritt relation

The meromorphic germ field of a disc about the origin carries the whole frame the contracting Ritt
bridge consumes: the derivation is complex-linear because it kills the constants, the contracting
scaling is a complex algebra endomorphism because it fixes them, it acts on realizations by
precomposition, it moves the coordinate by the scaling constant, and it twists the derivation by
that same constant.

Instantiating the bridge there turns the pointwise Poincaré identity
`Φ(z)·D(Φ(μz)) = N(Φ(μz))` on the disc, together with a first-order relation
`(Φ′)^r = z^j A(Φ)`, into a rational cocycle for the channel map — which an interior channel does
not have.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Set
open scoped Differential

noncomputable section

/-- **The scaling acts by precomposition on realizations.** -/
theorem scaleMero_analyticMeroElement {U : Set ℂ} {mu : ℂ} (hmu : mu ≠ 0)
    (hmaps : Set.MapsTo (scaleMap mu) U U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) :
    letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
    scaleMero hmu hmaps hUo hUc hUne (analyticMeroElement f hf)
      = analyticMeroElement (fun w => f (mu * w))
        (fun w hw => (hf (mu * w) (hmaps hw)).comp ((analyticOnNhd_scaleMap mu U) w hw)) := by
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  rw [analyticMeroElement, analyticMeroElement, scaleMero, Bottcher.precompMeroMap_algebraMap]
  congr 1

theorem ratFuncEval_congr_eq {E : Type*} [Field E] [Algebra ℂ E] {y y' : E}
    (hy : Transcendental ℂ y) (hy' : Transcendental ℂ y') (h : y = y') (Q : RatFunc ℂ) :
    ratFuncEval y hy Q = ratFuncEval y' hy' Q := by
  subst h
  rfl

/-- The coordinate germ of a disc is nonzero. -/
theorem discCoordMero_ne_zero {ρ : ℝ} (hρ : 0 < ρ) :
    letI := Bottcher.isDomain_analyticSubring (Metric.ball (0 : ℂ) ρ) Metric.isOpen_ball
      (convex_ball (0 : ℂ) ρ).isPreconnected (Metric.nonempty_ball.mpr hρ)
    discCoordMero (Metric.ball (0 : ℂ) ρ) ≠ 0 := by
  letI := Bottcher.isDomain_analyticSubring (Metric.ball (0 : ℂ) ρ) Metric.isOpen_ball
    (convex_ball (0 : ℂ) ρ).isPreconnected (Metric.nonempty_ball.mpr hρ)
  rw [discCoordMero]
  intro h
  have hall := (analyticMeroElement_eq_zero_iff (U := Metric.ball (0 : ℂ) ρ)
    (fun _ _ => analyticAt_id)).mp h
  have hmem : (((ρ / 2 : ℝ) : ℂ)) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hzero := hall _ hmem
  simp only [id_eq] at hzero
  have hr2 : (ρ / 2 : ℝ) = 0 := by exact_mod_cast hzero
  linarith

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The Poincaré germ of an interior tree channel satisfies no Ritt relation.** -/
theorem no_ritt_relation_poincare_tree_interior {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    {ρ : ℝ} (hρ : 0 < ρ) {mu : ℂ} (hmu0 : mu ≠ 0) (hmu : ‖mu‖ ≤ 1)
    {Φ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ (Metric.ball (0 : ℂ) ρ))
    (hΦnc : ¬ ∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) ρ, Φ z = c)
    (hΦμnc : ¬ ∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) ρ, Φ (mu * z) = c)
    {hR : ¬ ∃ c : ℂ, treeRG p (u : ℂ) (v : ℂ) = RatFunc.C c}
    (hden : ¬ ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        (treeRG p (u : ℂ) (v : ℂ)).denom.eval (Φ (mu * z)) = 0)
    (hpoin : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        Φ z * (treeRG p (u : ℂ) (v : ℂ)).denom.eval (Φ (mu * z))
          = (treeRG p (u : ℂ) (v : ℂ)).num.eval (Φ (mu * z)))
    {A : RatFunc ℂ} (hA : A ≠ 0) {r j : ℤ} (hr : r ≠ 0)
    (hritt :
      letI := Bottcher.isDomain_analyticSubring (Metric.ball (0 : ℂ) ρ) Metric.isOpen_ball
        (convex_ball (0 : ℂ) ρ).isPreconnected (Metric.nonempty_ball.mpr hρ)
      letI := meroComplexAlgebra (Metric.ball (0 : ℂ) ρ)
      letI := meroFieldDifferential Metric.isOpen_ball
        (convex_ball (0 : ℂ) ρ).isPreconnected (Metric.nonempty_ball.mpr hρ)
      ((analyticMeroElement Φ hΦ)′) ^ r
        = (discCoordMero (Metric.ball (0 : ℂ) ρ)) ^ j
          * ratFuncEval (analyticMeroElement Φ hΦ)
            (transcendental_analyticMeroElement_of_nonconstant_on Metric.isOpen_ball
              (convex_ball (0 : ℂ) ρ).isPreconnected (Metric.nonempty_ball.mpr hρ) hΦ hΦnc) A) :
    False := by
  have hUo : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hUc : IsPreconnected (Metric.ball (0 : ℂ) ρ) := (convex_ball (0 : ℂ) ρ).isPreconnected
  have hUne : (Metric.ball (0 : ℂ) ρ).Nonempty := Metric.nonempty_ball.mpr hρ
  letI := Bottcher.isDomain_analyticSubring (Metric.ball (0 : ℂ) ρ) hUo hUc hUne
  letI : Algebra ℤ (Bottcher.analyticSubring (Metric.ball (0 : ℂ) ρ)) := Ring.toIntAlgebra _
  letI : Algebra ℤ (meroField (Metric.ball (0 : ℂ) ρ)) := Ring.toIntAlgebra _
  letI := meroComplexAlgebra (Metric.ball (0 : ℂ) ρ)
  letI := meroFieldDifferential hUo hUc hUne
  have hmaps : Set.MapsTo (scaleMap mu) (Metric.ball (0 : ℂ) ρ) (Metric.ball (0 : ℂ) ρ) :=
    mapsTo_scaleMap hmu ρ
  -- the complex derivation
  let dC : Derivation ℂ (meroField (Metric.ball (0 : ℂ) ρ)) (meroField (Metric.ball (0 : ℂ) ρ)) :=
    { toLinearMap :=
        { toAddHom := { toFun := fun x => Differential.deriv x,
                        map_add' := fun x y => map_add _ x y },
          map_smul' := fun c x => by
            show Differential.deriv (c • x) = c • Differential.deriv x
            rw [Algebra.smul_def c x]
            have hleib := Differential.deriv.leibniz
              (algebraMap ℂ (meroField (Metric.ball (0 : ℂ) ρ)) c) x
            simp only [smul_eq_mul] at hleib
            rw [hleib, meroDeriv_algebraMap_complex hUo hUc hUne c, mul_zero, add_zero,
              Algebra.smul_def] },
      map_one_eq_zero' := Derivation.map_one_eq_zero _,
      leibniz' := fun a b => Differential.deriv.leibniz a b }
  -- the scaling as a complex algebra endomorphism
  let TC : meroField (Metric.ball (0 : ℂ) ρ) →ₐ[ℂ] meroField (Metric.ball (0 : ℂ) ρ) :=
    AlgHom.mk' (scaleMero hmu0 hmaps hUo hUc hUne) (fun c x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul,
        scaleMero_algebraMap_complex hmu0 hmaps hUo hUc hUne c])
  -- the analytic data
  have hΦμ : AnalyticOnNhd ℂ (fun w => Φ (mu * w)) (Metric.ball (0 : ℂ) ρ) :=
    fun w hw => (hΦ (mu * w) (hmaps hw)).comp
      ((analyticOnNhd_scaleMap mu (Metric.ball (0 : ℂ) ρ)) w hw)
  have hy : Transcendental ℂ (analyticMeroElement Φ hΦ) :=
    transcendental_analyticMeroElement_of_nonconstant_on hUo hUc hUne hΦ hΦnc
  have hTyval : TC (analyticMeroElement Φ hΦ) = analyticMeroElement (fun w => Φ (mu * w)) hΦμ :=
    scaleMero_analyticMeroElement hmu0 hmaps hUo hUc hUne hΦ
  have hTy : Transcendental ℂ (TC (analyticMeroElement Φ hΦ)) := by
    rw [hTyval]
    exact transcendental_analyticMeroElement_of_nonconstant_on hUo hUc hUne hΦμ hΦμnc
  have hPoin : analyticMeroElement Φ hΦ
      = ratFuncEval (TC (analyticMeroElement Φ hΦ)) hTy (treeRG p (u : ℂ) (v : ℂ)) := by
    have h := analyticMeroElement_eq_ratFuncEval hΦ hΦμ
      (transcendental_analyticMeroElement_of_nonconstant_on hUo hUc hUne hΦμ hΦμnc) hden hpoin
    exact h.trans (ratFuncEval_congr_eq _ _ hTyval.symm _)
  refine no_ritt_relation_treeRG_interior_contracting hp hv huv hu dC TC hmu0
    (discCoordMero_ne_zero hρ) ?_ ?_ hy hTy (hR := hR) hPoin hA hr hritt
  · show scaleMero hmu0 hmaps hUo hUc hUne (discCoordMero (Metric.ball (0 : ℂ) ρ))
      = algebraMap ℂ (meroField (Metric.ball (0 : ℂ) ρ)) mu * discCoordMero (Metric.ball (0 : ℂ) ρ)
    exact scaleMero_discCoordMero hmu0 hmaps hUo hUc hUne
  · intro x
    show Differential.deriv (scaleMero hmu0 hmaps hUo hUc hUne x)
      = algebraMap ℂ (meroField (Metric.ball (0 : ℂ) ρ)) mu
        * scaleMero hmu0 hmaps hUo hUc hUne (Differential.deriv x)
    rw [scaleMero_deriv hmu0 hmaps hUo hUc hUne x, meroComplexAlgebra_algebraMap]

end

end GaloisForLFunctions.HTGeometry
