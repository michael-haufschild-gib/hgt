import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryNormOrientation

/-!
# Realness of the source slope and its interior quadratic evaluation

* `sourcePolyConj_slope`: the full source slope polynomial is fixed by coefficientwise complex
  conjugation, i.e. all its coefficients are real.
* `interiorHom v k e`: the evaluation of source polynomials in the boundary quadratic algebra
  `BoundaryAlg v k` sending `J ↦ e ω`; `e = 1` is `boundaryHom`, and composing with the evaluation
  at a boundary root `z` gives the ordinary evaluation at `(v, k, e z)`.
* For real `v, k, e` the image of a real polynomial has real components
  (`interiorHom_re_conj`, `interiorHom_im_conj`), and the components depend continuously on `e`
  (`continuous_interiorHom_re`, `continuous_interiorHom_im`).
-/

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare ComplexConjugate

/-! ### Coefficientwise conjugation of source polynomials -/

/-- Coefficientwise complex conjugation of source polynomials. -/
def sourcePolyConj : Poly →+* Poly := MvPolynomial.map (starRingEnd ℂ)

theorem sourcePolyConj_flow (f : Coord → Poly) (hf : ∀ i, sourcePolyConj (f i) = f i)
    (P : Poly) : sourcePolyConj (flow f P) = flow f (sourcePolyConj P) := by
  unfold flow
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hf i, sourcePolyConj, pderiv_map]

theorem sourcePolyConj_squareField (i : Coord) :
    sourcePolyConj (squareField i) = squareField i := by
  cases i <;> simp [squareField, sourcePolyConj]

theorem sourcePolyConj_moment2 : sourcePolyConj moment2 = moment2 := by
  simp only [sourcePolyConj, moment2, moment2Part0, moment2Part1, map_add, map_mul, map_pow,
    map_X, map_ofNat, map_neg, map_zero]

theorem sourcePolyConj_moment4 : sourcePolyConj moment4 = moment4 := by
  simp only [sourcePolyConj, moment4, moment4Part0, moment4Part1, moment4Part2, moment4Part3,
    map_add, map_mul, map_pow, map_X, map_ofNat, map_neg, map_zero]

theorem sourcePolyConj_moment6 : sourcePolyConj moment6 = moment6 := by
  simp only [sourcePolyConj, moment6, moment6Part0, moment6Part1, moment6Part2, moment6Part3,
    moment6Part4, moment6Part5, moment6Part6, moment6Part7,
    map_add, map_mul, map_pow, map_X, map_ofNat, map_neg, map_zero]

theorem sourcePolyConj_moment8 : sourcePolyConj moment8 = moment8 := by
  simp only [sourcePolyConj, moment8, moment8Part0, moment8Part1, moment8Part2, moment8Part3,
    moment8Part4, moment8Part5, moment8Part6, moment8Part7, moment8Part8, moment8Part9,
    moment8Part10, moment8Part11, moment8Part12, moment8Part13,
    map_add, map_mul, map_pow, map_X, map_ofNat, map_neg, map_zero]

theorem sourcePolyConj_moment10 : sourcePolyConj moment10 = moment10 := by
  simp only [sourcePolyConj, moment10, moment10Part0, moment10Part1, moment10Part2,
    moment10Part3, moment10Part4, moment10Part5, moment10Part6, moment10Part7, moment10Part8,
    moment10Part9, moment10Part10, moment10Part11, moment10Part12, moment10Part13,
    moment10Part14, moment10Part15, moment10Part16, moment10Part17, moment10Part18,
    moment10Part19, moment10Part20, moment10Part21, moment10Part22,
    map_add, map_mul, map_pow, map_X, map_ofNat, map_neg, map_zero]

theorem sourcePolyConj_minor : sourcePolyConj minor = minor := by
  simp only [minor, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    sourcePolyConj_moment2, sourcePolyConj_moment4, sourcePolyConj_moment6,
    sourcePolyConj_moment8, sourcePolyConj_moment10]

theorem sourcePolyConj_seed : sourcePolyConj seed = seed := by
  simp [seed, sourcePolyConj]

/-- The full source slope has real coefficients. -/
theorem sourcePolyConj_slope :
    sourcePolyConj ThetaRatioSquare.slope = ThetaRatioSquare.slope := by
  unfold ThetaRatioSquare.slope squareLie
  rw [map_sub, map_mul, map_mul, map_mul, sourcePolyConj_flow _ sourcePolyConj_squareField,
    sourcePolyConj_flow _ sourcePolyConj_squareField, sourcePolyConj_minor, sourcePolyConj_seed,
    map_ofNat]

/-! ### Conjugation on the boundary quadratic algebra -/

/-- Componentwise conjugation, a ring endomorphism when both structure constants are real. -/
def boundaryAlgConj {a b : ℂ} (ha : conj a = a) (hb : conj b = b) :
    QuadraticAlgebra ℂ a b →+* QuadraticAlgebra ℂ a b where
  toFun z := ⟨conj z.re, conj z.im⟩
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    ext
    · simp only [QuadraticAlgebra.re_mul, map_add, map_mul, ha]
    · simp only [QuadraticAlgebra.im_mul, map_add, map_mul, hb]
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

theorem boundaryAlgConj_re {a b : ℂ} (ha : conj a = a) (hb : conj b = b)
    (z : QuadraticAlgebra ℂ a b) : (boundaryAlgConj ha hb z).re = conj z.re := rfl

theorem boundaryAlgConj_im {a b : ℂ} (ha : conj a = a) (hb : conj b = b)
    (z : QuadraticAlgebra ℂ a b) : (boundaryAlgConj ha hb z).im = conj z.im := rfl

theorem boundaryA_conj_ofReal (v k : ℝ) : conj (boundaryA (v:ℂ) (k:ℂ)) = boundaryA (v:ℂ) (k:ℂ) := by
  unfold boundaryA boundaryMass
  simp [map_div₀, map_sub, map_mul, map_ofNat]

theorem boundaryB_conj_ofReal (k : ℝ) : conj (boundaryB (k:ℂ)) = boundaryB (k:ℂ) := by
  unfold boundaryB
  simp [map_div₀, map_sub, map_ofNat]

/-! ### Interior evaluation `J ↦ e ω` -/

/-- The source coordinates sent to `v`, `k` and `e ω`. -/
def interiorCoord (v k e : ℂ) : Coord → BoundaryAlg v k
  | .U => algebraMap ℂ (BoundaryAlg v k) v
  | .K => algebraMap ℂ (BoundaryAlg v k) k
  | .J => algebraMap ℂ (BoundaryAlg v k) e * QuadraticAlgebra.omega

/-- Evaluation of a source polynomial in the boundary quadratic algebra with `J ↦ e ω`. -/
def interiorHom (v k e : ℂ) : Poly →+* BoundaryAlg v k :=
  eval₂Hom (algebraMap ℂ (BoundaryAlg v k)) (interiorCoord v k e)

theorem interiorHom_one (v k : ℂ) : interiorHom v k 1 = boundaryHom v k := by
  unfold interiorHom boundaryHom
  congr 1
  funext i
  cases i <;> simp [interiorCoord, boundaryCoord]

/-- Composing with the evaluation at a boundary root `z` evaluates at `(v, k, e z)`. -/
theorem boundaryEval_interiorHom (v k e z : ℂ) (hz : z^2=boundaryA v k+boundaryB k*z)
    (P : Poly) :
    (interiorHom v k e P).re+z*(interiorHom v k e P).im=eval (basePoint v k (e*z)) P := by
  change boundaryEval v k z hz (interiorHom v k e P)=eval (basePoint v k (e*z)) P
  induction P using MvPolynomial.induction_on with
  | C c => simp [interiorHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    congr 1
    cases i <;> simp [interiorHom, interiorCoord, boundaryEval, basePoint, QuadraticAlgebra.omega]
    ring

/-- For real `v, k, e`, conjugation commutes with interior evaluation. -/
theorem boundaryAlgConj_interiorHom (v k e : ℝ) (P : Poly) :
    boundaryAlgConj (boundaryA_conj_ofReal v k) (boundaryB_conj_ofReal k)
        (interiorHom (v:ℂ) (k:ℂ) (e:ℂ) P) =
      interiorHom (v:ℂ) (k:ℂ) (e:ℂ) (sourcePolyConj P) := by
  have hext : (boundaryAlgConj (boundaryA_conj_ofReal v k) (boundaryB_conj_ofReal k)).comp
      (interiorHom (v:ℂ) (k:ℂ) (e:ℂ)) =
      (interiorHom (v:ℂ) (k:ℂ) (e:ℂ)).comp sourcePolyConj := by
    apply MvPolynomial.ringHom_ext
    · intro c
      ext <;> simp [interiorHom, sourcePolyConj, boundaryAlgConj_re, boundaryAlgConj_im]
    · intro i
      cases i <;> ext <;>
        simp [interiorHom, interiorCoord, sourcePolyConj, boundaryAlgConj_re,
          boundaryAlgConj_im, QuadraticAlgebra.omega]
  exact congrArg (fun f => f P) hext

/-- Interior evaluation of the source slope at real data has real components. -/
theorem interiorHom_slope_conj (v k e : ℝ) :
    conj (interiorHom (v:ℂ) (k:ℂ) (e:ℂ) ThetaRatioSquare.slope).re=(interiorHom (v:ℂ) (k:ℂ) (e:ℂ) ThetaRatioSquare.slope).re ∧
      conj (interiorHom (v:ℂ) (k:ℂ) (e:ℂ) ThetaRatioSquare.slope).im=(interiorHom (v:ℂ) (k:ℂ) (e:ℂ) ThetaRatioSquare.slope).im := by
  have h := boundaryAlgConj_interiorHom v k e ThetaRatioSquare.slope
  rw [sourcePolyConj_slope] at h
  exact ⟨congrArg QuadraticAlgebra.re h, congrArg QuadraticAlgebra.im h⟩

/-- The components of an interior evaluation are continuous in a real parameter `e`. -/
theorem continuous_interiorHom (v k : ℂ) (P : Poly) :
    Continuous (fun e : ℝ => (interiorHom v k (e:ℂ) P).re) ∧
      Continuous (fun e : ℝ => (interiorHom v k (e:ℂ) P).im) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [interiorHom, coe_eval₂Hom, eval₂_C, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im]
    exact ⟨continuous_const, continuous_const⟩
  | add p q hp hq =>
    simp only [map_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    exact ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  | mul_X p i hp =>
    have hc : Continuous (fun e : ℝ => (interiorHom v k (e:ℂ) (X i)).re) ∧
        Continuous (fun e : ℝ => (interiorHom v k (e:ℂ) (X i)).im) := by
      cases i <;>
        simp only [interiorHom, coe_eval₂Hom, eval₂_X, interiorCoord,
          QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
          QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.omega_re,
          QuadraticAlgebra.omega_im] <;>
        exact ⟨by fun_prop, by fun_prop⟩
    simp only [map_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    exact ⟨(hp.1.mul hc.1).add ((continuous_const.mul hp.2).mul hc.2),
      ((hp.1.mul hc.2).add (hp.2.mul hc.1)).add ((continuous_const.mul hp.2).mul hc.2)⟩

end
end HTGeometry.ThetaRatioInfinity
