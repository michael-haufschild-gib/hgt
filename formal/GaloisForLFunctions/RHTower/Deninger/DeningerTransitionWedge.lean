import GaloisForLFunctions.RHTower.Deninger.DeningerHolomorphicDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerDlogTransition

/-!
# The transition maps act on the generators by the minors of the exponent matrix

A transition map of character stages is a monomial map, and the exponential covering intertwines it
with the linear map of the exponent matrix.  So the pullback of an exterior product of logarithmic
differentials is the constant stage form obtained by composing the determinant form with that linear
map, and expanding it in the basis of the determinant forms gives the minors of the exponent matrix.
This is the functoriality of the comparison `Λ^k(L ⊗ ℂ) ≅ H^k` in the lattice.

* `deningerMatrixCLM` : the linear map of an exponent matrix on the covering spaces.
* `deningerExpMap_matrixCLM` : the covering intertwines the transition with the linear map.
* `deningerMonomialPullback_dlogWedge` : the pullback of a generator is a constant stage form.
* `deningerMonomialPullback_dlogWedge_sum` : its expansion in the generators, by the minors.
-/

namespace RHTower

open Complex

section MatrixCLM

variable {r s : ℕ}

/-- **The linear map of an exponent matrix** on the covering spaces. -/
noncomputable def deningerMatrixCLM (m : Fin r → Fin s → ℤ) : (Fin s → ℂ) →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, (m i j : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j

theorem deningerMatrixCLM_apply (m : Fin r → Fin s → ℤ) (w : Fin s → ℂ) (i : Fin r) :
    deningerMatrixCLM m w i = ∑ j, (m i j : ℂ) * w j := by
  show (∑ j, (m i j : ℂ) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j) w = _
  rw [sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem deningerMatrixCLM_single (m : Fin r → Fin s → ℤ) (j : Fin s) (i : Fin r) :
    deningerMatrixCLM m (Pi.single j (1 : ℂ)) i = (m i j : ℂ) := by
  classical
  rw [deningerMatrixCLM_apply]
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    show (m i l : ℂ) * (Pi.single j (1 : ℂ) : Fin s → ℂ) l =
      if l = j then (m i l : ℂ) else 0 by
        rw [Pi.single_apply]
        by_cases h : l = j
        · rw [if_pos h, if_pos h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero]]
  rw [Finset.sum_ite_eq' Finset.univ j fun l => (m i l : ℂ)]
  rw [if_pos (Finset.mem_univ j)]

/-- **The exponential covering intertwines a transition map with the linear map of its exponent
matrix.** -/
theorem deningerExpMap_matrixCLM (m : Fin r → Fin s → ℤ) (w : Fin s → ℂ) :
    deningerExpMap r (deningerMatrixCLM m w) = deningerMonomialMap m (deningerExpMap s w) := by
  funext i
  show Complex.exp (deningerMatrixCLM m w i) = ∏ j, (Complex.exp (w j)) ^ (m i j)
  rw [deningerMatrixCLM_apply, Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => Complex.exp_int_mul _ _

/-- **The chain rule for the transition map along the covering.** -/
theorem deningerMonomialDeriv_comp_expDeriv (m : Fin r → Fin s → ℤ) (w : Fin s → ℂ) :
    (fderiv ℂ (deningerMonomialMap m) (deningerExpMap s w)).comp (deningerExpDeriv w) =
      (deningerExpDeriv (deningerMatrixCLM m w)).comp (deningerMatrixCLM m) := by
  have hz : deningerExpMap s w ∈ deningerStageTorus s := deningerExpMap_mem w
  rw [(deningerMonomialMap_hasFDerivAt m hz).fderiv]
  refine ContinuousLinearMap.ext fun u => ?_
  funext i
  have hcoord : Complex.exp (deningerMatrixCLM m w i) =
      ∏ l, (Complex.exp (w l)) ^ (m i l) := congrFun (deningerExpMap_matrixCLM m w) i
  show deningerMonomialRowDeriv m (deningerExpMap s w) i (deningerExpDeriv w u) =
    Complex.exp (deningerMatrixCLM m w i) * deningerMatrixCLM m u i
  rw [deningerMonomialRowDeriv_apply, hcoord, deningerMatrixCLM_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (∏ l, (deningerExpMap s w l) ^ (m i l)) * ((m i j : ℂ) * (deningerExpMap s w j)⁻¹) *
      (deningerExpDeriv w u j) = _
  show (∏ l, (Complex.exp (w l)) ^ (m i l)) * ((m i j : ℂ) * (Complex.exp (w j))⁻¹) *
      (Complex.exp (w j) * u j) = (∏ l, (Complex.exp (w l)) ^ (m i l)) * ((m i j : ℂ) * u j)
  field_simp

/-- **Composing transitions multiplies the matrices**, so the linear models form a functor. -/
theorem deningerMatrixCLM_comp {t : ℕ} (m : Fin r → Fin s → ℤ) (n : Fin s → Fin t → ℤ) :
    deningerMatrixCLM (fun i k => ∑ j, m i j * n j k) =
      (deningerMatrixCLM m).comp (deningerMatrixCLM n) := by
  refine ContinuousLinearMap.ext fun w => ?_
  funext i
  show deningerMatrixCLM (fun i k => ∑ j, m i j * n j k) w i =
    deningerMatrixCLM m (deningerMatrixCLM n w) i
  rw [deningerMatrixCLM_apply, deningerMatrixCLM_apply]
  have hleft : ∀ k : Fin t, ((∑ j, m i j * n j k : ℤ) : ℂ) * w k =
      ∑ j, ((m i j : ℂ) * (n j k : ℂ)) * w k := by
    intro k
    push_cast
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun k _ => hleft k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerMatrixCLM_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The identity transition is the identity map.** -/
theorem deningerMatrixCLM_id :
    deningerMatrixCLM (fun i j : Fin r => if i = j then (1 : ℤ) else 0) =
      ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  refine ContinuousLinearMap.ext fun w => ?_
  funext i
  rw [deningerMatrixCLM_apply]
  show (∑ j, ((if i = j then (1 : ℤ) else 0 : ℤ) : ℂ) * w j) = w i
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    push_cast
    rw [one_mul]
  · intro j _ hj
    rw [if_neg fun h => hj h.symm]
    push_cast
    rw [zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end MatrixCLM

end RHTower

namespace RHTower

open Complex

section TransitionWedge

variable {r s k : ℕ}

/-- Composing an alternating form with two linear maps in turn is composing with their
composite. -/
theorem deningerCompCLM_compCLM {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (A : G [⋀^Fin n]→L[ℂ] ℂ) (L : F →L[ℂ] G) (L' : E →L[ℂ] F) :
    (A.compContinuousLinearMap L).compContinuousLinearMap L' =
      A.compContinuousLinearMap (L.comp L') := by
  ext v
  rfl

/-- **The pullback of an exterior product of logarithmic differentials along a transition map is
the constant stage form of the determinant form composed with the exponent matrix.** -/
theorem deningerMonomialPullback_dlogWedge (m : Fin r → Fin s → ℤ) (σ : Fin k → Fin r)
    {z : Fin s → ℂ} (hz : z ∈ deningerStageTorus s) :
    deningerStagePullback (deningerMonomialMap m) (deningerDlogWedge σ) z =
      deningerConstantStageForm
        ((deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m)) z := by
  refine deningerExpPullback_injective (fun w => ?_) hz
  rw [show deningerPullbackForm (deningerExpMap s)
      (deningerConstantStageForm
        ((deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m))) w =
      (deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m) from
    deningerConstantStageForm_pullback _ w]
  show ((deningerDlogWedge σ (deningerMonomialMap m (deningerExpMap s w))).compContinuousLinearMap
      (fderiv ℂ (deningerMonomialMap m) (deningerExpMap s w))).compContinuousLinearMap
      (fderiv ℂ (deningerExpMap s) w) =
    (deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m)
  rw [(deningerExpMap_hasFDerivAt w).fderiv, deningerCompCLM_compCLM,
    deningerMonomialDeriv_comp_expDeriv m w, ← deningerExpMap_matrixCLM m w,
    ← deningerCompCLM_compCLM]
  have hgen : ContinuousAlternatingMap.compContinuousLinearMap
      (deningerDlogWedge σ (deningerExpMap r (deningerMatrixCLM m w)))
      (deningerExpDeriv (deningerMatrixCLM m w)) = deningerDetForm σ := by
    have h := deningerExpPullback_dlogWedge σ (deningerMatrixCLM m w)
    rw [deningerExpPullbackForm, deningerPullbackForm,
      (deningerExpMap_hasFDerivAt (deningerMatrixCLM m w)).fderiv] at h
    exact h
  rw [hgen]

/-- **The coefficient of a generator in the pullback is the corresponding minor of the exponent
matrix.** -/
theorem deningerSubsetCoeff_detForm_comp (m : Fin r → Fin s → ℤ) (σ : Fin k → Fin r)
    (S : Finset (Fin s)) (hS : S.card = k) :
    deningerSubsetCoeff ((deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m)) S =
      Matrix.det (Matrix.of fun a b => ((m (σ a) (S.orderEmbOfFin hS b) : ℤ) : ℂ)) := by
  rw [deningerSubsetCoeff, dif_pos hS]
  show deningerDetForm σ
      (fun a => deningerMatrixCLM m (Pi.single (S.orderEmbOfFin hS a) (1 : ℂ))) = _
  rw [deningerDetForm_apply]
  have hmat : (Matrix.of fun a b =>
        deningerMatrixCLM m (Pi.single (S.orderEmbOfFin hS a) (1 : ℂ)) (σ b)) =
      (Matrix.of fun a b => ((m (σ a) (S.orderEmbOfFin hS b) : ℤ) : ℂ)).transpose := by
    ext a b
    show deningerMatrixCLM m (Pi.single (S.orderEmbOfFin hS a) (1 : ℂ)) (σ b) =
      ((m (σ b) (S.orderEmbOfFin hS a) : ℤ) : ℂ)
    rw [deningerMatrixCLM_single]
  rw [hmat, Matrix.det_transpose]

/-- **The transition maps act on the generators by the minors of the exponent matrix.**  This is the
functoriality in the lattice of the comparison between the exterior powers and the cohomology of a
character stage. -/
theorem deningerMonomialPullback_dlogWedge_sum (m : Fin r → Fin s → ℤ) (σ : Fin k → Fin r)
    {z : Fin s → ℂ} (hz : z ∈ deningerStageTorus s) :
    deningerStagePullback (deningerMonomialMap m) (deningerDlogWedge σ) z =
      ∑ S : Finset (Fin s),
        deningerSubsetCoeff ((deningerDetForm σ).compContinuousLinearMap (deningerMatrixCLM m)) S •
          deningerSubsetWedge k S z := by
  rw [deningerMonomialPullback_dlogWedge m σ hz, deningerConstantStageForm_eq_dlog_sum]

end TransitionWedge

end RHTower
