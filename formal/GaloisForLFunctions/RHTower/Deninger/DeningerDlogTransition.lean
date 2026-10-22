import GaloisForLFunctions.RHTower.Deninger.DeningerStageTransition
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# The transition law of the logarithmic differentials

Along a monomial transition map the logarithmic differential of a coarse coordinate pulls back to
the integral combination of the fine logarithmic differentials given by the exponent matrix:
`d log (∏ w_j^{m_j}) = ∑ m_j · d log w_j`.  So the generators of the cohomology of a character stage
transform exactly like the lattice of exponents, which is what rationalizes the lattice in the
colimit over finite-index inclusions.

* `deningerMonomialRowDeriv` : the derivative of a monomial coordinate of a transition map.
* `deningerMonomialCoord_hasFDerivAt`, `deningerMonomialMap_hasFDerivAt` : it is the derivative.
* `deningerDlogForm_pullback` : the transition law `π^* d log z_i = ∑_j m_{ij} d log w_j`.
-/

namespace RHTower

section MonomialDerivative

variable {r s : ℕ}

/-- The derivative of a monomial coordinate of a transition map: the monomial times the combination
of coordinate differentials given by its row of exponents. -/
noncomputable def deningerMonomialRowDeriv (m : Fin r → Fin s → ℤ) (z : Fin s → ℂ) (i : Fin r) :
    (Fin s → ℂ) →L[ℂ] ℂ :=
  ∑ j, ((∏ l, (z l) ^ (m i l)) * ((m i j : ℂ) * (z j)⁻¹)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j)

theorem deningerMonomialRowDeriv_apply (m : Fin r → Fin s → ℤ) (z : Fin s → ℂ) (i : Fin r)
    (u : Fin s → ℂ) :
    deningerMonomialRowDeriv m z i u =
      ∑ j, ((∏ l, (z l) ^ (m i l)) * ((m i j : ℂ) * (z j)⁻¹)) * u j := by
  rw [deningerMonomialRowDeriv, sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **The logarithmic derivative of a monomial**: the derivative of `∏_j y_j^{m_j}` is the monomial
times the combination `∑_j m_j y_j⁻¹` of the coordinate differentials. -/
theorem deningerMonomialCoord_hasFDerivAt (m : Fin r → Fin s → ℤ) (i : Fin r) {z : Fin s → ℂ}
    (hz : z ∈ deningerStageTorus s) :
    HasFDerivAt (fun y : Fin s → ℂ => ∏ j, (y j) ^ (m i j))
      (deningerMonomialRowDeriv m z i) z := by
  classical
  have hg : ∀ j ∈ Finset.univ, HasFDerivAt (fun y : Fin s → ℂ => (y j) ^ (m i j))
      (((m i j : ℂ) * (z j) ^ (m i j - 1)) •
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j)) z := by
    intro j _
    have hproj : HasFDerivAt (fun y : Fin s → ℂ => y j)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j).hasFDerivAt
    have hzp : HasDerivAt (fun w : ℂ => w ^ (m i j))
        ((m i j : ℂ) * (z j) ^ (m i j - 1)) (z j) :=
      hasDerivAt_zpow _ _ (Or.inl (hz j))
    have heq : (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((m i j : ℂ) * (z j) ^ (m i j - 1))).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j) =
          ((m i j : ℂ) * (z j) ^ (m i j - 1)) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j) := by
      refine ContinuousLinearMap.ext fun u => ?_
      show u j * ((m i j : ℂ) * (z j) ^ (m i j - 1)) =
        ((m i j : ℂ) * (z j) ^ (m i j - 1)) * u j
      ring
    rw [← heq]
    exact hzp.hasFDerivAt.comp z hproj
  have hprod := HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin s))) hg
  have hcoef : ∀ j ∈ (Finset.univ : Finset (Fin s)),
      (∏ l ∈ Finset.univ.erase j, (z l) ^ (m i l)) •
          (((m i j : ℂ) * (z j) ^ (m i j - 1)) •
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j)) =
        ((∏ l, (z l) ^ (m i l)) * ((m i j : ℂ) * (z j)⁻¹)) •
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin s => ℂ) j) := by
    intro j _
    rw [smul_smul]
    congr 1
    have hsub : (z j) ^ (m i j - 1) = (z j) ^ (m i j) * (z j)⁻¹ := by
      rw [zpow_sub₀ (hz j), zpow_one]
      rfl
    have hmul : (z j) ^ (m i j) * (∏ l ∈ Finset.univ.erase j, (z l) ^ (m i l)) =
        ∏ l, (z l) ^ (m i l) :=
      Finset.mul_prod_erase Finset.univ (fun l => (z l) ^ (m i l)) (Finset.mem_univ j)
    rw [hsub, ← hmul]
    ring
  rw [Finset.sum_congr rfl hcoef] at hprod
  exact hprod

/-- **The derivative of a transition map** between character stages. -/
theorem deningerMonomialMap_hasFDerivAt (m : Fin r → Fin s → ℤ) {z : Fin s → ℂ}
    (hz : z ∈ deningerStageTorus s) :
    HasFDerivAt (deningerMonomialMap m)
      (ContinuousLinearMap.pi fun i : Fin r => deningerMonomialRowDeriv m z i) z := by
  refine hasFDerivAt_pi.2 fun i => ?_
  exact deningerMonomialCoord_hasFDerivAt m i hz

end MonomialDerivative

section DlogTransition

variable {r s : ℕ}

/-- **The transition law of the logarithmic differentials**: along a monomial transition map the
logarithmic differential of a coarse coordinate is the integral combination of the fine logarithmic
differentials given by the exponent matrix.  The generators of `(5)` therefore transform like the
lattice of exponents. -/
theorem deningerDlogForm_pullback (m : Fin r → Fin s → ℤ) (i : Fin r) {z : Fin s → ℂ}
    (hz : z ∈ deningerStageTorus s) :
    deningerStagePullback (deningerMonomialMap m) (deningerDlogForm r i) z =
      ∑ j, (m i j : ℂ) • deningerDlogForm s j z := by
  have hfd := (deningerMonomialMap_hasFDerivAt m hz).fderiv
  have hne : (∏ l, (z l) ^ (m i l)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => zpow_ne_zero _ (hz l)
  ext v
  show deningerDlogForm r i (deningerMonomialMap m z)
      (fun a => fderiv ℂ (deningerMonomialMap m) z (v a)) = _
  rw [hfd]
  show (deningerMonomialMap m z i)⁻¹ * (deningerMonomialRowDeriv m z i (v 0)) = _
  rw [deningerMonomialRowDeriv_apply, ContinuousAlternatingMap.sum_apply,
    show deningerMonomialMap m z i = ∏ l, (z l) ^ (m i l) from rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (∏ l, (z l) ^ (m i l))⁻¹ * ((∏ l, (z l) ^ (m i l)) * ((m i j : ℂ) * (z j)⁻¹) * v 0 j) =
    (m i j : ℂ) * ((z j)⁻¹ * v 0 j)
  field_simp

end DlogTransition

end RHTower
