import GaloisForLFunctions.HTGeometry.PoincareHopf.VanishingLemma

/-!
# The cofactor transform of an arbitrary field

For a `C²` map `u` and a `C¹` field `G` on `ℝⁿ`, the cofactor transform

  `(cofField u G) j = ∑ i, cof (Du)_{i j} · G i`

has divergence `∑ i j, cof (Du)_{i j} · ∂_j G_i`: the terms in which the derivative falls on the
cofactor cancel by the Piola identity.  Together with the fundamental vanishing lemma this gives

  `∫_Ω ∑ i j, cof (Du x)_{i j} · ∂_j G_i x dx = 0`

for every `G` vanishing near the boundary of the bounded open set `Ω`.  This is the form of the
vanishing lemma that homotopy invariance needs, where `G` is not a field pulled back along `u`.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {u G : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}

/-- The cofactor transform of the field `G` by the Jacobian of `u`. -/
noncomputable def cofField (u G : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i, cofSum (jac u x) i j * G x i

/-- The differential of the `j`-th component of the cofactor transform. -/
noncomputable def cofFieldD (u G : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (cofSum (jac u x) i j • ((ContinuousLinearMap.proj i).comp (fderiv ℝ G x))
      + G x i • cofD u x i j)

theorem contDiff_cofField (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (cofField u G) := by
  rw [contDiff_pi]
  intro j
  exact ContDiff.sum fun i _ => (contDiff_cofSum_jac hu i j).mul (contDiff_pi.mp hG i)

theorem hasFDerivAt_cofField (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 1 G) (x : Fin n → ℝ) :
    HasFDerivAt (cofField u G) (ContinuousLinearMap.pi (cofFieldD u G x)) x := by
  have hG1 : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by simp) x).hasFDerivAt
  have hGi : ∀ i : Fin n, HasFDerivAt (fun y => G y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ G x)) x :=
    fun i => hasFDerivAt_pi'.mp hG1 i
  refine hasFDerivAt_pi'.mpr fun j => ?_
  rw [ContinuousLinearMap.proj_pi]
  have hfun : (fun y => cofField u G y j)
      = ∑ i, (fun y => cofSum (jac u y) i j * G y i) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun, cofFieldD]
  exact HasFDerivAt.sum fun i _ => (hasFDerivAt_cofSum hu x i j).mul (hGi i)

/-- **Divergence of the cofactor transform.** -/
theorem fieldDivergence_cofField (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 1 G) (x : Fin n → ℝ) :
    fieldDivergence (cofField u G) x = ∑ i, ∑ j, cofSum (jac u x) i j * jac G x i j := by
  have hfd : fderiv ℝ (cofField u G) x = ContinuousLinearMap.pi (cofFieldD u G x) :=
    (hasFDerivAt_cofField hu hG x).fderiv
  have hstep : fieldDivergence (cofField u G) x
      = ∑ j, cofFieldD u G x j (Pi.single j 1) := by
    simp [fieldDivergence, hfd]
  have hterm : ∀ j : Fin n, cofFieldD u G x j (Pi.single j 1)
      = ∑ i, (cofSum (jac u x) i j * jac G x i j + G x i * cofD u x i j (Pi.single j 1)) := by
    intro j
    rw [cofFieldD, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [jac]
  rw [hstep]
  have hsplit : (∑ j, cofFieldD u G x j (Pi.single j 1))
      = (∑ j, ∑ i, cofSum (jac u x) i j * jac G x i j)
        + ∑ j, ∑ i, G x i * cofD u x i j (Pi.single j 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hterm j, ← Finset.sum_add_distrib]
  have hpiola : (∑ j, ∑ i, G x i * cofD u x i j (Pi.single j 1)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, piola hu x i, mul_zero]
  rw [hsplit, hpiola, add_zero, Finset.sum_comm]

theorem cofField_eventuallyEq_zero {x : Fin n → ℝ} (h : G =ᶠ[nhds x] 0) :
    cofField u G =ᶠ[nhds x] 0 := by
  filter_upwards [h] with z hz
  funext j
  have : G z = 0 := hz
  simp [cofField, this]

/-- **The vanishing lemma for the cofactor transform.** -/
theorem integral_cofSum_mul_jac_eq_zero
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 1 G)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfront : ∀ x ∈ frontier Ω, G =ᶠ[nhds x] 0) :
    ∫ x in Ω, (∑ i, ∑ j, cofSum (jac u x) i j * jac G x i j) = 0 := by
  have hzero := integral_fieldDivergence_of_vanishing_near_frontier
    (contDiff_cofField hu hG) hΩ hΩb (fun x hx => cofField_eventuallyEq_zero (hfront x hx))
  rw [← hzero]
  exact (setIntegral_congr_fun hΩ.measurableSet
    (fun x _ => fieldDivergence_cofField hu hG x)).symm

end GaloisForLFunctions.HTGeometry.PoincareHopf
