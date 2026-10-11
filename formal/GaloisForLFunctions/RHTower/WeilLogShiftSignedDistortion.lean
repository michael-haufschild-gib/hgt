import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalDistortionModulus

/-! Logarithmic nodal distortion preserves the full signed raw weights. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilLogNodalDistortion_weights {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (r + 2)) :
    finiteWeilMomentWeights (fun j => Real.log (x j)) i =
      finiteWeilLogNodalDistortion x i * finiteWeilMomentWeights x i := by
  simp only [finiteWeilMomentWeights, Lagrange.nodalWeight,
    finiteWeilLogNodalDistortion, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hne : x i ≠ x j := fun he => Finset.ne_of_mem_erase hj (hinj he).symm
  have hD : x i - x j ≠ 0 := sub_ne_zero.mpr hne
  have hlog : Real.log (x i) - Real.log (x j) ≠ 0 :=
    sub_ne_zero.mpr (fun he => hne (Real.log_injOn_pos (hx i) (hx j) he))
  rw [finiteWeilLogarithmicMean]
  field_simp

theorem finiteWeilCanonicalRawDistortion_weights (r k : ℕ) (i : Fin (r + 2)) :
    finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i =
      finiteWeilCanonicalRawDistortion r k i *
        finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i := by
  let x := finiteWeilClusterPositiveNodes r k
  have hlog : finiteWeilMomentWeights (fun j => Real.log (x j)) i =
      finiteWeilMomentWeights (finiteWeilClusterLogNodes r k) i := by
    simp only [finiteWeilMomentWeights, Lagrange.nodalWeight]
    apply Finset.prod_congr rfl
    intro j hj
    have hgap : Real.log (x i) - Real.log (x j) =
        finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k j := by
      rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply]
      dsimp [x, finiteWeilClusterPositiveNodes]
      push_cast
      ring
    rw [hgap]
  have harith : finiteWeilMomentWeights x i =
      finiteWeilMomentWeights (finiteWeilArithmeticNodes r) i := by
    simp only [finiteWeilMomentWeights, Lagrange.nodalWeight]
    apply Finset.prod_congr rfl
    intro j hj
    change (finiteWeilClusterPositiveNodes r k i - finiteWeilClusterPositiveNodes r k j)⁻¹ = _
    rw [finiteWeilClusterPositiveNodes_gap]
    rfl
  have h := finiteWeilLogNodalDistortion_weights x (finiteWeilClusterPositiveNodes_pos r k)
    (finiteWeilClusterPositiveNodes_injective r k) i
  rw [hlog, harith] at h
  exact h

end RHTower
