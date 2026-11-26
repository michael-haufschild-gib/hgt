import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SelectedCoordinates

/-! # Selecting a contraction of one child on a Gaussian product space -/

open MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts
open BlockDilations
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

private theorem measurable_expand (S : Finset I) (a : ℝ) : Measurable (expand S a) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i∈S
  · simpa only [expand,if_pos hi] using measurable_const.mul (measurable_pi_apply i)
  · simpa only [expand,if_neg hi] using (measurable_pi_apply i : Measurable fun x : I→ℝ => x i)

/-- Choosing the contracting factor after seeing the child spectra
costs at most the number of choices times their largest inverse
Jacobian. No independence between the choice and the spectra is required. -/
theorem gaussian_contraction_cover (S : Finset I) (a : J→ℝ) (ha : ∀ j, a j∈Icc (1/2:ℝ) 1)
    (G : Set (I→ℝ)) {E : Set (I→ℝ)} (hE : MeasurableSet E)
    (hcover : ∀ x∈G, ∃ j, expand S (a j) x∈E) :
    let μ := Measure.pi fun _ : I => gaussianReal 0 1
    μ.real G ≤ (Fintype.card J:ℝ)*2^S.card*μ.real E := by
  intro μ
  let B (j : J) := expand S (a j) ⁻¹' E
  have hb (j : J) : μ.real (B j)≤2^S.card*μ.real E := by
    have hp : 0<a j := (by norm_num : (0:ℝ)<1/2).trans_le (ha j).1
    have hc : 1≤(a j)⁻¹ := (one_le_inv₀ hp).mpr (ha j).2
    have hd : (a j)⁻¹≤2 := by
      rw [←one_div,div_le_iff₀ hp]
      linarith only [(ha j).1]
    have hpre : expand S (a j)⁻¹ ⁻¹' B j=E := by
      ext x
      change expand S (a j) (expand S (a j)⁻¹ x)∈E ↔ x∈E
      have he : expand S (a j) (expand S (a j)⁻¹ x)=x := by
        funext i
        by_cases hi : i∈S <;> simp [expand,hi,←mul_assoc,hp.ne']
      rw [he]
    have h := selected_gaussian_comparison S hc (hE.preimage (measurable_expand S (a j)))
    change μ.real (B j) ≤ (a j)⁻¹^S.card*μ.real (expand S (a j)⁻¹ ⁻¹' B j) at h
    rw [hpre] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_pos.mpr hp).le hd _)
      measureReal_nonneg)
  have hsub : G⊆⋃ j, B j := fun x hx => mem_iUnion.mpr (hcover x hx)
  apply (measureReal_mono hsub).trans ((measureReal_iUnion_fintype_le _).trans ?_)
  apply (sum_le_sum (s:=univ) (fun j _ => hb j)).trans_eq
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_assoc]

#print axioms gaussian_contraction_cover
end
end GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap.BalancedCuts
