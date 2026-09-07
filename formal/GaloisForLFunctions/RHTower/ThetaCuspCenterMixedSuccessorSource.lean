import GaloisForLFunctions.HTGeometry.HankelSuccessorSchur
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedSixthRank

/-! # Exact successor source and the first open seven-dimensional sign -/
open MeasureTheory Set Matrix
namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Exact Schur coordinate of a successor in the actual signed source hierarchy. -/
def thetaCuspCenterMixedSuccessorSchur (a : ℝ) (n : ℕ) : ℝ :=
  finiteHankelSuccessorSchur (thetaCuspCenterMixedSignedJet a) n

/-- Literal native source whose integral is the actual successor Schur coordinate. -/
def thetaCuspNativeSuccessorSource (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspNativeSignedJet x (2*n) - ∑ i : Fin n, ∑ j : Fin n,
    thetaCuspCenterMixedSignedJet a (i.val+n) *
      (thetaCuspCenterMixedSignedHankel a n)⁻¹ i j * thetaCuspNativeSignedJet x (j.val+n)

/-- The complete weighted successor source is integrable at every order. -/
theorem integrableOn_thetaCuspWeightedNativeSuccessorSource
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (n : ℕ) :
    IntegrableOn (fun r => r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a n (r/2))
      (Ioi 0) := by
  have hi (i j : Fin n) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (j.val+n)).const_mul
    (thetaCuspCenterMixedSignedJet a (i.val+n)*(thetaCuspCenterMixedSignedHankel a n)⁻¹ i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))
  apply ((integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (2*n)).sub hsum).congr
  filter_upwards with r
  simp only [Pi.sub_apply, thetaCuspNativeSuccessorSource, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every successor coordinate retains the complete physical center integral exactly. -/
theorem thetaCuspCenterMixedSuccessorSchur_eq_integral_native
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (n : ℕ) :
    thetaCuspCenterMixedSuccessorSchur a n =
      ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a n (r/2) := by
  have hi (i j : Fin n) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (j.val+n)).const_mul
    (thetaCuspCenterMixedSignedJet a (i.val+n)*(thetaCuspCenterMixedSignedHankel a n)⁻¹ i j)
  have hpoint (r : ℝ) : r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a n (r/2) =
      r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) (2*n)-
        ∑ i : Fin n, ∑ j : Fin n,
          (thetaCuspCenterMixedSignedJet a (i.val+n)*(thetaCuspCenterMixedSignedHankel a n)⁻¹ i j)*
            (r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) (j.val+n)) := by
    simp only [thetaCuspNativeSuccessorSource, mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  rw [integral_sub (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (2*n))
    (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi i j))),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  unfold thetaCuspCenterMixedSuccessorSchur finiteHankelSuccessorSchur
  rw [← thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, ← thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]
  rfl

/-- With its literal head strict, a successor is admitted exactly by its native source integral. -/
theorem thetaCuspCenterMixedSignedHankel_succ_posSemidef_iff_nativeIntegral_nonneg
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) {n : ℕ}
    (hhead : (thetaCuspCenterMixedSignedHankel a n).PosDef) :
    (thetaCuspCenterMixedSignedHankel a (n+1)).PosSemidef ↔
      0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a n (r/2) := by
  change (finiteHankelMatrix (thetaCuspCenterMixedSignedJet a) (n+1)).PosSemidef ↔ _
  rw [finiteHankelMatrix_succ_posSemidef_iff_schur_nonneg hhead]
  change (0 ≤ thetaCuspCenterMixedSuccessorSchur a n) ↔ _
  rw [thetaCuspCenterMixedSuccessorSchur_eq_integral_native ha0 ha n]

/-- The first unproved section is exactly the complete native successor integral at order six. -/
theorem thetaCuspCenterMixedSignedHankel_seven_posSemidef_iff_nativeIntegral_nonneg
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a 7).PosSemidef ↔
      0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 6 (r/2) :=
  thetaCuspCenterMixedSignedHankel_succ_posSemidef_iff_nativeIntegral_nonneg ha0.le ha
    (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha)

/-- The unknown seventh-rank scalar starts with the literal twelfth mixed derivative. -/
theorem thetaCuspCenterMixedSuccessorSchur_six_eq_twelfth (a : ℝ) :
    thetaCuspCenterMixedSuccessorSchur a 6 =
      iteratedDeriv 12 (thetaCuspCenterMixedDensity a) 0-
        ∑ i : Fin 6, ∑ j : Fin 6,
          thetaCuspCenterMixedSignedJet a (i.val+6)*
            (thetaCuspCenterMixedSignedHankel a 6)⁻¹ i j*
              thetaCuspCenterMixedSignedJet a (j.val+6) := by
  have he := thetaCuspCenterMixedSignedJet_even a 6
  norm_num at he
  unfold thetaCuspCenterMixedSuccessorSchur finiteHankelSuccessorSchur
  rw [show 2*6 = 12 by norm_num, he]
  rfl

end
end RHTower
