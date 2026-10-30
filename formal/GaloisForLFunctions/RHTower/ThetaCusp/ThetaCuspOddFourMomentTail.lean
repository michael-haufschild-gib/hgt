import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMomentTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSeventhRankStrict
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSuccessorSource

/-!
# The eighth section through the odd first-moment tail

Odd signed jets vanish, so the eighth signed section splits into its even block, already a block
of the strict seventh section, and the odd block `O(a) = (s_{2(i+j)+2}(a))_{i,j<4}`. With the
first-moment tails `V_k(r) = ∫_{s>r} s h_k(s/2) ds`,

`vᵀ O(a) v = a ∫_{r>0} cosh(ar) Σ v_i v_j V_{2(i+j)+2}(r) dr`,

so the eighth section, equivalently the successor integral `I_7(a) ≥ 0`, follows at every
critical aperture at once from nonnegativity of a single `a`-free odd tail form.
-/

open MeasureTheory Set Matrix
namespace RHTower
noncomputable section

/-- The odd first-moment tail form of rank four. -/
def thetaCuspOddFourMomentTailForm (r : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, v i * v j *
    thetaCuspNativeSignedJetMomentTail (2 * (i.val + j.val) + 2) r

/-- The odd block of the eighth signed section. -/
def thetaCuspCenterMixedOddFour (a : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => thetaCuspCenterMixedSignedJet a (2 * (i.val + j.val) + 2)

/-- The odd block is the aperture integral of the odd tail form. -/
theorem thetaCuspCenterMixedOddFour_form_eq {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (v : Fin 4 → ℝ) :
    star v ⬝ᵥ (thetaCuspCenterMixedOddFour a *ᵥ v) =
      a * ∫ r in Ioi 0, Real.cosh (a*r) * thetaCuspOddFourMomentTailForm r v := by
  have hint (i j : Fin 4) : IntegrableOn (fun r => Real.cosh (a*r) *
      thetaCuspNativeSignedJetMomentTail (2 * (i.val + j.val) + 2) r) (Ioi 0) :=
    integrableOn_cosh_mul_thetaCuspNativeSignedJetMomentTail ha0 (by linarith) _
  have hpoint (r : ℝ) : Real.cosh (a*r) * thetaCuspOddFourMomentTailForm r v =
      ∑ i : Fin 4, ∑ j : Fin 4, (v i * v j) *
        (Real.cosh (a*r) * thetaCuspNativeSignedJetMomentTail (2 * (i.val + j.val) + 2) r) := by
    simp only [thetaCuspOddFourMomentTailForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (v i * v j))),
    Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedOddFour, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum Finset.univ (fun j _ => (hint i j).const_mul (v i * v j)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_momentTail ha0 ha]
  ring

theorem thetaCuspCenterMixedOddFour_isHermitian (a : ℝ) :
    (thetaCuspCenterMixedOddFour a).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [thetaCuspCenterMixedOddFour, add_comm]

/-- Nonnegative odd tail forms give a nonnegative odd block at every critical aperture. -/
theorem thetaCuspCenterMixedOddFour_posSemidef_of_tail
    (htail : ∀ r : ℝ, 0 < r → ∀ v : Fin 4 → ℝ, 0 ≤ thetaCuspOddFourMomentTailForm r v)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    (thetaCuspCenterMixedOddFour a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (thetaCuspCenterMixedOddFour_isHermitian a) fun v => ?_
  rw [thetaCuspCenterMixedOddFour_form_eq ha0 ha]
  refine mul_nonneg ha0 (setIntegral_nonneg measurableSet_Ioi fun r hr => ?_)
  exact mul_nonneg (Real.cosh_pos _).le (htail r hr v)

/-- The eighth signed section splits into the even block of the seventh and the odd block. -/
theorem thetaCuspCenterMixedSignedHankel_eight_posSemidef_of_oddFour
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hOdd : (thetaCuspCenterMixedOddFour a).PosSemidef) :
    (thetaCuspCenterMixedSignedHankel a 8).PosSemidef := by
  let e : Fin 4 → Fin 8 := fun i => ⟨2 * i.val, by omega⟩
  let o : Fin 4 → Fin 8 := fun i => ⟨2 * i.val + 1, by omega⟩
  let e7 : Fin 4 → Fin 7 := fun i => ⟨2 * i.val, by omega⟩
  have he7inj : Function.Injective e7 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only [e7] at h
    omega
  have hEven : ((thetaCuspCenterMixedSignedHankel a 8).submatrix e e).PosSemidef := by
    have h7 := ((thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha).submatrix he7inj).posSemidef
    have hEq : (thetaCuspCenterMixedSignedHankel a 8).submatrix e e =
        (thetaCuspCenterMixedSignedHankel a 7).submatrix e7 e7 := by
      ext i j
      rfl
    rw [hEq]
    exact h7
  have hOddEq : (thetaCuspCenterMixedSignedHankel a 8).submatrix o o =
      thetaCuspCenterMixedOddFour a := by
    ext i j
    simp only [submatrix_apply, thetaCuspCenterMixedSignedHankel, thetaCuspCenterMixedOddFour, o]
    congr 1
    omega
  have hHerm : (thetaCuspCenterMixedSignedHankel a 8).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
  have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
  have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
  have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
  have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
  have ho5 := thetaCuspCenterMixedSignedJet_odd a 5
  have ho6 := thetaCuspCenterMixedSignedJet_odd a 6
  norm_num at ho0 ho1 ho2 ho3 ho4 ho5 ho6
  have hSplit (v : Fin 8 → ℝ) :
      star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a 8 *ᵥ v) =
        star (v ∘ e) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 8).submatrix e e *ᵥ (v ∘ e)) +
        star (v ∘ o) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 8).submatrix o o *ᵥ (v ∘ o)) := by
    simp [dotProduct, mulVec, Fin.sum_univ_succ,
      thetaCuspCenterMixedSignedHankel, e, o, ho0, ho1, ho2, ho3, ho4, ho5, ho6]
    ring
  rw [hOddEq] at hSplit
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  rw [hSplit]
  exact add_nonneg (hEven.dotProduct_mulVec_nonneg _) (hOdd.dotProduct_mulVec_nonneg _)

/-- **The eighth section from the odd tail.** Nonnegative odd first-moment tail forms give the
eighth signed section, equivalently `I_7(a) ≥ 0`, at every critical aperture. -/
theorem thetaCuspNativeSuccessorIntegral_seven_nonneg_of_oddTail
    (htail : ∀ r : ℝ, 0 < r → ∀ v : Fin 4 → ℝ, 0 ≤ thetaCuspOddFourMomentTailForm r v)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 7 (r/2) :=
  (thetaCuspCenterMixedSignedHankel_succ_posSemidef_iff_nativeIntegral_nonneg ha0.le ha
    (thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha)).mp
    (thetaCuspCenterMixedSignedHankel_eight_posSemidef_of_oddFour ha0 ha
      (thetaCuspCenterMixedOddFour_posSemidef_of_tail htail ha0.le ha))

end
end RHTower
