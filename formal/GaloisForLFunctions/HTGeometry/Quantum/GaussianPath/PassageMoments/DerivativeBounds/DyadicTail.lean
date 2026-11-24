import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.RadialBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.LocalTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.MarginGrowth

/-! # A power-law upper bound for the joint physical first passage -/
open Filter Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
open PrescribedTimes SpectralJets
noncomputable section

theorem dyadic_margin_inverse (d u : ℕ) :
    (((1/2:ℝ)^u)^d)⁻¹=((2:ℝ)^d)^u := by
  rw [one_div,inv_pow,inv_pow,inv_inv,←pow_mul,←pow_mul,Nat.mul_comm]

/-- Multiplying all couplings by a positive scalar divides both first clocks by it. -/
theorem passageMax_smul (k s : ℕ) {a : ℝ} (ha : 0<a) (x : PrefixIndex (k+1) → ℝ) :
    a*passageMax k s (a • x)=passageMax k s x := by
  change a*max _ _=max _ _
  rw [mul_max_of_nonneg _ _ ha.le,smul_crossingOrigin _ _ _ ha,smul_crossingWait _ _ _ ha]

/-- The tail is weak L to the inverse detector-plus-jet order, including
the endpoint. The same constant works for every gate budget and confidence. -/
theorem gaussian_derivative_survival :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ η : ℝ, 0<η → η≤1 →
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      μ.real {x | boxDeadline k (confidenceBox k)*(η^marginOrder k)⁻¹<passageMax k s x}
        ≤ (8/3)*η := by
  filter_upwards [gaussian_local_passage_tail] with k hk
  intro s η hη hη' μ
  let n := k+1
  let m := Fintype.card (ChainLabel (k+3))
  let T := confidenceBox k
  let G := boxDeadline k T*(η^marginOrder k)⁻¹
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) ((pathCoeffEquiv n).symm (Sum.inl (0,0))).isLt
  have hT : 2*sqrt (m:ℝ)≤T := by
    simp only [T,confidenceBox,Coordinates,Fintype.card_fin]
    have hm' : 1 ≤ m := hm
    have hs := sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ) ≤ m by exact_mod_cast hm'))
    change 2*sqrt (m:ℝ) ≤ 2*(((2^(k+3):ℕ):ℝ)+(m:ℝ)+1)
    linarith only [hs,Nat.cast_nonneg (α:=ℝ) (2^(k+3))]
  have hG : 0≤G := mul_nonneg (boxDeadline_pos k T).le (inv_nonneg.mpr (pow_nonneg hη.le _))
  have hl := hk T η ((mul_nonneg two_pos.le (sqrt_nonneg _)).trans hT) hη hη'
  have h := (gaussian_box_retains_tail m hm (passageMax k 0) (measurable_passageMax k 0)
    (fun _ ha => passageMax_smul k 0 ha) hG hT).trans hl
  have hsub : {x | G<passageMax k s x} ⊆ {x | G<passageMax k 0 x} := by
    intro x hx
    exact hx.trans_le (max_le_max le_rfl (crossingWait_antitone (Nat.zero_le s) x))
  apply (measureReal_mono (μ:=μ) hsub).trans
  change (3/4:ℝ)*μ.real {x | G<passageMax k 0 x} ≤ 2*η at h
  linarith only [h]

#print axioms gaussian_derivative_survival
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
