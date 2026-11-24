import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.FirstPassage.Detuning
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.FrequencyEvent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.DerivativeBounds.DyadicTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.GeometricTail

/-! # First crossing and first return moments at linear spectral derivative order -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
open PrescribedTimes PassageMoments PassageMoments.DerivativeBounds
noncomputable section

/-- Combined confidence power at N=k+3, with D=2^N and L=2N−1. -/
def clockOrder (k : ℕ) := detectorDegree (k+2)+(2*(k+2)+1)

def directedDeadline (k : ℕ) (T : ℝ) : ℝ :=
  phaseClockPrice k/detuningMargin (k+2) (retainedClockModes k).card T 1

private theorem directedDeadline_pos (k : ℕ) (T : ℝ) : 0<directedDeadline k T := by
  dsimp only [directedDeadline,phaseClockPrice,detuningMargin,floorAtOrder]
  positivity

private theorem directed_factor (k : ℕ) (T η : ℝ) :
    phaseClockPrice k/detuningMargin (k+2) (retainedClockModes k).card T η =
      directedDeadline k T*(η^clockOrder k)⁻¹ := by
  simp only [directedDeadline,detuningMargin,floorAtOrder,clockOrder,detectorDegree,
    div_eq_mul_inv,mul_inv_rev,←inv_pow,inv_inv,pow_add,mul_pow,one_mul]
  ring

/-- The tail for the maximum of the actual first robust crossing and its first
return wait has weak moment order 1/(2D+4LD²+L), uniformly across gate budgets. -/
theorem directed_passage_survival :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ η : ℝ, 0<η → η≤1 →
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      μ.real {x | directedDeadline k (confidenceBox k)*(η^clockOrder k)⁻¹<passageMax k s x}
        ≤ (8/3)*η := by
  filter_upwards [passage_tail_on_event] with k hk
  intro s η hη hη' μ
  let T := confidenceBox k
  let m := Fintype.card (ChainLabel (k+3))
  let S := {x : PrefixIndex (k+1)→ℝ | ∀ i, |x i|≤T}
  let δ := detuningMargin (k+2) (retainedClockModes k).card T η
  let G := phaseClockPrice k/δ
  have hS : MeasurableSet S := by
    change MeasurableSet {x : PrefixIndex (k+1)→ℝ | ∀ i, |x i|≤T}
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) ((pathCoeffEquiv (k+1)).symm (Sum.inl (0,0))).isLt
  have hT : 2*sqrt (m:ℝ)≤T := by
    change 2*sqrt (m:ℝ) ≤ 2*(((2^(k+3):ℕ):ℝ)+(Fintype.card (Coordinates (k+3)):ℝ)+1)
    rw [show Fintype.card (Coordinates (k+3))=m from Fintype.card_fin _]
    have h₁ : 1 ≤ m := hm
    have hs := sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ) ≤ m by exact_mod_cast h₁))
    linarith only [hs,Nat.cast_nonneg (α:=ℝ) (2^(k+3))]
  have hT₀ := (mul_nonneg two_pos.le (sqrt_nonneg _)).trans hT
  have hδ : 0<δ := by dsimp only [δ,detuningMargin,floorAtOrder]; positivity
  have hG : 0≤G := by dsimp only [G,phaseClockPrice]; positivity
  have hb := (hk S hS s δ hδ).trans (gaussian_box_detuning (k+2) (retainedClockModes k) hT₀ hη hη')
  rw [←ENNReal.ofReal_add hη.le hη.le] at hb
  have hl := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (add_nonneg hη.le hη.le)] at hl
  have h := (gaussian_box_retains_tail m hm (passageMax k s) (measurable_passageMax k s)
    (fun _ ha => passageMax_smul k s ha) hG hT).trans hl
  rw [←directed_factor]
  change (3/4:ℝ)*μ.real {x | G<passageMax k s x} ≤ η+η at h
  linarith only [h]

/-- Every moment strictly below the reciprocal confidence power is finite, for
the same Hamiltonian before and after the first robust crossing. -/
theorem directed_first_passage_moments :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ p : ℝ, 0<p → p<1/(clockOrder k:ℝ) →
      Integrable (fun x => (passageMax k s x)^p)
        (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1) := by
  filter_upwards [directed_passage_survival] with k hk s p hp hq
  let d := clockOrder k
  let B := (2:ℝ)^d
  have hd : 0<d := by dsimp only [d,clockOrder,detectorDegree]; positivity
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hB : 1<B := one_lt_pow₀ (by norm_num) hd.ne'
  have hBp : B^p<2 := by
    change ((2:ℝ)^d)^p<2
    rw [←Real.rpow_natCast_mul (by norm_num : 0≤(2:ℝ))]
    apply (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1<(2:ℝ)) _).trans_eq (Real.rpow_one 2)
    simpa only [mul_comm] using (lt_div_iff₀ hd').mp hq
  apply integrable_rpow_of_geometric_tail _ _ (measurable_passageMax k s) (passageMax_nonneg k s)
    (directedDeadline_pos k (confidenceBox k)) hB (by norm_num : 0≤(1/2:ℝ)) hp
    (by linarith only [hBp] : B^p*(1/2)<1) (C:=8/3)
  intro u
  have h := hk s ((1/2:ℝ)^u) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  rwa [dyadic_margin_inverse] at h

#print axioms directed_passage_survival
#print axioms directed_first_passage_moments
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
