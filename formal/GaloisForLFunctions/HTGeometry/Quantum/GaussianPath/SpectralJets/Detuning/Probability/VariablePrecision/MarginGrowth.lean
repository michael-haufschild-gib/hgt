import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.FiniteMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.CouplingBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ScaleGrowth

/-! # A finite-mode floor with a prescribed number of confidence bits -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Box radius covering all coefficients with failure probability at most two to minus q. -/
def bitConfidenceBox (q k : ℕ) : ℝ :=
  2*((q:ℝ)+(Fintype.card (Coordinates (k+3)):ℝ)+1)

/-- At exponentially small exceptional probability, the logarithm of
the inverse margin is still polynomial in Hilbert dimension. -/
theorem bit_confidence_margin (q : ℕ → ℕ) (hq : PolynomialInDimension q) (count : ℕ → ℕ)
    (hS : LogPolynomialInDimension (fun k => (count k:ℝ))) :
    LogPolynomialInDimension (fun k => (confidenceMargin k (count k) (bitConfidenceBox (q k) k)
      ((1/2:ℝ)^(q k)))⁻¹) := by
  let D (k : ℕ) := 2^(k+3)
  let L (k : ℕ) := D k-2
  let hD := LogPolynomialInDimension.natCast PolynomialInDimension.dim
  let hL := LogPolynomialInDimension.natCast polynomial_jet_order
  let h₁ := LogPolynomialInDimension.const 1
  let h₂ := LogPolynomialInDimension.const 2
  have hcoords : PolynomialInDimension (fun k => Fintype.card (Coordinates (k+3))) := by
    simpa only [Coordinates,Fintype.card_fin] using polynomial_labels
  have hbox : LogPolynomialInDimension (fun k => bitConfidenceBox (q k) k) := by
    change LogPolynomialInDimension (fun k => 2*((q k:ℝ)+
      (Fintype.card (Coordinates (k+3)):ℝ)+1))
    simpa only [Nat.cast_ofNat,Nat.cast_one] using
      h₂.mul (((LogPolynomialInDimension.natCast hq).add (LogPolynomialInDimension.natCast hcoords)).add h₁)
  let hC := h₁.add ((responseCap_box_log_polynomial _ hbox).mul hD).abs
  let hB := h₁.add (h₂.mul (LogPolynomialInDimension.natCast polynomial_detector_degree))
  have hstrip : LogPolynomialInDimension (fun k => (modeStripPrice (D k) (L k) (count k):ℝ)) := by
    simpa only [modeStripPrice,Nat.cast_mul,Nat.cast_ofNat,D,L] using
      ((((LogPolynomialInDimension.const 16).mul hS).mul hD).mul hL).mul jetIntervals_log_polynomial
  let hη := LogPolynomialInDimension.twoPow hq
  have hh := (hC.mul ((hη.mul hB).pow polynomial_detector_degree)).mul
    ((hη.mul (h₁.add hstrip)).pow polynomial_jet_order)
  have he (k : ℕ) : (confidenceMargin k (count k) (bitConfidenceBox (q k) k) ((1/2:ℝ)^(q k)))⁻¹ =
      (1+|pathResponseCap (k+3) (L k) (bitConfidenceBox (q k) k)*(D k:ℝ)|)*
      ((2:ℝ)^(q k)*(1+2*(prefixDetectorDegree k:ℝ)))^(prefixDetectorDegree k)*
      ((2:ℝ)^(q k)*(1+(modeStripPrice (D k) (L k) (count k):ℝ)))^(L k) := by
    simp only [confidenceMargin,D,L,div_eq_mul_inv,mul_inv_rev,←inv_pow,inv_inv,one_mul]
    ac_rfl
  change LogPolynomialInDimension (fun k => (confidenceMargin k (count k) (bitConfidenceBox (q k) k)
    ((1/2:ℝ)^(q k)))⁻¹)
  simp_rw [he]
  simpa only [D,L,Nat.cast_one,Nat.cast_ofNat] using hh

/-- The same finite family of modes admits a deterministic doubly
exponential inverse margin and a stated Gaussian exceptional mass. -/
theorem gaussian_bit_confidence_margin (q : ℕ → ℕ) (hq : PolynomialInDimension q)
    (S : (k : ℕ) → Finset (Fin (2^(k+3)) → ℤ))
    (hcard : LogPolynomialInDimension (fun k => ((S k).card:ℝ))) :
    ∃ c : ℕ, ∀ k : ℕ,
      let N := k+3
      let D : ℕ := 2^N
      let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
      μ (smallBalancedMode N (S k) ((2:ℝ)^(D^c))⁻¹) ≤ ENNReal.ofReal (3*(1/2:ℝ)^(q k)) := by
  obtain ⟨c,hc⟩ := (bit_confidence_margin q hq (fun k => (S k).card) hcard).bound
  refine ⟨c,fun k => ?_⟩
  intro N D μ
  let η := (1/2:ℝ)^(q k)
  let T := bitConfidenceBox (q k) k
  let m := confidenceMargin k (S k).card T η
  have hη : 0<η := pow_pos (by norm_num) _
  have hη' : η≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm : 0 < m := by dsimp only [m,confidenceMargin]; positivity
  have ht : ((2:ℝ)^(D^c))⁻¹ ≤ m := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hm) (hc k)
  have hsub : smallBalancedMode N (S k) ((2:ℝ)^(D^c))⁻¹ ⊆ smallBalancedMode N (S k) m := by
    rintro x ⟨v,hv,h₁,h₂,hl⟩
    exact ⟨v,hv,h₁,h₂,hl.trans_le ht⟩
  have hT : 0≤T := by dsimp only [T,bitConfidenceBox]; positivity
  have hh := gaussian_confidence_margin k (S k) hT hη hη'
  have hb := gaussian_dimension_box (Coordinates N) (q k)
  apply (measure_mono hsub).trans (hh.trans _)
  apply (add_le_add (add_le_add hb (le_refl (ENNReal.ofReal η))) (le_refl (ENNReal.ofReal η))).trans_eq
  rw [←ENNReal.ofReal_add hη.le hη.le,←ENNReal.ofReal_add (add_nonneg hη.le hη.le) hη.le]
  congr 1
  ring

#print axioms gaussian_bit_confidence_margin
end
end GaloisForLFunctions.HTGeometry.SpectralJets
