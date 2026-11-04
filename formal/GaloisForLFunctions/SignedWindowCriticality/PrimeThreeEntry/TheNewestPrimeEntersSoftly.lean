import GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry.TheWindowEdgeCarriesTheNewestPrime
import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.RetainedVarianceAndHalfWindowBandBelowLogFour

/-!
# The newest prime enters softly

Below `log 4` the window `[−c, c]` reads the arithmetic through the two weights `w = (w₂, w₃)` of
the half-window band `|𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)| ≤ W(f)`
(`belowLogFourBandWeights`). Its two halves are the parity sectors:

* `belowLogFourBandWeights c = oddBandWeights c ∩ evenBandWeights c`, each set convex, and at the
  arithmetic weights `(Λ(2)/√2, Λ(3)/√3)` membership is the positivity of the odd, resp. even,
  sector of `[−c, c]` (`belowLogFourBandWeights_eq_inter`, `oddSector_iff_mem_oddBandWeights`,
  `evenSector_iff_mem_evenBandWeights`).
* **Entry**: for `2c ≤ log 3` both sector sets are cylinders in `w₃`
  (`mem_oddBandWeights_iff_of_le`, `mem_evenBandWeights_iff_of_le`).
* **Soft entry**: if a sector band holds with a Lévy margin `η` at `(w₂, w₃)`, it holds at every
  `(w₂, w₃')` with `|w₃' − w₃| ≤ η Ω(2c − log 3)`, `Ω(δ) = ∫_δ^∞ ω ≥ (e^{−1/2}/2) log(1/δ)`
  (`mem_oddBandWeights_of_margin`, `mem_evenBandWeights_of_margin`, and the `_log` forms): the
  tolerance of the newest weight is infinite at the entry `2c = log 3` and decreases as the
  collar sliver `[−c, c − log 3]` opens. The mechanism is the edge bound
  `|(f⋆f)(−log 3)| Ω(2c − log 3) ≤ levyEnergy f` (`TheWindowEdgeCarriesTheNewestPrime`).
-/

open MeasureTheory Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open _root_.RHTower

/-! ### The parity sectors of the two-prime band -/

/-- The odd half of the band: `𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3) ≤ W(f)`. -/
def oddBandWeights (c : ℝ) : Set (ℝ × ℝ) :=
  {w | ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
    collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3) ≤
      weilQuad f}

/-- The even half of the band: `−(𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)) ≤ W(f)`. -/
def evenBandWeights (c : ℝ) : Set (ℝ × ℝ) :=
  {w | ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
    -(collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3)) ≤
      weilQuad f}

theorem belowLogFourBandWeights_eq_inter (c : ℝ) :
    belowLogFourBandWeights c = oddBandWeights c ∩ evenBandWeights c := by
  ext w
  constructor
  · intro hw
    exact ⟨fun f hf h0 hfc => (abs_le.mp (hw f hf h0 hfc)).2,
      fun f hf h0 hfc => by linarith [(abs_le.mp (hw f hf h0 hfc)).1]⟩
  · rintro ⟨ho, he⟩ f hf h0 hfc
    exact abs_le.mpr ⟨by linarith [he f hf h0 hfc], ho f hf h0 hfc⟩

/-- At the arithmetic weights the odd half is the odd sector of `[−c, c]`. -/
theorem oddSector_iff_mem_oddBandWeights {c : ℝ} (hc0 : 0 < c) (hc : c < Real.log 2) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      (vonMangoldtAtom 2, vonMangoldtAtom 3) ∈ oddBandWeights c := by
  rw [odd_nonneg_iff_centreCoupling_le hc0]
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun hfc => ?_
  rw [centreCoupling_eq_two_three_of_lt_log_two hc hfc]

/-- At the arithmetic weights the even half is the even sector of `[−c, c]`. -/
theorem evenSector_iff_mem_evenBandWeights {c : ℝ} (hc0 : 0 < c) (hc : c < Real.log 2) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      (vonMangoldtAtom 2, vonMangoldtAtom 3) ∈ evenBandWeights c := by
  rw [even_nonneg_iff_neg_centreCoupling_le hc0]
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun hfc => ?_
  rw [centreCoupling_eq_two_three_of_lt_log_two hc hfc]

theorem convex_oddBandWeights (c : ℝ) : Convex ℝ (oddBandWeights c) := by
  intro w hw w' hw' s t hs ht hst f hf h0 hfc
  have e := hw f hf h0 hfc
  have e' := hw' f hf h0 hfc
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have hlin : collarHankel 0 f - (s * w.1 + t * w'.1) * selfConv f (-Real.log 2) -
        (s * w.2 + t * w'.2) * selfConv f (-Real.log 3) =
      s * (collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3)) +
        t * (collarHankel 0 f - w'.1 * selfConv f (-Real.log 2) -
          w'.2 * selfConv f (-Real.log 3)) := by
    linear_combination (-collarHankel 0 f) * hst
  rw [hlin]
  calc _ ≤ s * weilQuad f + t * weilQuad f :=
        add_le_add (mul_le_mul_of_nonneg_left e hs) (mul_le_mul_of_nonneg_left e' ht)
    _ = weilQuad f := by rw [← add_mul, hst, one_mul]

theorem convex_evenBandWeights (c : ℝ) : Convex ℝ (evenBandWeights c) := by
  intro w hw w' hw' s t hs ht hst f hf h0 hfc
  have e := hw f hf h0 hfc
  have e' := hw' f hf h0 hfc
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  have hlin : -(collarHankel 0 f - (s * w.1 + t * w'.1) * selfConv f (-Real.log 2) -
        (s * w.2 + t * w'.2) * selfConv f (-Real.log 3)) =
      s * -(collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3)) +
        t * -(collarHankel 0 f - w'.1 * selfConv f (-Real.log 2) -
          w'.2 * selfConv f (-Real.log 3)) := by
    linear_combination (collarHankel 0 f) * hst
  rw [hlin]
  calc _ ≤ s * weilQuad f + t * weilQuad f :=
        add_le_add (mul_le_mul_of_nonneg_left e hs) (mul_le_mul_of_nonneg_left e' ht)
    _ = weilQuad f := by rw [← add_mul, hst, one_mul]

/-! ### Entry: the newest weight is invisible -/

/-- Before its entry (`2c ≤ log 3`) the prime `3` does not meet a half-window test. -/
theorem selfConv_neg_log_three_eq_zero {c : ℝ} (hc : 2 * c ≤ Real.log 3) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : ∀ u, u < -c → f u = 0) : selfConv f (-Real.log 3) = 0 :=
  selfConv_neg_eq_zero_of_le hf.continuous hfc hc

theorem mem_oddBandWeights_iff_of_le {c : ℝ} (hc : 2 * c ≤ Real.log 3) (w₂ w₃ w₃' : ℝ) :
    (w₂, w₃) ∈ oddBandWeights c ↔ (w₂, w₃') ∈ oddBandWeights c := by
  constructor <;> intro h f hf h0 hfc <;> have e := h f hf h0 hfc <;>
    simp only [selfConv_neg_log_three_eq_zero hc hf hfc, mul_zero, sub_zero] at e ⊢ <;> exact e

theorem mem_evenBandWeights_iff_of_le {c : ℝ} (hc : 2 * c ≤ Real.log 3) (w₂ w₃ w₃' : ℝ) :
    (w₂, w₃) ∈ evenBandWeights c ↔ (w₂, w₃') ∈ evenBandWeights c := by
  constructor <;> intro h f hf h0 hfc <;> have e := h f hf h0 hfc <;>
    simp only [selfConv_neg_log_three_eq_zero hc hf hfc, mul_zero, sub_zero] at e ⊢ <;> exact e

/-! ### Soft entry: the tolerance of the newest weight -/

/-- The odd half of the band holds at `w` with Lévy margin `η`. -/
def OddBandMargin (c η : ℝ) (w : ℝ × ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
    collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3) +
      η * levyEnergy f ≤ weilQuad f

/-- The even half of the band holds at `w` with Lévy margin `η`. -/
def EvenBandMargin (c η : ℝ) (w : ℝ × ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
    -(collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3)) +
      η * levyEnergy f ≤ weilQuad f

/-- A change `Δ` of the prime-3 weight moves the coupling by at most `η Lévy` when
`|Δ| ≤ η Ω(2c − log 3)`. -/
theorem abs_mul_selfConv_log_three_le {c η Δ : ℝ} (hc : Real.log 3 < 2 * c) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -c → f u = 0)
    (htol : |Δ| ≤ η * ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x) :
    |Δ * selfConv f (-Real.log 3)| ≤ η * levyEnergy f := by
  have hfcs := hasCompactSupport_of_half h0 hfc
  have hk := abs_selfConv_neg_mul_levyTail_le (ℓ := Real.log 3) hf hfcs hfc hc
  have hΩ : 0 < ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x :=
    lt_of_lt_of_le (by positivity) (two_mul_exp_le_levyTail (by linarith))
  have hη : 0 ≤ η := by
    have := (abs_nonneg Δ).trans htol
    exact (mul_nonneg_iff_of_pos_right hΩ).mp this
  rw [abs_mul]
  calc |Δ| * |selfConv f (-Real.log 3)|
      ≤ η * (∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x) * |selfConv f (-Real.log 3)| :=
        mul_le_mul_of_nonneg_right htol (abs_nonneg _)
    _ = η * (|selfConv f (-Real.log 3)| * ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x) := by
        ring
    _ ≤ η * levyEnergy f := mul_le_mul_of_nonneg_left hk hη

/-- **Soft entry, odd half.** A Lévy margin `η` at `(w₂, w₃)` admits every `(w₂, w₃')` with
`|w₃' − w₃| ≤ η Ω(2c − log 3)`. -/
theorem mem_oddBandWeights_of_margin {c η : ℝ} {w : ℝ × ℝ} (hw : OddBandMargin c η w)
    (hc : Real.log 3 < 2 * c) {w₃' : ℝ}
    (htol : |w₃' - w.2| ≤ η * ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x) :
    (w.1, w₃') ∈ oddBandWeights c := by
  intro f hf h0 hfc
  have hm := hw f hf h0 hfc
  have hd := abs_mul_selfConv_log_three_le hc hf h0 hfc htol
  have hle := le_abs_self ((w₃' - w.2) * selfConv f (-Real.log 3))
  show collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w₃' * selfConv f (-Real.log 3) ≤
    weilQuad f
  have hneg := neg_abs_le ((w₃' - w.2) * selfConv f (-Real.log 3))
  nlinarith

/-- **Soft entry, even half.** -/
theorem mem_evenBandWeights_of_margin {c η : ℝ} {w : ℝ × ℝ} (hw : EvenBandMargin c η w)
    (hc : Real.log 3 < 2 * c) {w₃' : ℝ}
    (htol : |w₃' - w.2| ≤ η * ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x) :
    (w.1, w₃') ∈ evenBandWeights c := by
  intro f hf h0 hfc
  have hm := hw f hf h0 hfc
  have hd := abs_mul_selfConv_log_three_le hc hf h0 hfc htol
  have hle := le_abs_self ((w₃' - w.2) * selfConv f (-Real.log 3))
  show -(collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w₃' * selfConv f (-Real.log 3)) ≤
    weilQuad f
  nlinarith

/-- The logarithmic tolerance: `|w₃' − w₃| ≤ η (e^{−1/2}/2) log(1/(2c − log 3))` suffices. -/
theorem tol_of_log {c η Δ : ℝ} (hη : 0 ≤ η) (hc : Real.log 3 < 2 * c)
    (hδ1 : 2 * c - Real.log 3 ≤ 1)
    (htol : |Δ| ≤ η * (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log 3)))) :
    |Δ| ≤ η * ∫ x in Ioi (2 * c - Real.log 3), archLevyDensity x :=
  htol.trans (mul_le_mul_of_nonneg_left (levyTail_ge_log (by linarith) hδ1) hη)

/-- **Soft entry with logarithmic tolerance, both halves.** -/
theorem mem_bandWeights_of_margin_log {c η : ℝ} {w : ℝ × ℝ} (hη : 0 ≤ η)
    (hc : Real.log 3 < 2 * c) (hδ1 : 2 * c - Real.log 3 ≤ 1) {w₃' : ℝ}
    (htol : |w₃' - w.2| ≤ η * (Real.exp (-1 / 2) / 2 * Real.log (1 / (2 * c - Real.log 3)))) :
    (OddBandMargin c η w → (w.1, w₃') ∈ oddBandWeights c) ∧
      (EvenBandMargin c η w → (w.1, w₃') ∈ evenBandWeights c) :=
  ⟨fun hw => mem_oddBandWeights_of_margin hw hc (tol_of_log hη hc hδ1 htol),
    fun hw => mem_evenBandWeights_of_margin hw hc (tol_of_log hη hc hδ1 htol)⟩

end GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

end
