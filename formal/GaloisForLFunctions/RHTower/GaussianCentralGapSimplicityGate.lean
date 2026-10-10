import GaloisForLFunctions.RHTower.GaussianWeightedGapExtremalParseval
import GaloisForLFunctions.RHTower.GaussianCentralGapFilterLightCone

/-!
# A Gaussian simplicity gate

Let `G(u) = P_½(e^{-u}) − C_½(e^{-u})` and `c_ρ = ½Γ((ρ−½)/2)`.  Index the zeros of `ξ` by their
multiplicity copies `q`.  Under RH the Gaussian Cramér identity (`tendsto_centralGap_meanSquare_of_riemannHypothesis`)
splits exactly (`tendsto_centralGap_meanSquare_eq_diagonal_add_multiplicityExcess`):

  `T⁻¹ ∫₀^T G(u)² du → |A(½)|² + Σ_q |c_q|² + E`,   `E = Σ_{q ≠ q', ρ_q = ρ_{q'}} |c_q|² = Σ_ρ (m_ρ² − m_ρ)|c_ρ|²`.

The diagonal `Σ_q |c_q|² = Σ_ρ m_ρ |c_ρ|²` is linear in the multiplicities, so it is a Weil-type sum.
The excess is a sum of nonnegative quanta, one `|c_ρ|²` for every ordered pair of distinct copies of the
same zero.  It vanishes iff every zero is simple (`multiplicityExcess_eq_zero_iff_injective`).  So the
prime-side mean square of the central Gaussian gap reads, beyond the Weil-type diagonal, exactly the
multiplicity defect of the zeros.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- The multiplicity excess `Σ_{q ≠ q', ρ_q = ρ_{q'}} |c_q|²`. -/
def gaussianMultiplicityExcess : ℝ :=
  ∑' p : XiZeroCopy × XiZeroCopy,
    if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0

theorem zeroBohrAmplitude_eq_of_xiZero_eq {q q' : XiZeroCopy} (h : xiZero q = xiZero q') :
    zeroBohrAmplitude q = zeroBohrAmplitude q' := by
  unfold zeroBohrAmplitude
  rw [h]

theorem summable_zeroBohrAmplitude_pair :
    Summable fun p : XiZeroCopy × XiZeroCopy => ‖zeroBohrAmplitude p.1‖ * ‖zeroBohrAmplitude p.2‖ :=
  Summable.mul_norm (f := fun q => ‖zeroBohrAmplitude q‖) (g := fun q => ‖zeroBohrAmplitude q‖)
    (by simpa using summable_norm_zeroBohrAmplitude)
    (by simpa using summable_norm_zeroBohrAmplitude) |>.congr fun p => by simp

theorem multiplicityExcess_term_le (p : XiZeroCopy × XiZeroCopy) :
    (if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0) ≤
      ‖zeroBohrAmplitude p.1‖ * ‖zeroBohrAmplitude p.2‖ := by
  split_ifs with h
  · rw [sq, zeroBohrAmplitude_eq_of_xiZero_eq h.1]
  · positivity

theorem summable_multiplicityExcess :
    Summable fun p : XiZeroCopy × XiZeroCopy =>
      if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 :=
  Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) multiplicityExcess_term_le
    summable_zeroBohrAmplitude_pair

theorem gaussianMultiplicityExcess_nonneg : 0 ≤ gaussianMultiplicityExcess :=
  tsum_nonneg fun p => by split_ifs <;> positivity

/-- **The excess vanishes iff every zero is simple** (the copy map `q ↦ ρ_q` is injective). -/
theorem multiplicityExcess_eq_zero_iff_injective :
    gaussianMultiplicityExcess = 0 ↔ Function.Injective xiZero := by
  constructor
  · intro h q q' hqq
    by_contra hne
    have hpos : 0 < gaussianMultiplicityExcess := by
      refine summable_multiplicityExcess.tsum_pos (fun p => by split_ifs <;> positivity) (q, q') ?_
      simp only [hqq, ne_eq, hne, not_false_eq_true, and_self, if_true]
      exact pow_pos (norm_pos_iff.2 (zeroBohrAmplitude_ne_zero q)) 2
    linarith
  · intro hinj
    refine (tsum_congr fun p => ?_).trans tsum_zero
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h2 (hinj h1)

/-- Under RH the Parseval pair kernel is `|c_q|²` on pairs of copies of one zero and `0` otherwise. -/
theorem re_parsevalPair_eq_of_riemannHypothesis (hRH : RiemannHypothesis)
    (p : XiZeroCopy × XiZeroCopy) :
    (if xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 then
        zeroBohrAmplitude p.1 * (starRingEnd ℂ) (zeroBohrAmplitude p.2) else 0).re =
      if xiZero p.1 = xiZero p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 := by
  have hre1 : (xiZero p.1).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH p.1
  have hre2 : (xiZero p.2).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH p.2
  have hiff : xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 ↔ xiZero p.1 = xiZero p.2 := by
    rw [sub_eq_zero, xiZeroHalfOrdinate, xiZeroHalfOrdinate]
    constructor
    · intro h
      exact Complex.ext (by rw [hre1, hre2]) (by linarith)
    · intro h; rw [h]
  by_cases h : xiZero p.1 = xiZero p.2
  · rw [if_pos (hiff.2 h), if_pos h, ← zeroBohrAmplitude_eq_of_xiZero_eq h, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, Complex.zero_re]

/-- **Simplicity gate.**  Under RH the mean square of the central Gaussian gap converges to the
archimedean bias, plus the Weil-type diagonal `Σ_q |c_q|²`, plus the multiplicity excess. -/
theorem tendsto_centralGap_meanSquare_eq_diagonal_add_multiplicityExcess (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u))) ^ 2) atTop
      (𝓝 (‖gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ ^ 2 +
        (∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ ^ 2) + gaussianMultiplicityExcess)) := by
  have h := tendsto_centralGap_meanSquare_of_riemannHypothesis hRH
  convert h using 2
  set F : XiZeroCopy × XiZeroCopy → ℂ := fun p =>
    if xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 then
      zeroBohrAmplitude p.1 * (starRingEnd ℂ) (zeroBohrAmplitude p.2) else 0 with hF
  have hFs : Summable F := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      summable_zeroBohrAmplitude_pair)
    simp only [hF]
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
    · rw [norm_zero]; positivity
  set D : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if p.1 = p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 with hD
  set E : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 with hE
  have hsplit : ∀ p, (F p).re = D p + E p := by
    intro p
    rw [hF, re_parsevalPair_eq_of_riemannHypothesis hRH p]
    simp only [hD, hE]
    by_cases h1 : p.1 = p.2
    · rw [if_pos (by rw [h1]), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
    · by_cases h2 : xiZero p.1 = xiZero p.2
      · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
      · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]
  have hDs : Summable D :=
    Summable.of_nonneg_of_le (fun p => by simp only [hD]; split_ifs <;> positivity)
      (fun p => by
        simp only [hD]
        split_ifs with h
        · rw [sq, h]
        · positivity) summable_zeroBohrAmplitude_pair
  have hDsum : ∑' p, D p = ∑' q : XiZeroCopy, ‖zeroBohrAmplitude q‖ ^ 2 := by
    have hinj : Function.Injective fun q : XiZeroCopy => (q, q) := fun a b h => (Prod.mk.inj h).1
    rw [← hinj.tsum_eq (f := D)]
    · exact tsum_congr fun q => by simp [hD]
    · intro p hp
      simp only [Function.mem_support, hD, ne_eq, ite_eq_right_iff, not_forall] at hp
      obtain ⟨h1, -⟩ := hp
      exact ⟨p.1, by rw [Prod.ext_iff]; exact ⟨rfl, h1⟩⟩
  rw [Complex.re_tsum hFs, tsum_congr hsplit, hDs.tsum_add summable_multiplicityExcess, hDsum,
    gaussianMultiplicityExcess]
  ring

/-! ## The unconditional gate at the extremal line -/

/-- The multiplicity excess on the extremal line `Re ρ = Θ`. -/
def extremalMultiplicityExcess : ℝ :=
  ∑' p : XiZeroCopy × XiZeroCopy,
    if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 ∧ (xiZero p.1).re = xiZeroAbscissa then
      ‖zeroBohrAmplitude p.1‖ ^ 2 else 0

theorem summable_extremalMultiplicityExcess :
    Summable fun p : XiZeroCopy × XiZeroCopy =>
      if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 ∧ (xiZero p.1).re = xiZeroAbscissa then
        ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 :=
  Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
    (fun p => by
      split_ifs with h
      · rw [sq, zeroBohrAmplitude_eq_of_xiZero_eq h.1]
      · positivity) summable_zeroBohrAmplitude_pair

theorem extremalMultiplicityExcess_eq_zero_iff :
    extremalMultiplicityExcess = 0 ↔
      ∀ q q' : XiZeroCopy, (xiZero q).re = xiZeroAbscissa → xiZero q = xiZero q' → q = q' := by
  constructor
  · intro h q q' hre hqq
    by_contra hne
    have hpos : 0 < extremalMultiplicityExcess := by
      refine summable_extremalMultiplicityExcess.tsum_pos (fun p => by split_ifs <;> positivity)
        (q, q') ?_
      simp only [hqq, ne_eq, hne, not_false_eq_true, true_and]
      rw [if_pos (by rw [← hqq]; exact hre)]
      exact pow_pos (norm_pos_iff.2 (zeroBohrAmplitude_ne_zero q)) 2
    linarith
  · intro hsimp
    refine (tsum_congr fun p => ?_).trans tsum_zero
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h2 (hsimp p.1 p.2 h3 h1)

/-- **Extremal simplicity gate (unconditional).**  The normalized mean square of the Gaussian gap at
the zero abscissa `Θ` converges to `[Θ = ½]|A(½)|² + Σ_{Re ρ_q = Θ} |c_q|² + E_Θ`, where the excess
`E_Θ = Σ_{Re ρ = Θ} (m_ρ² − m_ρ)|c_ρ|²` vanishes iff every zero on `Re s = Θ` is simple. -/
theorem tendsto_extremalGap_meanSquare_eq_diagonal_add_excess :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ u in (0 : ℝ)..T,
        (Real.exp (-((xiZeroAbscissa - 1 / 2) * u / 2)) *
          (gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
            gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)))) ^ 2) atTop
      (𝓝 (‖(((if xiZeroAbscissa = 1 / 2 then 1 else 0 : ℝ)) : ℂ) *
          gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ)‖ ^ 2 +
        (∑' q : XiZeroCopy, if (xiZero q).re = xiZeroAbscissa then ‖zeroBohrAmplitude q‖ ^ 2 else 0) +
        extremalMultiplicityExcess)) := by
  have h := tendsto_extremalGap_meanSquare
  convert h using 2
  set c : XiZeroCopy → ℂ := fun q =>
    if (xiZero q).re = xiZeroAbscissa then zeroBohrAmplitude q else 0 with hc
  set F : XiZeroCopy × XiZeroCopy → ℂ := fun p =>
    if xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 then
      c p.1 * (starRingEnd ℂ) (c p.2) else 0 with hF
  have hcn : ∀ q, ‖c q‖ ≤ ‖zeroBohrAmplitude q‖ := fun q => by
    simp only [hc]; split_ifs <;> simp
  have hFs : Summable F := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      summable_zeroBohrAmplitude_pair)
    simp only [hF]
    split_ifs
    · rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hcn _) (hcn _) (norm_nonneg _) (norm_nonneg _)
    · rw [norm_zero]; positivity
  set D : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if p.1 = p.2 ∧ (xiZero p.1).re = xiZeroAbscissa then ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 with hD
  set E : XiZeroCopy × XiZeroCopy → ℝ := fun p =>
    if xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 ∧ (xiZero p.1).re = xiZeroAbscissa then
      ‖zeroBohrAmplitude p.1‖ ^ 2 else 0 with hE
  have hsplit : ∀ p, (F p).re = D p + E p := by
    intro p
    simp only [hF, hc, hD, hE]
    by_cases h1 : (xiZero p.1).re = xiZeroAbscissa
    · by_cases h2 : (xiZero p.2).re = xiZeroAbscissa
      · have hiff : xiZeroHalfOrdinate p.1 - xiZeroHalfOrdinate p.2 = 0 ↔
            xiZero p.1 = xiZero p.2 := by
          rw [sub_eq_zero, xiZeroHalfOrdinate, xiZeroHalfOrdinate]
          constructor
          · intro h; exact Complex.ext (by rw [h1, h2]) (by linarith)
          · intro h; rw [h]
        by_cases h3 : xiZero p.1 = xiZero p.2
        · rw [if_pos (hiff.2 h3), if_pos h1, if_pos h2, ← zeroBohrAmplitude_eq_of_xiZero_eq h3,
            Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
          by_cases h4 : p.1 = p.2
          · rw [if_pos ⟨h4, h1⟩, if_neg (fun h => h.2.1 h4), add_zero]
          · rw [if_neg (fun h => h4 h.1), if_pos ⟨h3, h4, h1⟩, zero_add]
        · rw [if_neg (fun h => h3 (hiff.1 h)), Complex.zero_re,
            if_neg (fun h => h3 (by rw [h.1])), if_neg (fun h => h3 h.1), add_zero]
      · have hD0 : ¬ (p.1 = p.2 ∧ (xiZero p.1).re = xiZeroAbscissa) := by
          rintro ⟨h, -⟩; exact h2 (by rw [← h]; exact h1)
        have hE0 : ¬ (xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 ∧ (xiZero p.1).re = xiZeroAbscissa) := by
          rintro ⟨h, -, -⟩; exact h2 (by rw [← h]; exact h1)
        rw [if_neg h2, if_neg hD0, if_neg hE0, add_zero]
        split_ifs <;> simp
    · have hD0 : ¬ (p.1 = p.2 ∧ (xiZero p.1).re = xiZeroAbscissa) := fun h => h1 h.2
      have hE0 : ¬ (xiZero p.1 = xiZero p.2 ∧ p.1 ≠ p.2 ∧ (xiZero p.1).re = xiZeroAbscissa) :=
        fun h => h1 h.2.2
      rw [if_neg h1, if_neg hD0, if_neg hE0, add_zero]
      split_ifs <;> simp
  have hDs : Summable D :=
    Summable.of_nonneg_of_le (fun p => by simp only [hD]; split_ifs <;> positivity)
      (fun p => by
        simp only [hD]
        split_ifs with h
        · rw [sq, h.1]
        · positivity) summable_zeroBohrAmplitude_pair
  have hDsum : ∑' p, D p =
      ∑' q : XiZeroCopy, if (xiZero q).re = xiZeroAbscissa then ‖zeroBohrAmplitude q‖ ^ 2 else 0 := by
    have hinj : Function.Injective fun q : XiZeroCopy => (q, q) := fun a b h => (Prod.mk.inj h).1
    rw [← hinj.tsum_eq (f := D)]
    · exact tsum_congr fun q => by simp [hD]
    · intro p hp
      simp only [Function.mem_support, hD, ne_eq, ite_eq_right_iff, not_forall] at hp
      obtain ⟨⟨h1, -⟩, -⟩ := hp
      exact ⟨p.1, by rw [Prod.ext_iff]; exact ⟨rfl, h1⟩⟩
  rw [Complex.re_tsum hFs, tsum_congr hsplit, hDs.tsum_add summable_extremalMultiplicityExcess,
    hDsum, extremalMultiplicityExcess]
  ring

end

end RHTower
