import GaloisForLFunctions.RHTower.SoninExtendedMellinEdge
import GaloisForLFunctions.RHTower.SoninExtendedMeromorphic
import GaloisForLFunctions.RHTower.ZetaChiLineSharp
import GaloisForLFunctions.RHTower.BurnolChiFactorIdentity
import GaloisForLFunctions.RHTower.LPropertyStrips
import GaloisForLFunctions.HTGeometry.PhragmenLindelofPower

/-!
# Burnol's Theorem 4.8: functions of `L̂_a` have the L-Property

## Main results

* `extendedMellinNumerator_eq_right`, `extendedMellinNumerator_eq_left`
* `extendedMellinNumeratorRight_eq`, `extendedMellinNumeratorLeft_eq` — the numerators as
  `s(1-s)` times the two continuations
* `exists_norm_numerator_right_line` — the right edge bound
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem extendedMellinNumerator_eq_right (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    extendedMellinNumerator a c d f s = extendedMellinNumeratorRight a c d f s := by
  rw [extendedMellinNumerator, glueVert, if_neg (not_lt.2 hs)]

theorem extendedMellinNumerator_eq_left (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    extendedMellinNumerator a c d f s = extendedMellinNumeratorLeft a c d f s := by
  rw [extendedMellinNumerator, glueVert, if_pos hs]

theorem norm_le_of_line {σ t : ℝ} : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (|σ| + 1) * (1 + |t|) := by
  have h1 : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ |σ| + |t| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  nlinarith [abs_nonneg σ, abs_nonneg t]

theorem norm_one_sub_le_of_line {σ t : ℝ} :
    ‖(1 : ℂ) - ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (|σ| + 2) * (1 + |t|) := by
  have h1 := norm_le_of_line (σ := σ) (t := t)
  have h2 : ‖(1 : ℂ) - ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 1 + ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp
  nlinarith [abs_nonneg σ, abs_nonneg t]

/-- **The right edge bound.** -/
theorem exists_norm_numerator_right_line {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    {B' : ℝ} (hB' : 1 / 2 < B') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖extendedMellinNumerator a c d f ((B' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ (2 : ℝ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_mellinTail_bounded ha f (σ₁ := B') (b := B') hB'
  set K : ℝ := |B'| + 2 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  set D : ℝ := ‖d‖ * a ^ ((1 : ℝ) - B') with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  refine ⟨K * K * C₀ + K * D, by positivity, ?_⟩
  intro t ht
  set s : ℂ := (B' : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = B' := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hs2 : 1 / 2 < s.re := by rw [hsre]; exact hB'
  have htail : ‖extendedTailMellin a c f s‖ ≤ C₀ := by
    rw [extendedTailMellin_eq ha hc hs2]
    exact hC₀ s (by rw [hsre]) (by rw [hsre])
  have hsn : ‖s‖ ≤ K * (1 + |t|) := by
    rw [hs]
    refine (norm_le_of_line).trans ?_
    gcongr
    rw [hKdef]
    linarith [abs_nonneg B']
  have hsn1 : ‖(1 : ℂ) - s‖ ≤ K * (1 + |t|) := by
    rw [hs]
    refine (norm_one_sub_le_of_line).trans ?_
    gcongr
  have hhead : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)‖ = D := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha, hDdef]
    congr 2
    rw [Complex.sub_re, Complex.one_re, hsre]
  have hpos : (0 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  rw [extendedMellinNumerator_eq_right a c d f (le_of_lt hs2), extendedMellinNumeratorRight]
  have hsq : (1 + |t|) ^ (2 : ℝ) = (1 + |t|) * (1 + |t|) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc ‖s * (1 - s) * extendedTailMellin a c f s + s * (d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s))‖
      ≤ ‖s * (1 - s) * extendedTailMellin a c f s‖
        + ‖s * (d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s))‖ := norm_add_le _ _
    _ = ‖s‖ * ‖(1 : ℂ) - s‖ * ‖extendedTailMellin a c f s‖
        + ‖s‖ * ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (K * (1 + |t|)) * (K * (1 + |t|)) * C₀ + (K * (1 + |t|)) * D := by
        rw [hhead]
        gcongr
    _ = (K * K * C₀) * ((1 + |t|) * (1 + |t|)) + (K * D) * (1 + |t|) := by ring
    _ ≤ (K * K * C₀ + K * D) * ((1 + |t|) * (1 + |t|)) := by
        have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hK0.le hK0.le) hC₀0) hpos,
          mul_nonneg (mul_nonneg hK0.le hD0) hpos]
    _ = (K * K * C₀ + K * D) * (1 + |t|) ^ (2 : ℝ) := by rw [hsq]

/-! ## The numerators as `s(1-s)` times the continuations -/

theorem extendedMellinNumeratorRight_eq (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s ≠ 1) :
    extendedMellinNumeratorRight a c d f s = s * (1 - s) * extendedMellinRight a c d f s := by
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h
    exact hs (by linear_combination -h)
  rw [extendedMellinNumeratorRight, extendedMellinRight]
  field_simp

theorem extendedMellinNumeratorLeft_eq (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s ≠ 0) :
    extendedMellinNumeratorLeft a c d f s
      = s * (1 - s) * (burnolChiFactor s
        * extendedMellinRight a d c (fourierUnitary f) (1 - s)) := by
  have hone : (1 : ℂ) - (1 - s) = s := by ring
  rw [extendedMellinNumeratorLeft, extendedMellinRight, hone]
  field_simp
  ring


/-- **The left edge bound.** -/
theorem exists_norm_numerator_left_line {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {A' : ℝ} (hA' : A' < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖extendedMellinNumerator a c d f ((A' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|) ^ (2 + (1 / 2 - A')) := by
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hdF : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
    rw [hff]; exact hd
  obtain ⟨Cχ, hCχ0, hCχ⟩ := exists_norm_zetaChi_line_le hA'
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    exists_norm_mellinTail_bounded ha (fourierUnitary f) (σ₁ := 1 - A') (b := 1 - A')
      (by linarith)
  set K : ℝ := |A'| + 2 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  set E : ℝ := ‖c‖ * a ^ A' with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  refine ⟨K * Cχ * (E + K * C₀), by positivity, ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  have hpos : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  set s : ℂ := (A' : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = A' := by rw [hs]; simp
  have hsim : s.im = t := by rw [hs]; simp
  have hsimne : s.im ≠ 0 := by
    rw [hsim]
    intro h
    rw [h] at ht
    norm_num at ht
  have hzre : 1 / 2 < ((1 : ℂ) - s).re := by
    rw [Complex.sub_re, Complex.one_re, hsre]
    linarith
  have hchi : ‖burnolChiFactor s‖ ≤ Cχ * |t| ^ (1 / 2 - A') := by
    rw [burnolChiFactor_eq_zetaChi hsimne, hs]
    exact hCχ t ht
  have h1 : ‖extendedTailMellin a d (fourierUnitary f) (1 - s)‖ ≤ C₀ := by
    rw [extendedTailMellin_eq ha hdF hzre]
    exact hC₀ ((1 : ℂ) - s) (by rw [Complex.sub_re, Complex.one_re, hsre])
      (by rw [Complex.sub_re, Complex.one_re, hsre])
  have hEval : ‖c * ((a : ℝ) : ℂ) ^ s‖ = E := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha, hsre, hEdef]
  have hsn : ‖s‖ ≤ K * (1 + |t|) := by
    rw [hs]
    refine (norm_le_of_line).trans ?_
    gcongr
    rw [hKdef]
    linarith [abs_nonneg A']
  have hsn1 : ‖(1 : ℂ) - s‖ ≤ K * (1 + |t|) := by
    rw [hs]
    refine (norm_one_sub_le_of_line).trans ?_
    gcongr
  have hsum : ‖c * ((a : ℝ) : ℂ) ^ s + s * extendedTailMellin a d (fourierUnitary f) (1 - s)‖
      ≤ (E + K * C₀) * (1 + |t|) := by
    refine (norm_add_le _ _).trans ?_
    rw [hEval, norm_mul]
    have h2 : ‖s‖ * ‖extendedTailMellin a d (fourierUnitary f) (1 - s)‖
        ≤ (K * (1 + |t|)) * C₀ := by
      exact mul_le_mul hsn h1 (norm_nonneg _) (by positivity)
    nlinarith [hE0, hpos, hC₀0, hK0]
  have hchi2 : Cχ * |t| ^ (1 / 2 - A') ≤ Cχ * (1 + |t|) ^ (1 / 2 - A') := by
    refine mul_le_mul_of_nonneg_left ?_ hCχ0.le
    exact Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by linarith)
  have hexp : (1 + |t|) * ((1 + |t|) ^ (1 / 2 - A') * (1 + |t|))
      = (1 + |t|) ^ (2 + (1 / 2 - A')) := by
    have hb : (0 : ℝ) < 1 + |t| := by linarith
    have h2e : (1 + |t|) ^ ((2 : ℝ) + (1 / 2 - A'))
        = (1 + |t|) ^ (2 : ℝ) * (1 + |t|) ^ (1 / 2 - A') := Real.rpow_add hb 2 (1 / 2 - A')
    have hsq : (1 + |t|) ^ (2 : ℝ) = (1 + |t|) * (1 + |t|) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [h2e, hsq]
    ring
  rw [extendedMellinNumerator_eq_left a c d f (by rw [hsre]; exact hA'),
    extendedMellinNumeratorLeft, norm_mul, norm_mul]
  calc ‖(1 : ℂ) - s‖ * ‖burnolChiFactor s‖
        * ‖c * ((a : ℝ) : ℂ) ^ s + s * extendedTailMellin a d (fourierUnitary f) (1 - s)‖
      ≤ (K * (1 + |t|)) * (Cχ * (1 + |t|) ^ (1 / 2 - A')) * ((E + K * C₀) * (1 + |t|)) := by
        gcongr
        · exact le_trans hchi hchi2
    _ = (K * Cχ * (E + K * C₀))
          * ((1 + |t|) * ((1 + |t|) ^ (1 / 2 - A') * (1 + |t|))) := by ring
    _ = K * Cχ * (E + K * C₀) * (1 + |t|) ^ (2 + (1 / 2 - A')) := by rw [hexp]

theorem norm_le_of_strip {A B : ℝ} {s : ℂ} (h1 : A ≤ s.re) (h2 : s.re ≤ B) :
    ‖s‖ ≤ (|A| + |B| + 1) * (1 + |s.im|) := by
  have hn : ‖s‖ ≤ |s.re| + |s.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im s
  have hre : |s.re| ≤ |A| + |B| := by
    rw [abs_le]
    constructor
    · have h3 : -|A| ≤ A := neg_abs_le A
      have h4 : (0 : ℝ) ≤ |B| := abs_nonneg B
      linarith
    · have h3 : B ≤ |B| := le_abs_self B
      have h4 : (0 : ℝ) ≤ |A| := abs_nonneg A
      linarith
  nlinarith [abs_nonneg s.im, abs_nonneg A, abs_nonneg B]

theorem norm_one_sub_le_of_strip {A B : ℝ} {s : ℂ} (h1 : A ≤ s.re) (h2 : s.re ≤ B) :
    ‖(1 : ℂ) - s‖ ≤ (|A| + |B| + 2) * (1 + |s.im|) := by
  have hn := norm_le_of_strip h1 h2
  have h3 : ‖(1 : ℂ) - s‖ ≤ 1 + ‖s‖ := by
    refine (norm_sub_le _ _).trans ?_
    simp
  nlinarith [abs_nonneg s.im, abs_nonneg A, abs_nonneg B]

/-- **The crude interior bound.**  Polynomial vertical growth of the numerator on any strip. -/
theorem exists_norm_numerator_strip {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (A' B' : ℝ) :
    ∃ (C N T : ℝ), 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ T ∧
      ∀ s : ℂ, A' ≤ s.re → s.re ≤ B' → T ≤ |s.im| →
        ‖extendedMellinNumerator a c d f s‖ ≤ C * (1 + |s.im|) ^ N := by
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hdF : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
    rw [hff]; exact hd
  obtain ⟨CR, hCR0, hCR⟩ :=
    exists_norm_extendedMellinRight_le (d := d) ha hc (1 / 2) (max B' 1) (by norm_num)
  obtain ⟨CL, hCL0, hCL⟩ :=
    exists_norm_extendedMellinRight_le (d := c) ha hdF (1 / 2) (max (1 - A') 1) (by norm_num)
  obtain ⟨Tχ, Nχ, Cχ, hCχ0, hCχ⟩ := hasStripPolyGrowthOffReal_zetaChi A' B'
  set K : ℝ := |A'| + |B'| + 2 with hKdef
  have hK0 : 0 < K := by rw [hKdef]; positivity
  refine ⟨K * K * ((K + 1) * (CR + Cχ * CL * (K + 1))), (Nχ : ℝ) + 3, max 1 Tχ,
    by positivity, by positivity, le_max_left _ _, ?_⟩
  intro s hs hsb ht
  have ht1 : (1 : ℝ) ≤ |s.im| := le_trans (le_max_left _ _) ht
  have htχ : Tχ ≤ |s.im| := le_trans (le_max_right _ _) ht
  have hpos : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hsimne : s.im ≠ 0 := by
    intro h
    rw [h] at ht1
    norm_num at ht1
  have hsn : ‖s‖ ≤ K * (1 + |s.im|) := by
    refine (norm_le_of_strip hs hsb).trans ?_
    gcongr
    rw [hKdef]; linarith
  have hsn1 : ‖(1 : ℂ) - s‖ ≤ K * (1 + |s.im|) := by
    refine (norm_one_sub_le_of_strip hs hsb).trans ?_
    gcongr
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at hsimne
    simp at hsimne
  have hne0 : s ≠ 0 := by
    intro h
    rw [h] at hsimne
    simp at hsimne
  have hcube : (1 + |s.im|) ^ ((Nχ : ℝ) + 3)
      = (1 + |s.im|) ^ (Nχ : ℝ) * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|)) := by
    have hb : (0 : ℝ) < 1 + |s.im| := by linarith
    have h3 : (1 + |s.im|) ^ (3 : ℝ) = (1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [Real.rpow_add hb (Nχ : ℝ) 3, h3]
  have hNχ : (1 : ℝ) ≤ (1 + |s.im|) ^ (Nχ : ℝ) := Real.one_le_rpow hpos (by positivity)
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hX0 : (0 : ℝ) ≤ Cχ * CL * (K + 1) := mul_nonneg (mul_nonneg hCχ0 hCL0) hK1
  have hKK : (0 : ℝ) ≤ K * K := mul_nonneg hK0.le hK0.le
  have hBig : (0 : ℝ) ≤ K * K * ((K + 1) * (CR + Cχ * CL * (K + 1))) :=
    mul_nonneg hKK (mul_nonneg hK1 (by linarith))
  rcases le_or_gt (1 / 2 : ℝ) s.re with hhalf | hhalf
  · -- right of the critical line
    have hval := hCR s hhalf (le_trans hsb (le_max_left _ _)) ht1
    have hns : (1 : ℝ) + ‖s‖ ≤ (K + 1) * (1 + |s.im|) := by nlinarith [hsn, hpos, hK0]
    rw [extendedMellinNumerator_eq_right a c d f hhalf, extendedMellinNumeratorRight_eq a c d f hne1,
      norm_mul, norm_mul]
    calc ‖s‖ * ‖(1 : ℂ) - s‖ * ‖extendedMellinRight a c d f s‖
        ≤ (K * (1 + |s.im|)) * (K * (1 + |s.im|)) * (CR * ((K + 1) * (1 + |s.im|))) := by
          gcongr
          exact hval.trans (mul_le_mul_of_nonneg_left hns hCR0)
      _ = (K * K * ((K + 1) * CR)) * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|)) := by ring
      _ ≤ (K * K * ((K + 1) * (CR + Cχ * CL * (K + 1))))
            * ((1 + |s.im|) ^ (Nχ : ℝ)
              * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|))) := by
          have hprod : (0 : ℝ) ≤ (1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|) := by positivity
          have hcoef : K * K * ((K + 1) * CR)
              ≤ K * K * ((K + 1) * (CR + Cχ * CL * (K + 1))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith) hK1) hKK
          exact mul_le_mul hcoef (le_mul_of_one_le_left hprod hNχ) hprod hBig
      _ = (K * K * ((K + 1) * (CR + Cχ * CL * (K + 1)))) * (1 + |s.im|) ^ ((Nχ : ℝ) + 3) := by
          rw [hcube]
  · -- left of the critical line
    have hzre : (1 : ℝ) / 2 ≤ ((1 : ℂ) - s).re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    have hzb : ((1 : ℂ) - s).re ≤ max (1 - A') 1 := by
      rw [Complex.sub_re, Complex.one_re]
      exact le_trans (by linarith) (le_max_left _ _)
    have hzim : (1 : ℝ) ≤ |((1 : ℂ) - s).im| := by
      have him : ((1 : ℂ) - s).im = -s.im := by simp
      rw [him, abs_neg]; exact ht1
    have hvalL := hCL ((1 : ℂ) - s) hzre hzb hzim
    have hchi : ‖burnolChiFactor s‖ ≤ Cχ * (1 + |s.im|) ^ Nχ := by
      rw [burnolChiFactor_eq_zetaChi hsimne]
      exact hCχ s hs hsb htχ
    have hns1 : (1 : ℝ) + ‖(1 : ℂ) - s‖ ≤ (K + 1) * (1 + |s.im|) := by
      nlinarith [hsn1, hpos, hK0]
    rw [extendedMellinNumerator_eq_left a c d f hhalf, extendedMellinNumeratorLeft_eq a c d f hne0,
      norm_mul, norm_mul, norm_mul]
    have hchiN : (1 + |s.im|) ^ Nχ = (1 + |s.im|) ^ (Nχ : ℝ) := (Real.rpow_natCast _ Nχ).symm
    calc ‖s‖ * ‖(1 : ℂ) - s‖
          * (‖burnolChiFactor s‖ * ‖extendedMellinRight a d c (fourierUnitary f) (1 - s)‖)
        ≤ (K * (1 + |s.im|)) * (K * (1 + |s.im|))
            * ((Cχ * (1 + |s.im|) ^ (Nχ : ℝ)) * (CL * ((K + 1) * (1 + |s.im|)))) := by
          gcongr
          · rw [← hchiN]; exact hchi
          · exact hvalL.trans (mul_le_mul_of_nonneg_left hns1 hCL0)
      _ = (K * K * (Cχ * CL * (K + 1)))
            * ((1 + |s.im|) ^ (Nχ : ℝ) * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|))) := by ring
      _ ≤ (K * K * ((K + 1) * (CR + Cχ * CL * (K + 1))))
            * ((1 + |s.im|) ^ (Nχ : ℝ)
              * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|))) := by
          have hprod : (0 : ℝ) ≤ (1 + |s.im|) ^ (Nχ : ℝ)
              * ((1 + |s.im|) * (1 + |s.im|) * (1 + |s.im|)) := by positivity
          have hXX : Cχ * CL * (K + 1) ≤ (K + 1) * (CR + Cχ * CL * (K + 1)) := by
            have hexp : (K + 1) * (CR + Cχ * CL * (K + 1))
                = (K + 1) * CR + K * (Cχ * CL * (K + 1)) + Cχ * CL * (K + 1) := by ring
            have h1 : (0 : ℝ) ≤ (K + 1) * CR := mul_nonneg hK1 hCR0
            have h2 : (0 : ℝ) ≤ K * (Cχ * CL * (K + 1)) := mul_nonneg hK0.le hX0
            rw [hexp]; linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXX hKK) hprod
      _ = (K * K * ((K + 1) * (CR + Cχ * CL * (K + 1)))) * (1 + |s.im|) ^ ((Nχ : ℝ) + 3) := by
          rw [hcube]

end RHTower

end
