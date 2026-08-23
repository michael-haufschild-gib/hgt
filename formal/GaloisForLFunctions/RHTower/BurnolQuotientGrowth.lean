import GaloisForLFunctions.RHTower.BurnolQuotientEntire
import GaloisForLFunctions.RHTower.MellinHalfPlaneBound
import GaloisForLFunctions.RHTower.BurnolReflectionStability
import GaloisForLFunctions.RHTower.BurnolResidueSeries
import GaloisForLFunctions.HTGeometry.RectangleMaxModulus

/-!
# Polynomial growth of the entire quotient

The entire representative `θ` of `M(f)/ζ` is:

* bounded on `Re s ≥ 2` — the aperture bound with `a ≥ 1` plus `‖1/ζ‖ ≤ 4`;
* bounded on `Re s ≤ −1` — by the functional equation, which reflects that half-plane onto the
  first one for the Fourier-transformed datum;
* polynomially bounded on the selected horizontal lines `Im s = ±T_n` — Theorem 4.8's `L`-property
  for `M(f)` and Proposition 5.1 for `1/ζ`.

The maximum modulus principle on the rectangles `[−1,2] × [−T_n, T_n]` then gives polynomial growth
on all of `ℂ`.  **This is the elementary replacement for Krein's theorem** in the `a = 1` case of
Burnol's Proposition 6.1.

## Main results

* `exists_height_between`
* `burnolQuotient_reflect_of_im_ne`
* `exists_polyGrowth_burnolQuotientNF`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Choosing a selected height just above a given one -/

theorem exists_height_between {T : ℕ → ℝ} (htop : Tendsto T atTop atTop)
    (hspace : ∀ k : ℕ, T (k + 1) ≤ T k + 3) (h : ℝ) :
    ∃ n : ℕ, h ≤ T n ∧ T n ≤ max (T 0) (h + 3) := by
  classical
  by_cases h0 : h ≤ T 0
  · exact ⟨0, h0, le_max_left _ _⟩
  · push Not at h0
    have hex : ∃ n : ℕ, h ≤ T n := by
      obtain ⟨n, hn⟩ := (htop.eventually_ge_atTop h).exists
      exact ⟨n, hn⟩
    classical
    set n : ℕ := Nat.find hex with hndef
    have hn : h ≤ T n := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro hzero
      rw [hzero] at hn
      linarith
    obtain ⟨m, hm_eq⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : ¬ (h ≤ T m) := Nat.find_min hex (by omega)
    push Not at hm
    refine ⟨n, hn, ?_⟩
    rw [hm_eq]
    refine le_trans (hspace m) ?_
    refine le_trans ?_ (le_max_right (T 0) (h + 3))
    linarith

/-! ## The reflection off the real axis -/

theorem burnolQuotient_reflect_of_im_ne (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) (him : s.im ≠ 0) :
    burnolQuotient (extendedMellinContinuation a c d f) s
      = burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f)) (1 - s) := by
  have hint : ∀ m : ℤ, s ≠ (m : ℂ) := by
    intro m hm
    have := congrArg Complex.im hm
    simp at this
    exact him this
  have hchi : burnolChiFactor s ≠ 0 := burnolChiFactor_ne_zero hint
  have hzeta : riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) :=
    riemannZeta_eq_burnolChiFactor_mul_one_sub hint
  have hmel : extendedMellinContinuation a c d f s
      = burnolChiFactor s * extendedMellinContinuation a d c (fourierUnitary f) (1 - s) :=
    extendedMellinContinuation_reflect a c d f hs
  rw [burnolQuotient, burnolQuotient, hmel, hzeta, mul_inv]
  field_simp

/-! ## The two half-planes -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

theorem meromorphicAt_extendedMellin_all (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ∀ s : ℂ, MeromorphicAt (extendedMellinContinuation a c d f) s :=
  fun s => meromorphicAt_extendedMellinContinuation ha hev hc hd s

/-- **Boundedness on the right half-plane.** -/
theorem exists_bound_burnolQuotientNF_right (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖burnolQuotientNF (extendedMellinContinuation a c d f) s‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨C, hC0, hCb⟩ := exists_norm_extendedMellin_halfPlane_le ha0 hev hc hd
  refine ⟨4 * C, by positivity, ?_⟩
  intro s hs
  have hζne : riemannZeta s ≠ 0 := by
    have h := norm_riemannZeta_ge_of_two_le_re (s := s) hs
    intro hzero
    rw [hzero] at h
    simp at h
    linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation a c d f)) s :=
    analyticAt_burnolQuotient
      (analyticAt_extendedMellinContinuation_of_ne ha0 hev hc hd hs0 hs1) hζne hs1
  rw [burnolQuotientNF_eq_of_analyticAt (meromorphicAt_extendedMellin_all ha0 hev hc hd) hana,
    burnolQuotient, norm_mul]
  have h1 := hCb s hs
  have h2 : ‖(riemannZeta s)⁻¹‖ ≤ 4 := norm_zeta_inv_le_of_two_le_re hs
  have hapow : a ^ (-s.re) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos ha ?_
    linarith
  have hM0 : (0:ℝ) ≤ ‖extendedMellinContinuation a c d f s‖ := norm_nonneg _
  have hi0 : (0:ℝ) ≤ ‖(riemannZeta s)⁻¹‖ := norm_nonneg _
  have hMle : ‖extendedMellinContinuation a c d f s‖ ≤ C := by
    refine le_trans h1 ?_
    nlinarith [hC0]
  nlinarith [hMle, h2, hM0, hi0, hC0]

/-- **Boundedness on the left half-plane**, through the functional equation. -/
theorem exists_bound_burnolQuotientNF_left (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hdvd : ∀ z : ℂ, 0 ≤ meromorphicOrderAt
      (burnolQuotient (extendedMellinContinuation a c d f)) z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ≤ -1 →
      ‖burnolQuotientNF (extendedMellinContinuation a c d f) s‖ ≤ C := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hev' : fourierUnitary f ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have hc' := fourierUnitary_band_of_reflect hev hd
  obtain ⟨C, hC0, hCb⟩ := exists_norm_extendedMellin_halfPlane_le (b := a)
    (g := fourierUnitary f) (c := d) (d := c) ha0 hev' hc' hc
  refine ⟨4 * C, by positivity, ?_⟩
  have hdiff : Differentiable ℂ (burnolQuotientNF (extendedMellinContinuation a c d f)) :=
    differentiable_burnolQuotientNF (meromorphicAt_extendedMellin_all ha0 hev hc hd) hdvd
  -- first off the real axis
  have hoff : ∀ s : ℂ, s.re ≤ -1 → s.im ≠ 0 →
      ‖burnolQuotientNF (extendedMellinContinuation a c d f) s‖ ≤ 4 * C := by
    intro s hs him
    have hζne : riemannZeta s ≠ 0 := by
      intro hzero
      rcases riemannZeta_zero_trivial_or_mem_strip hzero with ⟨n, hn⟩ | ⟨h1, -⟩
      · have := congrArg Complex.im hn
        simp at this
        exact him this
      · linarith
    have hs1 : s ≠ 1 := by
      intro h; rw [h] at hs; simp at hs; linarith
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at him; simp at him
    have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation a c d f)) s :=
      analyticAt_burnolQuotient
        (analyticAt_extendedMellinContinuation_of_ne ha0 hev hc hd hs0 hs1) hζne hs1
    rw [burnolQuotientNF_eq_of_analyticAt (meromorphicAt_extendedMellin_all ha0 hev hc hd) hana]
    rw [burnolQuotient_reflect_of_im_ne a c d f (by linarith) him, burnolQuotient, norm_mul]
    have hre : ((1 : ℂ) - s).re = 1 - s.re := by simp
    have h2re : (2:ℝ) ≤ ((1 : ℂ) - s).re := by rw [hre]; linarith
    have h1 := hCb ((1 : ℂ) - s) h2re
    have h2 : ‖(riemannZeta ((1 : ℂ) - s))⁻¹‖ ≤ 4 := norm_zeta_inv_le_of_two_le_re h2re
    have hapow : a ^ (-((1 : ℂ) - s).re) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ha ?_
      rw [hre]
      linarith
    have hM0 : (0:ℝ) ≤ ‖extendedMellinContinuation a d c (fourierUnitary f) ((1 : ℂ) - s)‖ :=
      norm_nonneg _
    have hi0 : (0:ℝ) ≤ ‖(riemannZeta ((1 : ℂ) - s))⁻¹‖ := norm_nonneg _
    have hMle : ‖extendedMellinContinuation a d c (fourierUnitary f) ((1 : ℂ) - s)‖ ≤ C := by
      refine le_trans h1 ?_
      nlinarith [hC0]
    nlinarith [hMle, h2, hM0, hi0, hC0]
  -- then on the real axis, by continuity
  intro s hs
  rcases eq_or_ne s.im 0 with him | him
  · set u : ℕ → ℂ := fun n => s + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hudef
    have hure : ∀ n : ℕ, (u n).re = s.re := by
      intro n; rw [hudef]; simp
    have huim : ∀ n : ℕ, (u n).im ≠ 0 := by
      intro n
      rw [hudef]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_one, mul_zero, add_zero, zero_add, him]
      positivity
    have hutend : Tendsto u atTop (𝓝 s) := by
      have hreal : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (0:ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcx : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 (0:ℂ)) := by
        have hcont : Continuous (fun x : ℝ => ((x : ℝ) : ℂ) * I) := by fun_prop
        have hcomp := (hcont.tendsto (0:ℝ)).comp hreal
        simpa [Function.comp_def] using hcomp
      have := (tendsto_const_nhds (x := s) (f := (atTop : Filter ℕ))).add hcx
      simpa [hudef] using this
    have hlim := (hdiff.continuous.continuousAt (x := s)).tendsto.comp hutend
    have hbd : ∀ n : ℕ,
        ‖burnolQuotientNF (extendedMellinContinuation a c d f) (u n)‖ ≤ 4 * C := by
      intro n
      exact hoff (u n) (by rw [hure n]; exact hs) (huim n)
    exact le_of_tendsto (hlim.norm) (Filter.Eventually.of_forall hbd)
  · exact hoff s hs him

/-! ## The selected horizontal lines -/

/-- **Polynomial bound on the selected horizontal lines.** -/
theorem exists_bound_burnolQuotientNF_horizontal (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    (hTne : ∀ k : ℕ, ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0)
    (hzeta : ∀ b : ℝ, 2 ≤ b → ∃ (C A : ℝ) (k₀ : ℕ), 0 < C ∧ 0 < A ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
        ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A) :
    ∃ (C : ℝ) (D k₀ : ℕ), 0 ≤ C ∧ ∀ k : ℕ, k₀ ≤ k → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 →
      (s.im = T k ∨ s.im = -T k) →
      ‖burnolQuotientNF (extendedMellinContinuation a c d f) s‖ ≤ C * (1 + T k) ^ D := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨TL, CL, hCL0, hLb⟩ :=
    (hasLProperty_extendedMellinContinuation ha0 hev hc hd) (-1) 2 1 one_pos
  obtain ⟨Cz, A, kz, hCz0, hA0, hzb⟩ := hzeta 2 (le_refl 2)
  obtain ⟨kT, hkT⟩ := (htop.eventually_ge_atTop TL).exists_forall_of_atTop
  refine ⟨CL * Cz, ⌈max (1 / 2 - (-1)) 0 + 1 + A⌉₊, max kz kT, by positivity, ?_⟩
  intro k hk s hs1 hs2 him
  have hkz : kz ≤ k := le_trans (le_max_left _ _) hk
  have hkT' : kT ≤ k := le_trans (le_max_right _ _) hk
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hTL : TL ≤ T k := hkT k hkT'
  have habs : |s.im| = T k := by
    rcases him with h | h
    · rw [h, abs_of_pos hTk0]
    · rw [h, abs_neg, abs_of_pos hTk0]
  -- the point is the standard one on the line
  have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hζne : riemannZeta s ≠ 0 := by
    rcases him with h | h
    · rw [hsplit, h]
      exact hTne k s.re hs1 hs2
    · rw [hsplit, h]
      have hbase := hTne k s.re hs1 hs2
      have := riemannZeta_ne_zero_neg_height (σ := s.re) (t := T k) hbase
      simpa using this
  have hs1' : s ≠ 1 := by
    intro h
    rw [h] at habs
    simp at habs
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at habs
    simp at habs
    linarith
  have hana : AnalyticAt ℂ (burnolQuotient (extendedMellinContinuation a c d f)) s :=
    analyticAt_burnolQuotient
      (analyticAt_extendedMellinContinuation_of_ne ha0 hev hc hd hs0 hs1') hζne hs1'
  rw [burnolQuotientNF_eq_of_analyticAt (meromorphicAt_extendedMellin_all ha0 hev hc hd) hana,
    burnolQuotient, norm_mul]
  have hM := hLb s hs1 hs2 (by rw [habs]; exact hTL)
  rw [habs] at hM
  have hz : ‖(riemannZeta s)⁻¹‖ ≤ Cz * (T k) ^ A := by
    rcases him with h | h
    · rw [hsplit, h]
      exact hzb k hkz s.re (by linarith) (by linarith)
    · rw [hsplit, h]
      have hbase := hzb k hkz s.re (by linarith) (by linarith)
      rw [show ((-T k : ℝ) : ℂ) = ((-(T k) : ℝ) : ℂ) by push_cast; ring,
        norm_zeta_inv_neg_height]
      exact hbase
  -- combine
  set ν : ℝ := max (1 / 2 - (-1)) 0 + 1 with hνdef
  have hbase1 : (1 : ℝ) ≤ 1 + T k := by linarith
  have hpow : (1 + T k) ^ ν * (T k) ^ A ≤ (1 + T k) ^ (⌈ν + A⌉₊ : ℕ) := by
    have h1 : (T k) ^ A ≤ (1 + T k) ^ A :=
      Real.rpow_le_rpow (le_of_lt hTk0) (by linarith) hA0.le
    have h2 : (1 + T k) ^ ν * (1 + T k) ^ A = (1 + T k) ^ (ν + A) := by
      rw [← Real.rpow_add (by linarith)]
    have h3 : (1 + T k) ^ (ν + A) ≤ (1 + T k) ^ ((⌈ν + A⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase1 (Nat.le_ceil _)
    have h4 : (1 + T k) ^ ((⌈ν + A⌉₊ : ℕ) : ℝ) = (1 + T k) ^ (⌈ν + A⌉₊ : ℕ) :=
      Real.rpow_natCast _ _
    calc (1 + T k) ^ ν * (T k) ^ A
        ≤ (1 + T k) ^ ν * (1 + T k) ^ A := by
          refine mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + T k) ^ (ν + A) := h2
      _ ≤ (1 + T k) ^ ((⌈ν + A⌉₊ : ℕ) : ℝ) := h3
      _ = (1 + T k) ^ (⌈ν + A⌉₊ : ℕ) := h4
  calc ‖extendedMellinContinuation a c d f s‖ * ‖(riemannZeta s)⁻¹‖
      ≤ (CL * (1 + T k) ^ ν) * (Cz * (T k) ^ A) := by
        refine mul_le_mul hM hz (norm_nonneg _) (by positivity)
    _ = CL * Cz * ((1 + T k) ^ ν * (T k) ^ A) := by ring
    _ ≤ CL * Cz * (1 + T k) ^ (⌈ν + A⌉₊ : ℕ) := by
        refine mul_le_mul_of_nonneg_left hpow (by positivity)

end

end RHTower
