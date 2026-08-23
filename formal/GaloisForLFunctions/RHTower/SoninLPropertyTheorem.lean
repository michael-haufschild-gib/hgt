import GaloisForLFunctions.RHTower.SoninLProperty

/-!
# Burnol's Theorem 4.8

For every vector `f` of the extended Sonine space `L_a` the continued Mellin transform

`M(f)(s) = [s(1-s)·M(f)(s)] / (s(1-s))`

satisfies **Burnol's L-Property** (Definition 10): on every vertical strip `A ≤ σ ≤ B` and for every
`ε > 0` one has `M(f)(σ+iτ) = O((1+|τ|)^{(1/2-A)^+ + ε})` away from the two possible poles.

The proof is a Phragmén--Lindelöf interpolation between the two edges of a slightly larger strip
`[A', B']`, `A' = min(A,1/2) - ε/2`, `B' = max(B,1)`:

* on the right edge the Hardy bound gives the numerator `O((1+|τ|)^2)`
  (`exists_norm_numerator_right_line`);
* on the left edge the functional equation together with the sharp line bound for `χ` gives
  `O((1+|τ|)^{2 + (1/2 - A')})` (`exists_norm_numerator_left_line`);
* in the interior the crude estimate gives some polynomial growth
  (`exists_norm_numerator_strip`), which is all Phragmén--Lindelöf needs.

Dividing by `s(1-s)`, whose modulus is at least `|τ|²`, converts the numerator exponent
`2 + (1/2 - A')` into `(1/2-A)^+ + ε/2 ≤ (1/2-A)^+ + ε`.

## Main results

* `extendedMellinContinuation`
* `hasLProperty_extendedMellinContinuation` — **Burnol's Theorem 4.8**
* `exists_hasLProperty_extendedMellin` — the same statement for a vector of `L_a`, with the
  identification with the Mellin integral on `1/2 < Re s < 1`
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The continued Mellin transform of a vector of the extended Sonine space: the entire numerator
`s(1-s)·M(f)(s)` of Proposition 2.2 divided back by `s(1-s)`. -/
def extendedMellinContinuation (a : ℝ) (c d : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  extendedMellinNumerator a c d f s / (s * (1 - s))

/-- On a vertical line at distance at least one from `c₀` the height weight `1+|τ|` is dominated by
twice the distance to `c₀`. -/
theorem rpow_one_add_abs_le_weight {σ c₀ ν : ℝ} (hν : 0 ≤ ν) (hσ : 1 ≤ σ - c₀) {z : ℂ}
    (hz : z.re = σ) : (1 + |z.im|) ^ ν ≤ 2 ^ ν * ‖z - (c₀ : ℂ)‖ ^ ν := by
  have h1 : (1 : ℝ) ≤ ‖z - (c₀ : ℂ)‖ := by
    calc (1 : ℝ) ≤ σ - c₀ := hσ
      _ = (z - (c₀ : ℂ)).re := by rw [Complex.sub_re, Complex.ofReal_re, hz]
      _ ≤ |(z - (c₀ : ℂ)).re| := le_abs_self _
      _ ≤ ‖z - (c₀ : ℂ)‖ := Complex.abs_re_le_norm _
  have h2 : |z.im| ≤ ‖z - (c₀ : ℂ)‖ := by
    have him : (z - (c₀ : ℂ)).im = z.im := by simp
    calc |z.im| = |(z - (c₀ : ℂ)).im| := by rw [him]
      _ ≤ ‖z - (c₀ : ℂ)‖ := Complex.abs_im_le_norm _
  calc (1 + |z.im|) ^ ν ≤ (2 * ‖z - (c₀ : ℂ)‖) ^ ν :=
        Real.rpow_le_rpow (by positivity) (by linarith) hν
    _ = 2 ^ ν * ‖z - (c₀ : ℂ)‖ ^ ν := Real.mul_rpow (by norm_num) (norm_nonneg _)

/-- The positive part identity behind the exponent bookkeeping of Theorem 4.8. -/
theorem half_sub_min (A : ℝ) : 1 / 2 - min A (1 / 2) = max (1 / 2 - A) 0 := by
  rcases le_total A (1 / 2 : ℝ) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

/-- **Burnol's Theorem 4.8.**  The continued Mellin transform of a vector of the extended Sonine
space has the L-Property. -/
theorem hasLProperty_extendedMellinContinuation {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    HasLProperty (extendedMellinContinuation a c d f) := by
  obtain ⟨hdiff, -⟩ := differentiable_extendedMellinNumerator ha hev hc hd
  intro A B ε hε
  set A' : ℝ := min A (1 / 2) - ε / 2 with hA'def
  set B' : ℝ := max B 1 with hB'def
  set c₀ : ℝ := A' - 1 with hc₀def
  set ν : ℝ := 2 + (1 / 2 - A') with hνdef
  have hA'A : A' ≤ A := by
    rw [hA'def]; have := min_le_left A (1 / 2 : ℝ); linarith
  have hA'half : A' < 1 / 2 := by
    rw [hA'def]; have := min_le_right A (1 / 2 : ℝ); linarith
  have hB'B : B ≤ B' := le_max_left _ _
  have hB'one : (1 : ℝ) ≤ B' := le_max_right _ _
  have hB'half : 1 / 2 < B' := by linarith
  have hAB' : A' < B' := by linarith
  have hν0 : (0 : ℝ) ≤ ν := by rw [hνdef]; linarith
  have hν2 : (2 : ℝ) ≤ ν := by rw [hνdef]; linarith
  have hc₀A : c₀ < A' := by rw [hc₀def]; linarith
  have hc₀B : (1 : ℝ) ≤ B' - c₀ := by rw [hc₀def]; linarith
  have hc₀A1 : (1 : ℝ) ≤ A' - c₀ := by rw [hc₀def]; linarith
  clear_value A' B' c₀ ν
  -- the right edge
  obtain ⟨CB0, hCB00, hCB0⟩ := exists_norm_numerator_right_line ha hc hB'half
  have hCB1 : ∀ t : ℝ, (1 : ℝ) ≤ |t| →
      ‖extendedMellinNumerator a c d f ((B' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (CB0 * 2 ^ ν) * ‖((B' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by
    intro t ht
    have hzre : ((B' : ℂ) + (t : ℂ) * Complex.I).re = B' := by simp
    have hzim : ((B' : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have hbase : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h1 : (1 + |t|) ^ (2 : ℝ) ≤ (1 + |t|) ^ ν :=
      Real.rpow_le_rpow_of_exponent_le hbase hν2
    have h2 : (1 + |t|) ^ ν
        ≤ 2 ^ ν * ‖((B' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by
      have h := rpow_one_add_abs_le_weight (σ := B') (c₀ := c₀) hν0 hc₀B hzre
      rwa [hzim] at h
    calc ‖extendedMellinNumerator a c d f ((B' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CB0 * (1 + |t|) ^ (2 : ℝ) := hCB0 t ht
      _ ≤ CB0 * (2 ^ ν * ‖((B' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hCB00
      _ = (CB0 * 2 ^ ν) * ‖((B' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by ring
  obtain ⟨CB, hCB0', hCB⟩ := exists_line_bound_weighted
    (F := extendedMellinNumerator a c d f) hdiff.continuous (σ := B') (c₀ := c₀) (ν := ν)
    (C := CB0 * 2 ^ ν) (T := 1) hν0 hc₀B (by positivity) zero_le_one hCB1
  -- the left edge
  obtain ⟨CA0, hCA00, hCA0⟩ := exists_norm_numerator_left_line ha hev hd hA'half
  have hCA1 : ∀ t : ℝ, (2 : ℝ) ≤ |t| →
      ‖extendedMellinNumerator a c d f ((A' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (CA0 * 2 ^ ν) * ‖((A' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by
    intro t ht
    have hzre : ((A' : ℂ) + (t : ℂ) * Complex.I).re = A' := by simp
    have hzim : ((A' : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have h2 : (1 + |t|) ^ ν
        ≤ 2 ^ ν * ‖((A' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by
      have h := rpow_one_add_abs_le_weight (σ := A') (c₀ := c₀) hν0 hc₀A1 hzre
      rwa [hzim] at h
    calc ‖extendedMellinNumerator a c d f ((A' : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ CA0 * (1 + |t|) ^ ν := by rw [hνdef]; exact hCA0 t ht
      _ ≤ CA0 * (2 ^ ν * ‖((A' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν) :=
          mul_le_mul_of_nonneg_left h2 hCA00
      _ = (CA0 * 2 ^ ν) * ‖((A' : ℂ) + (t : ℂ) * Complex.I) - (c₀ : ℂ)‖ ^ ν := by ring
  obtain ⟨CA, hCA0', hCA⟩ := exists_line_bound_weighted
    (F := extendedMellinNumerator a c d f) hdiff.continuous (σ := A') (c₀ := c₀) (ν := ν)
    (C := CA0 * 2 ^ ν) (T := 2) hν0 hc₀A1 (by positivity) (by norm_num) hCA1
  -- the crude interior bound
  obtain ⟨C0, N0, T0, hC00, hN00, hT01, hC0⟩ := exists_norm_numerator_strip ha hev hc hd A' B'
  obtain ⟨C1, hC10, hC1⟩ := exists_strip_bound_of_high
    (F := extendedMellinNumerator a c d f) hdiff.continuous hN00 hC00 (by linarith)
    (le_of_lt hAB') hC0
  -- Phragmén--Lindelöf
  have hPL := norm_le_mul_rpow_of_vertical_strip (F := extendedMellinNumerator a c d f)
    hAB' hν0 hc₀A hdiff hC10 hN00 hC1 hCA hCB
  set M : ℝ := max CA CB with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_trans hCA0' (le_max_left _ _)
  set K : ℝ := |A'| + |B'| + 1 + |c₀| with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hKν : (0 : ℝ) ≤ K ^ ν := Real.rpow_nonneg hK0.le ν
  clear_value M K
  refine ⟨1, 4 * M * K ^ ν, mul_nonneg (by linarith) hKν, ?_⟩
  intro s hs hsb ht
  set μ : ℝ := max (1 / 2 - A) 0 + ε with hμdef
  clear_value μ
  have hsA' : A' ≤ s.re := le_trans hA'A hs
  have hsB' : s.re ≤ B' := le_trans hsb hB'B
  have habs : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hbase : (1 : ℝ) ≤ 1 + |s.im| := by linarith
  have hs1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hs2 : |s.im| ≤ ‖(1 : ℂ) - s‖ := by
    have him : ((1 : ℂ) - s).im = -s.im := by simp
    have h := Complex.abs_im_le_norm ((1 : ℂ) - s)
    rwa [him, abs_neg] at h
  have hspos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le (by linarith) hs1
  have hs1pos : (0 : ℝ) < ‖(1 : ℂ) - s‖ := lt_of_lt_of_le (by linarith) hs2
  have hweight : ‖s - (c₀ : ℂ)‖ ≤ K * (1 + |s.im|) := by
    have hn := norm_le_of_strip hsA' hsB'
    have hc : ‖(c₀ : ℂ)‖ = |c₀| := Complex.norm_real c₀
    calc ‖s - (c₀ : ℂ)‖ ≤ ‖s‖ + ‖(c₀ : ℂ)‖ := norm_sub_le _ _
      _ ≤ (|A'| + |B'| + 1) * (1 + |s.im|) + |c₀| := by rw [hc]; linarith
      _ ≤ K * (1 + |s.im|) := by
          rw [hKdef]; nlinarith [abs_nonneg c₀, habs]
  have hpow : ‖s - (c₀ : ℂ)‖ ^ ν ≤ K ^ ν * (1 + |s.im|) ^ ν := by
    calc ‖s - (c₀ : ℂ)‖ ^ ν ≤ (K * (1 + |s.im|)) ^ ν :=
          Real.rpow_le_rpow (norm_nonneg _) hweight hν0
      _ = K ^ ν * (1 + |s.im|) ^ ν := Real.mul_rpow hK0.le (by linarith)
  have hνμ : ν ≤ μ + 2 := by
    rw [hνdef, hμdef, hA'def]
    have h := half_sub_min A
    linarith
  have hpow2 : (1 + |s.im|) ^ ν ≤ (1 + |s.im|) ^ (μ + 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase hνμ
  have hsplit : (1 + |s.im|) ^ (μ + 2)
      = (1 + |s.im|) ^ μ * ((1 + |s.im|) * (1 + |s.im|)) := by
    have hb : (0 : ℝ) < 1 + |s.im| := by linarith
    have h2 : (1 + |s.im|) ^ (2 : ℝ) = (1 + |s.im|) * (1 + |s.im|) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [Real.rpow_add hb μ 2, h2]
  have hq : |s.im| * |s.im| ≤ ‖s‖ * ‖(1 : ℂ) - s‖ :=
    mul_le_mul hs1 hs2 habs (norm_nonneg s)
  have hsq : (1 + |s.im|) * (1 + |s.im|) ≤ 4 * (‖s‖ * ‖(1 : ℂ) - s‖) := by
    nlinarith [hq, ht, sq_nonneg (|s.im| - 1)]
  have hμ0 : (0 : ℝ) ≤ (1 + |s.im|) ^ μ := Real.rpow_nonneg (by linarith) μ
  have hGbound : ‖extendedMellinNumerator a c d f s‖
      ≤ 4 * M * K ^ ν * (1 + |s.im|) ^ μ * (‖s‖ * ‖(1 : ℂ) - s‖) := by
    calc ‖extendedMellinNumerator a c d f s‖ ≤ M * ‖s - (c₀ : ℂ)‖ ^ ν := hPL s hsA' hsB'
      _ ≤ M * (K ^ ν * (1 + |s.im|) ^ ν) := mul_le_mul_of_nonneg_left hpow hM0
      _ ≤ M * (K ^ ν * (1 + |s.im|) ^ (μ + 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow2 hKν) hM0
      _ = M * K ^ ν * ((1 + |s.im|) ^ μ * ((1 + |s.im|) * (1 + |s.im|))) := by
          rw [hsplit, ← mul_assoc]
      _ ≤ M * K ^ ν * ((1 + |s.im|) ^ μ * (4 * (‖s‖ * ‖(1 : ℂ) - s‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hμ0)
            (mul_nonneg hM0 hKν)
      _ = 4 * M * K ^ ν * (1 + |s.im|) ^ μ * (‖s‖ * ‖(1 : ℂ) - s‖) := by ring
  simp only [extendedMellinContinuation, norm_div, norm_mul]
  rw [div_le_iff₀ (mul_pos hspos hs1pos)]
  exact hGbound

/-- **Burnol's Theorem 4.8, packaged for a vector of the extended Sonine space.**  For every even
`f ∈ L_a` the Mellin transform continues to a function holomorphic off `{0, 1}` which has the
L-Property, and which agrees with the Mellin integral on the strip `1/2 < Re s < 1`. -/
theorem exists_hasLProperty_extendedMellin {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ M : ℂ → ℂ, HasLProperty M ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ M s) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        M s = ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hf
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hf
  obtain ⟨hdiff, hval⟩ := differentiable_extendedMellinNumerator ha hev hc hd
  refine ⟨extendedMellinContinuation a c d f,
    hasLProperty_extendedMellinContinuation ha hev hc hd, ?_, ?_⟩
  · intro s h0 h1
    refine (hdiff s).div ?_ (mul_ne_zero h0 (sub_ne_zero.2 (fun h => h1 h.symm)))
    exact differentiableAt_id.mul ((differentiableAt_const _).sub differentiableAt_id)
  · intro s hs hs1
    have hne0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith
    have hne1 : s ≠ 1 := by
      intro h
      rw [h] at hs1
      simp at hs1
    have hprod : s * (1 - s) ≠ 0 :=
      mul_ne_zero hne0 (sub_ne_zero.2 (fun h => hne1 h.symm))
    have h := hval s hs hs1
    simp only [extendedMellinContinuation, ← h]
    exact mul_div_cancel_left₀ _ hprod

end RHTower

end
