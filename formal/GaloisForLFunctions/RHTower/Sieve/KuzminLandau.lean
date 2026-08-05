import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation

/-!
# The Kuzmin–Landau inequality, band form

If the increments of a real phase sequence are monotone and confined to one band
`[δ, 1−δ]` modulo one, the exponential sum over the sequence is bounded by `3/(2δ) + 1`,
uniformly in its length.

The proof is summation by parts against the coefficients `(e(β)−1)^{-1}`.  These have
constant real part `−1/2` and imaginary part `−cot(πβ)/2`, so along a monotone increment
sequence their total variation telescopes to a single cotangent difference — no integral
and no derivative enters.
-/

namespace RHTower.Sieve

open Real

/-- The sine is positive on the open unit band. -/
theorem sin_pi_mul_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) : 0 < Real.sin (Real.pi * β) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])

/-- Jordan's bound on the whole band: the sine exceeds twice the distance to the edge. -/
theorem two_mul_le_sin_pi_mul {β δ : ℝ} (hδ0 : 0 < δ) (hb : δ ≤ β) (hb' : β ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * β) := by
  have hpi := Real.pi_pos
  rcases le_or_gt β (1/2) with hhalf | hhalf
  · have hnn : 0 ≤ Real.pi * β := by nlinarith
    have hle : Real.pi * β ≤ Real.pi / 2 := by nlinarith
    have hj := Real.mul_le_sin hnn hle
    have heq : 2 / Real.pi * (Real.pi * β) = 2 * β := by field_simp
    rw [heq] at hj
    linarith
  · have hnn : 0 ≤ Real.pi * (1 - β) := by nlinarith
    have hle : Real.pi * (1 - β) ≤ Real.pi / 2 := by nlinarith
    have hj := Real.mul_le_sin hnn hle
    have heq : 2 / Real.pi * (Real.pi * (1 - β)) = 2 * (1 - β) := by field_simp
    rw [heq] at hj
    have hsub : Real.sin (Real.pi * β) = Real.sin (Real.pi * (1 - β)) := by
      rw [show Real.pi * (1 - β) = Real.pi - Real.pi * β by ring, Real.sin_pi_sub]
    rw [hsub]
    linarith

/-- The cotangent is antitone across the band. -/
theorem cot_pi_mul_antitone {x y δ : ℝ} (hδ0 : 0 < δ)
    (hx : δ ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 - δ) :
    Real.cos (Real.pi * y) / Real.sin (Real.pi * y)
      ≤ Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx
  have hx1 : x < 1 := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hy1 : y < 1 := by linarith
  have hsx := sin_pi_mul_pos hx0 hx1
  have hsy := sin_pi_mul_pos hy0 hy1
  have hkey : Real.cos (Real.pi * x) * Real.sin (Real.pi * y)
      - Real.cos (Real.pi * y) * Real.sin (Real.pi * x)
      = Real.sin (Real.pi * y - Real.pi * x) := by
    rw [Real.sin_sub]
    ring
  have hdiff : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  rw [div_le_div_iff₀ hsy hsx]
  nlinarith [hkey, hdiff]

/-- The cotangent on the band is at most `1/(2δ)`. -/
theorem cot_pi_mul_le {β δ : ℝ} (hδ0 : 0 < δ)
    (hb : δ ≤ β) (hb' : β ≤ 1 - δ) :
    Real.cos (Real.pi * β) / Real.sin (Real.pi * β) ≤ 1 / (2 * δ) := by
  have hs := two_mul_le_sin_pi_mul hδ0 hb hb'
  have hs0 : 0 < Real.sin (Real.pi * β) :=
    sin_pi_mul_pos (lt_of_lt_of_le hδ0 hb) (by linarith)
  have hcos : Real.cos (Real.pi * β) ≤ 1 := Real.cos_le_one _
  have h1 : Real.cos (Real.pi * β) / Real.sin (Real.pi * β)
      ≤ 1 / Real.sin (Real.pi * β) :=
    div_le_div_of_nonneg_right hcos hs0.le
  have h2 : 1 / Real.sin (Real.pi * β) ≤ 1 / (2 * δ) :=
    one_div_le_one_div_of_le (by positivity) hs
  linarith

/-- The Kuzmin–Landau coefficient `−1/2 − i·cot(πβ)/2`. -/
noncomputable def klCoeff (β : ℝ) : ℂ :=
  -(1/2 : ℂ) - Complex.I / 2
    * ((Real.cos (Real.pi * β) / Real.sin (Real.pi * β) : ℝ) : ℂ)

/-- The coefficient inverts the phase chord. -/
theorem klCoeff_mul {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    klCoeff β * (Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1) = 1 := by
  have hs := sin_pi_mul_pos h0 h1
  set S : ℂ := ((Real.sin (Real.pi * β) : ℝ) : ℂ) with hSdef
  set C : ℂ := ((Real.cos (Real.pi * β) : ℝ) : ℂ) with hCdef
  have hSne : S ≠ 0 := by
    rw [hSdef]
    exact_mod_cast hs.ne'
  have hklc : klCoeff β = -(1/2 : ℂ) - Complex.I / 2 * (C / S) := by
    rw [klCoeff, Complex.ofReal_div, hSdef, hCdef]
  have hexp : Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (2 * Real.pi * β) : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * β) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc2 : Real.cos (2 * Real.pi * β) = 1 - 2 * Real.sin (Real.pi * β) ^ 2 := by
    have h := Real.cos_two_mul' (Real.pi * β)
    rw [show 2 * (Real.pi * β) = 2 * Real.pi * β by ring] at h
    linarith [Real.sin_sq_add_cos_sq (Real.pi * β)]
  have hs2 : Real.sin (2 * Real.pi * β)
      = 2 * Real.sin (Real.pi * β) * Real.cos (Real.pi * β) := by
    have h := Real.sin_two_mul (Real.pi * β)
    rw [show 2 * (Real.pi * β) = 2 * Real.pi * β by ring] at h
    exact h
  have hfact : Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1
      = 2 * S * (-S + C * Complex.I) := by
    rw [hexp, hc2, hs2]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_one, Complex.ofReal_ofNat, hSdef, hCdef]
    ring_nf
  have hpy : S ^ 2 + C ^ 2 = 1 := by
    rw [hSdef, hCdef]
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * β)
  rw [hklc, hfact]
  have hexpand : (-(1/2 : ℂ) - Complex.I / 2 * (C / S)) * (2 * S * (-S + C * Complex.I))
      = S ^ 2 - Complex.I ^ 2 * C ^ 2 := by
    field_simp
    ring
  rw [hexpand]
  linear_combination (-(C ^ 2)) * Complex.I_sq + hpy

/-- The coefficient's norm is at most `1/(4δ)` on the band. -/
theorem norm_klCoeff_le {β δ : ℝ} (hδ0 : 0 < δ)
    (hb : δ ≤ β) (hb' : β ≤ 1 - δ) :
    ‖klCoeff β‖ ≤ 1 / (4 * δ) := by
  have h0 : 0 < β := lt_of_lt_of_le hδ0 hb
  have h1 : β < 1 := by linarith
  have hmul := klCoeff_mul h0 h1
  have hchord : 4 * δ ≤ ‖Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1‖ := by
    rw [norm_exp_I_sub_one]
    rw [show (2 * Real.pi * β : ℝ) / 2 = Real.pi * β by ring]
    have hsin := two_mul_le_sin_pi_mul hδ0 hb hb'
    have habs : Real.sin (Real.pi * β) ≤ |Real.sin (Real.pi * β)| := le_abs_self _
    linarith
  have hnorm : ‖klCoeff β‖
      * ‖Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hk : 0 ≤ ‖klCoeff β‖ := norm_nonneg _
  have hδ4 : 0 < 4 * δ := by positivity
  rw [le_div_iff₀ hδ4]
  calc ‖klCoeff β‖ * (4 * δ)
      ≤ ‖klCoeff β‖ * ‖Complex.exp (((2 * Real.pi * β : ℝ) : ℂ) * Complex.I) - 1‖ :=
        mul_le_mul_of_nonneg_left hchord hk
    _ = 1 := hnorm

/-- Coefficient differences are purely imaginary cotangent differences. -/
theorem norm_klCoeff_sub (x y : ℝ) :
    ‖klCoeff y - klCoeff x‖
      = |Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
          - Real.cos (Real.pi * y) / Real.sin (Real.pi * y)| / 2 := by
  have hdiff : klCoeff y - klCoeff x
      = Complex.I / 2
        * (((Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
            - Real.cos (Real.pi * y) / Real.sin (Real.pi * y) : ℝ)) : ℂ) := by
    rw [klCoeff, klCoeff]
    push_cast
    ring
  have hI2 : ‖Complex.I / 2‖ = 1/2 := by
    rw [norm_div, Complex.norm_I]
    norm_num
  have hr : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hdiff, norm_mul, hI2, hr]
  ring

/-- **The Kuzmin–Landau inequality, band form.**  A phase sequence with monotone increments
confined to `[δ, 1−δ]` has exponential sum at most `3/(2δ) + 1`, uniformly in the length. -/
theorem kuzminLandau_band (φ : ℕ → ℝ) (M : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hlo : ∀ m < M, δ ≤ φ (m+1) - φ m) (hhi : ∀ m < M, φ (m+1) - φ m ≤ 1 - δ)
    (hmono : ∀ m, m + 1 < M → φ (m+1) - φ m ≤ φ (m+2) - φ (m+1)) :
    ‖∑ m ∈ Finset.range (M+1),
        Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)‖ ≤ 3/(2*δ) + 1 := by
  classical
  have hEnorm : ∀ m : ℕ,
      ‖Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)‖ = 1 := fun m =>
    Complex.norm_exp_ofReal_mul_I _
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    rw [Finset.sum_range_one, hEnorm 0]
    have : 0 < 3/(2*δ) := by positivity
    linarith
  set E : ℕ → ℂ := fun m => Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)
    with hE
  set c : ℕ → ℂ := fun m => klCoeff (φ (m+1) - φ m) with hc
  set g : ℕ → ℝ := fun m => Real.cos (Real.pi * (φ (m+1) - φ m))
      / Real.sin (Real.pi * (φ (m+1) - φ m)) with hg
  have hstep : ∀ m < M, E m = c m * (E (m+1) - E m) := by
    intro m hm
    have hb0 : 0 < φ (m+1) - φ m := lt_of_lt_of_le hδ0 (hlo m hm)
    have hb1 : φ (m+1) - φ m < 1 := by
      have := hhi m hm
      linarith
    have hshift : E (m+1)
        = E m * Complex.exp (((2 * Real.pi * (φ (m+1) - φ m) : ℝ) : ℂ) * Complex.I) := by
      simp only [hE]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hkl := klCoeff_mul hb0 hb1
    simp only [hc]
    rw [hshift]
    calc E m = E m * (klCoeff (φ (m+1) - φ m)
        * (Complex.exp (((2 * Real.pi * (φ (m+1) - φ m) : ℝ) : ℂ) * Complex.I) - 1)) := by
          rw [hkl, mul_one]
      _ = klCoeff (φ (m+1) - φ m)
          * (E m * Complex.exp (((2 * Real.pi * (φ (m+1) - φ m) : ℝ) : ℂ) * Complex.I)
              - E m) := by ring
  have hsplit : ∑ m ∈ Finset.range (M+1), E m
      = ∑ m ∈ Finset.range M, c m * (E (m+1) - E m) + E M := by
    rw [Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun m hm => hstep m (Finset.mem_range.mp hm)
  -- summation by parts (mathlib partial-sum form, applied to the increments)
  have hparts : ∑ m ∈ Finset.range M, c m * (E (m+1) - E m)
      = c (M-1) * (E M - E 0)
        - ∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0) := by
    have h := Finset.sum_range_by_parts (fun m => c m)
      (fun m => E (m+1) - E m) M
    simp only [smul_eq_mul] at h
    have htel : ∀ n : ℕ, ∑ j ∈ Finset.range n, (E (j+1) - E j) = E n - E 0 := fun n =>
      Finset.sum_range_sub E n
    rw [htel] at h
    calc ∑ m ∈ Finset.range M, c m * (E (m+1) - E m) = _ := h
      _ = c (M-1) * (E M - E 0)
          - ∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0) := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [htel (i+1)]
  have hcband : ∀ m < M, ‖c m‖ ≤ 1/(4*δ) := fun m hm =>
    norm_klCoeff_le hδ0 (hlo m hm) (hhi m hm)
  have hvar : ∑ i ∈ Finset.range (M-1), ‖c (i+1) - c i‖ ≤ 1/(2*δ) := by
    have hterm : ∀ i ∈ Finset.range (M-1),
        ‖c (i+1) - c i‖ = (g i - g (i+1)) / 2 := by
      intro i hi
      have hi1 : i + 1 < M := by
        have := Finset.mem_range.mp hi
        omega
      have hii : i < M := by omega
      have hanti := cot_pi_mul_antitone hδ0 (hlo i hii)
        (hmono i hi1) (hhi (i+1) hi1)
      simp only [hc, hg]
      rw [norm_klCoeff_sub]
      rw [abs_of_nonneg (by linarith)]
    rw [Finset.sum_congr rfl hterm]
    have htel : ∑ i ∈ Finset.range (M-1), (g i - g (i+1)) = g 0 - g (M-1) :=
      Finset.sum_range_sub' g (M-1)
    rw [← Finset.sum_div, htel]
    have hg0 : g 0 ≤ 1/(2*δ) := by
      simp only [hg]
      exact cot_pi_mul_le hδ0 (hlo 0 hM1) (hhi 0 hM1)
    have hgM : -(1/(2*δ)) ≤ g (M-1) := by
      have hMm : M - 1 < M := by omega
      have hanti := cot_pi_mul_antitone hδ0 (hlo _ hMm)
        (hhi _ hMm) (le_refl (1-δ))
      have hedge : Real.cos (Real.pi * (1-δ)) / Real.sin (Real.pi * (1-δ))
          = -(Real.cos (Real.pi * δ) / Real.sin (Real.pi * δ)) := by
        rw [show Real.pi * (1-δ) = Real.pi - Real.pi * δ by ring,
          Real.cos_pi_sub, Real.sin_pi_sub]
        ring
      have hδhalf : δ ≤ 1 - δ := by
        by_contra hcon
        rw [not_le] at hcon
        have hl := hlo 0 hM1
        have hh := hhi 0 hM1
        linarith
      have hcotδ : Real.cos (Real.pi * δ) / Real.sin (Real.pi * δ) ≤ 1/(2*δ) :=
        cot_pi_mul_le hδ0 (le_refl δ) hδhalf
      simp only [hg]
      rw [hedge] at hanti
      linarith
    linarith
  rw [hsplit, hparts]
  have hMm : M - 1 < M := by omega
  have hEsub : ∀ n k : ℕ, ‖E n - E k‖ ≤ 2 := by
    intro n k
    refine le_trans (norm_sub_le _ _) ?_
    simp only [hE]
    rw [hEnorm, hEnorm]
    norm_num
  have h1 : ‖c (M-1) * (E M - E 0)‖ ≤ 1/(4*δ) * 2 := by
    rw [norm_mul]
    exact mul_le_mul (hcband (M-1) hMm) (hEsub M 0) (norm_nonneg _) (by positivity)
  have h3 : ‖∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0)‖
      ≤ 1/(2*δ) * 2 := by
    refine le_trans (norm_sum_le _ _) ?_
    have hpt : ∀ i ∈ Finset.range (M-1),
        ‖(c (i+1) - c i) * (E (i+1) - E 0)‖ ≤ ‖c (i+1) - c i‖ * 2 := by
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEsub (i+1) 0) (norm_nonneg _)
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hvar (by norm_num)
  have h4 : ‖E M‖ = 1 := by
    simp only [hE]
    exact hEnorm M
  have hchain : ‖c (M-1) * (E M - E 0)
      - ∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0) + E M‖
      ≤ ‖c (M-1) * (E M - E 0)‖
        + ‖∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0)‖ + ‖E M‖ := by
    have s2 : ‖c (M-1) * (E M - E 0)
        - ∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0)‖
        ≤ ‖c (M-1) * (E M - E 0)‖
          + ‖∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0)‖ :=
      norm_sub_le _ _
    have s3 := norm_add_le (c (M-1) * (E M - E 0)
      - ∑ i ∈ Finset.range (M-1), (c (i+1) - c i) * (E (i+1) - E 0)) (E M)
    linarith
  have hfinal : 1/(4*δ) * 2 + 1/(2*δ) * 2 + 1 = 3/(2*δ) + 1 := by
    field_simp
    ring
  linarith [hchain, h1, h3, le_of_eq h4]

end RHTower.Sieve
