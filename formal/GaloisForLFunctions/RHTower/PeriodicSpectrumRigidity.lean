/-
Periodic-spectrum rigidity: symmetry plus spectral periodicity force constancy.

Let `G` be even and entire, and suppose its trace on the lower flank `Im s ≤ -w` is an
absolutely convergent one-sided exponential series `Σ_k b_k · exp(-i s · α k)` whose frequencies
`α k` run over an *arithmetic progression* — the spectrum is periodic under `k ↦ k+1` with step `α`.
Then `G` is constant, equal to `b₀`.  No growth bound, no flank bound, no quietness hypothesis is
imposed: symmetry and the arithmetic-progression spectrum alone close the fundamental cell.

The mechanism is constraint-side throughout.  Absolute convergence bounds `G` on the lower flank by
the envelope `B₀ = Σ_k ‖b_k‖ e^{-α k w}` (`norm_tsum_le_tsum_norm`).  Because the frequencies are
`α k`, the horizontal shift by the period `2π/α` multiplies each term by `e^{-2π i k} = 1`, so `G`
is invariant under that real period on the flank; analytic continuation
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) promotes the invariance to all of `ℂ`.
Evenness reflects the flank bound onto `Im s ≥ w`, and periodicity folds the intervening strip into
one compact cell `[0, 2π/α] × [-w, w]`, on which the continuous `G` is bounded; the three regions
cover the plane, so `G` is a bounded entire function and Liouville makes it constant.  Sending the
constant down the vertical ray `s = -(w+n)·i` kills every term with `k ≥ 1` and leaves `b₀`.

Every arithmetic-progression spectrum is rigid: this is the first closure of the cell with no growth,
quietness, or flank-bound hypothesis — periodicity of the spectrum substitutes for all of them.

* `periodic_spectrum_rigidity` — an even entire function whose lower-flank trace is an absolutely
  convergent exponential series with arithmetic-progression spectrum is constant, equal to `b₀`.
-/
import Mathlib
import GaloisForLFunctions.HTGeometry.CarrierDichotomy

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- **Periodic-spectrum rigidity.**  An *even* entire `G` whose trace on the lower flank
`Im s ≤ -w` is the absolutely convergent one-sided exponential series
`G s = Σ_k b_k · exp(-i s · α k)` (frequencies `α k`, `k ∈ ℕ`, envelope `Σ_k ‖b_k‖ e^{-α k w} < ∞`)
is constant, equal to `b₀`.

The spectrum `{α k}` is an arithmetic progression, so the real shift by `2π/α` fixes every term
(`e^{-2π i k} = 1`); the flank identity `G(s + 2π/α) = G(s)` continues to all of `ℂ`, and with the
evenness-reflected flank bound it makes `G` bounded on the plane (flanks by the envelope `B₀`, the
strip by the maximum on the compact fundamental cell).  Liouville forces `G` constant, and the
descending vertical ray `s = -(w+n)i` collapses the series onto its zeroth coefficient `b₀`.  No
growth, quietness, or flank-bound hypothesis enters: the arithmetic-progression spectrum alone is the
constraint that closes the cell. -/
theorem periodic_spectrum_rigidity {G : ℂ → ℂ} {b : ℕ → ℂ} {α w : ℝ}
    (hα : 0 < α) (_hw : 0 < w)
    (hG : Differentiable ℂ G)
    (hb : Summable fun k => ‖b k‖ * Real.exp (-(α * k * w)))
    (htrace : ∀ z : ℂ, z.im ≤ -w →
      G z = ∑' k : ℕ, b k * Complex.exp (-Complex.I * z * (α * k)))
    (hsym : ∀ z : ℂ, G z = G (-z)) :
    ∀ z : ℂ, G z = b 0 := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  -- Real part of the frequency-`j` exponent on any horizontal line: `Re(-i ζ · α j) = α j · Im ζ`.
  have hre_lemma : ∀ (ζ : ℂ) (j : ℕ),
      (-Complex.I * ζ * ((α : ℂ) * (j : ℂ))).re = α * j * ζ.im := by
    intro ζ j
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
    ring
  -- Termwise domination of the lower-flank series by the convergent envelope.
  have hbound_flank : ∀ (ζ : ℂ), ζ.im ≤ -w → ∀ k : ℕ,
      ‖b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))‖
        ≤ ‖b k‖ * Real.exp (-(α * k * w)) := by
    intro ζ hζ k
    have hknn : (0 : ℝ) ≤ α * k := by positivity
    have hmono : α * k * ζ.im ≤ -(α * k * w) := by nlinarith [hknn, hζ]
    calc ‖b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))‖
          = ‖b k‖ * Real.exp ((-Complex.I * ζ * ((α : ℂ) * (k : ℂ))).re) := by
            simp only [norm_mul, Complex.norm_exp]
      _ = ‖b k‖ * Real.exp (α * k * ζ.im) := by rw [hre_lemma ζ k]
      _ ≤ ‖b k‖ * Real.exp (-(α * k * w)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono) (norm_nonneg _)
  -- Absolute convergence of the lower-flank series.
  have hcsummable : ∀ (ζ : ℂ), ζ.im ≤ -w →
      Summable (fun k => b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))) :=
    fun ζ hζ => Summable.of_norm_bounded hb (hbound_flank ζ hζ)
  -- The lower-flank bound `‖G‖ ≤ B₀` on `Im s ≤ -w`.
  set B₀ : ℝ := ∑' k : ℕ, ‖b k‖ * Real.exp (-(α * k * w)) with hB0
  have hflank : ∀ (ζ : ℂ), ζ.im ≤ -w → ‖G ζ‖ ≤ B₀ := by
    intro ζ hζ
    have hnorm_sum :
        Summable (fun k => ‖b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (hbound_flank ζ hζ) hb
    rw [htrace ζ hζ]
    calc ‖∑' k, b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))‖
          ≤ ∑' k, ‖b k * Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))‖ :=
            norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' k, ‖b k‖ * Real.exp (-(α * k * w)) :=
            Summable.tsum_le_tsum (hbound_flank ζ hζ) hnorm_sum hb
      _ = B₀ := hB0.symm
  -- The real period `2π/α` and its complex incarnation.
  set pR : ℝ := 2 * Real.pi / α with hpR
  have hpRpos : 0 < pR := by rw [hpR]; positivity
  set P : ℂ := (pR : ℂ) with hP
  have hPim : P.im = 0 := by rw [hP]; exact Complex.ofReal_im pR
  -- Each spectral term is fixed by the period on the flank, so `G(· + P) = G` there.
  have hper_flank : ∀ (ζ : ℂ), ζ.im ≤ -w → G (ζ + P) = G ζ := by
    intro ζ hζ
    have hζP : (ζ + P).im ≤ -w := by rw [Complex.add_im, hPim, add_zero]; exact hζ
    rw [htrace (ζ + P) hζP, htrace ζ hζ]
    apply tsum_congr
    intro k
    have hfac : Complex.exp (-Complex.I * (ζ + P) * ((α : ℂ) * (k : ℂ)))
        = Complex.exp (-Complex.I * ζ * ((α : ℂ) * (k : ℂ)))
          * Complex.exp (-Complex.I * P * ((α : ℂ) * (k : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hone : Complex.exp (-Complex.I * P * ((α : ℂ) * (k : ℂ))) = 1 := by
      have hthis : -Complex.I * P * ((α : ℂ) * (k : ℂ))
          = (((-k : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [hP, hpR]; push_cast; field_simp
      rw [hthis, Complex.exp_int_mul_two_pi_mul_I]
    rw [hfac, hone, mul_one]
  -- Analytic continuation: the flank identity `G(· + P) = G` holds on all of `ℂ`.
  have hshift : Differentiable ℂ (fun z : ℂ => z + P) := by fun_prop
  have hA1 : AnalyticOnNhd ℂ (fun z => G (z + P)) Set.univ :=
    (hG.comp hshift).differentiableOn.analyticOnNhd isOpen_univ
  have hA2 : AnalyticOnNhd ℂ G Set.univ := hG.differentiableOn.analyticOnNhd isOpen_univ
  have hopenflank : IsOpen {z : ℂ | z.im < -w} := isOpen_lt Complex.continuous_im continuous_const
  set z₀ : ℂ := ⟨0, -(w + 1)⟩ with hz₀
  have hz₀mem : z₀.im < -w := by
    have he : z₀.im = -(w + 1) := rfl
    rw [he]; linarith
  have hev : (fun z => G (z + P)) =ᶠ[𝓝 z₀] G := by
    filter_upwards [hopenflank.mem_nhds hz₀mem] with z hz
    exact hper_flank z (le_of_lt hz)
  have hperF : Function.Periodic G P := fun z =>
    (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA1 hA2 isPreconnected_univ
      (Set.mem_univ z₀) hev) (Set.mem_univ z)
  -- Boundedness on the compact fundamental cell, transported through the strip by periodicity.
  have hKcompact : IsCompact
      ((fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ''
        (Set.Icc 0 pR ×ˢ Set.Icc (-w) w)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨B₁, hB₁⟩ := hKcompact.exists_bound_of_continuousOn hG.continuous.continuousOn
  have hstrip : ∀ (z : ℂ), -w ≤ z.im → z.im ≤ w → ‖G z‖ ≤ B₁ := by
    intro z hlo hhi
    set n : ℤ := ⌊z.re / pR⌋ with hn
    have hfloor_le : (↑n : ℝ) ≤ z.re / pR := by rw [hn]; exact Int.floor_le _
    have hlt_floor : z.re / pR < ↑n + 1 := by rw [hn]; exact Int.lt_floor_add_one _
    have hn_le : (↑n : ℝ) * pR ≤ z.re := by
      have h := mul_le_mul_of_nonneg_right hfloor_le hpRpos.le
      rwa [div_mul_cancel₀ z.re hpRpos.ne'] at h
    have hlt : z.re < (↑n : ℝ) * pR + pR := by
      have h := mul_lt_mul_of_pos_right hlt_floor hpRpos
      rwa [div_mul_cancel₀ z.re hpRpos.ne', add_mul, one_mul] at h
    have hnP : (↑n : ℂ) * P = (((↑n : ℝ) * pR : ℝ) : ℂ) := by rw [hP]; push_cast; ring
    have hz're : (z - (↑n : ℂ) * P).re = z.re - (↑n : ℝ) * pR := by
      rw [hnP, Complex.sub_re, Complex.ofReal_re]
    have hz'im : (z - (↑n : ℂ) * P).im = z.im := by
      rw [hnP, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hre_mem : (z - (↑n : ℂ) * P).re ∈ Set.Icc (0 : ℝ) pR := by
      rw [hz're]; exact ⟨by linarith, by linarith⟩
    have him_mem : (z - (↑n : ℂ) * P).im ∈ Set.Icc (-w) w := by
      rw [hz'im]; exact ⟨hlo, hhi⟩
    have hmem : (z - (↑n : ℂ) * P) ∈
        (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ''
          (Set.Icc 0 pR ×ˢ Set.Icc (-w) w) :=
      ⟨((z - (↑n : ℂ) * P).re, (z - (↑n : ℂ) * P).im), ⟨hre_mem, him_mem⟩,
        Complex.re_add_im (z - (↑n : ℂ) * P)⟩
    calc ‖G z‖ = ‖G (z - (↑n : ℂ) * P)‖ := by rw [hperF.sub_int_mul_eq n]
      _ ≤ B₁ := hB₁ _ hmem
  -- Bounded on the three regions covering `ℂ`; Liouville forces constancy.
  have hglobal : ∀ z : ℂ, ‖G z‖ ≤ max B₀ B₁ := by
    intro z
    rcases le_or_gt z.im (-w) with h | h
    · exact le_trans (hflank z h) (le_max_left _ _)
    · rcases le_or_gt w z.im with h2 | h2
      · rw [hsym z]
        refine le_trans (hflank (-z) ?_) (le_max_left _ _)
        rw [Complex.neg_im]; linarith
      · exact le_trans (hstrip z (le_of_lt h) (le_of_lt h2)) (le_max_right _ _)
  have hconst : ∀ s t : ℂ, G s = G t :=
    GaloisForLFunctions.bounded_entire_symbol_const G hG ⟨max B₀ B₁, hglobal⟩
  -- The constant is `b₀`: the descending vertical ray annihilates every term with `k ≥ 1`.
  set B₀' : ℝ := ∑' k : ℕ, ‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w)) with hB0'
  have hgtail_sum :
      Summable (fun k : ℕ => ‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) :=
    (summable_nat_add_iff 1).mpr hb
  have hlt1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpow0 : Tendsto (fun n : ℕ => (Real.exp (-α)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hlt1
  have htend : Tendsto (fun n : ℕ => B₀' * (Real.exp (-α)) ^ n) atTop (𝓝 0) := by
    simpa using hpow0.const_mul B₀'
  intro z
  have hbnd : ∀ n : ℕ, ‖G z - b 0‖ ≤ B₀' * (Real.exp (-α)) ^ n := by
    intro n
    set zn : ℂ := ⟨0, -(w + n)⟩ with hzn
    have hznim : zn.im = -(w + n) := rfl
    have hznflank : zn.im ≤ -w := by
      rw [hznim]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    set F : ℕ → ℂ := fun k => b k * Complex.exp (-Complex.I * zn * ((α : ℂ) * (k : ℂ))) with hF
    have htz : G zn = ∑' k, F k := htrace zn hznflank
    have hshiftsum : Summable (fun k => F (k + 1)) :=
      (summable_nat_add_iff 1).mpr (hcsummable zn hznflank)
    have hF0 : F 0 = b 0 := by rw [hF]; simp [Complex.exp_zero]
    have hsplit : ∑' k, F k = F 0 + ∑' k, F (k + 1) := tsum_eq_zero_add' hshiftsum
    have hGznsub : G zn - b 0 = ∑' k, F (k + 1) := by rw [htz, hsplit, hF0]; ring
    have hfk1_bound : ∀ k, ‖F (k + 1)‖
        ≤ (‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) * (Real.exp (-α)) ^ n := by
      intro k
      have hnorm : ‖F (k + 1)‖ = ‖b (k + 1)‖ * Real.exp (α * ((k + 1 : ℕ) : ℝ) * zn.im) := by
        rw [hF]; simp only [norm_mul, Complex.norm_exp]; rw [hre_lemma zn (k + 1)]
      rw [hnorm, hznim]
      have hbk1 : (0 : ℝ) ≤ ‖b (k + 1)‖ := norm_nonneg _
      have hexp_le : Real.exp (α * ((k + 1 : ℕ) : ℝ) * (-(w + n)))
          ≤ Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w)) * (Real.exp (-α)) ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        push_cast
        nlinarith [mul_nonneg (mul_nonneg hα.le hn0) hk0, hα.le, hn0, hk0]
      calc ‖b (k + 1)‖ * Real.exp (α * ((k + 1 : ℕ) : ℝ) * (-(w + ↑n)))
            ≤ ‖b (k + 1)‖ * (Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w)) * (Real.exp (-α)) ^ n) :=
              mul_le_mul_of_nonneg_left hexp_le hbk1
        _ = (‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) * (Real.exp (-α)) ^ n := by
              ring
    have hrhs_sum : Summable
        (fun k => (‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) * (Real.exp (-α)) ^ n) :=
      hgtail_sum.mul_right _
    have hnorm_sum : Summable (fun k => ‖F (k + 1)‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hfk1_bound hrhs_sum
    calc ‖G z - b 0‖ = ‖G zn - b 0‖ := by rw [hconst z zn]
      _ = ‖∑' k, F (k + 1)‖ := by rw [hGznsub]
      _ ≤ ∑' k, ‖F (k + 1)‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' k, (‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) * (Real.exp (-α)) ^ n :=
            Summable.tsum_le_tsum hfk1_bound hnorm_sum hrhs_sum
      _ = (∑' k, ‖b (k + 1)‖ * Real.exp (-(α * ((k + 1 : ℕ) : ℝ) * w))) * (Real.exp (-α)) ^ n :=
            tsum_mul_right
      _ = B₀' * (Real.exp (-α)) ^ n := by rw [hB0']
  have hle0 : ‖G z - b 0‖ ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hbnd)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle0)

end RHTower
