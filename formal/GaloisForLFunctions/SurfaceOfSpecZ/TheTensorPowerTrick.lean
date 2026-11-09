import GaloisForLFunctions.SurfaceOfSpecZ.TheZeroFreeStripImprovesItself

/-!
# The tensor power trick

The traces `2 Re S(log p)` at the primes are the point counts over `𝔽_p` of the virtual motive
`M = Σ_z e_z ℤ(−z)`; the even powers `(2 Re S(log p))^{2k}` are those of `M^{⊗2k}` and are nonnegative
without any hypothesis. Deligne's tensor power trick bounds the weights of `M` by the growth of the
point counts of all `M^{⊗2k}`, uniformly in `k`. Over `ℤ`:

**Theorem** (`riemannHypothesis_iff_moments_primeTraces`). RH holds iff there is `A` such that for every
`k ≥ 1` the moments grow at most like `N^{1+A}`:
`Σ_{p ≤ N} log p · (2 Re S(log p))^{2k} ≤ C_k N^{1+A}`.

**Proof.** One term of the `k`-th moment gives `|2 Re S(log p)| ≤ C' p^{(1+A)/(2k)}`, and the width law
at the primes (`zetaZeroWidth_le_iff_bddBelow_primeDegrees`) gives `zetaZeroWidth ≤ (1 + A)/(2k)` once
`(1 + A)/(2k) < ½`. Letting `k → ∞` gives width `0`. Positivity is free; the uniformity in `k` is RH.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- The `k`-th moment of the prime traces up to `N`. -/
def primeTraceMoment (k N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k)

/-- **The tensor power trick over `ℤ`.** -/
theorem riemannHypothesis_iff_moments_primeTraces :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ N : ℕ,
      primeTraceMoment k N ≤ C * (N : ℝ) ^ (1 + A) := by
  constructor
  · intro hRH
    -- under RH the traces are bounded
    obtain ⟨K, hK⟩ := (zetaZeroWidth_le_iff_bddBelow_primeDegrees le_rfl (by norm_num)).mp
      (riemannHypothesis_iff_zetaZeroWidth_le_zero.mp hRH)
    obtain ⟨K', hK'⟩ := (zetaZeroWidth_le_iff_bddAbove_primeDegrees le_rfl (by norm_num)).mp
      (riemannHypothesis_iff_zetaZeroWidth_le_zero.mp hRH)
    refine ⟨1, fun k _ => ⟨2 * (|K| + |K'|) ^ (2 * k), fun N => ?_⟩⟩
    have hbound : ∀ p : ℕ, p.Prime →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ |K| + |K'| := by
      intro p hp
      have h1 := hK p hp
      have h2 := hK' p hp
      simp only [Real.rpow_zero, mul_one] at h1 h2
      rw [abs_le]; constructor <;> linarith [le_abs_self K, le_abs_self K', abs_nonneg K, abs_nonneg K']
    have hterm : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) ≤
          N * (|K| + |K'|) ^ (2 * k) := by
      intro p hp
      obtain ⟨hpN, hpp⟩ := Finset.mem_filter.mp hp
      have hpN' : (p : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hpN)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hlog : Real.log p ≤ N :=
        (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
      have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have hpow : (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) ≤
          (|K| + |K'|) ^ (2 * k) := by
        rw [pow_mul, pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _) (by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbound p hpp) 2) k
      exact mul_le_mul hlog hpow (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (by positivity)
    have hcard : (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤ 2 * N := by
      rcases Nat.eq_zero_or_pos N with h0 | hN
      · subst h0; simp [Finset.filter_singleton, Nat.not_prime_zero]
      · have h1 : ((Finset.range (N + 1)).filter Nat.Prime).card ≤ N + 1 :=
          (Finset.card_filter_le _ _).trans (by simp)
        have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have : (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤ N + 1 := by exact_mod_cast h1
        linarith
    calc primeTraceMoment k N
        ≤ ∑ _p ∈ (Finset.range (N + 1)).filter Nat.Prime, (N : ℝ) * (|K| + |K'|) ^ (2 * k) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (N + 1)).filter Nat.Prime).card * (N * (|K| + |K'|) ^ (2 * k)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * N) * (N * (|K| + |K'|) ^ (2 * k)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * (|K| + |K'|) ^ (2 * k) * (N : ℝ) ^ (1 + 1 : ℝ) := by
          rw [show (1 + 1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  · rintro ⟨A, hA⟩
    rw [riemannHypothesis_iff_zetaZeroWidth_le_zero]
    -- every large `k` bounds the width by `(1 + A)/(2k)`
    have hwidth : ∀ k : ℕ, (1 + |A|) < k → zetaZeroWidth ≤ (1 + |A|) / (2 * k) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        have : (1 : ℝ) < k := by linarith [abs_nonneg A]
        exact_mod_cast this.le
      have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg A]
      obtain ⟨C, hC⟩ := hA k hk1
      set a : ℝ := (1 + |A|) / (2 * k) with ha
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have ha1 : a < 1 / 2 := by
        rw [ha, div_lt_iff₀ (by positivity)]; linarith
      rw [zetaZeroWidth_le_iff_bddBelow_primeDegrees ha0 ha1]
      set B : ℝ := |C| / Real.log 2 with hB
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      refine ⟨B ^ ((1 : ℝ) / (2 * k)), fun p hp => ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hp0 : (0 : ℝ) < p := by linarith
      have hlogp : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      set c := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re with hc
      -- one term of the moment at `N = p`
      have hone : Real.log p * c ^ (2 * k) ≤ C * (p : ℝ) ^ (1 + A) := by
        have hmem : p ∈ (Finset.range (p + 1)).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp⟩
        have h := hC p
        unfold primeTraceMoment at h
        refine le_trans (Finset.single_le_sum (f := fun q : ℕ => Real.log q *
          (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log q)).re) ^ (2 * k))
          (fun q hq => mul_nonneg (Real.log_nonneg (by
            exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le)) (by
              rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)) hmem) h
      have hpA : (p : ℝ) ^ (1 + A) ≤ (p : ℝ) ^ (1 + |A|) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [le_abs_self A])
      have hc2k : |c| ^ (2 * k) ≤ B * (p : ℝ) ^ (1 + |A|) := by
        rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
        have h1 : Real.log 2 * c ^ (2 * k) ≤ Real.log p * c ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hlogp (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
        have h2 : C * (p : ℝ) ^ (1 + A) ≤ |C| * (p : ℝ) ^ (1 + |A|) :=
          mul_le_mul (le_abs_self C) hpA (by positivity) (abs_nonneg C)
        rw [hB, div_mul_eq_mul_div, le_div_iff₀ hlog2]
        linarith
      -- take the `2k`-th root
      have h2k : (2 * k : ℕ) ≠ 0 := by omega
      have hroot : |c| ≤ B ^ ((1 : ℝ) / (2 * k)) * (p : ℝ) ^ a := by
        have h1 := Real.rpow_le_rpow (by positivity) hc2k (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
          show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by push_cast; field_simp, Real.rpow_one,
          Real.mul_rpow hB0 (by positivity), ← Real.rpow_mul hp0.le] at h1
        rw [ha]
        convert h1 using 3
        ring
      linarith [neg_abs_le c]
    -- let `k → ∞`
    by_contra hpos
    push Not at hpos
    obtain ⟨k, hk⟩ := exists_nat_gt (max (1 + |A|) ((1 + |A|) / (2 * zetaZeroWidth)))
    have hk1 : 1 + |A| < k := (le_max_left _ _).trans_lt hk
    have hk2 : (1 + |A|) / (2 * zetaZeroWidth) < k := (le_max_right _ _).trans_lt hk
    have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg A]
    have := hwidth k hk1
    rw [div_lt_iff₀ (by positivity)] at hk2
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith

end GaloisForLFunctions.SurfaceOfSpecZ
