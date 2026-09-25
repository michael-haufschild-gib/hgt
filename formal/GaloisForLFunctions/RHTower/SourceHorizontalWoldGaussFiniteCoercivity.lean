import GaloisForLFunctions.RHTower.SourceHorizontalWoldGaussHodgeVirialBridge

/-!
# Finite Wold–Gauss source response has an unavoidable linear outer-prime scale

The depth-one Gauss coefficient obeys an exact rational identity after its
two logarithmic clock factors are restored. This yields a sharp uniform
linear-in-prime lower bound, even when the inner Wold cutoff moves. Consequently
no additive outer-prime counterterm of sublinear scale can bound the finite
response at a nonzero horizontal grade. This is a source-side scale obstruction,
not a bound that proves RH or a claim about an actual prime–Gamma counterterm.
-/

noncomputable section
open Filter
namespace RHTower

private def responseTerm (N : ℕ) (u : ℝ) (k : ℕ) : ℝ :=
  u ^ (2 * k) / (2 * k).factorial *
    sourceHorizontalWoldOrderedNormalizedMoment N (2 * k)

private lemma responseTerm_nonneg (N : ℕ) (u : ℝ) (k : ℕ) :
    0 ≤ responseTerm N u k := by
  unfold responseTerm
  have hp : 0 ≤ u ^ (2 * k) := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
    exact sq_nonneg _
  exact mul_nonneg (div_nonneg hp (Nat.cast_nonneg _))
    (sourceHorizontalWoldOrderedNormalizedMoment_nonneg N (2 * k))

private lemma responseTerm_summable (N : ℕ) (u : ℝ) :
    Summable (responseTerm N u) := by
  have hmass : 0 ≤ sourceHorizontalWoldOrderedNormalizedMoment N 0 :=
    sourceHorizontalWoldOrderedNormalizedMoment_nonneg N 0
  have hmajor := (Real.hasSum_cosh |u|).summable.mul_left
    (sourceHorizontalWoldOrderedNormalizedMoment N 0)
  apply hmajor.of_nonneg_of_le (responseTerm_nonneg N u)
  intro k
  have hp : 0 ≤ u ^ (2 * k) := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
    exact sq_nonneg _
  have heq : u ^ (2 * k) = |u| ^ (2 * k) := by
    rw [← abs_pow, abs_of_nonneg hp]
  unfold responseTerm
  rw [heq]
  calc
    |u| ^ (2 * k) / ↑(2 * k).factorial *
        sourceHorizontalWoldOrderedNormalizedMoment N (2 * k) ≤
        |u| ^ (2 * k) / ↑(2 * k).factorial *
          sourceHorizontalWoldOrderedNormalizedMoment N 0 :=
      mul_le_mul_of_nonneg_left
        (sourceHorizontalWoldOrderedNormalizedMoment_le_mass N (2 * k)) (by positivity)
    _ = sourceHorizontalWoldOrderedNormalizedMoment N 0 *
        (|u| ^ (2 * k) / ↑(2 * k).factorial) := by ring

private lemma finiteResponse_ge_mass (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldOrderedNormalizedMoment N 0 ≤
      sourceHorizontalWoldPrimeClockCompletedFiniteResponse N u := by
  have h := (responseTerm_summable N u).le_tsum 0
    (by intro k hk; exact responseTerm_nonneg N u k)
  simpa [sourceHorizontalWoldPrimeClockCompletedFiniteResponse, responseTerm] using h

/-- Exact depth-one Gauss weight after restoring the two horizontal clock factors. -/
theorem gaussReciprocalCharacterWeight_one_mul_log_sq (p : Nat.Primes) :
    gaussReciprocalCharacterWeight 1 p * Real.log (p : ℝ) ^ (2 : ℕ) =
      Real.log 2 * ((p : ℝ) - 1) ^ (4 : ℕ) /
        ((p : ℝ) * ((p : ℝ) + 1) ^ (2 : ℕ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p : ℝ) + 1 ≠ 0 := by
    have h : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
    positivity
  have hl : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  rw [gaussReciprocalCharacterWeight_one_eq_wold_gauge,
    gaussWoldDepthOneCoefficientGauge, woldCoeff]
  simp only [pow_one]
  field_simp [hp0, hp1, hl]

/-- The restored depth-one weight has a sharp linear prime-label floor. -/
theorem gaussReciprocalCharacterWeight_one_log_sq_linear_lower (p : Nat.Primes) :
    Real.log 2 / 36 * (p : ℝ) ≤
      gaussReciprocalCharacterWeight 1 p * Real.log (p : ℝ) ^ (2 : ℕ) := by
  let x : ℝ := (p : ℝ)
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast p.property.two_le
  have hsub : x / 2 ≤ x - 1 := by linarith
  have hsubPow : (x / 2) ^ (4 : ℕ) ≤ (x - 1) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hsub 4
  have hplus : x + 1 ≤ 3 * x / 2 := by linarith
  have hplusPow : (x + 1) ^ (2 : ℕ) ≤ (3 * x / 2) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by linarith) hplus 2
  have hcore : x ^ (2 : ℕ) * (x + 1) ^ (2 : ℕ) ≤
      36 * (x - 1) ^ (4 : ℕ) := by
    calc
      _ ≤ x ^ (2 : ℕ) * (3 * x / 2) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hplusPow (sq_nonneg x)
      _ = 36 * (x / 2) ^ (4 : ℕ) := by ring
      _ ≤ 36 * (x - 1) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hsubPow (by norm_num)
  rw [gaussReciprocalCharacterWeight_one_mul_log_sq]
  change Real.log 2 / 36 * x ≤
    Real.log 2 * (x - 1) ^ (4 : ℕ) / (x * (x + 1) ^ (2 : ℕ))
  rw [le_div_iff₀ (by positivity : 0 < x * (x + 1) ^ (2 : ℕ))]
  calc
    Real.log 2 / 36 * x * (x * (x + 1) ^ (2 : ℕ)) =
        Real.log 2 / 36 * (x ^ (2 : ℕ) * (x + 1) ^ (2 : ℕ)) := by ring
    _ ≤ Real.log 2 / 36 * (36 * (x - 1) ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = Real.log 2 * (x - 1) ^ (4 : ℕ) := by ring

/-- One inner-clock depth works simultaneously for all outer primes and grades. -/
theorem gaussWoldFiniteSourceVirialResponse_uniform_linear_lower :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Nat.Primes) (t : ℝ),
      Real.log 2 / 36 * (p : ℝ) * t ^ (2 : ℕ) ≤
        gaussWoldFiniteSourceVirialResponse N 1 p t := by
  have hm : Tendsto
      (fun N : ℕ => sourceHorizontalWoldOrderedNormalizedMoment N 0)
      atTop (nhds 1) := by
    simpa using tendsto_sourceHorizontalWoldOrderedNormalizedMoment 0
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hm.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1))
  refine ⟨N₀, ?_⟩
  intro N hN p t
  have hresp : (1 / 2 : ℝ) ≤
      sourceHorizontalWoldPrimeClockCompletedFiniteResponse N
        (Real.log (p : ℝ) * t) :=
    (hN₀ N hN).le.trans
      (finiteResponse_ge_mass N (Real.log (p : ℝ) * t))
  have ha := gaussReciprocalCharacterWeight_one_log_sq_linear_lower p
  have ha_pos := gaussReciprocalCharacterWeight_pos (by norm_num : 1 ≤ 1) p
  have hsq : 0 ≤ t ^ (2 : ℕ) := sq_nonneg _
  unfold gaussWoldFiniteSourceVirialResponse
  have h1 : (Real.log 2 / 36 * (p : ℝ)) * t ^ (2 : ℕ) ≤
      (gaussReciprocalCharacterWeight 1 p * Real.log (p : ℝ) ^ (2 : ℕ)) *
        t ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_right ha hsq
  have hcoef : 0 ≤ gaussReciprocalCharacterWeight 1 p *
      Real.log (p : ℝ) ^ (2 : ℕ) :=
    mul_nonneg ha_pos.le (sq_nonneg _)
  have hleft : 0 ≤ 2 * (gaussReciprocalCharacterWeight 1 p *
      Real.log (p : ℝ) ^ (2 : ℕ)) * t ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (by norm_num) hcoef) hsq
  have h2 : (gaussReciprocalCharacterWeight 1 p * Real.log (p : ℝ) ^ (2 : ℕ)) *
        t ^ (2 : ℕ) ≤
      2 * (gaussReciprocalCharacterWeight 1 p * Real.log (p : ℝ) ^ (2 : ℕ)) *
        t ^ (2 : ℕ) *
        sourceHorizontalWoldPrimeClockCompletedFiniteResponse N
          (Real.log (p : ℝ) * t) := by
    calc
      _ = (2 * (gaussReciprocalCharacterWeight 1 p *
          Real.log (p : ℝ) ^ (2 : ℕ)) * t ^ (2 : ℕ)) * (1 / 2 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hresp hleft
  simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using h1.trans h2

/-- A sublinear-in-prime additive counterterm cannot bound the finite source
response at any nonzero horizontal grade, for any sufficiently deep inner clock. -/
theorem gaussWoldFiniteSourceVirialResponse_no_sublinear_correction
    (t : ℝ) (ht : t ≠ 0) (R : Nat.Primes → ℝ)
    (hR : Tendsto (fun n : ℕ =>
        R (nthPrimeSubtype n) / (nthPrimeSubtype n : ℝ)) atTop (nhds 0)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ,
      ∃ n : ℕ, B < gaussWoldFiniteSourceVirialResponse N 1
        (nthPrimeSubtype n) t - R (nthPrimeSubtype n) := by
  obtain ⟨N₀, hN₀⟩ := gaussWoldFiniteSourceVirialResponse_uniform_linear_lower
  let c : ℝ := Real.log 2 / 36 * t ^ (2 : ℕ)
  have hc : 0 < c :=
    mul_pos (by positivity) (sq_pos_of_ne_zero ht)
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      R (nthPrimeSubtype n) / (nthPrimeSubtype n : ℝ) < c / 2 :=
    hR.eventually_lt_const (by linarith)
  have hlarge : Tendsto
      (fun n : ℕ => c / 2 * (nthPrimeSubtype n : ℝ)) atTop atTop :=
    hp.const_mul_atTop (by linarith)
  refine ⟨N₀, ?_⟩
  intro N hN B
  obtain ⟨n, hnSmall, hnLarge⟩ :=
    (hsmall.and (hlarge.eventually_gt_atTop B)).exists
  have hp0 : 0 < (nthPrimeSubtype n : ℝ) := by
    exact_mod_cast (nthPrimeSubtype n).property.pos
  have hRsmall : R (nthPrimeSubtype n) <
      c / 2 * (nthPrimeSubtype n : ℝ) :=
    (div_lt_iff₀ hp0).mp hnSmall
  have hV : c * (nthPrimeSubtype n : ℝ) ≤
      gaussWoldFiniteSourceVirialResponse N 1 (nthPrimeSubtype n) t := by
    simpa only [c, mul_assoc, mul_comm, mul_left_comm] using
      hN₀ N hN (nthPrimeSubtype n) t
  exact ⟨n, by linarith⟩

end RHTower
