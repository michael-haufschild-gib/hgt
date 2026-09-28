import GaloisForLFunctions.RHTower.Sieve.HarmanWindowCrudeTails

/-!
# The Harman minorant on a window: the main-term lower bound

For the Harman minorant `ρ⁻ = rhoMinus z Q D E` with parameters on the window scale `y`
(`HarmanWindowScale`), and every window `(y, y(1+θ)]` with `θ ≥ exp(-(c/4)√log y)`,
`∑_{y < n ≤ y(1+θ)} ρ⁻(n) ≥ (1/250) θy/log y` for all large `y`.  The count is
`#primes − ∑ D₂ − ∑ D₄`; the discarded tails are prime counts over prime tuples, bounded by the
discarded densities `0.8896` (prime cofactor), `0.0960` (two-prime cofactor) and the boxes of the
three-prime cofactor and quadruple tail (`≤ 0.0097`), against the prime count `≥ (1-η)θy/log y`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- `y^b < m` from the logarithmic scale. -/
theorem rpow_lt_of_lt_logScale {y m b : ℝ} (hy : 1 < y) (hm : 0 < m) (h : b < log m / log y) :
    y ^ b < m := by
  have hly := Real.log_pos hy
  rw [lt_div_iff₀ hly] at h
  rw [← Real.exp_log hm, Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_lt_exp.2 (by linarith)

/-- The discarded pairs satisfy `⌊y(1+θ)⌋/(q₁q₂) < q₂⁴` (the cofactor has at most three prime
factors). -/
theorem harmanDiscardPair_small {y θ : ℝ} {z Q D E : ℕ} (hy : 1 < y) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h10 : 2 ≤ y ^ (1 / 10 : ℝ)) (hP : HarmanWindowScale (1 / 1000000) y z Q D E) :
    ∀ qq ∈ harmanDiscardPairSet z Q D E, ⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) < qq.2 ^ 4 := by
  intro qq hq
  obtain ⟨q₁, q₂⟩ := qq
  simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico] at hq
  obtain ⟨⟨_, hz2, _⟩, hp1, hp2, _, hdisc⟩ := hq
  simp only
  have hd : 0 < q₁ * q₂ := Nat.mul_pos hp1.pos hp2.pos
  rw [Nat.div_lt_iff_lt_mul hd]
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := Real.log_pos hy
  have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
  have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
  have hα2 : 2 / 11 < log q₂ / log y :=
    lt_logScale_of_rpow_lt hy (lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz2))
  have hsum : 11 / 10 < log ((q₁ : ℝ) * q₂ ^ 5) / log y := by
    rw [Real.log_mul hq1.ne' (by positivity), Real.log_pow, add_div]
    push_cast
    have e : 5 * log (q₂ : ℝ) / log y = 5 * (log q₂ / log y) := by ring
    rw [e]
    by_cases hD : q₁ < D
    · have hE : E ≤ q₁ * q₂ ^ (4 : ℕ) := by
        by_contra h; exact hdisc ⟨hD, by omega⟩
      have hE' : y ^ (1 - 1 / 1000000 : ℝ) < (q₁ : ℝ) * q₂ ^ 4 :=
        lt_of_lt_of_le hP.E_gt (by exact_mod_cast hE)
      have := lt_logScale_of_rpow_lt hy hE'
      rw [Real.log_mul hq1.ne' (by positivity), Real.log_pow, add_div] at this
      push_cast at this
      have e4 : 4 * log (q₂ : ℝ) / log y = 4 * (log q₂ / log y) := by ring
      linarith
    · have hD' : (D : ℝ) ≤ q₁ := by exact_mod_cast not_lt.mp hD
      have := lt_logScale_of_rpow_lt hy (lt_of_lt_of_le hP.D_gt hD')
      linarith
  have hm := rpow_lt_of_lt_logScale hy (by positivity) hsum
  have h2y : y * (1 + θ) ≤ y ^ (11 / 10 : ℝ) := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.rpow_add hy0, Real.rpow_one]
    nlinarith
  have hb : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
  have : (⌊y * (1 + θ)⌋₊ : ℝ) < ((q₂ ^ 4 * (q₁ * q₂) : ℕ) : ℝ) := by
    push_cast
    have e : (q₂ : ℝ) ^ 4 * (q₁ * q₂) = q₁ * q₂ ^ 5 := by ring
    rw [e]; linarith
  exact_mod_cast this

/-- The discarded quadruples satisfy `⌊y(1+θ)⌋/(q₁q₂q₃q₄) < q₄²`. -/
theorem harmanDiscardQuad_small {y θ : ℝ} {z Q D E : ℕ} (hy : 1 < y) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h11 : 2 ≤ y ^ (1 / 11 : ℝ)) (hP : HarmanWindowScale (1 / 1000000) y z Q D E) :
    ∀ t ∈ harmanDiscardQuadSet z D E, ⌊y * (1 + θ)⌋₊ / quadProd t < t.2.2 ^ 2 := by
  intro t ht
  obtain ⟨⟨q₁, q₂⟩, ⟨q₃, q₄⟩⟩ := t
  simp only [harmanDiscardQuadSet, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico] at ht
  obtain ⟨⟨⟨_, _⟩, _, hz4, _⟩, hp1, hp2, hp3, hp4, h21, h32, h43, _⟩ := ht
  simp only [quadProd]
  have hd : 0 < q₁ * q₂ * q₃ * q₄ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos
  rw [Nat.div_lt_iff_lt_mul hd]
  have hy0 : 0 < y := by linarith
  have hz : y ^ (2 / 11 : ℝ) < q₄ := lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz4)
  have h43' : (q₄ : ℝ) < q₃ := by exact_mod_cast h43
  have h32' : (q₃ : ℝ) < q₂ := by exact_mod_cast h32
  have h21' : (q₂ : ℝ) < q₁ := by exact_mod_cast h21
  have hw0 : 0 ≤ y ^ (2 / 11 : ℝ) := Real.rpow_nonneg hy0.le _
  set w := y ^ (2 / 11 : ℝ) with hw
  -- the product exceeds `w⁶ = y^{12/11}`
  have hprod : w ^ 6 < (q₁ : ℝ) * q₂ * q₃ * q₄ ^ 3 := by
    have h3 : w < q₃ := hz.trans h43'
    have h2 : w < q₂ := h3.trans h32'
    have h1 : w < q₁ := h2.trans h21'
    have e : w ^ 6 = w * w * w * w ^ 3 := by ring
    rw [e]
    have hw3 : w ^ 3 < (q₄ : ℝ) ^ 3 := pow_lt_pow_left₀ hz hw0 (by norm_num)
    have a1 : w * w < (q₁ : ℝ) * q₂ := mul_lt_mul'' h1 h2 hw0 hw0
    have a2 : w * w * w < (q₁ : ℝ) * q₂ * q₃ := mul_lt_mul'' a1 h3 (by positivity) hw0
    exact mul_lt_mul'' a2 hw3 (by positivity) (by positivity)
  have hw6 : w ^ 6 = y * y ^ (1 / 11 : ℝ) := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_one_add' hy0.le (by norm_num)]
    norm_num
  have hb : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
  have h2y : y * (1 + θ) ≤ y * y ^ (1 / 11 : ℝ) := by nlinarith
  have : (⌊y * (1 + θ)⌋₊ : ℝ) < ((q₄ ^ 2 * (q₁ * q₂ * q₃ * q₄) : ℕ) : ℝ) := by
    push_cast
    have e : (q₄ : ℝ) ^ 2 * (q₁ * q₂ * q₃ * q₄) = q₁ * q₂ * q₃ * q₄ ^ 3 := by ring
    rw [e]; linarith
  exact_mod_cast this

/-- The boxes of the three-prime cofactor and of the quadruple tail are below `0.0097`. -/
theorem harmanCrudeBoxes_le :
    6 * ((log ((3 / 11 + 1 / 1000000) / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((7 / 11 + 1 / 1000000) / 3 / (2 / 11)) + 1 / 100000) *
        (log ((5 / 11 + 1 / 1000000) / 2 / (2 / 11)) + 1 / 100000))
      + 6 * ((log ((1 / 4 + 1 / 1000000) / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000)) ≤ 97 / 10000 := by
  have l1 : log ((3 / 11 + 1 / 1000000 : ℝ) / (2 / 11)) ≤ 405469 / 1000000 :=
    (log_le_logSeriesUpper (by norm_num)).trans (by norm_num [logSeriesUpper, logSeriesLower])
  have l2 : log ((1 + 1 / 1000000 : ℝ) / 5 / (2 / 11)) ≤ 5957 / 62500 :=
    (log_le_logSeriesUpper (by norm_num)).trans (by norm_num [logSeriesUpper, logSeriesLower])
  have l3 : log ((7 / 11 + 1 / 1000000 : ℝ) / 3 / (2 / 11)) ≤ 154153 / 1000000 :=
    (log_le_logSeriesUpper (by norm_num)).trans (by norm_num [logSeriesUpper, logSeriesLower])
  have l4 : log ((5 / 11 + 1 / 1000000 : ℝ) / 2 / (2 / 11)) ≤ 111573 / 500000 :=
    (log_le_logSeriesUpper (by norm_num)).trans (by norm_num [logSeriesUpper, logSeriesLower])
  have l5 : log ((1 / 4 + 1 / 1000000 : ℝ) / (2 / 11)) ≤ 159229 / 500000 :=
    (log_le_logSeriesUpper (by norm_num)).trans (by norm_num [logSeriesUpper, logSeriesLower])
  have n1 : 0 ≤ log ((3 / 11 + 1 / 1000000 : ℝ) / (2 / 11)) + 1 / 100000 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (3 / 11 + 1 / 1000000) / (2 / 11) by norm_num)
    linarith
  have n2 : 0 ≤ log ((1 + 1 / 1000000 : ℝ) / 5 / (2 / 11)) + 1 / 100000 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (1 + 1 / 1000000) / 5 / (2 / 11) by norm_num)
    linarith
  have n3 : 0 ≤ log ((7 / 11 + 1 / 1000000 : ℝ) / 3 / (2 / 11)) + 1 / 100000 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (7 / 11 + 1 / 1000000) / 3 / (2 / 11) by norm_num)
    linarith
  have n4 : 0 ≤ log ((5 / 11 + 1 / 1000000 : ℝ) / 2 / (2 / 11)) + 1 / 100000 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (5 / 11 + 1 / 1000000) / 2 / (2 / 11) by norm_num)
    linarith
  have n5 : 0 ≤ log ((1 / 4 + 1 / 1000000 : ℝ) / (2 / 11)) + 1 / 100000 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (1 / 4 + 1 / 1000000) / (2 / 11) by norm_num)
    linarith
  have p5 := prod4_le n1 n2 n3 n4 (add_le_add l1 le_rfl) (add_le_add l2 le_rfl)
    (add_le_add l3 le_rfl) (add_le_add l4 le_rfl)
  have p4 := prod4_le n5 n2 n2 n2 (add_le_add l5 le_rfl) (add_le_add l2 le_rfl)
    (add_le_add l2 le_rfl) (add_le_add l2 le_rfl)
  have hnum : 6 * ((405469 / 1000000 + 1 / 100000) * (5957 / 62500 + 1 / 100000) *
      (154153 / 1000000 + 1 / 100000) * (111573 / 500000 + 1 / 100000))
      + 6 * ((159229 / 500000 + 1 / 100000) * (5957 / 62500 + 1 / 100000) *
      (5957 / 62500 + 1 / 100000) * (5957 / 62500 + 1 / 100000)) ≤ (97 / 10000 : ℝ) := by
    norm_num
  linarith

/-- **The main-term lower bound for the Harman minorant on windows.** -/
theorem exists_window_rhoMinus_ge :
    ∃ c > 0, ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E → z ≤ Q → D ≤ Q →
      (Q : ℝ) ≤ y → y * 2 < (Q : ℝ) * Q →
      1 / 250 * (θ * y / log y) ≤
        ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, (rhoMinus z Q D E n : ℝ) := by
  obtain ⟨c, hc, hPNT⟩ := exists_card_primesIn_window
  refine ⟨c, hc, ?_⟩
  have hη : (0 : ℝ) < 1 / 100000 := by norm_num
  have hB := hPNT (1 / 100000) hη
  have hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + 1 / 100000) * (θ * Z / log Z) :=
    hB.mono (fun Z hZ θ h1 h2 => (hZ θ h1 h2).2)
  filter_upwards [hB, eventually_sum_harmanDiscardPair_unit_le hc hη hB2,
    eventually_sum_harmanDiscardPair_primeCount_le hc hη hB2,
    eventually_sum_harmanDiscardPair_twoPrime_le hc hη hB2,
    eventually_sum_harmanDiscardPair_twoPrime_diag_le hc hη hB2,
    eventually_sum_harmanDiscardPair_threePrime_le hc hη hB2,
    eventually_sum_harmanDiscardQuad_le hc hη hB2,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hPy hT1 hT3 hT4 hT4d hT5 hT6 h10 h11 hy1
  intro θ hθ hθ1 z Q D E hP hzQ hDQ hQy hQ2
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  have hC₀0 : 0 ≤ θ * y / log y := by positivity
  -- the prime count
  have hθc : exp (-c * sqrt (log y)) ≤ θ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hθ
    have := Real.sqrt_nonneg (log y)
    nlinarith
  have hprime := (hPy θ hθc hθ1).1
  have hQ2' : 2 ≤ Q := by
    have hz : (2 : ℝ) < z := by
      have : y ^ (1 / 11 : ℝ) ≤ y ^ (2 / 11 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num)
      linarith [hP.z_gt]
    have : 2 < z := by exact_mod_cast hz
    omega
  -- the pointwise identity `ρ⁻ = 1_P - D₂ - D₄`
  have hdecomp : ∀ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, (rhoMinus z Q D E n : ℝ) =
      (if n.Prime then 1 else 0) - (harmanDiscardPairSum z Q D E n : ℝ)
        - (harmanDiscardQuadrupleSum z D E n : ℝ) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.1 hn
    have hny : y < n := by
      have := Nat.lt_floor_add_one y
      have h' : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast at h'; linarith
    have hnb : (n : ℝ) ≤ y * (1 + θ) := by
      have : (n : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hn2
      exact this.trans (Nat.floor_le (by positivity))
    have hQn : Q ≤ n := by
      have : (Q : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hnQ : n < Q * Q := by
      have : (n : ℝ) < Q * Q := by nlinarith
      exact_mod_cast this
    have hn0 : 0 < n := by omega
    have h := rhoMinus_eq_prime_sub_discards (E := E) hn0 hQ2' hzQ hDQ hQn hnQ
    have h' := congrArg (fun x : ℤ => (x : ℝ)) h
    rw [h']
    push_cast
    rfl
  have hsum : ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, (rhoMinus z Q D E n : ℝ) =
      ((primesIn y (y * (1 + θ))).card : ℝ)
        - ((∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, harmanDiscardPairSum z Q D E n : ℕ) : ℝ)
        - ((∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, harmanDiscardQuadrupleSum z D E n : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl hdecomp, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_boole, Nat.cast_sum, Nat.cast_sum]
    rfl
  -- the discarded pair tail
  have hD2N := sum_Ioc_harmanDiscardPairSum_le (a := ⌊y⌋₊) (b := ⌊y * (1 + θ)⌋₊)
    (harmanDiscardPair_small (z := z) (Q := Q) (D := D) (E := E) hy1 hθ0.le hθ1 h10 hP)
  have hD2 : ((∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, harmanDiscardPairSum z Q D E n : ℕ) : ℝ)
      ≤ ∑ qq ∈ harmanDiscardPairSet z Q D E,
          ((if 1 ∈ Finset.Ioc (⌊y⌋₊ / (qq.1 * qq.2)) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))
              then (1 : ℝ) else 0)
            + (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2)) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)) qq.2 : ℝ)
            + ((primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / qq.2)
                (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / qq.2) qq.2 : ℝ)
              + ∑ p ∈ (Finset.Ioc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))).filter Nat.Prime,
                (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / p)
                  (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / p) p : ℝ))
            + ∑ pp ∈ ((Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))) ×ˢ
                (Finset.Icc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2)))).filter
                (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
              (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2))
                (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / (pp.1 * pp.2)) pp.2 : ℝ)) := by
    refine (Nat.cast_le.2 hD2N).trans ?_
    rw [Nat.cast_sum]
    refine Finset.sum_le_sum (fun qq _ => ?_)
    simp only [harmanPairTupleBound]
    push_cast
    have := sum_Icc_prime_le_diag_add (q := qq.2) (B := ⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))
      (fun p => (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / p)
        (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / p) p : ℝ)) (fun _ => Nat.cast_nonneg _)
    linarith
  -- the discarded quadruple tail
  have hD4N := sum_Ioc_harmanDiscardQuadrupleSum_le (a := ⌊y⌋₊) (b := ⌊y * (1 + θ)⌋₊)
    (harmanDiscardQuad_small (z := z) (Q := Q) (D := D) (E := E) hy1 hθ0.le hθ1 h11 hP)
  have hD4 : ((∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, harmanDiscardQuadrupleSum z D E n : ℕ) : ℝ)
      ≤ ∑ t ∈ harmanDiscardQuadSet z D E,
          (harmanQuadTupleBound (⌊y⌋₊ / quadProd t) (⌊y * (1 + θ)⌋₊ / quadProd t) t.2.2 : ℝ) := by
    refine (Nat.cast_le.2 hD4N).trans ?_
    rw [Nat.cast_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at hD2
  have e1 := hT1 θ hθ hθ1 z Q D E hP
  have e3 := hT3 θ hθ hθ1 z Q D E hP
  have e4 := hT4 θ hθ hθ1 z Q D E hP
  have e4d := hT4d θ hθ hθ1 z Q D E hP
  have e5 := hT5 θ hθ hθ1 z Q D E hP
  have e6 := hT6 θ hθ hθ1 z Q D E hP
  have hbox := harmanCrudeBoxes_le
  set P5 := (log ((3 / 11 + 1 / 1000000) / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((7 / 11 + 1 / 1000000) / 3 / (2 / 11)) + 1 / 100000) *
        (log ((5 / 11 + 1 / 1000000) / 2 / (2 / 11)) + 1 / 100000) with hP5
  set P4 := (log ((1 / 4 + 1 / 1000000) / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) *
        (log ((1 + 1 / 1000000) / 5 / (2 / 11)) + 1 / 100000) with hP4
  set C₀ := θ * y / log y with hC₀
  have hbox' : C₀ * (6 * P5) + C₀ * (6 * P4) ≤ C₀ * (97 / 10000) := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hbox hC₀0
  have e5' : (1 + 1 / 100000) * C₀ * 6 * P5 = (1 + 1 / 100000) * (C₀ * (6 * P5)) := by ring
  have e6' : (1 + 1 / 100000) * C₀ * 6 * P4 = (1 + 1 / 100000) * (C₀ * (6 * P4)) := by ring
  rw [hsum]
  linarith

end

end RHTower.Sieve
