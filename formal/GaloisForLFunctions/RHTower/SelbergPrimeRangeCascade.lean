import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# The prime part of Selberg's polynomial over ranges of primes

For reals `A < B` let `P_{(A,B]}` be the part of the prime polynomial `P_x` carried by the primes
`A < p ≤ B` (`selbergPrimeRangePoly`). For an antitone sequence of cutoffs `c_0 ≥ N_x ≥ c_1 ≥ ⋯`,
`P_x = Σ_{j<J} P_{(c_{j+1}, c_j]} + P_{(0, c_J]}` (`selbergPrimePoly_eq_sum_range`).

On `Re z = 1/2 + δ`, `0 < δ ≤ 1`, the coefficient energy of a range is at most
`A^{−δ}·20/δ²` (`sum_selbergPrimeRangeCoeff_sq_le_rpow`), since `n^{−1−2δ} ≤ A^{−δ} n^{−1−δ}`
for `n > A`. For any prime-supported polynomial of length `b` whose energy is `≤ V` on the columns
of the box `1/2 + 3R/4 ≤ Re ≤ 1/2 + 6R`, the heights near which it exceeds `M` have measure
`≤ 1380 m! V^m (T + 17R + 8b^m(1 + log b^m))/(π M^{2m})`
(`volume_largeNearBox_edPoly_primeSupported_le`). Large values of a finite sum are large values of
one summand (`largeNearBox_sum_subset`).
-/

noncomputable section

open Complex Set MeasureTheory ArithmeticFunction

namespace RHTower

/-- A Dirichlet polynomial does not see indices outside the support of its coefficients. -/
theorem edPoly_Icc_eq_of_support {a : ℕ → ℂ} {N b : ℕ} (h : ∀ n, a n ≠ 0 → n ≤ b ∧ n ≤ N)
    (z : ℂ) : edPoly a (Finset.Icc 1 N) z = edPoly a (Finset.Icc 1 b) z := by
  unfold edPoly
  have hsub : ∀ K : ℕ, min b N ≤ K → ∑ n ∈ Finset.Icc 1 (min b N), a n * ((n : ℝ) : ℂ) ^ (-z) =
      ∑ n ∈ Finset.Icc 1 K, a n * ((n : ℝ) : ℂ) ^ (-z) := by
    intro K hK
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hK) fun n hn hn' => ?_
    have : a n = 0 := by
      by_contra h0
      obtain ⟨h1, h2⟩ := h n h0
      apply hn'
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, le_min h1 h2⟩
    rw [this, zero_mul]
  rw [← hsub N (min_le_right _ _), ← hsub b (min_le_left _ _)]

/-- **Large values of a prime-supported polynomial near the box**, through the `m`-th moment. -/
theorem volume_largeNearBox_edPoly_primeSupported_le {a : ArithmeticFunction ℂ} {b : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (hab : ∀ k, a k ≠ 0 → k ≤ b) {T R M V : ℝ} {m : ℕ}
    (hT : 0 < T) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hM : 0 < M) (hm : 1 ≤ m)
    (hV : ∀ δ : ℝ, R / 2 ≤ δ → δ ≤ 1 →
      ∑ n ∈ Finset.Icc 1 b, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤ V) :
    volume (largeNearBox (edPoly (⇑a) (Finset.Icc 1 b)) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R
        M) ≤
      ENNReal.ofReal (1380 * (m.factorial * V ^ m *
        (T + 17 * R + 8 * (b ^ m : ℕ) * (1 + Real.log (b ^ m : ℕ)))) /
          (Real.pi * (M ^ m) ^ 2)) := by
  set Q : ℝ := m.factorial * V ^ m *
    (T + 17 * R + 8 * (b ^ m : ℕ) * (1 + Real.log (b ^ m : ℕ))) with hQ
  have hlogN : 0 ≤ 8 * ((b ^ m : ℕ) : ℝ) * (1 + Real.log (b ^ m : ℕ)) := by
    rcases Nat.eq_zero_or_pos (b ^ m) with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (b ^ m : ℕ) by exact_mod_cast hpos)
      positivity
  have hsub : largeNearBox (edPoly (⇑a) (Finset.Icc 1 b)) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R)
      R M ⊆ largeNearBox (fun z => edPoly (⇑a) (Finset.Icc 1 b) z ^ m) T (1 / 2 + 3 * R / 4)
        (1 / 2 + 6 * R) R (M ^ m) := by
    rintro t ⟨ht, z, h1, h2, h3, hz⟩
    refine ⟨ht, z, h1, h2, h3, ?_⟩
    rw [norm_pow]
    exact pow_lt_pow_left₀ hz hM.le (by omega)
  have hcol : ∀ c ∈ Icc (1 / 2 + 3 * R / 4 - R / 4) (1 / 2 + 6 * R + R / 4),
      ∫ y in (T - (7 : ℕ) * R)..(T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R),
        ‖(fun z => edPoly (⇑a) (Finset.Icc 1 b) z ^ m) ((c : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ Q := by
    intro c hc
    set δ := c - 1 / 2 with hδ
    have hδ0 : R / 2 ≤ δ := by rw [hδ]; linarith [hc.1]
    have hδ1 : δ ≤ 1 := by rw [hδ]; linarith [hc.2]
    have hceil : (⌈T / R⌉₊ : ℝ) ≤ T / R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlen : T - (7 : ℕ) * R ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R := by
      push_cast
      have : (0 : ℝ) ≤ ⌈T / R⌉₊ := Nat.cast_nonneg _
      nlinarith
    have hpt : ∀ y : ℝ, (fun z => edPoly (⇑a) (Finset.Icc 1 b) z ^ m) ((c : ℂ) + (y : ℂ) * I) =
        edPoly (⇑a) (Finset.Icc 1 b) (displacedLinePt (-δ) y) ^ m := by
      intro y
      simp only
      unfold displacedLinePt
      congr 3
      rw [hδ]; push_cast; ring
    simp_rw [hpt]
    refine (integral_norm_edPoly_pow_displaced_le ha hab (-δ) m _ _ hlen).trans ?_
    have hlen2 : T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) ≤ T + 17 * R := by
      push_cast
      have : (⌈T / R⌉₊ : ℝ) * R ≤ (T / R + 1) * R := mul_le_mul_of_nonneg_right hceil hR.le
      have e : (T / R + 1) * R = T + R := by field_simp
      nlinarith
    have hE0 : 0 ≤ ∑ n ∈ Finset.Icc 1 b, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hpow : (m.factorial : ℝ) * (∑ n ∈ Finset.Icc 1 b, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1)) ^ m ≤
        m.factorial * V ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE0 (hV δ hδ0 hδ1) m) (by positivity)
    have hA : 0 ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
        8 * ((b ^ m : ℕ) : ℝ) * (1 + Real.log (b ^ m : ℕ)) := by linarith
    calc (T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
          8 * ((b ^ m : ℕ) : ℝ) * (1 + Real.log (b ^ m : ℕ))) *
          (m.factorial * (∑ n ∈ Finset.Icc 1 b, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1)) ^ m)
        ≤ (T + 17 * R + 8 * ((b ^ m : ℕ) : ℝ) * (1 + Real.log (b ^ m : ℕ))) *
            (m.factorial * V ^ m) :=
          mul_le_mul (by linarith) hpow (by positivity) (by linarith)
      _ = Q := by rw [hQ]; ring
  have hdiff : Differentiable ℂ (fun z => edPoly (⇑a) (Finset.Icc 1 b) z ^ m) :=
    (differentiable_edPoly _ fun _ hn => (Finset.mem_Icc.mp hn).1).pow m
  have hbox := volume_largeNearBox_le hdiff
    (T := T) (a := 1 / 2 + 3 * R / 4) (b := 1 / 2 + 6 * R) (R := R) (r := R / 4) (M := M ^ m)
    (Q := Q) (by positivity) (by linarith) (by positivity) (by linarith) hcol
  refine (measure_mono hsub).trans (hbox.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  field_simp
  ring_nf

/-- Large values of a finite sum are large values of one summand. -/
theorem largeNearBox_sum_subset {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (Mj : ι → ℝ)
    {T a b R M : ℝ} (hM : ∑ j ∈ s, Mj j ≤ M) :
    largeNearBox (fun z => ∑ j ∈ s, F j z) T a b R M ⊆
      ⋃ j ∈ s, largeNearBox (F j) T a b R (Mj j) := by
  rintro t ⟨ht, z, h1, h2, h3, hz⟩
  by_contra hno
  simp only [mem_iUnion, not_exists] at hno
  have hle : ∀ j ∈ s, ‖F j z‖ ≤ Mj j := fun j hj => by
    by_contra hlt
    exact hno j hj ⟨ht, z, h1, h2, h3, not_le.mp hlt⟩
  have := (norm_sum_le s fun j => F j z).trans (Finset.sum_le_sum hle)
  linarith

/-! ## Ranges of primes -/

/-- The prime coefficients `Λ(p) W_x(p)` restricted to `A < p ≤ B`. -/
def selbergPrimeRangeCoeff (x A B : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime ∧ A < (n : ℝ) ∧ (n : ℝ) ≤ B then selbergPolyCoeff x n else 0,
    by simp [Nat.not_prime_zero]⟩

theorem selbergPrimeRangeCoeff_apply (x A B : ℝ) (n : ℕ) :
    selbergPrimeRangeCoeff x A B n =
      if n.Prime ∧ A < (n : ℝ) ∧ (n : ℝ) ≤ B then selbergPolyCoeff x n else 0 := rfl

/-- The range polynomial `P_{(A,B]}` over `1 ≤ n ≤ N_x`. -/
def selbergPrimeRangePoly (x A B : ℝ) (z : ℂ) : ℂ :=
  edPoly (⇑(selbergPrimeRangeCoeff x A B)) (Finset.Icc 1 (selbergPolyLength x)) z

theorem selbergPolyCoeff_eq_zero_of_length_lt {x : ℝ} (hx : 1 < x) {n : ℕ}
    (hn : selbergPolyLength x < n) : selbergPolyCoeff x n = 0 := by
  have hx2 : x ^ 2 ≤ n := by
    have h1 := Nat.le_ceil (x ^ 2)
    have h2 : (selbergPolyLength x : ℝ) < n := by exact_mod_cast hn
    unfold selbergPolyLength at h2
    linarith
  unfold selbergPolyCoeff
  rw [selbergWeight_eq_zero hx hx2]
  simp

theorem selbergPrimeRangeCoeff_support {x A B : ℝ} (hx : 1 < x) (k : ℕ)
    (hk : selbergPrimeRangeCoeff x A B k ≠ 0) :
    k.Prime ∧ A < (k : ℝ) ∧ (k : ℝ) ≤ B ∧ k ≤ selbergPolyLength x := by
  rw [selbergPrimeRangeCoeff_apply] at hk
  split_ifs at hk with h
  · refine ⟨h.1, h.2.1, h.2.2, ?_⟩
    by_contra hlt
    exact hk (selbergPolyCoeff_eq_zero_of_length_lt hx (not_le.mp hlt))
  · exact absurd rfl hk

/-- One step of the telescoping over cutoffs. -/
theorem selbergPrimeRangeCoeff_split (x A B C : ℝ) (hAB : A ≤ B) (hBC : B ≤ C) (n : ℕ) :
    selbergPrimeRangeCoeff x A C n =
      selbergPrimeRangeCoeff x B C n + selbergPrimeRangeCoeff x A B n := by
  simp only [selbergPrimeRangeCoeff_apply]
  by_cases hp : n.Prime
  · rcases le_or_gt (n : ℝ) A with h1 | h1
    · have h2 : ¬ A < (n : ℝ) := not_lt.mpr h1
      have h3 : ¬ B < (n : ℝ) := not_lt.mpr (h1.trans hAB)
      simp [hp, h2, h3]
    · rcases le_or_gt (n : ℝ) B with h2 | h2
      · have h3 : ¬ B < (n : ℝ) := not_lt.mpr h2
        have h4 : (n : ℝ) ≤ C := h2.trans hBC
        simp [hp, h1, h2, h3, h4]
      · rcases le_or_gt (n : ℝ) C with h3 | h3
        · have h4 : ¬ (n : ℝ) ≤ B := not_le.mpr h2
          simp [hp, h1, h2, h3, h4]
        · have h4 : ¬ (n : ℝ) ≤ C := not_le.mpr h3
          have h5 : ¬ (n : ℝ) ≤ B := not_le.mpr h2
          simp [hp, h4, h5]
  · simp [hp]

/-- **Telescoping of the prime coefficients over antitone cutoffs.** -/
theorem selbergPrimeCoeff_eq_sum_range {x : ℝ} (hx : 1 < x) {c : ℕ → ℝ} (hc : Antitone c)
    (hcpos : ∀ j, 0 ≤ c j) (hc0 : (selbergPolyLength x : ℝ) ≤ c 0) (J : ℕ) (n : ℕ) :
    selbergPrimeCoeff x n = ∑ j ∈ Finset.range J, selbergPrimeRangeCoeff x (c (j + 1)) (c j) n +
      selbergPrimeRangeCoeff x 0 (c J) n := by
  induction J with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    rw [selbergPrimeCoeff_apply, selbergPrimeRangeCoeff_apply]
    by_cases hp : n.Prime
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
      by_cases hn : (n : ℝ) ≤ c 0
      · simp [hp, hn0, hn]
      · have hlt : selbergPolyLength x < n := by
          have : (selbergPolyLength x : ℝ) < n := lt_of_le_of_lt hc0 (not_le.mp hn)
          exact_mod_cast this
        simp [hp, hn, selbergPolyCoeff_eq_zero_of_length_lt hx hlt]
    · simp [hp]
  | succ J ih =>
    rw [ih, Finset.sum_range_succ, add_assoc,
      selbergPrimeRangeCoeff_split x 0 (c (J + 1)) (c J) (hcpos _) (hc (Nat.le_succ J)) n]

/-- **Telescoping of the prime polynomial over antitone cutoffs.** -/
theorem selbergPrimePoly_eq_sum_range {x : ℝ} (hx : 1 < x) {c : ℕ → ℝ} (hc : Antitone c)
    (hcpos : ∀ j, 0 ≤ c j) (hc0 : (selbergPolyLength x : ℝ) ≤ c 0) (J : ℕ) (z : ℂ) :
    selbergPrimePoly x z = ∑ j ∈ Finset.range J, selbergPrimeRangePoly x (c (j + 1)) (c j) z +
      selbergPrimeRangePoly x 0 (c J) z := by
  unfold selbergPrimePoly selbergPrimeRangePoly edPoly
  simp_rw [selbergPrimeCoeff_eq_sum_range hx hc hcpos hc0 J, add_mul, Finset.sum_mul,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- A range polynomial is the Dirichlet polynomial of its coefficients over `1 ≤ n ≤ ⌊B⌋`. -/
theorem selbergPrimeRangePoly_eq {x A B : ℝ} (hx : 1 < x) (z : ℂ) :
    selbergPrimeRangePoly x A B z =
      edPoly (⇑(selbergPrimeRangeCoeff x A B)) (Finset.Icc 1 ⌊B⌋₊) z := by
  unfold selbergPrimeRangePoly
  refine edPoly_Icc_eq_of_support (fun n hn => ?_) z
  obtain ⟨-, -, hnB, hnN⟩ := selbergPrimeRangeCoeff_support hx n hn
  exact ⟨Nat.le_floor hnB, hnN⟩

/-! ## Energy of a range -/

/-- **The energy of the primes above `A`:** `Σ_{A < p ≤ B} |Λ(p)W(p)|² p^{−1−2δ} ≤ A^{−δ}·20/δ²`. -/
theorem sum_selbergPrimeRangeCoeff_sq_le_rpow {x A B δ : ℝ} (hx : 1 < x) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b : ℕ) :
    ∑ n ∈ Finset.Icc 1 b, ‖selbergPrimeRangeCoeff x A B n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
      A ^ (-δ) * (20 / δ ^ 2) := by
  have hA0 : 0 < A := by linarith
  have hAδ : 0 ≤ A ^ (-δ) := Real.rpow_nonneg hA0.le _
  have hsum := sum_vonMangoldt_sq_rpow_le (δ := δ / 2) (by positivity) (by linarith) b
  have e20 : 5 / (δ / 2) ^ 2 = 20 / δ ^ 2 := by field_simp; ring
  rw [e20] at hsum
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) ((Finset.mul_sum _ _ _).symm.le.trans
    (mul_le_mul_of_nonneg_left hsum hAδ))
  have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hp0 : 0 ≤ (n : ℝ) ^ (-1 - 2 * (δ / 2)) := Real.rpow_nonneg hn.le _
  rw [selbergPrimeRangeCoeff_apply]
  split_ifs with h
  · obtain ⟨-, hAn, -⟩ := h
    unfold selbergPolyCoeff
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have hW0 := selbergWeight_nonneg hx n
    have hW1 := selbergWeight_le_one hx n
    have hW : selbergWeight x n ^ 2 ≤ 1 := by nlinarith
    have hΛ : vonMangoldt n ^ 2 * selbergWeight x n ^ 2 ≤ vonMangoldt n ^ 2 := by
      nlinarith [sq_nonneg (vonMangoldt n)]
    have hsplit : (n : ℝ) ^ (2 * -δ - 1) = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-1 - 2 * (δ / 2)) := by
      rw [← Real.rpow_add hn]; congr 1; ring
    have hnA : (n : ℝ) ^ (-δ) ≤ A ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hA0 hAn.le (by linarith)
    rw [hsplit]
    calc vonMangoldt n ^ 2 * selbergWeight x n ^ 2 * ((n : ℝ) ^ (-δ) * (n : ℝ) ^ (-1 - 2 * (δ / 2)))
        ≤ vonMangoldt n ^ 2 * (A ^ (-δ) * (n : ℝ) ^ (-1 - 2 * (δ / 2))) := by
          apply mul_le_mul hΛ (mul_le_mul_of_nonneg_right hnA hp0) (by positivity) (sq_nonneg _)
      _ = A ^ (-δ) * (vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * (δ / 2))) := by ring
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg hAδ (mul_nonneg (sq_nonneg _) hp0)

/-- **The energy of the small primes:** `Σ_{p ≤ b} |Λ(p)W(p)|² p^{−1−2δ} ≤ log b (log b + C)`. -/
theorem exists_sum_selbergPrimeRangeCoeff_sq_le_log :
    ∃ C : ℝ, ∀ {x A B δ : ℝ}, 1 < x → 0 ≤ δ → ∀ b : ℕ, 1 ≤ b →
      ∑ n ∈ Finset.Icc 1 b, ‖selbergPrimeRangeCoeff x A B n‖ ^ 2 * (n : ℝ) ^ (2 * -δ - 1) ≤
        Real.log b * (Real.log b + C) := by
  obtain ⟨C, hC⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨C, fun {x A B δ} hx hδ b hb => le_trans (Finset.sum_le_sum fun n hn => ?_) (hC b hb)⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn : (0 : ℝ) < n := by linarith
  have hpow : (n : ℝ) ^ (2 * -δ - 1) ≤ (n : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hp0 : 0 ≤ (n : ℝ) ^ (2 * -δ - 1) := Real.rpow_nonneg hn.le _
  rw [div_eq_mul_inv]
  rw [selbergPrimeRangeCoeff_apply]
  split_ifs with h
  · unfold selbergPolyCoeff
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    have hW0 := selbergWeight_nonneg hx n
    have hW1 := selbergWeight_le_one hx n
    have hW : selbergWeight x n ^ 2 ≤ 1 := by nlinarith
    have hΛ : vonMangoldt n ^ 2 * selbergWeight x n ^ 2 ≤ vonMangoldt n ^ 2 := by
      nlinarith [sq_nonneg (vonMangoldt n)]
    exact mul_le_mul hΛ hpow hp0 (sq_nonneg _)
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hn.le)

end RHTower
