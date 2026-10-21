import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineFejer
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

set_option autoImplicit false

/-!
# Dilated Fejér weights and the divisor bound

The Fejér weight `P_K(θ) = |Σ_{a<K} e(aθ)|²` satisfies `P_K ≤ K²` and `P_K(θ) · 4‖θ‖² ≤ 1`
(`‖θ‖` the distance to `ℤ`). For the Fourier transform of the Fejér majorant one needs, at a
frequency `ξ`, the dilated sum `Σ_{n ∼ M₁} P_K(ξ/n)`:

* for `|ξ| ≤ M₁/2` every `ξ/n` lies in `(−1/2, 1/2)`, so `P_K(ξ/n) ≤ 2K² λ(Kξ/M₁)` with the
  Lorentzian `λ(x) = (1 + x²)⁻¹` (`fejerWeight_div_le_low`);
* for `M₁/2 < |ξ| ≤ Ξ` (`sum_fejerWeight_div_le`): writing `ℓ = round(ξ/n)`, the terms with
  `ℓ = 0` are `≤ 4`, and the others are `≤ 2K² λ(K(ξ − s)/M₁)` with `s = ℓ n ≠ 0`. Each nonzero
  integer `s` arises from at most `d(|s|) ≤ C_ε (3Ξ)^ε` values `n ∣ s`, and a Lorentzian summed
  over integers is `≤ 2(1 + π/a)` (`sum_lorentz_int_le`), so

  `Σ_{n ∼ M₁} P_K(ξ/n) ≤ 12 M₁ + C_ε (3Ξ)^ε (4K² + 4π K M₁)`.

This is the only place where arithmetic enters Guth–Maynard's Lemma 9.2: the number of
factorisations `s = ℓ m₁`.
-/

open MeasureTheory Finset Real

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (finitePhaseProgression unitPhaseDistance divisorBoundConst)

/-- The Fejér weight `P_K(θ) = |D_K(θ)|²`. -/
def fejerWeight (K : ℕ) (θ : ℝ) : ℝ :=
  ‖finitePhaseProgression K θ‖ ^ 2

/-- The Lorentzian `(1 + (a x)²)⁻¹`. -/
def lorentz (a x : ℝ) : ℝ :=
  (1 + (a * x) ^ 2)⁻¹

theorem fejerWeight_nonneg (K : ℕ) (θ : ℝ) : 0 ≤ fejerWeight K θ := sq_nonneg _

theorem fejerWeight_le (K : ℕ) (θ : ℝ) : fejerWeight K θ ≤ (K : ℝ) ^ 2 := by
  unfold fejerWeight
  have := RHTower.Sieve.norm_finitePhaseProgression_le_length K θ
  gcongr

/-- `P_K(θ) · 4 ‖θ‖² ≤ 1`, with `‖θ‖ = |θ − round θ|`. -/
theorem fejerWeight_mul_dist_le (K : ℕ) (θ : ℝ) :
    fejerWeight K θ * (4 * |θ - round θ| ^ 2) ≤ 1 := by
  rw [← RHTower.Sieve.unitPhaseDistance_eq_abs_sub_round]
  have hd0 : 0 ≤ unitPhaseDistance θ := norm_nonneg _
  rcases hd0.eq_or_lt with hd | hd
  · rw [← hd]
    norm_num
  · have h := RHTower.Sieve.norm_finitePhaseProgression_le_inv_distance K hd.ne'
    rw [le_div_iff₀ (by positivity)] at h
    have hx0 : 0 ≤ ‖finitePhaseProgression K θ‖ * (2 * unitPhaseDistance θ) := by positivity
    calc fejerWeight K θ * (4 * unitPhaseDistance θ ^ 2)
        = (‖finitePhaseProgression K θ‖ * (2 * unitPhaseDistance θ)) ^ 2 := by
          unfold fejerWeight
          ring
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ hx0 h 2
      _ = 1 := one_pow 2

theorem lorentz_pos (a x : ℝ) : 0 < lorentz a x := inv_pos.mpr (by positivity)

theorem lorentz_le_one (a x : ℝ) : lorentz a x ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (a * x)])

/-- The Lorentzian decreases in `|x|`. -/
theorem lorentz_anti (a : ℝ) {x y : ℝ} (h : |x| ≤ |y|) : lorentz a y ≤ lorentz a x := by
  unfold lorentz
  apply inv_anti₀ (by positivity)
  have : (a * x) ^ 2 ≤ (a * y) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left (sq_le_sq.mpr h) (sq_nonneg a)
  linarith

theorem integrable_lorentz {a : ℝ} (ha : a ≠ 0) : Integrable (lorentz a) :=
  (integrable_inv_one_add_sq).comp_mul_left' ha

/-- `∫ (1 + (a x)²)⁻¹ dx = π / a`. -/
theorem integral_lorentz {a : ℝ} (ha : 0 < a) : ∫ x, lorentz a x = π / a := by
  have h := Measure.integral_comp_mul_left (fun y : ℝ => (1 + y ^ 2)⁻¹) a
  show ∫ x, (1 + (a * x) ^ 2)⁻¹ = π / a
  rw [h, integral_univ_inv_one_add_sq, smul_eq_mul, abs_inv, abs_of_pos ha]
  ring

/-- **Harmonic-mean bound.** `0 ≤ P ≤ K²` and `P t² ≤ M²` give `P ≤ 2K² λ(Kt/M)`. -/
theorem le_two_mul_lorentz {P K M t : ℝ} (hPK : P ≤ K ^ 2) (hPt : P * t ^ 2 ≤ M ^ 2)
    (hM : 0 < M) : P ≤ 2 * K ^ 2 * lorentz (K / M) t := by
  have hM' : M ≠ 0 := hM.ne'
  unfold lorentz
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : P * (K / M * t) ^ 2 = K ^ 2 * (P * t ^ 2) / M ^ 2 := by
    field_simp
  have h2 : K ^ 2 * (P * t ^ 2) / M ^ 2 ≤ K ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hPt (sq_nonneg K)
  have h3 : P * (1 + (K / M * t) ^ 2) = P + P * (K / M * t) ^ 2 := by ring
  linarith

/-! ### Lorentzians summed over integers -/

/-- `Σ_{k ∈ T} λ(a k) ≤ 1 + π/a` for a finite set of naturals. -/
theorem sum_lorentz_nat_le {a : ℝ} (ha : 0 < a) (T : Finset ℕ) :
    ∑ k ∈ T, lorentz a k ≤ 1 + π / a := by
  set N := T.sup id
  have hsub : T ⊆ range (N + 1) := fun k hk =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hanti : AntitoneOn (lorentz a) (Set.Icc (0 : ℝ) (0 + N)) := fun x hx y hy hxy =>
    lorentz_anti a (by rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]; exact hxy)
  have hint := AntitoneOn.sum_le_integral hanti
  simp only [zero_add] at hint
  have hII : ∫ x in (0 : ℝ)..N, lorentz a x ≤ π / a := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N), ← integral_lorentz ha]
    exact setIntegral_le_integral (integrable_lorentz ha.ne')
      (Filter.Eventually.of_forall fun x => (lorentz_pos a x).le)
  calc ∑ k ∈ T, lorentz a k ≤ ∑ k ∈ range (N + 1), lorentz a k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => (lorentz_pos a k).le
    _ = lorentz a 0 + ∑ i ∈ range N, lorentz a ((i + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_range_succ', Nat.cast_zero]
        ring
    _ ≤ 1 + π / a := by
        have h0 := lorentz_le_one a 0
        have hsum : ∑ i ∈ range N, lorentz a ((i + 1 : ℕ) : ℝ) ≤ π / a := hint.trans hII
        linarith

/-- **Lattice Lorentzian sum.** `Σ_{s ∈ S} λ(a(x − s)) ≤ 2(1 + π/a)` for any finite `S ⊆ ℤ`. -/
theorem sum_lorentz_int_le {a : ℝ} (ha : 0 < a) (x : ℝ) (S : Finset ℤ) :
    ∑ s ∈ S, lorentz a (x - s) ≤ 2 * (1 + π / a) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun s : ℤ => (s : ℝ) ≤ x)]
  -- left of `x`: `s ↦ ⌊x⌋ − s`
  have hleft : ∑ s ∈ S.filter (fun s : ℤ => (s : ℝ) ≤ x), lorentz a (x - s) ≤ 1 + π / a := by
    set j : ℤ → ℕ := fun s => (⌊x⌋ - s).toNat
    have hj : ∀ s ∈ S.filter (fun s : ℤ => (s : ℝ) ≤ x), (j s : ℝ) = ⌊x⌋ - s := fun s hs => by
      have : s ≤ ⌊x⌋ := Int.le_floor.mpr (Finset.mem_filter.mp hs).2
      simp only [j]
      rw [show ((⌊x⌋ - s).toNat : ℝ) = (((⌊x⌋ - s).toNat : ℤ) : ℝ) from rfl,
        Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have hinj : Set.InjOn j ↑(S.filter (fun s : ℤ => (s : ℝ) ≤ x)) := fun s hs s' hs' h => by
      have e1 := hj s hs
      have e2 := hj s' hs'
      rw [h] at e1
      exact_mod_cast (by linarith : (s : ℝ) = s')
    have hle : ∀ s ∈ S.filter (fun s : ℤ => (s : ℝ) ≤ x), |((j s : ℕ) : ℝ)| ≤ |x - s| :=
      fun s hs => by
        have hs' := (Finset.mem_filter.mp hs).2
        have hfl' : (s : ℝ) ≤ ⌊x⌋ := by exact_mod_cast Int.le_floor.mpr hs'
        rw [hj s hs, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith [Int.floor_le x]
    calc ∑ s ∈ S.filter (fun s : ℤ => (s : ℝ) ≤ x), lorentz a (x - s)
        ≤ ∑ s ∈ S.filter (fun s : ℤ => (s : ℝ) ≤ x), lorentz a (j s) :=
          Finset.sum_le_sum fun s hs => lorentz_anti a (hle s hs)
      _ = ∑ k ∈ (S.filter (fun s : ℤ => (s : ℝ) ≤ x)).image j, lorentz a k :=
          (Finset.sum_image (f := fun k : ℕ => lorentz a k) hinj).symm
      _ ≤ 1 + π / a := sum_lorentz_nat_le ha _
  -- right of `x`: `s ↦ s − ⌈x⌉`
  have hright : ∑ s ∈ S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x), lorentz a (x - s) ≤ 1 + π / a := by
    set j : ℤ → ℕ := fun s => (s - ⌈x⌉).toNat
    have hj : ∀ s ∈ S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x), (j s : ℝ) = s - ⌈x⌉ := fun s hs => by
      have : ⌈x⌉ ≤ s := Int.ceil_le.mpr (not_le.mp (Finset.mem_filter.mp hs).2).le
      simp only [j]
      rw [show ((s - ⌈x⌉).toNat : ℝ) = (((s - ⌈x⌉).toNat : ℤ) : ℝ) from rfl,
        Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have hinj : Set.InjOn j ↑(S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x)) := fun s hs s' hs' h => by
      have e1 := hj s hs
      have e2 := hj s' hs'
      rw [h] at e1
      exact_mod_cast (by linarith : (s : ℝ) = s')
    have hle : ∀ s ∈ S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x), |((j s : ℕ) : ℝ)| ≤ |x - s| :=
      fun s hs => by
        have hlt := not_le.mp (Finset.mem_filter.mp hs).2
        have hce : (⌈x⌉ : ℝ) ≤ s := by exact_mod_cast Int.ceil_le.mpr hlt.le
        rw [hj s hs, abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
        linarith [Int.le_ceil x]
    calc ∑ s ∈ S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x), lorentz a (x - s)
        ≤ ∑ s ∈ S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x), lorentz a (j s) :=
          Finset.sum_le_sum fun s hs => lorentz_anti a (hle s hs)
      _ = ∑ k ∈ (S.filter (fun s : ℤ => ¬ (s : ℝ) ≤ x)).image j, lorentz a k :=
          (Finset.sum_image (f := fun k : ℕ => lorentz a k) hinj).symm
      _ ≤ 1 + π / a := sum_lorentz_nat_le ha _
  linarith

/-! ### The dilated Fejér sums -/

/-- **Low frequencies.** For `|ξ| ≤ M₁/2` and `n ∼ M₁`: `P_K(ξ/n) ≤ 2K² λ(Kξ/M₁)`. -/
theorem fejerWeight_div_le_low (K : ℕ) {M₁ ξ : ℝ} {n : ℕ} (hn : n ∈ dyadicNat M₁)
    (hξ : |ξ| ≤ M₁ / 2) : fejerWeight K (ξ / n) ≤ 2 * (K : ℝ) ^ 2 * lorentz (K / M₁) ξ := by
  obtain ⟨hn1, hn2⟩ := mem_dyadicNat.mp hn
  have hM₁ := half_le_of_mem_dyadicNat hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ : |ξ / n| < 1 / 2 := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    linarith
  have hround : round (ξ / n) = 0 :=
    round_eq_zero_iff.mpr ⟨by linarith [neg_abs_le (ξ / n)], by linarith [le_abs_self (ξ / n)]⟩
  have hmain := fejerWeight_mul_dist_le K (ξ / n)
  rw [hround, Int.cast_zero, sub_zero, sq_abs, div_pow] at hmain
  refine le_two_mul_lorentz (fejerWeight_le _ _) ?_ (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hmain (sq_nonneg (n : ℝ))
  have h2 : fejerWeight K (ξ / n) * (4 * (ξ ^ 2 / (n : ℝ) ^ 2)) * (n : ℝ) ^ 2 =
      4 * (fejerWeight K (ξ / n) * ξ ^ 2) := by
    field_simp
  have h3 : (n : ℝ) ^ 2 ≤ (2 * M₁) ^ 2 := by gcongr
  nlinarith

theorem divisorBoundConst_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ divisorBoundConst ε := by
  have h1 := RHTower.Sieve.card_divisors_le_rpow hε (n := 1) one_ne_zero
  simp only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Real.one_rpow,
    mul_one] at h1
  linarith

/-- The divisor bound in the form used here: `d(n) ≤ C_ε X^ε` for `1 ≤ n ≤ X`. -/
theorem card_divisors_le_of_le {ε X : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) (hX : (n : ℝ) ≤ X) :
    (n.divisors.card : ℝ) ≤ divisorBoundConst ε * X ^ ε :=
  (RHTower.Sieve.card_divisors_le_rpow hε hn).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le)
      (divisorBoundConst_nonneg hε))

/-- **High frequencies.** For `M₁/2 < |ξ| ≤ Ξ`:
`Σ_{n ∼ M₁} P_K(ξ/n) ≤ 12 M₁ + C_ε (3Ξ)^ε (4K² + 4π K M₁)`. -/
theorem sum_fejerWeight_div_le {K : ℕ} (hK : 1 ≤ K) {M₁ ξ Ξ ε : ℝ} (hM₁ : 1 / 2 ≤ M₁)
    (hε : 0 < ε) (hξ1 : M₁ / 2 < |ξ|) (hξ2 : |ξ| ≤ Ξ) :
    ∑ n ∈ dyadicNat M₁, fejerWeight K (ξ / n) ≤
      12 * M₁ + divisorBoundConst ε * (3 * Ξ) ^ ε * (4 * (K : ℝ) ^ 2 + 4 * π * K * M₁) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : 0 < M₁ := by linarith
  have hΞ0 : 0 < Ξ := by linarith [abs_nonneg ξ]
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℤ, s = fun n : ℕ => round (ξ / (n : ℝ)) * (n : ℤ) := ⟨_, rfl⟩
  have hn0 : ∀ n ∈ dyadicNat M₁, (0 : ℝ) < n := fun n hn => by
    exact_mod_cast one_le_of_mem_dyadicNat hn
  have hsn : ∀ n : ℕ, ((s n : ℤ) : ℝ) = (round (ξ / n) : ℝ) * n := fun n => by
    rw [hs]
    push_cast
    ring
  -- `P(ξ/n) · (ξ − s n)² ≤ M₁²`, from `P(θ) · 4‖θ‖² ≤ 1`
  have hdist : ∀ n ∈ dyadicNat M₁, fejerWeight K (ξ / n) * (ξ - s n) ^ 2 ≤ M₁ ^ 2 := by
    intro n hn
    have hn' := hn0 n hn
    have hn'' : (n : ℝ) ≠ 0 := hn'.ne'
    have h2 := (mem_dyadicNat.mp hn).2
    have hmain := fejerWeight_mul_dist_le K (ξ / n)
    have heq : 4 * |ξ / n - round (ξ / n)| ^ 2 = 4 * (ξ - s n) ^ 2 / (n : ℝ) ^ 2 := by
      rw [sq_abs, hsn]
      field_simp
    rw [heq, mul_div_assoc', div_le_one (by positivity)] at hmain
    have h3 : (n : ℝ) ^ 2 ≤ (2 * M₁) ^ 2 := by gcongr
    nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not (dyadicNat M₁) (fun n : ℕ => round (ξ / (n : ℝ)) = 0)]
  -- `round(ξ/n) = 0`: the weight is at most `4`
  have hfour : ∀ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0),
      fejerWeight K (ξ / n) ≤ 4 := by
    intro n hn
    obtain ⟨hn, hr⟩ := Finset.mem_filter.mp hn
    have hd := hdist n hn
    rw [hsn, hr, Int.cast_zero, zero_mul, sub_zero] at hd
    have hP0 := fejerWeight_nonneg K (ξ / n)
    have hξ2' : M₁ ^ 2 < 4 * ξ ^ 2 := by
      have : (M₁ / 2) ^ 2 < |ξ| ^ 2 := by gcongr
      rw [sq_abs] at this
      linarith
    by_contra hcon
    have hξpos : 0 < ξ ^ 2 := by nlinarith
    have := mul_lt_mul_of_pos_right (not_le.mp hcon) hξpos
    linarith
  have hzero : ∑ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), fejerWeight K (ξ / n) ≤
      12 * M₁ := by
    calc ∑ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), fejerWeight K (ξ / n)
        ≤ ∑ _n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), (4 : ℝ) :=
          Finset.sum_le_sum hfour
      _ ≤ ∑ _n ∈ dyadicNat M₁, (4 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by norm_num
      _ = (dyadicNat M₁).card * 4 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * M₁ * 4 := by gcongr; exact card_dyadicNat_le_three_mul hM₁
      _ = 12 * M₁ := by ring
  -- `round(ξ/n) ≠ 0`: group by `s = round(ξ/n) · n` and count divisors
  set dmax := divisorBoundConst ε * (3 * Ξ) ^ ε with hdmax
  have hdmax0 : 0 ≤ dmax := mul_nonneg (divisorBoundConst_nonneg hε) (Real.rpow_nonneg (by linarith) _)
  set A := (dyadicNat M₁).filter (fun n : ℕ => ¬ round (ξ / (n : ℝ)) = 0) with hA
  have hAmem : ∀ n ∈ A, n ∈ dyadicNat M₁ ∧ round (ξ / n) ≠ 0 := fun n hn => Finset.mem_filter.mp hn
  have hsbound : ∀ n ∈ A, s n ≠ 0 ∧ |((s n : ℤ) : ℝ)| ≤ 3 * Ξ := by
    intro n hn
    obtain ⟨hn, hr⟩ := hAmem n hn
    have hn' := hn0 n hn
    have h2 := (mem_dyadicNat.mp hn).2
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact mul_ne_zero hr (by exact_mod_cast hn'.ne')
    · have hround := abs_sub_round (ξ / n)
      have h3 : |(s n : ℝ) - ξ| ≤ n / 2 := by
        have : (s n : ℝ) - ξ = -((ξ / n - round (ξ / n)) * n) := by
          rw [hsn]
          field_simp
          ring
        rw [this, abs_neg, abs_mul, abs_of_pos hn']
        nlinarith [abs_nonneg (ξ / n - round (ξ / n))]
      have := abs_sub_abs_le_abs_sub (s n : ℝ) ξ
      linarith
  have hterm : ∀ n ∈ A, fejerWeight K (ξ / n) ≤ 2 * (K : ℝ) ^ 2 * lorentz (K / M₁) (ξ - s n) :=
    fun n hn => le_two_mul_lorentz (fejerWeight_le _ _) (hdist n (hAmem n hn).1) hM0
  have hfib : ∀ t ∈ A.image s, ((A.filter fun n => s n = t).card : ℝ) ≤ dmax := by
    intro t ht
    obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hs0, hsb⟩ := hsbound n₀ hn₀
    have hsub : A.filter (fun n => s n = s n₀) ⊆ (s n₀).natAbs.divisors := by
      intro n hn
      obtain ⟨-, hns⟩ := Finset.mem_filter.mp hn
      rw [Nat.mem_divisors]
      refine ⟨?_, Int.natAbs_ne_zero.mpr hs0⟩
      rw [← hns, hs]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      exact Dvd.intro_left _ rfl
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (card_divisors_le_of_le hε (Int.natAbs_ne_zero.mpr hs0) ?_)
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hsb
  have hnonzero : ∑ n ∈ A, fejerWeight K (ξ / n) ≤ dmax * (4 * (K : ℝ) ^ 2 + 4 * π * K * M₁) := by
    calc ∑ n ∈ A, fejerWeight K (ξ / n)
        ≤ ∑ n ∈ A, 2 * (K : ℝ) ^ 2 * lorentz (K / M₁) (ξ - s n) := Finset.sum_le_sum hterm
      _ = ∑ t ∈ A.image s, (A.filter fun n => s n = t).card •
            (2 * (K : ℝ) ^ 2 * lorentz (K / M₁) (ξ - t)) :=
          Finset.sum_comp (fun t : ℤ => 2 * (K : ℝ) ^ 2 * lorentz (K / M₁) (ξ - t)) s
      _ ≤ ∑ t ∈ A.image s, dmax * (2 * (K : ℝ) ^ 2 * lorentz (K / M₁) (ξ - t)) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hfib t ht)
            (mul_nonneg (by positivity) (lorentz_pos _ _).le)
      _ = dmax * (2 * (K : ℝ) ^ 2) * ∑ t ∈ A.image s, lorentz (K / M₁) (ξ - t) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ ≤ dmax * (2 * (K : ℝ) ^ 2) * (2 * (1 + π / (K / M₁))) :=
          mul_le_mul_of_nonneg_left (sum_lorentz_int_le (div_pos hK0 hM0) ξ _)
            (mul_nonneg hdmax0 (by positivity))
      _ = dmax * (4 * (K : ℝ) ^ 2 + 4 * π * K * M₁) := by
          field_simp
          ring
  linarith

end

end RHTower.GuthMaynard
