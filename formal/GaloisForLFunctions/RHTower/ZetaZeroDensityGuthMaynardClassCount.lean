import GaloisForLFunctions.RHTower.ZetaZeroDensityWindowClassCount
import GaloisForLFunctions.RHTower.DirichletPolynomialLargeValueCounts
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.RouteTHybridZetaAssembly
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLargeValuesStatement
import GaloisForLFunctions.RHTower.ZetaZeroDensityGuthMaynardExponentLemmas

/-!
# The Guth–Maynard class count

A Type I class of the zero detector is a `1`-separated set `W ⊆ [T, 2T]` on which a block
polynomial `P` of length `2^j ∈ [T^{δ/2}, T^{3a/4}(log T)²]` is at least `1/(48J)`.  A power
`ℓ ≤ M` puts `X = (2^j)^ℓ` in the window `[T^a, T^{3a/2}(log T)⁴]` (`exists_pow_mem_window`).
Two estimates for `P^ℓ` (Guth–Maynard, Section 13.1):

* `X ≤ T^α`: the large values estimate `GuthMaynardLargeValuesBound` for `X^σ P^ℓ`, whose
  coefficients are at most `d(n)^{2ℓ} ≤ T^{o(1)}`, split into `ℓ + 1` dyadic blocks.  It gives
  `|W| ⪅ X^{2-2σ} + X^{18/5-4σ} + T X^{12/5-4σ} ≤ T^{3a(1-σ)} + T^{α(18/5-4σ)} + T^{1+a(12/5-4σ)}`;
* `X > T^α`: the mean value theorem, `|W| ⪅ X^{2-2σ} + T X^{1-2σ} ≤ T^{3a(1-σ)} + T^{1+α(1-2σ)}`.

If each of these four exponents is at most `E₀`, every class count is `≤ K T^{E₀ + ε}`
(`exists_gm_window_class_card_le`).
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Complex Finset Filter RHTower.Sieve RHTower.GuthMaynard

/-! ## The large values estimate on several dyadic blocks -/

/-- **The large values estimate on `R` dyadic blocks.**  If `|Σ_{N₀ < n ≤ 2^R N₀} b_n n^{it}| ≥ V`
on a `1`-separated `W ⊆ [T₀, T₀ + T]` with `‖b_n‖ ≤ B`, then one of the blocks
`(2^r N₀, 2^{r+1} N₀]` carries `V/R` on a `1/R` share of `W`, and with `L = 2^R N₀`:
`|W| ≤ R C T^ε (B² L²/(V/R)² + B⁴ L^{18/5}/(V/R)⁴ + T B⁴ L^{12/5}/(V/R)⁴)`. -/
theorem GuthMaynard.GuthMaynardLargeValuesBound.card_le_of_dyadic_range
    (hGM : GuthMaynardLargeValuesBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ R : ℕ) (T T₀ V B : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N₀ → 1 ≤ R → 2 ≤ T → 0 < V → 0 < B → (∀ n, ‖b n‖ ≤ B) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤
        ‖∑ n ∈ Finset.Ioc N₀ (N₀ * 2 ^ R), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ R * (C * T ^ ε * (B ^ 2 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ 2 / (V / R) ^ 2
        + B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (18/5 : ℝ) / (V / R) ^ 4
        + T * B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (12/5 : ℝ) / (V / R) ^ 4)) := by
  classical
  obtain ⟨C, hC, hsc⟩ := hGM.scaled hε
  refine ⟨C, hC, fun N₀ R T T₀ V B b W hN₀ hR hT hV hB hb hW hsep hbig => ?_⟩
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hVR : 0 < V / R := div_pos hV hRpos
  -- the `r`-th dyadic block at `t`
  have hpick : ∀ t ∈ W, ∃ r ∈ range R, V / R ≤
      ‖∑ n ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
        b n * Complex.exp (Complex.I * t * Real.log n)‖ := by
    intro t ht
    have h := hbig t ht
    rw [Sieve.sum_Ioc_dyadic] at h
    by_contra hcon
    push Not at hcon
    have hlt := Finset.sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by omega)) hcon
    have hsum : ∑ _r ∈ range R, V / (R : ℝ) = V := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp
    linarith [norm_sum_le (range R) (fun r => ∑ n ∈ Finset.Ioc (N₀ * 2 ^ r) (N₀ * 2 ^ (r + 1)),
      b n * Complex.exp (Complex.I * t * Real.log n))]
  choose! rsel hrsel using hpick
  obtain ⟨r, hr, hfib⟩ := exists_fiber_card_ge W (range R) rsel (fun t ht => (hrsel t ht).1)
    (nonempty_range_iff.mpr (by omega))
  rw [card_range] at hfib
  have hr' : r < R := mem_range.mp hr
  have hN1 : 1 ≤ N₀ * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hWr := hsc (N₀ * 2 ^ r) T T₀ (V / R) B b (W.filter (fun t => rsel t = r)) hN1 hT hVR hB hb
    (fun t ht => hW t (mem_filter.mp ht).1)
    (fun t ht t' ht' => hsep t (mem_filter.mp ht).1 t' (mem_filter.mp ht').1)
    (fun t ht => by
      obtain ⟨ht1, ht2⟩ := mem_filter.mp ht
      have h := (hrsel t ht1).2
      rw [ht2, show N₀ * 2 ^ (r + 1) = 2 * (N₀ * 2 ^ r) by ring] at h
      exact h)
  -- the block length is at most `L = 2^R N₀`
  have hNL : ((N₀ * 2 ^ r : ℕ) : ℝ) ≤ ((N₀ * 2 ^ R : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr'.le)
  have hN0 : (0 : ℝ) ≤ ((N₀ * 2 ^ r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hT0 : 0 ≤ T := by linarith
  have hterms : B ^ 2 * ((N₀ * 2 ^ r : ℕ) : ℝ) ^ 2 / (V / R) ^ 2
      + B ^ 4 * ((N₀ * 2 ^ r : ℕ) : ℝ) ^ (18/5 : ℝ) / (V / R) ^ 4
      + T * B ^ 4 * ((N₀ * 2 ^ r : ℕ) : ℝ) ^ (12/5 : ℝ) / (V / R) ^ 4
      ≤ B ^ 2 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ 2 / (V / R) ^ 2
      + B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (18/5 : ℝ) / (V / R) ^ 4
      + T * B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (12/5 : ℝ) / (V / R) ^ 4 := by
    gcongr
  calc (W.card : ℝ) ≤ R * ((W.filter (fun t => rsel t = r)).card : ℝ) := hfib
    _ ≤ R * (C * T ^ ε * (B ^ 2 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ 2 / (V / R) ^ 2
          + B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (18/5 : ℝ) / (V / R) ^ 4
          + T * B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (12/5 : ℝ) / (V / R) ^ 4)) := by
        refine mul_le_mul_of_nonneg_left (le_trans hWr ?_) hRpos.le
        exact mul_le_mul_of_nonneg_left hterms (by positivity)

/-! ## The raised class polynomial in Guth–Maynard form -/

/-- `Σ_{n ∈ S} a_n n^{it}` and `Σ_{n ∈ S} a_n n^{-it}` are complex conjugate for real `a`. -/
theorem norm_sum_ofReal_mul_cexp_eq_norm_dpoly (a : ℕ → ℝ) (S : Finset ℕ) (t : ℝ) :
    ‖∑ n ∈ S, (a n : ℂ) * Complex.exp (Complex.I * t * Real.log n)‖ = ‖dpoly a S t‖ := by
  rw [← Complex.norm_conj (dpoly a S t), dpoly, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [cterm, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **Normalized coefficients.**  For `S ⊆ (A, C]` and `s ≥ 0`, the coefficients `s·g` on `S`
(zero elsewhere) give `|Σ_{A < n ≤ C} (s g)_n n^{it}| = s |Σ_{n ∈ S} g_n n^{-it}|`. -/
theorem norm_sum_Ioc_dpolySupportCoeff_eq {g : ℕ → ℝ} {S : Finset ℕ} {A C : ℕ}
    (hS : S ⊆ Finset.Ioc A C) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc A C,
        dpolySupportCoeff (fun n => s * g n) S n * Complex.exp (Complex.I * t * Real.log n)‖
      = s * ‖dpoly g S t‖ := by
  have hsum : ∑ n ∈ Finset.Ioc A C,
        dpolySupportCoeff (fun n => s * g n) S n * Complex.exp (Complex.I * t * Real.log n)
      = ∑ n ∈ S, ((s * g n : ℝ) : ℂ) * Complex.exp (Complex.I * t * Real.log n) := by
    rw [← Finset.sum_subset hS]
    · exact Finset.sum_congr rfl fun n hn => by rw [dpolySupportCoeff, if_pos hn]
    · intro n _ hn
      rw [dpolySupportCoeff, if_neg hn, zero_mul]
  have hscale : dpoly (fun n => s * g n) S t = (s : ℂ) * dpoly g S t := by
    unfold dpoly cterm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [hsum, norm_sum_ofReal_mul_cexp_eq_norm_dpoly (fun n => s * g n), hscale, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hs]

/-- **The coefficient bound.**  On the block `[2^j, 2^{j+1})` with divisor-bounded class
coefficients, the `ℓ`-th power normalized by `X^σ`, `X = (2^j)^ℓ`, has coefficients
`≤ d(n)^{2ℓ}`; with `n ≤ T³` and `ℓ ≤ M` this is at most `((C_η + 1) T^{3η})^{2M}`. -/
theorem norm_dpolySupportCoeff_powConv_le {B : Finset ℕ} {c : ℕ → ℝ} {Λ σ σ' η T : ℝ}
    {j i ℓ M : ℕ} (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1)
    (hBΛ : ∀ k ∈ B, Real.log k ≤ Λ) (hc : ∀ k ∈ B, |c k| ≤ k.divisors.card) (hσ : 0 ≤ σ)
    (hσσ' : σ ≤ σ') (hℓ : 1 ≤ ℓ) (hℓM : ℓ ≤ M) (hη : 0 < η) (hT : 1 ≤ T)
    (hlen : ∀ n ∈ powSupport B ℓ, (n : ℝ) ≤ T ^ (3 : ℝ)) (n : ℕ) :
    ‖dpolySupportCoeff (fun n => ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ σ *
        powConv (genClassCoeff c Λ i σ') B ℓ n) (powSupport B ℓ) n‖
      ≤ ((divisorBoundConst η + 1) * T ^ (3 * η)) ^ (2 * M) := by
  have hT0 : 0 < T := by linarith
  have hCη := divisorBoundConst_pos hη
  have hbase : 1 ≤ (divisorBoundConst η + 1) * T ^ (3 * η) := by
    have h1 : 1 ≤ T ^ (3 * η) := Real.one_le_rpow hT (by positivity)
    nlinarith
  unfold dpolySupportCoeff
  split_ifs with hn
  swap
  · rw [norm_zero]
    exact pow_nonneg (by linarith) _
  obtain ⟨hn1, -⟩ := powSupport_block_bounds hB hℓ n hn
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos (Nat.two_pow_pos j) ℓ) hn1
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => le_trans Nat.one_le_two_pow (hB k hk).1
  have habs := abs_powConv_le (a := genClassCoeff c Λ i σ') hB1
    (fun k hk => abs_genClassCoeff_le (i := i) hσσ' (hB1 k hk) (hBΛ k hk) (hc k hk)) ℓ n hnpos
  have hX0 : (0 : ℝ) < (((2 ^ j : ℕ) : ℝ)) ^ ℓ := by positivity
  have hXn : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ n := by exact_mod_cast hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- `X^σ n^{-σ} ≤ 1`
  have hratio : ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ σ * (n : ℝ) ^ (-σ) ≤ 1 := by
    rw [Real.rpow_neg hnR.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hnR _)]
    exact Real.rpow_le_rpow hX0.le hXn hσ
  -- `d(n) ≤ C_η n^η ≤ (C_η + 1) T^{3η}`
  have hd : (n.divisors.card : ℝ) ≤ (divisorBoundConst η + 1) * T ^ (3 * η) := by
    have h1 := card_divisors_le_rpow hη hnpos.ne'
    have h2 : (n : ℝ) ^ η ≤ T ^ (3 * η) := by
      rw [Real.rpow_mul hT0.le]
      exact Real.rpow_le_rpow hnR.le (hlen n hn) hη.le
    calc (n.divisors.card : ℝ) ≤ divisorBoundConst η * (n : ℝ) ^ η := h1
      _ ≤ divisorBoundConst η * T ^ (3 * η) := mul_le_mul_of_nonneg_left h2 hCη.le
      _ ≤ (divisorBoundConst η + 1) * T ^ (3 * η) := by
          nlinarith [Real.rpow_nonneg hT0.le (3 * η)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hX0.le _)]
  calc ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ σ * |powConv (genClassCoeff c Λ i σ') B ℓ n|
      ≤ ((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ σ * ((n : ℝ) ^ (-σ) * (n.divisors.card : ℝ) ^ (2 * ℓ)) :=
        mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg hX0.le _)
    _ = (((((2 ^ j : ℕ) : ℝ)) ^ ℓ) ^ σ * (n : ℝ) ^ (-σ)) * (n.divisors.card : ℝ) ^ (2 * ℓ) := by
        ring
    _ ≤ 1 * ((divisorBoundConst η + 1) * T ^ (3 * η)) ^ (2 * ℓ) :=
        mul_le_mul hratio (pow_le_pow_left₀ (Nat.cast_nonneg _) hd _) (by positivity) zero_le_one
    _ ≤ ((divisorBoundConst η + 1) * T ^ (3 * η)) ^ (2 * M) := by
        rw [one_mul]
        exact pow_le_pow_right₀ hbase (by omega)

/-! ## The class count -/

/-- **The Guth–Maynard class count at a fixed `σ`.**  Let `0 < a ≤ 1`, `0 < δ`,
`M ≥ max(2, 2a/δ)`, `3/5 < σ < 9/10`, and let the exponents satisfy `3a(1-σ) ≤ E₀`,
`α(18/5 - 4σ) ≤ E₀`, `1 + a(12/5 - 4σ) ≤ E₀` and `1 + α(1 - 2σ) ≤ E₀`.  Under the large values
estimate, for every `ε > 0` every Type I class `W ⊆ [T, 2T]` of the window detector
(`1`-separated, block polynomial `≥ 1/(48J)` on the line `σ' ≥ σ`) has `|W| ≤ K T^{E₀ + ε}` for
all large `T`. -/
theorem exists_gm_window_class_card_le (hGM : GuthMaynardLargeValuesBound)
    {a δ σ α E₀ ε : ℝ} {M : ℕ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hδ0 : 0 < δ)
    (hM : 2 * a / δ ≤ M) (hM2 : 2 ≤ M) (hσ0 : 3 / 5 < σ) (hσ1 : σ < 9 / 10) (hε : 0 < ε)
    (hd : 3 * a * (1 - σ) ≤ E₀) (hg2 : α * (18 / 5 - 4 * σ) ≤ E₀)
    (hg3 : 1 + a * (12 / 5 - 4 * σ) ≤ E₀) (hm : 1 + α * (1 - 2 * σ) ≤ E₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (48 * (gDetBlockCount (pDetCut (3 * a / 4) T) : ℝ)) ≤
          ‖abscissaTaylorPoly (gDetBlock (pDetCut (3 * a / 4) T) j)
            (fun k => ((gDetCoeff (pDetMoll δ T) (pDetSmooth (3 * a / 4) T) k : ℝ) : ℂ))
            (gDetLog (pDetCut (3 * a / 4) T)) i σ' t‖) →
        (W.card : ℝ) ≤ K * T ^ (E₀ + ε) := by
  obtain ⟨CG, hCG, hGMr⟩ := hGM.card_le_of_dyadic_range (show 0 < ε / 4 by positivity)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (96 * M) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have h24 : 24 * (M : ℝ) * η = ε / 4 := by rw [hηdef]; field_simp; ring
  have hCη := divisorBoundConst_pos hη
  obtain ⟨KG, hKG⟩ : ∃ KG : ℝ,
      KG = 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * CG * (divisorBoundConst η + 1) ^ (8 * M) :=
    ⟨_, rfl⟩
  obtain ⟨KM, hKM⟩ : ∃ KM : ℝ, KM = 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) := ⟨_, rfl⟩
  have hKG0 : 0 ≤ KG := by rw [hKG]; positivity
  have hKM0 : 0 ≤ KM := by rw [hKM]; positivity
  -- the size conditions on `T`
  have hev : ∀ᶠ T : ℝ in atTop, Real.exp 1 ≤ T ∧ 4 ≤ T ∧ (2 : ℝ) ^ M ≤ T ∧
      1 * (1 + Real.log T) ^ 2 ≤ T ^ (1 / 4 : ℝ) ∧ 1 * (1 + Real.log T) ^ 4 ≤ T ^ (1 / 2 : ℝ) ∧
      1 * (1 + Real.log T) ^ 8 ≤ T ^ (ε / 4) ∧ 2 ≤ T ^ (δ / 2) ∧
      ((M : ℝ) + 100) ^ (4 * M) * (1 + Real.log T) ^ (4 * M) ≤ T ^ (ε / 4) ∧
      ((M : ℝ) + 100) ^ (2 * M + 1 + 1 + 2 ^ (4 * M)) *
        (1 + Real.log T) ^ (2 * M + 1 + 1 + 2 ^ (4 * M)) ≤ T ^ (ε / 2) := by
    filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (4 : ℝ),
      eventually_ge_atTop ((2 : ℝ) ^ M),
      eventually_const_mul_polylog_le_rpow 2 (c := 1 / 4) (by norm_num) 1,
      eventually_const_mul_polylog_le_rpow 4 (c := 1 / 2) (by norm_num) 1,
      eventually_const_mul_polylog_le_rpow 8 (c := ε / 4) (by positivity) 1,
      (tendsto_rpow_atTop (show (0 : ℝ) < δ / 2 by positivity)).eventually_ge_atTop 2,
      eventually_const_mul_polylog_le_rpow (4 * M) (c := ε / 4) (by positivity)
        (((M : ℝ) + 100) ^ (4 * M)),
      eventually_const_mul_polylog_le_rpow (2 * M + 1 + 1 + 2 ^ (4 * M)) (c := ε / 2)
        (by positivity) (((M : ℝ) + 100) ^ (2 * M + 1 + 1 + 2 ^ (4 * M)))]
      with T h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  refine ⟨KG + KM, by positivity, T₀, ?_⟩
  intro T hT j i σ' hσσ' W hW hsep hbig
  obtain ⟨hTe, hT4, hT2M, hA, hB, hC, hD, hQev, hPev⟩ := hT₀ T hT
  simp only [one_mul] at hA hB hC
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hT2 : (2 : ℝ) ≤ T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    exact hTe
  have hlogsq : Real.log T ^ 2 ≤ T ^ (1 / 4 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 2) hA
  have hlog4 : Real.log T ^ 4 ≤ T ^ (1 / 2 : ℝ) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 4) hB
  have hlog8 : Real.log T ^ 8 ≤ T ^ (ε / 4) :=
    le_trans (pow_le_pow_left₀ hlog0 (by linarith) 8) hC
  have hZT : T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T := by
    calc T ^ (3 * a / 4) * Real.log T ^ 2 ≤ T ^ (3 / 4 : ℝ) * T ^ (1 / 4 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hlogsq (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T := by rw [← Real.rpow_add hT0]; norm_num
  have hwin2 : T ^ (3 * a / 2) * Real.log T ^ 4 ≤ T ^ (2 : ℝ) := by
    calc T ^ (3 * a / 2) * Real.log T ^ 4 ≤ T ^ (3 / 2 : ℝ) * T ^ (1 / 2 : ℝ) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hlog4 (by positivity)
            (Real.rpow_nonneg hT0.le _)
      _ = T ^ (2 : ℝ) := by rw [← Real.rpow_add hT0]; norm_num
  have hTE : 0 ≤ T ^ (E₀ + ε) := Real.rpow_nonneg hT0.le _
  set Zc := pDetCut (3 * a / 4) T with hZc
  have hZle : (Zc : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 := Nat.floor_le (by positivity)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = ((M : ℝ) + 100) * (1 + Real.log T) := ⟨_, rfl⟩
  have hl1 : 1 ≤ 1 + Real.log T := by linarith
  have hMR0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hQM3 : ((M : ℝ) + 3) * (1 + Real.log T) ≤ Q := by
    rw [hQdef]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hQ1 : 1 ≤ Q :=
    le_trans (one_le_mul_of_one_le_of_one_le (by linarith only [hMR0]) hl1) hQM3
  have hQ0 : 0 < Q := by linarith
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Q ^ (2 ^ (4 * M)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  rcases W.eq_empty_or_nonempty with hWe | ⟨t₀, ht₀⟩
  · rw [hWe, card_empty, Nat.cast_zero]
    positivity
  set J := gDetBlockCount Zc with hJdef
  set V : ℝ := 1 / (48 * (J : ℝ)) with hVdef
  have hJpos : (0 : ℝ) < J := by rw [hJdef, gDetBlockCount]; positivity
  have hV0 : 0 < V := by positivity
  obtain ⟨hjX, hjZ⟩ := gDetBlock_bounds_of_large hV0 (hbig t₀ ht₀)
  have hK1 := rpow_half_le_of_moll_lt hT1 hD hjX
  have hK2 : ((2 ^ j : ℕ) : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 :=
    le_trans (by exact_mod_cast hjZ) hZle
  have hZ2 : 2 ≤ Zc := by
    have hTy : (2 : ℝ) ≤ T ^ (3 * a / 4) * Real.log T ^ 2 := by linarith
    rw [hZc, pDetCut]
    exact Nat.le_floor (by exact_mod_cast hTy)
  have hJQ : 48 * (J : ℝ) ≤ Q := by
    have hJ2 := gDetBlockCount_le_log hZ2 (le_trans hZle hZT)
    rw [hQdef]
    calc 48 * (J : ℝ) ≤ 48 * (2 * (1 + Real.log T)) := by linarith only [hJ2]
      _ = 96 * (1 + Real.log T) := by ring
      _ ≤ ((M : ℝ) + 100) * (1 + Real.log T) :=
          mul_le_mul_of_nonneg_right (by linarith only [hMR0]) (by linarith only [hlog0])
  have hVQ : 1 / Q ≤ V := by
    rw [hVdef]
    exact one_div_le_one_div_of_le (by positivity) hJQ
  set Λ := gDetLog Zc with hΛ
  set Bk := gDetBlock Zc j with hBkdef
  set Xm := pDetMoll δ T with hXm
  set Ys := pDetSmooth (3 * a / 4) T with hYs
  have hXm1 : 1 ≤ Xm := one_le_pDetMoll hδ0.le hT1
  have hYs0 : 0 < Ys := lt_of_lt_of_le one_pos (one_le_pDetSmooth (by positivity) hT1)
  have hB1 : ∀ k ∈ Bk, 1 ≤ k := fun k hk => (mem_gDetBlock_bounds hk).1
  have hBb : ∀ k ∈ Bk, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1 := fun k hk =>
    ⟨(mem_gDetBlock_bounds hk).2.2.1, (mem_gDetBlock_bounds hk).2.2.2⟩
  have hBΛ : ∀ k ∈ Bk, Real.log k ≤ Λ := by
    intro k hk
    have hk := mem_gDetBlock_bounds hk
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2.1)
  have hcoef : ∀ k ∈ Bk, |gDetCoeff Xm Ys k| ≤ k.divisors.card :=
    fun k _ => abs_gDetCoeff_le hXm1 hYs0 k
  have hbig' : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff (gDetCoeff Xm Ys) Λ i σ') Bk t‖ := by
    intro t ht
    rw [← abscissaTaylorPoly_ofReal_eq_dpoly hB1]
    exact hbig t ht
  obtain ⟨ℓ, hℓ1, hℓM, hX1, hX2⟩ := exists_pow_mem_window ha0 hδ0 hM hM2
    (lt_of_lt_of_le one_lt_two hT2) hlog1 hK1 hK2
  have hX2' : (((2 ^ j : ℕ) : ℝ)) ^ ℓ ≤ T ^ (2 : ℝ) := le_trans hX2 hwin2
  set X : ℝ := (((2 ^ j : ℕ) : ℝ)) ^ ℓ with hXdef
  have hXge1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast Nat.one_le_two_pow)
  have hσ0' : (0 : ℝ) ≤ σ := by linarith
  have hVl : 1 / Q ^ M ≤ V ^ ℓ := by
    calc 1 / Q ^ M ≤ 1 / Q ^ ℓ := one_div_le_one_div_of_le (pow_pos hQ0 _)
          (pow_le_pow_right₀ hQ1 hℓM)
      _ = (1 / Q) ^ ℓ := by rw [one_div_pow]
      _ ≤ V ^ ℓ := pow_le_pow_left₀ (by positivity) hVQ ℓ
  -- the diagonal term
  have hdiagX : X ^ (2 - 2 * σ) ≤ T ^ (E₀ + ε / 4) := by
    have h := rpow_two_sub_le_of_le_window hT1 (by linarith) (by positivity) hX2
      (by rw [← pow_mul]; exact hlog8) (by linarith : σ ≤ 1)
    refine le_trans h (Real.rpow_le_rpow_of_exponent_le hT1 ?_)
    have h4 : ε / 4 * (1 - σ) ≤ ε / 4 :=
      mul_le_of_le_one_right (by positivity) (by linarith only [hσ0])
    have h5 : (3 * a + ε / 4) * (1 - σ) = 3 * a * (1 - σ) + ε / 4 * (1 - σ) := by ring
    linarith only [h4, h5, hd]
  by_cases hsw : X ≤ T ^ α
  · -- the Guth–Maynard range: the large values estimate for `X^σ P^ℓ`
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      have h1 : ((2 ^ j : ℕ) : ℝ) = 1 := by rw [hj0]; norm_num
      linarith
    have hjl : 1 ≤ j * ℓ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : ℕ, N₀ = 2 ^ (j * ℓ - 1) := ⟨_, rfl⟩
    have hN₀X : 2 * N₀ = (2 ^ j) ^ ℓ := by
      rw [hN₀def, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hjl]
    have hN₀1 : 1 ≤ N₀ := by rw [hN₀def]; exact Nat.one_le_two_pow
    have htop : (2 ^ j) ^ ℓ * 2 ^ ℓ = N₀ * 2 ^ (ℓ + 1) := by rw [← hN₀X, pow_succ]; ring
    have hSsub : powSupport Bk ℓ ⊆ Finset.Ioc N₀ (N₀ * 2 ^ (ℓ + 1)) := by
      intro n hn
      obtain ⟨h1, h2⟩ := powSupport_block_bounds hBb hℓ1 n hn
      rw [Finset.mem_Ioc]
      refine ⟨lt_of_lt_of_le (by omega : N₀ < 2 * N₀) (hN₀X ▸ h1), ?_⟩
      rw [htop] at h2
      exact h2.le
    have hLcast : (((N₀ * 2 ^ (ℓ + 1) : ℕ) : ℝ)) = 2 ^ ℓ * X := by
      rw [← htop, hXdef]
      push_cast
      ring
    have hLM : (((N₀ * 2 ^ (ℓ + 1) : ℕ) : ℝ)) ≤ 2 ^ M * X := by
      rw [hLcast]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓM) (by linarith)
    have hlen : ∀ n ∈ powSupport Bk ℓ, (n : ℝ) ≤ T ^ (3 : ℝ) := by
      intro n hn
      have hn' := (Finset.mem_Ioc.mp (hSsub hn)).2
      calc (n : ℝ) ≤ 2 ^ M * X := le_trans (by exact_mod_cast hn') hLM
        _ ≤ T * T ^ (2 : ℝ) := mul_le_mul hT2M hX2' (by linarith) hT0.le
        _ = T ^ (3 : ℝ) := by
            rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add hT0, Real.rpow_one]
    obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ((divisorBoundConst η + 1) * T ^ (3 * η)) ^ (2 * M) :=
      ⟨_, rfl⟩
    have hBd1 : 1 ≤ Bd := by
      rw [hBd]
      have h1 : 1 ≤ T ^ (3 * η) := Real.one_le_rpow hT1 (by positivity)
      exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith only [hCη]) h1)
    have hp0 : 0 ≤ X ^ σ := Real.rpow_nonneg (by linarith) σ
    have hcb : ∀ n, ‖dpolySupportCoeff
        (fun n => X ^ σ * powConv (genClassCoeff (gDetCoeff Xm Ys) Λ i σ') Bk ℓ n)
        (powSupport Bk ℓ) n‖ ≤ Bd := by
      intro n
      rw [hBd]
      exact norm_dpolySupportCoeff_powConv_le hBb hBΛ hcoef hσ0' hσσ' hℓ1 hℓM hη hT1 hlen n
    have hbigGM : ∀ t ∈ W, X ^ σ * V ^ ℓ ≤ ‖∑ n ∈ Finset.Ioc N₀ (N₀ * 2 ^ (ℓ + 1)),
        dpolySupportCoeff
          (fun n => X ^ σ * powConv (genClassCoeff (gDetCoeff Xm Ys) Λ i σ') Bk ℓ n)
          (powSupport Bk ℓ) n * Complex.exp (Complex.I * t * Real.log n)‖ := by
      intro t ht
      rw [norm_sum_Ioc_dpolySupportCoeff_eq hSsub hp0 t, ← norm_pow_genClass_eq hB1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV0.le (hbig' t ht) ℓ) hp0
    have hcard := hGMr N₀ (ℓ + 1) T T (X ^ σ * V ^ ℓ) Bd _ W hN₀1 (by omega) hT2
      (mul_pos (Real.rpow_pos_of_pos (by linarith) σ) (pow_pos hV0 ℓ)) (by linarith) hcb
      (fun t ht => ⟨(hW t ht).1, by linarith [(hW t ht).2]⟩) hsep hbigGM
    have hR1 : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ + 1)
    have hRM : ((ℓ + 1 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
      push_cast
      have : (ℓ : ℝ) ≤ M := by exact_mod_cast hℓM
      linarith
    have hc := class_count_gm_arith hT1 hXge1 hσ0 hσ1 hX1 hsw hdiagX (by positivity) hg2 hg3
      (pow_pos hV0 ℓ) hQ1 hVl hR1 hRM (Nat.cast_nonneg _) hLM hBd1 hCG hcard
    have hQ4 : Q ^ (4 * M) ≤ T ^ (ε / 4) := by rw [hQdef, mul_pow]; exact hQev
    have hloss := gm_loss_le (E₀ := E₀) hT0 hCη.le h24 hQ4
    rw [← hBd] at hloss
    calc (W.card : ℝ)
        ≤ 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * CG * (T ^ (ε / 4) * Bd ^ 4 * Q ^ (4 * M)) *
            T ^ (E₀ + ε / 4) := hc
      _ = 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * CG *
            (T ^ (ε / 4) * Bd ^ 4 * Q ^ (4 * M) * T ^ (E₀ + ε / 4)) := by ring
      _ ≤ 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * CG *
            ((divisorBoundConst η + 1) ^ (8 * M) * T ^ (E₀ + ε)) :=
          mul_le_mul_of_nonneg_left hloss (by positivity)
      _ = KG * T ^ (E₀ + ε) := by rw [hKG]; ring
      _ ≤ (KG + KM) * T ^ (E₀ + ε) :=
          mul_le_mul_of_nonneg_right (by linarith only [hKM0]) hTE
  · -- past the switch: the mean value theorem for `P^ℓ`
    push Not at hsw
    have hTa : T * X ^ (1 - 2 * σ) ≤ T ^ (E₀ + ε / 2) :=
      le_trans (mul_rpow_le_of_rpow_le hT0 hsw.le (by linarith))
        (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
    have hdiag2 : X ^ (2 - 2 * σ) ≤ T ^ (E₀ + ε / 2) :=
      le_trans hdiagX (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
    have hmass₀ := classPowerMass_le_of_le (σ := σ) hT1 hℓM hX2'
    have hPP : (((M : ℝ) + 3) * (1 + Real.log T)) ^ (2 ^ (4 * M)) ≤ P := by
      rw [hPdef]
      exact pow_le_pow_left₀ (by positivity) hQM3 _
    have hmass : classPowerMass j ℓ σ ≤ 2 ^ M * X ^ (1 - 2 * σ) * P :=
      le_trans hmass₀ (mul_le_mul_of_nonneg_left hPP (by positivity))
    have hLcast : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) = 2 ^ ℓ * X := by
      rw [hXdef]
      push_cast
      ring
    have hLM : (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ 2 ^ M * X := by
      rw [hLcast]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hℓM) (by linarith)
    have hL1 : (1 : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow _ _ (by positivity)
    have hlogL : 1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) ≤ Q :=
      le_trans (one_add_log_raised_le_of_le hT1 hℓM hX2') hQM3
    have hG0 : 0 ≤ classPowerMass j ℓ σ := by unfold classPowerMass; positivity
    have hmvt := card_mul_pow_le_genClass_mvt (B := Bk) (c := gDetCoeff Xm Ys) (Λ := Λ) (i := i)
      hℓ1 hBb hBΛ hcoef hσ0' hσσ' hT0.le hV0.le hW hsep hbig'
    have hc := class_count_mvt_arith_of_le hT1 hXge1 hTa hdiag2 hQ1 hP0 hL1 hLM hlogL hG0 hmass
      hVl (Nat.cast_nonneg _) hmvt
    have hQP : Q ^ (2 * M) * Q * Q * P ≤ T ^ (ε / 2) := by
      rw [hPdef, ← pow_succ, ← pow_succ, ← pow_add, hQdef, mul_pow]
      exact hPev
    calc (W.card : ℝ)
        ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) * (Q ^ (2 * M) * Q * Q * P) * T ^ (E₀ + ε / 2) := hc
      _ ≤ 2 ^ (M + 1) * (2 + 2 ^ (M + 2)) * T ^ (ε / 2) * T ^ (E₀ + ε / 2) := by
          gcongr
      _ = KM * T ^ (E₀ + ε) := by
          rw [hKM, mul_assoc _ (T ^ (ε / 2)), ← Real.rpow_add hT0]
          ring_nf
      _ ≤ (KG + KM) * T ^ (E₀ + ε) :=
          mul_le_mul_of_nonneg_right (by linarith only [hKG0]) hTE

end RHTower

end
