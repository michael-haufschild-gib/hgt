import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIMeanSquare

/-!
# Height windows for the Type-I/II case of Matomäki–Teräväinen (5.3)

For `F = M₁M₂M₃` (`m₁ ∼ M₁`, `m₂ ∼ M₂`, `M₃ < m₃ ≤ (1+δ)M₃`) and a height window `[T/2, T]`:

* **over height** (`T ≤ ⌊M₃⌋`): Kuzmin–Landau gives `|M₃(1+it)| ≪ 1/T` pointwise, and the mean
  value theorem for `M₁M₂` pays the rest with only polylogarithmic losses;
* **under height**: the three-factor arithmetic–geometric mean split with the amplifier
  `𝓜 = P₁^k/k!` gives `√(∫|M₃|⁴|M₂|² · ∫|M₁|⁴|M₂|²|𝓜|²)`; the first factor is Watt's twisted
  fourth moment (the twist `M₂` split into two integer dyadic blocks), the second the mean value
  theorem for `M₁²M₂𝓜` with the fibrewise Cauchy–Schwarz coefficient energy.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Mean value theorem with a lower support bound.**  If `c` vanishes on `n ≤ N₀`, then
`∫_{-T}^{T} |∑_{n ≤ K} c(n) n^{-1-it}|² ≤ (5πe/N₀ + (5π/2) T/N₀²) ∑_{n ≤ K} |c(n)|²`. -/
theorem integral_normSq_perronPoly_le_of_lower_support (c : ℕ → ℂ) (K : ℕ) {N₀ T : ℝ}
    (hN₀ : 0 < N₀) (hT : 1 ≤ T) (hc : ∀ n, c n ≠ 0 → N₀ < n) :
    ∫ t in Set.Icc (-T) T, ‖perronPoly c K 1 t‖ ^ 2 ≤
      (5 * Real.pi * Real.exp 1 / N₀ + 5 * Real.pi / 2 * T / N₀ ^ 2) *
        ∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2 := by
  classical
  set c' : ℕ → ℂ := fun n => if n ∈ Finset.Icc 1 K then c n else 0 with hc'
  have hsupp : ∀ n, c' n ≠ 0 → n ∈ Finset.Icc 1 K := by
    intro n hn
    by_contra h
    exact hn (by simp only [hc', if_neg h])
  have hpoly : ∀ t, perronPoly c K 1 t = LSeries c' (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) := by
    intro t
    rw [← perronPoly_eq_LSeries_of_support hsupp]
    unfold perronPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hc', if_pos hn]
  simp_rw [hpoly]
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 K := by simp
  refine (integral_Icc_normSq_LSeries_le_general_affine hs0 hsupp 1 hT).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 K,
      (n : ℝ) * ‖c' n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤ ‖c n‖ ^ 2 / N₀ ∧
        ‖c' n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤ ‖c n‖ ^ 2 / N₀ ^ 2 := by
    intro n hn
    have hcn : c' n = c n := by simp only [hc', if_pos hn]
    rw [hcn]
    by_cases h0 : c n = 0
    · simp [h0]
    have hlt := hc n h0
    have hn0 : (0 : ℝ) < n := hN₀.trans hlt
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg_one,
      mul_pow]
    have hq : 0 ≤ ‖c n‖ ^ 2 := sq_nonneg _
    constructor
    · calc (n : ℝ) * (‖c n‖ ^ 2 * ((n : ℝ)⁻¹) ^ 2) = ‖c n‖ ^ 2 / n := by field_simp
        _ ≤ ‖c n‖ ^ 2 / N₀ := div_le_div_of_nonneg_left hq hN₀ hlt.le
    · calc ‖c n‖ ^ 2 * ((n : ℝ)⁻¹) ^ 2 = ‖c n‖ ^ 2 / (n : ℝ) ^ 2 := by field_simp
        _ ≤ ‖c n‖ ^ 2 / N₀ ^ 2 :=
          div_le_div_of_nonneg_left hq (by positivity) (pow_le_pow_left₀ hN₀.le hlt.le 2)
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hConst : generalMeanSquareConst c' (Finset.Icc 1 K) 1 ≤
      5 * Real.pi * Real.exp 1 / N₀ * ∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2 := by
    unfold generalMeanSquareConst
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have h := (hterm n hn).1
    have hpos : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
    calc _ ≤ 5 * Real.pi * Real.exp 1 * (‖c n‖ ^ 2 / N₀) := mul_le_mul_of_nonneg_left h hpos
      _ = 5 * Real.pi * Real.exp 1 / N₀ * ‖c n‖ ^ 2 := by ring
  have hRate : generalMeanSquareRate c' (Finset.Icc 1 K) 1 ≤
      5 * Real.pi / 2 / N₀ ^ 2 * ∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2 := by
    unfold generalMeanSquareRate
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have h := (hterm n hn).2
    have hpos : 0 ≤ 5 * Real.pi / 2 := by positivity
    calc _ ≤ 5 * Real.pi / 2 * (‖c n‖ ^ 2 / N₀ ^ 2) := mul_le_mul_of_nonneg_left h hpos
      _ = 5 * Real.pi / 2 / N₀ ^ 2 * ‖c n‖ ^ 2 := by ring
  have hT0 : 0 ≤ T := by linarith
  calc generalMeanSquareConst c' (Finset.Icc 1 K) 1 + generalMeanSquareRate c' (Finset.Icc 1 K) 1 * T
      ≤ 5 * Real.pi * Real.exp 1 / N₀ * ∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2 +
          5 * Real.pi / 2 / N₀ ^ 2 * (∑ n ∈ Finset.Icc 1 K, ‖c n‖ ^ 2) * T := by
        gcongr
    _ = _ := by ring

/-- **Convolution energy.**  `∑_{n ≤ K} |(f ⋆ b)(n)|² ≤ D (∑ |f|²)(∑ |b|²)` when `d(n) ≤ D` on
`[1, K]`: Cauchy–Schwarz over each divisor fibre. -/
theorem sum_normSq_arithmeticFunction_mul_le (f b : ArithmeticFunction ℂ) {K Kf Kb : ℕ} {D : ℝ}
    (hf : ∀ n, f n ≠ 0 → n ∈ Finset.Icc 1 Kf) (hb : ∀ n, b n ≠ 0 → n ∈ Finset.Icc 1 Kb)
    (hD0 : 0 ≤ D) (hD : ∀ n ∈ Finset.Icc 1 K, (n.divisors.card : ℝ) ≤ D) :
    ∑ n ∈ Finset.Icc 1 K, ‖(f * b) n‖ ^ 2 ≤
      D * ((∑ d ∈ Finset.Icc 1 Kf, ‖f d‖ ^ 2) * ∑ m ∈ Finset.Icc 1 Kb, ‖b m‖ ^ 2) := by
  classical
  set g : ℕ × ℕ → ℝ := fun x => ‖f x.1‖ ^ 2 * ‖b x.2‖ ^ 2 with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hfibre : ∀ n ∈ Finset.Icc 1 K,
      ‖(f * b) n‖ ^ 2 ≤ D * ∑ x ∈ n.divisorsAntidiagonal, g x := by
    intro n hn
    rw [ArithmeticFunction.mul_apply]
    have h1 : ‖∑ x ∈ n.divisorsAntidiagonal, f x.1 * b x.2‖ ≤
        ∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ * ‖b x.2‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (∑ x ∈ n.divisorsAntidiagonal, ‖f x.1‖ * ‖b x.2‖) ^ 2 ≤
        (n.divisorsAntidiagonal.card : ℝ) *
          ∑ x ∈ n.divisorsAntidiagonal, (‖f x.1‖ * ‖b x.2‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ D := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]; exact hD n hn
    have hsum0 : 0 ≤ ∑ x ∈ n.divisorsAntidiagonal, (‖f x.1‖ * ‖b x.2‖) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc ‖∑ x ∈ n.divisorsAntidiagonal, f x.1 * b x.2‖ ^ 2
        ≤ (n.divisorsAntidiagonal.card : ℝ) *
            ∑ x ∈ n.divisorsAntidiagonal, (‖f x.1‖ * ‖b x.2‖) ^ 2 := h2.trans h3
      _ ≤ D * ∑ x ∈ n.divisorsAntidiagonal, (‖f x.1‖ * ‖b x.2‖) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard hsum0
      _ = D * ∑ x ∈ n.divisorsAntidiagonal, g x := by
          congr 1; exact Finset.sum_congr rfl fun x _ => by rw [hg]; ring
  have hstep : ∑ n ∈ Finset.Icc 1 K, ‖(f * b) n‖ ^ 2 ≤
      D * ∑ n ∈ Finset.Icc 1 K, ∑ x ∈ n.divisorsAntidiagonal, g x := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hfibre
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ hD0)
  rw [Finset.sum_sigma']
  set Sg := (Finset.Icc 1 K).sigma fun n => n.divisorsAntidiagonal with hSg
  have hinj : Set.InjOn (fun p : (_ : ℕ) × (ℕ × ℕ) => p.2) (Sg : Set ((_ : ℕ) × (ℕ × ℕ))) := by
    intro p hp q hq hpq
    have hp' := Nat.mem_divisorsAntidiagonal.1 (Finset.mem_sigma.1 hp).2
    have hq' := Nat.mem_divisorsAntidiagonal.1 (Finset.mem_sigma.1 hq).2
    have h2 : p.2 = q.2 := hpq
    have h1 : p.1 = q.1 := by rw [← hp'.1, ← hq'.1, h2]
    exact Sigma.ext h1 (heq_of_eq h2)
  rw [show (∑ p ∈ Sg, g p.2) = ∑ x ∈ Sg.image (fun p => p.2), g x from
    (Finset.sum_image hinj).symm]
  rw [← Finset.sum_filter_ne_zero]
  have hsub : (Sg.image fun p => p.2).filter (fun x => g x ≠ 0) ⊆
      Finset.Icc 1 Kf ×ˢ Finset.Icc 1 Kb := by
    intro x hx
    have hgx := (Finset.mem_filter.1 hx).2
    have hfx : f x.1 ≠ 0 := by
      intro h; apply hgx; rw [hg]; simp [h]
    have hbx : b x.2 ≠ 0 := by
      intro h; apply hgx; rw [hg]; simp [h]
    exact Finset.mem_product.2 ⟨hf _ hfx, hb _ hbx⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hg0 x).trans (le_of_eq ?_)
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-- Two finite sums agree when every nonzero term lies in both index sets. -/
theorem sum_eq_sum_of_support_subset {s₁ s₂ : Finset ℕ} {F : ℕ → ℂ}
    (h : ∀ n, F n ≠ 0 → n ∈ s₁ ∧ n ∈ s₂) : ∑ n ∈ s₁, F n = ∑ n ∈ s₂, F n := by
  classical
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := s₂)]
  congr 1
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, hn⟩; exact ⟨(h n hn).2, hn⟩
  · rintro ⟨-, hn⟩; exact ⟨(h n hn).1, hn⟩

/-- **Watt blocks for a real dyadic twist.**  A polynomial supported on `(M₂, 2M₂]`, `M₂ ≥ 1/2`,
is dominated by two integer dyadic blocks `(A, 2A]` with `M₂/2 ≤ A ≤ 2M₂`:
`|M₂(1+it)|² ≤ 2|W₁|² + 2|W₂|²`, coefficients at most twice as large. -/
theorem exists_twist_watt_blocks (β : ℕ → ℂ) {M₂ B : ℝ} (hM₂ : 1 / 2 ≤ M₂)
    (hB : ∀ m, ‖mtRealIntervalAF β M₂ (2 * M₂) m‖ ≤ B) :
    ∃ (a₁ a₂ : ℕ → ℂ) (A₁ A₂ : ℕ), 1 ≤ A₁ ∧ 1 ≤ A₂ ∧ M₂ / 2 ≤ (A₁ : ℝ) ∧ M₂ / 2 ≤ (A₂ : ℝ) ∧
      (A₁ : ℝ) ≤ 2 * M₂ ∧ (A₂ : ℝ) ≤ 2 * M₂ ∧ (∀ m, ‖a₁ m‖ ≤ 2 * B) ∧
      (∀ m, ‖a₂ m‖ ≤ 2 * B) ∧
      ∀ t, ‖perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t‖ ^ 2 ≤
        2 * ‖mtWattCoefficientBlock a₁ A₁ t‖ ^ 2 + 2 * ‖mtWattCoefficientBlock a₂ A₂ t‖ ^ 2 := by
  classical
  set a' : ℕ → ℂ := fun n => mtRealIntervalAF β M₂ (2 * M₂) n with ha'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hsupp : ∀ n, a' n ≠ 0 → 0 < n ∧ M₂ < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M₂ := fun n hn =>
    mtRealIntervalAF_scaleSupported β M₂ (2 * M₂) hn
  rcases lt_or_ge M₂ 1 with hlt | hge
  · -- only `n = 1` lies in `(M₂, 2M₂]`
    set e : ℕ → ℂ := fun n => if n = 2 then 2 * a' 1 else 0 with he
    have hTw : ∀ t, perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t =
        a' 1 := by
      intro t
      unfold perronPoly
      rw [Finset.sum_eq_single 1]
      · simp [ha']
      · intro n _ hn1
        by_cases h0 : a' n = 0
        · change a' n * _ = 0; rw [h0, zero_mul]
        · exfalso
          obtain ⟨hn0, hlo, hhi⟩ := hsupp n h0
          have h2 : (n : ℝ) < 2 := by linarith
          have : n < 2 := by exact_mod_cast h2
          omega
      · intro h1
        by_cases h0 : a' 1 = 0
        · change a' 1 * _ = 0; rw [h0, zero_mul]
        · exfalso
          obtain ⟨-, hlo, hhi⟩ := hsupp 1 h0
          apply h1
          refine Finset.mem_Icc.2 ⟨le_rfl, Nat.one_le_iff_ne_zero.2 ?_⟩
          intro hc; rw [Nat.ceil_eq_zero] at hc; push_cast at hhi; linarith
    have hW : ∀ t, ‖mtWattCoefficientBlock e 1 t‖ = ‖a' 1‖ := by
      intro t
      rw [mtWattCoefficientBlock_eq_sum_Ioc]
      have hIoc : Finset.Ioc 1 (2 * 1) = {2} := by decide
      rw [hIoc, Finset.sum_singleton]
      simp only [he, if_pos rfl]
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by norm_num)]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_self, add_zero,
        RCLike.norm_ofNat, Nat.cast_ofNat]
      rw [Real.rpow_neg_one]; ring
    refine ⟨e, e, 1, 1, le_rfl, le_rfl, by push_cast; linarith, by push_cast; linarith,
      by push_cast; linarith, by push_cast; linarith, ?_, ?_, ?_⟩
    · intro m; simp only [he]; split_ifs
      · rw [norm_mul]; simp only [RCLike.norm_ofNat]; linarith [hB 1]
      · simp; linarith
    · intro m; simp only [he]; split_ifs
      · rw [norm_mul]; simp only [RCLike.norm_ofNat]; linarith [hB 1]
      · simp; linarith
    · intro t
      rw [hTw, hW]
      nlinarith [sq_nonneg ‖a' 1‖]
  · -- `(M₂, 2M₂] ⊆ (A, 2A] ∪ (2A, 4A]` with `A = ⌊M₂⌋`
    set A := ⌊M₂⌋₊ with hA
    have hA1 : 1 ≤ A := Nat.le_floor (by exact_mod_cast hge)
    have hAle : (A : ℝ) ≤ M₂ := Nat.floor_le (by linarith)
    have hAlt : M₂ < (A : ℝ) + 1 := Nat.lt_floor_add_one M₂
    have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
    have hsplit : ∀ t, perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t =
        mtWattCoefficientBlock a' A t + mtWattCoefficientBlock a' (2 * A) t := by
      intro t
      rw [mtWattCoefficientBlock_eq_sum_Ioc, mtWattCoefficientBlock_eq_sum_Ioc,
        Finset.sum_Ioc_consecutive _ (by omega : A ≤ 2 * A) (by omega : 2 * A ≤ 2 * (2 * A))]
      unfold perronPoly
      refine sum_eq_sum_of_support_subset fun n hn => ?_
      have h0 : a' n ≠ 0 := left_ne_zero_of_mul hn
      obtain ⟨hn0, hlo, hhi⟩ := hsupp n h0
      refine ⟨Finset.mem_Icc.2 ⟨hn0, ?_⟩, Finset.mem_Ioc.2 ⟨?_, ?_⟩⟩
      · exact_mod_cast hhi.trans (Nat.le_ceil _)
      · have : (A : ℝ) < n := hAle.trans_lt hlo
        exact_mod_cast this
      · have : (n : ℝ) < 2 * (2 * (A : ℝ)) := by linarith
        have : (n : ℝ) < ((2 * (2 * A) : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this.le
    refine ⟨a', a', A, 2 * A, hA1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases lt_or_ge M₂ 2 with h2 | h2
      · linarith
      · linarith
    · push_cast; linarith
    · linarith
    · push_cast; linarith
    · intro m; linarith [hB m]
    · intro m; linarith [hB m]
    · intro t
      rw [hsplit t]
      have h := norm_add_le (mtWattCoefficientBlock a' A t) (mtWattCoefficientBlock a' (2 * A) t)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith [sq_nonneg (‖mtWattCoefficientBlock a' A t‖ - ‖mtWattCoefficientBlock a' (2 * A) t‖)]

/-- **The three-factor split.**  On `E ⊆ [a, b]` with `1 ≤ λ|𝓜|`:
`∫_E |F₁F₂F₃|² ≤ λ √(∫|F₃|⁴|F₂|² · ∫|F₁|⁴|F₂|²|𝓜|²)`. -/
theorem setIntegral_normSq_mul_three_le_sqrt {F₁ F₂ F₃ G : ℝ → ℂ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (hF₃ : Continuous F₃) (hG : Continuous G) {E : Set ℝ}
    (hE : MeasurableSet E) {a b lam I₁ I₂ : ℝ} (hab : a ≤ b) (hEab : E ⊆ Set.Icc a b)
    (hlam0 : 0 ≤ lam) (hlam : ∀ t ∈ E, 1 ≤ lam * ‖G t‖)
    (hI₁ : (∫ t in a..b, ‖F₃ t‖ ^ (4 : ℕ) * ‖F₂ t‖ ^ (2 : ℕ)) ≤ I₁)
    (hI₂ : (∫ t in a..b, ‖F₁ t‖ ^ (4 : ℕ) * ‖F₂ t‖ ^ (2 : ℕ) * ‖G t‖ ^ (2 : ℕ)) ≤ I₂)
    (hI₁0 : 0 < I₁) (hI₂0 : 0 < I₂) :
    ∫ t in E, ‖F₁ t * F₂ t * F₃ t‖ ^ (2 : ℕ) ≤ lam * Real.sqrt (I₁ * I₂) := by
  set r : ℝ → ℂ := fun t => ((Real.sqrt ‖F₂ t‖ : ℝ) : ℂ) with hr
  have hrc : Continuous r := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hF₂.norm)
  have hr4 : ∀ t, ‖r t‖ ^ (4 : ℕ) = ‖F₂ t‖ ^ (2 : ℕ) := by
    intro t
    rw [hr, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (norm_nonneg _)]
  have hr2 : ∀ t, ‖r t‖ ^ (2 : ℕ) = ‖F₂ t‖ := by
    intro t
    rw [hr, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (norm_nonneg _)]
  have h := setIntegral_normSq_mul_le_sqrt (F₁ := fun t => F₃ t * r t)
    (F₂ := fun t => F₁ t * r t) (hF₃.mul hrc) (hF₁.mul hrc) hG hE hab hEab hlam0 hlam
    (I₁ := I₁) (I₂ := I₂) ?_ ?_ hI₁0 hI₂0
  · refine le_of_eq_of_le ?_ h
    congr 1
    funext t
    simp only [norm_mul, mul_pow]
    rw [hr2]
    ring
  · refine le_of_eq_of_le ?_ hI₁
    congr 1
    funext t
    simp only [norm_mul, mul_pow]
    rw [hr4]
  · refine le_of_eq_of_le ?_ hI₂
    congr 1
    funext t
    simp only [norm_mul, mul_pow]
    rw [hr4]

/-- The Watt envelope of a block `(A, 2A]` with `M₂/2 ≤ A ≤ 2M₂` is at most twice the envelope
at `M₂`. -/
theorem wattEnvelope_le_of_scale {T N A M₂ : ℝ} (hT : 0 < T) (hN : 0 < N) (hM₂ : 0 < M₂)
    (hA1 : M₂ / 2 ≤ A) (hA2 : A ≤ 2 * M₂) :
    (T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A) + (T + A) / (T ^ 4 * A) ≤
      2 * ((T + 4 * M₂ ^ 2 * Real.sqrt T) / (N ^ 2 * M₂) + (T + 2 * M₂) / (T ^ 4 * M₂)) := by
  have hA : 0 < A := by linarith
  have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have e1 : (T + A ^ 2 * Real.sqrt T) / (N ^ 2 * A) = T / (N ^ 2 * A) + A * Real.sqrt T / N ^ 2 := by
    field_simp
  have e2 : (T + A) / (T ^ 4 * A) = 1 / (T ^ 3 * A) + 1 / T ^ 4 := by field_simp
  have e3 : 2 * ((T + 4 * M₂ ^ 2 * Real.sqrt T) / (N ^ 2 * M₂) + (T + 2 * M₂) / (T ^ 4 * M₂)) =
      2 * T / (N ^ 2 * M₂) + 8 * M₂ * Real.sqrt T / N ^ 2 + 2 / (T ^ 3 * M₂) + 4 / T ^ 4 := by
    field_simp; ring
  rw [e1, e2, e3]
  have h1 : T / (N ^ 2 * A) ≤ 2 * T / (N ^ 2 * M₂) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hT.le (sq_nonneg N)) (by linarith : 0 ≤ 2 * A - M₂)]
  have h2 : A * Real.sqrt T / N ^ 2 ≤ 8 * M₂ * Real.sqrt T / N ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have h3 : 1 / (T ^ 3 * A) ≤ 2 / (T ^ 3 * M₂) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hT 3]
  have h4 : 1 / T ^ 4 ≤ 4 / T ^ 4 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  linarith

/-- **The Watt side.**  Given Watt's bound,
`∫_{T/2}^{T} |N(1+it)|⁴ |M₂(1+it)|² ≤ 32 C T^η B² ((T + 4M₂²√T)/(N²M₂) + (T + 2M₂)/(T⁴M₂))`
for a twist supported on `(M₂, 2M₂]` with coefficients `≤ B`. -/
theorem integral_unitBlock_fourth_twist_le (hW : MTWattBound) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℕ → ℂ) {M₂ B : ℝ} {N N' : ℕ} {T : ℝ}, 1 / 2 ≤ M₂ →
      (∀ m, ‖mtRealIntervalAF β M₂ (2 * M₂) m‖ ≤ B) → 1 ≤ N → N < N' → N' ≤ 2 * N → 2 ≤ T →
      (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
          ‖perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t‖ ^ (2 : ℕ)) ≤
        32 * C * T ^ η * B ^ 2 *
          ((T + 4 * M₂ ^ 2 * Real.sqrt T) / ((N : ℝ) ^ 2 * M₂) + (T + 2 * M₂) / (T ^ 4 * M₂)) := by
  obtain ⟨C, hC, hWatt⟩ := hW η hη
  refine ⟨C, hC, ?_⟩
  intro β M₂ B N N' T hM₂ hB hN hNN' hN' hT
  obtain ⟨a₁, a₂, A₁, A₂, hA₁, hA₂, hA₁lo, hA₂lo, hA₁hi, hA₂hi, ha₁, ha₂, hpt⟩ :=
    exists_twist_watt_blocks β hM₂ hB
  have hT0 : 0 < T := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (T + 4 * M₂ ^ 2 * Real.sqrt T) / ((N : ℝ) ^ 2 * M₂) +
      (T + 2 * M₂) / (T ^ 4 * M₂) := ⟨_, rfl⟩
  rw [← hQ]
  have hTη : 0 ≤ T ^ η := Real.rpow_nonneg hT0.le _
  have hblock : ∀ (a : ℕ → ℂ) (A : ℕ), 1 ≤ A → M₂ / 2 ≤ (A : ℝ) → (A : ℝ) ≤ 2 * M₂ →
      (∀ m, ‖a m‖ ≤ 2 * B) →
      (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
          ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤ 8 * C * T ^ η * B ^ 2 * Q := by
    intro a A hA hAlo hAhi ha
    refine (hWatt a A N N' (2 * B) hA hN hNN' hN' ha T hT).trans ?_
    have henv := wattEnvelope_le_of_scale hT0 hN0 hM₂0 hAlo hAhi
    rw [← hQ] at henv
    have hC0 : 0 ≤ C * T ^ η := by positivity
    calc C * T ^ η * (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T) / ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
          (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) * (2 * B) ^ 2)
        ≤ C * T ^ η * ((2 * Q) * (2 * B) ^ 2) := by gcongr
      _ = 8 * C * T ^ η * B ^ 2 * Q := by ring
  have hint : ∀ (a : ℕ → ℂ) (A : ℕ), IntervalIntegrable (fun t => ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
      ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) MeasureTheory.volume (T / 2) T := fun a A =>
    (((continuous_mtWattUnitBlock N N').norm.pow 4).mul
      ((continuous_mtWattCoefficientBlock a A).norm.pow 2)).intervalIntegrable _ _
  have hmono : (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t‖ ^ (2 : ℕ)) ≤
      ∫ t in (T / 2)..T, (2 * (‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
          ‖mtWattCoefficientBlock a₁ A₁ t‖ ^ (2 : ℕ)) +
        2 * (‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock a₂ A₂ t‖ ^ (2 : ℕ))) := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun t _ => ?_
    · exact (((continuous_mtWattUnitBlock N N').norm.pow 4).mul
        ((continuous_perronPoly _ _ 1).norm.pow 2)).intervalIntegrable _ _
    · exact ((hint a₁ A₁).const_mul 2).add ((hint a₂ A₂).const_mul 2)
    · have h := hpt t
      have hU : 0 ≤ ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) := by positivity
      calc ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
            ‖perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t‖ ^ (2 : ℕ)
          ≤ ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * (2 * ‖mtWattCoefficientBlock a₁ A₁ t‖ ^ 2 +
              2 * ‖mtWattCoefficientBlock a₂ A₂ t‖ ^ 2) := mul_le_mul_of_nonneg_left h hU
        _ = _ := by ring
  refine hmono.trans ?_
  rw [intervalIntegral.integral_add ((hint a₁ A₁).const_mul 2) ((hint a₂ A₂).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h1 := hblock a₁ A₁ hA₁ hA₁lo hA₁hi ha₁
  have h2 := hblock a₂ A₂ hA₂ hA₂lo hA₂hi ha₂
  linarith

/-- The amplifier `P₁(s)^k/k!` as an arithmetic function. -/
def primeSetAmplifierAF (B : Finset ℕ) (k : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else primeSetAmplifierCoeff B k n, if_pos rfl⟩

theorem primeSetAmplifierAF_apply_of_pos (B : Finset ℕ) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    primeSetAmplifierAF B k n = primeSetAmplifierCoeff B k n := by
  change (if n = 0 then 0 else primeSetAmplifierCoeff B k n) = _
  rw [if_neg hn.ne']

theorem perronPoly_primeSetAmplifierAF (B : Finset ℕ) (k K : ℕ) (t : ℝ) :
    perronPoly (fun n => primeSetAmplifierAF B k n) K 1 t =
      perronPoly (primeSetAmplifierCoeff B k) K 1 t := by
  unfold perronPoly
  refine Finset.sum_congr rfl fun n hn => ?_
  dsimp only
  rw [primeSetAmplifierAF_apply_of_pos B k (Finset.mem_Icc.1 hn).1]

theorem primeSetAmplifierAF_scaleSupported {B : Finset ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k : ℕ} (hk : 1 ≤ k) :
    MTRealScaleSupported (primeSetAmplifierAF B k) (P ^ k) ((2 * P) ^ k) := by
  intro n hn
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h]; rfl) hn
    · exact h
  rw [primeSetAmplifierAF_apply_of_pos B k hn0] at hn
  have hb := mem_primeSetSupport_bounds hP hB hk (mem_primeSetSupport_of_amplifierCoeff_ne_zero hn)
  exact ⟨hn0, hb.1, hb.2⟩

theorem primeSetAmplifierAF_support {B : Finset ℕ} {P : ℝ} (hP : 0 ≤ P)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k K : ℕ} (hk : 1 ≤ k) (hK : (2 * P) ^ k ≤ K) :
    ∀ n, primeSetAmplifierAF B k n ≠ 0 → n ∈ Finset.Icc 1 K := by
  intro n hn
  obtain ⟨hn0, -, hhi⟩ := primeSetAmplifierAF_scaleSupported hP hB hk hn
  exact Finset.mem_Icc.2 ⟨hn0, by exact_mod_cast hhi.trans hK⟩

/-- **The amplified mean value theorem.**  For `M₁(s)²M₂(s)𝓜(s)`, `𝓜 = P₁^k/k!`:
`∫_{T/2}^{T} |M₁|⁴|M₂|²|𝓜|² ≤ (5πe/N₀ + (5π/2)T/N₀²) · D · K_f B_f² · (P+1)^k/k!`, where
`N₀ = M₁²M₂P^k`, `K_f = ⌈2M₁⌉²⌈2M₂⌉`, `|(α⋆α⋆β)(n)| ≤ B_f` and `d(n) ≤ D` below the length. -/
theorem integral_amplified_short_twist_le (α β : ℕ → ℂ) {M₁ M₂ P : ℝ} {B : Finset ℕ}
    {k K : ℕ} {T D Bf : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hBp : ∀ p ∈ B, p.Prime)
    (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) (hP : 1 ≤ P) (hk : 1 ≤ k) (hK : (2 * P) ^ k ≤ K)
    (hT : 1 ≤ T) (hD0 : 0 ≤ D)
    (hD : ∀ n ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K),
      (n.divisors.card : ℝ) ≤ D)
    (hBf : ∀ n, ‖(mtRealIntervalAF α M₁ (2 * M₁) * mtRealIntervalAF α M₁ (2 * M₁) *
      mtRealIntervalAF β M₂ (2 * M₂)) n‖ ≤ Bf) :
    (∫ t in (T / 2)..T,
        ‖perronPoly (fun n => mtRealIntervalAF α M₁ (2 * M₁) n) ⌈2 * M₁⌉₊ 1 t‖ ^ (4 : ℕ) *
          ‖perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t‖ ^ (2 : ℕ) *
          ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ ^ (2 : ℕ)) ≤
      (5 * Real.pi * Real.exp 1 / (M₁ * M₁ * M₂ * P ^ k) +
          5 * Real.pi / 2 * T / (M₁ * M₁ * M₂ * P ^ k) ^ 2) *
        (D * (((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) * Bf ^ 2 *
          ((P + 1) ^ k / k.factorial))) := by
  classical
  set F₁ := mtRealIntervalAF α M₁ (2 * M₁) with hF₁
  set F₂ := mtRealIntervalAF β M₂ (2 * M₂) with hF₂
  have hP0 : 0 ≤ P := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hs₁ := mtRealIntervalAF_support_nat α M₁ (2 * M₁)
  have hs₂ := mtRealIntervalAF_support_nat β M₂ (2 * M₂)
  have hsG := primeSetAmplifierAF_support hP0 hB hk hK
  have hs11 : ∀ n, (F₁ * F₁) n ≠ 0 → n ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊) := fun n hn =>
    convolution_mem_Icc_of_support_mul hs₁ hs₁
      (arithmeticFunction_mul_eq_lseriesConvolution F₁ F₁ ▸ hn)
  have hsf : ∀ n, (F₁ * F₁ * F₂) n ≠ 0 →
      n ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) := fun n hn =>
    convolution_mem_Icc_of_support_mul hs11 hs₂
      (arithmeticFunction_mul_eq_lseriesConvolution (F₁ * F₁) F₂ ▸ hn)
  -- the product polynomial
  have hfac : ∀ t, ‖perronPoly (fun n => F₁ n) ⌈2 * M₁⌉₊ 1 t‖ ^ (4 : ℕ) *
        ‖perronPoly (fun n => F₂ n) ⌈2 * M₂⌉₊ 1 t‖ ^ (2 : ℕ) *
        ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ ^ (2 : ℕ) =
      ‖perronPoly (fun n => (F₁ * F₁ * F₂ * primeSetAmplifierAF B k) n)
        (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K) 1 t‖ ^ 2 := by
    intro t
    rw [perronPoly_arithmeticFunction_mul _ _ hsf hsG,
      perronPoly_arithmeticFunction_mul _ _ hs11 hs₂,
      perronPoly_arithmeticFunction_mul _ _ hs₁ hs₁, perronPoly_primeSetAmplifierAF]
    simp only [hF₁, hF₂, norm_mul, mul_pow]
    ring
  simp_rw [hfac]
  -- the support lower bound
  have hscale : MTRealScaleSupported (F₁ * F₁ * F₂ * primeSetAmplifierAF B k) (M₁ * M₁ * M₂ * P ^ k)
      ((2 * M₁) * (2 * M₁) * (2 * M₂) * (2 * P) ^ k) :=
    MTRealScaleSupported.mul (MTRealScaleSupported.mul (MTRealScaleSupported.mul
      (mtRealIntervalAF_scaleSupported α M₁ (2 * M₁))
      (mtRealIntervalAF_scaleSupported α M₁ (2 * M₁)) hM₁0.le hM₁0.le)
      (mtRealIntervalAF_scaleSupported β M₂ (2 * M₂)) (by positivity) hM₂0.le)
      (primeSetAmplifierAF_scaleSupported hP0 hB hk) (by positivity) (by positivity)
  have hN₀ : 0 < M₁ * M₁ * M₂ * P ^ k := by positivity
  have hMVT := integral_normSq_perronPoly_le_of_lower_support (fun n => (F₁ * F₁ * F₂ * primeSetAmplifierAF B k) n)
    (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K) hN₀ hT (fun n hn => (hscale hn).2.1)
  have hsub : (∫ t in (T / 2)..T, ‖perronPoly (fun n => (F₁ * F₁ * F₂ * primeSetAmplifierAF B k) n)
        (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K) 1 t‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T, ‖perronPoly (fun n => (F₁ * F₁ * F₂ * primeSetAmplifierAF B k) n)
        (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K) 1 t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set ((continuous_perronPoly _ _ 1).norm.pow 2).integrableOn_Icc
      (Filter.Eventually.of_forall fun t => by positivity)
      (Filter.Eventually.of_forall (Set.Icc_subset_Icc (by linarith) le_rfl))
  refine hsub.trans (hMVT.trans ?_)
  have hpre : 0 ≤ 5 * Real.pi * Real.exp 1 / (M₁ * M₁ * M₂ * P ^ k) +
      5 * Real.pi / 2 * T / (M₁ * M₁ * M₂ * P ^ k) ^ 2 := by
    have : 0 ≤ T := by linarith
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hpre
  -- the coefficient energy
  have hCS := sum_normSq_arithmeticFunction_mul_le (F₁ * F₁ * F₂) (primeSetAmplifierAF B k) hsf hsG hD0 hD
  refine hCS.trans (mul_le_mul_of_nonneg_left ?_ hD0)
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 0)
  have hf : ∑ d ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊), ‖(F₁ * F₁ * F₂) d‖ ^ 2 ≤
      ((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) * Bf ^ 2 := by
    calc ∑ d ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊), ‖(F₁ * F₁ * F₂) d‖ ^ 2
        ≤ ∑ _d ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊), Bf ^ 2 :=
          Finset.sum_le_sum fun d _ => pow_le_pow_left₀ (norm_nonneg _) (hBf d) 2
      _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hb : ∑ m ∈ Finset.Icc 1 K, ‖primeSetAmplifierAF B k m‖ ^ 2 ≤ (P + 1) ^ k / k.factorial := by
    have h1 : ∑ m ∈ Finset.Icc 1 K, ‖primeSetAmplifierAF B k m‖ ^ 2 =
        ∑ m ∈ Finset.Icc 1 K, ‖primeSetAmplifierCoeff B k m‖ ^ 2 :=
      Finset.sum_congr rfl fun m hm => by
        rw [primeSetAmplifierAF_apply_of_pos B k (Finset.mem_Icc.1 hm).1]
    rw [h1]
    refine (sum_normSq_primeSetAmplifierCoeff_le hBp k _).trans ?_
    have hc := card_le_of_subset_Ioc_real hP0 hB
    have hf0 : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc k) hf0.le
  have hGs0 : 0 ≤ ∑ m ∈ Finset.Icc 1 K, ‖primeSetAmplifierAF B k m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ d ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊), ‖(F₁ * F₁ * F₂) d‖ ^ 2) *
        ∑ m ∈ Finset.Icc 1 K, ‖primeSetAmplifierAF B k m‖ ^ 2
      ≤ (((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) * Bf ^ 2) *
          ((P + 1) ^ k / k.factorial) := mul_le_mul hf hb hGs0 (by positivity)
    _ = _ := by ring

/-- The amplifier lower bound on `U`, square-rooted: `1 ≤ k! (P^k)^{ε_U/10} |𝓜(1+it)|`. -/
theorem one_le_factorial_mul_rpow_mul_amplifier {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime)
    {P εU : ℝ} (hP : 1 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {k K : ℕ} (hk : 1 ≤ k)
    (hK : (2 * P) ^ k ≤ K) {t : ℝ}
    (hSt : P ^ (-εU / 10) ≤ ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) :
    1 ≤ (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) *
      ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ := by
  have h := one_le_amplifier_perronPoly (X := (K : ℝ)) hBp hP hB hk hK hSt
  rw [Nat.floor_natCast] at h
  have hx : 0 ≤ (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) *
      ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ := by positivity
  have hsq : ((k.factorial : ℝ) * (P ^ k) ^ (εU / 10) *
      ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖) ^ 2 =
      (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) *
        ‖perronPoly (primeSetAmplifierCoeff B k) K 1 t‖ ^ 2 := by
    have ha : ((P ^ k) ^ (εU / 10)) ^ 2 = (P ^ k) ^ (εU / 5) := by
      rw [← Real.rpow_mul_natCast (by positivity)]
      norm_num [div_mul_eq_mul_div]
      ring_nf
    rw [mul_pow, mul_pow, ha]
  nlinarith [hsq, h]

/-- **Over-height window.**  For `T ≤ N = ⌊M₃⌋`, Kuzmin–Landau gives `|M₃(1+it)| ≤ C₀/T` and the
mean value theorem for `M₁M₂` gives
`∫_E |M₁M₂M₃|² ≤ (C₀/T)² (5πe/(M₁M₂) + (5π/2)T/(M₁M₂)²) K (1 + log K)^e`,
`K = ⌈2M₁⌉⌈2M₂⌉`, `e = 2^{22} − 1`, `C₀ = 2(6π + 1)`. -/
theorem setIntegral_typeI_II_overHeight_le (α β : ℕ → ℂ) {M₁ M₂ T : ℝ} {N N' : ℕ}
    {E : Set ℝ} (hα : MTUniformDivisorBounded 5 α) (hβ : MTUniformDivisorBounded 5 β)
    (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hTN : T ≤ (N : ℝ)) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (T / 2) T) :
    ∫ t in E, ‖perronPoly (fun n => mtRealIntervalAF α M₁ (2 * M₁) n) ⌈2 * M₁⌉₊ 1 t *
        perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t *
        mtWattUnitBlock N N' t‖ ^ (2 : ℕ) ≤
      (2 * (6 * Real.pi + 1) / T) ^ 2 *
        ((5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) *
          (((⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) *
            (1 + Real.log ((⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ)) ^ fourthMomentExponent 5)) := by
  classical
  set F₁ := mtRealIntervalAF α M₁ (2 * M₁) with hF₁
  set F₂ := mtRealIntervalAF β M₂ (2 * M₂) with hF₂
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hs₁ := mtRealIntervalAF_support_nat α M₁ (2 * M₁)
  have hs₂ := mtRealIntervalAF_support_nat β M₂ (2 * M₂)
  have hfac : ∀ t, perronPoly (fun n => F₁ n) ⌈2 * M₁⌉₊ 1 t *
      perronPoly (fun n => F₂ n) ⌈2 * M₂⌉₊ 1 t =
      perronPoly (fun n => (F₁ * F₂) n) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) 1 t := fun t =>
    (perronPoly_arithmeticFunction_mul _ _ hs₁ hs₂ 1 t).symm
  set C₀ : ℝ := 2 * (6 * Real.pi + 1) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  -- pointwise Kuzmin–Landau
  have hpt : ∀ t ∈ E, ‖perronPoly (fun n => F₁ n) ⌈2 * M₁⌉₊ 1 t *
      perronPoly (fun n => F₂ n) ⌈2 * M₂⌉₊ 1 t * mtWattUnitBlock N N' t‖ ^ (2 : ℕ) ≤
      (C₀ / T) ^ 2 *
        ‖perronPoly (fun n => (F₁ * F₂) n) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) 1 t‖ ^ 2 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hEsub ht
    have hU := norm_mtWattUnitBlock_le_over_height hN hNN' hN' hT0 h1 h2 hTN
    rw [hfac t, norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hU 2) (sq_nonneg _)
  have hcont : Continuous fun t =>
      ‖perronPoly (fun n => (F₁ * F₂) n) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) 1 t‖ ^ 2 :=
    (continuous_perronPoly _ _ 1).norm.pow 2
  have hint : IntegrableOn (fun t => (C₀ / T) ^ 2 *
      ‖perronPoly (fun n => (F₁ * F₂) n) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) 1 t‖ ^ 2) (Set.Icc (-T) T) :=
    (continuous_const.mul hcont).integrableOn_Icc
  have hEI : E ⊆ Set.Icc (-T) T := fun t ht =>
    ⟨by linarith [(hEsub ht).1], (hEsub ht).2⟩
  have hstep : ∫ t in E, ‖perronPoly (fun n => F₁ n) ⌈2 * M₁⌉₊ 1 t *
        perronPoly (fun n => F₂ n) ⌈2 * M₂⌉₊ 1 t * mtWattUnitBlock N N' t‖ ^ (2 : ℕ) ≤
      ∫ t in Set.Icc (-T) T, (C₀ / T) ^ 2 *
        ‖perronPoly (fun n => (F₁ * F₂) n) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) 1 t‖ ^ 2 := by
    refine (setIntegral_mono_on ?_ (hint.mono_set hEI) hE hpt).trans ?_
    · exact ((((continuous_perronPoly _ _ 1).mul (continuous_perronPoly _ _ 1)).mul
        (continuous_mtWattUnitBlock N N')).norm.pow 2).integrableOn_Icc.mono_set
          (hEsub.trans (Set.Icc_subset_Icc le_rfl le_rfl))
    · exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun t => by positivity)
        (Filter.Eventually.of_forall hEI)
  refine hstep.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hscale : MTRealScaleSupported (F₁ * F₂) (M₁ * M₂) ((2 * M₁) * (2 * M₂)) :=
    MTRealScaleSupported.mul (mtRealIntervalAF_scaleSupported α M₁ (2 * M₁))
      (mtRealIntervalAF_scaleSupported β M₂ (2 * M₂)) hM₁0.le hM₂0.le
  refine (integral_normSq_perronPoly_le_of_lower_support _ _ (by positivity) (by linarith)
    (fun n hn => (hscale hn).2.1)).trans ?_
  have hpre : 0 ≤ 5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2 := by
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hpre
  have hK1 : 1 ≤ ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ := by
    have h1 : 1 ≤ ⌈2 * M₁⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 1 ≤ ⌈2 * M₂⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hcoef : MTUniformDivisorBounded (5 + 5 + 1) fun n => (F₁ * F₂) n :=
    (hα.realInterval M₁ (2 * M₁)).arithmeticFunction_mul (hβ.realInterval M₂ (2 * M₂))
  have hsum := sum_card_divisors_pow_le_polylog (2 * (2 * 5 + 1)) (⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊) hK1
  have he : 2 ^ (2 * (2 * 5 + 1)) - 1 = fourthMomentExponent 5 := rfl
  rw [he] at hsum
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) hsum
  have hn0 : 0 < n := (Finset.mem_Icc.1 hn).1
  have hb := hcoef hn0
  calc ‖(F₁ * F₂) n‖ ^ 2 ≤ ((n.divisors.card : ℝ) ^ (5 + 5 + 1)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = (n.divisors.card : ℝ) ^ (2 * (2 * 5 + 1)) := by rw [← pow_mul]

/-- **Sub-height window, given Watt.**  The three-factor split with the amplifier
`𝓜 = P₁^k/k!`: Watt's bound for `∫|M₃|⁴|M₂|²` and the amplified mean value theorem for
`∫|M₁|⁴|M₂|²|𝓜|²`. -/
theorem setIntegral_typeI_II_window_le (hW : MTWattBound) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α β : ℕ → ℂ) {M₁ M₂ P εU T Bβ D Bf : ℝ} {B : Finset ℕ}
      {k K N N' : ℕ} {E : Set ℝ},
      1 / 2 ≤ M₁ → 1 / 2 ≤ M₂ → 0 < Bβ → (∀ m, ‖mtRealIntervalAF β M₂ (2 * M₂) m‖ ≤ Bβ) →
      1 ≤ N → N < N' → N' ≤ 2 * N →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 1 ≤ P → 1 ≤ k →
      (2 * P) ^ k ≤ K → 2 ≤ T → MeasurableSet E → E ⊆ Set.Icc (T / 2) T →
      (∀ t ∈ E, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      0 < D → (∀ n ∈ Finset.Icc 1 (⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * K),
        (n.divisors.card : ℝ) ≤ D) →
      0 < Bf → (∀ n, ‖(mtRealIntervalAF α M₁ (2 * M₁) * mtRealIntervalAF α M₁ (2 * M₁) *
        mtRealIntervalAF β M₂ (2 * M₂)) n‖ ≤ Bf) →
      ∫ t in E, ‖perronPoly (fun n => mtRealIntervalAF α M₁ (2 * M₁) n) ⌈2 * M₁⌉₊ 1 t *
          perronPoly (fun n => mtRealIntervalAF β M₂ (2 * M₂) n) ⌈2 * M₂⌉₊ 1 t *
          mtWattUnitBlock N N' t‖ ^ (2 : ℕ) ≤
        (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) * Real.sqrt (
          (32 * C * T ^ η * Bβ ^ 2 * ((T + 4 * M₂ ^ 2 * Real.sqrt T) / ((N : ℝ) ^ 2 * M₂) +
            (T + 2 * M₂) / (T ^ 4 * M₂))) *
          ((5 * Real.pi * Real.exp 1 / (M₁ * M₁ * M₂ * P ^ k) +
              5 * Real.pi / 2 * T / (M₁ * M₁ * M₂ * P ^ k) ^ 2) *
            (D * (((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) * Bf ^ 2 *
              ((P + 1) ^ k / k.factorial))))) := by
  obtain ⟨C, hC, hWatt⟩ := integral_unitBlock_fourth_twist_le hW hη
  refine ⟨C, hC, ?_⟩
  intro α β M₁ M₂ P εU T Bβ D Bf B k K N N' E hM₁ hM₂ hBβ0 hBβ hN hNN' hN' hBp hB hP hk hK hT
    hE hEsub hS hD0 hD hBf0 hBf
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : 0 < P := by linarith
  have hKf : (0 : ℝ) < ((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ : ℕ) : ℝ) := by
    have h1 : 0 < ⌈2 * M₁⌉₊ := Nat.ceil_pos.2 (by positivity)
    have h2 : 0 < ⌈2 * M₂⌉₊ := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast Nat.mul_pos (Nat.mul_pos h1 h1) h2
  have hf0 : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  refine setIntegral_normSq_mul_three_le_sqrt (continuous_perronPoly _ _ 1)
    (continuous_perronPoly _ _ 1) (continuous_mtWattUnitBlock N N') (continuous_perronPoly _ _ 1)
    hE (by linarith) hEsub (by positivity)
    (fun t ht => one_le_factorial_mul_rpow_mul_amplifier hBp hP hB hk hK (hS t ht))
    (hWatt β hM₂ hBβ hN hNN' hN' hT)
    (integral_amplified_short_twist_le α β hM₁ hM₂ hBp hB hP hk hK (by linarith) hD0.le hD hBf)
    (by positivity) (by positivity)

end

end RHTower.Sieve
