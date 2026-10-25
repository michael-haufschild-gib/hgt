import GaloisForLFunctions.HTGeometry.HamburgerGeneralFrequencies

/-!
# The Riemann theta relation with integral masses forces the integers

Let `ν = Σ_n a_n δ_{λ_n}` be a discrete measure on `[1, ∞)`: frequencies `1 = λ_0 < λ_1 < ⋯`
with masses `a_n ≥ 1` (every atom counted at least once) and `Σ a_n/λ_n² < ∞`.  Suppose `ν`
satisfies the theta relation of `ζ`: `1 + 2θ` is self-dual, `θ(x) = Σ a_n e^{-πλ_n² x}`,

`θ(x) = x^{-1/2} θ(1/x) - 1/2 + x^{-1/2}/2`   (`RiemannThetaRelation`),

the additive (Poisson) form of `π^{-s/2}Γ(s/2)ζ_ν(s) = π^{-(1-s)/2}Γ((1-s)/2)ζ_ν(1-s)`.

**Theorem** (`eq_integers_of_riemannThetaRelation`).  Then `λ_n = n + 1` and `a_n = 1`: the
measure is `Σ_{n ≥ 1} δ_n`, so `ζ_ν = ζ`.  No Euler product is assumed.

**Proof.**  The Laplace identity and the residues of `L(t) = Σ a_n t/(π(λ_n² + t²))` on the
imaginary axis (`HamburgerGeneralFrequencies`) give the Abel means
`C_τ(ε) = ε Σ a_n e^{-2πλ_n ε} cos(2πλ_n τ)`:
`C_0 → 1/(2π)`; `C_{λ_m} → a_m/(2π)`; `C_τ → 0` when `τ` is a positive non-frequency.  The Bohr
spectrum of `ν` is its support.
* *Unit masses.*  `cos ≤ 1` gives `a_m ≤ 1`, so `a_m = 1` and `C_0 - C_{λ_m} → 0`.
* *Integral frequencies.*  With `K = ⌊λ_m⌋` and `f = λ_m - K`,
  `1 - cos(2πλf) ≤ 2(1 - cos 2πλλ_m) + 2K²(1 - cos 2πλ)` (`one_sub_cos_sub_le`), so
  `C_0 - C_f → 0`.  If `0 < f < 1` the frequency `f` is no atom and `C_f → 0`, contradicting
  `C_0 → 1/(2π)`.  Hence `λ_m ∈ ℕ`.
* *Every integer.*  If `k ≥ 1` were missing, `C_k = C_0 → 1/(2π)` (all `λ_n ∈ ℕ`) while `k` is
  no atom, so `C_k → 0`.
* Strict monotonicity then gives `λ_n = n + 1`.

So the functional equation of `ζ`, in its Poisson form, together with integrality of the masses,
already determines the rational integers: the additive lattice is forced, and the Euler product of
`ζ` follows from it.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FreqHamburger

/-- The theta relation of `ζ`: `1 + 2θ` is invariant under `x ↦ 1/x` with weight `x^{-1/2}`. -/
def RiemannThetaRelation (a : ℕ → ℂ) (lam : ℕ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → freqTheta a lam x =
    (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta a lam x⁻¹ + (-(1 / 2 : ℂ)) +
      (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ))

/-! ## Trigonometric inequalities -/

theorem abs_sin_nat_mul_le (k : ℕ) (x : ℝ) : |Real.sin (k * x)| ≤ k * |Real.sin x| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : Real.sin (((k + 1 : ℕ) : ℝ) * x) = Real.sin (k * x) * Real.cos x +
        Real.cos (k * x) * Real.sin x := by
      rw [show ((k + 1 : ℕ) : ℝ) * x = k * x + x by push_cast; ring, Real.sin_add]
    rw [h]
    calc |Real.sin (k * x) * Real.cos x + Real.cos (k * x) * Real.sin x|
        ≤ |Real.sin (k * x)| * |Real.cos x| + |Real.cos (k * x)| * |Real.sin x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |Real.sin (k * x)| * 1 + 1 * |Real.sin x| := by
          gcongr
          · exact Real.abs_cos_le_one x
          · exact Real.abs_cos_le_one _
      _ ≤ k * |Real.sin x| + |Real.sin x| := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * |Real.sin x| := by push_cast; ring

/-- `1 - cos(kx) ≤ k²(1 - cos x)`. -/
theorem one_sub_cos_nat_mul_le (k : ℕ) (x : ℝ) :
    1 - Real.cos (k * x) ≤ (k : ℝ) ^ 2 * (1 - Real.cos x) := by
  have h1 : 1 - Real.cos (k * x) = 2 * Real.sin (k * (x / 2)) ^ 2 := by
    rw [show (k : ℝ) * x = 2 * (k * (x / 2)) by ring, Real.cos_two_mul, Real.sin_sq]; ring
  have h2 : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul, Real.sin_sq]; ring_nf
  rw [h1, h2]
  have h := abs_sin_nat_mul_le k (x / 2)
  have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, sq_abs] at h'
  linarith

/-- `1 - cos(a - b) ≤ 2(1 - cos a) + 2(1 - cos b)`. -/
theorem one_sub_cos_sub_le (a b : ℝ) :
    1 - Real.cos (a - b) ≤ 2 * (1 - Real.cos a) + 2 * (1 - Real.cos b) := by
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b,
    sq_nonneg (Real.sin a + Real.sin b), sq_nonneg (Real.cos a + Real.cos b - 2)]

/-- `1 - cos(x(λ - K)) ≤ 2(1 - cos λx) + 2K²(1 - cos x)`. -/
theorem one_sub_cos_frac_le (x l : ℝ) (K : ℕ) :
    1 - Real.cos (x * (l - K)) ≤ 2 * (1 - Real.cos (x * l)) + 2 * (K : ℝ) ^ 2 * (1 - Real.cos x) := by
  have h := one_sub_cos_sub_le (x * l) (K * x)
  have h2 := one_sub_cos_nat_mul_le K x
  rw [show x * (l - K) = x * l - K * x by ring]
  linarith

/-! ## Abel means -/

variable {a : ℕ → ℝ} {lam : ℕ → ℝ}

/-- The Abel mean `C_τ(ε) = ε Σ a_n e^{-2πλ_n ε} cos(2πλ_n τ)`. -/
def abelCos (a lam : ℕ → ℝ) (τ ε : ℝ) : ℝ :=
  ε * ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) * Real.cos (2 * Real.pi * lam n * τ)

theorem summable_abelWeight (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {ε : ℝ} (hε : 0 < ε) :
    Summable fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε)) := by
  refine (ha.mul_left (2 / (2 * Real.pi * ε) ^ 2)).of_nonneg_of_le
    (fun n => mul_nonneg (ha0 n) (Real.exp_pos _).le) fun n => ?_
  have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
  have hy : 0 < 2 * Real.pi * lam n * ε := by positivity
  have he := exp_neg_le_two_div_sq hy
  calc a n * Real.exp (-(2 * Real.pi * lam n * ε)) ≤ a n * (2 / (2 * Real.pi * lam n * ε) ^ 2) :=
        mul_le_mul_of_nonneg_left he (ha0 n)
    _ = 2 / (2 * Real.pi * ε) ^ 2 * (a n / lam n ^ 2) := by
        field_simp

theorem summable_abelCos (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      Real.cos (2 * Real.pi * lam n * τ) :=
  Summable.of_norm_bounded (summable_abelWeight hlam ha0 ha hε) fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (ha0 n) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (mul_nonneg (ha0 n) (Real.exp_pos _).le)
      (Real.abs_cos_le_one _)

/-- Termwise comparison of Abel means with nonnegative weights. -/
theorem abelCos_le_of_le (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {τ₁ τ₂ : ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ n, Real.cos (2 * Real.pi * lam n * τ₁) ≤ Real.cos (2 * Real.pi * lam n * τ₂)) :
    abelCos a lam τ₁ ε ≤ abelCos a lam τ₂ ε := by
  unfold abelCos
  refine mul_le_mul_of_nonneg_left ((summable_abelCos hlam ha0 ha τ₁ hε).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (h n) (mul_nonneg (ha0 n) (Real.exp_pos _).le))
    (summable_abelCos hlam ha0 ha τ₂ hε)) hε.le

theorem summable_abelGap (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      (1 - Real.cos (2 * Real.pi * lam n * τ)) :=
  ((summable_abelWeight hlam ha0 ha hε).mul_right 2).of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (ha0 n) (Real.exp_pos _).le)
      (by linarith [Real.cos_le_one (2 * Real.pi * lam n * τ)]))
    fun n => mul_le_mul_of_nonneg_left (by linarith [Real.neg_one_le_cos (2 * Real.pi * lam n * τ)])
      (mul_nonneg (ha0 n) (Real.exp_pos _).le)

/-- `C_0(ε) - C_τ(ε) = ε Σ a_n e^{-2πλ_n ε}(1 - cos 2πλ_n τ)`. -/
theorem abelCos_zero_sub (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    abelCos a lam 0 ε - abelCos a lam τ ε = ε * ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      (1 - Real.cos (2 * Real.pi * lam n * τ)) := by
  unfold abelCos
  rw [← mul_sub, ← (summable_abelCos hlam ha0 ha 0 hε).tsum_sub (summable_abelCos hlam ha0 ha τ hε)]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [mul_zero, Real.cos_zero]
  ring

/-- The real part of `F(ε + iτ)` is the cosine series. -/
theorem re_freqDual (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (freqDual (fun n => (a n : ℂ)) lam ((ε : ℂ) + (τ : ℂ) * I)).re =
      ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) * Real.cos (2 * Real.pi * lam n * τ) := by
  have hterm : ∀ n, ((a n : ℂ) * cexp (-(2 * Real.pi * (lam n : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)))).re
      = a n * Real.exp (-(2 * Real.pi * lam n * ε)) * Real.cos (2 * Real.pi * lam n * τ) := by
    intro n
    rw [Complex.re_ofReal_mul, Complex.exp_re]
    have hre : (-(2 * (Real.pi : ℂ) * (lam n : ℂ) * ((ε : ℂ) + (τ : ℂ) * I))).re =
        -(2 * Real.pi * lam n * ε) := by simp
    have him : (-(2 * (Real.pi : ℂ) * (lam n : ℂ) * ((ε : ℂ) + (τ : ℂ) * I))).im =
        -(2 * Real.pi * lam n * τ) := by simp
    rw [hre, him, Real.cos_neg]
    ring
  have hsum : Summable fun n => (a n : ℂ) * cexp (-(2 * Real.pi * (lam n : ℂ) *
      ((ε : ℂ) + (τ : ℂ) * I))) := by
    refine Summable.of_norm_bounded (summable_abelWeight hlam ha0 ha hε) fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n), Complex.norm_exp]
    simp
  rw [freqDual, Complex.re_tsum hsum]
  exact tsum_congr hterm

theorem tendsto_abelCos_of_tendsto (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {τ : ℝ} {z : ℂ}
    (h : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] 0) (𝓝 z)) :
    Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 z.re) := by
  have hre := (Complex.continuous_re.tendsto z).comp h
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp only [Function.comp, Complex.re_ofReal_mul, abelCos]
  rw [re_freqDual hlam ha0 ha τ hε]

/-! ## The Abel limits from the Laplace identity -/

theorem freqDual_eq_of_riemannThetaRelation (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hθ : RiemannThetaRelation (fun n => (a n : ℂ)) lam) {t : ℂ} (ht : 0 < t.re) :
    freqDual (fun n => (a n : ℂ)) lam t =
      freqSeries (fun n => (a n : ℂ)) lam t + 1 / (2 * Real.pi * t) - 1 / 2 := by
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 := by
    refine ha.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have h := freqSeries_eq_of_freqTheta_relation hlam haC hθ ht
  rw [h]
  have ht0 : t ≠ 0 := fun h0 => by rw [h0, zero_re] at ht; exact lt_irrefl _ ht
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- `C_0(ε) → 1/(2π)`: the density of `ν` is `1`. -/
theorem tendsto_abelCos_zero (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hθ : RiemannThetaRelation (fun n => (a n : ℂ)) lam) :
    Tendsto (abelCos a lam 0) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 := by
    refine ha.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := tendsto_mul_freqSeries_ofReal (a := fun n => (a n : ℂ)) hlam haC
  have hlin : Tendsto (fun ε : ℝ => (1 / (2 * Real.pi) : ℂ) - (ε : ℂ) / 2) (𝓝[>] 0)
      (𝓝 ((1 / (2 * Real.pi) : ℂ) - ((0 : ℝ) : ℂ) / 2)) :=
    ((by fun_prop : Continuous fun ε : ℝ => (1 / (2 * Real.pi) : ℂ) - (ε : ℂ) / 2).tendsto
      0).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + ((0 : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi) : ℂ)) := by
    have := hL.add hlin
    simp only [zero_add, Complex.ofReal_zero, zero_div, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [freqDual_eq_of_riemannThetaRelation hlam ha0 ha hθ (by simpa using hε)]
    field_simp
    ring
  have := tendsto_abelCos_of_tendsto hlam ha0 ha hF
  have hre : ((1 / (2 * Real.pi) : ℂ)).re = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rwa [hre] at this

/-- From `ε L(ε + iτ) → w` with `τ > 0`, the Abel mean `C_τ(ε) → Re w`. -/
theorem tendsto_abelCos_of_series (hlam : ∀ n, 1 ≤ lam n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hθ : RiemannThetaRelation (fun n => (a n : ℂ)) lam) {τ : ℝ} (hτ : 0 < τ) {w : ℂ}
    (hL : Tendsto (fun ε : ℝ => (ε : ℂ) * freqSeries (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] 0) (𝓝 w)) :
    Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 w.re) := by
  have hτ0 : (τ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hτ.ne') Complex.I_ne_zero
  have hcont : ContinuousAt (fun ε : ℝ => (ε : ℂ) / (2 * Real.pi * ((ε : ℂ) + (τ : ℂ) * I)) -
      (ε : ℂ) / 2) 0 := by
    refine ContinuousAt.sub (ContinuousAt.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)
    simp only [Complex.ofReal_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) hτ0
  have hlin : Tendsto (fun ε : ℝ => (ε : ℂ) / (2 * Real.pi * ((ε : ℂ) + (τ : ℂ) * I)) -
      (ε : ℂ) / 2) (𝓝[>] 0) (𝓝 0) := by
    have := hcont.tendsto
    simp only [Complex.ofReal_zero, zero_div, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun ε : ℝ => (ε : ℂ) * freqDual (fun n => (a n : ℂ)) lam
      ((ε : ℂ) + (τ : ℂ) * I)) (𝓝[>] 0) (𝓝 w) := by
    have := hL.add hlin
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hre : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simpa using hε
    have hne : (ε : ℂ) + (τ : ℂ) * I ≠ 0 := fun h0 => by rw [h0, zero_re] at hre; exact lt_irrefl _ hre
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [freqDual_eq_of_riemannThetaRelation hlam ha0 ha hθ hre]
    field_simp
    ring
  exact tendsto_abelCos_of_tendsto hlam ha0 ha hF

/-! ## Separation of the frequencies -/

theorem exists_sep_of_strictMono (hmono : StrictMono lam) (hpos : ∀ n, 0 < lam n) (m : ℕ) :
    ∃ c > 0, ∀ n, n ≠ m → c * lam n ≤ |lam n - lam m| := by
  set g : ℝ := if m = 0 then lam 1 - lam 0 else min (lam (m + 1) - lam m) (lam m - lam (m - 1))
    with hg
  have hg0 : 0 < g := by
    rw [hg]
    split_ifs with h
    · linarith [hmono (show 0 < 1 by norm_num)]
    · exact lt_min (by linarith [hmono (Nat.lt_succ_self m)])
        (by linarith [hmono (Nat.sub_lt (Nat.pos_of_ne_zero h) one_pos)])
  have hlm := hpos m
  refine ⟨g / (g + lam m), by positivity, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · -- `n < m`: `λ_m - λ_n ≥ g` and `λ_n < λ_m`
    have hm0 : m ≠ 0 := by omega
    have hgap : g ≤ lam m - lam n := by
      have h1 : lam n ≤ lam (m - 1) := hmono.monotone (by omega)
      have h2 : g ≤ lam m - lam (m - 1) := by rw [hg, if_neg hm0]; exact min_le_right _ _
      linarith
    have hln : lam n < lam m := hmono h
    rw [abs_of_neg (by linarith)]
    have : g / (g + lam m) * lam n ≤ g / (g + lam m) * lam m :=
      mul_le_mul_of_nonneg_left hln.le (by positivity)
    have h3 : g / (g + lam m) * lam m ≤ g := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · -- `n > m`: `λ_n ≥ λ_m + g`
    have hgap : lam m + g ≤ lam n := by
      have h1 : lam (m + 1) ≤ lam n := hmono.monotone (by omega)
      have h2 : g ≤ lam (m + 1) - lam m := by
        rw [hg]; split_ifs with h0
        · subst h0; simp
        · exact min_le_left _ _
      linarith
    rw [abs_of_pos (by linarith)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hpos n]

/-! ## The rigidity theorem -/

/-- **The Riemann theta relation with integral masses forces the integers.**  If
`1 = λ_0 < λ_1 < ⋯`, `a_n ≥ 1`, `Σ a_n/λ_n² < ∞` and `1 + 2 Σ a_n e^{-πλ_n² x}` satisfies the
theta relation of `ζ`, then `λ_n = n + 1` and `a_n = 1` for every `n`. -/
theorem eq_integers_of_riemannThetaRelation (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (ha1 : ∀ n, 1 ≤ a n) (ha : Summable fun n => a n / lam n ^ 2)
    (hθ : RiemannThetaRelation (fun n => (a n : ℂ)) lam) :
    ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 := by
    refine ha.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hC0 := tendsto_abelCos_zero hlam ha0 ha hθ
  have hπ2 : 0 < 1 / (2 * Real.pi) := by positivity
  -- the atoms: `C_{λ_m} → a_m/(2π)`
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0) (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hL := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl (hpos m) hc hsep
    have := tendsto_abelCos_of_series hlam ha0 ha hθ (hpos m) hL
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rwa [hre] at this
  -- unit masses
  have hunit : ∀ m, a m = 1 := by
    intro m
    have hle : a m / (2 * Real.pi) ≤ 1 / (2 * Real.pi) := by
      refine le_of_tendsto_of_tendsto (hatom m) hC0 ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
    have : a m ≤ 1 := by
      rwa [div_le_div_iff_of_pos_right (by positivity)] at hle
    linarith [ha1 m]
  -- a positive non-frequency `τ` has `C_τ → 0`
  have hgap : ∀ τ c : ℝ, 0 < τ → 0 < c → (∀ n, c * lam n ≤ |lam n - τ|) →
      Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 0) := by
    intro τ c hτ hc hsep
    have hL := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hτ.le hc hsep
    simpa using tendsto_abelCos_of_series hlam ha0 ha hθ hτ hL
  -- integral frequencies
  have hint : ∀ m, ∃ K : ℕ, lam m = K := by
    intro m
    set K : ℕ := ⌊lam m⌋₊ with hK
    set f : ℝ := lam m - K with hf
    have hf0 : 0 ≤ f := by rw [hf, hK]; linarith [Nat.floor_le (hpos m).le]
    have hf1 : f < 1 := by rw [hf, hK]; linarith [Nat.lt_floor_add_one (lam m)]
    refine ⟨K, ?_⟩
    by_contra hne
    have hfpos : 0 < f := lt_of_le_of_ne hf0 (fun h => hne (by rw [hf] at h; linarith))
    -- `C_f → 0` since `f ∈ (0, 1)` is no atom
    have hCf : Tendsto (abelCos a lam f) (𝓝[>] 0) (𝓝 0) := by
      refine hgap f (1 - f) hfpos (by linarith) fun n => ?_
      rw [abs_of_pos (by linarith [hlam n])]
      nlinarith [hlam n]
    -- `C_0 - C_f ≤ 2(C_0 - C_{λ_m}) + 2K²(C_0 - C_{λ_0})`
    have hbound : ∀ ε, 0 < ε → abelCos a lam 0 ε - abelCos a lam f ε ≤
        2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
          2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε) := by
      intro ε hε
      rw [abelCos_zero_sub hlam ha0 ha f hε, abelCos_zero_sub hlam ha0 ha (lam m) hε,
        abelCos_zero_sub hlam ha0 ha (lam 0) hε]
      have sm := summable_abelGap hlam ha0 ha (lam m) hε
      have s1 := summable_abelGap hlam ha0 ha (lam 0) hε
      have hsum : 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) =
          ∑' n, (2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
            2 * (K : ℝ) ^ 2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
              (1 - Real.cos (2 * Real.pi * lam n * lam 0)))) := by
        rw [(sm.mul_left 2).tsum_add (s1.mul_left _), tsum_mul_left, tsum_mul_left]
      have hle : ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * f)) ≤
          2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam m))) +
          2 * (K : ℝ) ^ 2 * (∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
            (1 - Real.cos (2 * Real.pi * lam n * lam 0))) := by
        rw [hsum]
        refine (summable_abelGap hlam ha0 ha f hε).tsum_le_tsum (fun n => ?_)
          ((sm.mul_left 2).add (s1.mul_left _))
        have hw := mul_nonneg (ha0 n) (Real.exp_pos (-(2 * Real.pi * lam n * ε))).le
        have htrig := one_sub_cos_frac_le (2 * Real.pi * lam n) (lam m) K
        rw [hlam0, mul_one]
        have e1 : 2 * Real.pi * lam n * f = 2 * Real.pi * lam n * (lam m - K) := by rw [hf]
        rw [e1]
        nlinarith [mul_le_mul_of_nonneg_left htrig hw]
      nlinarith [hle, hε.le]
    -- limits: the right side tends to `0`, so `C_f → 1/(2π)`
    have hR : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε) +
        2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε => 2 * (abelCos a lam 0 ε - abelCos a lam (lam m) ε)) (𝓝[>] 0)
          (𝓝 0) := by
        have := (hC0.sub (hatom m)).const_mul 2
        rwa [hunit m, sub_self, mul_zero] at this
      have h2 : Tendsto (fun ε => 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε - abelCos a lam (lam 0) ε))
          (𝓝[>] 0) (𝓝 0) := by
        have := (hC0.sub (hatom 0)).const_mul (2 * (K : ℝ) ^ 2)
        rwa [hunit 0, sub_self, mul_zero] at this
      simpa using h1.add h2
    have hlow : Tendsto (fun ε => abelCos a lam 0 ε - (2 * (abelCos a lam 0 ε -
        abelCos a lam (lam m) ε) + 2 * (K : ℝ) ^ 2 * (abelCos a lam 0 ε -
          abelCos a lam (lam 0) ε))) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      simpa using hC0.sub hR
    have hge : 1 / (2 * Real.pi) ≤ 0 := by
      refine le_of_tendsto_of_tendsto hlow hCf ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have := hbound ε hε
      linarith
    linarith
  -- every positive integer is a frequency
  have hsurj : ∀ k : ℕ, 1 ≤ k → ∃ n, lam n = k := by
    intro k hk
    by_contra hnone
    push Not at hnone
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    -- all frequencies are integers different from `k`
    have hsep : ∀ n, 1 / (2 * k) * lam n ≤ |lam n - k| := by
      intro n
      obtain ⟨K, hKn⟩ := hint n
      have hne : K ≠ k := fun h => hnone n (by rw [hKn, h])
      have hdist : 1 ≤ |lam n - k| := by
        rw [hKn]
        rcases lt_or_gt_of_ne hne with h | h
        · have : (K : ℝ) + 1 ≤ k := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (k : ℝ) + 1 ≤ K := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      rcases le_or_gt (lam n) (2 * k) with h | h
      · calc 1 / (2 * k) * lam n ≤ 1 / (2 * k) * (2 * k) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = 1 := by field_simp
          _ ≤ |lam n - k| := hdist
      · rw [abs_of_pos (by linarith)]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have : 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        nlinarith [hpos n]
    have hCk := hgap k (1 / (2 * k)) hk0 (by positivity) hsep
    have heq : ∀ ε, abelCos a lam k ε = abelCos a lam 0 ε := by
      intro ε
      unfold abelCos
      congr 1
      refine tsum_congr fun n => ?_
      obtain ⟨K, hKn⟩ := hint n
      have : Real.cos (2 * Real.pi * lam n * k) = 1 := by
        rw [hKn, show 2 * Real.pi * (K : ℝ) * k = ((K * k : ℕ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact Real.cos_nat_mul_two_pi _
      rw [this]; simp
    have : Tendsto (abelCos a lam k) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
      rw [show abelCos a lam k = abelCos a lam 0 from funext heq]; exact hC0
    have := tendsto_nhds_unique this hCk
    linarith
  -- strict monotonicity pins `λ_n = n + 1`
  have hval : ∀ n, lam n = n + 1 := by
    intro n
    induction n with
    | zero => simp [hlam0]
    | succ n ih =>
      obtain ⟨K, hK⟩ := hint (n + 1)
      have hlt : lam n < lam (n + 1) := hmono (Nat.lt_succ_self n)
      have hKge : n + 2 ≤ K := by
        rw [ih, hK] at hlt
        have : (n : ℝ) + 1 < K := by linarith
        exact_mod_cast (show n + 1 < K by exact_mod_cast this)
      obtain ⟨m, hm⟩ := hsurj (n + 2) (by omega)
      have hmn : n + 1 ≤ m := by
        by_contra h
        push Not at h
        have : lam m ≤ lam n := hmono.monotone (by omega)
        rw [hm, ih] at this
        push_cast at this
        linarith
      have hle : lam (n + 1) ≤ lam m := hmono.monotone hmn
      rw [hK, hm] at hle
      have hKle : K ≤ n + 2 := by exact_mod_cast hle
      rw [hK]
      push_cast
      have : K = n + 2 := le_antisymm hKle hKge
      rw [this]; push_cast; ring
  exact fun n => ⟨hval n, hunit n⟩

end GaloisForLFunctions.HTGeometry.FreqHamburger
