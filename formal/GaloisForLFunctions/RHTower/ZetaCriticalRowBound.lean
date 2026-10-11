import GaloisForLFunctions.RHTower.ZetaCriticalWindowStructure
import GaloisForLFunctions.HTGeometry.FejerNearLattice

/-!
# Fejér pair rows over the ordered zeros

For a finite index set `B`, put
`Ψ_n = Σ_{k ∈ B} e^{iθ(γ_n − γ_k)} · 4/(4 + (γ_n − γ_k)²) · K_c(γ_n − γ_k)`, where
`K_c(Δ) = sinc(cΔ/2)²` is the Fejér kernel.

* `norm_critRow_le_lorentzMass`: `‖Ψ_n‖ ≤ 4 Σ_ρ 1/(1 + (γ_n − γ)²)`.
* `norm_critRow_le_six_narrowMass`: `‖Ψ_n‖ ≤ 6 M_τ(t)` when `|γ_n − t| ≤ τ`, `2/c ≤ τ ≤ 1`, using
  `K_c ≤ 2 f_{2/c}` and `f_τ(u) ≤ 3 f_τ(u + v)` for `|v| ≤ τ`.
* `norm_critRow_le_of_window`: the good-row bound. Inside a window where all gaps agree up to the
  factor `E = e^η ≤ 6/5`, the zeros near `γ_n` form a near-lattice with spacing `g = g_n`. If `g` is
  non-resonant (`c ≤ θ`, `θg/2π ≤ 1/2`, `cg/2π ≤ 1/2`), the Poisson cancellation of
  `norm_fejer_pair_sum_le` gives
  `‖Ψ_n‖ ≤ 16/(c²gτ₂) + (θ + 2c)(E − 1)(2τ₂E/g + 3)(τ₂E + g) + (2τ₂E/g + 3)((τ₂E + g)E)²/4
    + (8/(c²τ₂²)) · 3Λ₀`, where `Λ₀ ≥ M_{τ₂}(t)`.
-/

noncomputable section

open Complex Finset
open GaloisForLFunctions.HTGeometry (lorentzF lorentzF_nonneg lorentzF_mono_scale
  lorentzF_le_three_mul_shift fejerKernel norm_fejerKernel_le_one norm_fejerKernel_le_two_lorentzF
  norm_fejer_pair_sum_le sub_ge_of_gaps sub_le_of_gaps)

namespace RHTower

/-- The Fejér pair row `Ψ_n`. -/
def critRow (θ c : ℝ) (B : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ k ∈ B, Complex.exp ((θ * (xiOrderedPositiveOrdinate n - xiOrderedPositiveOrdinate k) : ℝ) * I) *
    ((4 / (4 + (xiOrderedPositiveOrdinate n - xiOrderedPositiveOrdinate k) ^ 2) : ℝ) : ℂ) *
    fejerKernel c (xiOrderedPositiveOrdinate n - xiOrderedPositiveOrdinate k)

/-- The norm of one row term. -/
theorem norm_critRow_term_eq (θ c Δ : ℝ) :
    ‖Complex.exp ((θ * Δ : ℝ) * I) * ((4 / (4 + Δ ^ 2) : ℝ) : ℂ) * fejerKernel c Δ‖ =
      4 / (4 + Δ ^ 2) * ‖fejerKernel c Δ‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `‖Ψ_n‖ ≤ 4 Σ_ρ 1/(1 + (γ_n − γ)²)`. -/
theorem norm_critRow_le_lorentzMass (θ c : ℝ) (B : Finset ℕ) (n : ℕ) :
    ‖critRow θ c B n‖ ≤ 4 * lorentzMass (xiOrderedPositiveOrdinate n) := by
  set γ := xiOrderedPositiveOrdinate with hγ
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ k ∈ B, ‖Complex.exp ((θ * (γ n - γ k) : ℝ) * I) *
      ((4 / (4 + (γ n - γ k) ^ 2) : ℝ) : ℂ) * fejerKernel c (γ n - γ k)‖ ≤
      4 * lorentzF 1 (γ n - γ k) := by
    intro k _
    rw [norm_critRow_term_eq]
    have hK := norm_fejerKernel_le_one c (γ n - γ k)
    have h1 : 4 / (4 + (γ n - γ k) ^ 2) ≤ 4 * lorentzF 1 (γ n - γ k) := by
      unfold lorentzF
      rw [one_pow, mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    calc 4 / (4 + (γ n - γ k) ^ 2) * ‖fejerKernel c (γ n - γ k)‖
        ≤ 4 / (4 + (γ n - γ k) ^ 2) * 1 := mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ 4 * lorentzF 1 (γ n - γ k) := by rw [mul_one]; exact h1
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact (sum_lorentzF_ordinate_le_narrowMass one_pos le_rfl B (γ n)).trans
    (narrowMass_le_lorentzMass zero_le_one le_rfl _)

/-- `‖Ψ_n‖ ≤ 6 M_τ(t)` for `|γ_n − t| ≤ τ` and `2/c ≤ τ ≤ 1`. -/
theorem norm_critRow_le_six_narrowMass {θ c τ t : ℝ} (hc : 0 < c) (hcτ : 2 / c ≤ τ) (hτ1 : τ ≤ 1)
    (B : Finset ℕ) {n : ℕ} (hn : |xiOrderedPositiveOrdinate n - t| ≤ τ) :
    ‖critRow θ c B n‖ ≤ 6 * narrowMass τ t := by
  set γ := xiOrderedPositiveOrdinate with hγ
  have hτ : 0 < τ := lt_of_lt_of_le (by positivity) hcτ
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ k ∈ B, ‖Complex.exp ((θ * (γ n - γ k) : ℝ) * I) *
      ((4 / (4 + (γ n - γ k) ^ 2) : ℝ) : ℂ) * fejerKernel c (γ n - γ k)‖ ≤
      6 * lorentzF τ (t - γ k) := by
    intro k _
    rw [norm_critRow_term_eq]
    have hK := norm_fejerKernel_le_two_lorentzF hc (γ n - γ k)
    have hw : 4 / (4 + (γ n - γ k) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg (γ n - γ k)]
    have h2 := lorentzF_mono_scale (by positivity) hcτ (γ n - γ k)
    have h3 := lorentzF_le_three_mul_shift hτ (γ n - γ k) (v := t - γ n)
      (by rw [abs_sub_comm]; exact hn)
    rw [show γ n - γ k + (t - γ n) = t - γ k by ring] at h3
    calc 4 / (4 + (γ n - γ k) ^ 2) * ‖fejerKernel c (γ n - γ k)‖
        ≤ 1 * (2 * lorentzF (2 / c) (γ n - γ k)) :=
          mul_le_mul hw hK (norm_nonneg _) zero_le_one
      _ ≤ 6 * lorentzF τ (t - γ k) := by linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact sum_lorentzF_ordinate_le_narrowMass hτ hτ1 B t


/-- **Non-resonance** for `0 < c ≤ θ`, `θg/2π ≤ 1/2`, `cg/2π ≤ 1/2`. -/
theorem nonresonant_of_small {c θ g : ℝ} (hc : 0 < c) (hcθ : c ≤ θ) (hg : 0 < g)
    (hθg : θ * g / (2 * Real.pi) ≤ 1 / 2) (hcg : c * g / (2 * Real.pi) ≤ 1 / 2) :
    ∀ ℓ : ℤ, c * g / (2 * Real.pi) ≤ |-(θ * g) / (2 * Real.pi) + ℓ| := by
  intro ℓ
  have hπ := Real.pi_pos
  have h1 : c * g / (2 * Real.pi) ≤ θ * g / (2 * Real.pi) := by gcongr
  have h0 : 0 ≤ c * g / (2 * Real.pi) := by positivity
  rw [neg_div]
  rcases lt_trichotomy ℓ 0 with h | h | h
  · have : (ℓ : ℝ) ≤ -1 := by exact_mod_cast (show ℓ ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]; linarith
  · rw [h, Int.cast_zero, add_zero, abs_neg, abs_of_nonneg (h0.trans h1)]; exact h1
  · have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
    rw [abs_of_pos (by linarith)]; linarith

/-- `|Δ − kg| ≤ kg(E − 1)` when `k g/E ≤ Δ ≤ k g E`. -/
theorem abs_sub_le_of_mem_ratio {Δ g E : ℝ} {k : ℝ} (hk : 0 ≤ k) (hg : 0 < g) (hE : 1 ≤ E)
    (hlo : k * (g / E) ≤ Δ) (hup : Δ ≤ k * (g * E)) : |Δ - k * g| ≤ k * g * (E - 1) := by
  have hE0 : 0 < E := by linarith
  have h2 : 2 - E ≤ 1 / E := by rw [le_div_iff₀ hE0]; nlinarith [sq_nonneg (E - 1)]
  have h3 : k * g * (2 - E) ≤ k * (g / E) := by
    rw [show k * (g / E) = k * g * (1 / E) by ring]
    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg hk hg.le)
  rw [abs_le]; constructor <;> nlinarith

/-- The cutoff arithmetic of the good-row bound, for `τ₂E/g ≤ M < τ₂E/g + 1`. -/
theorem row_cutoff_bound {τ₂ g E θ c Λ₀ : ℝ} (M : ℕ) (hτ₂ : 0 < τ₂) (hg : 0 < g) (hE1 : 1 ≤ E)
    (hc : 0 < c) (hθ : 0 < θ) (hM1 : τ₂ * E / g ≤ M) (hM2 : (M : ℝ) < τ₂ * E / g + 1) :
    16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) + (|θ| + 2 * c) * g * (E - 1) * (2 * M + 1) * M +
        (2 * M + 1) * (M * g * (1 + (E - 1))) ^ 2 / 4 + 8 / (c ^ 2 * τ₂ ^ 2) * (3 * Λ₀) ≤
      16 / (c ^ 2 * g * τ₂) + (θ + 2 * c) * (E - 1) * (2 * τ₂ * E / g + 3) * (τ₂ * E + g) +
        (2 * τ₂ * E / g + 3) * ((τ₂ * E + g) * E) ^ 2 / 4 + 8 / (c ^ 2 * τ₂ ^ 2) * (3 * Λ₀) := by
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hE0 : 0 < E := by linarith
  have ha' : 16 / (c ^ 2 * g ^ 2 * ((M : ℝ) + 1)) ≤ 16 / (c ^ 2 * g * τ₂) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : τ₂ ≤ g * ((M : ℝ) + 1) := by
      rw [div_le_iff₀ hg] at hM1; nlinarith
    have : c ^ 2 * g * τ₂ ≤ c ^ 2 * g * (g * ((M : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hMg2 : (M : ℝ) * g ≤ τ₂ * E + g := by
    have := (lt_div_iff₀ hg).mp (show (M : ℝ) - 1 < τ₂ * E / g by linarith)
    linarith
  have h2M : 2 * (M : ℝ) + 1 ≤ 2 * τ₂ * E / g + 3 := by
    have : 2 * (τ₂ * E / g) = 2 * τ₂ * E / g := by ring
    linarith
  have hb' : (|θ| + 2 * c) * g * (E - 1) * (2 * M + 1) * M ≤
      (θ + 2 * c) * (E - 1) * (2 * τ₂ * E / g + 3) * (τ₂ * E + g) := by
    rw [abs_of_pos hθ]
    have e : (θ + 2 * c) * g * (E - 1) * (2 * M + 1) * M =
        (θ + 2 * c) * (E - 1) * (2 * M + 1) * (M * g) := by ring
    rw [e]
    have hE1' : 0 ≤ E - 1 := by linarith
    gcongr
  have hc' : (2 * (M : ℝ) + 1) * (M * g * (1 + (E - 1))) ^ 2 / 4 ≤
      (2 * τ₂ * E / g + 3) * ((τ₂ * E + g) * E) ^ 2 / 4 := by
    rw [show 1 + (E - 1) = E by ring]
    gcongr
  linarith

/-- **Near-lattice from comparable gaps.** If every gap of a sequence on `[a, b)` lies in
`[g/E, gE]` and `a + M ≤ n`, `n + M ≤ b`, then `|y_{n+m} − y_n − mg| ≤ |m| g (E − 1)` for `|m| ≤ M`. -/
theorem nearLattice_of_gaps {y : ℕ → ℝ} {g E : ℝ} {a b n M : ℕ} (hg : 0 < g) (hE1 : 1 ≤ E)
    (hgup : ∀ k, a ≤ k → k < b → y (k + 1) - y k ≤ g * E)
    (hglo : ∀ k, a ≤ k → k < b → g / E ≤ y (k + 1) - y k) (haM : a + M ≤ n) (hbM : n + M ≤ b) :
    ∀ m : ℤ, |m| ≤ M → |(y (n + m).toNat - y n) - m * g| ≤ (|m| : ℤ) * g * (E - 1) := by
  intro m hm
  have hna : a ≤ n := by omega
  have hnb : n ≤ b := by omega
  rcases le_or_gt 0 m with hm0 | hm0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
    have hk : k ≤ M := by rw [abs_of_nonneg hm0] at hm; exact_mod_cast hm
    rw [show ((n : ℤ) + (k : ℤ)).toNat = n + k by omega]
    have hup := sub_le_of_gaps hgup hna (show n ≤ n + k by omega) (by omega : n + k ≤ b)
    have hlo := sub_ge_of_gaps hglo hna (show n ≤ n + k by omega) (by omega : n + k ≤ b)
    rw [show n + k - n = k by omega] at hup hlo
    rw [abs_of_nonneg hm0]
    push_cast
    exact abs_sub_le_of_mem_ratio (Nat.cast_nonneg k) hg hE1 hlo hup
  · set k := m.natAbs with hkdef
    have hmk : m = -(k : ℤ) := by omega
    have hk : k ≤ M := by
      rw [abs_of_neg hm0] at hm
      have : (k : ℤ) ≤ M := by omega
      exact_mod_cast this
    rw [show ((n : ℤ) + m).toNat = n - k by omega]
    have hup := sub_le_of_gaps hgup (show a ≤ n - k by omega) (show n - k ≤ n by omega) hnb
    have hlo := sub_ge_of_gaps hglo (show a ≤ n - k by omega) (show n - k ≤ n by omega) hnb
    rw [show n - (n - k) = k by omega] at hup hlo
    rw [abs_of_neg hm0, hmk]
    push_cast
    have := abs_sub_le_of_mem_ratio (Nat.cast_nonneg k) hg hE1 hlo hup
    rw [show y (n - k) - y n - -(k : ℝ) * g = -(y n - y (n - k) - k * g) by ring, abs_neg]
    simpa using this

/-- **Far points.** With gaps `≥ g/E` on `[a, b)`, `a + M ≤ n ≤ n + M ≤ b` and `τ ≤ M g/E`, every
index outside `[n − M, n + M]` is at distance `≥ τ` from `y_n`. -/
theorem far_of_gaps {y : ℕ → ℝ} (hy : Monotone y) {g E τ : ℝ} {a b n M : ℕ} (hτ : 0 ≤ τ)
    (hglo : ∀ k, a ≤ k → k < b → g / E ≤ y (k + 1) - y k) (haM : a + M ≤ n) (hbM : n + M ≤ b)
    (hMg : τ ≤ (M : ℝ) * (g / E)) :
    ∀ k, k ∉ Finset.Icc (n - M) (n + M) → τ ≤ |y n - y k| := by
  intro k hk
  rw [Finset.mem_Icc] at hk; push Not at hk
  rcases lt_or_ge k (n - M) with hk1 | hk1
  · have h1 := sub_ge_of_gaps hglo (show a ≤ n - M by omega) (show n - M ≤ n by omega)
      (show n ≤ b by omega)
    rw [show n - (n - M) = M by omega] at h1
    have h2 := hy hk1.le
    rw [abs_of_nonneg (by linarith)]; linarith
  · have hk2 : n + M < k := hk hk1
    have h1 := sub_ge_of_gaps hglo (show a ≤ n by omega) (show n ≤ n + M by omega) hbM
    rw [show n + M - n = M by omega] at h1
    have h2 := hy hk2.le
    rw [abs_of_nonpos (by linarith)]; linarith

/-- The far mass seen from `γ_n` is at most `3 M_τ(t)` when `|γ_n − t| ≤ τ`. -/
theorem sum_filter_lorentzF_le_three_narrowMass {τ t : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (B : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] {n : ℕ}
    (hn : |xiOrderedPositiveOrdinate n - t| ≤ τ) :
    ∑ k ∈ B.filter P, lorentzF τ (xiOrderedPositiveOrdinate n - xiOrderedPositiveOrdinate k) ≤
      3 * narrowMass τ t := by
  set γ := xiOrderedPositiveOrdinate with hγ
  calc ∑ k ∈ B.filter P, lorentzF τ (γ n - γ k)
      ≤ ∑ k ∈ B, lorentzF τ (γ n - γ k) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => lorentzF_nonneg _ _)
    _ ≤ ∑ k ∈ B, 3 * lorentzF τ (t - γ k) := Finset.sum_le_sum fun k _ => by
        have h3 := lorentzF_le_three_mul_shift hτ (γ n - γ k) (v := t - γ n)
          (by rw [abs_sub_comm]; exact hn)
        rwa [show γ n - γ k + (t - γ n) = t - γ k by ring] at h3
    _ = 3 * ∑ k ∈ B, lorentzF τ (t - γ k) := by rw [Finset.mul_sum]
    _ ≤ 3 * narrowMass τ t := by
        gcongr; exact sum_lorentzF_ordinate_le_narrowMass hτ hτ1 B t

/-- The window index facts: `a ≤ n ≤ b`, the gaps on `[a, b)` lie in `[g/E, gE]`, and the cutoff
`M = ⌈τ₂E/g⌉` fits: `a + M ≤ n`, `n + M ≤ b`. -/
theorem window_index_facts {t τ₁ τ₂ E : ℝ} {n a b : ℕ}
    (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hE1 : 1 ≤ E) (hE : E ≤ 6 / 5)
    (hratio : ∀ m m', |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ →
      |xiOrderedPositiveOrdinate m' - t| ≤ 8 * τ₂ → ordinateGap m' ≤ ordinateGap m * E)
    (ha1 : t - 7 * τ₂ < xiOrderedPositiveOrdinate a)
    (ha2 : xiOrderedPositiveOrdinate a < t - 5 * τ₂)
    (hb1 : t + 5 * τ₂ < xiOrderedPositiveOrdinate b)
    (hb2 : xiOrderedPositiveOrdinate b < t + 7 * τ₂)
    (hn : |xiOrderedPositiveOrdinate n - t| ≤ τ₁) (hg : 0 < ordinateGap n)
    (hgτ : ordinateGap n ≤ τ₂) :
    (∀ k, a ≤ k → k < b →
      xiOrderedPositiveOrdinate (k + 1) - xiOrderedPositiveOrdinate k ≤ ordinateGap n * E) ∧
    (∀ k, a ≤ k → k < b →
      ordinateGap n / E ≤ xiOrderedPositiveOrdinate (k + 1) - xiOrderedPositiveOrdinate k) ∧
    a + ⌈τ₂ * E / ordinateGap n⌉₊ ≤ n ∧ n + ⌈τ₂ * E / ordinateGap n⌉₊ ≤ b := by
  set γ := xiOrderedPositiveOrdinate with hγ
  set g := ordinateGap n with hgdef
  have hE0 : 0 < E := by linarith
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  rw [abs_le] at hn
  have hwin : ∀ k, a ≤ k → k ≤ b → |γ k - t| ≤ 8 * τ₂ := by
    intro k hk1 hk2
    have h1 := xiOrderedPositiveOrdinate_monotone hk1
    have h2 := xiOrderedPositiveOrdinate_monotone hk2
    rw [abs_le]; constructor <;> linarith
  have hna : a ≤ n := by
    by_contra h; push Not at h
    have := xiOrderedPositiveOrdinate_monotone h.le; linarith
  have hnb : n ≤ b := by
    by_contra h; push Not at h
    have := xiOrderedPositiveOrdinate_monotone h.le; linarith
  have hnwin : |γ n - t| ≤ 8 * τ₂ := hwin n hna hnb
  have hgup : ∀ k, a ≤ k → k < b → γ (k + 1) - γ k ≤ g * E :=
    fun k hk1 hk2 => hratio n k hnwin (hwin k hk1 hk2.le)
  have hglo : ∀ k, a ≤ k → k < b → g / E ≤ γ (k + 1) - γ k := by
    intro k hk1 hk2
    have := hratio k n (hwin k hk1 hk2.le) hnwin
    rw [div_le_iff₀ hE0]; exact this
  set M : ℕ := ⌈τ₂ * E / g⌉₊ with hM
  have hM2 : (M : ℝ) < τ₂ * E / g + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkey : τ₂ * E / g + 1 ≤ 4 * τ₂ / (g * E) := by
    rw [div_add_one hg.ne', div_le_div_iff₀ hg (by positivity)]
    have e1 : E * E ≤ 6 / 5 * (6 / 5) := mul_le_mul hE hE hE0.le (by norm_num)
    have e2 : g * E ≤ τ₂ * (6 / 5) := mul_le_mul hgτ hE hE0.le hτ₂.le
    have h6 : (τ₂ * E + g) * E ≤ 4 * τ₂ := by
      nlinarith [mul_le_mul_of_nonneg_left e1 hτ₂.le]
    nlinarith
  refine ⟨hgup, hglo, ?_, ?_⟩
  · have hs := sub_le_of_gaps hgup le_rfl hna hnb
    have h2 : 4 * τ₂ / (g * E) < ((n - a : ℕ) : ℝ) := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    have h3 : (M : ℝ) < ((n - a : ℕ) : ℝ) := by linarith
    have : M < n - a := by exact_mod_cast h3
    omega
  · have hs := sub_le_of_gaps hgup hna hnb le_rfl
    have h2 : 4 * τ₂ / (g * E) < ((b - n : ℕ) : ℝ) := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    have h3 : (M : ℝ) < ((b - n : ℕ) : ℝ) := by linarith
    have : M < b - n := by exact_mod_cast h3
    omega

/-- **The good-row bound.** -/
theorem norm_critRow_le_of_window {t τ₁ τ₂ η θ c Λ₀ : ℝ} {B : Finset ℕ} {n a b : ℕ}
    (hτ₁ : 0 < τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂1 : τ₂ ≤ 1) (hc : 0 < c) (hcθ : c ≤ θ) (hη0 : 0 ≤ η)
    (hη : Real.exp η ≤ 6 / 5)
    (hratio : ∀ m m', |xiOrderedPositiveOrdinate m - t| ≤ 8 * τ₂ →
      |xiOrderedPositiveOrdinate m' - t| ≤ 8 * τ₂ →
      ordinateGap m' ≤ ordinateGap m * Real.exp η)
    (ha1 : t - 7 * τ₂ < xiOrderedPositiveOrdinate a)
    (ha2 : xiOrderedPositiveOrdinate a < t - 5 * τ₂)
    (hb1 : t + 5 * τ₂ < xiOrderedPositiveOrdinate b)
    (hb2 : xiOrderedPositiveOrdinate b < t + 7 * τ₂)
    (hB : Finset.Icc a b ⊆ B) (hn : |xiOrderedPositiveOrdinate n - t| ≤ τ₁)
    (hg : 0 < ordinateGap n) (hgτ : ordinateGap n ≤ τ₂)
    (hθg : θ * ordinateGap n / (2 * Real.pi) ≤ 1 / 2)
    (hcg : c * ordinateGap n / (2 * Real.pi) ≤ 1 / 2)
    (hΛ : narrowMass τ₂ t ≤ Λ₀) :
    ‖critRow θ c B n‖ ≤ 16 / (c ^ 2 * ordinateGap n * τ₂) +
      (θ + 2 * c) * (Real.exp η - 1) * (2 * τ₂ * Real.exp η / ordinateGap n + 3) *
        (τ₂ * Real.exp η + ordinateGap n) +
      (2 * τ₂ * Real.exp η / ordinateGap n + 3) *
        ((τ₂ * Real.exp η + ordinateGap n) * Real.exp η) ^ 2 / 4 +
      8 / (c ^ 2 * τ₂ ^ 2) * (3 * Λ₀) := by
  classical
  have hE1 : 1 ≤ Real.exp η := Real.one_le_exp hη0
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ₁₂
  have hθ : 0 < θ := hc.trans_le hcθ
  obtain ⟨hgup, hglo, haM, hbM⟩ := window_index_facts hτ₁ hτ₁₂ hE1 hη hratio ha1 ha2 hb1 hb2 hn
    hg hgτ
  set M : ℕ := ⌈τ₂ * Real.exp η / ordinateGap n⌉₊ with hM
  have hM1 : τ₂ * Real.exp η / ordinateGap n ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) < τ₂ * Real.exp η / ordinateGap n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMg : τ₂ ≤ (M : ℝ) * (ordinateGap n / Real.exp η) := by
    rw [div_le_iff₀ hg] at hM1
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]; linarith
  have hB' : Finset.Icc (n - M) (n + M) ⊆ B := by
    refine subset_trans ?_ hB
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hnear := nearLattice_of_gaps hg hE1 hgup hglo haM hbM
  have hfar := far_of_gaps xiOrderedPositiveOrdinate_monotone hτ₂.le hglo haM hbM hMg
  have hmass := sum_filter_lorentzF_le_three_narrowMass hτ₂ hτ₂1 B
    (fun k => k ∉ Finset.Icc (n - M) (n + M)) (hn.trans hτ₁₂)
  have hmass' : ∑ k ∈ B.filter (fun k => k ∉ Finset.Icc (n - M) (n + M)),
      lorentzF τ₂ (xiOrderedPositiveOrdinate n - xiOrderedPositiveOrdinate k) ≤ 3 * Λ₀ :=
    hmass.trans (by linarith)
  have hres := nonresonant_of_small hc hcθ hg hθg hcg
  refine (norm_fejer_pair_sum_le (θ := θ) M n hc hg (by linarith : 0 ≤ Real.exp η - 1) hτ₂
    (by omega) hB' hres hnear (fun k _ hk => hfar k hk) hmass').trans ?_
  exact row_cutoff_bound M hτ₂ hg hE1 hc hθ hM1 hM2

end RHTower
