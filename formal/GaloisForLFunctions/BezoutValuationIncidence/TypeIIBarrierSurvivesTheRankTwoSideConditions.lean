import GaloisForLFunctions.BezoutValuationIncidence.SharpConstantAttainedByPrimesInTheUnitClass

/-!
# The Type-II barrier survives the rank-two side conditions

The coherent obstruction bounds the remainder `B + m R' + β H'` of the rank-two law from below. Here the
bilinear form `B` itself is bounded from below, with both rank-two readouts of the large scale killed:
`R(c') = H(c') = 0`.

Anti-coherent windows mirror coherent ones. Suppose `|n₀ mod d/d - 1/2| ≤ 1/512` and the window
`[n₀, n₀ + H)` has `512 H ≤ d`. Then every `n` in the window has `|n mod d/d - 1/2| ≤ 1/64`, so
`𝔅(d, n) ≤ -d²/100`. By double counting, a set of moduli in `[512, D]` has a `1/1024` share
anti-coherent for some shift in any interval of length `2D`.

Take three windows `W₂ < W₁ < W₃` in height, with `W₁` coherent and `W₂, W₃` anti-coherent for the same
moduli. Nested pigeonholes give a common modulus set of relative size `2⁻²⁷`. On `c' = c₁ - a₂ c₂ - a₃ c₃`
with nonnegative `cᵢ` on `Wᵢ` and `a₂, a₃ ≥ 0`, every piece pushes the kernel term up. For `n₂ ≥ 150 D`,

`B(c, c') + m R(c') + β H(c') ≥ (1/200)(Σ_d c(d) d)(Σ_n |c'(n)|/n²)`.

The ratio `ℓ = R/H` is an average of `log n` over the support, so `ℓ₂ < ℓ₁ < ℓ₃`. Then

`a₂ = H₁(ℓ₃ - ℓ₁)/(H₂(ℓ₃ - ℓ₂)) ≥ 0`,  `a₃ = H₁(ℓ₁ - ℓ₂)/(H₃(ℓ₃ - ℓ₂)) ≥ 0`

kill both readouts, and

`B(c, c') ≥ (1/200)(Σ_d c(d) d)(Σ_n |c'(n)|/n²)`  with  `R(c') = H(c') = 0`.

The two rank-two side conditions on the large scale cannot bring Type-II inputs below the rank-two
remainder size. The cross-scale barrier `Q ≍ P^{5/3}` is intrinsic to the bilinear form, not an artefact
of its rank-two part. The replacement hypothesis is still equidistribution of the large-scale
coefficients across near-multiple and near-half windows of the small moduli.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Anti-coherent windows -/

/-- Anti-coherence of `n` for the modulus `d`: `255d ≤ 512 (n mod d) ≤ 257d`. -/
def antiCoherent (d n : ℕ) : Prop := 255 * d ≤ 512 * (n % d) ∧ 512 * (n % d) ≤ 257 * d

instance (d n : ℕ) : Decidable (antiCoherent d n) := by unfold antiCoherent; infer_instance

theorem antiCoherent_periodic (d : ℕ) : Function.Periodic (antiCoherent d) d := fun n => by
  simp only [antiCoherent, Nat.add_mod_right]

/-- At least `d/512` residues are anti-coherent when `d ≥ 512`. -/
theorem le_count_antiCoherent {d : ℕ} (hd : 512 ≤ d) : d ≤ 512 * Nat.count (antiCoherent d) d := by
  have hc : Nat.count (antiCoherent d) d = ((range d).filter (antiCoherent d)).card :=
    Nat.count_eq_card_filter_range _ _
  rw [hc]
  set lo := (255 * d + 511) / 512
  have hsub : Ico lo (lo + (d / 512 + 1)) ⊆ (range d).filter (antiCoherent d) := by
    intro x hx
    have hx' := mem_Ico.mp hx
    have hxd : x < d := by omega
    simp only [mem_filter, mem_range, antiCoherent, Nat.mod_eq_of_lt hxd]
    refine ⟨hxd, by omega, by omega⟩
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

theorem card_filter_Ico_antiCoherent_ge {d : ℕ} (hd : 512 ≤ d) (Q T : ℕ) :
    T ≤ d + 512 * ((Ico Q (Q + T)).filter (antiCoherent d)).card := by
  have hd0 : 0 < d := by omega
  have hblock := card_filter_Ico_mul_eq (antiCoherent d) (antiCoherent_periodic d) Q (T / d)
  have hmono : ((Ico Q (Q + T / d * d)).filter (antiCoherent d)).card ≤
      ((Ico Q (Q + T)).filter (antiCoherent d)).card :=
    card_le_card (filter_subset_filter _ (Ico_subset_Ico_right (by
      have := Nat.div_mul_le_self T d; omega)))
  have hT : T ≤ d + T / d * d := by
    have := Nat.div_add_mod T d
    have := Nat.mod_lt T hd0
    nlinarith
  have hc := le_count_antiCoherent hd
  calc T ≤ d + T / d * d := hT
    _ ≤ d + T / d * (512 * Nat.count (antiCoherent d) d) := by gcongr
    _ = d + 512 * ((Ico Q (Q + T / d * d)).filter (antiCoherent d)).card := by rw [hblock]; ring
    _ ≤ d + 512 * ((Ico Q (Q + T)).filter (antiCoherent d)).card := by gcongr

/-- **The anti-coherent shift.** For moduli `S ⊆ [512, D]` and any `Q` there is `n₀ ∈ [Q, Q + 2D)` with
`|S| ≤ 1024 |{d ∈ S : n₀ anti-coherent for d}|`. -/
theorem exists_antiCoherent_shift {S : Finset ℕ} {D : ℕ} (hD : 0 < D)
    (hS : ∀ d ∈ S, 512 ≤ d ∧ d ≤ D) (Q : ℕ) :
    ∃ n₀ ∈ Ico Q (Q + 2 * D), S.card ≤ 1024 * (S.filter fun d => antiCoherent d n₀).card := by
  classical
  have hne : (Ico Q (Q + 2 * D)).Nonempty := nonempty_Ico.mpr (by omega)
  refine exists_le_of_sum_le hne ?_
  have hswap : ∑ n₀ ∈ Ico Q (Q + 2 * D), (S.filter fun d => antiCoherent d n₀).card =
      ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => antiCoherent d n₀).card := by
    simp only [card_filter]
    exact sum_comm
  have hd : ∀ d ∈ S, D ≤ 512 * ((Ico Q (Q + 2 * D)).filter fun n₀ => antiCoherent d n₀).card :=
    fun d hdS => by
      have h1 := card_filter_Ico_antiCoherent_ge (hS d hdS).1 Q (2 * D)
      have h2 : ((Ico Q (Q + 2 * D)).filter fun n₀ => antiCoherent d n₀).card =
          ((Ico Q (Q + 2 * D)).filter (antiCoherent d)).card := rfl
      have := (hS d hdS).2
      omega
  rw [← mul_sum, hswap, sum_const, Nat.card_Ico, smul_eq_mul, show Q + 2 * D - Q = 2 * D by omega]
  calc 2 * D * S.card = 2 * ∑ _d ∈ S, D := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ 2 * ∑ d ∈ S, 512 * ((Ico Q (Q + 2 * D)).filter fun n₀ => antiCoherent d n₀).card :=
        Nat.mul_le_mul_left _ (sum_le_sum hd)
    _ = 1024 * ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => antiCoherent d n₀).card := by
        rw [← mul_sum]; ring

/-- An anti-coherent window stays near the half: for `t < H`, `512 H ≤ d`,
`|((n₀ + t) mod d)/d - 1/2| ≤ 1/64`. -/
theorem near_half_of_antiCoherent {d n₀ t H : ℕ} (h₀ : antiCoherent d n₀) (ht : t < H)
    (hH : 512 * H ≤ d) : |(((n₀ + t) % d : ℕ) : ℝ) / d - 1 / 2| ≤ 1 / 64 := by
  obtain ⟨h1, h2⟩ := h₀
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : (n₀ + t) % d = n₀ % d + t := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : t < d), Nat.mod_eq_of_lt (by omega)]
  have e1 : (255 : ℝ) * d ≤ 512 * ((n₀ % d : ℕ) : ℝ) := by exact_mod_cast h1
  have e2 : (512 : ℝ) * ((n₀ % d : ℕ) : ℝ) ≤ 257 * d := by exact_mod_cast h2
  have e3 : (512 : ℝ) * t ≤ d := by
    have : 512 * t ≤ d := by omega
    exact_mod_cast this
  have e4 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hx : ((n₀ % d + t : ℕ) : ℝ) / d - 1 / 2 =
      (2 * ((n₀ % d : ℕ) : ℝ) + 2 * t - d) / (2 * d) := by
    push_cast; field_simp
  rw [hmod, hx, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * d), div_le_iff₀ (by positivity),
    abs_le]
  constructor <;> linarith

/-! ## §2. The sign of the kernel on coherent and anti-coherent windows -/

/-- On an anti-coherent window of length `H`, `512 H ≤ d`: `𝔅(d, n) ≤ -d²/100`. -/
theorem bernoulliKernel_le_of_antiCoherent {d n₀ n H : ℕ} (h₀ : antiCoherent d n₀)
    (hn : n ∈ Ico n₀ (n₀ + H)) (hH : 512 * H ≤ d) : bernoulliKernel d n ≤ -((d : ℝ) ^ 2 / 100) := by
  have hw := mem_Ico.mp hn
  have h := near_half_of_antiCoherent (t := n - n₀) h₀ (by omega) hH
  rw [show n₀ + (n - n₀) = n by omega] at h
  exact bernoulliKernel_le_of_near_half (by omega) h

/-- On a coherent window of length `H`, `64 H ≤ d`: `𝔅(d, n) ≥ d²/100`. -/
theorem bernoulliKernel_ge_of_coherent {d n₀ n H : ℕ} (h₀ : 64 * (n₀ % d) ≤ d)
    (hn : n ∈ Ico n₀ (n₀ + H)) (hH : 64 * H ≤ d) : (d : ℝ) ^ 2 / 100 ≤ bernoulliKernel d n := by
  have hw := mem_Ico.mp hn
  have h32 : 32 * (n % d) ≤ d := by
    have := mod_add_coherent (t := n - n₀) h₀ (by omega) hH
    rwa [show n₀ + (n - n₀) = n by omega] at this
  have hK := bernoulliKernel_ge (by omega : 0 < d) h32
  have hdR : (64 : ℝ) ≤ d := by exact_mod_cast (by omega : 64 ≤ d)
  nlinarith

/-! ## §3. The three-window lower bound -/

/-- **The three-window lower bound.** Let every `d ∈ S` satisfy `512 H ≤ d ≤ D`, be coherent for `n₁`
and anti-coherent for `n₂` and `n₃`, with `0 < D`, `1 ≤ H`, `150 D ≤ n₂ ≤ n₁, n₃`. For nonnegative rows
`c` on `S` and `cᵢ` on `[nᵢ, nᵢ + H)` and `a₂, a₃ ≥ 0`, the row `c' = c₁ - a₂ c₂ - a₃ c₃` has
`B(c, c') + m(c) R(c') + β(c) H(c') ≥ (1/200)(Σ_d c(d) d)(Σ_n |c'(n)|/n²)`. -/
theorem three_window_lower_bound {N D H n₁ n₂ n₃ : ℕ} {S : Finset ℕ} {c c₁ c₂ c₃ : ℕ → ℝ}
    {a₂ a₃ : ℝ} (hH : 1 ≤ H) (hD0 : 0 < D)
    (hS : ∀ d ∈ S, 512 * H ≤ d ∧ d ≤ D ∧ 64 * (n₁ % d) ≤ d ∧ antiCoherent d n₂ ∧ antiCoherent d n₃)
    (hD : 150 * D ≤ n₂) (h21 : n₂ ≤ n₁) (h23 : n₂ ≤ n₃)
    (hc : ∀ d, c d ≠ 0 → d ∈ S) (hc0 : ∀ d, 0 ≤ c d)
    (hc₁ : ∀ n, c₁ n ≠ 0 → n ∈ Ico n₁ (n₁ + H)) (hc₁0 : ∀ n, 0 ≤ c₁ n)
    (hc₂ : ∀ n, c₂ n ≠ 0 → n ∈ Ico n₂ (n₂ + H)) (hc₂0 : ∀ n, 0 ≤ c₂ n)
    (hc₃ : ∀ n, c₃ n ≠ 0 → n ∈ Ico n₃ (n₃ + H)) (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) :
    1 / 200 * (∑ d ∈ Icc 1 N, c d * d) *
        ∑ n ∈ Icc 1 N, |c₁ n - a₂ * c₂ n - a₃ * c₃ n| / (n : ℝ) ^ 2 ≤
      rowBilinear N c (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) +
        rowMean N c * vonMangoldtReadout N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) +
        rowBeta N c * finiteHarmonicSum N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) := by
  set c' : ℕ → ℝ := fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n
  set g : ℕ → ℝ := fun n => c₁ n + a₂ * c₂ n + a₃ * c₃ n
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set A := ∑ d ∈ Icc 1 N, c d * d
  set M := ∑ n ∈ Icc 1 N, g n / (n : ℝ) ^ 2
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    have := mul_nonneg ha₂ (hc₂0 n); have := mul_nonneg ha₃ (hc₃0 n); have := hc₁0 n
    simp only [g]; linarith
  have hA : 0 ≤ A := sum_nonneg fun d _ => mul_nonneg (hc0 d) (Nat.cast_nonneg _)
  have hM : 0 ≤ M := sum_nonneg fun n _ => div_nonneg (hg0 n) (by positivity)
  have habs : ∀ n, |c' n| ≤ g n := fun n => by
    have := mul_nonneg ha₂ (hc₂0 n); have := mul_nonneg ha₃ (hc₃0 n); have := hc₁0 n
    simp only [c', g]
    rw [abs_le]; constructor <;> linarith
  -- the kernel term is at least `A M / 100`
  have hmain : 1 / 100 * (A * M) ≤
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2) := by
    rw [show A * M = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, g n * c d * d / (n : ℝ) ^ 2 by
      rw [mul_comm, sum_mul_sum]
      exact sum_congr rfl fun n _ => sum_congr rfl fun d _ => by ring, mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mul_sum]
    refine sum_le_sum fun d _ => ?_
    by_cases hcd : c d = 0
    · simp [hcd]
    obtain ⟨hHd, -, hcoh, hanti₂, hanti₃⟩ := hS d (hc d hcd)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    set K := bernoulliKernel d n
    have k₁ : c₁ n * ((d : ℝ) ^ 2 / 100) ≤ c₁ n * K := by
      by_cases h : c₁ n = 0
      · simp [h]
      exact mul_le_mul_of_nonneg_left
        (bernoulliKernel_ge_of_coherent hcoh (hc₁ n h) (by omega)) (hc₁0 n)
    have k₂ : a₂ * c₂ n * ((d : ℝ) ^ 2 / 100) ≤ -(a₂ * c₂ n * K) := by
      by_cases h : c₂ n = 0
      · simp [h]
      have := mul_le_mul_of_nonneg_left (bernoulliKernel_le_of_antiCoherent hanti₂ (hc₂ n h) hHd)
        (mul_nonneg ha₂ (hc₂0 n))
      linarith
    have k₃ : a₃ * c₃ n * ((d : ℝ) ^ 2 / 100) ≤ -(a₃ * c₃ n * K) := by
      by_cases h : c₃ n = 0
      · simp [h]
      have := mul_le_mul_of_nonneg_left (bernoulliKernel_le_of_antiCoherent hanti₃ (hc₃ n h) hHd)
        (mul_nonneg ha₃ (hc₃0 n))
      linarith
    have hfac : 0 ≤ c d / d / (n : ℝ) ^ 2 := div_nonneg (div_nonneg (hc0 d) hd0.le) (by positivity)
    have key : g n * ((d : ℝ) ^ 2 / 100) ≤ c' n * K := by simp only [g, c']; linarith
    calc 1 / 100 * (g n * c d * d / (n : ℝ) ^ 2)
        = c d / d / (n : ℝ) ^ 2 * (g n * ((d : ℝ) ^ 2 / 100)) := by field_simp
      _ ≤ c d / d / (n : ℝ) ^ 2 * (c' n * K) := mul_le_mul_of_nonneg_left key hfac
      _ = c' n * (c d / d) * (K / (n : ℝ) ^ 2) := by ring
  -- the error is at most `A M / 200`
  have herr : 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 ≤
      1 / 200 * (A * M) := by
    have h1 : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 ≤ D * A := by
      rw [mul_sum]
      refine sum_le_sum fun d _ => ?_
      rw [abs_of_nonneg (hc0 d)]
      by_cases hcd : c d = 0
      · simp [hcd]
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast (hS d (hc d hcd)).2.1
      have hmul := mul_le_mul_of_nonneg_left hdD (mul_nonneg (hc0 d) (Nat.cast_nonneg d))
      calc c d * (d : ℝ) ^ 2 = c d * d * d := by ring
        _ ≤ c d * d * D := hmul
        _ = D * (c d * d) := by ring
    have hn₂pos : (0 : ℝ) < n₂ := by exact_mod_cast (by omega : 0 < n₂)
    have h2 : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 ≤ M / n₂ := by
      rw [div_eq_mul_inv M, sum_mul]
      refine sum_le_sum fun n hn => ?_
      have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      by_cases hgn : g n = 0
      · have : c' n = 0 := abs_nonpos_iff.mp (hgn ▸ habs n)
        simp [this, hgn]
      have hn₂ : (n₂ : ℝ) ≤ n := by
        have : n₂ ≤ n := by
          by_cases h1 : c₁ n = 0
          · by_cases h2 : c₂ n = 0
            · by_cases h3 : c₃ n = 0
              · exact absurd (by simp [g, h1, h2, h3]) hgn
              · have := mem_Ico.mp (hc₃ n h3); omega
            · have := mem_Ico.mp (hc₂ n h2); omega
          · have := mem_Ico.mp (hc₁ n h1); omega
        exact_mod_cast this
      calc |c' n| / (n : ℝ) ^ 3 ≤ g n / (n : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right (habs n) (by positivity)
        _ = g n / (n : ℝ) ^ 2 * (n : ℝ)⁻¹ := by field_simp
        _ ≤ g n / (n : ℝ) ^ 2 * (n₂ : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hn₂pos hn₂) (div_nonneg (hg0 n) (by positivity))
    have hDn : (150 : ℝ) * D ≤ n₂ := by exact_mod_cast hD
    have hsum1 : 0 ≤ ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2 := sum_nonneg fun d _ => by positivity
    calc 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3
        ≤ 3 / 4 * (D * A) * (M / n₂) := by gcongr
      _ = 3 / 4 * (D / n₂) * (A * M) := by ring
      _ ≤ 1 / 200 * (A * M) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hA hM)
          have : (D : ℝ) / n₂ ≤ 1 / 150 := by
            rw [div_le_iff₀ hn₂pos]; linarith
          linarith
  have hlow := (abs_le.mp hlaw).1
  have hMc : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 ≤ M :=
    sum_le_sum fun n _ => div_le_div_of_nonneg_right (habs n) (by positivity)
  have : 1 / 200 * A * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 ≤ 1 / 200 * A * M :=
    mul_le_mul_of_nonneg_left hMc (by positivity)
  linarith

/-! ## §4. Killing both readouts -/

theorem finiteHarmonicSum_comb (N : ℕ) (c₁ c₂ c₃ : ℕ → ℝ) (a₂ a₃ : ℝ) :
    finiteHarmonicSum N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) =
      finiteHarmonicSum N c₁ - a₂ * finiteHarmonicSum N c₂ - a₃ * finiteHarmonicSum N c₃ := by
  simp only [finiteHarmonicSum]
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

theorem vonMangoldtReadout_comb (N : ℕ) (c₁ c₂ c₃ : ℕ → ℝ) (a₂ a₃ : ℝ) :
    vonMangoldtReadout N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) =
      vonMangoldtReadout N c₁ - a₂ * vonMangoldtReadout N c₂ - a₃ * vonMangoldtReadout N c₃ := by
  simp only [vonMangoldtReadout_eq_log_harmonic]
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- The readout is a weighted average of `log n`: a nonnegative row supported on `[a, ∞)`, `1 ≤ a`,
has `R(c) ≥ (log a) H(c)`. -/
theorem log_mul_harmonic_le_readout {N a : ℕ} {c : ℕ → ℝ} (ha : 1 ≤ a) (hc0 : ∀ n, 0 ≤ c n)
    (hc : ∀ n, c n ≠ 0 → a ≤ n) :
    Real.log a * finiteHarmonicSum N c ≤ vonMangoldtReadout N c := by
  rw [vonMangoldtReadout_eq_log_harmonic, finiteHarmonicSum, mul_sum]
  refine sum_le_sum fun n hn => ?_
  by_cases h : c n = 0
  · simp [h]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlog : Real.log a ≤ Real.log n := Real.log_le_log haR (by exact_mod_cast hc n h)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  calc Real.log a * (c n / n) ≤ Real.log n * (c n / n) :=
        mul_le_mul_of_nonneg_right hlog (div_nonneg (hc0 n) hnR.le)
    _ = c n * Real.log n / n := by ring

/-- A nonnegative row supported on `(0, b]` has `R(c) ≤ (log b) H(c)`. -/
theorem readout_le_log_mul_harmonic {N b : ℕ} {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hc : ∀ n, c n ≠ 0 → n ≤ b) :
    vonMangoldtReadout N c ≤ Real.log b * finiteHarmonicSum N c := by
  rw [vonMangoldtReadout_eq_log_harmonic, finiteHarmonicSum, mul_sum]
  refine sum_le_sum fun n hn => ?_
  by_cases h : c n = 0
  · simp [h]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hlog : Real.log n ≤ Real.log b := Real.log_le_log hnR (by exact_mod_cast hc n h)
  calc c n * Real.log n / n = Real.log n * (c n / n) := by ring
    _ ≤ Real.log b * (c n / n) := mul_le_mul_of_nonneg_right hlog (div_nonneg (hc0 n) hnR.le)

/-- **Killing both readouts.** Let `c₂` live below `n₁`, `c₁` in `[n₁, n₃]`, `c₃` above `n₃`, all
nonnegative, `1 ≤ n₁ < n₃`, and `H(c₂), H(c₃) > 0`. With `ℓᵢ = R(cᵢ)/H(cᵢ)` the coefficients
`a₂ = H₁(ℓ₃ - ℓ₁)/(H₂(ℓ₃ - ℓ₂))`, `a₃ = H₁(ℓ₁ - ℓ₂)/(H₃(ℓ₃ - ℓ₂))` are nonnegative and
`c₁ - a₂ c₂ - a₃ c₃` has `H = R = 0`. -/
theorem exists_readout_free_combination {N n₁ n₃ : ℕ} {c₁ c₂ c₃ : ℕ → ℝ} (h1 : 1 ≤ n₁)
    (h13 : n₁ < n₃) (hc₁0 : ∀ n, 0 ≤ c₁ n) (hc₂0 : ∀ n, 0 ≤ c₂ n) (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₁ : ∀ n, c₁ n ≠ 0 → n₁ ≤ n ∧ n ≤ n₃) (hc₂ : ∀ n, c₂ n ≠ 0 → n ≤ n₁)
    (hc₃ : ∀ n, c₃ n ≠ 0 → n₃ ≤ n)
    (hH₂ : 0 < finiteHarmonicSum N c₂) (hH₃ : 0 < finiteHarmonicSum N c₃) :
    ∃ a₂ a₃ : ℝ, 0 ≤ a₂ ∧ 0 ≤ a₃ ∧
      finiteHarmonicSum N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) = 0 ∧
      vonMangoldtReadout N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) = 0 := by
  have hH₁ : 0 ≤ finiteHarmonicSum N c₁ :=
    sum_nonneg fun n _ => div_nonneg (hc₁0 n) (Nat.cast_nonneg _)
  set H₁ := finiteHarmonicSum N c₁
  set H₂ := finiteHarmonicSum N c₂
  set H₃ := finiteHarmonicSum N c₃
  set R₁ := vonMangoldtReadout N c₁
  set R₂ := vonMangoldtReadout N c₂
  set R₃ := vonMangoldtReadout N c₃
  set L₁ := Real.log n₁
  set L₃ := Real.log n₃
  have e₂ : R₂ ≤ L₁ * H₂ := readout_le_log_mul_harmonic hc₂0 hc₂
  have e₁ : L₁ * H₁ ≤ R₁ := log_mul_harmonic_le_readout h1 hc₁0 fun n h => (hc₁ n h).1
  have e₁' : R₁ ≤ L₃ * H₁ := readout_le_log_mul_harmonic hc₁0 fun n h => (hc₁ n h).2
  have e₃ : L₃ * H₃ ≤ R₃ := log_mul_harmonic_le_readout (by omega) hc₃0 hc₃
  have hL : L₁ < L₃ := Real.log_lt_log (by exact_mod_cast h1) (by exact_mod_cast h13)
  set den := R₃ * H₂ - R₂ * H₃
  have hden : 0 < den := by
    have : (L₃ - L₁) * (H₂ * H₃) ≤ den := by
      have := mul_le_mul_of_nonneg_right e₃ hH₂.le
      have := mul_le_mul_of_nonneg_right e₂ hH₃.le
      simp only [den]; nlinarith
    have : 0 < (L₃ - L₁) * (H₂ * H₃) := mul_pos (by linarith) (mul_pos hH₂ hH₃)
    linarith
  refine ⟨(R₃ * H₁ - R₁ * H₃) / den, (R₁ * H₂ - R₂ * H₁) / den, ?_, ?_, ?_, ?_⟩
  · refine div_nonneg ?_ hden.le
    have := mul_le_mul_of_nonneg_right e₃ hH₁
    have := mul_le_mul_of_nonneg_right e₁' hH₃.le
    nlinarith
  · refine div_nonneg ?_ hden.le
    have := mul_le_mul_of_nonneg_right e₁ hH₂.le
    have := mul_le_mul_of_nonneg_right e₂ hH₁
    nlinarith
  · rw [finiteHarmonicSum_comb]
    field_simp
    simp only [den]; ring
  · rw [vonMangoldtReadout_comb]
    field_simp
    simp only [den]; ring

/-! ## §5. The barrier with both readouts killed -/

/-- **The Type-II barrier survives the rank-two side conditions.** For every set of moduli
`S ⊆ [512 H, D]`, `1 ≤ H`, `0 < D` and every `Q ≥ 150 D` there are heights
`Q ≤ n₂ < n₂ + H ≤ n₁ < n₁ + H ≤ n₃ < Q + 6D + 2H` and moduli `S' ⊆ S`, `|S| ≤ 2²⁷ |S'|`, such that for
all nonnegative rows `c` on `S'` and `cᵢ` on `[nᵢ, nᵢ + H)` with `H(c₂), H(c₃) > 0` some
`a₂, a₃ ≥ 0` give a large-scale row `c' = c₁ - a₂ c₂ - a₃ c₃` with `R(c') = H(c') = 0` and
`B(c, c') ≥ (1/200)(Σ_d c(d) d)(Σ_n |c'(n)|/n²)`. -/
theorem exists_readout_free_barrier {S : Finset ℕ} {D H Q : ℕ} (hH : 1 ≤ H) (hD0 : 0 < D)
    (hS : ∀ d ∈ S, 512 * H ≤ d ∧ d ≤ D) (hQ : 150 * D ≤ Q) :
    ∃ n₁ n₂ n₃ : ℕ, Q ≤ n₂ ∧ n₂ + H ≤ n₁ ∧ n₁ + H ≤ n₃ ∧ n₃ < Q + 6 * D + 2 * H ∧
      ∃ S' ⊆ S, S.card ≤ 2 ^ 27 * S'.card ∧
        ∀ (N : ℕ) (c c₁ c₂ c₃ : ℕ → ℝ), (∀ d, c d ≠ 0 → d ∈ S') → (∀ d, 0 ≤ c d) →
          (∀ n, c₁ n ≠ 0 → n ∈ Ico n₁ (n₁ + H)) → (∀ n, 0 ≤ c₁ n) →
          (∀ n, c₂ n ≠ 0 → n ∈ Ico n₂ (n₂ + H)) → (∀ n, 0 ≤ c₂ n) →
          (∀ n, c₃ n ≠ 0 → n ∈ Ico n₃ (n₃ + H)) → (∀ n, 0 ≤ c₃ n) →
          0 < finiteHarmonicSum N c₂ → 0 < finiteHarmonicSum N c₃ →
          ∃ a₂ a₃ : ℝ, 0 ≤ a₂ ∧ 0 ≤ a₃ ∧
            finiteHarmonicSum N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) = 0 ∧
            vonMangoldtReadout N (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) = 0 ∧
            1 / 200 * (∑ d ∈ Icc 1 N, c d * d) *
                ∑ n ∈ Icc 1 N, |c₁ n - a₂ * c₂ n - a₃ * c₃ n| / (n : ℝ) ^ 2 ≤
              rowBilinear N c (fun n => c₁ n - a₂ * c₂ n - a₃ * c₃ n) := by
  classical
  have h512 : ∀ d ∈ S, 512 ≤ d := fun d hd => by have := (hS d hd).1; omega
  -- coherent window in the middle
  obtain ⟨n₁, hn₁, hcard₁⟩ := exists_coherent_shift hD0
    (fun d hd => ⟨by have := h512 d hd; omega, (hS d hd).2⟩) (Q + 2 * D + H)
  set S₁ := S.filter fun d => 64 * (n₁ % d) ≤ d
  -- anti-coherent window below
  obtain ⟨n₂, hn₂, hcard₂⟩ := exists_antiCoherent_shift (S := S₁) hD0
    (fun d hd => ⟨h512 d (mem_filter.mp hd).1, (hS d (mem_filter.mp hd).1).2⟩) Q
  set S₂ := S₁.filter fun d => antiCoherent d n₂
  -- anti-coherent window above
  obtain ⟨n₃, hn₃, hcard₃⟩ := exists_antiCoherent_shift (S := S₂) hD0
    (fun d hd => ⟨h512 d (mem_filter.mp (mem_filter.mp hd).1).1,
      (hS d (mem_filter.mp (mem_filter.mp hd).1).1).2⟩) (Q + 4 * D + 2 * H)
  set S₃ := S₂.filter fun d => antiCoherent d n₃
  have b₁ := mem_Ico.mp hn₁
  have b₂ := mem_Ico.mp hn₂
  have b₃ := mem_Ico.mp hn₃
  refine ⟨n₁, n₂, n₃, by omega, by omega, by omega, by omega, S₃,
    fun d hd => (mem_filter.mp (mem_filter.mp (mem_filter.mp hd).1).1).1, ?_, ?_⟩
  · calc S.card ≤ 128 * S₁.card := hcard₁
      _ ≤ 128 * (1024 * S₂.card) := Nat.mul_le_mul_left _ hcard₂
      _ ≤ 128 * (1024 * (1024 * S₃.card)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcard₃)
      _ = 2 ^ 27 * S₃.card := by ring
  intro N c c₁ c₂ c₃ hc hc0 hc₁ hc₁0 hc₂ hc₂0 hc₃ hc₃0 hH₂ hH₃
  obtain ⟨a₂, a₃, ha₂, ha₃, hHz, hRz⟩ := exists_readout_free_combination (N := N) (n₁ := n₁)
    (n₃ := n₃) (by omega) (by omega) hc₁0 hc₂0 hc₃0
    (fun n h => by have := mem_Ico.mp (hc₁ n h); omega)
    (fun n h => by have := mem_Ico.mp (hc₂ n h); omega)
    (fun n h => (mem_Ico.mp (hc₃ n h)).1) hH₂ hH₃
  refine ⟨a₂, a₃, ha₂, ha₃, hHz, hRz, ?_⟩
  have hS₃ : ∀ d ∈ S₃, 512 * H ≤ d ∧ d ≤ D ∧ 64 * (n₁ % d) ≤ d ∧ antiCoherent d n₂ ∧
      antiCoherent d n₃ := fun d hd => by
    obtain ⟨hd₂, h₃⟩ := mem_filter.mp hd
    obtain ⟨hd₁, h₂⟩ := mem_filter.mp hd₂
    obtain ⟨hd₀, h₁⟩ := mem_filter.mp hd₁
    exact ⟨(hS d hd₀).1, (hS d hd₀).2, h₁, h₂, h₃⟩
  have h := three_window_lower_bound (N := N) hH hD0 hS₃ (by omega) (by omega) (by omega) hc hc0
    hc₁ hc₁0 hc₂ hc₂0 hc₃ hc₃0 ha₂ ha₃
  rw [hRz, hHz, mul_zero, mul_zero, add_zero, add_zero] at h
  exact h

end

end GaloisForLFunctions.BezoutValuationIncidence
