import GaloisForLFunctions.RHTower.WeilLagSubexponentialExcursionBlind

/-!
# Fejér-block excursions: the Paley–Wiener threshold is sharp

A Fejér-block configuration has lag function `Φ(t) = Σ_b (a_b(t)/2)(F_b(t) − 1)`, where
`a_b(t) = c_b e^{δ_b t}` is the level of block `b`, `F_b(t) = K_b^{−1}|Σ_{k<K_b} e^{ikω_b t}|²` its
Fejér kernel, and `c_b K_b` its mass. `exists_configuration_excursion_le` builds such configurations
whose excursion set `{Φ > 0}` meets `[k, k+1)` in measure at most `e^{−f(k)k}` whenever `f` decreases
and `Σ_b f(2^b) < ∞`.

**Theorem** (`FejerData.Admissible.summable_of_excursion_le`). Conversely, take an admissible
configuration: positive levels, rates in `[0, Θ]`, frequencies at least `ω₀ > 0`, finite mass, and
`Σ_b 1/K_b ≤ e^{−ΘL}/8`, where `ω₀ L ≥ 12π`. If `f ≥ 0` decreases and the excursions satisfy
`|{Φ > 0} ∩ [k, k+1)| ≤ e^{−f(k)k}` eventually, then `Σ_b f(2^b) < ∞`. So for Fejér blocks the
Paley–Wiener condition `∫ f(t) dt/t < ∞` is exactly the threshold for thin excursions.

**Mechanism.**
* *Visibility* (`FejerData.Admissible.volume_core_ge`). A block whose peak `a_b K_b` exceeds
  `4e^{ΘL}` times the total level `A = Σ a` is positive on its spike windows of width
  `2/(K_b ω_b)`. These fill a proportion `1/(2πK_b)` of any window of length `L`. So under thin
  excursions every block with `K_b < e^E/(2π)` is suppressed, and the sharp blocks carry half of the
  level (`FejerData.Admissible.half_le_levelAbove`).
* *Level budget* (`LevelBudget.sum_div_two_pow_le`). If at `T = 2^k` the blocks with `K ≥ e^{F_k}`
  carry a fraction `η` of the level, then:
  - by Markov, their level at time `0` is at most `e^{−F_k} Σ cK`;
  - by Cauchy–Schwarz in time, `A_κ(T)² ≤ A_κ(0) A_κ(2T)`;
  - hence `F_k ≤ log A(2T) − 2 log A(T) + log(Σ cK/η²)`.

  Divided by `2^k` the right side telescopes, so `Σ_k F_k/2^k ≤ 2Θ + C`. Sharpness costs mass at a
  fixed level, and the finite mass and bounded rates pay for it at the Paley–Wiener rate.
-/

open MeasureTheory Set Complex Filter

noncomputable section

namespace RHTower

namespace LevelBudget

variable {ι : Type*} {c K δ : ι → ℝ}

noncomputable def level (c δ : ι → ℝ) (t : ℝ) : ℝ := ∑' i, c i * Real.exp (δ i * t)

noncomputable def levelAbove (c K δ : ι → ℝ) (κ t : ℝ) : ℝ :=
  ∑' i, Set.indicator {i | κ ≤ K i} (fun i => c i * Real.exp (δ i * t)) i

section

variable (hc : ∀ i, 0 < c i) (hK : ∀ i, 1 ≤ K i) (hcK : Summable fun i => c i * K i)
  {Θ : ℝ} (hδΘ : ∀ i, δ i ≤ Θ)
include hc hK hcK hδΘ

theorem summable_level_term {t : ℝ} (ht : 0 ≤ t) :
    Summable fun i => c i * Real.exp (δ i * t) := by
  refine Summable.of_nonneg_of_le (fun i => (mul_pos (hc i) (Real.exp_pos _)).le) (fun i => ?_)
    (hcK.mul_right (Real.exp (Θ * t)))
  have h1 : Real.exp (δ i * t) ≤ Real.exp (Θ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hδΘ i) ht)
  have h2 : c i ≤ c i * K i := le_mul_of_one_le_right (hc i).le (hK i)
  exact mul_le_mul h2 h1 (Real.exp_pos _).le ((hc i).le.trans h2)

theorem level_le_exp {t : ℝ} (ht : 0 ≤ t) : level c δ t ≤ level c δ 0 * Real.exp (Θ * t) := by
  unfold level
  rw [← tsum_mul_right]
  refine (summable_level_term hc hK hcK hδΘ ht).tsum_le_tsum (fun i => ?_)
    ((summable_level_term hc hK hcK hδΘ le_rfl).mul_right _)
  rw [mul_zero, Real.exp_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hδΘ i) ht))
    (hc i).le

theorem level_pos [Nonempty ι] {t : ℝ} (ht : 0 ≤ t) : 0 < level c δ t :=
  (summable_level_term hc hK hcK hδΘ ht).tsum_pos (fun i => (mul_pos (hc i) (Real.exp_pos _)).le)
    (Classical.arbitrary ι) (mul_pos (hc _) (Real.exp_pos _))

theorem summable_levelAbove_term (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun i => Set.indicator {i | κ ≤ K i} (fun i => c i * Real.exp (δ i * t)) i :=
  (summable_level_term hc hK hcK hδΘ ht).indicator _

omit hK hcK hδΘ in
theorem levelAbove_nonneg (κ t : ℝ) : 0 ≤ levelAbove c K δ κ t :=
  tsum_nonneg fun i => Set.indicator_nonneg (fun i _ => (mul_pos (hc i) (Real.exp_pos _)).le) i

theorem levelAbove_le_level (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) : levelAbove c K δ κ t ≤ level c δ t :=
  (summable_levelAbove_term hc hK hcK hδΘ κ ht).tsum_le_tsum
    (fun i => Set.indicator_le_self' (fun i _ => (mul_pos (hc i) (Real.exp_pos _)).le) i)
    (summable_level_term hc hK hcK hδΘ ht)

/-- **Markov.** The blocks with `K ≥ κ` carry level at most `Σ cK/κ` at time `0`. -/
theorem levelAbove_zero_le {κ : ℝ} (hκ : 0 < κ) :
    levelAbove c K δ κ 0 ≤ (∑' i, c i * K i) / κ := by
  unfold levelAbove
  rw [div_eq_mul_inv, ← tsum_mul_right]
  refine (summable_levelAbove_term hc hK hcK hδΘ κ le_rfl).tsum_le_tsum (fun i => ?_)
    (hcK.mul_right _)
  by_cases hi : κ ≤ K i
  · rw [Set.indicator_of_mem (show i ∈ {i | κ ≤ K i} from hi), mul_zero, Real.exp_zero, mul_one,
      mul_assoc, ← div_eq_mul_inv]
    exact le_mul_of_one_le_right (hc i).le ((one_le_div hκ).mpr hi)
  · rw [Set.indicator_of_notMem (show i ∉ {i | κ ≤ K i} from hi)]
    exact mul_nonneg (mul_nonneg (hc i).le (le_trans zero_le_one (hK i))) (inv_nonneg.mpr hκ.le)

/-- **Cauchy–Schwarz in time.** `A_κ(T)² ≤ A_κ(0) A_κ(2T)`. -/
theorem levelAbove_sq_le (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    levelAbove c K δ κ T ^ 2 ≤ levelAbove c K δ κ 0 * levelAbove c K δ κ (2 * T) := by
  have ha := levelAbove_nonneg hc (K := K) (δ := δ) κ 0
  have hb := levelAbove_nonneg hc (K := K) (δ := δ) κ T
  have hd := levelAbove_nonneg hc (K := K) (δ := δ) κ (2 * T)
  -- `2b ≤ λ a + d/λ` for every `λ > 0`
  have key : ∀ l : ℝ, 0 < l → 2 * levelAbove c K δ κ T ≤
      l * levelAbove c K δ κ 0 + levelAbove c K δ κ (2 * T) / l := by
    intro l hl
    have hs0 := summable_levelAbove_term hc hK hcK hδΘ κ (t := 0) le_rfl
    have hsT := summable_levelAbove_term hc hK hcK hδΘ κ hT
    have hs2 := summable_levelAbove_term hc hK hcK hδΘ κ (t := 2 * T) (by linarith)
    unfold levelAbove
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_div_const,
      ← (hs0.mul_left l).tsum_add (hs2.div_const l)]
    refine (hsT.mul_left 2).tsum_le_tsum (fun i => ?_) ((hs0.mul_left l).add (hs2.div_const l))
    by_cases hi : κ ≤ K i
    · simp only [Set.indicator_of_mem (show i ∈ {i | κ ≤ K i} from hi), mul_zero, Real.exp_zero,
        mul_one]
      have h2 : Real.exp (δ i * (2 * T)) = Real.exp (δ i * T) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      rw [h2]
      have hci := (hc i).le
      have hsq : 0 ≤ c i * l⁻¹ * (l - Real.exp (δ i * T)) ^ 2 :=
        mul_nonneg (mul_nonneg hci (inv_nonneg.mpr hl.le)) (sq_nonneg _)
      have hexp : c i * l⁻¹ * (l - Real.exp (δ i * T)) ^ 2 =
          l * c i + c i * Real.exp (δ i * T) ^ 2 / l - 2 * (c i * Real.exp (δ i * T)) := by
        field_simp; ring
      linarith
    · simp only [Set.indicator_of_notMem (show i ∉ {i | κ ≤ K i} from hi), mul_zero, zero_div,
        add_zero, le_refl]
  generalize levelAbove c K δ κ 0 = a at ha key ⊢
  generalize levelAbove c K δ κ T = b at hb key ⊢
  generalize levelAbove c K δ κ (2 * T) = d at hd key ⊢
  rcases hb.lt_or_eq with hbpos | hb0
  · rcases ha.lt_or_eq with hapos | ha0
    · have h := key (b / a) (div_pos hbpos hapos)
      have e1 : b / a * a = b := div_mul_cancel₀ b hapos.ne'
      have e2 : d / (b / a) = d * a / b := by field_simp
      rw [e1, e2] at h
      have h3 : b ≤ d * a / b := by linarith
      rw [le_div_iff₀ hbpos] at h3
      nlinarith
    · exfalso
      have h := key (d / b + 1) (by positivity)
      rw [← ha0, mul_zero, zero_add] at h
      have hlt : d / (d / b + 1) < 2 * b := by
        rw [div_lt_iff₀ (by positivity)]
        have : d / b * b = d := div_mul_cancel₀ d hbpos.ne'
        nlinarith [div_nonneg hd hbpos.le]
      linarith
  · rw [← hb0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg ha hd

theorem level_mono (hδ0 : ∀ i, 0 ≤ δ i) {t : ℝ} (ht : 0 ≤ t) : level c δ 0 ≤ level c δ t :=
  (summable_level_term hc hK hcK hδΘ le_rfl).tsum_le_tsum
    (fun i => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      rw [mul_zero]; exact mul_nonneg (hδ0 i) ht)) (hc i).le)
    (summable_level_term hc hK hcK hδΘ ht)

omit hδΘ in
theorem tsum_mul_K_pos [Nonempty ι] : 0 < ∑' i, c i * K i :=
  hcK.tsum_pos (fun i => mul_nonneg (hc i).le (le_trans zero_le_one (hK i)))
    (Classical.arbitrary ι) (mul_pos (hc _) (lt_of_lt_of_le zero_lt_one (hK _)))

/-- **One dyadic step.** If the blocks with `K ≥ e^F` carry at least the fraction `η` of the level
at time `T`, then `F ≤ log Σ cK − 2 log η + log A(2T) − 2 log A(T)`. -/
theorem le_log_of_levelShare [Nonempty ι] {η F T : ℝ} (hη : 0 < η) (hT : 0 ≤ T)
    (hshare : η * level c δ T ≤ levelAbove c K δ (Real.exp F) T) :
    F ≤ Real.log (∑' i, c i * K i) - 2 * Real.log η + Real.log (level c δ (2 * T)) -
      2 * Real.log (level c δ T) := by
  have hL := level_pos hc hK hcK hδΘ hT
  have hL2 := level_pos hc hK hcK hδΘ (t := 2 * T) (by linarith)
  have hm := tsum_mul_K_pos hc hK hcK
  have h1 := levelAbove_sq_le hc hK hcK hδΘ (Real.exp F) hT
  have h2 := levelAbove_zero_le hc hK hcK hδΘ (Real.exp_pos F)
  have h3 := levelAbove_le_level hc hK hcK hδΘ (Real.exp F) (t := 2 * T) (by linarith)
  have hb0 : 0 ≤ η * level c δ T := (mul_pos hη hL).le
  have hsq : (η * level c δ T) ^ 2 ≤ (∑' i, c i * K i) / Real.exp F * level c δ (2 * T) :=
    calc (η * level c δ T) ^ 2 ≤ levelAbove c K δ (Real.exp F) T ^ 2 :=
          pow_le_pow_left₀ hb0 hshare 2
      _ ≤ levelAbove c K δ (Real.exp F) 0 * levelAbove c K δ (Real.exp F) (2 * T) := h1
      _ ≤ (∑' i, c i * K i) / Real.exp F * level c δ (2 * T) :=
          mul_le_mul h2 h3 (levelAbove_nonneg hc _ _) (div_nonneg hm.le (Real.exp_pos F).le)
  have hpos : 0 < (η * level c δ T) ^ 2 := by positivity
  have hlog := Real.log_le_log hpos hsq
  rw [Real.log_mul (div_pos hm (Real.exp_pos F)).ne' hL2.ne', Real.log_div hm.ne'
    (Real.exp_pos F).ne', Real.log_exp, Real.log_pow, Real.log_mul hη.ne' hL.ne'] at hlog
  push_cast at hlog
  linarith

/-- **The level budget.** Suppose that at every dyadic time `T = 2^k`, `k ≥ k₀`, the blocks with
`K ≥ e^{F_k}` carry at least the fraction `η` of the level `A(T) = Σ c e^{δT}`. If the rates lie in
`[0, Θ]` and the masses `Σ c K` are finite, then `Σ_k F_k / 2^k ≤ 2Θ + 4|log A(0)| + 2|log Σ cK − 2 log η|`.
-/
theorem sum_div_two_pow_le [Nonempty ι] {η : ℝ} (hη : 0 < η) (hδ0 : ∀ i, 0 ≤ δ i) {F : ℕ → ℝ}
    {k₀ : ℕ} (hshare : ∀ k, k₀ ≤ k →
      η * level c δ (2 ^ k) ≤ levelAbove c K δ (Real.exp (F k)) (2 ^ k)) (n : ℕ) :
    ∑ j ∈ Finset.range n, F (k₀ + j) / 2 ^ (k₀ + j) ≤
      2 * Θ + 4 * |Real.log (level c δ 0)| +
        2 * |Real.log (∑' i, c i * K i) - 2 * Real.log η| := by
  set C₁ := Real.log (∑' i, c i * K i) - 2 * Real.log η with hC₁
  set g : ℕ → ℝ := fun k => 2 * Real.log (level c δ (2 ^ k)) / 2 ^ k with hg
  have step : ∀ j, F (k₀ + j) / 2 ^ (k₀ + j) ≤
      C₁ / 2 ^ (k₀ + j) + (g (k₀ + j + 1) - g (k₀ + j)) := by
    intro j
    have hp : (0 : ℝ) < 2 ^ (k₀ + j) := by positivity
    have h := le_log_of_levelShare hc hK hcK hδΘ hη (T := 2 ^ (k₀ + j)) hp.le
      (hshare _ (by omega))
    have e2 : (2 : ℝ) * 2 ^ (k₀ + j) = 2 ^ (k₀ + j + 1) := by ring
    rw [e2] at h
    have e3 : g (k₀ + j + 1) = Real.log (level c δ (2 ^ (k₀ + j + 1))) / 2 ^ (k₀ + j) := by
      simp only [hg]; rw [pow_succ]; field_simp
    rw [e3, hg]
    simp only
    have e4 : C₁ / 2 ^ (k₀ + j) + (Real.log (level c δ (2 ^ (k₀ + j + 1))) / 2 ^ (k₀ + j) -
        2 * Real.log (level c δ (2 ^ (k₀ + j))) / 2 ^ (k₀ + j)) =
        (C₁ + Real.log (level c δ (2 ^ (k₀ + j + 1))) -
          2 * Real.log (level c δ (2 ^ (k₀ + j)))) / 2 ^ (k₀ + j) := by ring
    rw [e4]
    exact div_le_div_of_nonneg_right (by rw [hC₁]; linarith) hp.le
  have htel : ∑ j ∈ Finset.range n, (g (k₀ + j + 1) - g (k₀ + j)) = g (k₀ + n) - g k₀ := by
    have := Finset.sum_range_sub (fun j => g (k₀ + j)) n
    simpa [add_assoc] using this
  have hL0 := level_pos hc hK hcK hδΘ (t := 0) le_rfl
  have hgN : g (k₀ + n) ≤ 2 * |Real.log (level c δ 0)| + 2 * Θ := by
    have hp : (0 : ℝ) < 2 ^ (k₀ + n) := by positivity
    have hle := level_le_exp hc hK hcK hδΘ hp.le
    have hlog := Real.log_le_log (level_pos hc hK hcK hδΘ hp.le) hle
    rw [Real.log_mul hL0.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    simp only [hg]
    rw [div_le_iff₀ hp]
    have h1 : (1 : ℝ) ≤ 2 ^ (k₀ + n) := one_le_pow₀ (by norm_num)
    have h2 : Real.log (level c δ 0) ≤ |Real.log (level c δ 0)| := le_abs_self _
    have h3 : 0 ≤ |Real.log (level c δ 0)| := abs_nonneg _
    nlinarith
  have hg0 : -g k₀ ≤ 2 * |Real.log (level c δ 0)| := by
    have hp : (0 : ℝ) < 2 ^ k₀ := by positivity
    have hmono := level_mono hc hK hcK hδΘ hδ0 hp.le
    have hlog := Real.log_le_log hL0 hmono
    simp only [hg]
    rw [neg_le, le_div_iff₀ hp]
    have h1 : (1 : ℝ) ≤ 2 ^ k₀ := one_le_pow₀ (by norm_num)
    have h2 : -|Real.log (level c δ 0)| ≤ Real.log (level c δ 0) := neg_abs_le _
    have h3 : 0 ≤ |Real.log (level c δ 0)| := abs_nonneg _
    nlinarith
  have hgeo : ∑ j ∈ Finset.range n, C₁ / 2 ^ (k₀ + j) ≤ 2 * |C₁| := by
    calc ∑ j ∈ Finset.range n, C₁ / 2 ^ (k₀ + j)
        ≤ ∑ j ∈ Finset.range n, |C₁| * (1 / 2) ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hp : (0 : ℝ) < 2 ^ (k₀ + j) := by positivity
          have hpj : (2 : ℝ) ^ j ≤ 2 ^ (k₀ + j) := pow_le_pow_right₀ (by norm_num) (by omega)
          rw [one_div_pow, ← div_eq_mul_one_div]
          calc C₁ / 2 ^ (k₀ + j) ≤ |C₁| / 2 ^ (k₀ + j) :=
                div_le_div_of_nonneg_right (le_abs_self _) hp.le
            _ ≤ |C₁| / 2 ^ j := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hpj
      _ = |C₁| * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ |C₁| * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (abs_nonneg _)
      _ = 2 * |C₁| := by ring
  calc ∑ j ∈ Finset.range n, F (k₀ + j) / 2 ^ (k₀ + j)
      ≤ ∑ j ∈ Finset.range n, (C₁ / 2 ^ (k₀ + j) + (g (k₀ + j + 1) - g (k₀ + j))) :=
        Finset.sum_le_sum fun j _ => step j
    _ = ∑ j ∈ Finset.range n, C₁ / 2 ^ (k₀ + j) + (g (k₀ + n) - g k₀) := by
        rw [Finset.sum_add_distrib, htel]
    _ ≤ 2 * Θ + 4 * |Real.log (level c δ 0)| + 2 * |C₁| := by linarith

end

end LevelBudget

namespace SubexpExcursion

open RHTower.AlmostEverySpacing

/-- Admissible Fejér-block data: positive levels, rates in `[0, Θ]`, frequencies `≥ ω₀`, finite mass. -/
structure FejerData.Admissible (D : FejerData) (Θ ω₀ : ℝ) : Prop where
  K_pos : ∀ b, 1 ≤ D.K b
  c_pos : ∀ b, 0 < D.c b
  δ_nonneg : ∀ b, 0 ≤ D.δ b
  δ_le : ∀ b, D.δ b ≤ Θ
  ω_ge : ∀ b, ω₀ ≤ D.ω b
  sum_cK : Summable fun b => D.c b * D.K b

variable {D : FejerData} {Θ ω₀ : ℝ}

/-- Near a multiple of `2π`, the Dirichlet sum has real part at least `K/2`. -/
theorem re_dirSum_ge {K : ℕ} {θ : ℝ} {n : ℤ} (hθ : |θ - 2 * Real.pi * n| ≤ 1 / K) :
    (K : ℝ) / 2 ≤ (dirSum K θ).re := by
  unfold dirSum
  rw [Complex.re_sum]
  have hterm : ∀ k ∈ Finset.range K, (1 : ℝ) / 2 ≤ (cexp (I * ((k : ℝ) * θ : ℝ))).re := by
    intro k hk
    have hk' : (k : ℝ) < K := by exact_mod_cast Finset.mem_range.mp hk
    have hK0 : (0 : ℝ) < K := lt_of_le_of_lt (Nat.cast_nonneg k) hk'
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    have hper : Real.cos ((k : ℝ) * θ) = Real.cos ((k : ℝ) * (θ - 2 * Real.pi * n)) := by
      have : (k : ℝ) * θ = (k : ℝ) * (θ - 2 * Real.pi * n) + ((k : ℤ) * n : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hper]
    have hsmall : |(k : ℝ) * (θ - 2 * Real.pi * n)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      calc (k : ℝ) * |θ - 2 * Real.pi * n| ≤ K * (1 / K) :=
            mul_le_mul hk'.le hθ (abs_nonneg _) hK0.le
        _ = 1 := by field_simp
    have hc := Real.one_sub_sq_div_two_le_cos (x := (k : ℝ) * (θ - 2 * Real.pi * n))
    have hsq : ((k : ℝ) * (θ - 2 * Real.pi * n)) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((k : ℝ) * (θ - 2 * Real.pi * n))]
    linarith
  calc (K : ℝ) / 2 = ∑ _k ∈ Finset.range K, (1 : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

/-- Near a spike time the Fejér kernel is at least `K/4`. -/
theorem fej_ge_of_near (b : ℕ) (hK : 1 ≤ D.K b) {t : ℝ} {n : ℤ}
    (hn : |D.ω b * t - 2 * Real.pi * n| ≤ 1 / D.K b) : (D.K b : ℝ) / 4 ≤ fej D b t := by
  have hK0 : (0 : ℝ) < D.K b := by exact_mod_cast hK
  have hre := re_dirSum_ge (K := D.K b) hn
  have hnorm : (D.K b : ℝ) / 2 ≤ ‖dirSum (D.K b) (D.ω b * t)‖ :=
    hre.trans (Complex.re_le_norm _)
  unfold fej
  rw [le_div_iff₀ hK0]
  have h0 : 0 ≤ (D.K b : ℝ) / 2 := by positivity
  nlinarith [pow_le_pow_left₀ h0 hnorm 2]

/-! ## Amplitudes and the lag function -/

theorem FejerData.Admissible.summable_amp (hD : D.Admissible Θ ω₀) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => amp D b t := by
  refine Summable.of_nonneg_of_le (fun b => (mul_pos (hD.c_pos b) (Real.exp_pos _)).le)
    (fun b => ?_) (hD.sum_cK.mul_right (Real.exp (Θ * t)))
  have h1 : Real.exp (D.δ b * t) ≤ Real.exp (Θ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hD.δ_le b) ht)
  have hK1 : (1 : ℝ) ≤ D.K b := by exact_mod_cast hD.K_pos b
  have h2 : D.c b ≤ D.c b * D.K b := le_mul_of_one_le_right (hD.c_pos b).le hK1
  exact mul_le_mul h2 h1 (Real.exp_pos _).le ((hD.c_pos b).le.trans h2)

theorem FejerData.Admissible.summable_amp_mul_fej (hD : D.Admissible Θ ω₀) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => amp D b t * fej D b t := by
  refine Summable.of_nonneg_of_le
    (fun b => mul_nonneg (mul_pos (hD.c_pos b) (Real.exp_pos _)).le
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))) (fun b => ?_)
    (hD.sum_cK.mul_right (Real.exp (Θ * t)))
  have hK0 : (0 : ℝ) < D.K b := by exact_mod_cast hD.K_pos b
  have hf : fej D b t ≤ D.K b := by
    unfold fej
    rw [div_le_iff₀ hK0]
    have h := norm_dirSum_le (D.K b) (D.ω b * t)
    nlinarith [norm_nonneg (dirSum (D.K b) (D.ω b * t))]
  have h1 : Real.exp (D.δ b * t) ≤ Real.exp (Θ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hD.δ_le b) ht)
  calc amp D b t * fej D b t ≤ (D.c b * Real.exp (Θ * t)) * D.K b :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (hD.c_pos b).le) hf
          (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
          (mul_pos (hD.c_pos b) (Real.exp_pos _)).le
    _ = D.c b * D.K b * Real.exp (Θ * t) := by ring

/-- **One block against the others.** `Φ(t) ≥ a_b(t) F_b(t)/2 − A(t)/2`, `A = Σ a`. -/
theorem FejerData.Admissible.lag_ge (hD : D.Admissible Θ ω₀) (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    amp D b t * fej D b t / 2 - (∑' b', amp D b' t) / 2 ≤ lag D t := by
  classical
  have hA := hD.summable_amp ht
  have hAF := hD.summable_amp_mul_fej ht
  have hbv : Summable fun b' => blockVal D b' t := by
    have : (fun b' => blockVal D b' t) = fun b' => (amp D b' t * fej D b' t - amp D b' t) / 2 := by
      funext b'; unfold blockVal; ring
    rw [this]; exact (hAF.sub hA).div_const 2
  have hg : Summable fun b' => -(amp D b' t / 2) + if b' = b then amp D b t * fej D b t / 2 else 0 :=
    (hA.div_const 2).neg.add (summable_of_ne_finset_zero (s := {b}) (fun b' hb' => by
      rw [Finset.mem_singleton] at hb'; simp [hb']))
  have e : ∑' b', (-(amp D b' t / 2) + if b' = b then amp D b t * fej D b t / 2 else 0) =
      amp D b t * fej D b t / 2 - (∑' b', amp D b' t) / 2 := by
    rw [(hA.div_const 2).neg.tsum_add (summable_of_ne_finset_zero (s := {b}) (fun b' hb' => by
      rw [Finset.mem_singleton] at hb'; simp [hb'])), tsum_neg, tsum_div_const, tsum_ite_eq]
    ring
  rw [← e]
  unfold lag
  refine hg.tsum_le_tsum (fun b' => ?_) hbv
  have hf0 : 0 ≤ fej D b' t := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have ha0 : 0 ≤ amp D b' t := (mul_pos (hD.c_pos b') (Real.exp_pos _)).le
  unfold blockVal
  split_ifs with h
  · subst h; linarith
  · nlinarith

/-- `A(t) ≤ A(T) e^{Θ(t−T)}` for `0 ≤ T ≤ t`. -/
theorem FejerData.Admissible.tsum_amp_le (hD : D.Admissible Θ ω₀) {T t : ℝ} (hT : 0 ≤ T)
    (hTt : T ≤ t) : ∑' b, amp D b t ≤ (∑' b, amp D b T) * Real.exp (Θ * (t - T)) := by
  rw [← tsum_mul_right]
  refine (hD.summable_amp (hT.trans hTt)).tsum_le_tsum (fun b => ?_)
    ((hD.summable_amp hT).mul_right _)
  unfold amp
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hD.c_pos b).le
  have := mul_le_mul_of_nonneg_right (hD.δ_le b) (sub_nonneg.mpr hTt)
  nlinarith

theorem FejerData.Admissible.amp_mono (hD : D.Admissible Θ ω₀) (b : ℕ) {T t : ℝ} (hTt : T ≤ t) :
    amp D b T ≤ amp D b t :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hTt (hD.δ_nonneg b))) (hD.c_pos b).le

/-- **A visible block is positive at its spike times.** If `a_b(T) K_b > 4e^{ΘL} A(T)`, then
`Φ(t) > 0` for every `t ∈ [T, T + L]` within `1/(K_b ω_b)` of a spike `2πn/ω_b`. -/
theorem FejerData.Admissible.lag_pos_of_near (hD : D.Admissible Θ ω₀) {b : ℕ} {T L t : ℝ}
    (hT : 0 ≤ T) (hTt : T ≤ t) (htL : t ≤ T + L)
    (hvis : 4 * Real.exp (Θ * L) * ∑' b', amp D b' T < amp D b T * D.K b) {n : ℤ}
    (hn : |D.ω b * t - 2 * Real.pi * n| ≤ 1 / D.K b) : 0 < lag D t := by
  have ht : 0 ≤ t := hT.trans hTt
  have h1 := hD.lag_ge b ht
  have h2 := fej_ge_of_near b (hD.K_pos b) hn
  have h3 := hD.tsum_amp_le hT hTt
  have h4 := hD.amp_mono b hTt
  have hA0 : 0 ≤ ∑' b', amp D b' T :=
    tsum_nonneg fun b' => (mul_pos (hD.c_pos b') (Real.exp_pos _)).le
  have hK0 : (0 : ℝ) ≤ D.K b := Nat.cast_nonneg _
  have hΘ : 0 ≤ Θ := (hD.δ_nonneg 0).trans (hD.δ_le 0)
  have h5 : Real.exp (Θ * (t - T)) ≤ Real.exp (Θ * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hΘ)
  have hab0 : 0 ≤ amp D b T := (mul_pos (hD.c_pos b) (Real.exp_pos _)).le
  have h6 : amp D b T * (D.K b / 4) ≤ amp D b t * fej D b t :=
    mul_le_mul h4 h2 (by positivity) (hab0.trans h4)
  have h7 : (∑' b', amp D b' t) ≤ (∑' b', amp D b' T) * Real.exp (Θ * L) :=
    h3.trans (mul_le_mul_of_nonneg_left h5 hA0)
  nlinarith

/-- The spike window `[(2π(n₁+i) − ε)/ω, (2π(n₁+i) + ε)/ω]`. -/
def spikeWin (ω ε : ℝ) (n₁ : ℤ) (i : ℕ) : Set ℝ :=
  Icc ((2 * Real.pi * ((n₁ : ℝ) + i) - ε) / ω) ((2 * Real.pi * ((n₁ : ℝ) + i) + ε) / ω)

theorem pairwiseDisjoint_spikeWin {ω ε : ℝ} (hω : 0 < ω) (hε : ε ≤ 1) (n₁ : ℤ) (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (spikeWin ω ε n₁) := by
  intro i _ j _ hij
  rw [Function.onFun, Set.disjoint_left]
  intro t ht ht'
  obtain ⟨a1, a2⟩ := ht
  obtain ⟨b1, b2⟩ := ht'
  rw [div_le_iff₀ hω] at a1 b1
  rw [le_div_iff₀ hω] at a2 b2
  have hne : (1 : ℝ) ≤ |((i : ℝ) - j)| := by
    have : (i : ℤ) ≠ j := by exact_mod_cast hij
    have h := Int.one_le_abs (sub_ne_zero.mpr this)
    exact_mod_cast h
  have hπ := Real.pi_gt_three
  rcases le_abs.mp hne with h | h <;> nlinarith

theorem volume_spikeWin {ω ε : ℝ} (hω : 0 < ω) (n₁ : ℤ) (i : ℕ) :
    volume (spikeWin ω ε n₁ i) = ENNReal.ofReal (2 * ε / ω) := by
  rw [spikeWin, Real.volume_Icc]
  congr 1
  field_simp
  ring

/-- Count of spike windows: `M = ⌊x⌋₊ − 2` windows with `x/2 ≤ M ≤ x − 2` when `x ≥ 6`. -/
theorem floor_sub_two_bounds {x : ℝ} (hx : 6 ≤ x) :
    x / 2 ≤ ((⌊x⌋₊ - 2 : ℕ) : ℝ) ∧ ((⌊x⌋₊ - 2 : ℕ) : ℝ) ≤ x - 2 := by
  have hfl : 6 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hMr : ((⌊x⌋₊ - 2 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hMr]
  constructor
  · linarith [Nat.lt_floor_add_one x]
  · linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ x)]

/-- **The spike windows of a visible block fill a proportion `1/(2πK_b)` of `[T, T + L)`.** -/
theorem FejerData.Admissible.volume_core_ge (hD : D.Admissible Θ ω₀) {b : ℕ} {T L : ℝ}
    (hT : 0 ≤ T) (hL0 : 0 ≤ L) (hL : 12 * Real.pi ≤ D.ω b * L)
    (hvis : 4 * Real.exp (Θ * L) * ∑' b', amp D b' T < amp D b T * D.K b) :
    ENNReal.ofReal (L / (2 * Real.pi * D.K b)) ≤ volume (posSet D ∩ Ico T (T + L)) := by
  have hπ := Real.pi_gt_three
  have hK1 : (1 : ℝ) ≤ D.K b := by exact_mod_cast hD.K_pos b
  have hK0 : (0 : ℝ) < D.K b := by linarith
  have hω : 0 < D.ω b := by
    by_contra h
    push Not at h
    have : D.ω b * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hL0
    linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (D.K b : ℝ) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one hK0]; exact hK1
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℤ, n₁ = ⌈(D.ω b * T + 1) / (2 * Real.pi)⌉ := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = D.ω b * L / (2 * Real.pi) := ⟨_, rfl⟩
  have h3 : 2 * Real.pi * x = D.ω b * L := by rw [hxdef]; field_simp
  have hx6 : 6 ≤ x := by nlinarith
  obtain ⟨hMlo, hMhi⟩ := floor_sub_two_bounds hx6
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌊x⌋₊ - 2 := ⟨_, rfl⟩
  rw [← hMdef] at hMlo hMhi
  have hn₁lo : (D.ω b * T + 1) / (2 * Real.pi) ≤ n₁ := by rw [hn₁]; exact Int.le_ceil _
  have hn₁hi : (n₁ : ℝ) < (D.ω b * T + 1) / (2 * Real.pi) + 1 := by
    rw [hn₁]; exact Int.ceil_lt_add_one _
  have hlo2 : D.ω b * T + 1 ≤ 2 * Real.pi * n₁ := by
    rw [div_le_iff₀ (by positivity)] at hn₁lo; linarith
  have hhi2 : 2 * Real.pi * n₁ < D.ω b * T + 1 + 2 * Real.pi := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp (by linarith :
      (n₁ : ℝ) - 1 < (D.ω b * T + 1) / (2 * Real.pi))
    linarith
  -- each window lies in the excursion set
  have hsub : ∀ i ∈ Finset.range M, spikeWin (D.ω b) ε n₁ i ⊆ posSet D ∩ Ico T (T + L) := by
    intro i hi t ht
    have hiM : (i : ℝ) + 1 ≤ M := by
      have := Finset.mem_range.mp hi; exact_mod_cast this
    obtain ⟨ht1, ht2⟩ := ht
    rw [div_le_iff₀ hω] at ht1
    rw [le_div_iff₀ hω] at ht2
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hTt : T ≤ t := by
      have : D.ω b * T ≤ t * D.ω b := by nlinarith
      nlinarith
    have h5 : t * D.ω b < D.ω b * T + D.ω b * L := by nlinarith
    have htL : t < T + L := by
      have h4 : t * D.ω b < (T + L) * D.ω b := by linarith
      exact lt_of_mul_lt_mul_right h4 hω.le
    refine ⟨⟨hT.trans hTt, ?_⟩, hTt, htL⟩
    refine hD.lag_pos_of_near hT hTt htL.le hvis (n := n₁ + i) ?_
    rw [abs_le, ← hεdef]
    push_cast
    constructor <;> nlinarith
  have hmeas : ∀ i ∈ Finset.range M, MeasurableSet (spikeWin (D.ω b) ε n₁ i) :=
    fun i _ => measurableSet_Icc
  have hvol : volume (⋃ i ∈ Finset.range M, spikeWin (D.ω b) ε n₁ i) =
      M * ENNReal.ofReal (2 * ε / D.ω b) := by
    rw [measure_biUnion_finset (pairwiseDisjoint_spikeWin hω hε1 n₁ _) hmeas]
    rw [Finset.sum_congr rfl (fun i _ => volume_spikeWin hω n₁ i), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  calc ENNReal.ofReal (L / (2 * Real.pi * D.K b))
      ≤ ENNReal.ofReal (M * (2 * ε / D.ω b)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hεdef, div_le_iff₀ (by positivity)]
        have e : (M : ℝ) * (2 * (1 / (D.K b : ℝ)) / D.ω b) * (2 * Real.pi * D.K b) =
            4 * Real.pi * M / D.ω b := by
          field_simp; ring
        rw [e, le_div_iff₀ hω]
        nlinarith
    _ = M * ENNReal.ofReal (2 * ε / D.ω b) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = volume (⋃ i ∈ Finset.range M, spikeWin (D.ω b) ε n₁ i) := hvol.symm
    _ ≤ volume (posSet D ∩ Ico T (T + L)) := measure_mono (Set.iUnion₂_subset hsub)

/-- **Thinness over a window of `L` unit intervals.** -/
theorem volume_posSet_window_le {T L : ℕ} {E : ℝ}
    (hthin : ∀ j < L, volume (posSet D ∩ Ico ((T + j : ℕ) : ℝ) ((T + j : ℕ) + 1)) ≤
      ENNReal.ofReal (Real.exp (-E))) :
    volume (posSet D ∩ Ico (T : ℝ) (T + L)) ≤ ENNReal.ofReal (L * Real.exp (-E)) := by
  have hsub : posSet D ∩ Ico (T : ℝ) (T + L) ⊆
      ⋃ j ∈ Finset.range L, posSet D ∩ Ico ((T + j : ℕ) : ℝ) ((T + j : ℕ) + 1) := by
    rintro t ⟨hp, ht1, ht2⟩
    have h0 : (0 : ℝ) ≤ t - T := by linarith
    refine Set.mem_iUnion₂.mpr ⟨⌊t - T⌋₊, Finset.mem_range.mpr ?_, hp, ?_, ?_⟩
    · have := Nat.floor_lt h0 |>.mpr (by linarith : t - T < (L : ℝ)); exact this
    · push_cast; linarith [Nat.floor_le h0]
    · push_cast; linarith [Nat.lt_floor_add_one (t - T)]
  calc volume (posSet D ∩ Ico (T : ℝ) (T + L))
      ≤ ∑ j ∈ Finset.range L, volume (posSet D ∩ Ico ((T + j : ℕ) : ℝ) ((T + j : ℕ) + 1)) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _j ∈ Finset.range L, ENNReal.ofReal (Real.exp (-E)) :=
        Finset.sum_le_sum fun j hj => hthin j (Finset.mem_range.mp hj)
    _ = ENNReal.ofReal (L * Real.exp (-E)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **Blunt blocks are suppressed.** If the excursions on `[T, T + L)` have measure
`≤ L e^{−E}` and `K_b < e^E/(2π)`, then `a_b(T) K_b ≤ 4e^{ΘL} A(T)`. -/
theorem FejerData.Admissible.amp_mul_K_le (hD : D.Admissible Θ ω₀) (hω₀ : 0 < ω₀) {b T L : ℕ}
    (hL : 12 * Real.pi ≤ ω₀ * L) {E : ℝ}
    (hthin : ∀ j < L, volume (posSet D ∩ Ico ((T + j : ℕ) : ℝ) ((T + j : ℕ) + 1)) ≤
      ENNReal.ofReal (Real.exp (-E)))
    (hK : (D.K b : ℝ) < Real.exp E / (2 * Real.pi)) :
    amp D b T * D.K b ≤ 4 * Real.exp (Θ * L) * ∑' b', amp D b' T := by
  by_contra hvis
  push Not at hvis
  have hL0 : (0 : ℝ) < L := by
    by_contra h; push Not at h
    have : ω₀ * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hω₀.le h
    linarith [Real.pi_pos]
  have hωL : 12 * Real.pi ≤ D.ω b * L :=
    hL.trans (mul_le_mul_of_nonneg_right (hD.ω_ge b) hL0.le)
  have h1 := hD.volume_core_ge (Nat.cast_nonneg T) hL0.le hωL hvis
  have h2 := volume_posSet_window_le (D := D) hthin
  have h3 := h1.trans h2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have hK0 : (0 : ℝ) < D.K b := by exact_mod_cast hD.K_pos b
  rw [div_le_iff₀ (by positivity)] at h3
  have h4 : 1 ≤ Real.exp (-E) * (2 * Real.pi * D.K b) := by
    have : (L : ℝ) * 1 ≤ L * (Real.exp (-E) * (2 * Real.pi * D.K b)) := by nlinarith
    exact le_of_mul_le_mul_left this hL0
  rw [lt_div_iff₀ (by positivity)] at hK
  have h5 : Real.exp (-E) * Real.exp E = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos E, Real.exp_pos (-E)]

/-- **The sharp blocks carry half of the level.** -/
theorem FejerData.Admissible.half_le_levelAbove (hD : D.Admissible Θ ω₀) (hω₀ : 0 < ω₀) {T L : ℕ}
    (hL : 12 * Real.pi ≤ ω₀ * L) (hKs : Summable fun b => 1 / (D.K b : ℝ))
    (hKsum : ∑' b, 1 / (D.K b : ℝ) ≤ Real.exp (-(Θ * L)) / 8) {E : ℝ}
    (hthin : ∀ j < L, volume (posSet D ∩ Ico ((T + j : ℕ) : ℝ) ((T + j : ℕ) + 1)) ≤
      ENNReal.ofReal (Real.exp (-E))) :
    1 / 2 * ∑' b, amp D b T ≤
      ∑' b, Set.indicator {b | Real.exp (E - Real.log (2 * Real.pi)) ≤ (D.K b : ℝ)}
        (fun b => amp D b T) b := by
  classical
  set S : Set ℕ := {b | Real.exp (E - Real.log (2 * Real.pi)) ≤ (D.K b : ℝ)} with hS
  have hA := hD.summable_amp (t := T) (Nat.cast_nonneg T)
  have hsplit : ∑' b, amp D b T = ∑' b, S.indicator (fun b => amp D b T) b +
      ∑' b, Sᶜ.indicator (fun b => amp D b T) b := by
    rw [← (hA.indicator S).tsum_add (hA.indicator Sᶜ)]
    exact tsum_congr fun b => (Set.indicator_self_add_compl_apply S (fun b => amp D b T) b).symm
  have hexp : Real.exp (E - Real.log (2 * Real.pi)) = Real.exp E / (2 * Real.pi) := by
    rw [Real.exp_sub, Real.exp_log (by positivity)]
  have hA0 : 0 ≤ ∑' b, amp D b T :=
    tsum_nonneg fun b => (mul_pos (hD.c_pos b) (Real.exp_pos _)).le
  have hblunt : ∑' b, Sᶜ.indicator (fun b => amp D b T) b ≤
      (4 * Real.exp (Θ * L) * ∑' b, amp D b T) * ∑' b, 1 / (D.K b : ℝ) := by
    rw [← tsum_mul_left]
    refine (hA.indicator Sᶜ).tsum_le_tsum (fun b => ?_) (hKs.mul_left _)
    by_cases hb : b ∈ Sᶜ
    · rw [Set.indicator_of_mem hb]
      have hK : (D.K b : ℝ) < Real.exp E / (2 * Real.pi) := by
        rw [← hexp]; simpa [hS] using hb
      have h := hD.amp_mul_K_le hω₀ (b := b) hL hthin hK
      have hK0 : (0 : ℝ) < D.K b := by exact_mod_cast hD.K_pos b
      rw [mul_one_div, le_div_iff₀ hK0]
      exact h
    · rw [Set.indicator_of_notMem hb]
      exact mul_nonneg (by positivity) (div_nonneg zero_le_one (Nat.cast_nonneg _))
  generalize ∑' b, amp D b T = A at hsplit hA0 hblunt ⊢
  have he : Real.exp (Θ * L) * Real.exp (-(Θ * L)) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 ≤ 4 * Real.exp (Θ * L) * A := by positivity
  have hsmall : (4 * Real.exp (Θ * L) * A) * ∑' b, 1 / (D.K b : ℝ) ≤ 1 / 2 * A :=
    calc (4 * Real.exp (Θ * L) * A) * ∑' b, 1 / (D.K b : ℝ)
        ≤ (4 * Real.exp (Θ * L) * A) * (Real.exp (-(Θ * L)) / 8) :=
          mul_le_mul_of_nonneg_left hKsum hpos
      _ = 1 / 2 * A * (Real.exp (Θ * L) * Real.exp (-(Θ * L))) := by ring
      _ = 1 / 2 * A := by rw [he, mul_one]
  linarith

/-! ## The converse -/

/-- **Fejér-block excursions obey the level budget.** -/
theorem FejerData.Admissible.sum_excursion_le (hD : D.Admissible Θ ω₀) (hω₀ : 0 < ω₀) {L : ℕ}
    (hL : 12 * Real.pi ≤ ω₀ * L) (hKs : Summable fun b => 1 / (D.K b : ℝ))
    (hKsum : ∑' b, 1 / (D.K b : ℝ) ≤ Real.exp (-(Θ * L)) / 8) {E : ℕ → ℝ} {k₀ : ℕ}
    (hthin : ∀ k, k₀ ≤ k → ∀ j < L,
      volume (posSet D ∩ Ico ((2 ^ k + j : ℕ) : ℝ) ((2 ^ k + j : ℕ) + 1)) ≤
        ENNReal.ofReal (Real.exp (-E k)))
    (n : ℕ) :
    ∑ j ∈ Finset.range n, (E (k₀ + j) - Real.log (2 * Real.pi)) / 2 ^ (k₀ + j) ≤
      2 * Θ + 4 * |Real.log (∑' b, D.c b)| +
        2 * |Real.log (∑' b, D.c b * D.K b) - 2 * Real.log (1 / 2)| := by
  have hK1 : ∀ b, (1 : ℝ) ≤ (D.K b : ℝ) := fun b => by exact_mod_cast hD.K_pos b
  have h := LevelBudget.sum_div_two_pow_le (c := D.c) (K := fun b => (D.K b : ℝ)) (δ := D.δ)
    hD.c_pos hK1 hD.sum_cK hD.δ_le (η := 1 / 2) (by norm_num) hD.δ_nonneg
    (F := fun k => E k - Real.log (2 * Real.pi)) (k₀ := k₀) (fun k hk => by
      have hk' := hD.half_le_levelAbove hω₀ (T := 2 ^ k) hL hKs hKsum (E := E k) (hthin k hk)
      simpa [LevelBudget.level, LevelBudget.levelAbove, amp] using hk') n
  simpa [LevelBudget.level] using h

/-- **The Paley–Wiener converse for Fejér blocks.** If `f ≥ 0` decreases and the excursions of an
admissible configuration satisfy `|{Φ > 0} ∩ [k, k+1)| ≤ e^{−f(k)k}` eventually, then
`Σ_b f(2^b) < ∞`. This is the hypothesis of `exists_configuration_excursion_le`. -/
theorem FejerData.Admissible.summable_of_excursion_le (hD : D.Admissible Θ ω₀) (hω₀ : 0 < ω₀)
    {L : ℕ} (hL : 12 * Real.pi ≤ ω₀ * L) (hKs : Summable fun b => 1 / (D.K b : ℝ))
    (hKsum : ∑' b, 1 / (D.K b : ℝ) ≤ Real.exp (-(Θ * L)) / 8) {f : ℝ → ℝ}
    (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s) (hf0 : ∀ t, 0 ≤ f t)
    (hthin : ∀ᶠ k : ℕ in atTop,
      volume (posSet D ∩ Ico (k : ℝ) (k + 1)) ≤ ENNReal.ofReal (Real.exp (-(f k * k)))) :
    Summable fun b : ℕ => f (2 ^ b) := by
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp hthin
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = k₁ + L := ⟨_, rfl⟩
  have hpow : ∀ k, k ≤ 2 ^ k := fun k => (Nat.lt_two_pow_self).le
  have hkL : ∀ k, k₀ ≤ k → L ≤ 2 ^ k ∧ k₁ ≤ 2 ^ k := fun k hk =>
    ⟨by have := hpow k; omega, by have := hpow k; omega⟩
  -- the window exponent
  set E : ℕ → ℝ := fun k => f (2 ^ k + L) * 2 ^ k with hE
  have hthin' : ∀ k, k₀ ≤ k → ∀ j < L,
      volume (posSet D ∩ Ico ((2 ^ k + j : ℕ) : ℝ) ((2 ^ k + j : ℕ) + 1)) ≤
        ENNReal.ofReal (Real.exp (-E k)) := by
    intro k hk j hj
    have h1 := hk₁ (2 ^ k + j) (by have := (hkL k hk).2; omega)
    refine h1.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    simp only [hE]
    have hj' : ((2 ^ k + j : ℕ) : ℝ) ≤ (2 : ℝ) ^ k + L := by push_cast; exact_mod_cast (by omega)
    have hfa := hf ((2 ^ k + j : ℕ) : ℝ) ((2 : ℝ) ^ k + L) (Nat.cast_nonneg _) hj'
    have hge : (2 : ℝ) ^ k ≤ ((2 ^ k + j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h0 := hf0 ((2 : ℝ) ^ k + L)
    have h0' := hf0 ((2 ^ k + j : ℕ) : ℝ)
    have hpk : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith
  have hsum := fun n => hD.sum_excursion_le hω₀ hL hKs hKsum (E := E) (k₀ := k₀) hthin' n
  -- partial sums of the shifted sequence are bounded
  set C : ℝ := 2 * Θ + 4 * |Real.log (∑' b, D.c b)| +
    2 * |Real.log (∑' b, D.c b * D.K b) - 2 * Real.log (1 / 2)| + 2 * |Real.log (2 * Real.pi)|
  have hbound : ∀ n, ∑ j ∈ Finset.range n, f (2 ^ (k₀ + 1 + j)) ≤ C := by
    intro n
    have h1 := hsum n
    have hterm : ∀ j ∈ Finset.range n, f (2 ^ (k₀ + 1 + j)) ≤
        (E (k₀ + j) - Real.log (2 * Real.pi)) / 2 ^ (k₀ + j) +
          |Real.log (2 * Real.pi)| * (1 / 2) ^ j := by
      intro j _
      have hp : (0 : ℝ) < 2 ^ (k₀ + j) := by positivity
      have hL2 : ((2 : ℝ) ^ (k₀ + j) + L) ≤ 2 ^ (k₀ + 1 + j) := by
        have := (hkL (k₀ + j) (by omega)).1
        have h' : (L : ℝ) ≤ 2 ^ (k₀ + j) := by exact_mod_cast this
        rw [show k₀ + 1 + j = (k₀ + j) + 1 by ring, pow_succ]; linarith
      have hfa := hf ((2 : ℝ) ^ (k₀ + j) + L) (2 ^ (k₀ + 1 + j)) (by positivity) hL2
      have hE' : (E (k₀ + j) - Real.log (2 * Real.pi)) / 2 ^ (k₀ + j) =
          f (2 ^ (k₀ + j) + L) - Real.log (2 * Real.pi) / 2 ^ (k₀ + j) := by
        simp only [hE]; field_simp
      rw [hE']
      have hpj : (2 : ℝ) ^ j ≤ 2 ^ (k₀ + j) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hlog : Real.log (2 * Real.pi) / 2 ^ (k₀ + j) ≤ |Real.log (2 * Real.pi)| * (1 / 2) ^ j := by
        rw [one_div_pow, ← div_eq_mul_one_div]
        calc Real.log (2 * Real.pi) / 2 ^ (k₀ + j) ≤ |Real.log (2 * Real.pi)| / 2 ^ (k₀ + j) :=
              div_le_div_of_nonneg_right (le_abs_self _) hp.le
          _ ≤ |Real.log (2 * Real.pi)| / 2 ^ j :=
              div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hpj
      linarith
    calc ∑ j ∈ Finset.range n, f (2 ^ (k₀ + 1 + j))
        ≤ ∑ j ∈ Finset.range n, ((E (k₀ + j) - Real.log (2 * Real.pi)) / 2 ^ (k₀ + j) +
            |Real.log (2 * Real.pi)| * (1 / 2) ^ j) := Finset.sum_le_sum hterm
      _ = ∑ j ∈ Finset.range n, (E (k₀ + j) - Real.log (2 * Real.pi)) / 2 ^ (k₀ + j) +
            |Real.log (2 * Real.pi)| * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ C := by
          have hg := sum_geometric_two_le n
          have ha := abs_nonneg (Real.log (2 * Real.pi))
          nlinarith
  have hshift : Summable fun j : ℕ => f (2 ^ (j + (k₀ + 1))) :=
    summable_of_sum_range_le (fun j => hf0 _) (fun n => by
      have := hbound n
      simpa [add_comm, add_left_comm, add_assoc] using this)
  exact (summable_nat_add_iff (k₀ + 1)).mp hshift

end SubexpExcursion

end RHTower
