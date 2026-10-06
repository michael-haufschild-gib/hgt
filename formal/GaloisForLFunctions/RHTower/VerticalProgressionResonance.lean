import GaloisForLFunctions.RHTower.VerticalProgressionBumpSums
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

/-!
# Resonance counting along a vertical progression

The frequency of `n^{−it}` along `t = αℓ + β` is `u_n = γ − α log n/2π` (mod 1). It is within
`δ` of the integer `j` exactly when `log n` is within `ε₀ = 2πδ/α` of `log ρ_j`, where
`ρ_j = exp(2π(γ − j)/α)` is the *resonance centre* of `j`.

* **Counting** (`card_resonant_le`): for `ε₀ ≤ 1` the integers `n` with `|u_n − j| < δ` number at
  most `1 + 2e ε₀ ρ_j`; they lie in `(ρ_j/e, e ρ_j)`.
* **Geometric sums** (`sum_geometric_le_of_le`, `sum_geometric_neg_le_of_le`): if
  `x_j = x₀ s^j` with `s > 1`, then over any finite set of `j` with `x_j ≤ Q` the sum of `x_j` is at
  most `Q s/(s − 1)`.  The resonance centres `ρ_j` form such a progression in `−j`, which turns
  sums over resonant integers into convergent geometric sums.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.VerticalAP

noncomputable section

/-- The resonance centre `ρ_j = exp(2π(γ − j)/α)`. -/
def resCentre (α γ : ℝ) (j : ℤ) : ℝ := Real.exp (2 * Real.pi * (γ - j) / α)

/-- The frequency `u_n = γ − α log n/2π`. -/
def resFreq (α γ : ℝ) (n : ℕ) : ℝ := γ - α * Real.log n / (2 * Real.pi)

theorem resCentre_pos (α γ : ℝ) (j : ℤ) : 0 < resCentre α γ j := Real.exp_pos _

theorem log_resCentre (α γ : ℝ) (j : ℤ) :
    Real.log (resCentre α γ j) = 2 * Real.pi * (γ - j) / α := Real.log_exp _

/-- `|u_n − j| < δ` iff `|log n − log ρ_j| < 2πδ/α`. -/
theorem abs_log_sub_log_resCentre_lt {α γ δ : ℝ} (hα : 0 < α) {n : ℕ} {j : ℤ}
    (h : |resFreq α γ n - j| < δ) :
    |Real.log n - Real.log (resCentre α γ j)| < 2 * Real.pi * δ / α := by
  rw [log_resCentre]
  have hpi : 0 < 2 * Real.pi := by positivity
  have heq : Real.log n - 2 * Real.pi * (γ - j) / α =
      -(2 * Real.pi / α) * (resFreq α γ n - j) := by
    unfold resFreq; field_simp; ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity)]
  calc 2 * Real.pi / α * |resFreq α γ n - j| < 2 * Real.pi / α * δ :=
        mul_lt_mul_of_pos_left h (by positivity)
    _ = 2 * Real.pi * δ / α := by ring

theorem mem_Ioo_of_resonant {α γ δ : ℝ} (hα : 0 < α) {n : ℕ}
    (hn : 1 ≤ n) {j : ℤ} (h : |resFreq α γ n - j| < δ) :
    resCentre α γ j * Real.exp (-(2 * Real.pi * δ / α)) < n ∧
      (n : ℝ) < resCentre α γ j * Real.exp (2 * Real.pi * δ / α) := by
  have hl := abs_log_sub_log_resCentre_lt hα h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := resCentre_pos α γ j
  rw [abs_lt] at hl
  constructor
  · rw [← Real.exp_log hnR, ← Real.exp_log hρ, ← Real.exp_add, Real.exp_lt_exp]; linarith
  · rw [← Real.exp_log hnR, ← Real.exp_log hρ, ← Real.exp_add, Real.exp_lt_exp]; linarith

/-- **Counting resonant integers.** For `ε₀ = 2πδ/α ≤ 1`, the integers `n ≥ 1` with `|u_n − j| < δ`
in any finite set number at most `1 + 2e ε₀ ρ_j`. -/
theorem card_resonant_le {α γ δ : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ) (hδ : 2 * Real.pi * δ / α ≤ 1)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (j : ℤ) :
    ((S.filter fun n => |resFreq α γ n - j| < δ).card : ℝ) ≤
      1 + 2 * Real.exp 1 * (2 * Real.pi * δ / α) * resCentre α γ j := by
  set ε₀ : ℝ := 2 * Real.pi * δ / α with hε₀
  have hε0 : 0 ≤ ε₀ := by positivity
  set a : ℝ := resCentre α γ j * Real.exp (-ε₀) with ha
  set b : ℝ := resCentre α γ j * Real.exp ε₀ with hb
  have hsub : (S.filter fun n => |resFreq α γ n - j| < δ) ⊆ Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨h1, h2⟩ := mem_Ioo_of_resonant hα (hS n hn.1) hn.2
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr h1.le, Nat.le_floor h2.le⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hρ := resCentre_pos α γ j
  have hab : a ≤ b := by
    rw [ha, hb]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hρ.le
  -- `b − a ≤ 2e ε₀ ρ_j`
  have hlen : b - a ≤ 2 * Real.exp 1 * ε₀ * resCentre α γ j := by
    rw [ha, hb]
    have h1 : Real.exp ε₀ - Real.exp (-ε₀) ≤ 2 * Real.exp 1 * ε₀ := by
      have hm := Real.add_one_le_exp (-ε₀)
      have hx : Real.exp ε₀ ≤ 1 + ε₀ * Real.exp 1 := by
        -- convexity of `exp` on `[0, 1]`
        have hc := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (by linarith : 0 ≤ 1 - ε₀)
          hε0 (by ring)
        simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hc
        linarith
      have he1 : 1 ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      nlinarith
    calc resCentre α γ j * Real.exp ε₀ - resCentre α γ j * Real.exp (-ε₀)
        = resCentre α γ j * (Real.exp ε₀ - Real.exp (-ε₀)) := by ring
      _ ≤ resCentre α γ j * (2 * Real.exp 1 * ε₀) := mul_le_mul_of_nonneg_left h1 hρ.le
      _ = 2 * Real.exp 1 * ε₀ * resCentre α γ j := by ring
  calc ((S.filter fun n => |resFreq α γ n - j| < δ).card : ℝ) ≤ ((⌊b⌋₊ + 1 - ⌈a⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ b - a + 1 := by
        rcases le_or_gt (⌊b⌋₊ + 1) ⌈a⌉₊ with hle | hlt
        · rw [Nat.sub_eq_zero_of_le hle]; push_cast; linarith
        · rw [Nat.cast_sub hlt.le]
          push_cast
          have h1 : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by positivity)
          have h2 : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
          linarith
    _ ≤ 1 + 2 * Real.exp 1 * ε₀ * resCentre α γ j := by linarith

/-! ## Geometric sums -/

/-- If `x_j = x₀ s^j` with `s > 1` and `x_j ≤ Q` on a finite set `J`, then `Σ_J x_j ≤ Q s/(s − 1)`. -/
theorem sum_geometric_le_of_le {x₀ s Q : ℝ} (hs : 1 < s) (hQ : 0 ≤ Q)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, x₀ * s ^ j ≤ Q) :
    ∑ j ∈ J, x₀ * s ^ j ≤ Q * (s / (s - 1)) := by
  have hs0 : 0 < s := by linarith
  have hgeo : s / (s - 1) = ∑' i : ℕ, (s⁻¹) ^ i := by
    rw [tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hs)]
    field_simp
  rcases J.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    have : 0 ≤ s / (s - 1) := div_nonneg hs0.le (by linarith)
    positivity
  set m : ℤ := J.max' hne with hm
  have hle : ∀ j ∈ J, j ≤ m := fun j hj => J.le_max' j hj
  have hterm : ∀ j ∈ J, x₀ * s ^ j ≤ Q * (s⁻¹) ^ (m - j).toNat := by
    intro j hj
    have hmj : ((m - j).toNat : ℤ) = m - j := Int.toNat_of_nonneg (by linarith [hle j hj])
    have hsplit : x₀ * s ^ j = x₀ * s ^ m * (s⁻¹) ^ (m - j).toNat := by
      rw [inv_pow, ← zpow_natCast, hmj, ← zpow_neg, mul_assoc, ← zpow_add₀ hs0.ne']
      congr 2
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right (hJ m (J.max'_mem hne)) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, hgeo]
  refine mul_le_mul_of_nonneg_left ?_ hQ
  have hinj : Set.InjOn (fun j : ℤ => (m - j).toNat) J := by
    intro a ha b hb hab
    simp only at hab
    have h1 : ((m - a).toNat : ℤ) = m - a := Int.toNat_of_nonneg (by linarith [hle a ha])
    have h2 : ((m - b).toNat : ℤ) = m - b := Int.toNat_of_nonneg (by linarith [hle b hb])
    have : ((m - a).toNat : ℤ) = ((m - b).toNat : ℤ) := by rw [hab]
    linarith
  rw [← Finset.sum_image (f := fun i : ℕ => (s⁻¹) ^ i) hinj]
  exact (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hs)).sum_le_tsum _
    (fun i _ => by positivity)

/-- The mirrored form: if `x₀ s^{−j} ≤ Q` on `J`, then `Σ_J x₀ s^{−j} ≤ Q s/(s − 1)`. -/
theorem sum_geometric_neg_le_of_le {x₀ s Q : ℝ} (hs : 1 < s) (hQ : 0 ≤ Q)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, x₀ * s ^ (-j) ≤ Q) :
    ∑ j ∈ J, x₀ * s ^ (-j) ≤ Q * (s / (s - 1)) := by
  have h := sum_geometric_le_of_le hs hQ (J.map (Equiv.neg ℤ).toEmbedding) (by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simpa using hJ i hi)
  rw [Finset.sum_map] at h
  simpa using h

/-! ## Sums over resonant integers -/

/-- The nearest integer to the frequency is the resonance index. -/
theorem abs_resFreq_sub_round_lt {α γ δ : ℝ} {n : ℕ} (h : ∃ j : ℤ, |resFreq α γ n - j| < δ) :
    |resFreq α γ n - round (resFreq α γ n)| < δ := by
  obtain ⟨j, hj⟩ := h
  exact lt_of_le_of_lt (round_le _ j) hj

/-- **Sums over resonant integers.** If every `n ∈ S` is resonant (`|u_n − j| < δ` for some `j`) and
`0 ≤ f(n) ≤ C n^{−a}` with `a ≥ 0`, then
`Σ_S f ≤ Σ_j C e^a ρ_j^{−a} (1 + 2e ε₀ ρ_j)`, the sum over the resonance indices `j` of `S`. -/
theorem sum_resonant_le {α γ δ : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ) (hε : 2 * Real.pi * δ / α ≤ 1)
    (S : Finset ℕ) (hS1 : ∀ n ∈ S, 1 ≤ n) (hres : ∀ n ∈ S, ∃ j : ℤ, |resFreq α γ n - j| < δ)
    (f : ℕ → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hf : ∀ n ∈ S, f n ≤ C * (n : ℝ) ^ (-a)) :
    ∑ n ∈ S, f n ≤ ∑ j ∈ S.image (fun n => round (resFreq α γ n)),
      C * Real.exp a * resCentre α γ j ^ (-a) *
        (1 + 2 * Real.exp 1 * (2 * Real.pi * δ / α) * resCentre α γ j) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => round (resFreq α γ n))
    (t := S.image (fun n => round (resFreq α γ n))) (fun n hn => Finset.mem_image_of_mem _ hn)]
  refine Finset.sum_le_sum fun j _ => ?_
  set F := S.filter fun n => round (resFreq α γ n) = j with hF
  have hFres : ∀ n ∈ F, |resFreq α γ n - j| < δ := by
    intro n hn
    rw [hF, Finset.mem_filter] at hn
    rw [← hn.2]
    exact abs_resFreq_sub_round_lt (hres n hn.1)
  have hcard : (F.card : ℝ) ≤ 1 + 2 * Real.exp 1 * (2 * Real.pi * δ / α) * resCentre α γ j := by
    have hsub : F ⊆ S.filter fun n => |resFreq α γ n - j| < δ := by
      intro n hn
      rw [Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hn).1, hFres n hn⟩
    exact (by exact_mod_cast Finset.card_le_card hsub : (F.card : ℝ) ≤ _).trans
      (card_resonant_le hα hδ0 hε S hS1 j)
  have hρ := resCentre_pos α γ j
  have hterm : ∀ n ∈ F, f n ≤ C * Real.exp a * resCentre α γ j ^ (-a) := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hn1 := hS1 n hnS
    obtain ⟨h1, _⟩ := mem_Ioo_of_resonant hα hn1 (hFres n hn)
    have hlow : resCentre α γ j * Real.exp (-1) ≤ n := by
      refine le_trans ?_ h1.le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hρ.le
    have hpos : 0 < resCentre α γ j * Real.exp (-1) := by positivity
    calc f n ≤ C * (n : ℝ) ^ (-a) := hf n hnS
      _ ≤ C * (resCentre α γ j * Real.exp (-1)) ^ (-a) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)) hC
      _ = C * Real.exp a * resCentre α γ j ^ (-a) := by
          rw [Real.mul_rpow hρ.le (Real.exp_pos _).le, ← Real.exp_mul]
          ring_nf
  calc ∑ n ∈ F, f n ≤ ∑ _n ∈ F, C * Real.exp a * resCentre α γ j ^ (-a) :=
        Finset.sum_le_sum hterm
    _ = F.card * (C * Real.exp a * resCentre α γ j ^ (-a)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 + 2 * Real.exp 1 * (2 * Real.pi * δ / α) * resCentre α γ j) *
          (C * Real.exp a * resCentre α γ j ^ (-a)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * Real.exp a * resCentre α γ j ^ (-a) *
          (1 + 2 * Real.exp 1 * (2 * Real.pi * δ / α) * resCentre α γ j) := by ring

/-- The resonance centre of the index of a resonant `n` lies within a factor `e^{ε₀}` of `n`. -/
theorem resCentre_round_bounds {α γ δ : ℝ} (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n)
    (h : ∃ j : ℤ, |resFreq α γ n - j| < δ) :
    (n : ℝ) * Real.exp (-(2 * Real.pi * δ / α)) < resCentre α γ (round (resFreq α γ n)) ∧
      resCentre α γ (round (resFreq α γ n)) < n * Real.exp (2 * Real.pi * δ / α) := by
  obtain ⟨h1, h2⟩ := mem_Ioo_of_resonant hα hn (abs_resFreq_sub_round_lt h)
  have he := Real.exp_pos (2 * Real.pi * δ / α)
  constructor
  · rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ he]
    exact h2
  · have h1' : resCentre α γ (round (resFreq α γ n)) / Real.exp (2 * Real.pi * δ / α) < n := by
      rwa [div_eq_mul_inv, ← Real.exp_neg]
    exact (div_lt_iff₀ he).mp h1'

/-- `ρ_j^{−a} = e^{−2πaγ/α} (e^{2πa/α})^j`. -/
theorem resCentre_rpow_neg (α γ a : ℝ) (j : ℤ) :
    resCentre α γ j ^ (-a) =
      Real.exp (-(2 * Real.pi * a * γ / α)) * Real.exp (2 * Real.pi * a / α) ^ j := by
  unfold resCentre
  rw [← Real.exp_mul, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- `ρ_j^{b} = e^{2πbγ/α} (e^{2πb/α})^{−j}`. -/
theorem resCentre_rpow (α γ b : ℝ) (j : ℤ) :
    resCentre α γ j ^ b =
      Real.exp (2 * Real.pi * b * γ / α) * Real.exp (2 * Real.pi * b / α) ^ (-j) := by
  unfold resCentre
  rw [← Real.exp_mul, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

end

end RHTower.VerticalAP
