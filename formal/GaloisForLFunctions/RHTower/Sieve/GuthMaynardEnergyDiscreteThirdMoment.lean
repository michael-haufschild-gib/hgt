import GaloisForLFunctions.RHTower.Sieve.GuthMaynardDirichletPolynomialLocalAverage
import GaloisForLFunctions.RHTower.Sieve.SeparatedCount

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.4: the energy is controlled by the discrete third moment of `R`

Let `D(t) = Σ_{N<n≤2N} b_n n^{it}` with `|b_n| ≤ 1`, and let `W` be `1`-separated with
`|D(t)| ≥ N^σ` on `W`. Then (Guth–Maynard, arXiv 2405.20552, Lemma 11.4)

`E(W) ≪ N^{−2σ} Σ_{n₁,n₂ ∼ N} |R(n₁/n₂)|³`,

with an absolute constant (stronger than the paper's `⪅`; no interval, no `T`).

Proof. `E(W) = Σ_{t₁,t₂,t₃} #{t₄ : |t₁+t₂−t₃−t₄| ≤ 1}` and each count is at most `3` by
separation. For such `t₄ = x − σ'` (`x = t₁+t₂−t₃`, `|σ'| ≤ 1`), `1 ≤ N^{−2σ}|D(t₄)|²` and the
shifted square form of Lemma 11.3 gives `|D(t₄)|² ≤ ‖K‖₁ ∫ 3c/(1+η²) |D(x + η)|² dη`. Expanding
`|D|²` as a double sum over `n₁, n₂`,
`Σ_{t₁,t₂,t₃} |D(t₁+t₂−t₃+η)|² = Σ_{n₁,n₂} b_{n₁} b̄_{n₂} (n₁/n₂)^{iη} R(n₁/n₂)² R̄(n₁/n₂)`,
which is at most `Σ |R(n₁/n₂)|³` because `|b_n| ≤ 1` (the only use of the `ℓ^∞` bound).

The module also records the elementary energy bounds `|W|² ≤ E(W)` and, for `1`-separated `W`,
`E(W) ≤ 3|W|³`.
-/

open MeasureTheory Set Finset ComplexConjugate

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Elementary energy bounds -/

/-- At most three points of a `1`-separated set lie within distance `1` of a given point. -/
theorem card_filter_abs_sub_le_three {W : Finset ℝ} (hsep : IsSeparated 1 W) (x : ℝ) :
    ((W.filter fun t => |x - t| ≤ 1).card : ℝ) ≤ 3 := by
  have h := Sieve.card_le_of_separated (s := W.filter fun t => |x - t| ≤ 1) (u := id) (g := 1)
    (L := 2) (c := x - 1) one_pos (by norm_num)
    (fun t ht t' ht' hne => hsep t (mem_filter.mp ht).1 t' (mem_filter.mp ht').1 hne)
    (fun t ht => by
      have := abs_le.mp (mem_filter.mp ht).2
      simp only [id]
      constructor <;> linarith)
  calc _ ≤ 2 / 1 + 1 := h
    _ = 3 := by norm_num

/-- The energy as a sum over triples of the number of admissible fourth points. -/
theorem additiveEnergy_eq_sum_card (W : Finset ℝ) :
    (additiveEnergy W : ℝ) = ∑ q ∈ W ×ˢ W ×ˢ W,
      ((W.filter fun t₄ => |q.1 + q.2.1 - q.2.2 - t₄| ≤ 1).card : ℝ) := by
  classical
  unfold additiveEnergy
  rw [card_filter]
  push_cast
  simp only [sum_product, card_filter]
  push_cast
  rfl

/-- For `1`-separated `W`: `E(W) ≤ 3|W|³`. -/
theorem additiveEnergy_le_three_mul_card_pow {W : Finset ℝ} (hsep : IsSeparated 1 W) :
    (additiveEnergy W : ℝ) ≤ 3 * (W.card : ℝ) ^ 3 := by
  rw [additiveEnergy_eq_sum_card]
  calc ∑ q ∈ W ×ˢ W ×ˢ W, ((W.filter fun t₄ => |q.1 + q.2.1 - q.2.2 - t₄| ≤ 1).card : ℝ)
      ≤ ∑ _q ∈ W ×ˢ W ×ˢ W, (3 : ℝ) :=
        sum_le_sum fun q _ => card_filter_abs_sub_le_three hsep _
    _ = 3 * (W.card : ℝ) ^ 3 := by simp [card_product]; ring

/-- `|W|² ≤ E(W)`: the quadruples `(t₁, t₂, t₁, t₂)` are additive. -/
theorem card_sq_le_additiveEnergy (W : Finset ℝ) : (W.card : ℝ) ^ 2 ≤ additiveEnergy W := by
  classical
  have h : (W ×ˢ W).card ≤ additiveEnergy W := by
    unfold additiveEnergy
    refine card_le_card_of_injOn (fun p => (p.1, p.2, p.1, p.2)) ?_ ?_
    · intro p hp
      have hp' := mem_product.mp (mem_coe.mp hp)
      simp only [coe_filter, Set.mem_setOf_eq, mem_product]
      refine ⟨⟨hp'.1, hp'.2, hp'.1, hp'.2⟩, ?_⟩
      simp
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 hpq.2.1
  rw [card_product] at h
  exact_mod_cast (show W.card ^ 2 ≤ additiveEnergy W by rw [sq]; exact h)

/-! ### The expansion of `Σ |D(t₁+t₂−t₃+η)|²` -/

/-- `n₁^{iy} \overline{n₂^{iy}} = (n₁/n₂)^{iy}` for positive integers. -/
theorem exp_mul_conj_exp_log {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) (y : ℝ) :
    Complex.exp (Complex.I * y * Real.log n₁) * conj (Complex.exp (Complex.I * y * Real.log n₂)) =
      Complex.exp (Complex.I * y * Real.log ((n₁ : ℝ) / n₂)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add,
    Real.log_div (Nat.cast_ne_zero.mpr h₁.ne') (Nat.cast_ne_zero.mpr h₂.ne')]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `|D(y)|² = Σ_{n₁,n₂} b_{n₁} b̄_{n₂} (n₁/n₂)^{iy}`. -/
theorem normSq_dyadicDirichletPoly_eq (N : ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ((‖dyadicDirichletPoly N b y‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        b n₁ * conj (b n₂) * Complex.exp (Complex.I * y * Real.log ((n₁ : ℝ) / n₂)) := by
  push_cast
  rw [← Complex.mul_conj', dyadicDirichletPoly, map_sum, sum_mul_sum]
  refine sum_congr rfl fun n₁ h₁ => sum_congr rfl fun n₂ h₂ => ?_
  have p₁ : 0 < n₁ := by have := (mem_Ioc.mp h₁).1; omega
  have p₂ : 0 < n₂ := by have := (mem_Ioc.mp h₂).1; omega
  rw [← exp_mul_conj_exp_log p₁ p₂ y, map_mul]
  ring

/-- `Σ_{t₁,t₂,t₃} v^{i(t₁+t₂−t₃+η)} = v^{iη} R(v)² \overline{R(v)}`. -/
theorem sum_triple_exp_eq (W : Finset ℝ) (v η : ℝ) :
    ∑ q ∈ W ×ˢ W ×ˢ W, Complex.exp (Complex.I * (q.1 + q.2.1 - q.2.2 + η) * Real.log v) =
      Complex.exp (Complex.I * η * Real.log v) * lagSum W v * lagSum W v *
        conj (lagSum W v) := by
  set e : ℝ → ℂ := fun s => Complex.exp (Complex.I * s * Real.log v) with he_def
  have he : ∀ q : ℝ × ℝ × ℝ, Complex.exp (Complex.I * (q.1 + q.2.1 - q.2.2 + η) * Real.log v) =
      e q.1 * (e q.2.1 * (conj (e q.2.2) * e η)) := by
    intro q
    simp only [he_def]
    rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hR : lagSum W v = ∑ t ∈ W, e t := rfl
  simp_rw [he]
  rw [hR, map_sum, sum_product]
  calc ∑ x ∈ W, ∑ y ∈ W ×ˢ W, e (x, y).1 * (e (x, y).2.1 * (conj (e (x, y).2.2) * e η))
      = (∑ t ∈ W, e t) * ((∑ t ∈ W, e t) * ((∑ t ∈ W, conj (e t)) * e η)) := by
        rw [sum_mul]
        refine sum_congr rfl fun t₁ _ => ?_
        rw [sum_product, sum_mul, mul_sum]
        refine sum_congr rfl fun t₂ _ => ?_
        rw [sum_mul, mul_sum, mul_sum]
    _ = _ := by ring

/-- **The `ℓ^∞` step of Lemma 11.4.** For `|b_n| ≤ 1` and every `η`:
`Σ_{t₁,t₂,t₃ ∈ W} |D(t₁+t₂−t₃+η)|² ≤ Σ_{n₁,n₂ ∼ N} |R(n₁/n₂)|³`. -/
theorem sum_triple_normSq_dyadicDirichletPoly_le {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1)
    (W : Finset ℝ) (η : ℝ) :
    ∑ q ∈ W ×ˢ W ×ˢ W, ‖dyadicDirichletPoly N b (q.1 + q.2.1 - q.2.2 + η)‖ ^ 2 ≤
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 := by
  have hexp : ((∑ q ∈ W ×ˢ W ×ˢ W,
      ‖dyadicDirichletPoly N b (q.1 + q.2.1 - q.2.2 + η)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N), b n₁ * conj (b n₂) *
        (Complex.exp (Complex.I * η * Real.log ((n₁ : ℝ) / n₂)) * lagSum W ((n₁ : ℝ) / n₂) *
          lagSum W ((n₁ : ℝ) / n₂) * conj (lagSum W ((n₁ : ℝ) / n₂))) := by
    push_cast
    simp_rw [← sum_triple_exp_eq]
    have := fun q : ℝ × ℝ × ℝ => normSq_dyadicDirichletPoly_eq N b (q.1 + q.2.1 - q.2.2 + η)
    push_cast at this
    simp_rw [this]
    rw [sum_comm]
    refine sum_congr rfl fun n₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n₂ _ => ?_
    rw [mul_sum]
  have hle : ‖((∑ q ∈ W ×ˢ W ×ˢ W,
      ‖dyadicDirichletPoly N b (q.1 + q.2.1 - q.2.2 + η)‖ ^ 2 : ℝ) : ℂ)‖ ≤
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 := by
    rw [hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n₁ _ => (norm_sum_le _ _).trans
      (sum_le_sum fun n₂ _ => ?_))
    simp only [norm_mul, Complex.norm_conj, norm_exp_mul_log]
    have h1 := hb n₁
    have h2 := hb n₂
    have h0 : 0 ≤ ‖lagSum W ((n₁ : ℝ) / n₂)‖ := norm_nonneg _
    calc ‖b n₁‖ * ‖b n₂‖ * (1 * ‖lagSum W ((n₁ : ℝ) / n₂)‖ * ‖lagSum W ((n₁ : ℝ) / n₂)‖ *
          ‖lagSum W ((n₁ : ℝ) / n₂)‖)
        ≤ 1 * 1 * (1 * ‖lagSum W ((n₁ : ℝ) / n₂)‖ * ‖lagSum W ((n₁ : ℝ) / n₂)‖ *
          ‖lagSum W ((n₁ : ℝ) / n₂)‖) := by gcongr
      _ = ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 := by ring
  rwa [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun _ _ => by positivity)] at hle

/-! ### Lemma 11.4 -/

/-- The absolute constant of Lemma 11.4: `9π ‖K‖₁ bandCauchy`. -/
def energyThirdMomentConst : ℝ := 9 * Real.pi * bandMass * bandCauchy

theorem energyThirdMomentConst_nonneg : 0 ≤ energyThirdMomentConst := by
  unfold energyThirdMomentConst
  have := bandMass_nonneg
  have := bandCauchy_nonneg
  positivity

/-- **Guth–Maynard Lemma 11.4** (`E(W) ⪅ N^{−2σ} Σ_{n₁,n₂∼N} |R(n₁/n₂)|³`, here with an absolute
constant): for `N ≥ 1`, `|b_n| ≤ 1`, `1`-separated `W` with `|D(t)| ≥ N^σ` on `W`,
`E(W) ≤ 9π‖K‖₁ bandCauchy · N^{−2σ} Σ_{n₁,n₂ ∈ (N,2N]} |R(n₁/n₂)|³`. -/
theorem additiveEnergy_le_discreteThirdMoment {N : ℕ} {b : ℕ → ℂ} {σ : ℝ} {W : Finset ℝ}
    (hN : 1 ≤ N) (hb : ∀ n, ‖b n‖ ≤ 1) (hsep : IsSeparated 1 W)
    (hD : ∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicDirichletPoly N b t‖) :
    (additiveEnergy W : ℝ) ≤ energyThirdMomentConst * (N : ℝ) ^ (-2 * σ) *
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (N : ℝ) ^ (-2 * σ) with hc
  have hc0 : 0 ≤ c := by positivity
  set w : ℝ → ℝ := fun η => 3 * bandCauchy / (1 + η ^ 2) with hw
  have hw0 : ∀ η, 0 ≤ w η := fun η => by have := bandCauchy_nonneg; positivity
  set Φ : ℝ → ℝ := fun x => ∫ η, w η * ‖dyadicDirichletPoly N b (x + η)‖ ^ 2 with hΦ
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x =>
    integral_nonneg fun η => mul_nonneg (hw0 η) (by positivity)
  -- integrability of the weighted squares
  have hwint : Integrable w := by
    simpa [hw, div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (3 * bandCauchy)
  have hint : ∀ x, Integrable fun η => w η * ‖dyadicDirichletPoly N b (x + η)‖ ^ 2 := by
    intro x
    refine hwint.mul_bdd (c := (N : ℝ) ^ 2)
      (((continuous_dyadicDirichletPoly N b).comp (continuous_const_add x)).norm.pow 2
        ).aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_dyadicDirichletPoly_le hb _) 2
  -- each large value gives `1 ≤ c |D(t₄)|² ≤ c ‖K‖₁ Φ(x)`
  have hone : ∀ x t₄, t₄ ∈ W → |x - t₄| ≤ 1 → 1 ≤ c * (bandMass * Φ x) := by
    intro x t₄ ht₄ hx
    have hpow : c * ((N : ℝ) ^ σ) ^ 2 = 1 := by
      rw [hc, sq, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      ring_nf
      exact Real.rpow_zero _
    have hsq : ((N : ℝ) ^ σ) ^ 2 ≤ ‖dyadicDirichletPoly N b t₄‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hD t₄ ht₄) 2
    have hshift := norm_dyadicDirichletPoly_sub_sq_le N b x (x - t₄) hx
    rw [sub_sub_cancel] at hshift
    calc (1 : ℝ) = c * ((N : ℝ) ^ σ) ^ 2 := hpow.symm
      _ ≤ c * ‖dyadicDirichletPoly N b t₄‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hc0
      _ ≤ c * (bandMass * Φ x) := mul_le_mul_of_nonneg_left hshift hc0
  -- count the fourth points
  have hcount : ∀ q ∈ W ×ˢ W ×ˢ W,
      ((W.filter fun t₄ => |q.1 + q.2.1 - q.2.2 - t₄| ≤ 1).card : ℝ) ≤
        3 * (c * (bandMass * Φ (q.1 + q.2.1 - q.2.2))) := by
    intro q _
    have hk3 := card_filter_abs_sub_le_three hsep (q.1 + q.2.1 - q.2.2)
    have hX0 : 0 ≤ c * (bandMass * Φ (q.1 + q.2.1 - q.2.2)) :=
      mul_nonneg hc0 (mul_nonneg bandMass_nonneg (hΦ0 _))
    by_cases hne : (W.filter fun t₄ => |q.1 + q.2.1 - q.2.2 - t₄| ≤ 1).Nonempty
    · obtain ⟨t₄, ht₄⟩ := hne
      have h1 := hone _ t₄ (mem_filter.mp ht₄).1 (mem_filter.mp ht₄).2
      nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  -- sum over triples and swap with the integral
  have hswap : ∑ q ∈ W ×ˢ W ×ˢ W, Φ (q.1 + q.2.1 - q.2.2) =
      ∫ η, w η * ∑ q ∈ W ×ˢ W ×ˢ W,
        ‖dyadicDirichletPoly N b (q.1 + q.2.1 - q.2.2 + η)‖ ^ 2 := by
    simp only [hΦ]
    rw [← integral_finsetSum _ fun q _ => hint _]
    congr 1; funext η
    rw [mul_sum]
  have hbound : ∑ q ∈ W ×ˢ W ×ˢ W, Φ (q.1 + q.2.1 - q.2.2) ≤
      3 * Real.pi * bandCauchy * ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3 := by
    rw [hswap]
    set M := ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
      ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3
    calc ∫ η, w η * ∑ q ∈ W ×ˢ W ×ˢ W,
          ‖dyadicDirichletPoly N b (q.1 + q.2.1 - q.2.2 + η)‖ ^ 2
        ≤ ∫ η, w η * M := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η =>
            mul_nonneg (hw0 η) (sum_nonneg fun _ _ => by positivity)) (hwint.mul_const M)
            (Filter.Eventually.of_forall fun η => ?_)
          exact mul_le_mul_of_nonneg_left (sum_triple_normSq_dyadicDirichletPoly_le hb W η)
            (hw0 η)
      _ = 3 * Real.pi * bandCauchy * M := by
          rw [integral_mul_const]
          simp only [hw, div_eq_mul_inv]
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
          ring
  rw [additiveEnergy_eq_sum_card]
  calc ∑ q ∈ W ×ˢ W ×ˢ W, ((W.filter fun t₄ => |q.1 + q.2.1 - q.2.2 - t₄| ≤ 1).card : ℝ)
      ≤ ∑ q ∈ W ×ˢ W ×ˢ W, 3 * (c * (bandMass * Φ (q.1 + q.2.1 - q.2.2))) := sum_le_sum hcount
    _ = 3 * c * bandMass * ∑ q ∈ W ×ˢ W ×ˢ W, Φ (q.1 + q.2.1 - q.2.2) := by
        rw [mul_sum]; refine sum_congr rfl fun q _ => by ring
    _ ≤ 3 * c * bandMass * (3 * Real.pi * bandCauchy *
          ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
            ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 3) :=
        mul_le_mul_of_nonneg_left hbound (by have := bandMass_nonneg; positivity)
    _ = _ := by unfold energyThirdMomentConst; ring

end

end RHTower.GuthMaynard
