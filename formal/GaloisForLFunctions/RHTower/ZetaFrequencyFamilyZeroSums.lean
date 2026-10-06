import GaloisForLFunctions.RHTower.ZetaZeroReflectionSums

/-!
# Zero sums against finite rational-frequency families

For a finite family `X(s) = Σ_i c_i (p_i/q_i)^s` (`c_i` real, `p_i, q_i ≥ 1`), over the zeros of
`[−½, 11/10] × [t₀, Y]` with `Y` admissible and `U = log T + 1`:

* (`exists_abs_re_zeroSum_deriv_famPoly_sub_le`) if every integral frequency `p_i/q_i` equals a
  fixed `P`, then `Re Σ m_ρ ζ'(ρ) X(ρ) g_T(ρ) = (Σ_{q_i ∣ p_i} c_i) Re Σ m_ρ ζ'(ρ) P^ρ g_T(ρ) + O(TU)`;
* (`exists_abs_re_zeroSum_famPoly_le`, `exists_abs_re_zeroSum_zetaChi_famPoly_le`)
  `Re Σ m_ρ X(ρ) g_T(ρ)` and `Re Σ m_ρ χ(ρ) X(ρ) g_T(ρ)` are `O(TU)`;
* (`exists_abs_re_zeroSum_deriv_one_sub_famPoly_le`) if no `p_i ∣ q_i`, then
  `Re Σ m_ρ ζ'(1 − ρ) X(ρ) g_T(ρ) = O(TU)` (reflect `ρ ↦ 1 − ρ̄`, then the integral-frequency-free
  case of the first item at the frequencies `q_i/p_i`);
* (`false_of_zeroSum_main`) a sum `Σ m_ρ H(ρ) g_T(ρ)` cannot both be `o(T log² T)` (the zero side) and
  equal `c Re Σ m_ρ ζ'(ρ) P^ρ g_T(ρ) + O(TU)` with `c ≠ 0`, since the latter is `≥ c' T log² T`.
-/

open Complex Filter Topology Set

namespace RHTower.GaussZeroSum

noncomputable section

/-- `(p/q)^s`. -/
def ratPow (p q : ℕ) (s : ℂ) : ℂ := ((((p : ℝ) / q) : ℝ) : ℂ) ^ s

theorem ratPow_mul (p₁ q₁ p₂ q₂ : ℕ) (s : ℂ) :
    ratPow p₁ q₁ s * ratPow p₂ q₂ s = ratPow (p₁ * p₂) (q₁ * q₂) s := by
  unfold ratPow
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [div_mul_div_comm]

theorem natCast_cpow_neg_eq_ratPow {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-s) = ratPow 1 n s := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ratPow
  rw [Nat.cast_one, one_div, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hn0.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, Complex.ofReal_natCast]

theorem natCast_cpow_neg_one_sub_eq_ratPow {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℂ) ^ (-(1 - s)) = (((1 : ℝ) / n : ℝ) : ℂ) * ratPow n 1 s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold ratPow
  rw [Nat.cast_one, div_one, Complex.ofReal_natCast, neg_sub, Complex.cpow_sub _ _ hn0,
    Complex.cpow_one]
  push_cast
  ring

theorem ratPow_of_dvd {p q P : ℕ} (hq : 0 < q) (h : p = P * q) (s : ℂ) :
    ratPow p q s = ((P : ℝ) : ℂ) ^ s := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold ratPow
  rw [h, Nat.cast_mul, mul_div_assoc, div_self hq0, mul_one]

/-- `X(s) = Σ_i c_i (p_i/q_i)^s`. -/
def famPoly {ι : Type*} (I : Finset ι) (c : ι → ℝ) (p q : ι → ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ I, (c i : ℂ) * ratPow (p i) (q i) s

theorem zeroSum_famPoly_eq {ι : Type*} (Z : Finset ℂ) (u : ℂ → ℂ) (T : ℝ) (I : Finset ι)
    (c : ι → ℝ) (p q : ι → ℕ) :
    ∑ w ∈ Z, (mult w : ℂ) * (u w * famPoly I c p q w * gaussWeight T w) =
      ∑ i ∈ I, (c i : ℂ) * ∑ w ∈ Z, (mult w : ℂ) * (u w * ratPow (p i) (q i) w * gaussWeight T w) := by
  unfold famPoly
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by ring

theorem re_sum_ofReal_mul {ι : Type*} (I : Finset ι) (c : ι → ℝ) (S : ι → ℂ) :
    (∑ i ∈ I, (c i : ℂ) * S i).re = ∑ i ∈ I, c i * (S i).re := by
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.re_ofReal_mul _ _

theorem GoodTop.bottom_le {T Y : ℝ} (hT : 2 ≤ T) (hY : GoodTop T Y) : bottomHeight ≤ Y := by
  have h1 := bottomHeight_mem.2
  have h2 := hY.1.1
  nlinarith

/-- Uniform constants for finitely many `O(TU)` estimates. -/
theorem exists_uniform_of_forall {ι : Type*} (I : Finset ι) {E : ι → ℝ → ℝ → ℝ}
    (h : ∀ i ∈ I, ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |E i T Y| ≤ C * T * (Real.log T + 1)) {w : ι → ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      ∑ i ∈ I, |w i| * |E i T Y| ≤ C * T * (Real.log T + 1) := by
  classical
  have h' : ∀ i : ι, ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      i ∈ I → |E i T Y| ≤ C * T * (Real.log T + 1) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨C, hC, T₀, hT⟩ := h i hi
      exact ⟨C, hC, T₀, fun T hT' Y hY _ => hT T hT' Y hY⟩
    · exact ⟨0, le_rfl, 0, fun _ _ _ _ hi' => absurd hi' hi⟩
  choose C hC T₀ hT using h'
  refine ⟨∑ i ∈ I, |w i| * C i, Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hC i),
    ∑ i ∈ I, |T₀ i|, fun T hT' Y hY => ?_⟩
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hTi : T₀ i ≤ T :=
    (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (T₀ j)) hi).trans hT')
  calc |w i| * |E i T Y| ≤ |w i| * (C i * T * (Real.log T + 1)) :=
        mul_le_mul_of_nonneg_left (hT i T hTi Y hY hi) (abs_nonneg _)
    _ = _ := by ring

/-- `|Σ_i c_i x_i| ≤ Σ_i |c_i| |x_i|`. -/
theorem abs_sum_mul_le {ι : Type*} (I : Finset ι) (c x : ι → ℝ) :
    |∑ i ∈ I, c i * x i| ≤ ∑ i ∈ I, |c i| * |x i| :=
  (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => abs_mul _ _))

/-! ## The four family estimates -/

/-- **Rule A for a family.** -/
theorem exists_abs_re_zeroSum_deriv_famPoly_sub_le {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    (p q : ι → ℕ) (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i) (P : ℕ)
    (hint : ∀ i ∈ I, q i ∣ p i → p i = P * q i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (deriv riemannZeta w * famPoly I c p q w * gaussWeight T w)).re -
        (∑ i ∈ I.filter (fun i => q i ∣ p i), c i) *
          (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
            (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  classical
  set J := I.filter (fun i => ¬ q i ∣ p i) with hJ
  obtain ⟨C, hC, T₀, hT⟩ := exists_uniform_of_forall J (w := c)
    (E := fun i T Y => (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
      (deriv riemannZeta w * ratPow (p i) (q i) w * gaussWeight T w)).re) fun i hi => by
      rw [hJ, Finset.mem_filter] at hi
      exact exists_abs_re_zeroSum_deriv_div_le (hp i hi.1) (hq i hi.1) hi.2
  refine ⟨C, hC, T₀, fun T hT' Y hY => ?_⟩
  rw [zeroSum_famPoly_eq, re_sum_ofReal_mul,
    ← Finset.sum_filter_add_sum_filter_not I (fun i => q i ∣ p i), Finset.sum_mul]
  have hdiv : ∀ i ∈ I.filter (fun i => q i ∣ p i),
      c i * (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
        (deriv riemannZeta w * ratPow (p i) (q i) w * gaussWeight T w)).re =
      c i * (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
        (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re := by
    intro i hi
    rw [Finset.mem_filter] at hi
    simp_rw [ratPow_of_dvd (hq i hi.1) (hint i hi.1 hi.2)]
  rw [Finset.sum_congr rfl hdiv, add_sub_cancel_left]
  exact (abs_sum_mul_le _ _ _).trans (hT T hT' Y hY)

/-- **Landau–Gonek for a family.** -/
theorem exists_abs_re_zeroSum_famPoly_le {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    (p q : ι → ℕ) (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (famPoly I c p q w * gaussWeight T w)).re| ≤ C * T * (Real.log T + 1) := by
  obtain ⟨C, hC, T₀, hT⟩ := exists_uniform_of_forall I (w := c)
    (E := fun i T Y => (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
      ((1 : ℂ) * ratPow (p i) (q i) w * gaussWeight T w)).re) fun i hi => by
      have hr : (0 : ℝ) < (p i : ℝ) / q i := by
        have := hp i hi; have := hq i hi; positivity
      obtain ⟨C, hC, h⟩ := exists_abs_re_zeroSum_gW_le hr
      refine ⟨C, hC, 2, fun T hT Y hY => ?_⟩
      simp only [one_mul, ratPow]
      exact h T hT Y hY
  refine ⟨C, hC, T₀, fun T hT' Y hY => ?_⟩
  have e := zeroSum_famPoly_eq (rectZeros bottomHeight Y) (fun _ => 1) T I c p q
  simp only [one_mul] at e
  rw [e, re_sum_ofReal_mul]
  refine (abs_sum_mul_le _ _ _).trans (le_trans (le_of_eq ?_) (hT T hT' Y hY))
  simp only [one_mul]

/-- **The `χ`-twisted sum for a family.** -/
theorem exists_abs_re_zeroSum_zetaChi_famPoly_le {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    (p q : ι → ℕ) (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (zetaChi w * famPoly I c p q w * gaussWeight T w)).re| ≤ C * T * (Real.log T + 1) := by
  obtain ⟨C, hC, T₀, hT⟩ := exists_uniform_of_forall I (w := c)
    (E := fun i T Y => (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
      (zetaChi w * ratPow (p i) (q i) w * gaussWeight T w)).re) fun i hi => by
      have hr : (0 : ℝ) < (p i : ℝ) / q i := by
        have := hp i hi; have := hq i hi; positivity
      obtain ⟨C, hC, h⟩ := exists_abs_re_zeroSum_zetaChi_gW_le hr
      refine ⟨C, hC, max 2 ((p i : ℝ) / q i), fun T hT Y hY => ?_⟩
      have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
      have hU : 1 ≤ Real.log T + 1 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]
      refine (h T hT2 ((le_max_right _ _).trans hT) Y hY).trans ?_
      calc C * T = C * T * 1 := (mul_one _).symm
        _ ≤ C * T * (Real.log T + 1) := mul_le_mul_of_nonneg_left hU (by positivity)
  refine ⟨C, hC, T₀, fun T hT' Y hY => ?_⟩
  rw [zeroSum_famPoly_eq, re_sum_ofReal_mul]
  exact (abs_sum_mul_le _ _ _).trans (hT T hT' Y hY)

/-- **The reflected derivative sum for a family without integral reciprocal frequencies.** -/
theorem exists_abs_re_zeroSum_deriv_one_sub_famPoly_le {ι : Type*} (I : Finset ι) (c : ι → ℝ)
    (p q : ι → ℕ) (hp : ∀ i ∈ I, 0 < p i) (hq : ∀ i ∈ I, 0 < q i)
    (hint : ∀ i ∈ I, ¬ p i ∣ q i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (deriv riemannZeta (1 - w) * famPoly I c p q w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1) := by
  obtain ⟨C, hC, T₀, hT⟩ := exists_uniform_of_forall I (w := c)
    (E := fun i T Y => (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
      (deriv riemannZeta (1 - w) * ratPow (p i) (q i) w * gaussWeight T w)).re) fun i hi => by
      have hp0 : (0 : ℝ) < p i := by exact_mod_cast hp i hi
      have hq0 : (0 : ℝ) < q i := by exact_mod_cast hq i hi
      obtain ⟨C, hC, T₀, h⟩ := exists_abs_re_zeroSum_deriv_div_le (hq i hi) (hp i hi) (hint i hi)
      refine ⟨(p i : ℝ) / q i * C, by positivity, max 2 T₀, fun T hT Y hY => ?_⟩
      have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
      have hx : (0 : ℝ) < (p i : ℝ) / q i := by positivity
      simp only [ratPow]
      rw [re_zeroSum_deriv_one_sub_eq (hY.bottom_le hT2) hx, inv_div, abs_mul, abs_of_pos hx,
        mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by
        have := h T ((le_max_right _ _).trans hT) Y hY
        rwa [mul_assoc] at this) hx.le
  refine ⟨C, hC, T₀, fun T hT' Y hY => ?_⟩
  rw [zeroSum_famPoly_eq, re_sum_ofReal_mul]
  exact (abs_sum_mul_le _ _ _).trans (hT T hT' Y hY)

/-! ## The contradiction -/

/-- For `α > 0`, eventually `β (log T + 1) < α log² T`. -/
theorem eventually_lt_log_sq {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ᶠ T : ℝ in atTop, β * (Real.log T + 1) < α * Real.log T ^ 2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2 * β / α + 2)] with T hT
  have hb : 0 ≤ 2 * β / α := by positivity
  have hL : 2 ≤ Real.log T := by linarith
  have h1 : α * (2 * β / α + 2) = 2 * β + 2 * α := by field_simp
  have h2 : α * Real.log T * (2 * β / α + 2) ≤ α * Real.log T * Real.log T :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  nlinarith

/-- **No zero sum is both small and a nonzero multiple of a Rule-A main term.** -/
theorem false_of_zeroSum_main {H : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hcrit : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → 1 ≤ ρ.im → H ρ = 0)
    (hoff : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 → 1 ≤ ρ.im →
      ‖H ρ‖ ≤ K * Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im))
    {a : ℝ} (ha : a ≠ 0) {P : ℕ} (hP : 1 ≤ P)
    (hmain : ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ Y : ℝ, GoodTop T Y →
      |(∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * (H w * gaussWeight T w)).re -
        a * (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
          (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re| ≤
        C * T * (Real.log T + 1)) : False := by
  obtain ⟨C, hC, T₀, hT₀⟩ := hmain
  obtain ⟨C₁, hC₁, hRA⟩ := exists_re_zeroSum_deriv_natCast_ge hP
  set c₀ : ℝ := Real.exp (-(4 * Real.pi ^ 2)) / 32 with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  have ha0 : 0 < |a| := abs_pos.mpr ha
  set ε : ℝ := |a| * c₀ / (16 * Real.exp 1 * (K + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hev := (eventually_norm_zeroSum_le hK hcrit hoff hε0).and
    ((eventually_ge_atTop (max (max T₀ 4) (max (Real.exp 202 * P) ((P : ℝ) ^ 2)))).and
      (eventually_lt_log_sq (α := |a| * c₀ / 8) (β := |a| * C₁ + C) (by positivity)
        (by positivity)))
  obtain ⟨T, hzero, hTbig, hlog⟩ := hev.exists
  have hT4 : 4 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hTT₀ : T₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTP : Real.exp 202 * P ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTP2 : (P : ℝ) ^ 2 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hT0 : 0 < T := by linarith
  obtain ⟨Y, hY⟩ := exists_goodTop hT4
  have hYb := hY.bottom_le (by linarith)
  set S := (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * (H w * gaussWeight T w)).re
  set M := (∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) *
    (deriv riemannZeta w * ((P : ℝ) : ℂ) ^ w * gaussWeight T w)).re
  have h1 : |S - a * M| ≤ C * T * (Real.log T + 1) := hT₀ T hTT₀ Y hY
  have h2 : c₀ * T * Real.log (T / P) ^ 2 - C₁ * T * (Real.log T + 1) ≤ M :=
    hRA T (by linarith) hTP Y hY
  have h3 : |S| ≤ 2 * Real.exp 1 * K * (ε * T * Real.log T ^ 2) :=
    (Complex.abs_re_le_norm _).trans (hzero Y hYb)
  -- `log(T/P) ≥ ½ log T`
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogP : 2 * Real.log P ≤ Real.log T := by
    have := Real.log_le_log (by positivity) hTP2
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlogP0 : 0 ≤ Real.log P := Real.log_natCast_nonneg P
  have hlogTP : Real.log T / 2 ≤ Real.log (T / P) := by
    rw [Real.log_div hT0.ne' hP0.ne']; linarith
  have hsq : Real.log T ^ 2 / 4 ≤ Real.log (T / P) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hlogTP 2
    linarith [show (Real.log T / 2) ^ 2 = Real.log T ^ 2 / 4 by ring]
  -- `|a| M ≤ |S| + C T U`
  have h4 : |a| * M ≤ |S| + C * T * (Real.log T + 1) := by
    have := abs_sub_abs_le_abs_sub (a * M) S
    rw [abs_sub_comm] at this
    have h5 : |a| * M ≤ |a * M| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (le_abs_self M) ha0.le
    linarith
  have hεK : 2 * Real.exp 1 * K * ε ≤ |a| * c₀ / 8 := by
    rw [hε]
    have hK1 : 0 < K + 1 := by linarith
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    rw [show 2 * Real.exp 1 * K * (|a| * c₀ / (16 * Real.exp 1 * (K + 1))) =
      |a| * c₀ / 8 * (K / (K + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one hK1).mpr (by linarith))
  have h6 : |S| ≤ |a| * c₀ / 8 * (T * Real.log T ^ 2) := by
    refine h3.trans ?_
    rw [show 2 * Real.exp 1 * K * (ε * T * Real.log T ^ 2) =
      2 * Real.exp 1 * K * ε * (T * Real.log T ^ 2) by ring]
    exact mul_le_mul_of_nonneg_right hεK (by positivity)
  have h7 : |a| * (c₀ * T * (Real.log T ^ 2 / 4) - C₁ * T * (Real.log T + 1)) ≤ |a| * M := by
    apply mul_le_mul_of_nonneg_left _ ha0.le
    refine le_trans ?_ h2
    have : c₀ * T * (Real.log T ^ 2 / 4) ≤ c₀ * T * Real.log (T / P) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  have h8 : |a| * c₀ / 8 * Real.log T ^ 2 ≤ (|a| * C₁ + C) * (Real.log T + 1) := by
    have : T * (|a| * c₀ / 8 * Real.log T ^ 2) ≤ T * ((|a| * C₁ + C) * (Real.log T + 1)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hT0
  linarith

end

end RHTower.GaussZeroSum
