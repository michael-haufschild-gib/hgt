import GaloisForLFunctions.RHTower.DeBruijnHeatLocalModel

/-!
# The forward local heat model of `H_t` at a zero of order `k`

Let `z₀` be a zero of order `k` of `H_s` (`s ≥ 0`) and `a = H_s^{(k)}(z₀)`.  Forward in time, at
the parabolic scale `z = z₀ + qσ`,

`H_{s+q²}(z₀ + qσ) = (a/k!) q^k Q_k(σ) + O(q^{k+1})`,
`Q_k(σ) = Σ_{2m ≤ k} (−1)^m k!/(m!(k−2m)!) σ^{k−2m}`,

uniformly for `σ` in compact sets (`exists_norm_riemannHeat_sub_heatModelFwd_le`).  Here
`Q_k = e^{−D²}σ^k` is the forward heat evolution of the monomial, a rescaled Hermite polynomial with
`k` simple real roots.  The proof is the backward model's with the time step `+q²` in place of
`−q²` in the time Taylor expansion `norm_riemannHeat_time_taylor_le`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-- The forward heat evolution `e^{−D²}σ^k = Σ_{2m ≤ k} (−1)^m k!/(m!(k−2m)!) σ^{k−2m}`. -/
def heatModelFwd (k : ℕ) (σ : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (k / 2 + 1),
    ((-1 : ℂ) ^ m * (k.factorial : ℂ) / ((m.factorial : ℂ) * ((k - 2 * m).factorial : ℂ))) *
      σ ^ (k - 2 * m)

theorem sum_jetPart_eq_fwd (k : ℕ) (a : ℂ) (q : ℝ) (σ : ℂ) :
    ∑ m ∈ Finset.range (k + 1), (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        jetPart k a m (q * σ) = a / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModelFwd k σ := by
  have hsub : Finset.range (k / 2 + 1) ⊆ Finset.range (k + 1) := by
    intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  rw [← Finset.sum_subset hsub (fun m hm hm' => by
    simp only [Finset.mem_range] at hm hm'
    simp [jetPart, show ¬ 2 * m ≤ k by omega])]
  rw [heatModelFwd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  have hm2 : 2 * m ≤ k := by omega
  simp only [jetPart, hm2, if_true]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hmf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hkm : ((k - 2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hq : ((q : ℂ) ^ 2) ^ m * (q : ℂ) ^ (k - 2 * m) = (q : ℂ) ^ k := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [mul_pow, neg_pow, ← hq]
  field_simp

/-- Each even derivative of `H_s` near a zero of order `k` is its jet part up to
`O(|w|^{k+1−2m})`. -/
theorem exists_norm_iteratedDeriv_sub_jetPart_le {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0) (m : ℕ) :
    ∃ C r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w‖ ≤ r →
      ‖iteratedDeriv (2 * m) (riemannHeat s) (z₀ + w) -
        jetPart k (iteratedDeriv k (riemannHeat s) z₀) m w‖ ≤ C * ‖w‖ ^ (k + 1 - 2 * m) := by
  set H := riemannHeat s
  have hd := differentiable_iteratedDeriv_riemannHeat hs (2 * m)
  by_cases hm : 2 * m ≤ k
  · have hv : ∀ i < k - 2 * m, iteratedDeriv i (iteratedDeriv (2 * m) H) z₀ = 0 := by
      intro i hi
      rw [iteratedDeriv_iteratedDeriv_eq]
      exact hvan _ (by omega)
    obtain ⟨C, r, hr, hb⟩ := exists_norm_sub_monomial_le hd hv
    refine ⟨C, r, hr, fun w hw => ?_⟩
    have h := hb w hw
    rw [iteratedDeriv_iteratedDeriv_eq, show k - 2 * m + 2 * m = k by omega] at h
    simp only [jetPart, hm, if_true]
    rw [show k + 1 - 2 * m = k - 2 * m + 1 by omega]
    exact h
  · obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
      hd.continuous.continuousOn
    refine ⟨B, 1, one_pos, fun w hw => ?_⟩
    simp only [jetPart, hm, if_false, sub_zero]
    rw [show k + 1 - 2 * m = 0 by omega, pow_zero, mul_one]
    exact hB _ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hw)

/-- **The forward local heat model.** Let the derivatives of `H_s` (`s ≥ 0`) of order `< k` vanish
at `z₀` and `a = H_s^{(k)}(z₀)`. For every `S ≥ 0` there are `C` and `q₀ > 0` with
`‖H_{s+q²}(z₀ + qσ) − (a/k!) q^k Q_k(σ)‖ ≤ C q^{k+1}` for `0 ≤ q ≤ q₀`, `‖σ‖ ≤ S`. -/
theorem exists_norm_riemannHeat_sub_heatModelFwd_le {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) z₀ = 0) {S : ℝ} (hS : 0 ≤ S) :
    ∃ C q₀ : ℝ, 0 < q₀ ∧ ∀ q : ℝ, 0 ≤ q → q ≤ q₀ → ∀ σ : ℂ, ‖σ‖ ≤ S →
      ‖riemannHeat (s + q ^ 2) (z₀ + q * σ) -
        iteratedDeriv k (riemannHeat s) z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModelFwd k σ‖ ≤
        C * q ^ (k + 1) := by
  set H := riemannHeat s
  set a := iteratedDeriv k H z₀
  choose Cj rj hrj hjb using exists_norm_iteratedDeriv_sub_jetPart_le hs hvan
  set M := k + 1
  have hne : (Finset.range M).Nonempty := ⟨0, by simp [M]⟩
  set r₀ := (Finset.range M).inf' hne rj
  have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff hne).mpr fun m _ => hrj m
  set S₁ := S + 1
  have hS₁ : 1 ≤ S₁ := by simp only [S₁]; linarith
  set q₀ := min 1 (min r₀ 1 / S₁)
  have hq₀ : 0 < q₀ := lt_min one_pos (div_pos (lt_min hr₀ one_pos) (by positivity))
  set K := ∫ x, |x| ^ (2 * M) * ‖heatWeight (s + 1) x‖ * Real.exp ((|z₀.im| + 1) * |x|)
  refine ⟨∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1) + K, q₀, hq₀,
    fun q hq0 hq σ hσ => ?_⟩
  have hq1 : q ≤ 1 := hq.trans (min_le_left _ _)
  set w : ℂ := q * σ with hw
  have hwn : ‖w‖ ≤ q * S₁ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    gcongr
    simp only [S₁]; linarith
  have hwmin : ‖w‖ ≤ min r₀ 1 := by
    refine hwn.trans ?_
    have : q ≤ min r₀ 1 / S₁ := hq.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hwr : ‖w‖ ≤ r₀ := hwmin.trans (min_le_left _ _)
  have hw1 : ‖w‖ ≤ 1 := hwmin.trans (min_le_right _ _)
  -- the time expansion at `h = q²`
  have hT := norm_riemannHeat_time_taylor_le hs (h := q ^ 2) (by positivity)
    (by rw [abs_of_nonneg (sq_nonneg q)]; nlinarith) M (z₀ + w)
  have hcast : (-(((q ^ 2 : ℝ)) : ℂ)) = -(q : ℂ) ^ 2 := by push_cast; ring
  rw [hcast, abs_of_nonneg (sq_nonneg q)] at hT
  have hKle : (∫ x, |x| ^ (2 * M) * ‖heatWeight (s + 1) x‖ *
      Real.exp (|(z₀ + w).im| * |x|)) ≤ K := by
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith) _ _)
      (integrable_pow_mul_heatWeight (by linarith) _ _) fun x => ?_
    have him : |(z₀ + w).im| ≤ |z₀.im| + 1 := by
      rw [Complex.add_im]
      refine (abs_add_le _ _).trans ?_
      have := (Complex.abs_im_le_norm w).trans hw1
      linarith
    dsimp only
    gcongr
  have hK0 : 0 ≤ K := integral_nonneg fun x => by positivity
  have hq2M : (q ^ 2) ^ M ≤ q ^ (k + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq0 hq1 (by simp only [M]; omega)
  have hpow : ∀ m : ℕ, q ^ (2 * m) * (q * S₁) ^ (M - 2 * m) ≤ S₁ ^ (k + 1) * q ^ (k + 1) := by
    intro m
    simp only [M]
    rw [mul_pow]
    by_cases hm : 2 * m ≤ k + 1
    · have e : q ^ (2 * m) * (q ^ (k + 1 - 2 * m) * S₁ ^ (k + 1 - 2 * m)) =
          q ^ (k + 1) * S₁ ^ (k + 1 - 2 * m) := by
        rw [← mul_assoc, ← pow_add, show 2 * m + (k + 1 - 2 * m) = k + 1 by omega]
      rw [e, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS₁ (by omega)) (by positivity)
    · rw [show k + 1 - 2 * m = 0 by omega, pow_zero, pow_zero, mul_one, mul_one]
      calc q ^ (2 * m) ≤ q ^ (k + 1) := pow_le_pow_of_le_one hq0 hq1 (by omega)
        _ = 1 * q ^ (k + 1) := (one_mul _).symm
        _ ≤ S₁ ^ (k + 1) * q ^ (k + 1) := by gcongr; exact one_le_pow₀ hS₁
  have hjetsum : ‖∑ m ∈ Finset.range M, (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
      (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w)‖ ≤
        (∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1)) * q ^ (k + 1) := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hwm : ‖w‖ ≤ rj m := hwr.trans (Finset.inf'_le _ hm)
    have hb := hjb m w hwm
    have hfac : (1 : ℝ) ≤ m.factorial := by
      have : 1 ≤ m.factorial := Nat.factorial_pos m
      exact_mod_cast this
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0, Complex.norm_natCast, ← pow_mul]
    calc q ^ (2 * m) / (m.factorial : ℝ) *
          ‖iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w‖
        ≤ q ^ (2 * m) * (|Cj m| * (q * S₁) ^ (M - 2 * m)) := by
          gcongr
          · exact div_le_self (by positivity) hfac
          · exact hb.trans (by gcongr; exact le_abs_self _)
      _ = |Cj m| * (q ^ (2 * m) * (q * S₁) ^ (M - 2 * m)) := by ring
      _ ≤ |Cj m| * (S₁ ^ (k + 1) * q ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hpow m) (abs_nonneg _)
      _ = |Cj m| * S₁ ^ (k + 1) * q ^ (k + 1) := by ring
  rw [← sum_jetPart_eq_fwd k a q σ, ← hw]
  have hsplit : riemannHeat (s + q ^ 2) (z₀ + w) -
      ∑ m ∈ Finset.range (k + 1), (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * jetPart k a m w =
      (riemannHeat (s + q ^ 2) (z₀ + w) - ∑ m ∈ Finset.range M,
        (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * iteratedDeriv (2 * m) H (z₀ + w)) +
      ∑ m ∈ Finset.range M, (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w) := by
    simp only [M, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc _ ≤ ‖riemannHeat (s + q ^ 2) (z₀ + w) - ∑ m ∈ Finset.range M,
        (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) * iteratedDeriv (2 * m) H (z₀ + w)‖ +
      ‖∑ m ∈ Finset.range M, (-(q : ℂ) ^ 2) ^ m / (m.factorial : ℂ) *
        (iteratedDeriv (2 * m) H (z₀ + w) - jetPart k a m w)‖ := norm_add_le _ _
    _ ≤ K * q ^ (k + 1) + (∑ m ∈ Finset.range M, |Cj m| * S₁ ^ (k + 1)) * q ^ (k + 1) := by
        gcongr
        refine hT.trans ?_
        calc _ ≤ K * (q ^ 2) ^ M := by gcongr
          _ ≤ K * q ^ (k + 1) := by gcongr
    _ = _ := by ring

end

end RHTower.DeBruijn
