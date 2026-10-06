import GaloisForLFunctions.RHTower.VerticalProgressionFirstMoment

/-!
# The resonant mass of the mollified first moment tends to zero

With `N = ⌊T^θ⌋` (`0 < θ ≤ ½`), `X = T^{21/16}`, `δ = T^{−31/32}`, the resonant mass

`Q(T) = Σ_{n ≥ 2, dist(u_n, ℤ) < δ} |a(n)| n^{−1/2}`

tends to `0` (`tendsto_resonantMass`). Given `ε`, fix `R₀` with `2C_d e^a (R₀/e)^{−a} s/(s−1) ≤ ε/4`
(`a = 49/100`); then for large `T` split `n` into `n ≤ R₀` (each `a(n) → 0`), `R₀ < n ≤ T^{15/16}`
(the middle-range geometric bound), `T^{15/16} < n ≤ Z = T^{θ+21/16+1/100}` (the upper-range bound,
`≪ T^{−(15/16)a} + T^{−31/32+(1−a)(θ+1.3225)}`), and `n > Z` (power decay of the cutoff,
`≪ T^{2.5θ − 2.01625}`).
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower.VerticalAP

noncomputable section

/-- `f → 0` and `c > 0` give `f ≤ c` eventually. -/
theorem eventually_le_of_tendsto_zero {f : ℝ → ℝ} (hf : Tendsto f atTop (𝓝 0)) {c : ℝ}
    (hc : 0 < c) : ∀ᶠ T in atTop, f T ≤ c :=
  ((tendsto_order.1 hf).2 c hc).mono fun _ h => h.le

/-- `T^{15/16} ≤ T^{θ + 21/16 + 1/100}` for `T ≥ 1`. -/
theorem rpow_le_rpow_of_one_le {T p q : ℝ} (hT : 1 ≤ T) (hpq : p ≤ q) : T ^ p ≤ T ^ q :=
  Real.rpow_le_rpow_of_exponent_le hT hpq

/-- **The resonant mass tends to zero.** -/
theorem tendsto_resonantMass {α γ θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) :
    Tendsto (resonantMass α γ θ) atTop (𝓝 0) := by
  classical
  set a : ℝ := 49 / 100 with ha
  have ha0 : 0 < a := by norm_num [ha]
  set Cd : ℝ := Sieve.divisorBoundConst (1 / 100) with hCd
  have hCd0 : 0 ≤ Cd := (Sieve.divisorBoundConst_pos (by norm_num)).le
  set s : ℝ := Real.exp (2 * Real.pi * a / α) with hsdef
  set s' : ℝ := Real.exp (2 * Real.pi * (1 - a) / α) with hs'def
  have hs : 1 < s := Real.one_lt_exp_iff.mpr (by positivity)
  have h1a : 0 < 1 - a := by norm_num [ha]
  have hs' : 1 < s' := Real.one_lt_exp_iff.mpr (by positivity)
  set gs : ℝ := s / (s - 1) with hgsdef
  set gs' : ℝ := s' / (s' - 1) with hgs'def
  have hgs : 0 ≤ gs := div_nonneg (by linarith) (by linarith)
  have hgs' : 0 ≤ gs' := div_nonneg (by linarith) (by linarith)
  obtain ⟨K, hK, hKb⟩ := norm_mollCoeff_le_decay (A := 400) (by norm_num)
  set S₂c : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) with hS₂c
  have hS₂c0 : 0 ≤ S₂c := tsum_nonneg fun n => by positivity
  set z : ℝ := θ + 21 / 16 + 1 / 100 with hz
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun T =>
    lt_of_lt_of_le hb (resonantMass_nonneg α γ θ T), fun b hb => ?_⟩
  set ε : ℝ := b / 2 with hεdef
  have hε : 0 < ε := by positivity
  -- the cut-off `R₀`
  have hR : Tendsto (fun R : ℝ => 2 * Cd * Real.exp a * ((R / Real.exp 1) ^ (-a) * gs)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (R / Real.exp 1) ^ (-a)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop ha0).comp (tendsto_id.atTop_div_const (Real.exp_pos 1))
    simpa using (h1.mul_const gs).const_mul (2 * Cd * Real.exp a)
  obtain ⟨R₀, hR₀2, hR₀⟩ : ∃ R₀ : ℕ, 2 ≤ R₀ ∧
      2 * Cd * Real.exp a * (((R₀ : ℝ) / Real.exp 1) ^ (-a) * gs) ≤ ε / 4 := by
    have hev := tendsto_natCast_atTop_atTop.eventually
      (eventually_le_of_tendsto_zero hR (by positivity : (0 : ℝ) < ε / 4))
    obtain ⟨R₀, h⟩ := (hev.and (eventually_ge_atTop 2)).exists
    exact ⟨R₀, h.2, h.1⟩
  -- (E2) the fixed integers `2 ≤ n ≤ R₀`
  have hE2 : ∀ᶠ T in atTop, ∑ n ∈ Finset.Icc 2 R₀,
      ‖mollCoeff (molLen θ T) (dirLen T) n‖ ≤ ε / 4 := by
    have h := tendsto_finsetSum (Finset.Icc 2 R₀) fun n hn =>
      (tendsto_mollCoeff_of_two_le (tendsto_molLen hθ0) tendsto_dirLen
        (Finset.mem_Icc.mp hn).1).norm
    simp only [norm_zero, Finset.sum_const_zero] at h
    exact eventually_le_of_tendsto_zero h (by positivity)
  -- (E3), (E4) the resonance width
  have hδlim : Tendsto (fun T : ℝ => T ^ (-(31 / 32 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_of_neg (by norm_num)
  have hE3 : ∀ᶠ T : ℝ in atTop, 2 * Real.pi * T ^ (-(31 / 32 : ℝ)) / α ≤ 1 := by
    refine eventually_le_of_tendsto_zero ?_ one_pos
    simpa [mul_div_assoc] using (hδlim.const_mul (2 * Real.pi)).div_const α
  have hE4 : ∀ᶠ T : ℝ in atTop, 2 * Real.exp 1 * (2 * Real.pi * T ^ (-(31 / 32 : ℝ)) / α) *
      (Real.exp 1 * T ^ (15 / 16 : ℝ)) ≤ 1 := by
    have hlim : Tendsto (fun T : ℝ => 2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 *
        T ^ (-(1 / 32 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_of_neg (by norm_num : -(1 / 32 : ℝ) < 0)).const_mul
        (2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1)
    filter_upwards [eventually_le_of_tendsto_zero hlim one_pos, eventually_gt_atTop 0]
      with T hT hT0
    calc 2 * Real.exp 1 * (2 * Real.pi * T ^ (-(31 / 32 : ℝ)) / α) *
          (Real.exp 1 * T ^ (15 / 16 : ℝ))
        = 2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 *
            (T ^ (-(31 / 32 : ℝ)) * T ^ (15 / 16 : ℝ)) := by ring
      _ = 2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 * T ^ (-(1 / 32 : ℝ)) := by
          rw [← Real.rpow_add hT0]; norm_num
      _ ≤ 1 := hT
  -- (E5) the upper range
  have hE5 : ∀ᶠ T : ℝ in atTop, Cd * Real.exp a *
      ((T ^ (15 / 16 : ℝ) / Real.exp 1) ^ (-a) * gs +
        2 * Real.exp 1 * (2 * Real.pi * T ^ (-(31 / 32 : ℝ)) / α) *
          ((Real.exp 1 * T ^ z) ^ (1 - a) * gs')) ≤ ε / 4 := by
    have hA : Tendsto (fun T : ℝ => (T ^ (15 / 16 : ℝ) / Real.exp 1) ^ (-a)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop ha0).comp
        ((tendsto_rpow_atTop (by norm_num)).atTop_div_const (Real.exp_pos 1))
    have hexp : -(31 / 32 : ℝ) + z * (1 - a) < 0 := by
      rw [hz, ha]; nlinarith
    have hB : Tendsto (fun T : ℝ => 2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 ^ (1 - a) *
        T ^ (-(31 / 32 : ℝ) + z * (1 - a))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_of_neg hexp).const_mul
        (2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 ^ (1 - a))
    have hsum : Tendsto (fun T : ℝ => Cd * Real.exp a *
        ((T ^ (15 / 16 : ℝ) / Real.exp 1) ^ (-a) * gs +
          2 * Real.exp 1 * (2 * Real.pi / α) * Real.exp 1 ^ (1 - a) *
            T ^ (-(31 / 32 : ℝ) + z * (1 - a)) * gs')) atTop (𝓝 0) := by
      simpa using ((hA.mul_const gs).add (hB.mul_const gs')).const_mul (Cd * Real.exp a)
    filter_upwards [eventually_le_of_tendsto_zero hsum (by positivity : (0 : ℝ) < ε / 4),
      eventually_gt_atTop 0] with T hT hT0
    refine le_trans (le_of_eq ?_) hT
    congr 2
    rw [Real.mul_rpow (Real.exp_pos 1).le (by positivity), ← Real.rpow_mul hT0.le,
      Real.rpow_add hT0]
    ring
  -- (E6) the tail
  have hE6 : ∀ᶠ T : ℝ in atTop, T ^ θ * (K * T ^ (400 * (θ + 21 / 16))) *
      (T ^ z) ^ (-((400 : ℝ) - 3 / 2)) * S₂c ≤ ε / 4 := by
    have hexp : θ + 400 * (θ + 21 / 16) + z * (-((400 : ℝ) - 3 / 2)) < 0 := by
      rw [hz]; nlinarith
    have hlim : Tendsto (fun T : ℝ => K * S₂c * T ^ (θ + 400 * (θ + 21 / 16) +
        z * (-((400 : ℝ) - 3 / 2)))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_of_neg hexp).const_mul (K * S₂c)
    filter_upwards [eventually_le_of_tendsto_zero hlim (by positivity : (0 : ℝ) < ε / 4),
      eventually_gt_atTop 0] with T hT hT0
    refine le_trans (le_of_eq ?_) hT
    rw [← Real.rpow_mul hT0.le, Real.rpow_add hT0, Real.rpow_add hT0]
    ring
  filter_upwards [hE2, hE3, hE4, hE5, hE6, eventually_ge_atTop 1] with T h2 h3 h4 h5 h6 hT1
  have hT0 : 0 < T := by linarith
  set Nm : ℕ := molLen θ T with hNm
  set X : ℝ := dirLen T with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hT0 _
  set δ : ℝ := T ^ (-(31 / 32 : ℝ)) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  set Y : ℝ := T ^ (15 / 16 : ℝ) with hYdef
  have hY0 : 0 < Y := by positivity
  set Zt : ℝ := T ^ z with hZtdef
  have hYZ : Y ≤ Zt := Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hz]; linarith)
  have hZ1 : 1 ≤ Zt := Real.one_le_rpow hT1 (by rw [hz]; linarith)
  set f : ℕ → ℝ := fun n => ‖mollCoeff Nm X n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) with hfdef
  have hfC : ∀ n : ℕ, 1 ≤ n → f n ≤ Cd * (n : ℝ) ^ (-a) := fun n hn =>
    norm_mollCoeff_mul_rpow_le Nm hX hn
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  suffices hsuff : resonantMass α γ θ T ≤ ε by linarith
  unfold resonantMass
  refine Real.tsum_le_of_sum_le (fun m => by split_ifs <;> positivity) fun U => ?_
  set S : Finset ℕ := U.map ⟨fun m => m + 2, add_left_injective 2⟩ with hSdef
  have hS2 : ∀ n ∈ S, 2 ≤ n := by
    intro n hn
    rw [hSdef, Finset.mem_map] at hn
    obtain ⟨m, _, rfl⟩ := hn
    simp
  set res : ℕ → Prop := fun n => ∃ j : ℤ, |resFreq α γ n - j| < δ with hres
  have hU : (∑ m ∈ U, if (∃ j : ℤ, |resFreq α γ (m + 2) - j| < T ^ (-(31 / 32 : ℝ))) then
      ‖mollCoeff (molLen θ T) (dirLen T) (m + 2)‖ * ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) else 0) =
      ∑ n ∈ S, if res n then f n else 0 := by
    rw [hSdef, Finset.sum_map]
    rfl
  rw [hU]
  -- the four ranges
  set t₁ : ℕ → ℝ := fun n => if n ≤ R₀ then ‖mollCoeff Nm X n‖ else 0 with ht₁
  set t₂ : ℕ → ℝ := fun n => if (R₀ : ℝ) < n ∧ (n : ℝ) ≤ Y ∧ res n then f n else 0 with ht₂
  set t₃ : ℕ → ℝ := fun n => if Y < n ∧ (n : ℝ) ≤ Zt ∧ res n then f n else 0 with ht₃
  set t₄ : ℕ → ℝ := fun n => if Zt < n then f n else 0 with ht₄
  have hpt : ∀ n ∈ S, (if res n then f n else 0) ≤ t₁ n + t₂ n + t₃ n + t₄ n := by
    intro n hn
    have hn2 := hS2 n hn
    have h1n : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have ht0 : 0 ≤ t₁ n ∧ 0 ≤ t₂ n ∧ 0 ≤ t₃ n ∧ 0 ≤ t₄ n := by
      simp only [ht₁, ht₂, ht₃, ht₄]
      refine ⟨by split_ifs <;> positivity, by split_ifs <;> [exact hf0 n; rfl],
        by split_ifs <;> [exact hf0 n; rfl], by split_ifs <;> [exact hf0 n; rfl]⟩
    obtain ⟨g1, g2, g3, g4⟩ := ht0
    by_cases hr : res n
    · rw [if_pos hr]
      by_cases hR : n ≤ R₀
      · have : f n ≤ t₁ n := by
          simp only [ht₁, if_pos hR, hfdef]
          have hle : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos h1n (by norm_num)
          calc ‖mollCoeff Nm X n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖mollCoeff Nm X n‖ * 1 :=
                mul_le_mul_of_nonneg_left hle (norm_nonneg _)
            _ = ‖mollCoeff Nm X n‖ := mul_one _
        linarith
      · have hR' : (R₀ : ℝ) < n := by exact_mod_cast not_le.mp hR
        by_cases hYn : (n : ℝ) ≤ Y
        · have : t₂ n = f n := by simp only [ht₂]; rw [if_pos ⟨hR', hYn, hr⟩]
          linarith
        · by_cases hZn : (n : ℝ) ≤ Zt
          · have : t₃ n = f n := by
              simp only [ht₃]; rw [if_pos ⟨not_le.mp hYn, hZn, hr⟩]
            linarith
          · have : t₄ n = f n := by simp only [ht₄]; rw [if_pos (not_le.mp hZn)]
            linarith
    · rw [if_neg hr]; linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  simp only [Finset.sum_add_distrib]
  -- range 1
  have hs1 : ∑ n ∈ S, t₁ n ≤ ε / 4 := by
    simp only [ht₁]
    rw [← Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => norm_nonneg _) h2
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨hS2 n hn.1, hn.2⟩
  -- range 2
  have hs2 : ∑ n ∈ S, t₂ n ≤ ε / 4 := by
    simp only [ht₂]
    rw [← Finset.sum_filter]
    refine le_trans ?_ hR₀
    refine sum_resonant_middle_le (γ := γ) hα hδ0 h3 (by positivity) h4 _ (fun n hn => ?_) f hCd0 ha0
      (fun n hn => hfC n ?_)
    · rw [Finset.mem_filter] at hn
      exact ⟨by have := hS2 n hn.1; omega, hn.2.1, hn.2.2.1, hn.2.2.2⟩
    · rw [Finset.mem_filter] at hn
      have := hS2 n hn.1; omega
  -- range 3
  have hs3 : ∑ n ∈ S, t₃ n ≤ ε / 4 := by
    simp only [ht₃]
    rw [← Finset.sum_filter]
    refine le_trans ?_ h5
    refine sum_resonant_upper_le (γ := γ) hα hδ0 h3 hY0 hYZ _ (fun n hn => ?_) f hCd0 ha0
      (by norm_num [ha]) (fun n hn => hfC n ?_)
    · rw [Finset.mem_filter] at hn
      exact ⟨by have := hS2 n hn.1; omega, hn.2.1, hn.2.2.1, hn.2.2.2⟩
    · rw [Finset.mem_filter] at hn
      have := hS2 n hn.1; omega
  -- range 4
  have hs4 : ∑ n ∈ S, t₄ n ≤ ε / 4 := by
    simp only [ht₄]
    rw [← Finset.sum_filter]
    refine le_trans ?_ h6
    refine sum_tail_le hZ1 (by positivity) (by norm_num) _ (fun n hn => (Finset.mem_filter.mp hn).2)
      f fun n hn => ?_
    have hnZ := (Finset.mem_filter.mp hn).2
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : 1 ≤ n := by
      have := hS2 n (Finset.mem_filter.mp hn).1; omega
    have hdec := hKb Nm hX hn1
    have hNm : (Nm : ℝ) ≤ T ^ θ := molLen_le hT0.le
    have hbase : (Nm : ℝ) * X / n ≤ T ^ (θ + 21 / 16) / n := by
      rw [Real.rpow_add hT0]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNm hX.le) hn0.le
    have hpow : ((Nm : ℝ) * X / n) ^ (400 : ℝ) ≤ T ^ (400 * (θ + 21 / 16)) * (n : ℝ) ^ (-(400 : ℝ)) := by
      calc ((Nm : ℝ) * X / n) ^ (400 : ℝ) ≤ (T ^ (θ + 21 / 16) / n) ^ (400 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hbase (by norm_num)
        _ = T ^ (400 * (θ + 21 / 16)) * (n : ℝ) ^ (-(400 : ℝ)) := by
            rw [Real.div_rpow (by positivity) hn0.le, ← Real.rpow_mul hT0.le,
              Real.rpow_neg hn0.le, mul_comm (θ + 21 / 16), div_eq_mul_inv]
    calc f n = ‖mollCoeff Nm X n‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := rfl
      _ ≤ (Nm * (K * ((Nm : ℝ) * X / n) ^ (400 : ℝ))) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hdec (by positivity)
      _ ≤ (T ^ θ * (K * (T ^ (400 * (θ + 21 / 16)) * (n : ℝ) ^ (-(400 : ℝ))))) *
            (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          gcongr
      _ = T ^ θ * (K * T ^ (400 * (θ + 21 / 16))) * (n : ℝ) ^ (-((400 : ℝ) + 1 / 2)) := by
          rw [show -((400 : ℝ) + 1 / 2) = -(400 : ℝ) + -(1 / 2) by ring, Real.rpow_add hn0]
          ring
  linarith

end

end RHTower.VerticalAP
