import GaloisForLFunctions.RHTower.FamilyCellTheorem

/-!
# Two thirds of the zeros of the nontrivial Dirichlet L-functions modulo a prime

For every `ε > 0` and all large `T`, uniformly in primes `q ≤ T^{1−ε}` (`family_two_thirds`):

`(2/3 − ε) ∑_{χ ≠ 1 (mod q)} N_χ(T, 2T) ≤ ∑_{χ ≠ 1 (mod q)} N₀*_χ(T, 2T)`,

i.e. at least `2/3 − ε` of the zeros with `T < γ ≤ 2T` of the family of the `q − 2` nontrivial characters
lie on the critical line (and are counted without multiplicity in `N₀*`).

Moduli `q ≤ T^{κ₀}` are covered character by character by the modulus-uniform Theorem E
(`thmE_uniform_two_thirds`).  Larger moduli fall in one of finitely many cells `T^{κ_j} ≤ q ≤ T^{κ_j + δ}`,
where the family certificate (`family_cell`) runs at bandwidth `λ_j = 1 + κ_j − δ`: the prime polynomials
reach `X = (T/2π)^{λ_j} ≤ q T^{1−δ}`, so the bandwidth relative to the analytic conductor `qT` is
`λ₁ ≥ 1 − 2δ − 5/l` and `H(λ₁) ≥ 2/3 − 4δ − 10/l` (`lam1q_mesh_bounds`, `Hfun_one_sub_ge`).
-/

open MeasureTheory Real Set Filter Topology Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly

noncomputable section

namespace RHTower

/-- `H(1 − x) ≥ 2/3 − 2x` for `0 ≤ x ≤ 1/2`. -/
theorem Hfun_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : 2 / 3 - 2 * x ≤ Hfun (1 - x) := by
  unfold Hfun
  have h1 : 0 < 1 - x := by linarith
  have h2 : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- **The relative bandwidth in a mesh cell.**  For `T^κ ≤ q ≤ T^{κ+δ}` and `λ = 1 + κ − δ`,
`1 − (2δ + 5/l) ≤ λ₁ ≤ 1`. -/
theorem lam1q_mesh_bounds {κ δ : ℝ} {q : ℕ} {T : ℝ} (hq : 1 ≤ q) (hT : 0 < T) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hl : 20 ≤ Zeta23.l T)
    (hlT : Zeta23.l T ≤ Real.log T) (hlT2 : Real.log T ≤ Zeta23.l T + 2)
    (hqlo : κ * Real.log T ≤ Real.log q) (hqhi : Real.log q ≤ (κ + δ) * Real.log T) :
    1 - (2 * δ + 5 / Zeta23.l T) ≤ lam1q (stdParams (1 + κ - δ)) q T
      ∧ lam1q (stdParams (1 + κ - δ)) q T ≤ 1 := by
  obtain ⟨l, hldef⟩ : ∃ x : ℝ, x = Zeta23.l T := ⟨_, rfl⟩
  rw [← hldef] at hl hlT hlT2 ⊢
  have hl0 : 0 < l := by linarith
  have hlam : lam1q (stdParams (1 + κ - δ)) q T = (1 + κ - δ) * l / ell1q q T := by
    rw [hldef]; rfl
  have he := ell1q_eq_log_add hq hT
  rw [← hldef] at he
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have helo : Real.log q + l ≤ ell1q q T := by rw [he]; linarith
  have hehi : ell1q q T ≤ Real.log q + l + 1 := by rw [he]; linarith
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have he0 : 0 < ell1q q T := by linarith
  have hκl : κ * l ≤ κ * Real.log T := mul_le_mul_of_nonneg_left hlT hκ0
  rw [hlam]
  constructor
  · obtain ⟨x, hx⟩ : ∃ y : ℝ, y = 2 * δ + 5 / l := ⟨_, rfl⟩
    rw [le_div_iff₀ he0]
    rcases le_or_gt (1 - x) 0 with hneg | hpos
    · have : 0 ≤ (1 + κ - δ) * l := mul_nonneg (by linarith) hl0.le
      nlinarith
    · -- `ℓ₁ ≤ a l + 5` with `a = 1 + κ + δ`
      have hκT : (κ + δ) * Real.log T ≤ (κ + δ) * (l + 2) :=
        mul_le_mul_of_nonneg_left hlT2 (by linarith)
      have hD : ell1q q T ≤ (1 + κ + δ) * l + 5 := by nlinarith
      have h1 : (1 - x) * ell1q q T ≤ (1 - x) * ((1 + κ + δ) * l + 5) :=
        mul_le_mul_of_nonneg_left hD hpos.le
      have hxl : x * l = 2 * δ * l + 5 := by rw [hx]; field_simp
      have h2 : (1 - x) * ((1 + κ + δ) * l + 5)
          = (1 + κ + δ) * l + 5 - (1 + κ + δ) * (x * l) - 5 * x := by ring
      rw [hxl] at h2
      have hx0 : 0 ≤ x := by rw [hx]; positivity
      have h3 : 0 ≤ (κ + δ) * (2 * δ * l) := by positivity
      nlinarith
  · rw [div_le_one he0]
    nlinarith

/-- **Two thirds of the zeros of the family `{L(s, χ) : χ ≠ 1 (mod q)}`, `q ≤ T^{1−ε}` prime, lie on the
critical line.** -/
theorem family_two_thirds :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (q : ℕ) [NeZero q], q.Prime → (q : ℝ) ≤ T ^ (1 - ε) →
      (2 / 3 - ε) * ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ)
        ≤ ∑ χ ∈ nontrivChars q, (N0starL χ T (2 * T) : ℝ) := by
  suffices H : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (q : ℕ) [NeZero q], q.Prime →
      (q : ℝ) ≤ T ^ (1 - ε) →
      (2 / 3 - ε) * ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ)
        ≤ ∑ χ ∈ nontrivChars q, (N0starL χ T (2 * T) : ℝ) by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := H (min ε (1 / 2)) (lt_min hε (by norm_num)) (min_le_right _ _)
    refine ⟨max T₀ 1, fun T hT q _ hp hqT => ?_⟩
    have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    have hm := min_le_left ε (1 / 2)
    have h := hT₀ T ((le_max_left _ _).trans hT) q hp
      (hqT.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)))
    have hN0 : 0 ≤ ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ) :=
      Finset.sum_nonneg fun χ _ => Nat.cast_nonneg _
    exact (mul_le_mul_of_nonneg_right (by linarith) hN0).trans h
  intro ε hε hε2
  obtain ⟨κ₀, hκ₀, T₁, h1⟩ := thmE_uniform_two_thirds ε hε
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = min (ε / 16) (1 / 8) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (by positivity) (by norm_num)
  have hδ8 : δ ≤ 1 / 8 := by rw [hδdef]; exact min_le_right _ _
  have hδε : δ ≤ ε / 16 := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨J, hJdef⟩ : ∃ n : ℕ, n = ⌈1 / δ⌉₊ + 1 := ⟨_, rfl⟩
  -- the cells
  have hcells : ∀ j ∈ Finset.range J, ∀ᶠ T : ℝ in atTop, κ₀ + j * δ < 1 →
      ∀ (q : ℕ) [NeZero q], q.Prime → (q : ℝ) ≤ T ^ (min (κ₀ + j * δ + δ) (1 - ε)) →
        T ^ (κ₀ + j * δ) ≤ q →
        (Hfun (lam1q (stdParams (1 + (κ₀ + j * δ) - δ)) q T) - ε / 2)
            * ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ)
          ≤ ∑ χ ∈ nontrivChars q, (N0starL χ T (2 * T) : ℝ) := by
    intro j _
    by_cases hk : κ₀ + j * δ < 1
    · have hj0 : (0 : ℝ) ≤ j * δ := by positivity
      obtain ⟨T₀, hT₀⟩ := family_cell (lam := 1 + (κ₀ + j * δ) - δ) (κlo := κ₀ + j * δ)
        (κhi := min (κ₀ + j * δ + δ) (1 - ε)) (by linarith) (by linarith) (by linarith)
        (by linarith) ((min_le_right _ _).trans_lt (by linarith))
        (le_min (by linarith) (by linarith)) (ε / 2) (by positivity)
      exact eventually_atTop.mpr ⟨T₀, fun T hT _ q _ hp hq1 hq2 => hT₀ T hT q hp hq1 hq2⟩
    · exact Filter.Eventually.of_forall fun T h => absurd h hk
  have hall := (Filter.eventually_all_finset (Finset.range J)).mpr hcells
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp ((hall.and eventually_l_bounds).and
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 * (40 / ε + 20))))
  refine ⟨max (max T₁ T₂) (4 * π ^ 2), fun T hT q _ hp hqT => ?_⟩
  obtain ⟨⟨hcellT, hlog1, hl1, hlo, hhi⟩, hlogε⟩ := hT₂ T ((le_max_right _ _).trans
    ((le_max_left _ _).trans hT))
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT4 : 4 * π ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hπ := Real.pi_gt_three
  have hT0 : 0 < T := by nlinarith
  have hT1 : 1 < T := by nlinarith
  have hq1 : 1 < q := hp.one_lt
  have hprim : ∀ χ ∈ nontrivChars q, χ.IsPrimitive := fun χ hχ =>
    isPrimitive_of_prime hp χ (Finset.mem_filter.mp hχ).2
  have hN0 : 0 ≤ ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ) :=
    Finset.sum_nonneg fun χ _ => Nat.cast_nonneg _
  by_cases hsmall : (q : ℝ) ≤ T ^ κ₀
  · -- small moduli, one character at a time
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun χ hχ => h1 T hTT₁ q χ hq1 hsmall (hprim χ hχ)
  · -- a mesh cell
    have hbig : T ^ κ₀ < q := lt_of_not_ge hsmall
    obtain ⟨lT, hlTdef⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
    rw [← hlTdef] at hlog1 hlo hhi hlogε
    have hlT0 : 0 < lT := by linarith
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hp.pos
    have hlogq_hi : Real.log q ≤ (1 - ε) * lT := by
      have h := Real.log_le_log hqpos hqT
      rwa [Real.log_rpow hT0, ← hlTdef] at h
    have hlogq_lo : κ₀ * lT < Real.log q := by
      have h := Real.log_lt_log (by positivity) hbig
      rwa [Real.log_rpow hT0, ← hlTdef] at h
    obtain ⟨t, htdef⟩ : ∃ x : ℝ, x = Real.log q / lT := ⟨_, rfl⟩
    have ht0 : κ₀ < t := by rw [htdef, lt_div_iff₀ hlT0]; linarith
    have ht1 : t ≤ 1 - ε := by rw [htdef, div_le_iff₀ hlT0]; linarith
    have htq : t * lT = Real.log q := by rw [htdef]; field_simp
    obtain ⟨j, hjdef⟩ : ∃ n : ℕ, n = ⌊(t - κ₀) / δ⌋₊ := ⟨_, rfl⟩
    have hx0 : 0 ≤ (t - κ₀) / δ := div_nonneg (by linarith) hδ0.le
    have hj1 : (j : ℝ) ≤ (t - κ₀) / δ := by rw [hjdef]; exact Nat.floor_le hx0
    have hj2 : (t - κ₀) / δ < j + 1 := by rw [hjdef]; exact Nat.lt_floor_add_one _
    have hκj_le : κ₀ + j * δ ≤ t := by
      have := mul_le_mul_of_nonneg_right hj1 hδ0.le
      rw [div_mul_cancel₀ _ hδ0.ne'] at this; linarith
    have hκj_lt : t < κ₀ + j * δ + δ := by
      have := mul_lt_mul_of_pos_right hj2 hδ0
      rw [div_mul_cancel₀ _ hδ0.ne'] at this; linarith
    have hjJ : j ∈ Finset.range J := by
      rw [Finset.mem_range, hJdef]
      have h1' : (t - κ₀) / δ ≤ 1 / δ := div_le_div_of_nonneg_right (by linarith) hδ0.le
      have h2' : j ≤ ⌊1 / δ⌋₊ := by rw [hjdef]; exact Nat.floor_le_floor h1'
      have h3' := Nat.floor_le_ceil (1 / δ : ℝ)
      omega
    have hk1 : κ₀ + j * δ < 1 := by linarith
    have hTq : T ^ (κ₀ + j * δ) ≤ q := by
      rw [Real.rpow_def_of_pos hT0, ← Real.exp_log hqpos, ← hlTdef]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hκj_le hlT0.le
      linarith
    have hqT2 : (q : ℝ) ≤ T ^ (min (κ₀ + j * δ + δ) (1 - ε)) := by
      rcases le_total (κ₀ + j * δ + δ) (1 - ε) with h | h
      · rw [min_eq_left h, Real.rpow_def_of_pos hT0, ← hlTdef]
        rw [← Real.exp_log hqpos]
        apply Real.exp_le_exp.mpr
        have := mul_lt_mul_of_pos_left hκj_lt hlT0
        linarith
      · rw [min_eq_right h]; exact hqT
    have hcell := hcellT j hjJ hk1 q hp hqT2 hTq
    -- the relative bandwidth
    have hlT2 : lT ≤ Zeta23.l T + 2 := by
      have e : Zeta23.l T = Real.log T - Real.log (2 * π) := by
        unfold Zeta23.l; rw [Real.log_div hT0.ne' (by positivity)]
      have := log_two_pi_le_two
      rw [e, ← hlTdef]; linarith
    have h40 : 0 ≤ 40 / ε := by positivity
    have hl20 : 20 ≤ Zeta23.l T := by linarith
    have hκj0 : 0 ≤ κ₀ + j * δ := by positivity
    have hqlo : (κ₀ + j * δ) * lT ≤ Real.log q := by
      have := mul_le_mul_of_nonneg_left hκj_le hlT0.le; linarith
    have hqhi : Real.log q ≤ (κ₀ + j * δ + δ) * lT := by
      have := mul_lt_mul_of_pos_left hκj_lt hlT0; linarith
    obtain ⟨hlam_lo, hlam_hi⟩ := lam1q_mesh_bounds (κ := κ₀ + j * δ) (δ := δ) hq1.le hT0 hκj0 hk1
      hδ0 hδ8 hl20 (by rw [← hlTdef]; exact hhi) (by rw [← hlTdef]; exact hlT2)
      (by rw [← hlTdef]; exact hqlo) (by rw [← hlTdef]; linarith)
    obtain ⟨x, hxdef⟩ : ∃ y : ℝ, y = 2 * δ + 5 / Zeta23.l T := ⟨_, rfl⟩
    rw [← hxdef] at hlam_lo
    have hx0 : 0 ≤ x := by rw [hxdef]; positivity
    have h5l : 5 / Zeta23.l T ≤ 1 / 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have h10l : 10 / Zeta23.l T ≤ ε / 4 := by
      rw [div_le_iff₀ (by linarith)]
      have : 40 / ε ≤ Zeta23.l T := by linarith
      rw [div_le_iff₀ hε] at this; linarith
    have hx12 : x ≤ 1 / 2 := by rw [hxdef]; linarith
    have hxε : 2 * x ≤ ε / 2 := by
      have e : 2 * x = 4 * δ + 10 / Zeta23.l T := by rw [hxdef]; ring
      linarith
    have hH : 2 / 3 - ε / 2 ≤ Hfun (lam1q (stdParams (1 + (κ₀ + j * δ) - δ)) q T) := by
      have h1' := Hfun_one_sub_ge hx0 hx12
      have h2' := Hfun_mono (by linarith : (0:ℝ) < 1 - x) hlam_lo hlam_hi
      linarith
    have := mul_le_mul_of_nonneg_right
      (by linarith : 2 / 3 - ε ≤ Hfun (lam1q (stdParams (1 + (κ₀ + j * δ) - δ)) q T) - ε / 2) hN0
    exact this.trans hcell

end RHTower
