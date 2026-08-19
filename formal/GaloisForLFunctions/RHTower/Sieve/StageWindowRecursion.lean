import GaloisForLFunctions.RHTower.Sieve.LadderCharacterRecursion

/-!
# One stage of the order recursion

A stage begins with a single *transition* window of length `b^{θ+δ}`, long enough to absorb the one
coordinate the previous stage did not control, and continues with ordinary windows of length `x^θ`.
Because `δ` may be taken as small as `(1-θ)/(J+1)`, the transition window is barely longer than an
ordinary one, and the level bounds inside it are `x^{(j+1)(θ+δ)}`.
-/

noncomputable section

open Filter GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- Base and length of the `k`-th window of a stage: the first has length `b^{θ+δ}`, the rest
`x^θ`. -/
def stageWindow (θ δ b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (b, b ^ (θ + δ))
  | (k + 1) =>
      let s := stageWindow θ δ b k
      (s.1 + s.2, (s.1 + s.2) ^ θ)

/-- The base point of the `k`-th window of the stage. -/
def stageBaseAt (θ δ b : ℝ) (k : ℕ) : ℝ := (stageWindow θ δ b k).1

/-- The length of the `k`-th window of the stage. -/
def stageLenAt (θ δ b : ℝ) (k : ℕ) : ℝ := (stageWindow θ δ b k).2

theorem stageBaseAt_zero (θ δ b : ℝ) : stageBaseAt θ δ b 0 = b := rfl

theorem stageLenAt_zero (θ δ b : ℝ) : stageLenAt θ δ b 0 = b ^ (θ + δ) := rfl

theorem stageBaseAt_succ (θ δ b : ℝ) (k : ℕ) :
    stageBaseAt θ δ b (k + 1) = stageBaseAt θ δ b k + stageLenAt θ δ b k := rfl

theorem stageLenAt_succ (θ δ b : ℝ) (k : ℕ) :
    stageLenAt θ δ b (k + 1) = (stageBaseAt θ δ b (k + 1)) ^ θ := rfl

theorem stageLenAt_pos {θ δ b : ℝ} (hb : 0 < b) (k : ℕ) : 0 < stageLenAt θ δ b k := by
  cases k with
  | zero =>
      rw [stageLenAt_zero]
      exact Real.rpow_pos_of_pos hb _
  | succ k =>
      rw [stageLenAt_succ]
      refine Real.rpow_pos_of_pos ?_ θ
      rw [stageBaseAt_succ]
      induction k with
      | zero =>
          rw [stageBaseAt_zero, stageLenAt_zero]
          have := Real.rpow_pos_of_pos hb (θ + δ)
          linarith
      | succ k ih =>
          have h1 : 0 < stageBaseAt θ δ b (k + 1) := by
            rw [stageBaseAt_succ]
            exact ih
          have h2 : 0 < stageLenAt θ δ b (k + 1) := by
            rw [stageLenAt_succ]
            exact Real.rpow_pos_of_pos h1 θ
          rw [stageBaseAt_succ]
          linarith

theorem stageBaseAt_pos {θ δ b : ℝ} (hb : 0 < b) (k : ℕ) : 0 < stageBaseAt θ δ b k := by
  induction k with
  | zero =>
      rw [stageBaseAt_zero]
      exact hb
  | succ k ih =>
      rw [stageBaseAt_succ]
      have := stageLenAt_pos hb (θ := θ) (δ := δ) k
      linarith

theorem stageBaseAt_le_succ {θ δ b : ℝ} (hb : 0 < b) (k : ℕ) :
    stageBaseAt θ δ b k ≤ stageBaseAt θ δ b (k + 1) := by
  rw [stageBaseAt_succ]
  have := stageLenAt_pos hb (θ := θ) (δ := δ) k
  linarith

theorem stageBaseAt_mono {θ δ b : ℝ} (hb : 0 < b) : Monotone (stageBaseAt θ δ b) :=
  monotone_nat_of_le_succ (stageBaseAt_le_succ hb)

theorem stageBaseAt_ge {θ δ b : ℝ} (hb : 0 < b) (k : ℕ) : b ≤ stageBaseAt θ δ b k := by
  have := stageBaseAt_mono hb (θ := θ) (δ := δ) (Nat.zero_le k)
  rwa [stageBaseAt_zero] at this

/-- Every window of the stage is at least the `θ`-power of its base. -/
theorem rpow_le_stageLenAt {θ δ b : ℝ} (hb : 1 ≤ b) (hδ : 0 ≤ δ) (k : ℕ) :
    (stageBaseAt θ δ b k) ^ θ ≤ stageLenAt θ δ b k := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  cases k with
  | zero =>
      rw [stageBaseAt_zero, stageLenAt_zero]
      exact Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  | succ k =>
      rw [stageLenAt_succ]

/-! ## The recursion inside a stage -/

open scoped Classical in
/-- The phases after `k` windows of the stage. -/
noncomputable def stageChar (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) (u₀ : ℕ → ℂ) : ℕ → (ℕ → ℂ)
  | 0 => u₀
  | (k + 1) =>
      if h : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ k) (stageBaseAt θ δ b k)
          (stageLenAt θ δ b k) c then
        fun m => if m ∈ windowPrimes (stageBaseAt θ δ b k)
            (stageBaseAt θ δ b k + stageLenAt θ δ b k) then h.choose m
          else stageChar J dq θ δ b u₀ k m
      else stageChar J dq θ δ b u₀ k

theorem stageChar_zero (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) (u₀ : ℕ → ℂ) : stageChar J dq θ δ b u₀ 0 = u₀ := rfl

open scoped Classical in
theorem stageChar_succ (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) (u₀ : ℕ → ℂ) (k : ℕ) :
    stageChar J dq θ δ b u₀ (k + 1) =
      if h : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ k) (stageBaseAt θ δ b k)
          (stageLenAt θ δ b k) c then
        fun m => if m ∈ windowPrimes (stageBaseAt θ δ b k)
            (stageBaseAt θ δ b k + stageLenAt θ δ b k) then h.choose m
          else stageChar J dq θ δ b u₀ k m
      else stageChar J dq θ δ b u₀ k := rfl

theorem norm_stageChar (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) {u₀ : ℕ → ℂ} (hu₀ : ∀ n, ‖u₀ n‖ = 1)
    (k : ℕ) :
    ∀ n : ℕ, ‖stageChar J dq θ δ b u₀ k n‖ = 1 := by
  classical
  induction k with
  | zero =>
      intro n
      rw [stageChar_zero]
      exact hu₀ n
  | succ k ih =>
      intro n
      rw [stageChar_succ]
      by_cases h : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ k) (stageBaseAt θ δ b k)
          (stageLenAt θ δ b k) c
      · rw [dif_pos h]
        by_cases hmem : n ∈ windowPrimes (stageBaseAt θ δ b k)
            (stageBaseAt θ δ b k + stageLenAt θ δ b k)
        · simp only [if_pos hmem]
          exact (h.choose_spec).1 n hmem
        · simp only [if_neg hmem]
          exact ih n
      · rw [dif_neg h]
        exact ih n

theorem stageChar_succ_apply_of_le (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) (u₀ : ℕ → ℂ) (k : ℕ) {n : ℕ}
    (hn : (n : ℝ) ≤ stageBaseAt θ δ b k) :
    stageChar J dq θ δ b u₀ (k + 1) n = stageChar J dq θ δ b u₀ k n := by
  classical
  rw [stageChar_succ]
  by_cases h : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ k) (stageBaseAt θ δ b k)
      (stageLenAt θ δ b k) c
  · rw [dif_pos h]
    have hnot : n ∉ windowPrimes (stageBaseAt θ δ b k)
        (stageBaseAt θ δ b k + stageLenAt θ δ b k) := by
      intro hmem
      have hmem' := Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1
      have h1 : ⌊stageBaseAt θ δ b k⌋₊ < n := hmem'.1
      have h2 : n ≤ ⌊stageBaseAt θ δ b k⌋₊ := Nat.le_floor hn
      omega
    simp only [if_neg hnot]
  · rw [dif_neg h]

theorem stageChar_stable (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 0 < b) (u₀ : ℕ → ℂ) {n k : ℕ}
    (m : ℕ)
    (hkm : k ≤ m) (hn : (n : ℝ) ≤ stageBaseAt θ δ b k) :
    stageChar J dq θ δ b u₀ m n = stageChar J dq θ δ b u₀ k n := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.1 hkm
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hlt
        have hle : (n : ℝ) ≤ stageBaseAt θ δ b m := le_trans hn (stageBaseAt_mono hb hkm')
        rw [stageChar_succ_apply_of_le J dq θ δ b u₀ m hle, ih hkm']
      · have : k = m + 1 := le_antisymm hkm hge
        rw [this]

theorem stageBaseAt_ge_index {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ) (k : ℕ) :
    (k : ℝ) ≤ stageBaseAt θ δ b k := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  induction k with
  | zero =>
      rw [stageBaseAt_zero]
      simp only [Nat.cast_zero]
      linarith
  | succ k ih =>
      have hstep : (1:ℝ) ≤ stageLenAt θ δ b k := by
        cases k with
        | zero =>
            rw [stageLenAt_zero]
            exact Real.one_le_rpow hb (by linarith)
        | succ k =>
            rw [stageLenAt_succ]
            exact Real.one_le_rpow (le_trans hb (stageBaseAt_ge hb0 (k + 1))) hθ0
      rw [stageBaseAt_succ]
      push_cast
      linarith

/-- The limiting phases of one stage. -/
noncomputable def stageLimit (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) (u₀ : ℕ → ℂ) : ℕ → ℂ :=
  fun n => stageChar J dq θ δ b u₀ n n

theorem stageLimit_eq (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ)
    (u₀ : ℕ → ℂ) {n k : ℕ} (hn : (n : ℝ) ≤ stageBaseAt θ δ b k) :
    stageLimit J dq θ δ b u₀ n = stageChar J dq θ δ b u₀ k n := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  rw [stageLimit]
  rcases Nat.le_total k n with hkn | hnk
  · exact stageChar_stable J dq hb0 u₀ n hkn hn
  · have hself : (n : ℝ) ≤ stageBaseAt θ δ b n := stageBaseAt_ge_index hb hδ0 hθ0 n
    exact (stageChar_stable J dq hb0 u₀ k hnk hself).symm

theorem norm_stageLimit (J : ℕ) (dq : ℝ → ℂ) (θ δ b : ℝ) {u₀ : ℕ → ℂ} (hu₀ : ∀ n, ‖u₀ n‖ = 1)
    (n : ℕ) :
    ‖stageLimit J dq θ δ b u₀ n‖ = 1 :=
  norm_stageChar J dq θ δ b hu₀ n n

theorem stageLimit_eq_of_le_base (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ)
    (hθ0 : 0 ≤ θ)
    (u₀ : ℕ → ℂ) {n : ℕ} (hn : (n : ℝ) ≤ b) : stageLimit J dq θ δ b u₀ n = u₀ n := by
  have h := stageLimit_eq J dq hb hδ0 hθ0 u₀ (k := 0) (by rwa [stageBaseAt_zero])
  rwa [stageChar_zero] at h

theorem arithJumpProfile_stageLimit (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ)
    (hθ0 : 0 ≤ θ)
    (u₀ : ℕ → ℂ) (j k : ℕ) :
    arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j (stageBaseAt θ δ b k)
      = arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ k)) j
          (stageBaseAt θ δ b k) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hpos : 0 < stageBaseAt θ δ b k := stageBaseAt_pos hb0 k
  rw [arithJumpProfile, arithJumpProfile]
  congr 1
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ stageBaseAt θ δ b k := by
    have h1 : n ≤ ⌊stageBaseAt θ δ b k⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊stageBaseAt θ δ b k⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le (le_of_lt hpos))
  congr 1
  refine characterSource_congr ?_
  intro m hm
  have hmle : (m : ℝ) ≤ stageBaseAt θ δ b k := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  exact stageLimit_eq J dq hb hδ0 hθ0 u₀ hmle

theorem arithJumpProfile_stageLimit_le (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 1 ≤ b)
    (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ)
    (u₀ : ℕ → ℂ) (j k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ stageBaseAt θ δ b k) :
    arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j x
      = arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ k)) j x := by
  rw [arithJumpProfile, arithJumpProfile]
  congr 1
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ stageBaseAt θ δ b k := by
    have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans (le_trans h2 (Nat.floor_le hx0)) hx
  congr 1
  refine characterSource_congr ?_
  intro m hm
  have hmle : (m : ℝ) ≤ stageBaseAt θ δ b k := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  exact stageLimit_eq J dq hb hδ0 hθ0 u₀ hmle

theorem exists_stage_window_index {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ)
    {x : ℝ} (hx : b ≤ x) :
    ∃ k : ℕ, stageBaseAt θ δ b k ≤ x ∧ x ≤ stageBaseAt θ δ b (k + 1) := by
  classical
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hexists : ∃ k : ℕ, x < stageBaseAt θ δ b k := by
    obtain ⟨k, hk⟩ := exists_nat_gt x
    exact ⟨k, lt_of_lt_of_le hk (stageBaseAt_ge_index hb hδ0 hθ0 k)⟩
  classical
  let k₀ := Nat.find hexists
  have hk₀ : x < stageBaseAt θ δ b k₀ := Nat.find_spec hexists
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · exfalso
      rw [h, stageBaseAt_zero] at hk₀
      linarith
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, k₀ = k + 1 := ⟨k₀ - 1, by omega⟩
  refine ⟨k, ?_, ?_⟩
  · by_contra hcon
    have : x < stageBaseAt θ δ b k := lt_of_not_ge hcon
    have := Nat.find_min hexists (m := k) (by omega)
    exact this ‹x < stageBaseAt θ δ b k›
  · rw [← hk]
    exact le_of_lt hk₀

/-! ## Admissibility and the size condition for stage windows -/

theorem window_admissible_of_len (J : ℕ) (hJ : 0 < J) {α θ : ℝ} (hα0 : 0 < α) (hαθ : α < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → x ^ θ ≤ L → L ≤ x →
      x + L ≤ x ^ 2 ∧ 4 * (J : ℝ) * (x + L) ^ α ≤ L := by
  have hd : 0 < θ - α := by linarith
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  set K : ℝ := 4 * (J : ℝ) * 2 ^ α with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have : (0:ℝ) < (2:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    positivity
  refine ⟨max (max 2 (K ^ (1 / (θ - α)))) 1, le_max_right _ _, fun x L hx hL hLx => ?_⟩
  have hx2 : (2:ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx0 : (0:ℝ) < x := by linarith
  have hKx : K ^ (1 / (θ - α)) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 θ) hL
  refine ⟨by nlinarith [hLx, hx2], ?_⟩
  have hsum : x + L ≤ 2 * x := by linarith
  have hpow : (x + L) ^ α ≤ (2 * x) ^ α := Real.rpow_le_rpow (by linarith) hsum (le_of_lt hα0)
  have hsplit : (2 * x) ^ α = (2:ℝ) ^ α * x ^ α := Real.mul_rpow (by norm_num) (le_of_lt hx0)
  have hKle : K ≤ x ^ (θ - α) := by
    have h1 : (K ^ (1 / (θ - α))) ^ (θ - α) ≤ x ^ (θ - α) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK0) _) hKx (le_of_lt hd)
    have h2 : (K ^ (1 / (θ - α))) ^ (θ - α) = K := by
      rw [← Real.rpow_mul (le_of_lt hK0), one_div, inv_mul_cancel₀ (ne_of_gt hd), Real.rpow_one]
    rwa [h2] at h1
  have hxα : (0:ℝ) < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hexp : x ^ (θ - α) * x ^ α = x ^ θ := by
    rw [← Real.rpow_add hx0]
    ring_nf
  calc 4 * (J : ℝ) * (x + L) ^ α
      ≤ 4 * (J : ℝ) * ((2:ℝ) ^ α * x ^ α) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = K * x ^ α := by
        rw [hKdef]
        ring
    _ ≤ x ^ (θ - α) * x ^ α := mul_le_mul_of_nonneg_right hKle (le_of_lt hxα)
    _ = x ^ θ := hexp
    _ ≤ L := hL

theorem eventually_K_quarter_stage (J : ℕ) (hJ : 0 < J) {θ δ : ℝ} (hδ0 : 0 ≤ δ)
    (hJδ : (J : ℝ) * δ < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x b : ℝ, X ≤ x → 1 ≤ b → b ≤ x →
      2 * (J : ℝ) * (2 ^ J * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x)))
        ≤ primeWindowFloorL J (x ^ θ) / 4 := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  have hgap : 0 < θ - (J : ℝ) * δ := by linarith
  set c : ℝ := 2 * (J : ℝ) * 2 ^ J * (J : ℝ)
    * (32768 * (J : ℝ) * (blockRayleighConst J * 4)) with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (eventually_log_sq_le hc hgap)
  refine ⟨max (max X₀ 4) 1, le_max_right _ _, fun x b hx hb1 hbx => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx0 : (0:ℝ) < x := by linarith
  have hlogx : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
  have hbx' : b ^ ((J : ℝ) * δ) ≤ x ^ ((J : ℝ) * δ) :=
    Real.rpow_le_rpow (by linarith) hbx (by positivity)
  have hkey : c * (Real.log x) ^ 2 ≤ x ^ (θ - (J : ℝ) * δ) := hX₀ x hxX₀
  have hlogle : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith [hlogx]
  have hexp : x ^ ((J : ℝ) * δ) * x ^ (θ - (J : ℝ) * δ) = x ^ θ := by
    rw [← Real.rpow_add hx0]
    ring_nf
  rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
  have hxJδ : (0:ℝ) < x ^ ((J : ℝ) * δ) := Real.rpow_pos_of_pos hx0 _
  calc 2 * (J : ℝ) * (2 ^ J * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x)))
        * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
      = (c * Real.log x) * b ^ ((J : ℝ) * δ) := by
        rw [hcdef]
        ring
    _ ≤ (c * (Real.log x) ^ 2) * x ^ ((J : ℝ) * δ) := by
        have h1 : c * Real.log x ≤ c * (Real.log x) ^ 2 :=
          mul_le_mul_of_nonneg_left hlogle (le_of_lt hc)
        have h2 : (0:ℝ) ≤ c * Real.log x := by positivity
        have h3 : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.rpow_nonneg (by linarith) _
        nlinarith [h1, h2, h3, hbx']
    _ ≤ (x ^ (θ - (J : ℝ) * δ)) * x ^ ((J : ℝ) * δ) :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hxJδ)
    _ = x ^ θ := by
        rw [mul_comm]
        exact hexp

theorem stageLenAt_le_mul {θ δ b : ℝ} (hb : 1 ≤ b) (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ) (k : ℕ) :
    stageLenAt θ δ b k ≤ b ^ δ * stageLenAt θ δ b (k + 1) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hbδ : (1:ℝ) ≤ b ^ δ := Real.one_le_rpow hb hδ0
  have hnext : b ≤ stageBaseAt θ δ b (k + 1) := stageBaseAt_ge hb0 (k + 1)
  cases k with
  | zero =>
      rw [stageLenAt_zero, stageLenAt_succ]
      have h1 : b ^ (θ + δ) = b ^ δ * b ^ θ := by
        rw [← Real.rpow_add hb0]
        ring_nf
      have h2 : b ^ θ ≤ (stageBaseAt θ δ b 1) ^ θ :=
        Real.rpow_le_rpow (le_of_lt hb0) hnext hθ0
      rw [h1]
      have hbδ0 : (0:ℝ) ≤ b ^ δ := Real.rpow_nonneg (le_of_lt hb0) δ
      exact mul_le_mul_of_nonneg_left h2 hbδ0
  | succ k =>
      rw [stageLenAt_succ, stageLenAt_succ]
      have hmono : (stageBaseAt θ δ b (k + 1)) ^ θ ≤ (stageBaseAt θ δ b (k + 2)) ^ θ :=
        Real.rpow_le_rpow (le_of_lt (stageBaseAt_pos hb0 (k + 1)))
          (stageBaseAt_le_succ hb0 (k + 1)) hθ0
      have hpos : (0:ℝ) < (stageBaseAt θ δ b (k + 2)) ^ θ :=
        Real.rpow_pos_of_pos (stageBaseAt_pos hb0 (k + 2)) θ
      nlinarith [hmono, hbδ, hpos]

set_option maxHeartbeats 1000000 in
/-- **The stage recursion closes.**  After a transition window of length `b^{θ+δ}` the ordinary
windows keep every level at the rounding-error scale of the window just completed. -/
theorem exists_stage_state_bound (J : ℕ) (hJ : 0 < J) {α θ δ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hJδ : (J : ℝ) * δ < θ) (hθδ1 : θ + δ < 1) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ b : ℝ, X ≤ b → ∀ Mq : ℝ, (∀ t : ℝ, b ≤ t → ‖dq t‖ ≤ Mq) →
      Mq ≤ datumSlack J → ∀ u₀ : ℕ → ℂ, (∀ n, ‖u₀ n‖ = 1) → ∀ K₀ : ℝ, 0 ≤ K₀ →
      (∀ m : ℕ, m < J → ‖arithJumpProfile dq (characterSource u₀) m b‖
        ≤ ((b ^ (θ + δ)) ^ m / ((m.factorial : ℕ) : ℝ)) * K₀) →
      2 * (J : ℝ) * (2 ^ J * K₀
          + (forcedMassBoundL b (b ^ (θ + δ)) + Mq * b ^ (θ + δ)))
        ≤ primeWindowFloorL J (b ^ (θ + δ)) →
      ∀ k : ℕ, ∀ j : ℕ, j < J →
        ‖arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) j
            (stageBaseAt θ δ b (k + 1))‖
          ≤ ((stageLenAt θ δ b k) ^ j / ((j.factorial : ℕ) : ℝ))
              * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1))) := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  have hα1 : α < 1 := lt_trans hαθ hθ1
  obtain ⟨X₁, hX₁, hstep⟩ := exists_character_window_step_general_full J hJ halpha hα1 hdq
  obtain ⟨X₂, hX₂, hadm⟩ := window_admissible_of_len J hJ hα0 hαθ
  obtain ⟨X₃, hX₃, hforced⟩ := eventually_forced_quarter J hJ hθ0
  obtain ⟨X₄, hX₄, hKstage⟩ := eventually_K_quarter_stage J hJ (le_of_lt hδ0) hJδ
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ 4))), ?_, ?_⟩
  · exact le_trans (by norm_num : (1:ℝ) ≤ 4) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  intro b hb Mq hdqs hMqsmall u₀ hu₀ K₀ hK₀ hstate₀ hsize₀
  have hX1le : X₁ ≤ b := le_trans (le_max_left _ _) hb
  have hX2le : X₂ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hb
  have hX3le : X₃ ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hb
  have hX4le : X₄ ≤ b :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hb
  have hb4 : (4:ℝ) ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hb
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hbase_ge : ∀ k, b ≤ stageBaseAt θ δ b k := stageBaseAt_ge hb0
  have hbase_pos : ∀ k, 0 < stageBaseAt θ δ b k := stageBaseAt_pos hb0
  have hlen_pos : ∀ k, 0 < stageLenAt θ δ b k := stageLenAt_pos hb0
  have hunimod : ∀ k n, ‖stageChar J dq θ δ b u₀ k n‖ = 1 := norm_stageChar J dq θ δ b hu₀
  have hbδ1 : (1:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.one_le_rpow hb1 (by positivity)
  -- the length is below the base at every window
  have hlen_le : ∀ k, stageLenAt θ δ b k ≤ stageBaseAt θ δ b k := by
    intro k
    cases k with
    | zero =>
        rw [stageLenAt_zero, stageBaseAt_zero]
        have h1 : b ^ (θ + δ) ≤ b ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        rwa [Real.rpow_one] at h1
    | succ k =>
        rw [stageLenAt_succ]
        have h1 : (stageBaseAt θ δ b (k + 1)) ^ θ ≤ (stageBaseAt θ δ b (k + 1)) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (le_trans hb1 (hbase_ge (k + 1))) (le_of_lt hθ1)
        rwa [Real.rpow_one] at h1
  intro k
  induction k with
  | zero =>
      intro j hj
      obtain ⟨hsq, hadm'⟩ := hadm b (b ^ (θ + δ)) hX2le
        (Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)) (hlen_le 0)
      obtain ⟨c, hc1, hc2⟩ := hstep b (b ^ (θ + δ)) hX1le (Real.rpow_pos_of_pos hb0 _) hsq hadm'
        u₀ K₀ Mq hK₀ (fun t ht => hdqs t ht.1) (fun p _ => hu₀ p) hstate₀ hsize₀
      have hex : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ 0) (stageBaseAt θ δ b 0)
          (stageLenAt θ δ b 0) c := ⟨c, hc1, hc2⟩
      rw [stageChar_succ, dif_pos hex]
      exact (hex.choose_spec).2 j hj
  | succ k ih =>
      intro j hj
      have hbk : b ≤ stageBaseAt θ δ b (k + 1) := hbase_ge (k + 1)
      have hlenge : (stageBaseAt θ δ b (k + 1)) ^ θ ≤ stageLenAt θ δ b (k + 1) :=
        rpow_le_stageLenAt hb1 (le_of_lt hδ0) (k + 1)
      obtain ⟨hsq, hadm'⟩ := hadm (stageBaseAt θ δ b (k + 1)) (stageLenAt θ δ b (k + 1))
        (le_trans hX2le hbk) hlenge (hlen_le (k + 1))
      have hlogb : 0 ≤ Real.log (stageBaseAt θ δ b (k + 1)) :=
        Real.log_nonneg (le_trans hb1 hbk)
      have hstate : ∀ m : ℕ, m < J →
          ‖arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) m
              (stageBaseAt θ δ b (k + 1))‖
            ≤ ((stageLenAt θ δ b (k + 1)) ^ m / ((m.factorial : ℕ) : ℝ))
                * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))) := by
        intro m hm
        refine le_trans (ih m hm) ?_
        have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hratio : (stageLenAt θ δ b k) ^ m
            ≤ b ^ ((J : ℝ) * δ) * (stageLenAt θ δ b (k + 1)) ^ m := by
          have h1 : (stageLenAt θ δ b k) ^ m ≤ (b ^ δ * stageLenAt θ δ b (k + 1)) ^ m :=
            pow_le_pow_left₀ (le_of_lt (hlen_pos k))
              (stageLenAt_le_mul hb1 (le_of_lt hδ0) (le_of_lt hθ0) k) m
          have h2 : (b ^ δ * stageLenAt θ δ b (k + 1)) ^ m
              = (b ^ δ) ^ m * (stageLenAt θ δ b (k + 1)) ^ m := by rw [mul_pow]
          have h3 : (b ^ δ) ^ m ≤ b ^ ((J : ℝ) * δ) := by
            rw [← Real.rpow_natCast (b ^ δ) m, ← Real.rpow_mul (le_of_lt hb0)]
            refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
            have hmJ : (m : ℝ) ≤ (J : ℝ) := by exact_mod_cast le_of_lt hm
            nlinarith [hmJ, hδ0]
          have h4 : (0:ℝ) ≤ (stageLenAt θ δ b (k + 1)) ^ m :=
            pow_nonneg (le_of_lt (hlen_pos (k + 1))) m
          calc (stageLenAt θ δ b k) ^ m ≤ (b ^ δ) ^ m * (stageLenAt θ δ b (k + 1)) ^ m := by
                rw [← h2]; exact h1
            _ ≤ b ^ ((J : ℝ) * δ) * (stageLenAt θ δ b (k + 1)) ^ m :=
                mul_le_mul_of_nonneg_right h3 h4
        have hJlog : (0:ℝ) ≤ (J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)) :=
          mul_nonneg (Nat.cast_nonneg J) hlogb
        calc (stageLenAt θ δ b k) ^ m / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))
            ≤ (b ^ ((J : ℝ) * δ) * (stageLenAt θ δ b (k + 1)) ^ m) / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1))) := by
              refine mul_le_mul_of_nonneg_right ?_ hJlog
              exact div_le_div_of_nonneg_right hratio hfac.le
          _ = (stageLenAt θ δ b (k + 1)) ^ m / ((m.factorial : ℕ) : ℝ)
              * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))) := by
              field_simp
      have hsize : 2 * (J : ℝ) * (2 ^ J * (b ^ ((J : ℝ) * δ)
            * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1))))
          + (forcedMassBoundL (stageBaseAt θ δ b (k + 1)) (stageLenAt θ δ b (k + 1))
            + Mq * stageLenAt θ δ b (k + 1)))
          ≤ primeWindowFloorL J (stageLenAt θ δ b (k + 1)) := by
        refine size_condition_of_quarters hJ (le_of_lt (hlen_pos (k + 1))) ?_ ?_ ?_
        · have hkey := hKstage (stageBaseAt θ δ b (k + 1)) b (le_trans hX4le hbk) hb1 hbk
          have hlen_eq : stageLenAt θ δ b (k + 1) = (stageBaseAt θ δ b (k + 1)) ^ θ :=
            stageLenAt_succ θ δ b k
          rw [hlen_eq]
          exact hkey
        · exact hforced (stageBaseAt θ δ b (k + 1)) (stageLenAt θ δ b (k + 1))
            (le_trans hX3le hbk) hlenge hsq
        · exact datum_quarter hJ (le_of_lt (hlen_pos (k + 1))) hMqsmall
      obtain ⟨c, hc1, hc2⟩ := hstep (stageBaseAt θ δ b (k + 1)) (stageLenAt θ δ b (k + 1))
        (le_trans hX1le hbk) (hlen_pos (k + 1)) hsq hadm'
        (stageChar J dq θ δ b u₀ (k + 1))
        (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))) Mq
        (by positivity) (fun t ht => hdqs t (le_trans hbk ht.1))
        (fun p _ => hunimod (k + 1) p) hstate hsize
      have hex : ∃ c, CharGoodL J dq (stageChar J dq θ δ b u₀ (k + 1)) (stageBaseAt θ δ b (k + 1))
          (stageLenAt θ δ b (k + 1)) c := ⟨c, hc1, hc2⟩
      rw [stageChar_succ, dif_pos hex]
      exact (hex.choose_spec).2 j hj

/-! ## The uniform bound over a stage -/

theorem arithJumpProfile_stageChar_succ_at_base (J : ℕ) (dq : ℝ → ℂ) {θ δ b : ℝ} (hb : 1 ≤ b)
    (u₀ : ℕ → ℂ) (m k : ℕ) :
    arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) m
        (stageBaseAt θ δ b k)
      = arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ k)) m
          (stageBaseAt θ δ b k) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hpos : 0 < stageBaseAt θ δ b k := stageBaseAt_pos hb0 k
  rw [arithJumpProfile, arithJumpProfile]
  congr 1
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ stageBaseAt θ δ b k := by
    have h1 : n ≤ ⌊stageBaseAt θ δ b k⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊stageBaseAt θ δ b k⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le (le_of_lt hpos))
  congr 1
  refine characterSource_congr ?_
  intro p hp
  have hple : (p : ℝ) ≤ stageBaseAt θ δ b k := by
    have : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
    linarith
  exact stageChar_succ_apply_of_le J dq θ δ b u₀ k hple

set_option maxHeartbeats 1000000 in
/-- **The uniform bound over a stage.**  At every point past the stage's base the levels are
controlled in the scale `x^{θ+δ}`. -/
theorem norm_arithJumpProfile_stage_uniform (J : ℕ) (hJ : 0 < J) {α θ δ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hJδ : (J : ℝ) * δ < θ) (hθδ1 : θ + δ < 1) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ b : ℝ, X ≤ b → ∀ Mq : ℝ, (∀ t : ℝ, b ≤ t → ‖dq t‖ ≤ Mq) →
      Mq ≤ datumSlack J → Mq ≤ 1 →
      ∀ u₀ : ℕ → ℂ, (∀ n, ‖u₀ n‖ = 1) → ∀ K₀ : ℝ, 0 ≤ K₀ →
      (∀ m : ℕ, m < J → ‖arithJumpProfile dq (characterSource u₀) m b‖
        ≤ ((b ^ (θ + δ)) ^ m / ((m.factorial : ℕ) : ℝ)) * K₀) →
      2 * (J : ℝ) * (2 ^ J * K₀
          + (forcedMassBoundL b (b ^ (θ + δ)) + Mq * b ^ (θ + δ)))
        ≤ primeWindowFloorL J (b ^ (θ + δ)) →
      ∀ x : ℝ, b ≤ x → ∀ j : ℕ, j < J →
        ‖arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j x‖
          ≤ ((x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ))
              * (2 ^ J * (K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x))
                + 2 * ((x ^ (θ + δ) + 1) * Real.log x)) := by
  classical
  have hθ0 : 0 < θ := lt_trans (lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha) hαθ
  obtain ⟨X₀, hX₀, hstage⟩ :=
    exists_stage_state_bound J hJ halpha hαθ hθ1 hδ0 hJδ hθδ1 hdq
  refine ⟨max X₀ 4, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb Mq hdqs hMqsmall hMq1 u₀ hu₀ K₀ hK₀ hstate₀ hsize₀ x hx j hj
  have hbX₀ : X₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : (4:ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hx1 : (1:ℝ) ≤ x := le_trans hb1 hx
  have hx0 : (0:ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  obtain ⟨k, hk1, hk2⟩ := exists_stage_window_index hb1 (le_of_lt hδ0) (le_of_lt hθ0) hx
  have hbase_ge : ∀ i, b ≤ stageBaseAt θ δ b i := stageBaseAt_ge hb0
  have hlen_pos : ∀ i, 0 < stageLenAt θ δ b i := stageLenAt_pos hb0
  -- move to the finite stage
  have hprof : arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j x
      = arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) j x :=
    arithJumpProfile_stageLimit_le J dq hb1 (le_of_lt hδ0) (le_of_lt hθ0) u₀ j (k + 1)
      (le_of_lt hx0) hk2
  rw [hprof]
  -- the state at the base of window `k`
  set S : ℝ := stageLenAt θ δ b k with hSdef
  set K : ℝ := K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) with hKdef
  have hSnn : (0:ℝ) ≤ S := le_of_lt (hlen_pos k)
  have hbδ1 : (1:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.one_le_rpow hb1 (by positivity)
  have hK0' : 0 ≤ K := by
    rw [hKdef]
    have : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) := by positivity
    linarith
  have hstate : ∀ m : ℕ, m ≤ j →
      ‖arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) m
          (stageBaseAt θ δ b k)‖
        ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
    intro m hm
    have hmJ : m < J := lt_of_le_of_lt hm hj
    rw [arithJumpProfile_stageChar_succ_at_base J dq hb1 u₀ m k]
    cases k with
    | zero =>
        rw [stageChar_zero, stageBaseAt_zero, hSdef, stageLenAt_zero]
        refine le_trans (hstate₀ m hmJ) ?_
        have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hKdef]
        have : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) := by positivity
        linarith
    | succ k =>
        have hbound := hstage b hbX₀ Mq hdqs hMqsmall u₀ hu₀ K₀ hK₀ hstate₀ hsize₀ k m hmJ
        refine le_trans hbound ?_
        have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hratio : (stageLenAt θ δ b k) ^ m ≤ b ^ ((J : ℝ) * δ) * S ^ m := by
          have h1 : (stageLenAt θ δ b k) ^ m ≤ (b ^ δ * S) ^ m := by
            rw [hSdef]
            exact pow_le_pow_left₀ (le_of_lt (hlen_pos k))
              (stageLenAt_le_mul hb1 (le_of_lt hδ0) (le_of_lt hθ0) k) m
          have h2 : (b ^ δ * S) ^ m = (b ^ δ) ^ m * S ^ m := by rw [mul_pow]
          have h3 : (b ^ δ) ^ m ≤ b ^ ((J : ℝ) * δ) := by
            rw [← Real.rpow_natCast (b ^ δ) m, ← Real.rpow_mul (le_of_lt hb0)]
            refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
            have hmJ' : (m : ℝ) ≤ (J : ℝ) := by exact_mod_cast le_of_lt hmJ
            nlinarith [hmJ', hδ0]
          have h4 : (0:ℝ) ≤ S ^ m := pow_nonneg (le_of_lt (hlen_pos (k + 1))) m
          calc (stageLenAt θ δ b k) ^ m ≤ (b ^ δ) ^ m * S ^ m := by rw [← h2]; exact h1
            _ ≤ b ^ ((J : ℝ) * δ) * S ^ m := mul_le_mul_of_nonneg_right h3 h4
        have hlogle : Real.log (stageBaseAt θ δ b (k + 1)) ≤ Real.log x :=
          Real.log_le_log (stageBaseAt_pos hb0 (k + 1)) hk1
        have hJlog : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        calc (stageLenAt θ δ b k) ^ m / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))
            ≤ (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log x) := by
              have hnum : (0:ℝ) ≤ (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ) := by
                have h1 : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.rpow_nonneg (le_of_lt hb0) _
                have h2 : (0:ℝ) ≤ S ^ m := pow_nonneg hSnn m
                positivity
              have hlogbase : (0:ℝ) ≤ Real.log (stageBaseAt θ δ b (k + 1)) :=
                Real.log_nonneg (le_trans hb1 (hbase_ge (k + 1)))
              refine mul_le_mul (div_le_div_of_nonneg_right hratio hfacm.le) ?_ ?_ hnum
              · exact mul_le_mul_of_nonneg_left hlogle hJlog
              · exact mul_nonneg hJlog hlogbase
          _ ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
              rw [hKdef]
              have hexp : (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ)
                  * ((J : ℝ) * Real.log x)
                  = (S ^ m / ((m.factorial : ℕ) : ℝ))
                    * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x)) := by
                field_simp
              rw [hexp]
              have hSm : (0:ℝ) ≤ S ^ m / ((m.factorial : ℕ) : ℝ) := by
                have h2 : (0:ℝ) ≤ S ^ m := pow_nonneg hSnn m
                positivity
              refine mul_le_mul_of_nonneg_left ?_ hSm
              linarith
  -- the window mass
  have hmass : ∑ n ∈ Finset.Ioc ⌊stageBaseAt θ δ b k⌋₊ ⌊x⌋₊,
      ‖characterSource (stageChar J dq θ δ b u₀ (k + 1)) n‖ ≤ (S + 1) * Real.log x := by
    refine le_trans (sum_norm_characterSource_window_le
      (fun p _ => norm_stageChar J dq θ δ b hu₀ (k + 1) p) (le_trans hb1 (hbase_ge k)) hk1) ?_
    have hxb : x - stageBaseAt θ δ b k ≤ S := by
      have : stageBaseAt θ δ b (k + 1) = stageBaseAt θ δ b k + S := stageBaseAt_succ θ δ b k
      linarith [hk2, this]
    exact mul_le_mul_of_nonneg_right (by linarith) hlogx
  have hSle : S ≤ x ^ (θ + δ) := by
    cases k with
    | zero =>
        rw [hSdef, stageLenAt_zero]
        exact Real.rpow_le_rpow (le_of_lt hb0) (le_trans (hbase_ge 0) (by rwa [stageBaseAt_zero] at hk1 ⊢))
          (by linarith)
    | succ k =>
        rw [hSdef, stageLenAt_succ]
        have h1 : (stageBaseAt θ δ b (k + 1)) ^ θ ≤ x ^ θ :=
          Real.rpow_le_rpow (le_of_lt (stageBaseAt_pos hb0 (k + 1))) hk1 (le_of_lt hθ0)
        have h2 : x ^ θ ≤ x ^ (θ + δ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        linarith
  have hwindow := norm_arithJumpProfile_window_le' hdq
    (a := characterSource (stageChar J dq θ δ b u₀ (k + 1)))
    (x := stageBaseAt θ δ b k) (y := x) (S := S) (K := K) (M := (S + 1) * Real.log x)
    (Mq := Mq) (j := j)
    (le_trans hb1 (hbase_ge k)) hk1 (by
      have : stageBaseAt θ δ b (k + 1) = stageBaseAt θ δ b k + S := stageBaseAt_succ θ δ b k
      linarith [hk2, this])
    (fun t ht => hdqs t (le_trans (le_trans (hbase_ge k) le_rfl) ht.1)) hstate hmass
  refine le_trans hwindow ?_
  have hpowle : S ^ j ≤ (x ^ (θ + δ)) ^ j := pow_le_pow_left₀ hSnn hSle j
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hMq0 : (0:ℝ) ≤ Mq := le_trans (norm_nonneg _) (hdqs b le_rfl)
  have hdatum : Mq * S ≤ (x ^ (θ + δ) + 1) * Real.log x := by
    have h1 : Mq * S ≤ S := by nlinarith [hSnn, hMq1, hMq0]
    have h2 : S ≤ x ^ (θ + δ) := hSle
    nlinarith [h1, h2, hlogx1, hSnn]
  have hinner : 2 ^ j * K + (S + 1) * Real.log x + Mq * S
      ≤ 2 ^ J * K + 2 * ((x ^ (θ + δ) + 1) * Real.log x) := by
    have h1 : (2:ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hj)
    have h2 : (S + 1) * Real.log x ≤ (x ^ (θ + δ) + 1) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlogx
    nlinarith [h1, hK0', h2, hdatum]
  have hinner0 : (0:ℝ) ≤ 2 ^ J * K + 2 * ((x ^ (θ + δ) + 1) * Real.log x) := by
    have : (0:ℝ) ≤ x ^ (θ + δ) := Real.rpow_nonneg (le_of_lt hx0) _
    positivity
  calc (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + (S + 1) * Real.log x + Mq * S)
      ≤ ((x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ))
          * (2 ^ J * K + 2 * ((x ^ (θ + δ) + 1) * Real.log x)) := by
        refine mul_le_mul (div_le_div_of_nonneg_right hpowle hfac.le) hinner ?_ (by positivity)
        have : (0:ℝ) ≤ 2 ^ j * K := by positivity
        have h2 : (0:ℝ) ≤ (S + 1) * Real.log x := by positivity
        have h3 : (0:ℝ) ≤ Mq * S := mul_nonneg hMq0 hSnn
        linarith
    _ = ((x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ))
          * (2 ^ J * (K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x))
            + 2 * ((x ^ (θ + δ) + 1) * Real.log x)) := by
        rw [hKdef]

set_option maxHeartbeats 1000000 in
/-- **The sharp bound past the first window.**  Beyond the transition window the levels are
controlled in the scale `x^θ`. -/
theorem norm_arithJumpProfile_stage_sharp (J : ℕ) (hJ : 0 < J) {α θ δ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hJδ : (J : ℝ) * δ < θ) (hθδ1 : θ + δ < 1) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ b : ℝ, X ≤ b → ∀ Mq : ℝ, (∀ t : ℝ, b ≤ t → ‖dq t‖ ≤ Mq) →
      Mq ≤ datumSlack J → Mq ≤ 1 →
      ∀ u₀ : ℕ → ℂ, (∀ n, ‖u₀ n‖ = 1) → ∀ K₀ : ℝ, 0 ≤ K₀ →
      (∀ m : ℕ, m < J → ‖arithJumpProfile dq (characterSource u₀) m b‖
        ≤ ((b ^ (θ + δ)) ^ m / ((m.factorial : ℕ) : ℝ)) * K₀) →
      2 * (J : ℝ) * (2 ^ J * K₀
          + (forcedMassBoundL b (b ^ (θ + δ)) + Mq * b ^ (θ + δ)))
        ≤ primeWindowFloorL J (b ^ (θ + δ)) →
      ∀ x : ℝ, stageBaseAt θ δ b 1 ≤ x → ∀ j : ℕ, j < J →
        ‖arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j x‖
          ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
              * (2 ^ J * (K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x))
                + 2 * ((x ^ θ + 1) * Real.log x)) := by
  classical
  have hθ0 : 0 < θ := lt_trans (lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha) hαθ
  obtain ⟨X₀, hX₀, hstage⟩ :=
    exists_stage_state_bound J hJ halpha hαθ hθ1 hδ0 hJδ hθδ1 hdq
  refine ⟨max X₀ 4, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb Mq hdqs hMqsmall hMq1 u₀ hu₀ K₀ hK₀ hstate₀ hsize₀ x hx1' j hj
  have hx : b ≤ x := le_trans (stageBaseAt_ge (lt_of_lt_of_le zero_lt_one
    (le_trans (by norm_num : (1:ℝ) ≤ 4) (le_trans (le_max_right _ _) hb))) 1) hx1'
  have hbX₀ : X₀ ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : (4:ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hx1 : (1:ℝ) ≤ x := le_trans hb1 hx
  have hx0 : (0:ℝ) < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hfac : (0:ℝ) < ((j.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  obtain ⟨k₀, hk₀1, hk₀2⟩ := exists_stage_window_index hb1 (le_of_lt hδ0) (le_of_lt hθ0) hx
  obtain ⟨k, hk1, hk2, hkpos⟩ : ∃ k : ℕ, stageBaseAt θ δ b k ≤ x ∧ x ≤ stageBaseAt θ δ b (k + 1)
      ∧ 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · refine ⟨1, ?_, ?_, le_refl 1⟩
      · exact hx1'
      · rw [h0] at hk₀2
        have hxe : x = stageBaseAt θ δ b 1 := le_antisymm hk₀2 hx1'
        rw [hxe]
        exact stageBaseAt_le_succ hb0 1
    · exact ⟨k₀, hk₀1, hk₀2, hpos⟩
  have hbase_ge : ∀ i, b ≤ stageBaseAt θ δ b i := stageBaseAt_ge hb0
  have hlen_pos : ∀ i, 0 < stageLenAt θ δ b i := stageLenAt_pos hb0
  -- move to the finite stage
  have hprof : arithJumpProfile dq (characterSource (stageLimit J dq θ δ b u₀)) j x
      = arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) j x :=
    arithJumpProfile_stageLimit_le J dq hb1 (le_of_lt hδ0) (le_of_lt hθ0) u₀ j (k + 1)
      (le_of_lt hx0) hk2
  rw [hprof]
  -- the state at the base of window `k`
  set S : ℝ := stageLenAt θ δ b k with hSdef
  set K : ℝ := K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) with hKdef
  have hSnn : (0:ℝ) ≤ S := le_of_lt (hlen_pos k)
  have hbδ1 : (1:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.one_le_rpow hb1 (by positivity)
  have hK0' : 0 ≤ K := by
    rw [hKdef]
    have : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) := by positivity
    linarith
  have hstate : ∀ m : ℕ, m ≤ j →
      ‖arithJumpProfile dq (characterSource (stageChar J dq θ δ b u₀ (k + 1))) m
          (stageBaseAt θ δ b k)‖
        ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
    intro m hm
    have hmJ : m < J := lt_of_le_of_lt hm hj
    rw [arithJumpProfile_stageChar_succ_at_base J dq hb1 u₀ m k]
    cases k with
    | zero =>
        rw [stageChar_zero, stageBaseAt_zero, hSdef, stageLenAt_zero]
        refine le_trans (hstate₀ m hmJ) ?_
        have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hKdef]
        have : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x) := by positivity
        linarith
    | succ k =>
        have hbound := hstage b hbX₀ Mq hdqs hMqsmall u₀ hu₀ K₀ hK₀ hstate₀ hsize₀ k m hmJ
        refine le_trans hbound ?_
        have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hratio : (stageLenAt θ δ b k) ^ m ≤ b ^ ((J : ℝ) * δ) * S ^ m := by
          have h1 : (stageLenAt θ δ b k) ^ m ≤ (b ^ δ * S) ^ m := by
            rw [hSdef]
            exact pow_le_pow_left₀ (le_of_lt (hlen_pos k))
              (stageLenAt_le_mul hb1 (le_of_lt hδ0) (le_of_lt hθ0) k) m
          have h2 : (b ^ δ * S) ^ m = (b ^ δ) ^ m * S ^ m := by rw [mul_pow]
          have h3 : (b ^ δ) ^ m ≤ b ^ ((J : ℝ) * δ) := by
            rw [← Real.rpow_natCast (b ^ δ) m, ← Real.rpow_mul (le_of_lt hb0)]
            refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
            have hmJ' : (m : ℝ) ≤ (J : ℝ) := by exact_mod_cast le_of_lt hmJ
            nlinarith [hmJ', hδ0]
          have h4 : (0:ℝ) ≤ S ^ m := pow_nonneg (le_of_lt (hlen_pos (k + 1))) m
          calc (stageLenAt θ δ b k) ^ m ≤ (b ^ δ) ^ m * S ^ m := by rw [← h2]; exact h1
            _ ≤ b ^ ((J : ℝ) * δ) * S ^ m := mul_le_mul_of_nonneg_right h3 h4
        have hlogle : Real.log (stageBaseAt θ δ b (k + 1)) ≤ Real.log x :=
          Real.log_le_log (stageBaseAt_pos hb0 (k + 1)) hk1
        have hJlog : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
        calc (stageLenAt θ δ b k) ^ m / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (stageBaseAt θ δ b (k + 1)))
            ≤ (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log x) := by
              have hnum : (0:ℝ) ≤ (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ) := by
                have h1 : (0:ℝ) ≤ b ^ ((J : ℝ) * δ) := Real.rpow_nonneg (le_of_lt hb0) _
                have h2 : (0:ℝ) ≤ S ^ m := pow_nonneg hSnn m
                positivity
              have hlogbase : (0:ℝ) ≤ Real.log (stageBaseAt θ δ b (k + 1)) :=
                Real.log_nonneg (le_trans hb1 (hbase_ge (k + 1)))
              refine mul_le_mul (div_le_div_of_nonneg_right hratio hfacm.le) ?_ ?_ hnum
              · exact mul_le_mul_of_nonneg_left hlogle hJlog
              · exact mul_nonneg hJlog hlogbase
          _ ≤ (S ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
              rw [hKdef]
              have hexp : (b ^ ((J : ℝ) * δ) * S ^ m) / ((m.factorial : ℕ) : ℝ)
                  * ((J : ℝ) * Real.log x)
                  = (S ^ m / ((m.factorial : ℕ) : ℝ))
                    * (b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x)) := by
                field_simp
              rw [hexp]
              have hSm : (0:ℝ) ≤ S ^ m / ((m.factorial : ℕ) : ℝ) := by
                have h2 : (0:ℝ) ≤ S ^ m := pow_nonneg hSnn m
                positivity
              refine mul_le_mul_of_nonneg_left ?_ hSm
              linarith
  -- the window mass
  have hmass : ∑ n ∈ Finset.Ioc ⌊stageBaseAt θ δ b k⌋₊ ⌊x⌋₊,
      ‖characterSource (stageChar J dq θ δ b u₀ (k + 1)) n‖ ≤ (S + 1) * Real.log x := by
    refine le_trans (sum_norm_characterSource_window_le
      (fun p _ => norm_stageChar J dq θ δ b hu₀ (k + 1) p) (le_trans hb1 (hbase_ge k)) hk1) ?_
    have hxb : x - stageBaseAt θ δ b k ≤ S := by
      have : stageBaseAt θ δ b (k + 1) = stageBaseAt θ δ b k + S := stageBaseAt_succ θ δ b k
      linarith [hk2, this]
    exact mul_le_mul_of_nonneg_right (by linarith) hlogx
  have hSle : S ≤ x ^ θ := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hSdef, stageLenAt_succ]
    exact Real.rpow_le_rpow (le_of_lt (stageBaseAt_pos hb0 (k' + 1))) hk1 (le_of_lt hθ0)
  have hwindow := norm_arithJumpProfile_window_le' hdq
    (a := characterSource (stageChar J dq θ δ b u₀ (k + 1)))
    (x := stageBaseAt θ δ b k) (y := x) (S := S) (K := K) (M := (S + 1) * Real.log x)
    (Mq := Mq) (j := j)
    (le_trans hb1 (hbase_ge k)) hk1 (by
      have : stageBaseAt θ δ b (k + 1) = stageBaseAt θ δ b k + S := stageBaseAt_succ θ δ b k
      linarith [hk2, this])
    (fun t ht => hdqs t (le_trans (le_trans (hbase_ge k) le_rfl) ht.1)) hstate hmass
  refine le_trans hwindow ?_
  have hpowle : S ^ j ≤ (x ^ θ) ^ j := pow_le_pow_left₀ hSnn hSle j
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hMq0 : (0:ℝ) ≤ Mq := le_trans (norm_nonneg _) (hdqs b le_rfl)
  have hdatum : Mq * S ≤ (x ^ θ + 1) * Real.log x := by
    have h1 : Mq * S ≤ S := by nlinarith [hSnn, hMq1, hMq0]
    have h2 : S ≤ x ^ θ := hSle
    nlinarith [h1, h2, hlogx1, hSnn]
  have hinner : 2 ^ j * K + (S + 1) * Real.log x + Mq * S
      ≤ 2 ^ J * K + 2 * ((x ^ θ + 1) * Real.log x) := by
    have h1 : (2:ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hj)
    have h2 : (S + 1) * Real.log x ≤ (x ^ θ + 1) * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlogx
    nlinarith [h1, hK0', h2, hdatum]
  have hinner0 : (0:ℝ) ≤ 2 ^ J * K + 2 * ((x ^ θ + 1) * Real.log x) := by
    have : (0:ℝ) ≤ x ^ (θ + δ) := Real.rpow_nonneg (le_of_lt hx0) _
    positivity
  calc (S ^ j / ((j.factorial : ℕ) : ℝ)) * (2 ^ j * K + (S + 1) * Real.log x + Mq * S)
      ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
          * (2 ^ J * K + 2 * ((x ^ θ + 1) * Real.log x)) := by
        refine mul_le_mul (div_le_div_of_nonneg_right hpowle hfac.le) hinner ?_ (by positivity)
        have : (0:ℝ) ≤ 2 ^ j * K := by positivity
        have h2 : (0:ℝ) ≤ (S + 1) * Real.log x := by positivity
        have h3 : (0:ℝ) ≤ Mq * S := mul_nonneg hMq0 hSnn
        linarith
    _ = ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
          * (2 ^ J * (K₀ + b ^ ((J : ℝ) * δ) * ((J : ℝ) * Real.log x))
            + 2 * ((x ^ θ + 1) * Real.log x)) := by
        rw [hKdef]

end RHTower.Sieve

end
