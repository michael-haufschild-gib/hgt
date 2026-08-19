import GaloisForLFunctions.RHTower.Sieve.StageWindowRecursion

/-!
# Stacking the stages

Each stage raises the order by one.  The state carried from stage to stage is the vector of levels
at the next stage's base: the first `J` of them at their natural size `b^{(m+1)θ}`, and the new one
at `b^{Jθ+1}`, which is what the integral `level_J = ∫ level_{J-1}` produces.  A transition window of
length `b^{θ+δ_J}` with `δ_J = 2(1-θ)/(J+3)` absorbs both.
-/

noncomputable section

open Filter GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- The transition exponent used when passing to order `J+1`. -/
def stackDelta (θ : ℝ) (J : ℕ) : ℝ := 2 * (1 - θ) / ((J : ℝ) + 3)

theorem stackDelta_pos {θ : ℝ} (hθ1 : θ < 1) (J : ℕ) : 0 < stackDelta θ J := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  have h2 : (0:ℝ) < (J : ℝ) + 3 := by positivity
  rw [stackDelta]
  exact div_pos (by linarith) h2

theorem stackDelta_lt {θ : ℝ} (hθ1 : θ < 1) (J : ℕ) : θ + stackDelta θ J < 1 := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  have h2 : (0:ℝ) < (J : ℝ) + 3 := by positivity
  have hkey : stackDelta θ J < 1 - θ := by
    rw [stackDelta, div_lt_iff₀ h2]
    nlinarith [h1, h2]
  linarith

theorem mul_stackDelta_lt {θ : ℝ} (hθ23 : 2/3 < θ) (hθ1 : θ < 1) (J : ℕ) :
    ((J : ℝ) + 1) * stackDelta θ J < θ := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  have h2 : (0:ℝ) < (J : ℝ) + 3 := by positivity
  have hJ0 : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hkey : ((J : ℝ) + 1) * stackDelta θ J ≤ 2 * (1 - θ) := by
    rw [stackDelta, mul_div_assoc']
    rw [div_le_iff₀ h2]
    nlinarith [h1, hJ0]
  nlinarith [hkey, hθ23]

/-- The key inequality for the transition: `(J+1) δ_J > 1 - θ` once `J ≥ 3`. -/
theorem one_sub_lt_mul_stackDelta {θ : ℝ} (hθ1 : θ < 1) {J : ℕ} (hJ : 3 ≤ J) :
    1 - θ < ((J : ℝ) + 1) * stackDelta θ J := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  have h2 : (0:ℝ) < (J : ℝ) + 3 := by positivity
  have hJR : (3:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  rw [stackDelta, mul_div_assoc', lt_div_iff₀ h2]
  nlinarith [h1, hJR]

/-- For `J ≥ 3` the transition also absorbs the new coordinate. -/
theorem one_sub_le_mul_stackDelta {θ : ℝ} (hθ1 : θ < 1) {J : ℕ} (hJ : 3 ≤ J) :
    1 - θ ≤ (J : ℝ) * stackDelta θ J := by
  have h1 : (0:ℝ) < 1 - θ := by linarith
  have h2 : (0:ℝ) < (J : ℝ) + 3 := by positivity
  have hJR : (3:ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  rw [stackDelta, mul_div_assoc', le_div_iff₀ h2]
  nlinarith [h1, hJR]

theorem eventually_const_log_le {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → A * Real.log x ≤ x ^ r := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (eventually_log_sq_le hA hr)
  refine ⟨max (max X₀ 4) 1, le_max_right _ _, fun x hx => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hlogx : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
  have hkey := hX₀ x hxX₀
  have hsq : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith [hlogx]
  have hmul : A * Real.log x ≤ A * (Real.log x) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hA)
  linarith

theorem eventually_const_le_rpow (A : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → A ≤ x ^ r := by
  have htend : Filter.Tendsto (fun x : ℝ => x ^ r) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hr
  obtain ⟨X₀, hX₀⟩ := (htend.eventually_ge_atTop A).exists_forall_of_atTop
  exact ⟨max X₀ 1, le_max_right _ _, fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)⟩

theorem eventually_const_le_rpow_mul_log (A : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → A ≤ x ^ r * Real.log x := by
  obtain ⟨X₀, hX₀, hbound⟩ := eventually_const_le_rpow (max A 0) hr
  refine ⟨max (max X₀ 4) 1, le_max_right _ _, fun x hx => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hlogx : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
  have h1 : max A 0 ≤ x ^ r := hbound x hxX₀
  have h2 : (0:ℝ) ≤ x ^ r := le_trans (le_max_right A 0) h1
  have h3 : A ≤ x ^ r := le_trans (le_max_left A 0) h1
  nlinarith [h1, h2, h3, hlogx]

/-- The state carried from one stage to the next: the first `J` levels at their natural size, and
the new one at the size the integral produces. -/
def StackInv (dq : ℝ → ℂ) (θ : ℝ) (J : ℕ) (b C : ℝ) (u : ℕ → ℂ) : Prop :=
  (∀ m : ℕ, m < J → ‖arithJumpProfile dq (characterSource u) m b‖
      ≤ C * b ^ (((m : ℝ) + 1) * θ) * Real.log b) ∧
    ‖arithJumpProfile dq (characterSource u) J b‖ ≤ C * b ^ ((J : ℝ) * θ + 1) * Real.log b

set_option maxHeartbeats 1000000 in
/-- **The transition applies.**  The carried state is inside the reach of a window of length
`b^{θ+δ_J}`. -/
theorem stage_hypotheses_of_stackInv {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (J : ℕ) (hJ : 3 ≤ J) (C : ℝ) (hC : 0 < C) (dq : ℝ → ℂ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ b : ℝ, X ≤ b → ∀ Mq : ℝ, 0 ≤ Mq → Mq ≤ datumSlack (J + 1) →
      ∀ u : ℕ → ℂ, StackInv dq θ J b C u →
      (∀ m : ℕ, m < J + 1 → ‖arithJumpProfile dq (characterSource u) m b‖
        ≤ ((b ^ (θ + stackDelta θ J)) ^ m / ((m.factorial : ℕ) : ℝ))
          * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b)) ∧
      2 * ((J + 1 : ℕ) : ℝ) * (2 ^ (J + 1)
          * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b)
          + (forcedMassBoundL b (b ^ (θ + stackDelta θ J))
            + Mq * b ^ (θ + stackDelta θ J)))
        ≤ primeWindowFloorL (J + 1) (b ^ (θ + stackDelta θ J)) := by
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  set δ : ℝ := stackDelta θ J with hδdef
  have hδ0 : 0 < δ := stackDelta_pos hθ1 J
  have hθδ1 : θ + δ < 1 := stackDelta_lt hθ1 J
  have hJδ : 1 - θ ≤ (J : ℝ) * δ := one_sub_le_mul_stackDelta hθ1 hJ
  have hJ1pos : 0 < J + 1 := Nat.succ_pos J
  obtain ⟨X₄, hX₄, hforced⟩ := eventually_forced_quarter (J + 1) hJ1pos hθ0
  -- the constant in the state half of the size condition
  set A : ℝ := 2 * ((J + 1 : ℕ) : ℝ) * 2 ^ (J + 1) * (C * (((J + 1).factorial : ℕ) : ℝ))
    * (32768 * ((J + 1 : ℕ) : ℝ) * (blockRayleighConst (J + 1) * 4)) with hAdef
  have hA0 : 0 < A := by
    have hD : 0 < blockRayleighConst (J + 1) := blockRayleighConst_pos hJ1pos
    have hfac : (0:ℝ) < (((J + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J + 1)
    have hJ1 : (0:ℝ) < ((J + 1 : ℕ) : ℝ) := by exact_mod_cast hJ1pos
    rw [hAdef]
    positivity
  obtain ⟨X₅, hX₅, hAlog⟩ := eventually_const_log_le hA0 hδ0
  refine ⟨max (max X₄ X₅) 4, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro b hb Mq hMq0 hMqsmall u hinv
  have hb4 : (4:ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hbX₄ : X₄ ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hbX₅ : X₅ ≤ b := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hbθ : (0:ℝ) < b ^ θ := Real.rpow_pos_of_pos hb0 θ
  have hbθδ : (0:ℝ) < b ^ (θ + δ) := Real.rpow_pos_of_pos hb0 _
  obtain ⟨hlow, htop⟩ := hinv
  constructor
  · intro m hm
    have hfacm : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hfacJ : (0:ℝ) < (((J + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J + 1)
    have hfacle : ((m.factorial : ℕ) : ℝ) ≤ (((J + 1).factorial : ℕ) : ℝ) := by
      have : m.factorial ≤ (J + 1).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hpow : ((b ^ (θ + δ)) ^ m) = b ^ ((m : ℝ) * (θ + δ)) := by
      rw [← Real.rpow_natCast (b ^ (θ + δ)) m, ← Real.rpow_mul (le_of_lt hb0)]
      ring_nf
    have hfacratio : ((m.factorial : ℕ) : ℝ) ≤ (((J + 1).factorial : ℕ) : ℝ) := hfacle
    have hkey : ∀ E : ℝ, E ≤ (m : ℝ) * (θ + δ) + θ →
        C * b ^ E * Real.log b
          ≤ ((b ^ (θ + δ)) ^ m / ((m.factorial : ℕ) : ℝ))
            * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b) := by
      intro E hE
      have hb1' : b ^ E ≤ b ^ ((m : ℝ) * (θ + δ) + θ) :=
        Real.rpow_le_rpow_of_exponent_le hb1 hE
      have hbm : (0:ℝ) < b ^ ((m : ℝ) * (θ + δ)) := Real.rpow_pos_of_pos hb0 _
      calc C * b ^ E * Real.log b
          ≤ C * b ^ ((m : ℝ) * (θ + δ) + θ) * Real.log b :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1' hC.le) hlogb
        _ = (b ^ ((m : ℝ) * (θ + δ)) / ((m.factorial : ℕ) : ℝ))
              * (C * ((m.factorial : ℕ) : ℝ) * b ^ θ * Real.log b) := by
            rw [Real.rpow_add hb0]
            field_simp
        _ ≤ (b ^ ((m : ℝ) * (θ + δ)) / ((m.factorial : ℕ) : ℝ))
              * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfacratio hC.le) hbθ.le) hlogb
        _ = ((b ^ (θ + δ)) ^ m / ((m.factorial : ℕ) : ℝ))
              * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b) := by
            rw [hpow]
    rcases Nat.lt_or_ge m J with hmJ | hmJ
    · refine le_trans (hlow m hmJ) (hkey _ ?_)
      have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [hδ0, hmnn]
    · have hmeq : m = J := by omega
      subst hmeq
      refine le_trans htop (hkey _ ?_)
      have h1 : (m : ℝ) * (θ + δ) = (m : ℝ) * θ + (m : ℝ) * δ := by ring
      rw [h1]
      linarith [hJδ]
  · refine size_condition_of_quarters hJ1pos (le_of_lt hbθδ) ?_ ?_ ?_
    · have hD : 0 < blockRayleighConst (J + 1) := blockRayleighConst_pos hJ1pos
      have hJ1 : (0:ℝ) < ((J + 1 : ℕ) : ℝ) := by exact_mod_cast hJ1pos
      rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
      have hkey : A * Real.log b ≤ b ^ δ := hAlog b hbX₅
      have hsplit : b ^ (θ + δ) = b ^ θ * b ^ δ := by
        rw [← Real.rpow_add hb0]
      rw [hsplit]
      calc 2 * ((J + 1 : ℕ) : ℝ) * (2 ^ (J + 1)
            * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b))
            * (32768 * ((J + 1 : ℕ) : ℝ) * (blockRayleighConst (J + 1) * 4))
          = (A * Real.log b) * b ^ θ := by
            rw [hAdef]
            ring
        _ ≤ b ^ δ * b ^ θ := mul_le_mul_of_nonneg_right hkey (le_of_lt hbθ)
        _ = b ^ θ * b ^ δ := by ring
    · refine hforced b (b ^ (θ + δ)) hbX₄ ?_ ?_
      · exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      · have h1 : b ^ (θ + δ) ≤ b ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        rw [Real.rpow_one] at h1
        nlinarith [h1, hb4, mul_nonneg (by linarith : (0:ℝ) ≤ b - 2) (le_of_lt hb0)]
    · exact datum_quarter hJ1pos (le_of_lt hbθδ) hMqsmall

set_option maxHeartbeats 2000000 in
/-- **One stage of the stacking.**  From the carried state at `b` the next stage produces a
character agreeing with the old one below `b`, a uniform level bound past `b`, and the carried
state of the next order at a point beyond `b`. -/
theorem exists_stack_step {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) (J : ℕ) (hJ : 3 ≤ J) (C : ℝ) (hC : 0 < C) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ b : ℝ, X ≤ b → ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) → StackInv dq θ J b C u →
      ∃ (C' : ℝ) (u' : ℕ → ℂ), 0 < C' ∧ C' ≤ b ^ (2 * θ) ∧ (∀ n, ‖u' n‖ = 1) ∧
        (∀ n : ℕ, (n : ℝ) ≤ b → u' n = u n) ∧
        (∀ x : ℝ, b ≤ x → ∀ j : ℕ, j < J + 1 →
          ‖arithJumpProfile dq (characterSource u') j x‖
            ≤ C' * x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) * Real.log x) ∧
        ∃ X' : ℝ, b < X' ∧ ∀ b' : ℝ, X' ≤ b' → StackInv dq θ (J + 1) b' C' u' := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  set δ : ℝ := stackDelta θ J with hδdef
  have hδ0 : 0 < δ := stackDelta_pos hθ1 J
  have hθδ1 : θ + δ < 1 := stackDelta_lt hθ1 J
  have hJ1pos : 0 < J + 1 := Nat.succ_pos J
  have hcast : ((J + 1 : ℕ) : ℝ) * δ < θ := by
    have := mul_stackDelta_lt hθ23 hθ1 J
    push_cast
    rw [hδdef]
    linarith [this]
  obtain ⟨X₀, hX₀, htrans⟩ := stage_hypotheses_of_stackInv halpha hαθ hθ1 J hJ C hC dq
  obtain ⟨X₁, hX₁, huniform⟩ :=
    norm_arithJumpProfile_stage_uniform (J + 1) hJ1pos halpha hαθ hθ1 hδ0 hcast hθδ1 hdq
  obtain ⟨X₂, hX₂, hsharp⟩ :=
    norm_arithJumpProfile_stage_sharp (J + 1) hJ1pos halpha hαθ hθ1 hδ0 hcast hθδ1 hdq
  obtain ⟨T, hT1, hTbound⟩ := exists_datum_threshold hdq0 (J := J + 1) hJ1pos
  set Mq : ℝ := min 1 (datumSlack (J + 1)) with hMqdef
  have hMq0 : 0 ≤ Mq := le_of_lt (lt_min one_pos (datumSlack_pos hJ1pos))
  have hMq1 : Mq ≤ 1 := min_le_left _ _
  have hMqsmall : Mq ≤ datumSlack (J + 1) := min_le_right _ _
  obtain ⟨X₃, hX₃, hlogbound⟩ := eventually_const_log_le
    (A := 3 * 2 ^ (J + 1) * C * (((J + 1).factorial : ℕ) : ℝ)) (r := θ)
    (by
      have hfac : (0:ℝ) < (((J + 1).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (J + 1)
      positivity) hθ0
  obtain ⟨X₄, hX₄, hpowbound⟩ := eventually_const_le_rpow
    (3 * 2 ^ (J + 1) * ((J + 1 : ℕ) : ℝ)) (r := 2 * θ - ((J + 1 : ℕ) : ℝ) * δ)
    (by nlinarith [hcast, hθ0])
  obtain ⟨X₅, hX₅, hninebound⟩ := eventually_const_le_rpow (15:ℝ) (r := 2 * θ) (by linarith)
  refine ⟨max (max (max X₀ X₁) (max X₂ 4)) (max (max X₃ X₄) (max X₅ T)), ?_, ?_⟩
  · exact le_trans (by norm_num) (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_left _ _))
  intro b hb u hu hinv
  have hbX₀ : X₀ ≤ b :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hb
  have hbX₁ : X₁ ≤ b :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hb
  have hbX₂ : X₂ ≤ b :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hb
  have hb4 : (4:ℝ) ≤ b :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hb
  have hbX₃ : X₃ ≤ b :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hb
  have hbX₄ : X₄ ≤ b :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hb
  have hbX₅ : X₅ ≤ b :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hb
  have hbT : T ≤ b :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) hb
  have hdqs : ∀ t : ℝ, b ≤ t → ‖dq t‖ ≤ Mq := fun t ht => hTbound t (le_trans hbT ht)
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  set K₀ : ℝ := C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b with hK₀def
  have hK₀0 : 0 ≤ K₀ := by
    have hfac : (0:ℝ) < (((J + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (J + 1)
    have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hbθ : (0:ℝ) < b ^ θ := Real.rpow_pos_of_pos hb0 θ
    rw [hK₀def]
    positivity
  obtain ⟨hstate₀, hsize₀⟩ := htrans b hbX₀ Mq hMq0 hMqsmall u hinv
  rw [← hδdef, ← hK₀def] at hstate₀ hsize₀
  set u' : ℕ → ℂ := stageLimit (J + 1) dq θ δ b u with hu'def
  have hu'norm : ∀ n, ‖u' n‖ = 1 := norm_stageLimit (J + 1) dq θ δ b hu
  have hu'agree : ∀ n : ℕ, (n : ℝ) ≤ b → u' n = u n := fun n hn =>
    stageLimit_eq_of_le_base (J + 1) dq hb1 (le_of_lt hδ0) (le_of_lt hθ0) u hn
  have huni := huniform b hbX₁ Mq hdqs hMqsmall hMq1 u hu K₀ hK₀0 hstate₀ hsize₀
  have hshp := hsharp b hbX₂ Mq hdqs hMqsmall hMq1 u hu K₀ hK₀0 hstate₀ hsize₀
  -- the constant coming out of the stage
  set Q : ℝ := 2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)) + 4 with hQdef
  have hbJδ : (0:ℝ) < b ^ (((J + 1 : ℕ) : ℝ) * δ) := Real.rpow_pos_of_pos hb0 _
  have hQ0 : 0 < Q := by
    rw [hQdef]
    have hJ0 : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
    positivity
  -- the uniform bound with the constant `Q`
  have hQuni : ∀ x : ℝ, b ≤ x → ∀ j : ℕ, j < J + 1 →
      ‖arithJumpProfile dq (characterSource u') j x‖
        ≤ Q * x ^ (((j : ℝ) + 1) * (θ + δ)) * Real.log x := by
    intro x hx j hj
    have hx4 : (4:ℝ) ≤ x := le_trans hb4 hx
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hx0 : (0:ℝ) < x := by linarith
    have hlogx : (1:ℝ) ≤ Real.log x := by
      have hlog4 : (1:ℝ) ≤ Real.log 4 := by
        have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
        rw [h4, Real.log_pow]
        have := Real.log_two_gt_d9
        push_cast
        linarith
      exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
    have hxθδ : (1:ℝ) ≤ x ^ (θ + δ) := Real.one_le_rpow hx1 (by linarith)
    have hfacj : (1:ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have hbase := huni x hx j hj
    refine le_trans hbase ?_
    have hpow : (x ^ (θ + δ)) ^ j = x ^ ((j : ℝ) * (θ + δ)) := by
      rw [← Real.rpow_natCast (x ^ (θ + δ)) j, ← Real.rpow_mul (le_of_lt hx0)]
      ring_nf
    have hprod : (1:ℝ) ≤ x ^ (θ + δ) * Real.log x := by nlinarith [hxθδ, hlogx]
    have hbracket : 2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
          * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ (θ + δ) + 1) * Real.log x)
        ≤ Q * (x ^ (θ + δ) * Real.log x) := by
      have h1 : K₀ ≤ K₀ * (x ^ (θ + δ) * Real.log x) := by nlinarith [hK₀0, hprod]
      have hJcast : (0:ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by positivity
      have h2 : b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x)
          ≤ b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ) * (x ^ (θ + δ) * Real.log x) := by
        have hxlog : Real.log x ≤ x ^ (θ + δ) * Real.log x := by nlinarith [hxθδ, hlogx]
        calc b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x)
            = (b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)) * Real.log x := by ring
          _ ≤ (b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)) * (x ^ (θ + δ) * Real.log x) := by
              refine mul_le_mul_of_nonneg_left hxlog ?_
              exact mul_nonneg (le_of_lt hbJδ) hJcast
          _ = b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)
              * (x ^ (θ + δ) * Real.log x) := by ring
      have h3 : 2 * ((x ^ (θ + δ) + 1) * Real.log x) ≤ 4 * (x ^ (θ + δ) * Real.log x) := by
        nlinarith [hxθδ, hlogx]
      have h2pow : (0:ℝ) < (2:ℝ) ^ (J + 1) := by positivity
      rw [hQdef]
      nlinarith [h1, h2, h3, h2pow, hprod]
    have hstep : (x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ)
          * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x))
            + 2 * ((x ^ (θ + δ) + 1) * Real.log x))
        ≤ (x ^ (θ + δ)) ^ j * (Q * (x ^ (θ + δ) * Real.log x)) := by
      have hdiv : (x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ) ≤ (x ^ (θ + δ)) ^ j := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hx0 (θ + δ))) j, hfacj]
      have hbr0 : (0:ℝ) ≤ 2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
          * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ (θ + δ) + 1) * Real.log x) := by
        have : (0:ℝ) ≤ Real.log x := by linarith
        positivity
      calc (x ^ (θ + δ)) ^ j / ((j.factorial : ℕ) : ℝ)
            * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
              * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ (θ + δ) + 1) * Real.log x))
          ≤ (x ^ (θ + δ)) ^ j * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
              * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ (θ + δ) + 1) * Real.log x)) :=
            mul_le_mul_of_nonneg_right hdiv hbr0
        _ ≤ (x ^ (θ + δ)) ^ j * (Q * (x ^ (θ + δ) * Real.log x)) := by
            refine mul_le_mul_of_nonneg_left hbracket ?_
            exact pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hx0 (θ + δ))) j
    refine le_trans hstep (le_of_eq ?_)
    rw [hpow]
    have hmul : x ^ ((j : ℝ) * (θ + δ)) * x ^ (θ + δ) = x ^ (((j : ℝ) + 1) * (θ + δ)) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    calc x ^ ((j : ℝ) * (θ + δ)) * (Q * (x ^ (θ + δ) * Real.log x))
        = Q * (x ^ ((j : ℝ) * (θ + δ)) * x ^ (θ + δ)) * Real.log x := by ring
      _ = Q * x ^ (((j : ℝ) + 1) * (θ + δ)) * Real.log x := by rw [hmul]
  have hQsharp : ∀ x : ℝ, stageBaseAt θ δ b 1 ≤ x → ∀ j : ℕ, j < J + 1 →
      ‖arithJumpProfile dq (characterSource u') j x‖
        ≤ Q * x ^ (((j : ℝ) + 1) * θ) * Real.log x := by
    intro x hxb1 j hj
    have hx : b ≤ x := le_trans (stageBaseAt_ge hb0 1) hxb1
    have hx4 : (4:ℝ) ≤ x := le_trans hb4 hx
    have hx1 : (1:ℝ) ≤ x := by linarith
    have hx0 : (0:ℝ) < x := by linarith
    have hlogx : (1:ℝ) ≤ Real.log x := by
      have hlog4 : (1:ℝ) ≤ Real.log 4 := by
        have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
        rw [h4, Real.log_pow]
        have := Real.log_two_gt_d9
        push_cast
        linarith
      exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
    have hxθδ : (1:ℝ) ≤ x ^ θ := Real.one_le_rpow hx1 (by linarith)
    have hfacj : (1:ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have hbase := hshp x hxb1 j hj
    refine le_trans hbase ?_
    have hpow : (x ^ θ) ^ j = x ^ ((j : ℝ) * θ) := by
      rw [← Real.rpow_natCast (x ^ θ) j, ← Real.rpow_mul (le_of_lt hx0)]
      ring_nf
    have hprod : (1:ℝ) ≤ x ^ θ * Real.log x := by nlinarith [hxθδ, hlogx]
    have hbracket : 2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
          * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ θ + 1) * Real.log x)
        ≤ Q * (x ^ θ * Real.log x) := by
      have h1 : K₀ ≤ K₀ * (x ^ θ * Real.log x) := by nlinarith [hK₀0, hprod]
      have hJcast : (0:ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by positivity
      have h2 : b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x)
          ≤ b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ) * (x ^ θ * Real.log x) := by
        have hxlog : Real.log x ≤ x ^ θ * Real.log x := by nlinarith [hxθδ, hlogx]
        calc b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x)
            = (b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)) * Real.log x := by ring
          _ ≤ (b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)) * (x ^ θ * Real.log x) := by
              refine mul_le_mul_of_nonneg_left hxlog ?_
              exact mul_nonneg (le_of_lt hbJδ) hJcast
          _ = b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ)
              * (x ^ θ * Real.log x) := by ring
      have h3 : 2 * ((x ^ θ + 1) * Real.log x) ≤ 4 * (x ^ θ * Real.log x) := by
        nlinarith [hxθδ, hlogx]
      have h2pow : (0:ℝ) < (2:ℝ) ^ (J + 1) := by positivity
      rw [hQdef]
      nlinarith [h1, h2, h3, h2pow, hprod]
    have hstep : (x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)
          * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ) * (((J + 1 : ℕ) : ℝ) * Real.log x))
            + 2 * ((x ^ θ + 1) * Real.log x))
        ≤ (x ^ θ) ^ j * (Q * (x ^ θ * Real.log x)) := by
      have hdiv : (x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ) ≤ (x ^ θ) ^ j := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hx0 θ)) j, hfacj]
      have hbr0 : (0:ℝ) ≤ 2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
          * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ θ + 1) * Real.log x) := by
        have : (0:ℝ) ≤ Real.log x := by linarith
        positivity
      calc (x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)
            * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
              * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ θ + 1) * Real.log x))
          ≤ (x ^ θ) ^ j * (2 ^ (J + 1) * (K₀ + b ^ (((J + 1 : ℕ) : ℝ) * δ)
              * (((J + 1 : ℕ) : ℝ) * Real.log x)) + 2 * ((x ^ θ + 1) * Real.log x)) :=
            mul_le_mul_of_nonneg_right hdiv hbr0
        _ ≤ (x ^ θ) ^ j * (Q * (x ^ θ * Real.log x)) := by
            refine mul_le_mul_of_nonneg_left hbracket ?_
            exact pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hx0 θ)) j
    refine le_trans hstep (le_of_eq ?_)
    rw [hpow]
    have hmul : x ^ ((j : ℝ) * θ) * x ^ θ = x ^ (((j : ℝ) + 1) * θ) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    calc x ^ ((j : ℝ) * θ) * (Q * (x ^ θ * Real.log x))
        = Q * (x ^ ((j : ℝ) * θ) * x ^ θ) * Real.log x := by ring
      _ = Q * x ^ (((j : ℝ) + 1) * θ) * Real.log x := by rw [hmul]
  obtain ⟨B₀, hB₀1, hB₀⟩ := eventually_const_le_rpow_mul_log
    (‖arithJumpProfile dq (characterSource u') (J + 1) (stageBaseAt θ δ b 1)‖)
    (r := ((J : ℝ) + 1) * θ + 1) (by
      have hJ0 : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith [hθ0, hJ0])
  set X' : ℝ := max (max (stageBaseAt θ δ b 1) (b + 1)) B₀ with hX'def
  have hX'gt : b < X' :=
    lt_of_lt_of_le (by linarith : b < b + 1) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hlogb : (0:ℝ) ≤ Real.log b := Real.log_nonneg hb1
  have hbθ : (0:ℝ) < b ^ θ := Real.rpow_pos_of_pos hb0 θ
  have hb2θ : (0:ℝ) < b ^ (2 * θ) := Real.rpow_pos_of_pos hb0 _
  -- the constant is small compared with the base
  have hQb : Q + 1 ≤ b ^ (2 * θ) := by
    have hsplitθ : b ^ (2 * θ) = b ^ θ * b ^ θ := by
      rw [← Real.rpow_add hb0]
      ring_nf
    have h1 : 2 ^ (J + 1) * K₀ ≤ b ^ (2 * θ) / 3 := by
      have hkey := hlogbound b hbX₃
      rw [hK₀def, hsplitθ]
      have hstep : 3 * (2 ^ (J + 1) * (C * (((J + 1).factorial : ℕ) : ℝ) * b ^ θ * Real.log b))
          ≤ b ^ θ * b ^ θ := by
        have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hbθ)
        nlinarith [hmul, hbθ]
      linarith
    have h2 : 2 ^ (J + 1) * (b ^ (((J + 1 : ℕ) : ℝ) * δ) * ((J + 1 : ℕ) : ℝ))
        ≤ b ^ (2 * θ) / 3 := by
      have hkey := hpowbound b hbX₄
      have hbδ : (0:ℝ) < b ^ (((J + 1 : ℕ) : ℝ) * δ) := Real.rpow_pos_of_pos hb0 _
      have hsplit2 : b ^ (2 * θ - ((J + 1 : ℕ) : ℝ) * δ) * b ^ (((J + 1 : ℕ) : ℝ) * δ)
          = b ^ (2 * θ) := by
        rw [← Real.rpow_add hb0]
        ring_nf
      have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hbδ)
      rw [hsplit2] at hmul
      nlinarith [hmul, hbδ]
    have h3 : (5:ℝ) ≤ b ^ (2 * θ) / 3 := by
      have := hninebound b hbX₅
      linarith
    rw [hQdef]
    linarith
  refine ⟨Q + 1, u', by linarith, hQb, hu'norm, hu'agree, ?_, X', hX'gt, ?_⟩
  · intro x hx j hj
    refine le_trans (hQuni x hx j hj) ?_
    have hx1 : (1:ℝ) ≤ x := le_trans hb1 hx
    have hx0 : (0:ℝ) < x := by linarith
    have hpow : (0:ℝ) ≤ x ^ (((j : ℝ) + 1) * (θ + δ)) := Real.rpow_nonneg (le_of_lt hx0) _
    have hlog0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Q ≤ Q + 1) hpow) hlog0
  intro b' hb'X
  have hb'ge : stageBaseAt θ δ b 1 ≤ b' :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb'X
  have hb'gt : b < b' := lt_of_lt_of_le hX'gt hb'X
  have hb'b : b ≤ b' := le_of_lt hb'gt
  have hb'B₀ : B₀ ≤ b' := le_trans (le_max_right _ _) hb'X
  have hb'4 : (4:ℝ) ≤ b' := le_trans hb4 hb'b
  have hb'1 : (1:ℝ) ≤ b' := by linarith
  have hb'0 : (0:ℝ) < b' := by linarith
  have hlogb' : (1:ℝ) ≤ Real.log b' := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hb'4)
  refine ⟨?_, ?_⟩
  · intro m hm
    refine le_trans (hQsharp b' hb'ge m hm) ?_
    have hpow : (0:ℝ) ≤ b' ^ (((m : ℝ) + 1) * θ) := Real.rpow_nonneg (le_of_lt hb'0) _
    have hlog0 : (0:ℝ) ≤ Real.log b' := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Q ≤ Q + 1) hpow) hlog0
  · set G : ℝ := Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log b' with hGdef
    have hbase1 : (1:ℝ) ≤ stageBaseAt θ δ b 1 := le_trans hb1 (stageBaseAt_ge hb0 1)
    have hEnn : (0:ℝ) ≤ ((J : ℝ) + 1) * θ := by
      have : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      nlinarith [hθ0, this]
    have hpow0 : (0:ℝ) < b' ^ (((J : ℝ) + 1) * θ) := Real.rpow_pos_of_pos hb'0 _
    have hsup : ∀ t ∈ Set.uIcc (stageBaseAt θ δ b 1) b',
        ‖arithJumpProfile dq (characterSource u') J t‖ ≤ G := by
      intro t ht
      rw [Set.uIcc_of_le hb'ge] at ht
      have ht1 : stageBaseAt θ δ b 1 ≤ t := ht.1
      have ht2 : t ≤ b' := ht.2
      have htb : (1:ℝ) ≤ t := le_trans hbase1 ht1
      have ht0 : (0:ℝ) < t := by linarith
      refine le_trans (hQsharp t ht1 J (by omega)) ?_
      rw [hGdef]
      have hp : t ^ (((J : ℝ) + 1) * θ) ≤ b' ^ (((J : ℝ) + 1) * θ) :=
        Real.rpow_le_rpow (le_of_lt ht0) ht2 hEnn
      have hl : Real.log t ≤ Real.log b' := Real.log_le_log ht0 ht2
      have hlt0 : (0:ℝ) ≤ Real.log t := Real.log_nonneg htb
      calc Q * t ^ (((J : ℝ) + 1) * θ) * Real.log t
          ≤ Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hQ0.le) hlt0
        _ ≤ Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log b' := by
            refine mul_le_mul_of_nonneg_left hl ?_
            exact mul_nonneg hQ0.le (le_of_lt hpow0)
    have hgrow := norm_arithJumpProfile_succ_le hdq (a := characterSource u')
      (b := stageBaseAt θ δ b 1) (x := b') (G := G) hbase1 hb'ge J hsup
    refine le_trans hgrow ?_
    have hcast : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hsplit : b' ^ (((J : ℝ) + 1) * θ + 1) = b' ^ (((J : ℝ) + 1) * θ) * b' := by
      rw [Real.rpow_add hb'0, Real.rpow_one]
    have hN := hB₀ b' hb'B₀
    have hGnn : (0:ℝ) ≤ G := by
      rw [hGdef]
      have : (0:ℝ) ≤ Real.log b' := by linarith
      positivity
    have hstep1 : (b' - stageBaseAt θ δ b 1) * G
        ≤ Q * (b' ^ (((J : ℝ) + 1) * θ) * b') * Real.log b' := by
      have h1 : b' - stageBaseAt θ δ b 1 ≤ b' := by linarith
      have hQPL : (0:ℝ) ≤ Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log b' :=
        mul_nonneg (mul_nonneg hQ0.le (le_of_lt hpow0)) (by linarith)
      rw [hGdef]
      calc (b' - stageBaseAt θ δ b 1) * (Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log b')
          ≤ b' * (Q * b' ^ (((J : ℝ) + 1) * θ) * Real.log b') :=
            mul_le_mul_of_nonneg_right h1 hQPL
        _ = Q * (b' ^ (((J : ℝ) + 1) * θ) * b') * Real.log b' := by ring
    rw [hsplit] at hN ⊢
    have hexpand : (Q + 1) * (b' ^ (((J : ℝ) + 1) * θ) * b') * Real.log b'
        = b' ^ (((J : ℝ) + 1) * θ) * b' * Real.log b'
          + Q * (b' ^ (((J : ℝ) + 1) * θ) * b') * Real.log b' := by ring
    linarith [hN, hstep1, hexpand.le, hexpand.ge]

set_option maxHeartbeats 1000000 in
/-- **The bootstrap.**  The ladder construction of order `4` supplies a character whose first four
levels are already at the size the stacking needs at order `3`. -/
theorem exists_stack_start {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (B : ℝ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) {Mglob : ℝ}
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) :
    ∃ (b : ℝ) (u : ℕ → ℂ), 4 ≤ b ∧ B ≤ b ∧ (∀ n, ‖u n‖ = 1) ∧
      StackInv dq θ 3 b 4 u := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  obtain ⟨X, hX, hladder⟩ := exists_ladder_state_bound 4 (by norm_num) halpha hαθ hθ1 hdq hdqb
  obtain ⟨T, hT1, hTbound⟩ := exists_datum_threshold hdq0 (J := 4) (by norm_num)
  set x₀ : ℝ := max (max X 4) T with hx₀def
  have hx₀X : X ≤ x₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx₀4 : (4:ℝ) ≤ x₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx₀T : T ≤ x₀ := le_max_right _ _
  have hdqs : ∀ t : ℝ, x₀ ≤ t → ‖dq t‖ ≤ min 1 (datumSlack 4) :=
    fun t ht => hTbound t (le_trans hx₀T ht)
  have hx₀1 : (1:ℝ) ≤ x₀ := by linarith
  have hx₀0 : (0:ℝ) < x₀ := by linarith
  set Cl : ℝ := Real.sqrt x₀ with hCldef
  have hCl1 : (1:ℝ) ≤ Cl := by
    rw [hCldef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx₀1
  have hCl0 : (0:ℝ) < Cl := by linarith
  -- pick a rung where the ladder has reached the short windows and the base is beyond `B`
  obtain ⟨N, hN⟩ := eventually_ladderLen_eq (θ := θ) (le_of_lt hθ0) hCl0 hx₀0
  have htend := ladderBase_tendsto (θ := θ) (le_of_lt hθ0) hCl0 hx₀0
  obtain ⟨M, hM⟩ := (htend.eventually_ge_atTop (max B 4)).exists_forall_of_atTop
  set k : ℕ := max N M with hkdef
  have hkN : N ≤ k := le_max_left _ _
  have hkM : M ≤ k := le_max_right _ _
  set b : ℝ := ladderBase θ Cl x₀ (k + 1) with hbdef
  have hbge : max B 4 ≤ b := by
    rw [hbdef]
    exact hM (k + 1) (by omega)
  have hb4 : (4:ℝ) ≤ b := le_trans (le_max_right _ _) hbge
  have hbB : B ≤ b := le_trans (le_max_left _ _) hbge
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hlogb : (1:ℝ) ≤ Real.log b := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hb4)
  set u : ℕ → ℂ := ladderLimit 4 dq θ Cl x₀ (fun _ => 1) with hudef
  have hunorm : ∀ n, ‖u n‖ = 1 := norm_ladderLimit 4 dq θ Cl x₀ (fun _ => by simp)
  refine ⟨b, u, hb4, hbB, hunorm, ?_, ?_⟩
  · intro m hm
    have hbound := hladder x₀ hx₀X (min 1 (datumSlack 4)) hdqs (min_le_right _ _)
      (fun _ => 1) (fun _ => by simp) k m (by omega)
    rw [← hbdef] at hbound
    have hprof : arithJumpProfile dq (characterSource u) m b
        = arithJumpProfile dq
            (characterSource (ladderChar 4 dq θ Cl x₀ (fun _ => 1) (k + 1))) m b := by
      rw [hudef, hbdef]
      exact arithJumpProfile_ladderLimit 4 dq (le_of_lt hθ0) hCl1 hx₀1 (fun _ => 1) m (k + 1)
    rw [hprof]
    refine le_trans hbound ?_
    -- the ladder length at rung `k` is `base_k ^ θ ≤ b ^ θ`
    have hlen : ladderLen θ Cl x₀ k = (ladderBase θ Cl x₀ k) ^ θ := hN k hkN
    have hbasele : ladderBase θ Cl x₀ k ≤ b := by
      rw [hbdef]
      exact ladderBase_le_succ θ hCl0 hx₀0 k
    have hbasepos : 0 < ladderBase θ Cl x₀ k := ladderBase_pos θ hCl0 hx₀0 k
    have hlenle : ladderLen θ Cl x₀ k ≤ b ^ θ := by
      rw [hlen]
      exact Real.rpow_le_rpow (le_of_lt hbasepos) hbasele (le_of_lt hθ0)
    have hlen0 : (0:ℝ) ≤ ladderLen θ Cl x₀ k := le_of_lt (ladderLen_pos θ hCl0 hx₀0 k)
    have hfac : (1:ℝ) ≤ ((m.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
    have hpow : (ladderLen θ Cl x₀ k) ^ m ≤ (b ^ θ) ^ m := pow_le_pow_left₀ hlen0 hlenle m
    have hbpow : (b ^ θ) ^ m = b ^ ((m : ℝ) * θ) := by
      rw [← Real.rpow_natCast (b ^ θ) m, ← Real.rpow_mul (le_of_lt hb0)]
      ring_nf
    have hmono : b ^ ((m : ℝ) * θ) ≤ b ^ (((m : ℝ) + 1) * θ) := by
      refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
      nlinarith [hθ0]
    have hstep : (ladderLen θ Cl x₀ k) ^ m / ((m.factorial : ℕ) : ℝ)
        ≤ b ^ (((m : ℝ) + 1) * θ) := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : (ladderLen θ Cl x₀ k) ^ m ≤ b ^ (((m : ℝ) + 1) * θ) := by
        calc (ladderLen θ Cl x₀ k) ^ m ≤ (b ^ θ) ^ m := hpow
          _ = b ^ ((m : ℝ) * θ) := hbpow
          _ ≤ b ^ (((m : ℝ) + 1) * θ) := hmono
      have h2 : (0:ℝ) ≤ b ^ (((m : ℝ) + 1) * θ) := Real.rpow_nonneg (le_of_lt hb0) _
      nlinarith [h1, h2, hfac]
    have hlogpos : (0:ℝ) ≤ Real.log b := by linarith
    calc (ladderLen θ Cl x₀ k) ^ m / ((m.factorial : ℕ) : ℝ) * ((4:ℕ) * Real.log b)
        ≤ b ^ (((m : ℝ) + 1) * θ) * ((4:ℕ) * Real.log b) := by
          refine mul_le_mul_of_nonneg_right hstep ?_
          push_cast
          linarith
      _ = 4 * b ^ (((m : ℝ) + 1) * θ) * Real.log b := by
          push_cast
          ring
  · have hbound := hladder x₀ hx₀X (min 1 (datumSlack 4)) hdqs (min_le_right _ _)
      (fun _ => 1) (fun _ => by simp) k 3 (by omega)
    rw [← hbdef] at hbound
    have hprof : arithJumpProfile dq (characterSource u) 3 b
        = arithJumpProfile dq
            (characterSource (ladderChar 4 dq θ Cl x₀ (fun _ => 1) (k + 1))) 3 b := by
      rw [hudef, hbdef]
      exact arithJumpProfile_ladderLimit 4 dq (le_of_lt hθ0) hCl1 hx₀1 (fun _ => 1) 3 (k + 1)
    rw [hprof]
    refine le_trans hbound ?_
    have hlen : ladderLen θ Cl x₀ k = (ladderBase θ Cl x₀ k) ^ θ := hN k hkN
    have hbasele : ladderBase θ Cl x₀ k ≤ b := by
      rw [hbdef]
      exact ladderBase_le_succ θ hCl0 hx₀0 k
    have hbasepos : 0 < ladderBase θ Cl x₀ k := ladderBase_pos θ hCl0 hx₀0 k
    have hlenle : ladderLen θ Cl x₀ k ≤ b ^ θ := by
      rw [hlen]
      exact Real.rpow_le_rpow (le_of_lt hbasepos) hbasele (le_of_lt hθ0)
    have hlen0 : (0:ℝ) ≤ ladderLen θ Cl x₀ k := le_of_lt (ladderLen_pos θ hCl0 hx₀0 k)
    have hfac : (1:ℝ) ≤ (((3:ℕ).factorial : ℕ) : ℝ) := by norm_num
    have hpow : (ladderLen θ Cl x₀ k) ^ (3:ℕ) ≤ (b ^ θ) ^ (3:ℕ) :=
      pow_le_pow_left₀ hlen0 hlenle 3
    have hbpow : (b ^ θ) ^ (3:ℕ) = b ^ ((3:ℝ) * θ) := by
      rw [← Real.rpow_natCast (b ^ θ) 3, ← Real.rpow_mul (le_of_lt hb0)]
      norm_num
      ring_nf
    have hmono : b ^ ((3:ℝ) * θ) ≤ b ^ ((3:ℝ) * θ + 1) := by
      refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
      linarith
    have hstep : (ladderLen θ Cl x₀ k) ^ (3:ℕ) / (((3:ℕ).factorial : ℕ) : ℝ)
        ≤ b ^ ((3:ℝ) * θ + 1) := by
      rw [div_le_iff₀ (by norm_num)]
      have h1 : (ladderLen θ Cl x₀ k) ^ (3:ℕ) ≤ b ^ ((3:ℝ) * θ + 1) := by
        calc (ladderLen θ Cl x₀ k) ^ (3:ℕ) ≤ (b ^ θ) ^ (3:ℕ) := hpow
          _ = b ^ ((3:ℝ) * θ) := hbpow
          _ ≤ b ^ ((3:ℝ) * θ + 1) := hmono
      have h2 : (0:ℝ) ≤ b ^ ((3:ℝ) * θ + 1) := Real.rpow_nonneg (le_of_lt hb0) _
      nlinarith [h1, h2]
    have hlogpos : (0:ℝ) ≤ Real.log b := by linarith
    have hcast : ((3:ℕ) : ℝ) = (3:ℝ) := by norm_num
    rw [hcast]
    calc (ladderLen θ Cl x₀ k) ^ (3:ℕ) / (((3:ℕ).factorial : ℕ) : ℝ) * ((4:ℕ) * Real.log b)
        ≤ b ^ ((3:ℝ) * θ + 1) * ((4:ℕ) * Real.log b) := by
          refine mul_le_mul_of_nonneg_right hstep ?_
          push_cast
          linarith
      _ = 4 * b ^ ((3:ℝ) * θ + 1) * Real.log b := by
          push_cast
          ring

/-! ## Iterating the stages -/

open scoped Classical in
/-- The threshold beyond which the stacking step of order `J` with constant `C` applies. -/
noncomputable def stackThr {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) (J : ℕ) (C : ℝ) : ℝ :=
  if h : 3 ≤ J ∧ 0 < C then
    (exists_stack_step halpha hαθ hθ1 hθ23 J h.1 C h.2 hdq hdq0).choose else 1

open scoped Classical in
theorem stackThr_spec {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) {J : ℕ} (hJ : 3 ≤ J) {C : ℝ} (hC : 0 < C) :
    ∀ b : ℝ, stackThr halpha hαθ hθ1 hθ23 hdq hdq0 J C ≤ b → ∀ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) →
      StackInv dq θ J b C u →
      ∃ (C' : ℝ) (u' : ℕ → ℂ), 0 < C' ∧ C' ≤ b ^ (2 * θ) ∧ (∀ n, ‖u' n‖ = 1) ∧
        (∀ n : ℕ, (n : ℝ) ≤ b → u' n = u n) ∧
        (∀ x : ℝ, b ≤ x → ∀ j : ℕ, j < J + 1 →
          ‖arithJumpProfile dq (characterSource u') j x‖
            ≤ C' * x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) * Real.log x) ∧
        ∃ X' : ℝ, b < X' ∧ ∀ b' : ℝ, X' ≤ b' → StackInv dq θ (J + 1) b' C' u' := by
  have hspec := (exists_stack_step halpha hαθ hθ1 hθ23 J hJ C hC hdq hdq0).choose_spec
  intro b hb
  rw [stackThr, dif_pos ⟨hJ, hC⟩] at hb
  exact hspec.2 b hb

/-- The stacking state is admissible at order `J`. -/
def StackOK {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
    (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) (J : ℕ) (s : ℝ × ℝ × (ℕ → ℂ)) : Prop :=
  4 ≤ s.1 ∧ 0 < s.2.1 ∧ (∀ n, ‖s.2.2 n‖ = 1) ∧ StackInv dq θ J s.1 s.2.1 s.2.2 ∧
    stackThr halpha hαθ hθ1 hθ23 hdq hdq0 J s.2.1 ≤ s.1

set_option maxHeartbeats 1000000 in
/-- One admissible stage advance. -/
theorem exists_stack_next {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) {J : ℕ} (hJ : 3 ≤ J) (s : ℝ × ℝ × (ℕ → ℂ))
    (hs : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 J s) :
    ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (J + 1) t ∧ s.1 + 1 ≤ t.1 ∧
      (∀ n : ℕ, (n : ℝ) ≤ s.1 → t.2.2 n = s.2.2 n) ∧
      (∀ x : ℝ, s.1 ≤ x → ∀ j : ℕ, j < J + 1 →
        ‖arithJumpProfile dq (characterSource t.2.2) j x‖
          ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J) + 2 * θ) * Real.log x) := by
  obtain ⟨hb4, hC0, hunorm, hinv, hthr⟩ := hs
  obtain ⟨C', u', hC'0, hC'le, hu'norm, hu'agree, huni, X', hX'gt, hX'inv⟩ :=
    stackThr_spec halpha hαθ hθ1 hθ23 hdq hdq0 hJ hC0 s.1 hthr s.2.2 hunorm hinv
  set b' : ℝ := max (max X' (s.1 + 1))
    (max (stackThr halpha hαθ hθ1 hθ23 hdq hdq0 (J + 1) C') 4) with hb'def
  have hb'X' : X' ≤ b' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb's : s.1 + 1 ≤ b' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb'thr : stackThr halpha hαθ hθ1 hθ23 hdq hdq0 (J + 1) C' ≤ b' :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hb'4 : (4:ℝ) ≤ b' := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨(b', C', u'), ⟨hb'4, hC'0, hu'norm, hX'inv b' hb'X', hb'thr⟩, hb's, hu'agree, ?_⟩
  intro x hx j hj
  refine le_trans (huni x hx j hj) ?_
  have hs4 : (4:ℝ) ≤ s.1 := hb4
  have hx4 : (4:ℝ) ≤ x := le_trans hs4 hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hs0 : (0:ℝ) < s.1 := by linarith
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hC'x : C' ≤ x ^ (2 * θ) := by
    refine le_trans hC'le ?_
    refine Real.rpow_le_rpow (le_of_lt hs0) hx ?_
    have hθ0 : 0 < θ := by linarith
    linarith
  have hpowsplit : x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J) + 2 * θ)
      = x ^ (2 * θ) * x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  rw [hpowsplit]
  have hpow0 : (0:ℝ) ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) :=
    Real.rpow_nonneg (le_of_lt hx0) _
  calc C' * x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) * Real.log x
      ≤ x ^ (2 * θ) * x ^ (((j : ℝ) + 1) * (θ + stackDelta θ J)) * Real.log x := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC'x hpow0) hlogx

attribute [local instance] Classical.propDecidable

/-- The stacking sequence: stage `n` runs at order `3 + n`. -/
noncomputable def stackSeq {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) (s₀ : ℝ × ℝ × (ℕ → ℂ)) :
    ℕ → ℝ × ℝ × (ℕ → ℂ)
  | 0 => s₀
  | (n + 1) =>
      if h : ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + n + 1) t ∧
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 + 1 ≤ t.1 ∧
          (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 →
            t.2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).2.2 m) ∧
          (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 ≤ x → ∀ j : ℕ, j < 3 + n + 1 →
            ‖arithJumpProfile dq (characterSource t.2.2) j x‖
              ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ) * Real.log x) then
        h.choose
      else stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n

theorem stackSeq_succ {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) (s₀ : ℝ × ℝ × (ℕ → ℂ)) (n : ℕ) :
    stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1) =
      if h : ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + n + 1) t ∧
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 + 1 ≤ t.1 ∧
          (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 →
            t.2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).2.2 m) ∧
          (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 ≤ x → ∀ j : ℕ, j < 3 + n + 1 →
            ‖arithJumpProfile dq (characterSource t.2.2) j x‖
              ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ) * Real.log x) then
        h.choose
      else stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n := rfl

set_option maxHeartbeats 1000000 in
/-- Every stage of the stacking sequence is admissible, advances the base, extends the previous
character, and carries the uniform level bound of its order. -/
theorem stackSeq_spec {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) {s₀ : ℝ × ℝ × (ℕ → ℂ)}
    (hs₀ : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 3 s₀) (n : ℕ) :
    StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + n) (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n) ∧
      ((stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 + 1
          ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 ∧
        (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 →
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).2.2 m
            = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).2.2 m) ∧
        (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 ≤ x → ∀ j : ℕ, j < 3 + n + 1 →
          ‖arithJumpProfile dq
              (characterSource (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).2.2) j x‖
            ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ) * Real.log x)) := by
  classical
  induction n with
  | zero =>
      have hOK : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + 0) (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0) := hs₀
      obtain ⟨t, ht⟩ := exists_stack_next halpha hαθ hθ1 hθ23 hdq hdq0 (J := 3 + 0) (by omega)
        (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0) hOK
      have hex : ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + 0 + 1) t ∧
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).1 + 1 ≤ t.1 ∧
          (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).1 →
            t.2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).2.2 m) ∧
          (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).1 ≤ x → ∀ j : ℕ, j < 3 + 0 + 1 →
            ‖arithJumpProfile dq (characterSource t.2.2) j x‖
              ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + 0)) + 2 * θ) * Real.log x) :=
        ⟨t, ht⟩
      have hval : stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (0 + 1) = hex.choose := by
        rw [stackSeq_succ, dif_pos hex]
      refine ⟨hOK, ?_, ?_, ?_⟩ <;> rw [hval]
      · exact (hex.choose_spec).2.1
      · exact (hex.choose_spec).2.2.1
      · exact (hex.choose_spec).2.2.2
  | succ n ih =>
      obtain ⟨hOKn, hstep⟩ := ih
      have hOK : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + (n + 1))
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)) := by
        have hex : ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + n + 1) t ∧
            (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 + 1 ≤ t.1 ∧
            (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 →
              t.2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).2.2 m) ∧
            (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 ≤ x → ∀ j : ℕ, j < 3 + n + 1 →
              ‖arithJumpProfile dq (characterSource t.2.2) j x‖
                ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ) * Real.log x) := by
          obtain ⟨t, ht⟩ := exists_stack_next halpha hαθ hθ1 hθ23 hdq hdq0 (J := 3 + n) (by omega)
            (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n) hOKn
          exact ⟨t, ht⟩
        rw [stackSeq_succ, dif_pos hex]
        have := (hex.choose_spec).1
        simpa [Nat.add_assoc] using this
      obtain ⟨t, ht⟩ := exists_stack_next halpha hαθ hθ1 hθ23 hdq hdq0 (J := 3 + (n + 1)) (by omega)
        (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)) hOK
      have hex : ∃ t : ℝ × ℝ × (ℕ → ℂ), StackOK halpha hαθ hθ1 hθ23 hdq hdq0 (3 + (n + 1) + 1) t ∧
          (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 + 1 ≤ t.1 ∧
          (∀ m : ℕ, (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 →
            t.2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).2.2 m) ∧
          (∀ x : ℝ, (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 ≤ x → ∀ j : ℕ,
            j < 3 + (n + 1) + 1 →
            ‖arithJumpProfile dq (characterSource t.2.2) j x‖
              ≤ x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + (n + 1))) + 2 * θ) * Real.log x) :=
        ⟨t, ht⟩
      have hval : stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1 + 1) = hex.choose := by
        rw [stackSeq_succ, dif_pos hex]
      refine ⟨hOK, ?_, ?_, ?_⟩ <;> rw [hval]
      · exact (hex.choose_spec).2.1
      · exact (hex.choose_spec).2.2.1
      · exact (hex.choose_spec).2.2.2

/-! ## The limiting character -/

/-- The character produced by the whole construction. -/
noncomputable def anderssonChar {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) (s₀ : ℝ × ℝ × (ℕ → ℂ)) : ℕ → ℂ :=
  fun m => (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ m).2.2 m

section
variable {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1)
  (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
  (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v)
  (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) {s₀ : ℝ × ℝ × (ℕ → ℂ)}
  (hs₀ : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 3 s₀)

include hs₀

theorem stackSeq_base_mono (n : ℕ) :
    (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 + 1 ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 :=
  (stackSeq_spec halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ n).2.1

theorem stackSeq_base_ge (n : ℕ) :
    (4:ℝ) + (n : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 := by
  induction n with
  | zero =>
      have h := (stackSeq_spec halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ 0).1.1
      simpa using h
  | succ n ih =>
      have h := stackSeq_base_mono halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ n
      push_cast
      linarith

theorem stackSeq_base_le_of_le {m n : ℕ} (hmn : m ≤ n) :
    (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ m).1 ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.1 hmn
      rw [this]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have := stackSeq_base_mono halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ n
        exact le_trans (ih (Nat.lt_succ_iff.1 hlt)) (by linarith)
      · have : m = n + 1 := le_antisymm hmn hge
        rw [this]

theorem stackSeq_phases_stable {k : ℕ} (n : ℕ) (hkn : k ≤ n) {m : ℕ}
    (hm : (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1) :
    (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).2.2 m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).2.2 m := by
  induction n with
  | zero =>
      have : k = 0 := Nat.le_zero.1 hkn
      rw [this]
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have hkn' : k ≤ n := Nat.lt_succ_iff.1 hlt
        have hle : (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 :=
          le_trans hm (stackSeq_base_le_of_le halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ hkn')
        rw [(stackSeq_spec halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ n).2.2.1 m hle, ih hkn']
      · have : k = n + 1 := le_antisymm hkn hge
        rw [this]

theorem anderssonChar_eq {m k : ℕ} (hm : (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1) :
    anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 s₀ m = (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).2.2 m := by
  rw [anderssonChar]
  rcases Nat.le_total k m with hkm | hmk
  · exact stackSeq_phases_stable halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ m hkm hm
  · have hself : (m : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ m).1 := by
      have := stackSeq_base_ge halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ m
      linarith
    exact (stackSeq_phases_stable halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ k hmk hself).symm

theorem norm_anderssonChar (m : ℕ) : ‖anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 s₀ m‖ = 1 := by
  rw [anderssonChar]
  exact (stackSeq_spec halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ m).1.2.2.1 m

theorem arithJumpProfile_anderssonChar (j k : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1) :
    arithJumpProfile dq (characterSource (anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 s₀)) j x
      = arithJumpProfile dq
          (characterSource (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).2.2) j x := by
  rw [arithJumpProfile, arithJumpProfile]
  congr 1
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1 := by
    have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans (le_trans h2 (Nat.floor_le hx0)) hx
  congr 1
  refine characterSource_congr ?_
  intro p hp
  have hple : (p : ℝ) ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1 := by
    have : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
    linarith

  exact anderssonChar_eq halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ hple

end

set_option maxHeartbeats 1000000 in
/-- **Lemma 7.**  There is a unimodular character whose remainder chain obeys, at every order and
past a threshold, the bound `x^{(j+1)(θ + (1-θ)/3) + 2θ} log x`. -/
theorem exists_andersson_character {α θ : ℝ} (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ)
    (hθ1 : θ < 1) (hθ23 : 2/3 < θ) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) {Mglob : ℝ}
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob)
    (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0)) :
    ∃ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) ∧
      ∀ j : ℕ, ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
        ‖arithJumpProfile dq (characterSource u) j x‖
          ≤ x ^ (((j : ℝ) + 1) * (θ + (1 - θ) / 3) + 2 * θ) * Real.log x := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  obtain ⟨b, u₀, hb4, hbthr, hu₀norm, hinv⟩ :=
    exists_stack_start halpha hαθ hθ1 (stackThr halpha hαθ hθ1 hθ23 hdq hdq0 3 4) hdq hdqb hdq0
  set s₀ : ℝ × ℝ × (ℕ → ℂ) := (b, 4, u₀) with hs₀def
  have hs₀ : StackOK halpha hαθ hθ1 hθ23 hdq hdq0 3 s₀ := ⟨hb4, by norm_num, hu₀norm, hinv, hbthr⟩
  refine ⟨anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 s₀,
    norm_anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 hs₀, ?_⟩
  intro j
  refine ⟨(stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ j).1, ?_, ?_⟩
  · have := stackSeq_base_ge halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ j
    have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  intro x hx
  -- locate the stage owning `x`
  have hbase_ge := stackSeq_base_ge halpha hαθ hθ1 hθ23 hdq hdq0 hs₀
  have hexists : ∃ k : ℕ, x < (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k).1 := by
    obtain ⟨k, hk⟩ := exists_nat_gt x
    refine ⟨k, lt_of_lt_of_le hk ?_⟩
    have := hbase_ge k
    linarith
  set k₀ := Nat.find hexists with hk₀def
  have hk₀ : x < (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ k₀).1 := Nat.find_spec hexists
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · exfalso
      rw [h] at hk₀
      have hx0 : (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).1 ≤ x := by
        have hle : (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ 0).1
            ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ j).1 :=
          stackSeq_base_le_of_le halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ (Nat.zero_le j)
        linarith
      linarith
    · exact h
  obtain ⟨n, hn⟩ : ∃ n, k₀ = n + 1 := ⟨k₀ - 1, by omega⟩
  have hnx : (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 ≤ x := by
    by_contra hcon
    have : x < (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ n).1 := lt_of_not_ge hcon
    exact Nat.find_min hexists (m := n) (by omega) this
  have hxn : x ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 := by
    rw [← hn]
    exact le_of_lt hk₀
  have hxlt : x < (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1 := by
    rw [hn] at hk₀
    exact hk₀
  have hjn : j ≤ n + 1 := by
    by_contra hcon
    have hlt : n + 1 < j := lt_of_not_ge hcon
    have hle : (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).1
        ≤ (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ j).1 :=
      stackSeq_base_le_of_le halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ (by omega)
    linarith
  have hx1 : (1:ℝ) ≤ x := by
    have := hbase_ge j
    linarith
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hprof : arithJumpProfile dq
        (characterSource (anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 s₀)) j x
      = arithJumpProfile dq
          (characterSource (stackSeq halpha hαθ hθ1 hθ23 hdq hdq0 s₀ (n + 1)).2.2) j x :=
    arithJumpProfile_anderssonChar halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ j (n + 1) hx0 hxn
  rw [hprof]
  have hbound := (stackSeq_spec halpha hαθ hθ1 hθ23 hdq hdq0 hs₀ n).2.2.2 x hnx j (by omega)
  refine le_trans hbound ?_
  -- the exponent only improves along the stages
  have hδle : stackDelta θ (3 + n) ≤ (1 - θ) / 3 := by
    rw [stackDelta]
    have h1 : (0:ℝ) < 1 - θ := by linarith
    have h2 : (6:ℝ) ≤ ((3 + n : ℕ) : ℝ) + 3 := by
      have : (3:ℝ) ≤ ((3 + n : ℕ) : ℝ) := by
        push_cast
        have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [h1, h2]
  have hexp : ((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ
      ≤ ((j : ℝ) + 1) * (θ + (1 - θ) / 3) + 2 * θ := by
    have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [hδle, hj0]
  have hmono : x ^ (((j : ℝ) + 1) * (θ + stackDelta θ (3 + n)) + 2 * θ)
      ≤ x ^ (((j : ℝ) + 1) * (θ + (1 - θ) / 3) + 2 * θ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 hexp
  have hlogx : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  exact mul_le_mul_of_nonneg_right hmono hlogx

end RHTower.Sieve

end
