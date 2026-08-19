import GaloisForLFunctions.RHTower.Sieve.CharacterWindowRecursion
import GaloisForLFunctions.RHTower.Sieve.WindowLadder
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The ladder recursion at a fixed order

At a fixed order `J` the character is built along the ladder: one long window absorbs whatever state
the previous orders left, the lengths halve until they reach `x^θ`, and from then on the windows are
short.  Each window resets the whole state to its rounding error, so the invariant is carried with a
single constant.
-/

noncomputable section

open Filter ArithmeticFunction GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- The crude bound on the levels: every level is controlled by the Chebyshev mass. -/
theorem norm_arithProfile_characterSource_le_crude {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {Cψ : ℝ}
    (hCψ : ∀ x : ℝ, 1 ≤ x → chebyshevPsiReal x ≤ Cψ * x) {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    ‖arithProfile (characterSource u) m x‖ ≤ (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Cψ * x) := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [arithProfile]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖characterSource u n * ((truncPow (n : ℝ) m x : ℝ) : ℂ)‖
        ≤ Λ n * (x ^ m / ((m.factorial : ℕ) : ℝ)) := by
    intro n hn
    have hnx : (n : ℝ) ≤ x := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.1 hn).2
      have h2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le hx0)
    have hn1 : (1:ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      exact_mod_cast this
    rw [norm_mul, norm_characterSource_eq hu n, Complex.norm_real, Real.norm_eq_abs,
      truncPow_of_le hnx m, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x - (n : ℝ)) ^ m /
        ((m.factorial : ℕ) : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    refine div_le_div_of_nonneg_right ?_ hfac.le
    exact pow_le_pow_left₀ (by linarith) (by linarith) m
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hpsi : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n) = Chebyshev.psi x := by
    rw [Chebyshev.psi]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    exact Finset.val_inj.mp rfl
  rw [hpsi]
  have hpsile : Chebyshev.psi x ≤ Cψ * x := by
    have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have h0 : (Λ 0 : ℝ) = 0 := by simp
    have heq : Chebyshev.psi x = chebyshevPsiReal x := by
      rw [Chebyshev.psi, chebyshevPsiReal_eq_sum_range, hset,
        Finset.sum_insert (by simp), h0, zero_add]
    rw [heq]
    exact hCψ x hx
  have hnn : (0:ℝ) ≤ x ^ m / ((m.factorial : ℕ) : ℝ) := by positivity
  calc Chebyshev.psi x * (x ^ m / ((m.factorial : ℕ) : ℝ))
      ≤ (Cψ * x) * (x ^ m / ((m.factorial : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hpsile hnn
    _ = (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Cψ * x) := by ring

/-- The crude bound for the full chain: the datum contributes its own linear mass. -/
theorem norm_arithJumpProfile_characterSource_le_crude {dq : ℝ → ℂ} {Mglob : ℝ}
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {Cψ : ℝ}
    (hCψ : ∀ x : ℝ, 1 ≤ x → chebyshevPsiReal x ≤ Cψ * x) {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    ‖arithJumpProfile dq (characterSource u) m x‖
      ≤ (x ^ m / ((m.factorial : ℕ) : ℝ)) * ((Cψ + Mglob) * x) := by
  have h1 : ‖iteratedAntideriv dq (m + 1) x‖
      ≤ (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Mglob * x) :=
    norm_iteratedAntideriv_le hx (fun t _ => hdqb t) m
  have h2 := norm_arithProfile_characterSource_le_crude hu hCψ hx m
  rw [arithJumpProfile]
  refine le_trans (norm_add_le _ _) ?_
  calc ‖iteratedAntideriv dq (m + 1) x‖ + ‖arithProfile (characterSource u) m x‖
      ≤ (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Mglob * x)
        + (x ^ m / ((m.factorial : ℕ) : ℝ)) * (Cψ * x) := add_le_add h1 h2
    _ = (x ^ m / ((m.factorial : ℕ) : ℝ)) * ((Cψ + Mglob) * x) := by ring

/-! ## The recursion along the ladder -/

/-- A phase assignment is good for the window `(x, x+L]` at order `J`. -/
def CharGoodL (J : ℕ) (dq : ℝ → ℂ) (u : ℕ → ℂ) (x L : ℝ) (c : ℕ → ℂ) : Prop :=
  (∀ q ∈ windowPrimes x (x + L), ‖c q‖ = 1) ∧
    ∀ j : ℕ, j < J →
      ‖arithJumpProfile dq (characterSource
          (fun m => if m ∈ windowPrimes x (x + L) then c m else u m)) j (x + L)‖
        ≤ (L ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + L))

open scoped Classical in
/-- The phases after `k` windows of the ladder. -/
noncomputable def ladderChar (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) (u₀ : ℕ → ℂ) : ℕ → (ℕ → ℂ)
  | 0 => u₀
  | (k + 1) =>
      if h : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ k) (ladderBase θ C x₀ k)
          (ladderLen θ C x₀ k) c then
        fun m => if m ∈ windowPrimes (ladderBase θ C x₀ k)
            (ladderBase θ C x₀ k + ladderLen θ C x₀ k) then h.choose m
          else ladderChar J dq θ C x₀ u₀ k m
      else ladderChar J dq θ C x₀ u₀ k

theorem ladderChar_zero (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) (u₀ : ℕ → ℂ) :
    ladderChar J dq θ C x₀ u₀ 0 = u₀ := rfl

open scoped Classical in
theorem ladderChar_succ (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) (u₀ : ℕ → ℂ) (k : ℕ) :
    ladderChar J dq θ C x₀ u₀ (k + 1) =
      if h : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ k) (ladderBase θ C x₀ k)
          (ladderLen θ C x₀ k) c then
        fun m => if m ∈ windowPrimes (ladderBase θ C x₀ k)
            (ladderBase θ C x₀ k + ladderLen θ C x₀ k) then h.choose m
          else ladderChar J dq θ C x₀ u₀ k m
      else ladderChar J dq θ C x₀ u₀ k := rfl

theorem norm_ladderChar (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) {u₀ : ℕ → ℂ} (hu₀ : ∀ n, ‖u₀ n‖ = 1)
    (k : ℕ)
    (n : ℕ) : ‖ladderChar J dq θ C x₀ u₀ k n‖ = 1 := by
  classical
  induction k with
  | zero => rw [ladderChar_zero]; exact hu₀ n
  | succ k ih =>
      rw [ladderChar_succ]
      by_cases h : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ k) (ladderBase θ C x₀ k)
          (ladderLen θ C x₀ k) c
      · rw [dif_pos h]
        by_cases hmem : n ∈ windowPrimes (ladderBase θ C x₀ k)
            (ladderBase θ C x₀ k + ladderLen θ C x₀ k)
        · simp only [if_pos hmem]
          exact (h.choose_spec).1 n hmem
        · simp only [if_neg hmem]
          exact ih
      · rw [dif_neg h]
        exact ih

theorem ladderChar_succ_apply_of_le (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) (u₀ : ℕ → ℂ) (k : ℕ)
    {n : ℕ}
    (hn : (n : ℝ) ≤ ladderBase θ C x₀ k) :
    ladderChar J dq θ C x₀ u₀ (k + 1) n = ladderChar J dq θ C x₀ u₀ k n := by
  classical
  rw [ladderChar_succ]
  by_cases h : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ k) (ladderBase θ C x₀ k)
      (ladderLen θ C x₀ k) c
  · rw [dif_pos h]
    have hnot : n ∉ windowPrimes (ladderBase θ C x₀ k)
        (ladderBase θ C x₀ k + ladderLen θ C x₀ k) := by
      intro hmem
      have hmem' := Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1
      have h1 : ⌊ladderBase θ C x₀ k⌋₊ < n := hmem'.1
      have h2 : n ≤ ⌊ladderBase θ C x₀ k⌋₊ := Nat.le_floor hn
      omega
    simp only [if_neg hnot]
  · rw [dif_neg h]

theorem ladderChar_stable (J : ℕ) (dq : ℝ → ℂ) {θ C x₀ : ℝ} (hC : 0 < C) (hx₀ : 0 < x₀)
    (u₀ : ℕ → ℂ)
    {n k : ℕ} (m : ℕ) (hkm : k ≤ m) (hn : (n : ℝ) ≤ ladderBase θ C x₀ k) :
    ladderChar J dq θ C x₀ u₀ m n = ladderChar J dq θ C x₀ u₀ k n := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.1 hkm
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hlt
        have hle : (n : ℝ) ≤ ladderBase θ C x₀ m :=
          le_trans hn (ladderBase_mono θ hC hx₀ hkm')
        rw [ladderChar_succ_apply_of_le J dq θ C x₀ u₀ m hle, ih hkm']
      · have : k = m + 1 := le_antisymm hkm hge
        rw [this]

/-- The limiting phases of one ladder stage. -/
noncomputable def ladderLimit (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) (u₀ : ℕ → ℂ) : ℕ → ℂ :=
  fun n => ladderChar J dq θ C x₀ u₀ n n

theorem ladderLimit_eq (J : ℕ) (dq : ℝ → ℂ) {θ C x₀ : ℝ} (hθ0 : 0 ≤ θ) (hC : 1 ≤ C) (hx₀ : 1 ≤ x₀)
    (u₀ : ℕ → ℂ) {n k : ℕ} (hn : (n : ℝ) ≤ ladderBase θ C x₀ k) :
    ladderLimit J dq θ C x₀ u₀ n = ladderChar J dq θ C x₀ u₀ k n := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  rw [ladderLimit]
  rcases Nat.le_total k n with hkn | hnk
  · exact ladderChar_stable J dq hC0 hx₀0 u₀ n hkn hn
  · have hself : (n : ℝ) ≤ ladderBase θ C x₀ n := ladderBase_ge_index hθ0 hC hx₀ n
    exact (ladderChar_stable J dq hC0 hx₀0 u₀ k hnk hself).symm

theorem norm_ladderLimit (J : ℕ) (dq : ℝ → ℂ) (θ C x₀ : ℝ) {u₀ : ℕ → ℂ} (hu₀ : ∀ n, ‖u₀ n‖ = 1)
    (n : ℕ) :
    ‖ladderLimit J dq θ C x₀ u₀ n‖ = 1 :=
  norm_ladderChar J dq θ C x₀ hu₀ n n

theorem ladderLimit_eq_of_le_base (J : ℕ) (dq : ℝ → ℂ) {θ C x₀ : ℝ} (hθ0 : 0 ≤ θ) (hC : 1 ≤ C)
    (hx₀ : 1 ≤ x₀)
    (u₀ : ℕ → ℂ) {n : ℕ} (hn : (n : ℝ) ≤ x₀) : ladderLimit J dq θ C x₀ u₀ n = u₀ n := by
  have h := ladderLimit_eq J dq hθ0 hC hx₀ u₀ (k := 0) (by rwa [ladderBase_zero])
  rwa [ladderChar_zero] at h

theorem arithJumpProfile_ladderLimit (J : ℕ) (dq : ℝ → ℂ) {θ C x₀ : ℝ} (hθ0 : 0 ≤ θ) (hC : 1 ≤ C)
    (hx₀ : 1 ≤ x₀)
    (u₀ : ℕ → ℂ) (j k : ℕ) :
    arithJumpProfile dq (characterSource (ladderLimit J dq θ C x₀ u₀)) j (ladderBase θ C x₀ k)
      = arithJumpProfile dq (characterSource (ladderChar J dq θ C x₀ u₀ k)) j
          (ladderBase θ C x₀ k) := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hpos : 0 < ladderBase θ C x₀ k := ladderBase_pos θ hC0 hx₀0 k
  rw [arithJumpProfile, arithJumpProfile]
  congr 1
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ ladderBase θ C x₀ k := by
    have h1 : n ≤ ⌊ladderBase θ C x₀ k⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊ladderBase θ C x₀ k⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le (le_of_lt hpos))
  congr 1
  refine characterSource_congr ?_
  intro m hm
  have hmle : (m : ℝ) ≤ ladderBase θ C x₀ k := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  exact ladderLimit_eq J dq hθ0 hC hx₀ u₀ hmle

/-! ## Admissibility of every ladder window -/

theorem ladder_window_admissible (J : ℕ) (hJ : 0 < J) {α θ : ℝ} (hα0 : 0 < α) (hαθ : α < θ)
    (hθ1 : θ < 1) {C : ℝ} (hC : 1 ≤ C) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ → ∀ k : ℕ,
      ladderBase θ C x₀ k + ladderLen θ C x₀ k ≤ (ladderBase θ C x₀ k) ^ 2 ∧
      4 * (J : ℝ) * (ladderBase θ C x₀ k + ladderLen θ C x₀ k) ^ α ≤ ladderLen θ C x₀ k := by
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  have hd : 0 < θ - α := by linarith
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  set K : ℝ := 4 * (J : ℝ) * (1 + C) ^ α with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have : (0:ℝ) < (1 + C) ^ α := Real.rpow_pos_of_pos (by linarith) α
    positivity
  refine ⟨max (max (1 + C) (K ^ (1 / (θ - α)))) 1, le_max_right _ _, fun x₀ hx₀ k => ?_⟩
  have hx₀1 : (1:ℝ) ≤ x₀ := le_trans (le_max_right _ _) hx₀
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀1
  have hbase : x₀ ≤ ladderBase θ C x₀ k := ladderBase_ge θ hC0 hx₀0 k
  have hb1 : (1:ℝ) ≤ ladderBase θ C x₀ k := le_trans hx₀1 hbase
  have hb0 : (0:ℝ) < ladderBase θ C x₀ k := lt_of_lt_of_le zero_lt_one hb1
  have hlen_le : ladderLen θ C x₀ k ≤ C * ladderBase θ C x₀ k :=
    ladderLen_le_mul (le_of_lt hθ0) (le_of_lt hθ1) hC hx₀1 k
  have hlen_ge : (ladderBase θ C x₀ k) ^ θ ≤ ladderLen θ C x₀ k :=
    rpow_le_ladderLen' (le_of_lt hθ1) hC hx₀1 k
  have hC1 : (1 + C) ≤ ladderBase θ C x₀ k :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hx₀ hbase)
  have hKb : K ^ (1 / (θ - α)) ≤ ladderBase θ C x₀ k :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hx₀ hbase)
  constructor
  · nlinarith [hlen_le, hb1, hC1, hb0]
  · have hsum : ladderBase θ C x₀ k + ladderLen θ C x₀ k
        ≤ (1 + C) * ladderBase θ C x₀ k := by nlinarith [hlen_le]
    have hpow : (ladderBase θ C x₀ k + ladderLen θ C x₀ k) ^ α
        ≤ ((1 + C) * ladderBase θ C x₀ k) ^ α := by
      refine Real.rpow_le_rpow ?_ hsum (le_of_lt hα0)
      have := ladderLen_pos θ hC0 hx₀0 k
      linarith
    have hsplit : ((1 + C) * ladderBase θ C x₀ k) ^ α
        = (1 + C) ^ α * (ladderBase θ C x₀ k) ^ α :=
      Real.mul_rpow (by linarith) (le_of_lt hb0)
    have hKle : K ≤ (ladderBase θ C x₀ k) ^ (θ - α) := by
      have h1 : (K ^ (1 / (θ - α))) ^ (θ - α) ≤ (ladderBase θ C x₀ k) ^ (θ - α) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK0) _) hKb (le_of_lt hd)
      have h2 : (K ^ (1 / (θ - α))) ^ (θ - α) = K := by
        rw [← Real.rpow_mul (le_of_lt hK0), one_div, inv_mul_cancel₀ (ne_of_gt hd),
          Real.rpow_one]
      rwa [h2] at h1
    have hfinal : 4 * (J : ℝ) * ((1 + C) ^ α * (ladderBase θ C x₀ k) ^ α)
        ≤ (ladderBase θ C x₀ k) ^ θ := by
      have hexp : (ladderBase θ C x₀ k) ^ (θ - α) * (ladderBase θ C x₀ k) ^ α
          = (ladderBase θ C x₀ k) ^ θ := by
        rw [← Real.rpow_add hb0]
        ring_nf
      have hbα : (0:ℝ) < (ladderBase θ C x₀ k) ^ α := Real.rpow_pos_of_pos hb0 α
      calc 4 * (J : ℝ) * ((1 + C) ^ α * (ladderBase θ C x₀ k) ^ α)
          = K * (ladderBase θ C x₀ k) ^ α := by
            rw [hKdef]
            ring
        _ ≤ (ladderBase θ C x₀ k) ^ (θ - α) * (ladderBase θ C x₀ k) ^ α :=
            mul_le_mul_of_nonneg_right hKle (le_of_lt hbα)
        _ = (ladderBase θ C x₀ k) ^ θ := hexp
    calc 4 * (J : ℝ) * (ladderBase θ C x₀ k + ladderLen θ C x₀ k) ^ α
        ≤ 4 * (J : ℝ) * ((1 + C) ^ α * (ladderBase θ C x₀ k) ^ α) := by
          rw [← hsplit]
          have h4J : (0:ℝ) ≤ 4 * (J : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hpow h4J
      _ ≤ (ladderBase θ C x₀ k) ^ θ := hfinal
      _ ≤ ladderLen θ C x₀ k := hlen_ge

/-- Admissibility of the windows after the first, uniformly in the ladder constant. -/
theorem ladder_window_admissible_succ (J : ℕ) (hJ : 0 < J) {α θ : ℝ} (hα0 : 0 < α) (hαθ : α < θ)
    (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (C x₀ : ℝ), 1 ≤ C → 1 ≤ x₀ → ∀ k : ℕ,
      X ≤ ladderBase θ C x₀ (k + 1) →
      ladderBase θ C x₀ (k + 1) + ladderLen θ C x₀ (k + 1)
          ≤ (ladderBase θ C x₀ (k + 1)) ^ 2 ∧
        4 * (J : ℝ) * (ladderBase θ C x₀ (k + 1) + ladderLen θ C x₀ (k + 1)) ^ α
          ≤ ladderLen θ C x₀ (k + 1) := by
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  have hd : 0 < θ - α := by linarith
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  set K : ℝ := 4 * (J : ℝ) * 2 ^ α with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have : (0:ℝ) < (2:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    positivity
  refine ⟨max (max 2 (K ^ (1 / (θ - α)))) 1, le_max_right _ _, fun C x₀ hC hx₀ k hb => ?_⟩
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  set b : ℝ := ladderBase θ C x₀ (k + 1) with hbdef
  set L : ℝ := ladderLen θ C x₀ (k + 1) with hLdef
  have hb2 : (2:ℝ) ≤ b := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hb
  have hb0 : (0:ℝ) < b := by linarith
  have hLb : L ≤ b := ladderLen_le_base (le_of_lt hθ0) (le_of_lt hθ1) hC hx₀ k
  have hLge : b ^ θ ≤ L := rpow_le_ladderLen θ C x₀ k
  have hL0 : 0 < L := ladderLen_pos θ hC0 hx₀0 (k + 1)
  have hKb : K ^ (1 / (θ - α)) ≤ b :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hb
  refine ⟨by nlinarith [hLb, hb2], ?_⟩
  have hsum : b + L ≤ 2 * b := by linarith
  have hpow : (b + L) ^ α ≤ (2 * b) ^ α :=
    Real.rpow_le_rpow (by linarith) hsum (le_of_lt hα0)
  have hsplit : (2 * b) ^ α = (2:ℝ) ^ α * b ^ α :=
    Real.mul_rpow (by norm_num) (le_of_lt hb0)
  have hKle : K ≤ b ^ (θ - α) := by
    have h1 : (K ^ (1 / (θ - α))) ^ (θ - α) ≤ b ^ (θ - α) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK0) _) hKb (le_of_lt hd)
    have h2 : (K ^ (1 / (θ - α))) ^ (θ - α) = K := by
      rw [← Real.rpow_mul (le_of_lt hK0), one_div, inv_mul_cancel₀ (ne_of_gt hd), Real.rpow_one]
    rwa [h2] at h1
  have hbα : (0:ℝ) < b ^ α := Real.rpow_pos_of_pos hb0 α
  have hexp : b ^ (θ - α) * b ^ α = b ^ θ := by
    rw [← Real.rpow_add hb0]
    ring_nf
  calc 4 * (J : ℝ) * (b + L) ^ α
      ≤ 4 * (J : ℝ) * ((2:ℝ) ^ α * b ^ α) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = K * b ^ α := by
        rw [hKdef]
        ring
    _ ≤ b ^ (θ - α) * b ^ α := mul_le_mul_of_nonneg_right hKle (le_of_lt hbα)
    _ = b ^ θ := hexp
    _ ≤ L := hLge

/-- Admissibility of the first window, whose length is `x₀^{3/2}`. -/
theorem ladder_window_admissible_zero (J : ℕ) (hJ : 0 < J) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ →
      x₀ + Real.sqrt x₀ * x₀ ≤ x₀ ^ 2 ∧
        4 * (J : ℝ) * (x₀ + Real.sqrt x₀ * x₀) ^ α ≤ Real.sqrt x₀ * x₀ := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hd : 0 < 3 * (1 - α) / 2 := by linarith
  set K : ℝ := 4 * (J : ℝ) * 2 ^ α with hKdef
  have hK0 : 0 < K := by
    rw [hKdef]
    have : (0:ℝ) < (2:ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    positivity
  refine ⟨max (max 4 (K ^ (1 / (3 * (1 - α) / 2)))) 1, le_max_right _ _, fun x₀ hx => ?_⟩
  have hx4 : (4:ℝ) ≤ x₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx0 : (0:ℝ) < x₀ := by linarith
  have hKx : K ^ (1 / (3 * (1 - α) / 2)) ≤ x₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hsqrt : Real.sqrt x₀ * x₀ = x₀ ^ ((3:ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show ((3:ℝ) / 2) = 1 / 2 + 1 by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  have hs2 : (2:ℝ) ≤ Real.sqrt x₀ := by
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx4
  have hspos : (0:ℝ) < Real.sqrt x₀ := by linarith
  have hsq : Real.sqrt x₀ * Real.sqrt x₀ = x₀ := Real.mul_self_sqrt (le_of_lt hx0)
  constructor
  · nlinarith [hs2, hsq, hx4]
  · have hsum : x₀ + Real.sqrt x₀ * x₀ ≤ 2 * (Real.sqrt x₀ * x₀) := by nlinarith [hs2, hx0]
    have hpow : (x₀ + Real.sqrt x₀ * x₀) ^ α ≤ (2 * (x₀ ^ ((3:ℝ) / 2))) ^ α := by
      rw [← hsqrt]
      exact Real.rpow_le_rpow (by positivity) hsum (le_of_lt hα0)
    have hsplit : (2 * (x₀ ^ ((3:ℝ) / 2))) ^ α = (2:ℝ) ^ α * (x₀ ^ ((3:ℝ) / 2)) ^ α :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg (le_of_lt hx0) _)
    have hmul : (x₀ ^ ((3:ℝ) / 2)) ^ α = x₀ ^ ((3:ℝ) / 2 * α) := by
      rw [← Real.rpow_mul (le_of_lt hx0)]
    have hKle : K ≤ x₀ ^ (3 * (1 - α) / 2) := by
      have h1 : (K ^ (1 / (3 * (1 - α) / 2))) ^ (3 * (1 - α) / 2)
          ≤ x₀ ^ (3 * (1 - α) / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hK0) _) hKx (le_of_lt hd)
      have h2 : (K ^ (1 / (3 * (1 - α) / 2))) ^ (3 * (1 - α) / 2) = K := by
        rw [← Real.rpow_mul (le_of_lt hK0), one_div, inv_mul_cancel₀ (ne_of_gt hd),
          Real.rpow_one]
      rwa [h2] at h1
    have hexp : x₀ ^ (3 * (1 - α) / 2) * x₀ ^ ((3:ℝ) / 2 * α) = x₀ ^ ((3:ℝ) / 2) := by
      rw [← Real.rpow_add hx0]
      ring_nf
    have hxα : (0:ℝ) < x₀ ^ ((3:ℝ) / 2 * α) := Real.rpow_pos_of_pos hx0 _
    calc 4 * (J : ℝ) * (x₀ + Real.sqrt x₀ * x₀) ^ α
        ≤ 4 * (J : ℝ) * ((2:ℝ) ^ α * (x₀ ^ ((3:ℝ) / 2)) ^ α) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = K * x₀ ^ ((3:ℝ) / 2 * α) := by
          rw [hKdef, hmul]
          ring
      _ ≤ x₀ ^ (3 * (1 - α) / 2) * x₀ ^ ((3:ℝ) / 2 * α) :=
          mul_le_mul_of_nonneg_right hKle (le_of_lt hxα)
      _ = x₀ ^ ((3:ℝ) / 2) := hexp
      _ = Real.sqrt x₀ * x₀ := hsqrt.symm

/-! ## The size condition, split into its two halves -/

theorem size_condition_of_halves {J : ℕ} {x L K : ℝ}
    (hK : 2 * (J : ℝ) * (2 ^ J * K) ≤ primeWindowFloorL J L / 2)
    (hforced : 2 * (J : ℝ) * forcedMassBoundL x L ≤ primeWindowFloorL J L / 2) :
    2 * (J : ℝ) * (2 ^ J * K + forcedMassBoundL x L) ≤ primeWindowFloorL J L := by
  have h : 2 * (J : ℝ) * (2 ^ J * K + forcedMassBoundL x L)
      = 2 * (J : ℝ) * (2 ^ J * K) + 2 * (J : ℝ) * forcedMassBoundL x L := by ring
  rw [h]
  linarith

/-- The largest datum size a window of order `J` can still absorb. -/
def datumSlack (J : ℕ) : ℝ := 1 / (262144 * (J : ℝ) ^ 2 * blockRayleighConst J)

theorem datumSlack_pos {J : ℕ} (hJ : 0 < J) : 0 < datumSlack J := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  rw [datumSlack]
  positivity

/-- A datum below the slack uses at most a quarter of the window's capacity. -/
theorem datum_quarter {J : ℕ} (hJ : 0 < J) {L Mq : ℝ} (hL : 0 ≤ L)
    (hsmall : Mq ≤ datumSlack J) :
    2 * (J : ℝ) * (Mq * L) ≤ primeWindowFloorL J L / 4 := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  have hkey : Mq * (2 * (J : ℝ)) ≤ 1 / (131072 * (J : ℝ) * blockRayleighConst J) := by
    have h1 : Mq * (2 * (J : ℝ)) ≤ datumSlack J * (2 * (J : ℝ)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    have h2 : datumSlack J * (2 * (J : ℝ)) = 1 / (131072 * (J : ℝ) * blockRayleighConst J) := by
      rw [datumSlack]
      field_simp
      ring
    linarith [h1, h2.le, h2.ge]
  rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
  have hrw : 2 * (J : ℝ) * (Mq * L) * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
      = (Mq * (2 * (J : ℝ))) * (131072 * (J : ℝ) * blockRayleighConst J) * L := by ring
  rw [hrw]
  have hpos : (0:ℝ) < 131072 * (J : ℝ) * blockRayleighConst J := by positivity
  have hstep : (Mq * (2 * (J : ℝ))) * (131072 * (J : ℝ) * blockRayleighConst J) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hkey hpos.le
    calc (Mq * (2 * (J : ℝ))) * (131072 * (J : ℝ) * blockRayleighConst J)
        ≤ (1 / (131072 * (J : ℝ) * blockRayleighConst J))
            * (131072 * (J : ℝ) * blockRayleighConst J) := this
      _ = 1 := by field_simp
  nlinarith [hstep, hL]

/-- A vanishing datum eventually falls below the slack of any fixed order. -/
theorem exists_datum_threshold {dq : ℝ → ℂ} (hdq0 : Filter.Tendsto dq Filter.atTop (nhds 0))
    {J : ℕ} (hJ : 0 < J) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → ‖dq t‖ ≤ min 1 (datumSlack J) := by
  have hpos : 0 < min 1 (datumSlack J) := lt_min one_pos (datumSlack_pos hJ)
  have hev : ∀ᶠ t : ℝ in Filter.atTop, ‖dq t‖ < min 1 (datumSlack J) :=
    NormedAddGroup.tendsto_nhds_zero.1 hdq0 _ hpos
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max T₀ 1, le_max_right _ _,
    fun t ht => le_of_lt (hT₀ t (le_trans (le_max_left _ _) ht))⟩

/-- The size condition, split into a state, a forced and a datum quarter. -/
theorem size_condition_of_quarters {J : ℕ} (hJ : 0 < J) {x L K Mq : ℝ} (hL : 0 ≤ L)
    (hK : 2 * (J : ℝ) * (2 ^ J * K) ≤ primeWindowFloorL J L / 4)
    (hforced : 2 * (J : ℝ) * forcedMassBoundL x L ≤ primeWindowFloorL J L / 4)
    (hdatum : 2 * (J : ℝ) * (Mq * L) ≤ primeWindowFloorL J L / 4) :
    2 * (J : ℝ) * (2 ^ J * K + (forcedMassBoundL x L + Mq * L)) ≤ primeWindowFloorL J L := by
  have h : 2 * (J : ℝ) * (2 ^ J * K + (forcedMassBoundL x L + Mq * L))
      = 2 * (J : ℝ) * (2 ^ J * K) + 2 * (J : ℝ) * forcedMassBoundL x L
        + 2 * (J : ℝ) * (Mq * L) := by ring
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  have hfloor : 0 ≤ primeWindowFloorL J L := by
    rw [primeWindowFloorL]
    positivity
  rw [h]
  linarith

/-- The forced quarter of the size condition holds beyond a threshold. -/
theorem eventually_forced_quarter (J : ℕ) (hJ : 0 < J) {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → x ^ θ ≤ L → x + L ≤ x ^ 2 →
      2 * (J : ℝ) * forcedMassBoundL x L ≤ primeWindowFloorL J L / 4 := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  set c : ℝ := 8 * (2 * (J : ℝ) * (8 / Real.log 2)) * (blockRayleighConst J * (32768 * (J : ℝ)))
    with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1
    (eventually_log_sq_le hc (by linarith : (0:ℝ) < θ / 2))
  refine ⟨max X₀ 4, le_trans (by norm_num) (le_max_right _ _), fun x L hx hL hxy => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxθ : (1:ℝ) ≤ x ^ θ := Real.one_le_rpow hx1 (le_of_lt hθ0)
  have hL1 : (1:ℝ) ≤ L := le_trans hxθ hL
  have hLpos : (0:ℝ) < L := by linarith
  have hsqrtL : x ^ (θ / 2) ≤ Real.sqrt L := by
    have h1 : Real.sqrt (x ^ θ) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    have h2 : Real.sqrt (x ^ θ) = x ^ (θ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hxpos)]
      ring_nf
    rwa [h2] at h1
  have hfb := forcedMassBoundL_le hx4 hL1 hxy
  have hkey : c * (Real.log x) ^ 2 ≤ x ^ (θ / 2) := hX₀ x hxX₀
  have h32 : (0:ℝ) < 32768 * (J : ℝ) := by positivity
  rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hLpos)
  calc 2 * (J : ℝ) * forcedMassBoundL x L * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
      ≤ 2 * (J : ℝ) * ((8 / Real.log 2) * (Real.log x) ^ 2 * Real.sqrt L)
          * (32768 * (J : ℝ) * (blockRayleighConst J * 4)) := by
        have hpos : (0:ℝ) ≤ 2 * (J : ℝ) * (32768 * (J : ℝ) * (blockRayleighConst J * 4)) := by
          positivity
        nlinarith [hfb, hpos]
    _ = (c * (Real.log x) ^ 2) * Real.sqrt L / 2 := by
        rw [hcdef]
        ring
    _ ≤ (x ^ (θ / 2)) * Real.sqrt L / 2 := by
        have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
        nlinarith [hkey, hs]
    _ ≤ (Real.sqrt L) * Real.sqrt L / 2 := by
        have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
        nlinarith [hsqrtL, hs]
    _ = L / 2 := by rw [hsq]
    _ ≤ L := by linarith

/-- The state half of the size condition for the first window. -/
theorem eventually_K_quarter_first (J : ℕ) (hJ : 0 < J) {Cψ : ℝ} (hCψ : 0 < Cψ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ →
      2 * (J : ℝ) * (2 ^ J * (Cψ * x₀)) ≤ primeWindowFloorL J (Real.sqrt x₀ * x₀) / 4 := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  set c : ℝ := 2 * (J : ℝ) * 2 ^ J * Cψ * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
    with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  refine ⟨max (c ^ 2) 1, le_max_right _ _, fun x₀ hx => ?_⟩
  have hx1 : (1:ℝ) ≤ x₀ := le_trans (le_max_right _ _) hx
  have hxc : c ^ 2 ≤ x₀ := le_trans (le_max_left _ _) hx
  have hx0 : (0:ℝ) < x₀ := by linarith
  have hsq : c ≤ Real.sqrt x₀ := by
    have h1 : Real.sqrt (c ^ 2) ≤ Real.sqrt x₀ := Real.sqrt_le_sqrt hxc
    rwa [Real.sqrt_sq (le_of_lt hc)] at h1
  rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
  have hkey : c * x₀ ≤ Real.sqrt x₀ * x₀ := by
    exact mul_le_mul_of_nonneg_right hsq (le_of_lt hx0)
  calc 2 * (J : ℝ) * (2 ^ J * (Cψ * x₀)) * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
      = c * x₀ := by
        rw [hcdef]
        ring
    _ ≤ Real.sqrt x₀ * x₀ := hkey

/-- The state half of the size condition for the later windows. -/
theorem eventually_K_quarter_succ (J : ℕ) (hJ : 0 < J) {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → x ^ θ ≤ L →
      2 * (J : ℝ) * (2 ^ J * (2 ^ J * (J : ℝ) * Real.log x))
        ≤ primeWindowFloorL J L / 4 := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hD : 0 < blockRayleighConst J := blockRayleighConst_pos hJ
  set c : ℝ := 2 * (J : ℝ) * 2 ^ J * (2 ^ J * (J : ℝ))
    * (32768 * (J : ℝ) * (blockRayleighConst J * 4)) with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 (eventually_log_sq_le hc hθ0)
  refine ⟨max (max X₀ 4) 1, le_max_right _ _, fun x L hx hL => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx : (1:ℝ) ≤ Real.log x := by
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
  have hkey : c * (Real.log x) ^ 2 ≤ x ^ θ := hX₀ x hxX₀
  have hlogle : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith [hlogx]
  rw [primeWindowFloorL, div_div, div_div, le_div_iff₀ (by positivity)]
  calc 2 * (J : ℝ) * (2 ^ J * (2 ^ J * (J : ℝ) * Real.log x))
        * (32768 * (J : ℝ) * (blockRayleighConst J * 4))
      = c * Real.log x := by
        rw [hcdef]
        ring
    _ ≤ c * (Real.log x) ^ 2 := mul_le_mul_of_nonneg_left hlogle (le_of_lt hc)
    _ ≤ x ^ θ := hkey
    _ ≤ L := hL

set_option maxHeartbeats 1000000 in
/-- **The ladder recursion closes.**  Beyond a threshold, the phases produced along the ladder keep
every level of the remainder chain at the rounding-error scale of the window just completed. -/
theorem exists_ladder_state_bound (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) {dq : ℝ → ℂ}
    (hdq : ∀ u v : ℝ, IntervalIntegrable dq MeasureTheory.volume u v) {Mglob : ℝ}
    (hdqb : ∀ t : ℝ, ‖dq t‖ ≤ Mglob) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ → ∀ Mq : ℝ, (∀ t : ℝ, x₀ ≤ t → ‖dq t‖ ≤ Mq) →
      Mq ≤ datumSlack J → ∀ u₀ : ℕ → ℂ, (∀ n, ‖u₀ n‖ = 1) →
      ∀ k : ℕ, ∀ j : ℕ, j < J →
        ‖arithJumpProfile dq
            (characterSource (ladderChar J dq θ (Real.sqrt x₀) x₀ u₀ (k + 1))) j
            (ladderBase θ (Real.sqrt x₀) x₀ (k + 1))‖
          ≤ ((ladderLen θ (Real.sqrt x₀) x₀ k) ^ j / ((j.factorial : ℕ) : ℝ))
              * ((J : ℝ) * Real.log (ladderBase θ (Real.sqrt x₀) x₀ (k + 1))) := by
  classical
  have hα0 : 0 < α := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) halpha
  have hθ0 : 0 < θ := lt_trans hα0 hαθ
  have hα1 : α < 1 := lt_trans hαθ hθ1
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_chebyshevPsiReal_le_linear
  have hMglob0 : (0:ℝ) ≤ Mglob := le_trans (norm_nonneg _) (hdqb 0)
  obtain ⟨X₁, hX₁, hstep⟩ := exists_character_window_step_general_full J hJ halpha hα1 hdq
  obtain ⟨X₂, hX₂, hadm0⟩ := ladder_window_admissible_zero J hJ hα0 hα1
  obtain ⟨X₃, hX₃, hadm1⟩ := ladder_window_admissible_succ J hJ hα0 hαθ hθ1
  obtain ⟨X₄, hX₄, hforced⟩ := eventually_forced_quarter J hJ hθ0
  obtain ⟨X₅, hX₅, hKfirst⟩ := eventually_K_quarter_first J hJ
    (by linarith : (0:ℝ) < Cψ + Mglob)
  obtain ⟨X₆, hX₆, hKsucc⟩ := eventually_K_quarter_succ J hJ hθ0
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ (max X₅ (max X₆ 4))))), ?_, ?_⟩
  · refine le_trans (by norm_num : (1:ℝ) ≤ 4) ?_
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
  intro x₀ hx₀ Mq hdqs hMqsmall u₀ hu₀
  have hX1le : X₁ ≤ x₀ := le_trans (le_max_left _ _) hx₀
  have hX2le : X₂ ≤ x₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx₀
  have hX3le : X₃ ≤ x₀ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx₀
  have hX4le : X₄ ≤ x₀ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hx₀
  have hX5le : X₅ ≤ x₀ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) hx₀
  have hX6le : X₆ ≤ x₀ :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))))) hx₀
  have hx4 : (4:ℝ) ≤ x₀ :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))))) hx₀
  have hx1 : (1:ℝ) ≤ x₀ := by linarith
  have hx0 : (0:ℝ) < x₀ := by linarith
  set C : ℝ := Real.sqrt x₀ with hCdef
  have hC1 : (1:ℝ) ≤ C := by
    rw [hCdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hbase_ge : ∀ k, x₀ ≤ ladderBase θ C x₀ k := ladderBase_ge θ hC0 hx0
  have hlen_pos : ∀ k, 0 < ladderLen θ C x₀ k := ladderLen_pos θ hC0 hx0
  have hbase_pos : ∀ k, 0 < ladderBase θ C x₀ k := ladderBase_pos θ hC0 hx0
  have hunimod : ∀ k n, ‖ladderChar J dq θ C x₀ u₀ k n‖ = 1 := norm_ladderChar J dq θ C x₀ hu₀
  have hprime : ∀ k, ∀ p : ℕ, Nat.Prime p → ‖ladderChar J dq θ C x₀ u₀ k p‖ = 1 :=
    fun k p _ => hunimod k p
  intro k
  induction k with
  | zero =>
      intro j hj
      have hb0 : ladderBase θ C x₀ 0 = x₀ := ladderBase_zero θ C x₀
      have hl0 : ladderLen θ C x₀ 0 = C * x₀ := ladderLen_zero θ C x₀
      obtain ⟨hsq, hadm⟩ := hadm0 x₀ hX2le
      have hstate : ∀ m : ℕ, m < J →
          ‖arithJumpProfile dq (characterSource u₀) m x₀‖
            ≤ ((C * x₀) ^ m / ((m.factorial : ℕ) : ℝ)) * ((Cψ + Mglob) * x₀) := by
        intro m _
        refine le_trans (norm_arithJumpProfile_characterSource_le_crude hdqb
          (fun p _ => hu₀ p) hCψ hx1 m) ?_
        have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hxle : x₀ ^ m ≤ (C * x₀) ^ m := by
          refine pow_le_pow_left₀ (le_of_lt hx0) ?_ m
          nlinarith [hC1, hx0]
        have hKnn : (0:ℝ) ≤ (Cψ + Mglob) * x₀ := by positivity
        refine mul_le_mul_of_nonneg_right ?_ hKnn
        exact div_le_div_of_nonneg_right hxle hfac.le
      have hsize : 2 * (J : ℝ) * (2 ^ J * ((Cψ + Mglob) * x₀)
            + (forcedMassBoundL x₀ (C * x₀) + Mq * (C * x₀)))
          ≤ primeWindowFloorL J (C * x₀) := by
        refine size_condition_of_quarters hJ (by positivity) ?_ ?_ ?_
        · have := hKfirst x₀ hX5le
          rwa [← hCdef] at this
        · refine hforced x₀ (C * x₀) hX4le ?_ ?_
          · have h1 : x₀ ^ θ ≤ x₀ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hθ1)
            rw [Real.rpow_one] at h1
            nlinarith [h1, hC1, hx0]
          · rw [hCdef]
            exact hsq
        · exact datum_quarter hJ (by positivity) hMqsmall
      obtain ⟨c, hc1, hc2⟩ := hstep x₀ (C * x₀) hX1le (by positivity)
        (by rw [hCdef]; exact hsq) (by rw [hCdef]; exact hadm) u₀ ((Cψ + Mglob) * x₀) Mq
        (by positivity) (fun t ht => hdqs t ht.1) (fun p _ => hu₀ p) hstate hsize
      have hex : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ 0) (ladderBase θ C x₀ 0)
          (ladderLen θ C x₀ 0) c := by
        refine ⟨c, ?_, ?_⟩
        · rw [hb0, hl0]
          exact hc1
        · rw [ladderChar_zero, hb0, hl0]
          exact hc2
      rw [ladderChar_succ, dif_pos hex]
      exact (hex.choose_spec).2 j hj
  | succ k ih =>
      intro j hj
      have hbk : X₃ ≤ ladderBase θ C x₀ (k + 1) := le_trans hX3le (hbase_ge (k + 1))
      obtain ⟨hsq, hadm⟩ := hadm1 C x₀ hC1 hx1 k hbk
      have hlenle : ladderLen θ C x₀ k ≤ 2 * ladderLen θ C x₀ (k + 1) :=
        ladderLen_le_two_mul θ C x₀ k
      have hlogb : 0 ≤ Real.log (ladderBase θ C x₀ (k + 1)) := by
        refine Real.log_nonneg ?_
        exact le_trans hx1 (hbase_ge (k + 1))
      have hstate : ∀ m : ℕ, m < J →
          ‖arithJumpProfile dq (characterSource (ladderChar J dq θ C x₀ u₀ (k + 1))) m
              (ladderBase θ C x₀ (k + 1))‖
            ≤ ((ladderLen θ C x₀ (k + 1)) ^ m / ((m.factorial : ℕ) : ℝ))
                * (2 ^ J * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1)))) := by
        intro m hm
        refine le_trans (ih m hm) ?_
        have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
        have hpow : (ladderLen θ C x₀ k) ^ m
            ≤ 2 ^ J * (ladderLen θ C x₀ (k + 1)) ^ m := by
          have h1 : (ladderLen θ C x₀ k) ^ m ≤ (2 * ladderLen θ C x₀ (k + 1)) ^ m :=
            pow_le_pow_left₀ (le_of_lt (hlen_pos k)) hlenle m
          have h2 : (2 * ladderLen θ C x₀ (k + 1)) ^ m
              = 2 ^ m * (ladderLen θ C x₀ (k + 1)) ^ m := by
            rw [mul_pow]
          have h3 : (2:ℝ) ^ m ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (le_of_lt hm)
          have h4 : (0:ℝ) ≤ (ladderLen θ C x₀ (k + 1)) ^ m :=
            pow_nonneg (le_of_lt (hlen_pos (k + 1))) m
          calc (ladderLen θ C x₀ k) ^ m ≤ 2 ^ m * (ladderLen θ C x₀ (k + 1)) ^ m := by
                rw [← h2]; exact h1
            _ ≤ 2 ^ J * (ladderLen θ C x₀ (k + 1)) ^ m :=
                mul_le_mul_of_nonneg_right h3 h4
        have hJlog : (0:ℝ) ≤ (J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1)) :=
          mul_nonneg (Nat.cast_nonneg J) hlogb
        calc (ladderLen θ C x₀ k) ^ m / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1)))
            ≤ (2 ^ J * (ladderLen θ C x₀ (k + 1)) ^ m) / ((m.factorial : ℕ) : ℝ)
              * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1))) := by
              refine mul_le_mul_of_nonneg_right ?_ hJlog
              exact div_le_div_of_nonneg_right hpow hfac.le
          _ = (ladderLen θ C x₀ (k + 1)) ^ m / ((m.factorial : ℕ) : ℝ)
              * (2 ^ J * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1)))) := by
              field_simp
      have hsize : 2 * (J : ℝ) * (2 ^ J * (2 ^ J * ((J : ℝ)
            * Real.log (ladderBase θ C x₀ (k + 1))))
          + (forcedMassBoundL (ladderBase θ C x₀ (k + 1)) (ladderLen θ C x₀ (k + 1))
            + Mq * (ladderLen θ C x₀ (k + 1))))
          ≤ primeWindowFloorL J (ladderLen θ C x₀ (k + 1)) := by
        refine size_condition_of_quarters hJ (le_of_lt (hlen_pos (k + 1))) ?_ ?_ ?_
        · have hkey := hKsucc (ladderBase θ C x₀ (k + 1)) (ladderLen θ C x₀ (k + 1))
            (le_trans hX6le (hbase_ge (k + 1))) (rpow_le_ladderLen θ C x₀ k)
          have hassoc : 2 ^ J * (2 ^ J * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1))))
              = 2 ^ J * (2 ^ J * (J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1))) := by ring
          rw [hassoc]
          exact hkey
        · exact hforced (ladderBase θ C x₀ (k + 1)) (ladderLen θ C x₀ (k + 1))
            (le_trans hX4le (hbase_ge (k + 1))) (rpow_le_ladderLen θ C x₀ k) hsq
        · exact datum_quarter hJ (le_of_lt (hlen_pos (k + 1))) hMqsmall
      obtain ⟨c, hc1, hc2⟩ := hstep (ladderBase θ C x₀ (k + 1)) (ladderLen θ C x₀ (k + 1))
        (le_trans hX1le (hbase_ge (k + 1))) (hlen_pos (k + 1)) hsq hadm
        (ladderChar J dq θ C x₀ u₀ (k + 1))
        (2 ^ J * ((J : ℝ) * Real.log (ladderBase θ C x₀ (k + 1)))) Mq (by positivity)
        (fun t ht => hdqs t (le_trans (hbase_ge (k + 1)) ht.1))
        (hprime (k + 1)) hstate hsize
      have hex : ∃ c, CharGoodL J dq (ladderChar J dq θ C x₀ u₀ (k + 1)) (ladderBase θ C x₀ (k + 1))
          (ladderLen θ C x₀ (k + 1)) c := ⟨c, hc1, hc2⟩
      rw [ladderChar_succ, dif_pos hex]
      exact (hex.choose_spec).2 j hj

end RHTower.Sieve

end
