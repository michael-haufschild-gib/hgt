import GaloisForLFunctions.RHTower.Sieve.CharacterWindowStep
import GaloisForLFunctions.RHTower.AnderssonWindowRecursion

/-!
# The character recursion

The window step is iterated along the window sequence `x_{k+1} = x_k + x_k^θ`, carrying the phases
of a character as the state.  Each stage fixes the phases at its own window's primes; the stages
agree below the current base point, so they define one character, and the levels of the remainder
chain of its source stay bounded at every window endpoint.
-/

noncomputable section

open Filter Asymptotics ArithmeticFunction GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- A phase assignment is good for a window when it is unimodular at the window primes and keeps
every level small at the right endpoint. -/
def CharGood (J : ℕ) (θ : ℝ) (u : ℕ → ℂ) (x : ℝ) (c : ℕ → ℂ) : Prop :=
  (∀ q ∈ windowPrimes x (x + x ^ θ), ‖c q‖ = 1) ∧
    ∀ j : ℕ, j < J →
      ‖arithProfile (characterSource
          (fun m => if m ∈ windowPrimes x (x + x ^ θ) then c m else u m)) j (x + x ^ θ)‖
        ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + x ^ θ))

open scoped Classical in
/-- The phases after `k` windows. -/
noncomputable def charStep (J : ℕ) (θ x₀ : ℝ) : ℕ → (ℕ → ℂ)
  | 0 => fun _ => 1
  | (k + 1) =>
      if h : ∃ c, CharGood J θ (charStep J θ x₀ k) (windowSeq θ x₀ k) c then
        fun m => if m ∈ windowPrimes (windowSeq θ x₀ k)
            (windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ) then h.choose m
          else charStep J θ x₀ k m
      else charStep J θ x₀ k

theorem charStep_zero (J : ℕ) (θ x₀ : ℝ) : charStep J θ x₀ 0 = fun _ => 1 := rfl

open scoped Classical in
theorem charStep_succ (J : ℕ) (θ x₀ : ℝ) (k : ℕ) :
    charStep J θ x₀ (k + 1) =
      if h : ∃ c, CharGood J θ (charStep J θ x₀ k) (windowSeq θ x₀ k) c then
        fun m => if m ∈ windowPrimes (windowSeq θ x₀ k)
            (windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ) then h.choose m
          else charStep J θ x₀ k m
      else charStep J θ x₀ k := rfl

/-- The phases stay unimodular at the primes. -/
theorem norm_charStep (J : ℕ) (θ x₀ : ℝ) (k : ℕ) (p : ℕ) :
    ‖charStep J θ x₀ k p‖ = 1 := by
  classical
  induction k with
  | zero => rw [charStep_zero]; simp
  | succ k ih =>
      rw [charStep_succ]
      by_cases h : ∃ c, CharGood J θ (charStep J θ x₀ k) (windowSeq θ x₀ k) c
      · rw [dif_pos h]
        by_cases hmem : p ∈ windowPrimes (windowSeq θ x₀ k)
            (windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ)
        · rw [if_pos hmem]
          exact (h.choose_spec).1 p hmem
        · rw [if_neg hmem]
          exact ih
      · rw [dif_neg h]
        exact ih

/-- Phases already fixed are never revised. -/
theorem charStep_succ_apply_of_le (J : ℕ) {θ x₀ : ℝ} (k : ℕ) {n : ℕ}
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    charStep J θ x₀ (k + 1) n = charStep J θ x₀ k n := by
  classical
  rw [charStep_succ]
  by_cases h : ∃ c, CharGood J θ (charStep J θ x₀ k) (windowSeq θ x₀ k) c
  · rw [dif_pos h]
    have hnot : n ∉ windowPrimes (windowSeq θ x₀ k)
        (windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ) := by
      intro hmem
      have hmem' := Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1
      have h1 : ⌊windowSeq θ x₀ k⌋₊ < n := hmem'.1
      have h2 : n ≤ ⌊windowSeq θ x₀ k⌋₊ := Nat.le_floor hn
      omega
    simp only [if_neg hnot]
  · rw [dif_neg h]

theorem charStep_stable (J : ℕ) {θ x₀ : ℝ} (hx₀ : 0 < x₀) {n k : ℕ} (m : ℕ) (hkm : k ≤ m)
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    charStep J θ x₀ m n = charStep J θ x₀ k n := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.1 hkm
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hlt
        have hle : (n : ℝ) ≤ windowSeq θ x₀ m := le_trans hn (windowSeq_mono hx₀ hkm')
        rw [charStep_succ_apply_of_le J m hle, ih hkm']
      · have : k = m + 1 := le_antisymm hkm hge
        rw [this]

/-- The limiting phases. -/
noncomputable def anderssonPhases (J : ℕ) (θ x₀ : ℝ) : ℕ → ℂ :=
  fun n => charStep J θ x₀ n n

theorem anderssonPhases_eq (J : ℕ) {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) {n k : ℕ}
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    anderssonPhases J θ x₀ n = charStep J θ x₀ k n := by
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  rw [anderssonPhases]
  rcases Nat.le_total k n with hkn | hnk
  · exact charStep_stable J hx₀0 n hkn hn
  · have hself : (n : ℝ) ≤ windowSeq θ x₀ n := windowSeq_ge_index hx₀ hθ n
    exact (charStep_stable J hx₀0 k hnk hself).symm

theorem norm_anderssonPhases (J : ℕ) (θ x₀ : ℝ) (p : ℕ) :
    ‖anderssonPhases J θ x₀ p‖ = 1 :=
  norm_charStep J θ x₀ p p

/-- At a window endpoint the limiting character has the same levels as the finite stage. -/
theorem arithProfile_characterSource_anderssonPhases (J : ℕ) {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀)
    (hθ : 0 ≤ θ) (j k : ℕ) :
    arithProfile (characterSource (anderssonPhases J θ x₀)) j (windowSeq θ x₀ k)
      = arithProfile (characterSource (charStep J θ x₀ k)) j (windowSeq θ x₀ k) := by
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hpos : 0 < windowSeq θ x₀ k := windowSeq_pos hx₀0 k
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ windowSeq θ x₀ k := by
    have h1 : n ≤ ⌊windowSeq θ x₀ k⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊windowSeq θ x₀ k⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le (le_of_lt hpos))
  congr 1
  refine characterSource_congr ?_
  intro m hm
  have hmle : (m : ℝ) ≤ windowSeq θ x₀ k := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
    linarith
  exact anderssonPhases_eq J hx₀ hθ hmle

/-! ## The recursion closes with the forced mass included -/

theorem eventually_log_sq_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ x : ℝ in atTop, c * (Real.log x) ^ 2 ≤ x ^ r := by
  have hhalf : 0 < r / 2 := by linarith
  have hε : 0 < Real.sqrt (1 / c) := Real.sqrt_pos.2 (by positivity)
  have h := (isLittleO_log_rpow_atTop hhalf).def (c := Real.sqrt (1 / c)) hε
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrp : (0:ℝ) < x ^ (r / 2) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_pos hrp] at hx
  have hsq : (Real.log x) ^ 2 ≤ (Real.sqrt (1 / c)) ^ 2 * (x ^ (r / 2)) ^ 2 := by
    have := mul_le_mul hx hx hlog (le_of_lt (by positivity))
    calc (Real.log x) ^ 2 = Real.log x * Real.log x := by ring
      _ ≤ (Real.sqrt (1 / c) * x ^ (r / 2)) * (Real.sqrt (1 / c) * x ^ (r / 2)) := this
      _ = (Real.sqrt (1 / c)) ^ 2 * (x ^ (r / 2)) ^ 2 := by ring
  have hsqrt : (Real.sqrt (1 / c)) ^ 2 = 1 / c := Real.sq_sqrt (by positivity)
  have hpow : (x ^ (r / 2)) ^ 2 = x ^ r := by
    rw [← Real.rpow_natCast (x ^ (r / 2)) 2, ← Real.rpow_mul (le_of_lt hxpos)]
    norm_num
  rw [hsqrt, hpow] at hsq
  calc c * (Real.log x) ^ 2 ≤ c * (1 / c * x ^ r) := by
        exact mul_le_mul_of_nonneg_left hsq (le_of_lt hc)
    _ = x ^ r := by field_simp

theorem forcedMassBound_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {x : ℝ} (hx : 4 ≤ x) :
    forcedMassBound θ x ≤ (8 / Real.log 2) * (Real.log x) ^ 2 * x ^ (θ / 2) := by
  have hxpos : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hΔ : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hθ1)
      _ = x := Real.rpow_one x
  have hy : x + x ^ θ ≤ x ^ 2 := by nlinarith [hΔ, hx]
  have hlogy : Real.log (x + x ^ θ) ≤ 2 * Real.log x := by
    have hpos : (0:ℝ) < x + x ^ θ := by
      have := Real.rpow_pos_of_pos hxpos θ
      linarith
    have h1 : Real.log (x + x ^ θ) ≤ Real.log (x ^ 2) := Real.log_le_log hpos hy
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogy0 : 0 ≤ Real.log (x + x ^ θ) := by
    refine Real.log_nonneg ?_
    have := Real.rpow_pos_of_pos hxpos θ
    linarith
  have hsqrt : Real.sqrt (x ^ θ) = x ^ (θ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hxpos)]
    ring_nf
  have hone : (1:ℝ) ≤ x ^ (θ / 2) := Real.one_le_rpow hx1 (by linarith)
  rw [forcedMassBound, forcedMassBoundL, hsqrt]
  calc (Real.log (x + x ^ θ) / Real.log 2) * (x ^ (θ / 2) + 1) * Real.log (x + x ^ θ)
      ≤ ((2 * Real.log x) / Real.log 2) * (2 * x ^ (θ / 2)) * (2 * Real.log x) := by
        gcongr
        linarith
    _ = (8 / Real.log 2) * (Real.log x) ^ 2 * x ^ (θ / 2) := by
        field_simp
        ring

/-- Beyond a threshold the Rayleigh floor dominates both the state constant and the forced mass. -/
theorem eventually_floor_dominates_forced (J : ℕ) (hJ : 0 < J) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      2 * (J : ℝ) * (2 ^ J * ((J : ℝ) * Real.log x) + forcedMassBound θ x)
        ≤ primeWindowFloor J θ x := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hUpos : 0 < unitCoeffConstSum J := unitCoeffConstSum_pos hJ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := (J : ℝ) * (2 * ((J : ℝ) * (2 ^ (J - 1) /
      ((1 / (2 * (J : ℝ))) ^ (J - 1) * (((J - 1).factorial : ℕ) : ℝ)))) *
      unitCoeffConstSum J) ^ 2 with hDdef
  have hfacpos : (0:ℝ) < (((J - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (J - 1)
  have hD : 0 < D := by
    rw [hDdef]
    positivity
  set C : ℝ := (2 * (J : ℝ) * 2 ^ J * (J : ℝ) + 2 * (J : ℝ) * (8 / Real.log 2))
    * (D * (32768 * (J : ℝ))) with hCdef
  have hC : 0 < C := by
    rw [hCdef]
    positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_log_sq_le hC (by linarith : (0:ℝ) < θ / 2))
  refine ⟨max (max X₀ 4) 3, le_trans (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxpos : (0:ℝ) < x := by linarith
  have hlogx : (1:ℝ) ≤ Real.log x := by
    have h4 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx4
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    linarith
  have hone : (1:ℝ) ≤ x ^ (θ / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hkey : C * (Real.log x) ^ 2 ≤ x ^ (θ / 2) := hX₀ x hxX₀
  have h32 : (0:ℝ) < 32768 * (J : ℝ) := by positivity
  rw [primeWindowFloor, primeWindowFloorL, blockRayleighConst, ← hDdef, le_div_iff₀ hD, le_div_iff₀ h32]
  have hfb : forcedMassBound θ x ≤ (8 / Real.log 2) * (Real.log x) ^ 2 * x ^ (θ / 2) :=
    forcedMassBound_le hθ0 hθ1 hx4
  have hlogle : Real.log x ≤ (Real.log x) ^ 2 * x ^ (θ / 2) := by
    have h1 : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith [hlogx]
    have h2 : (Real.log x) ^ 2 ≤ (Real.log x) ^ 2 * x ^ (θ / 2) := by
      nlinarith [hone, sq_nonneg (Real.log x)]
    linarith
  have hbound : 2 * (J : ℝ) * (2 ^ J * ((J : ℝ) * Real.log x) + forcedMassBound θ x)
      ≤ (2 * (J : ℝ) * 2 ^ J * (J : ℝ) + 2 * (J : ℝ) * (8 / Real.log 2))
        * ((Real.log x) ^ 2 * x ^ (θ / 2)) := by
    have hA : 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x)
        ≤ 2 * (J : ℝ) * 2 ^ J * (J : ℝ) * ((Real.log x) ^ 2 * x ^ (θ / 2)) := by
      have hc : (0:ℝ) ≤ 2 * (J : ℝ) * 2 ^ J * (J : ℝ) := by positivity
      calc 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x)
          = (2 * (J : ℝ) * 2 ^ J * (J : ℝ)) * Real.log x := by ring
        _ ≤ (2 * (J : ℝ) * 2 ^ J * (J : ℝ)) * ((Real.log x) ^ 2 * x ^ (θ / 2)) :=
            mul_le_mul_of_nonneg_left hlogle hc
        _ = 2 * (J : ℝ) * 2 ^ J * (J : ℝ) * ((Real.log x) ^ 2 * x ^ (θ / 2)) := by ring
    have hB : 2 * (J : ℝ) * forcedMassBound θ x
        ≤ 2 * (J : ℝ) * ((8 / Real.log 2) * (Real.log x) ^ 2 * x ^ (θ / 2)) :=
      mul_le_mul_of_nonneg_left hfb (by positivity)
    have hexp : 2 * (J : ℝ) * (2 ^ J * ((J : ℝ) * Real.log x) + forcedMassBound θ x)
        = 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x) + 2 * (J : ℝ) * forcedMassBound θ x := by
      ring
    have hrhs : (2 * (J : ℝ) * 2 ^ J * (J : ℝ) + 2 * (J : ℝ) * (8 / Real.log 2))
        * ((Real.log x) ^ 2 * x ^ (θ / 2))
        = 2 * (J : ℝ) * 2 ^ J * (J : ℝ) * ((Real.log x) ^ 2 * x ^ (θ / 2))
          + 2 * (J : ℝ) * ((8 / Real.log 2) * (Real.log x) ^ 2 * x ^ (θ / 2)) := by ring
    rw [hexp, hrhs]
    exact add_le_add hA hB
  have hxθ : x ^ (θ / 2) * x ^ (θ / 2) = x ^ θ := by
    rw [← Real.rpow_add hxpos]
    ring_nf
  calc 2 * (J : ℝ) * (2 ^ J * ((J : ℝ) * Real.log x) + forcedMassBound θ x)
        * D * (32768 * (J : ℝ))
      ≤ ((2 * (J : ℝ) * 2 ^ J * (J : ℝ) + 2 * (J : ℝ) * (8 / Real.log 2))
          * ((Real.log x) ^ 2 * x ^ (θ / 2))) * (D * (32768 * (J : ℝ))) := by
        have hpos : (0:ℝ) ≤ D * (32768 * (J : ℝ)) := by positivity
        nlinarith [hbound, hpos]
    _ = (C * (Real.log x) ^ 2) * x ^ (θ / 2) := by
        rw [hCdef]
        ring
    _ ≤ x ^ (θ / 2) * x ^ (θ / 2) := by
        exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg (le_of_lt hxpos) _)
    _ = x ^ θ := hxθ

theorem forcedMassBoundL_le {x L : ℝ} (hx : 4 ≤ x) (hL : 1 ≤ L) (hxy : x + L ≤ x ^ 2) :
    forcedMassBoundL x L ≤ (8 / Real.log 2) * (Real.log x) ^ 2 * Real.sqrt L := by
  have hxpos : (0:ℝ) < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpos : (0:ℝ) < L := by linarith
  have hsq1 : (1:ℝ) ≤ Real.sqrt L := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL
  have hlogy : Real.log (x + L) ≤ 2 * Real.log x := by
    have hpos : (0:ℝ) < x + L := by linarith
    have h1 : Real.log (x + L) ≤ Real.log (x ^ 2) := Real.log_le_log hpos hxy
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogy0 : 0 ≤ Real.log (x + L) := Real.log_nonneg (by linarith)
  rw [forcedMassBoundL]
  calc (Real.log (x + L) / Real.log 2) * (Real.sqrt L + 1) * Real.log (x + L)
      ≤ ((2 * Real.log x) / Real.log 2) * (2 * Real.sqrt L) * (2 * Real.log x) := by
        gcongr
        linarith
    _ = (8 / Real.log 2) * (Real.log x) ^ 2 * Real.sqrt L := by
        field_simp
        ring

/-- Beyond a threshold every admissible window satisfies the size condition. -/
theorem eventually_size_condition (J : ℕ) (hJ : 0 < J) {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x L : ℝ, X ≤ x → x ^ θ ≤ L → x + L ≤ x ^ 2 →
      2 * (J : ℝ) * (2 ^ J * (2 ^ J * (J : ℝ) * Real.log x) + forcedMassBoundL x L)
        ≤ primeWindowFloorL J L := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := blockRayleighConst J with hDdef
  have hD : 0 < D := blockRayleighConst_pos hJ
  set c₁ : ℝ := 4 * (2 * (J : ℝ) * 4 ^ J * (J : ℝ)) * (D * (32768 * (J : ℝ))) with hc₁
  set c₂ : ℝ := 4 * (2 * (J : ℝ) * (8 / Real.log 2)) * (D * (32768 * (J : ℝ))) with hc₂
  have hc₁pos : 0 < c₁ := by
    rw [hc₁]
    positivity
  have hc₂pos : 0 < c₂ := by
    rw [hc₂]
    positivity
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1
    (eventually_log_sq_le hc₁pos (by linarith : (0:ℝ) < θ))
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.1
    (eventually_log_sq_le hc₂pos (by linarith : (0:ℝ) < θ / 2))
  refine ⟨max (max X₁ X₂) 4, le_trans (by norm_num) (le_max_right _ _), fun x L hx hL hxy => ?_⟩
  have hx4 : (4:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxpos : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxθ : (1:ℝ) ≤ x ^ θ := Real.one_le_rpow hx1 (le_of_lt hθ0)
  have hL1 : (1:ℝ) ≤ L := le_trans hxθ hL
  have hLpos : (0:ℝ) < L := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  -- the two halves
  have hhalf1 : c₁ * (Real.log x) ^ 2 ≤ x ^ θ := hX₁ x hxX₁
  have hhalf2 : c₂ * (Real.log x) ^ 2 ≤ x ^ (θ / 2) := hX₂ x hxX₂
  have hsqrtL : x ^ (θ / 2) ≤ Real.sqrt L := by
    have h1 : Real.sqrt (x ^ θ) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    have h2 : Real.sqrt (x ^ θ) = x ^ (θ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hxpos)]
      ring_nf
    rwa [h2] at h1
  have hfb := forcedMassBoundL_le hx4 hL1 hxy
  have h32 : (0:ℝ) < 32768 * (J : ℝ) := by positivity
  rw [primeWindowFloorL, ← hDdef, le_div_iff₀ hD, le_div_iff₀ h32]
  have hA : 2 * (J : ℝ) * (2 ^ J * (2 ^ J * (J : ℝ) * Real.log x)) * (D * (32768 * (J : ℝ)))
      ≤ L / 4 := by
    have hlogle : Real.log x ≤ (Real.log x) ^ 2 := by
      have h1 : (1:ℝ) ≤ Real.log x := by
        have hlog4 : (1:ℝ) ≤ Real.log 4 := by
          have h4 : (4:ℝ) = 2 ^ 2 := by norm_num
          rw [h4, Real.log_pow]
          have := Real.log_two_gt_d9
          push_cast
          linarith
        exact le_trans hlog4 (Real.log_le_log (by norm_num) hx4)
      nlinarith [h1]
    have hpow : (2:ℝ) ^ J * 2 ^ J = 4 ^ J := by
      rw [← mul_pow]
      norm_num
    calc 2 * (J : ℝ) * (2 ^ J * (2 ^ J * (J : ℝ) * Real.log x)) * (D * (32768 * (J : ℝ)))
        = (2 * (J : ℝ) * ((2:ℝ) ^ J * 2 ^ J) * (J : ℝ)) * (D * (32768 * (J : ℝ)))
            * Real.log x := by ring
      _ = (2 * (J : ℝ) * 4 ^ J * (J : ℝ)) * (D * (32768 * (J : ℝ))) * Real.log x := by
            rw [hpow]
      _ ≤ (2 * (J : ℝ) * 4 ^ J * (J : ℝ)) * (D * (32768 * (J : ℝ))) * (Real.log x) ^ 2 := by
            refine mul_le_mul_of_nonneg_left hlogle ?_
            positivity
      _ = c₁ * (Real.log x) ^ 2 / 4 := by
            rw [hc₁]
            ring
      _ ≤ x ^ θ / 4 := by linarith
      _ ≤ L / 4 := by linarith
  have hB : 2 * (J : ℝ) * forcedMassBoundL x L * (D * (32768 * (J : ℝ))) ≤ L / 4 := by
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hLpos)
    calc 2 * (J : ℝ) * forcedMassBoundL x L * (D * (32768 * (J : ℝ)))
        ≤ 2 * (J : ℝ) * ((8 / Real.log 2) * (Real.log x) ^ 2 * Real.sqrt L)
            * (D * (32768 * (J : ℝ))) := by
          have hpos : (0:ℝ) ≤ 2 * (J : ℝ) * (D * (32768 * (J : ℝ))) := by positivity
          nlinarith [hfb, hpos]
      _ = (c₂ * (Real.log x) ^ 2 / 4) * Real.sqrt L := by
          rw [hc₂]
          ring
      _ ≤ (x ^ (θ / 2) / 4) * Real.sqrt L := by
          have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
          nlinarith [hhalf2, hs]
      _ ≤ (Real.sqrt L / 4) * Real.sqrt L := by
          have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
          nlinarith [hsqrtL, hs]
      _ = L / 4 := by
          have hrw : Real.sqrt L / 4 * Real.sqrt L = (Real.sqrt L * Real.sqrt L) / 4 := by ring
          rw [hrw, hsq]
  linarith [hA, hB]

end RHTower.Sieve

end
