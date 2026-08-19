import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# One step of the Andersson window recursion

Combining the prime Rayleigh floor with the window step: on a window `(x, x + x^θ]` whose previous
levels obey the bound with constant `K`, unimodular phases at the window primes push every level at
the right endpoint below `Δ^j / j! · (J log y)`, provided `K` is small compared with the floor.
-/

noncomputable section

open Filter Set GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- **One recursion step.** -/
theorem exists_window_step (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ (a : ℕ → ℂ) (K : ℝ), 0 ≤ K →
      (∀ m : ℕ, m < J → ‖arithProfile a m x‖
        ≤ ((x ^ θ) ^ m / ((m.factorial : ℕ) : ℝ)) * K) →
      2 * (J : ℝ) * 2 ^ J * K ≤ primeWindowFloor J θ x →
      ∃ b : Fin (windowPrimes x (x + x ^ θ)).card → ℂ, (∀ r, ‖b r‖ = 1) ∧
        ∀ j : ℕ, j < J →
          ‖arithProfile (updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊)
              (windowAssign (windowPrimeIndex x (x + x ^ θ)) b (windowPrimeWeight x θ)))
              j (x + x ^ θ)‖
            ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + x ^ θ)) := by
  obtain ⟨X₀, hX₀, hray⟩ := exists_prime_window_rayleigh J hJ halpha hαθ hθ1
  refine ⟨max X₀ 2, le_trans one_le_two (le_max_right _ _), ?_⟩
  intro x hx a K hK0 hstate hsmall
  have hx0 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  set y : ℝ := x + x ^ θ with hydef
  have hΔ : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hxpos θ
  have hxy : x < y := by
    rw [hydef]
    linarith
  have hy1 : (1:ℝ) ≤ y := by linarith
  set p := windowPrimeIndex x y with hpdef
  set w := windowPrimeWeight x θ with hwdef
  -- the weights are bounded by `log y`
  have hC : ∀ r, |w r| ≤ Real.log y := by
    intro r
    have hmem := windowPrimeIndex_mem x y r
    have hprime := windowPrimeIndex_prime x y r
    have hple : (p r : ℝ) ≤ y := by
      have h1 : p r ≤ ⌊y⌋₊ := (Finset.mem_Ioc.1 (mem_windowPrimes.1 hmem).1).2
      have h2 : (p r : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
      exact le_trans h2 (Nat.floor_le (by linarith))
    have h2 : (2:ℝ) ≤ (p r : ℝ) := by exact_mod_cast hprime.two_le
    have hlog0 : 0 ≤ Real.log (p r) := Real.log_nonneg (by linarith)
    rw [hwdef, windowPrimeWeight, abs_of_nonneg hlog0]
    exact Real.log_le_log (by linarith) hple
  have hC0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  -- the Rayleigh floor
  have hlam : 0 < primeWindowFloor J θ x := by
    rw [primeWindowFloor]
    have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    have hnum : (0:ℝ) < x ^ θ / (32768 * J) := by positivity
    have hden : (0:ℝ) < (J : ℝ) * (2 * ((J : ℝ) * (2 ^ (J - 1) /
        ((1 / (2 * (J : ℝ))) ^ (J - 1) * (((J - 1).factorial : ℕ) : ℝ)))) *
        unitCoeffConstSum J) ^ 2 := by
      have hUpos : 0 < unitCoeffConstSum J := unitCoeffConstSum_pos hJ
      positivity
    exact div_pos hnum hden
  have hquad : ∀ u : Fin J → ℝ,
      primeWindowFloor J θ x * (∑ i, u i ^ 2)
        ≤ u ⬝ᵥ (atomicHankel w (windowNode p x y) J).mulVec u := by
    intro u
    exact hray x hxX₀ u
  -- the size condition for the moment problem
  have hsize : (J : ℝ) * (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ 2)
      ≤ primeWindowFloor J θ x ^ 2 := by
    have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
    have hterm : ∀ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ≤ 2 * 2 ^ J * K := by
      intro j
      have hj : (j : ℕ) < J := j.2
      have hstate' : ∀ m ≤ (j : ℕ), ‖arithProfile a m x‖
          ≤ ((y - x) ^ m / ((m.factorial : ℕ) : ℝ)) * K := by
        intro m hm
        have hmJ : m < J := lt_of_le_of_lt hm hj
        have hyx : y - x = x ^ θ := by
          rw [hydef]
          ring
        rw [hyx]
        exact hstate m hmJ
      have hbound := norm_windowTarget_le hxy hstate'
      have hpow : (2:ℝ) ^ (j : ℕ) ≤ 2 ^ J := by
        exact pow_le_pow_right₀ one_le_two (le_of_lt hj)
      rw [norm_mul]
      simp only [Complex.norm_ofNat]
      have : ‖windowTarget a x y (j : ℕ)‖ ≤ 2 ^ J * K := by
        refine le_trans hbound ?_
        exact mul_le_mul_of_nonneg_right hpow hK0
      linarith
    have hsum : (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * (2 * 2 ^ J * K) ^ 2 := by
      calc (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ 2)
          ≤ ∑ _j : Fin J, (2 * 2 ^ J * K) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hterm j) 2
        _ = (J : ℝ) * (2 * 2 ^ J * K) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfinal : (J : ℝ) * ((J : ℝ) * (2 * 2 ^ J * K) ^ 2) ≤ primeWindowFloor J θ x ^ 2 := by
      have hkey : ((J : ℝ) * (2 * 2 ^ J * K)) ^ 2 ≤ primeWindowFloor J θ x ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        calc (J : ℝ) * (2 * 2 ^ J * K) = 2 * (J : ℝ) * 2 ^ J * K := by ring
          _ ≤ primeWindowFloor J θ x := hsmall
      calc (J : ℝ) * ((J : ℝ) * (2 * 2 ^ J * K) ^ 2)
          = ((J : ℝ) * (2 * 2 ^ J * K)) ^ 2 := by ring
        _ ≤ primeWindowFloor J θ x ^ 2 := hkey
    calc (J : ℝ) * (∑ j : Fin J, ‖2 * windowTarget a x y (j : ℕ)‖ ^ 2)
        ≤ (J : ℝ) * ((J : ℝ) * (2 * 2 ^ J * K) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hJR)
      _ ≤ primeWindowFloor J θ x ^ 2 := hfinal
  obtain ⟨b, hb1, hb2⟩ := exists_window_phases hJ a hx1 hxy (windowPrimeIndex_injective x y)
    (fun r => (mem_windowPrimes.1 (windowPrimeIndex_mem x y r)).1) w hC hC0 hlam hquad hsize
  refine ⟨b, hb1, fun j hj => ?_⟩
  have := hb2 ⟨j, hj⟩
  have hyx : y - x = x ^ θ := by
    rw [hydef]
    ring
  rw [hyx] at this
  exact this

/-! ## The window sequence -/

/-- The window endpoints `x_{k+1} = x_k + x_k^θ`. -/
def windowSeq (θ x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | (k + 1) => windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ

theorem windowSeq_zero (θ x₀ : ℝ) : windowSeq θ x₀ 0 = x₀ := rfl

theorem windowSeq_succ (θ x₀ : ℝ) (k : ℕ) :
    windowSeq θ x₀ (k + 1) = windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ := rfl

theorem windowSeq_ge {θ x₀ : ℝ} (hx₀ : 0 < x₀) (k : ℕ) : x₀ ≤ windowSeq θ x₀ k := by
  induction k with
  | zero => exact le_of_eq (windowSeq_zero θ x₀).symm
  | succ k ih =>
      rw [windowSeq_succ]
      have hz : (0:ℝ) < windowSeq θ x₀ k := lt_of_lt_of_le hx₀ ih
      have hpos : (0:ℝ) < (windowSeq θ x₀ k) ^ θ := Real.rpow_pos_of_pos hz θ
      linarith

theorem windowSeq_pos {θ x₀ : ℝ} (hx₀ : 0 < x₀) (k : ℕ) : 0 < windowSeq θ x₀ k :=
  lt_of_lt_of_le hx₀ (windowSeq_ge hx₀ k)

theorem windowSeq_le_succ {θ x₀ : ℝ} (hx₀ : 0 < x₀) (k : ℕ) :
    windowSeq θ x₀ k ≤ windowSeq θ x₀ (k + 1) := by
  rw [windowSeq_succ]
  have hpos : (0:ℝ) < (windowSeq θ x₀ k) ^ θ :=
    Real.rpow_pos_of_pos (windowSeq_pos hx₀ k) θ
  linarith

theorem windowSeq_mono {θ x₀ : ℝ} (hx₀ : 0 < x₀) : Monotone (windowSeq θ x₀) := by
  refine monotone_nat_of_le_succ ?_
  exact windowSeq_le_succ hx₀

theorem windowSeq_lower_linear {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) (k : ℕ) :
    x₀ + (k : ℝ) ≤ windowSeq θ x₀ k := by
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  induction k with
  | zero => simp [windowSeq_zero]
  | succ k ih =>
      rw [windowSeq_succ]
      have hone : (1:ℝ) ≤ (windowSeq θ x₀ k) ^ θ := by
        refine Real.one_le_rpow ?_ hθ
        exact le_trans hx₀ (windowSeq_ge hx₀0 k)
      push_cast
      linarith

theorem windowSeq_ge_index {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) (k : ℕ) :
    (k : ℝ) ≤ windowSeq θ x₀ k := by
  have := windowSeq_lower_linear hx₀ hθ k
  linarith

theorem windowSeq_tendsto {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) :
    Filter.Tendsto (windowSeq θ x₀) Filter.atTop Filter.atTop := by
  have hlin : Filter.Tendsto (fun k : ℕ => x₀ + (k : ℝ)) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_left _ x₀ tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono (fun k => windowSeq_lower_linear hx₀ hθ k) hlin

/-! ## The recursive construction of the source -/

/-- The source after one window assignment. -/
def windowUpdate (θ : ℝ) (a : ℕ → ℂ) (x : ℝ)
    (b : Fin (windowPrimes x (x + x ^ θ)).card → ℂ) : ℕ → ℂ :=
  updateWindow a (Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊)
    (windowAssign (windowPrimeIndex x (x + x ^ θ)) b (windowPrimeWeight x θ))

/-- A phase assignment is good when it is unimodular and keeps every level small at the right
endpoint of the window. -/
def WindowGood (J : ℕ) (θ : ℝ) (a : ℕ → ℂ) (x : ℝ)
    (b : Fin (windowPrimes x (x + x ^ θ)).card → ℂ) : Prop :=
  (∀ r, ‖b r‖ = 1) ∧
    ∀ j : ℕ, j < J → ‖arithProfile (windowUpdate θ a x b) j (x + x ^ θ)‖
      ≤ ((x ^ θ) ^ j / ((j.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log (x + x ^ θ))

open scoped Classical in
/-- The source after `k` windows. -/
noncomputable def stepSource (J : ℕ) (θ x₀ : ℝ) : ℕ → (ℕ → ℂ)
  | 0 => fun _ => 0
  | (k + 1) =>
      if h : ∃ b, WindowGood J θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) b then
        windowUpdate θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) h.choose
      else stepSource J θ x₀ k

theorem stepSource_zero (J : ℕ) (θ x₀ : ℝ) : stepSource J θ x₀ 0 = fun _ => 0 := rfl

open scoped Classical in
theorem stepSource_succ (J : ℕ) (θ x₀ : ℝ) (k : ℕ) :
    stepSource J θ x₀ (k + 1) =
      if h : ∃ b, WindowGood J θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) b then
        windowUpdate θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) h.choose
      else stepSource J θ x₀ k := rfl

/-- Values at integers already passed are never revised. -/
theorem stepSource_succ_apply_of_le (J : ℕ) (θ x₀ : ℝ) (k : ℕ) {n : ℕ}
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    stepSource J θ x₀ (k + 1) n = stepSource J θ x₀ k n := by
  classical
  rw [stepSource_succ]
  by_cases h : ∃ b, WindowGood J θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) b
  · rw [dif_pos h, windowUpdate, updateWindow]
    have hnot : n ∉ Finset.Ioc ⌊windowSeq θ x₀ k⌋₊
        ⌊windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ⌋₊ := by
      intro hmem
      have h1 : ⌊windowSeq θ x₀ k⌋₊ < n := (Finset.mem_Ioc.1 hmem).1
      have h2 : n ≤ ⌊windowSeq θ x₀ k⌋₊ := Nat.le_floor hn
      omega
    rw [if_neg hnot]
  · rw [dif_neg h]

/-- The construction stabilizes: later stages agree at integers already passed. -/
theorem stepSource_stable (J : ℕ) {θ x₀ : ℝ} (hx₀ : 0 < x₀) {n k : ℕ} (m : ℕ) (hkm : k ≤ m)
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    stepSource J θ x₀ m n = stepSource J θ x₀ k n := by
  induction m with
  | zero =>
      have : k = 0 := Nat.le_zero.1 hkm
      rw [this]
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hlt
        have hle : (n : ℝ) ≤ windowSeq θ x₀ m :=
          le_trans hn (windowSeq_mono hx₀ hkm')
        rw [stepSource_succ_apply_of_le J θ x₀ m hle, ih hkm']
      · have : k = m + 1 := le_antisymm hkm hge
        rw [this]

/-- The limiting source. -/
noncomputable def anderssonSource (J : ℕ) (θ x₀ : ℝ) : ℕ → ℂ :=
  fun n => stepSource J θ x₀ n n

theorem anderssonSource_eq (J : ℕ) {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) {n k : ℕ}
    (hn : (n : ℝ) ≤ windowSeq θ x₀ k) :
    anderssonSource J θ x₀ n = stepSource J θ x₀ k n := by
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  rw [anderssonSource]
  rcases Nat.le_total k n with hkn | hnk
  · exact stepSource_stable J hx₀0 n hkn hn
  · have hself : (n : ℝ) ≤ windowSeq θ x₀ n := windowSeq_ge_index hx₀ hθ n
    exact (stepSource_stable J hx₀0 k hnk hself).symm

/-- At a window endpoint the limiting source has the same levels as the finite stage. -/
theorem arithProfile_anderssonSource (J : ℕ) {θ x₀ : ℝ} (hx₀ : 1 ≤ x₀) (hθ : 0 ≤ θ) (j k : ℕ) :
    arithProfile (anderssonSource J θ x₀) j (windowSeq θ x₀ k)
      = arithProfile (stepSource J θ x₀ k) j (windowSeq θ x₀ k) := by
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀
  have hpos : 0 < windowSeq θ x₀ k := windowSeq_pos hx₀0 k
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ windowSeq θ x₀ k := by
    have h1 : n ≤ ⌊windowSeq θ x₀ k⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊windowSeq θ x₀ k⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (Nat.floor_le (le_of_lt hpos))
  rw [anderssonSource_eq J hx₀ hθ hle]

/-! ## The recursion closes -/

open Asymptotics in
/-- Beyond a threshold the Rayleigh floor dominates the state constant. -/
theorem eventually_floor_dominates (J : ℕ) (hJ : 0 < J) {θ : ℝ} (hθ : 0 < θ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x) ≤ primeWindowFloor J θ x := by
  have hJR : (0:ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hUpos : 0 < unitCoeffConstSum J := unitCoeffConstSum_pos hJ
  set D : ℝ := (J : ℝ) * (2 * ((J : ℝ) * (2 ^ (J - 1) /
      ((1 / (2 * (J : ℝ))) ^ (J - 1) * (((J - 1).factorial : ℕ) : ℝ)))) *
      unitCoeffConstSum J) ^ 2 with hDdef
  have hfacpos : (0:ℝ) < (((J - 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (J - 1)
  have hD : 0 < D := by
    rw [hDdef]
    positivity
  set c : ℝ := 2 * (J : ℝ) * 2 ^ J * (J : ℝ) * (D * (32768 * (J : ℝ))) with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    positivity
  have hev : ∀ᶠ x : ℝ in Filter.atTop, c * Real.log x ≤ x ^ θ := by
    have h := (isLittleO_log_rpow_atTop hθ).def (c := 1 / c) (by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hrpow : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hxpos θ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_pos hrpow] at hx
    rw [div_mul_eq_mul_div, le_div_iff₀ hc] at hx
    linarith
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max X₀ 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have hkey : c * Real.log x ≤ x ^ θ := hX₀ x hx0
  have h32 : (0:ℝ) < 32768 * (J : ℝ) := by positivity
  rw [primeWindowFloor, primeWindowFloorL, blockRayleighConst, ← hDdef, le_div_iff₀ hD, le_div_iff₀ h32]
  calc 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x) * D * (32768 * (J : ℝ))
      = c * Real.log x := by
        rw [hcdef]
        ring
    _ ≤ x ^ θ := hkey

/-- **Lemma 7.**  The recursively constructed source keeps every level of the remainder chain
below `Δ^j / j! · (J log x)` at every window endpoint. -/
theorem stepSource_state_bound (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ → ∀ k : ℕ, ∀ j : ℕ, j < J →
      ‖arithProfile (stepSource J θ x₀ (k + 1)) j (windowSeq θ x₀ (k + 1))‖
        ≤ (((windowSeq θ x₀ k) ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
            * ((J : ℝ) * Real.log (windowSeq θ x₀ (k + 1))) := by
  classical
  have hθ0 : 0 < θ := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) (lt_trans halpha hαθ)
  obtain ⟨X₁, hX₁, hstep⟩ := exists_window_step J hJ halpha hαθ hθ1
  obtain ⟨X₂, hX₂, hdom⟩ := eventually_floor_dominates J hJ hθ0
  refine ⟨max X₁ X₂, le_trans hX₁ (le_max_left _ _), fun x₀ hx₀ k => ?_⟩
  have hx₀1 : (1:ℝ) ≤ x₀ := le_trans hX₁ (le_trans (le_max_left _ _) hx₀)
  have hx₀0 : (0:ℝ) < x₀ := lt_of_lt_of_le zero_lt_one hx₀1
  -- the induction produces the state bound at every stage
  have key : ∀ k : ℕ, ∀ j : ℕ, j < J →
      ‖arithProfile (stepSource J θ x₀ (k + 1)) j (windowSeq θ x₀ (k + 1))‖
        ≤ (((windowSeq θ x₀ k) ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
            * ((J : ℝ) * Real.log (windowSeq θ x₀ (k + 1))) := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hxk : windowSeq θ x₀ 0 = x₀ := rfl
        have hX1le : X₁ ≤ x₀ := le_trans (le_max_left _ _) hx₀
        have hzero : ∀ m : ℕ, m < J → ‖arithProfile (stepSource J θ x₀ 0) m x₀‖
            ≤ ((x₀ ^ θ) ^ m / ((m.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log x₀) := by
          intro m _
          have h0 : arithProfile (stepSource J θ x₀ 0) m x₀ = 0 := by
            rw [stepSource_zero, arithProfile]
            simp
          rw [h0, norm_zero]
          have hlog : 0 ≤ Real.log x₀ := Real.log_nonneg hx₀1
          have hxθ : (0:ℝ) < x₀ ^ θ := Real.rpow_pos_of_pos hx₀0 θ
          have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
          have hJR : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
          positivity
        have hsmall : 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log x₀)
            ≤ primeWindowFloor J θ x₀ := hdom x₀ (le_trans (le_max_right _ _) hx₀)
        have hK0 : 0 ≤ (J : ℝ) * Real.log x₀ := by
          have hlog : 0 ≤ Real.log x₀ := Real.log_nonneg hx₀1
          positivity
        have hex : ∃ b, WindowGood J θ (stepSource J θ x₀ 0) (windowSeq θ x₀ 0) b := by
          obtain ⟨b, hb1, hb2⟩ := hstep x₀ hX1le (stepSource J θ x₀ 0) ((J : ℝ) * Real.log x₀)
            hK0 hzero hsmall
          exact ⟨b, hb1, hb2⟩
        rw [stepSource_succ, dif_pos hex]
        exact (hex.choose_spec).2 j hj
    | succ k ih =>
        intro j hj
        set xk : ℝ := windowSeq θ x₀ (k + 1) with hxkdef
        have hxk1 : (1:ℝ) ≤ xk := le_trans hx₀1 (windowSeq_ge hx₀0 (k + 1))
        have hxk0 : (0:ℝ) < xk := lt_of_lt_of_le zero_lt_one hxk1
        have hX1le : X₁ ≤ xk := le_trans (le_trans (le_max_left _ _) hx₀)
          (windowSeq_ge hx₀0 (k + 1))
        have hX2le : X₂ ≤ xk := le_trans (le_trans (le_max_right _ _) hx₀)
          (windowSeq_ge hx₀0 (k + 1))
        have hmono : windowSeq θ x₀ k ^ θ ≤ xk ^ θ := by
          refine Real.rpow_le_rpow (le_of_lt (windowSeq_pos hx₀0 k)) ?_ (le_of_lt hθ0)
          exact windowSeq_le_succ hx₀0 k
        have hstate : ∀ m : ℕ, m < J → ‖arithProfile (stepSource J θ x₀ (k + 1)) m xk‖
            ≤ ((xk ^ θ) ^ m / ((m.factorial : ℕ) : ℝ)) * ((J : ℝ) * Real.log xk) := by
          intro m hm
          refine le_trans (ih m hm) ?_
          have hfac : (0:ℝ) < ((m.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos m
          have hpow : (windowSeq θ x₀ k ^ θ) ^ m ≤ (xk ^ θ) ^ m := by
            refine pow_le_pow_left₀ ?_ hmono m
            exact le_of_lt (Real.rpow_pos_of_pos (windowSeq_pos hx₀0 k) θ)
          have hlogk : 0 ≤ Real.log xk := Real.log_nonneg hxk1
          have hJR : (0:ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact div_le_div_of_nonneg_right hpow hfac.le
        have hK0 : 0 ≤ (J : ℝ) * Real.log xk := by
          have hlog : 0 ≤ Real.log xk := Real.log_nonneg hxk1
          positivity
        have hsmall : 2 * (J : ℝ) * 2 ^ J * ((J : ℝ) * Real.log xk)
            ≤ primeWindowFloor J θ xk := hdom xk hX2le
        have hex : ∃ b, WindowGood J θ (stepSource J θ x₀ (k + 1)) (windowSeq θ x₀ (k + 1)) b := by
          obtain ⟨b, hb1, hb2⟩ := hstep xk hX1le (stepSource J θ x₀ (k + 1))
            ((J : ℝ) * Real.log xk) hK0 hstate hsmall
          exact ⟨b, hb1, hb2⟩
        rw [stepSource_succ, dif_pos hex]
        exact (hex.choose_spec).2 j hj
  exact key k

/-- **Lemma 7 for the limiting source.**  The single source constructed by the recursion keeps every
level of the remainder chain below `Δ^j / j! · (J log x)` at every window endpoint. -/
theorem anderssonSource_state_bound (J : ℕ) (hJ : 0 < J) {α θ : ℝ}
    (halpha : (701299/1000000:ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x₀ : ℝ, X ≤ x₀ → ∀ k : ℕ, ∀ j : ℕ, j < J →
      ‖arithProfile (anderssonSource J θ x₀) j (windowSeq θ x₀ (k + 1))‖
        ≤ (((windowSeq θ x₀ k) ^ θ) ^ j / ((j.factorial : ℕ) : ℝ))
            * ((J : ℝ) * Real.log (windowSeq θ x₀ (k + 1))) := by
  have hθ0 : 0 < θ := lt_trans (by norm_num : (0:ℝ) < 701299/1000000) (lt_trans halpha hαθ)
  obtain ⟨X, hX, hbound⟩ := stepSource_state_bound J hJ halpha hαθ hθ1
  refine ⟨max X 1, le_max_right _ _, fun x₀ hx₀ k j hj => ?_⟩
  have hXle : X ≤ x₀ := le_trans (le_max_left _ _) hx₀
  have hx₀1 : (1:ℝ) ≤ x₀ := le_trans (le_max_right _ _) hx₀
  rw [arithProfile_anderssonSource J hx₀1 (le_of_lt hθ0) j (k + 1)]
  exact hbound x₀ hXle k j hj

/-! ## The source is supported on primes with logarithmic size -/

theorem norm_windowAssign_le {N : ℕ} {p : Fin N → ℕ} {b : Fin N → ℂ} {w : Fin N → ℝ}
    (hb : ∀ r, ‖b r‖ = 1) (hw : ∀ r, w r = Real.log (p r)) (hp : ∀ r, Nat.Prime (p r)) (n : ℕ) :
    ‖windowAssign p b w n‖ ≤ if Nat.Prime n then Real.log n else 0 := by
  classical
  by_cases h : ∃ r, p r = n
  · rw [windowAssign, dif_pos h, norm_mul, hb, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hn : p h.choose = n := h.choose_spec
    have hprime : Nat.Prime n := hn ▸ hp h.choose
    rw [if_pos hprime, hw h.choose, hn]
    exact le_of_eq (abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)))
  · rw [windowAssign, dif_neg h, norm_zero]
    by_cases hprime : Nat.Prime n
    · rw [if_pos hprime]
      exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    · rw [if_neg hprime]

theorem norm_stepSource_le (J : ℕ) (θ x₀ : ℝ) (k n : ℕ) :
    ‖stepSource J θ x₀ k n‖ ≤ if Nat.Prime n then Real.log n else 0 := by
  classical
  induction k with
  | zero =>
      rw [stepSource_zero, norm_zero]
      by_cases hprime : Nat.Prime n
      · rw [if_pos hprime]
        exact Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      · rw [if_neg hprime]
  | succ k ih =>
      rw [stepSource_succ]
      by_cases h : ∃ b, WindowGood J θ (stepSource J θ x₀ k) (windowSeq θ x₀ k) b
      · rw [dif_pos h, windowUpdate, updateWindow]
        by_cases hmem : n ∈ Finset.Ioc ⌊windowSeq θ x₀ k⌋₊
            ⌊windowSeq θ x₀ k + (windowSeq θ x₀ k) ^ θ⌋₊
        · rw [if_pos hmem]
          refine norm_windowAssign_le (h.choose_spec).1 (fun r => rfl) ?_ n
          intro r
          exact windowPrimeIndex_prime _ _ r
        · rw [if_neg hmem]
          exact ih
      · rw [dif_neg h]
        exact ih

theorem norm_anderssonSource_le (J : ℕ) (θ x₀ : ℝ) (n : ℕ) :
    ‖anderssonSource J θ x₀ n‖ ≤ if Nat.Prime n then Real.log n else 0 :=
  norm_stepSource_le J θ x₀ n n

theorem sum_ite_prime_eq_primesBelow (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (if Nat.Prime m then Real.log m else 0))
      = ∑ p ∈ Nat.primesBelow (N + 1), Real.log p := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_, hp2⟩, hprime⟩
    exact ⟨by omega, hprime⟩
  · rintro ⟨hlt, hprime⟩
    exact ⟨⟨hprime.one_lt.le, by omega⟩, hprime⟩

/-- The partial sums of the constructed source obey the Chebyshev bound. -/
theorem norm_sum_anderssonSource_le (J : ℕ) (θ x₀ : ℝ) (N : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 N, anderssonSource J θ x₀ m‖ ≤ (N : ℝ) * Real.log 4 := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∑ m ∈ Finset.Icc 1 N, ‖anderssonSource J θ x₀ m‖
      ≤ ∑ m ∈ Finset.Icc 1 N, (if Nat.Prime m then Real.log m else 0) :=
    Finset.sum_le_sum fun m _ => norm_anderssonSource_le J θ x₀ m
  refine le_trans h1 ?_
  rw [sum_ite_prime_eq_primesBelow N]
  exact RHTower.sum_primesBelow_log_le N

/-- The jump mass of a window is at most its integer count times the largest logarithm. -/
theorem sum_norm_anderssonSource_window_le (J : ℕ) (θ x₀ : ℝ) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖anderssonSource J θ x₀ n‖
      ≤ ((⌊y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)) * Real.log y := by
  classical
  have hy0 : (0:ℝ) ≤ y := le_trans hx hxy
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖anderssonSource J θ x₀ n‖ ≤ Real.log y := by
    intro n hn
    have hmem := Finset.mem_Ioc.1 hn
    have hny : (n : ℝ) ≤ y := by
      have h1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
      exact le_trans h1 (Nat.floor_le hy0)
    refine le_trans (norm_anderssonSource_le J θ x₀ n) ?_
    by_cases hprime : Nat.Prime n
    · rw [if_pos hprime]
      exact Real.log_le_log (by exact_mod_cast hprime.pos) hny
    · rw [if_neg hprime]
      refine Real.log_nonneg ?_
      have h1 : ⌊x⌋₊ < n := hmem.1
      have h2 : (1:ℝ) ≤ (n : ℝ) := by
        have : 1 ≤ n := by omega
        exact_mod_cast this
      linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hcard : ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    rw [Nat.cast_sub hfl]
  rw [hcard]

end RHTower.Sieve

end
