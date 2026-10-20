import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapScheduleTwoChainRayBound

/-!
# One-gap Fermi schedules: global bound, edge gap and free middle gap

Summing the two-chain ray inequality over odd bases bounds the sieve energy by the one-gap trace
with the constant `1/(ρ_m min(λ_{h+m+2}, λ_{L-h+3}))`, `L = ⌊log₂ N⌋`, for the gap at level
`h + 1`. With `1/λ_n ≤ ((2n+1)² + 2)/π²` this is at most

`(1 + 2^-(m+1)) (max(2h + 2m + 5, 2(L - h) + 7)² + 2)/π²`.

The one-gap inverse constant `K_g` dominates the full-trace constant `K^all`, and at `g = 1` it is
the selected-trace constant `K_N` (sharp value `(4/π²) L²`). At half depth, `g = ⌊L/2⌋ + 1`,
the upper bound is `(L + O(1))²/π²`, which meets the full-trace lower bound:
`K_{⌊L/2⌋+1}(N)/(log₂ N)² → 1/π²`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The constant of the two-chain ray inequality for the gap at level `h + 1`, cutoff `m`. -/
def fermiGapRayConstant (N h m : ℕ) : ℝ :=
  1 / (fermiRayWeightFloor m * min (mixedChainConstant (h + m + 2))
    (mixedChainConstant (Nat.log 2 N - h + 3)))

theorem fermiGapRayConstant_nonneg (N h m : ℕ) : 0 ≤ fermiGapRayConstant N h m := by
  unfold fermiGapRayConstant
  have := fermiRayWeightFloor_pos m
  have := lt_min (mixedChainConstant_pos (h + m + 2)) (mixedChainConstant_pos (Nat.log 2 N - h + 3))
  positivity

/-- **One-gap observability bound.** For the gap at level `h + 1` and `m ≤ h ≤ log₂ N`, the
physical sieve energy is at most the ray constant times the one-gap trace energy. -/
theorem sieveTotalPronicEnergy_le_gap (N : ℕ) (c : ℕ → ℝ) {h m : ℕ} (hmh : m ≤ h)
    (hhL : h ≤ Nat.log 2 N) :
    sieveTotalPronicEnergy N c ≤ fermiGapRayConstant N h m * fermiGapPronicEnergy N c (h + 1) := by
  obtain ⟨hP, hPs⟩ := sieveTotalPronicEnergy_eq_sum_rays N c
  obtain ⟨hQ, hQs⟩ := fermiGapPronicEnergy_eq_sum_rays N c h
  rw [hP, hQ, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun j => fermiRaySieveEnergy_le_gap N c (by omega : 0 < 2 * j + 1) hmh hhL) hPs
    (hQs.mul_left _)

/-! ### The one-gap inverse constant -/

/-- Physical sieve/one-gap ratios over coefficient vectors in `D` with positive trace. -/
def fermiGapRatios (N g : ℕ) (D : Set (ℕ → ℝ)) : Set ℝ :=
  {t | ∃ c ∈ D, 0 < fermiGapPronicEnergy N c g ∧
    t = sieveTotalPronicEnergy N c / fermiGapPronicEnergy N c g}

/-- Optimal physical inverse constant `K_g(N)` of the trace missing the dyadic level `g`. -/
def fermiGapInverseConstant (N g : ℕ) : ℝ := sSup (fermiGapRatios N g Set.univ)

theorem fermiGapRatio_le (N : ℕ) (D : Set (ℕ → ℝ)) {h m : ℕ} (hmh : m ≤ h)
    (hhL : h ≤ Nat.log 2 N) {t : ℝ} (ht : t ∈ fermiGapRatios N (h + 1) D) :
    t ≤ fermiGapRayConstant N h m := by
  obtain ⟨c, -, hQ, rfl⟩ := ht
  rw [div_le_iff₀ hQ]
  exact sieveTotalPronicEnergy_le_gap N c hmh hhL

theorem fermiGapInverseConstant_le (N : ℕ) {h m : ℕ} (hmh : m ≤ h) (hhL : h ≤ Nat.log 2 N) :
    fermiGapInverseConstant N (h + 1) ≤ fermiGapRayConstant N h m :=
  Real.sSup_le (fun _ ht => fermiGapRatio_le N _ hmh hhL ht) (fermiGapRayConstant_nonneg N h m)

theorem fermiGapInverseConstant_nonneg (N g : ℕ) : 0 ≤ fermiGapInverseConstant N g := by
  apply Real.sSup_nonneg
  rintro t ⟨c, -, hQ, rfl⟩
  exact div_nonneg (tsum_nonneg fun _ => by
    unfold sievePairedPronicEnergy; positivity) hQ.le

/-- **Removing a level can only worsen conditioning.** `K^all_N ≤ K_{h+1}(N)`. -/
theorem fermiAllBoundaryInverseConstant_le_gap (N : ℕ) {h : ℕ} (hhL : h ≤ Nat.log 2 N) :
    fermiAllBoundaryInverseConstant N ≤ fermiGapInverseConstant N (h + 1) := by
  have hbdd : BddAbove (fermiGapRatios N (h + 1) Set.univ) :=
    ⟨fermiGapRayConstant N h 0, fun _ ht => fermiGapRatio_le N _ (Nat.zero_le h) hhL ht⟩
  apply Real.sSup_le _ (fermiGapInverseConstant_nonneg N (h + 1))
  rintro t ⟨c, -, hQ, rfl⟩
  have hP0 : 0 ≤ sieveTotalPronicEnergy N c :=
    tsum_nonneg fun _ => by unfold sievePairedPronicEnergy; positivity
  have hle := fermiGapPronicEnergy_le_allBoundary N c h
  have hge := fermiGapPronicEnergy_nonneg N c h
  rcases hge.lt_or_eq with hpos | hzero
  · calc sieveTotalPronicEnergy N c / fermiAllBoundaryPronicEnergy N c ≤
        sieveTotalPronicEnergy N c / fermiGapPronicEnergy N c (h + 1) :=
          div_le_div_of_nonneg_left hP0 hpos hle
      _ ≤ fermiGapInverseConstant N (h + 1) :=
          le_csSup hbdd ⟨c, Set.mem_univ _, hpos, rfl⟩
  · have hb := sieveTotalPronicEnergy_le_gap N c (Nat.zero_le h) hhL
    rw [← hzero, mul_zero] at hb
    have : sieveTotalPronicEnergy N c = 0 := le_antisymm hb hP0
    rw [this, zero_div]
    exact fermiGapInverseConstant_nonneg N (h + 1)

/-- **The edge gap is the selected trace.** `K_1(N) = K_N`. -/
theorem fermiGapInverseConstant_one (N : ℕ) :
    fermiGapInverseConstant N 1 = fermiPhysicalInverseConstant N := by
  have hset : fermiGapRatios N 1 Set.univ =
      {t | ∃ c ∈ (Set.univ : Set (ℕ → ℝ)), 0 < fermiSelectedTotalPronicEnergy N c ∧
        t = sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c} := by
    ext t
    simp only [fermiGapRatios, Set.mem_setOf_eq, fermiGapPronicEnergy_one]
  unfold fermiGapInverseConstant
  rw [hset]
  rfl

/-! ### Explicit bound -/

/-- **Explicit one-gap bound.** For the gap at level `h + 1`, `m ≤ h ≤ log₂ N`, with
`M = max(2h + 2m + 5, 2(L - h) + 7)`, `K_{h+1}(N) ≤ (1 + 2^-(m+1)) (M² + 2)/π²`. -/
theorem fermiGapInverseConstant_le_explicit (N : ℕ) {h m : ℕ} (hmh : m ≤ h)
    (hhL : h ≤ Nat.log 2 N) :
    fermiGapInverseConstant N (h + 1) ≤
      (1 + 1 / (2 : ℝ) ^ (m + 1)) *
        ((max (2 * ((h + m + 2 : ℕ) : ℝ) + 1) (2 * ((Nat.log 2 N - h + 3 : ℕ) : ℝ) + 1)) ^ 2 + 2) /
          Real.pi ^ 2 := by
  refine (fermiGapInverseConstant_le N hmh hhL).trans ?_
  set a := mixedChainConstant (h + m + 2)
  set b := mixedChainConstant (Nat.log 2 N - h + 3)
  have ha := mixedChainConstant_pos (h + m + 2)
  have hb := mixedChainConstant_pos (Nat.log 2 N - h + 3)
  set M := max (2 * ((h + m + 2 : ℕ) : ℝ) + 1) (2 * ((Nat.log 2 N - h + 3 : ℕ) : ℝ) + 1)
  have hia : 1 / a ≤ (M ^ 2 + 2) / Real.pi ^ 2 := by
    refine (one_div_mixedChainConstant_le (by omega)).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : 0 ≤ 2 * ((h + m + 2 : ℕ) : ℝ) + 1 := by positivity
    nlinarith [le_max_left (2 * ((h + m + 2 : ℕ) : ℝ) + 1)
      (2 * ((Nat.log 2 N - h + 3 : ℕ) : ℝ) + 1)]
  have hib : 1 / b ≤ (M ^ 2 + 2) / Real.pi ^ 2 := by
    refine (one_div_mixedChainConstant_le (by omega)).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : 0 ≤ 2 * ((Nat.log 2 N - h + 3 : ℕ) : ℝ) + 1 := by positivity
    nlinarith [le_max_right (2 * ((h + m + 2 : ℕ) : ℝ) + 1)
      (2 * ((Nat.log 2 N - h + 3 : ℕ) : ℝ) + 1)]
  have hmin : 1 / min a b ≤ (M ^ 2 + 2) / Real.pi ^ 2 := by
    rcases min_choice a b with h' | h' <;> rw [h'] <;> assumption
  have hρ : 1 / fermiRayWeightFloor m = 1 + 1 / (2 : ℝ) ^ (m + 1) := by
    unfold fermiRayWeightFloor; field_simp
  unfold fermiGapRayConstant
  have e : 1 / (fermiRayWeightFloor m * min a b) =
      1 / fermiRayWeightFloor m * (1 / min a b) := by rw [one_div_mul_one_div]
  rw [e, hρ, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hmin (by positivity)

/-! ### The free middle gap -/

private theorem logb_two_bounds {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.logb 2 N ∧ Real.logb 2 N < (Nat.log 2 N : ℝ) + 1 := by
  have h1 : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) N
  constructor
  · have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  · have := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    push_cast at this
    exact this

private theorem tendsto_nat_log_two :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun N hN => Nat.le_log_of_pow_le (by norm_num) hN⟩)

private theorem tendsto_shift_sq_profile (c : ℝ) :
    Tendsto (fun x : ℝ => ((x + c) ^ 2 + 2) / x ^ 2) atTop (𝓝 1) := by
  have hratio : Tendsto (fun x : ℝ => 1 + c / x) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
    simpa using this
  have h2 : Tendsto (fun x : ℝ => 2 / x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hlim := (hratio.pow 2).add h2
  simp only [one_pow, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

private theorem tendsto_lower_ratio :
    Tendsto (fun x : ℝ => (1 - 4 / (x + 2)) / Real.pi ^ 2) atTop (𝓝 (1 / Real.pi ^ 2)) := by
  have h : Tendsto (fun x : ℝ => 4 / (x + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div_const (Real.pi ^ 2)
  rwa [sub_zero] at this

/-- **A gap at half depth is free.** The trace missing the dyadic level `⌊log₂ N/2⌋ + 1` has the
conditioning of the full trace: `K_{⌊L/2⌋+1}(N)/(log₂ N)² → 1/π²`. (At the edge level `1` the
limit is `4/π²`.) -/
theorem fermiMiddleGapInverseConstant_logb_limit :
    Tendsto (fun N : ℕ => fermiGapInverseConstant N (Nat.log 2 N / 2 + 1) / (Real.logb 2 N) ^ 2)
      atTop (𝓝 (1 / Real.pi ^ 2)) := by
  have hπ := Real.pi_pos
  rw [tendsto_order]
  constructor
  · intro a ha
    have hl := (tendsto_lower_ratio.comp tendsto_nat_log_two).eventually (eventually_gt_nhds ha)
    filter_upwards [hl, eventually_ge_atTop 4] with N hN h4
    simp only [Function.comp] at hN
    obtain ⟨hx1, hx2⟩ := logb_two_bounds (show 1 ≤ N by omega)
    have hL2 : (2 : ℝ) ≤ (Nat.log 2 N : ℝ) := by
      have : 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
      exact_mod_cast this
    set L : ℝ := (Nat.log 2 N : ℝ)
    have hxpos : 0 < Real.logb 2 N := by linarith
    have hfac : 0 ≤ 1 - 4 / (L + 2) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hK : (1 - 4 / (L + 2)) * (L + 2) ^ 2 / Real.pi ^ 2 ≤
        fermiGapInverseConstant N (Nat.log 2 N / 2 + 1) :=
      (fermiAllBoundaryInverseConstant_ge N h4).1.trans
        (fermiAllBoundaryInverseConstant_le_gap N (Nat.div_le_self _ 2))
    rw [lt_div_iff₀ (by positivity)]
    have hsq : Real.logb 2 N ^ 2 ≤ (L + 2) ^ 2 := pow_le_pow_left₀ hxpos.le (by linarith) 2
    calc a * Real.logb 2 N ^ 2 < (1 - 4 / (L + 2)) / Real.pi ^ 2 * Real.logb 2 N ^ 2 :=
          mul_lt_mul_of_pos_right hN (by positivity)
      _ ≤ (1 - 4 / (L + 2)) / Real.pi ^ 2 * (L + 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (1 - 4 / (L + 2)) * (L + 2) ^ 2 / Real.pi ^ 2 := by ring
      _ ≤ _ := hK
  · intro b hb
    have hβ : 1 < b * Real.pi ^ 2 := by
      rw [gt_iff_lt, div_lt_iff₀ (by positivity)] at hb; linarith
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (show 0 < (b * Real.pi ^ 2 - 1) / 2 by linarith) (show (1 / 2 : ℝ) < 1 by norm_num)
    have hρm : 1 + 1 / (2 : ℝ) ^ (m + 1) < (1 + b * Real.pi ^ 2) / 2 := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have : 1 / (2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ m := by
        rw [one_div_pow, pow_succ]
        exact one_div_le_one_div_of_le hp (by linarith)
      linarith
    set γ := b * Real.pi ^ 2 / (1 + 1 / (2 : ℝ) ^ (m + 1))
    have hγ : 1 < γ := by rw [lt_div_iff₀ (by positivity)]; linarith
    have hu := ((tendsto_shift_sq_profile (2 * (m : ℝ) + 8)).comp tendsto_nat_log_two).eventually
      (eventually_lt_nhds hγ)
    filter_upwards [hu, eventually_ge_atTop (2 ^ (2 * m + 2))] with N hN hNm
    simp only [Function.comp] at hN
    have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hNm
    have hLm : 2 * m + 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hNm
    obtain ⟨hx1, hx2⟩ := logb_two_bounds hN1
    set L := Nat.log 2 N
    have hmh : m ≤ L / 2 := by omega
    have hK := fermiGapInverseConstant_le_explicit N hmh (Nat.div_le_self L 2)
    -- both chain lengths are at most `L + 2m + 8`
    have hM : max (2 * ((L / 2 + m + 2 : ℕ) : ℝ) + 1) (2 * ((L - L / 2 + 3 : ℕ) : ℝ) + 1) ≤
        (L : ℝ) + (2 * m + 8) := by
      apply max_le
      · have : 2 * (L / 2 + m + 2) + 1 ≤ L + (2 * m + 8) := by omega
        exact_mod_cast this
      · have : 2 * (L - L / 2 + 3) + 1 ≤ L + (2 * m + 8) := by omega
        exact_mod_cast this
    have hM0 : 0 ≤ max (2 * ((L / 2 + m + 2 : ℕ) : ℝ) + 1) (2 * ((L - L / 2 + 3 : ℕ) : ℝ) + 1) :=
      le_max_of_le_left (by positivity)
    have hLpos : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 2 ≤ L by omega)
    have hxpos : 0 < Real.logb 2 N := by linarith
    rw [div_lt_iff₀ (by positivity)]
    have hsq : (L : ℝ) ^ 2 ≤ Real.logb 2 N ^ 2 := pow_le_pow_left₀ (by linarith) hx1 2
    have hfac : 0 < 1 + 1 / (2 : ℝ) ^ (m + 1) := by positivity
    have hMsq : (max (2 * ((L / 2 + m + 2 : ℕ) : ℝ) + 1) (2 * ((L - L / 2 + 3 : ℕ) : ℝ) + 1)) ^ 2
        + 2 ≤ ((L : ℝ) + (2 * m + 8)) ^ 2 + 2 := by
      have := pow_le_pow_left₀ hM0 hM 2; linarith
    have hNlt : ((L : ℝ) + (2 * m + 8)) ^ 2 + 2 < γ * (L : ℝ) ^ 2 := by
      rw [div_lt_iff₀ (by positivity)] at hN; exact hN
    calc fermiGapInverseConstant N (L / 2 + 1)
        ≤ (1 + 1 / (2 : ℝ) ^ (m + 1)) * ((max (2 * ((L / 2 + m + 2 : ℕ) : ℝ) + 1)
            (2 * ((L - L / 2 + 3 : ℕ) : ℝ) + 1)) ^ 2 + 2) / Real.pi ^ 2 := hK
      _ ≤ (1 + 1 / (2 : ℝ) ^ (m + 1)) * (((L : ℝ) + (2 * m + 8)) ^ 2 + 2) / Real.pi ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hMsq hfac.le
      _ < (1 + 1 / (2 : ℝ) ^ (m + 1)) * (γ * (L : ℝ) ^ 2) / Real.pi ^ 2 := by
          apply div_lt_div_of_pos_right _ (by positivity)
          exact mul_lt_mul_of_pos_left hNlt hfac
      _ = b * (L : ℝ) ^ 2 := by simp only [γ]; field_simp
      _ ≤ b * Real.logb 2 N ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (lt_trans (by positivity : (0 : ℝ) < 1 / Real.pi ^ 2) hb).le

/-- **Edge versus middle.** The edge gap (the selected trace) is asymptotically four times worse
conditioned than the middle gap. -/
theorem fermiEdgeGap_div_middleGap_limit :
    Tendsto (fun N : ℕ => fermiGapInverseConstant N 1 /
      fermiGapInverseConstant N (Nat.log 2 N / 2 + 1)) atTop (𝓝 4) := by
  have he := fermiPhysicalInverseConstant_logb_limit
  have hm := fermiMiddleGapInverseConstant_logb_limit
  have hπ : (1 / Real.pi ^ 2) ≠ 0 := by positivity
  have hdiv := he.div hm hπ
  rw [show 4 / Real.pi ^ 2 / (1 / Real.pi ^ 2) = 4 by field_simp] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.logb 2 N := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
  simp only [Pi.div_apply]
  rw [fermiGapInverseConstant_one, div_div_div_cancel_right₀ (by positivity)]
