import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiAllBoundaryTraceRisingSinePackets

/-!
# The all-boundary Fermi trace is exactly four times better conditioned

The optimal physical inverse constant of the all-boundary trace satisfies

`K^all_N / (log₂ N)² → 1/π²`,

for real and for nonnegative coefficients, while the selected trace (odd and four-divisible
boundaries) has `K_N / (log₂ N)² → 4/π²`. Hence `K_N / K^all_N → 4`.

Mechanism. On each dyadic ray the selected schedule leaves the step from the odd base to its
first double unobserved: the ray is free at its bottom and pinned only by saturation at its
top, a mixed boundary with ground mode `cos((k + ½)π/(2L+3))` and constant `(2L/π)²`. The cells
`n ≡ 2 (mod 4)` observe exactly that step, so the ray becomes pinned at both ends, a Dirichlet
chain with ground mode `sin((k+1)π/(L+2))` and constant `(L/π)²`. Halving the effective length
of every ray divides the conditioning by four; the loss stays quadratic in `log₂ N`.

Explicit bounds: with `L = log₂ N` (natural logarithm floor),
`(1 - 4/(L+2)) (L+2)²/π² ≤ K^all_N` for `N ≥ 4`, and for every cutoff `m ≤ L + 1`,
`K^all_N ≤ ((L+m+6)²/(π² (1 - 5π²/(48 (L+m+6)²))) + 1)(1 + 2^-(m+1))`.
-/

open Filter Topology Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Explicit lower bound -/

private theorem logb_bounds {N : ℕ} (hN : 1 ≤ N) :
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

private theorem ratio_mem (N : ℕ) (D : Set (ℕ → ℝ)) {c : ℕ → ℝ} (hc : c ∈ D)
    (hQ : 0 < fermiAllBoundaryPronicEnergy N c) :
    sieveTotalPronicEnergy N c / fermiAllBoundaryPronicEnergy N c ∈ fermiAllBoundaryRatios N D :=
  ⟨c, hc, hQ, rfl⟩

/-- **Explicit lower bound.** For `N ≥ 4` and `L = log₂ N`, both all-boundary inverse
constants are at least `(1 - 4/(L+2)) (L+2)²/π²`. -/
theorem fermiAllBoundaryInverseConstant_ge (N : ℕ) (hN : 4 ≤ N) :
    (1 - 4 / ((Nat.log 2 N : ℝ) + 2)) * ((Nat.log 2 N : ℝ) + 2) ^ 2 / Real.pi ^ 2 ≤
        fermiAllBoundaryInverseConstant N ∧
      (1 - 4 / ((Nat.log 2 N : ℝ) + 2)) * ((Nat.log 2 N : ℝ) + 2) ^ 2 / Real.pi ^ 2 ≤
        fermiNonnegativeAllBoundaryInverseConstant N := by
  set L := Nat.log 2 N
  have hL : 2 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hLN : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  obtain ⟨hQ, hratio⟩ := sinePacket_allBoundary_ratio hL hLN
  set c := fermiDyadicSinePacket L
  set θ := sinePacketAngle L
  have hθ : θ = Real.pi / ((L : ℝ) + 2) := rfl
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hθpos : 0 < θ := by rw [hθ]; positivity
  -- `2 - 2 cos θ ≤ θ²`
  have hlamle : 2 - 2 * Real.cos θ ≤ θ ^ 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ); linarith
  have hlampos : 0 < 2 - 2 * Real.cos θ := by
    have hθπ : θ ≤ Real.pi := by
      rw [hθ, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ hθpos
    rw [Real.cos_zero] at this; linarith
  have hfac : 0 ≤ 1 - 4 / ((L : ℝ) + 2) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hκ : (1 - 4 / ((L : ℝ) + 2)) * ((L : ℝ) + 2) ^ 2 / Real.pi ^ 2 ≤
      (1 - 4 / ((L : ℝ) + 2)) / (2 - 2 * Real.cos θ) := by
    have hθsq : θ ^ 2 = Real.pi ^ 2 / ((L : ℝ) + 2) ^ 2 := by rw [hθ, div_pow]
    rw [div_le_div_iff₀ (by positivity) hlampos]
    have : (1 - 4 / ((L : ℝ) + 2)) * ((L : ℝ) + 2) ^ 2 * (2 - 2 * Real.cos θ) ≤
        (1 - 4 / ((L : ℝ) + 2)) * ((L : ℝ) + 2) ^ 2 * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hlamle (by positivity)
    rw [hθsq] at this
    have e : (1 - 4 / ((L : ℝ) + 2)) * ((L : ℝ) + 2) ^ 2 *
        (Real.pi ^ 2 / ((L : ℝ) + 2) ^ 2) = (1 - 4 / ((L : ℝ) + 2)) * Real.pi ^ 2 := by
      field_simp
    linarith
  have hr : (1 - 4 / ((L : ℝ) + 2)) / (2 - 2 * Real.cos θ) ≤
      sieveTotalPronicEnergy N c / fermiAllBoundaryPronicEnergy N c := by
    rw [le_div_iff₀ hQ]; exact hratio
  constructor
  · exact hκ.trans (hr.trans (le_csSup (fermiAllBoundaryRatios_bddAbove N _)
      (ratio_mem N Set.univ (Set.mem_univ _) hQ)))
  · exact hκ.trans (hr.trans (le_csSup (fermiAllBoundaryRatios_bddAbove N _)
      (ratio_mem N _ (fermiDyadicSinePacket_nonneg L) hQ)))

/-! ### Explicit upper bound -/

/-- **Explicit upper bound.** For every cutoff `m ≤ log₂ N + 1`, with
`r = log₂ N + m + 6` and `δ = 5π²/(48 r²)`, both all-boundary inverse constants are at most
`(r²/(π² (1 - δ)) + 1)(1 + 2^-(m+1))`. -/
theorem fermiAllBoundaryInverseConstant_le_explicit (N m : ℕ) (hm : m ≤ Nat.log 2 N + 1) :
    let r : ℝ := (Nat.log 2 N : ℝ) + m + 6
    fermiAllBoundaryInverseConstant N ≤
        (r ^ 2 / Real.pi ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * r ^ 2))⁻¹ + 1) *
          (1 + 1 / (2 : ℝ) ^ (m + 1)) ∧
      fermiNonnegativeAllBoundaryInverseConstant N ≤
        (r ^ 2 / Real.pi ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * r ^ 2))⁻¹ + 1) *
          (1 + 1 / (2 : ℝ) ^ (m + 1)) := by
  intro r
  obtain ⟨h1, h2⟩ := fermiAllBoundaryInverseConstant_le N m hm
  have hr6 : (6 : ℝ) ≤ r := by
    simp only [r]; linarith [(Nat.cast_nonneg (Nat.log 2 N) : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg m : (0 : ℝ) ≤ _)]
  have hcast : (((Nat.log 2 N + 1 + m + 4 : ℕ) : ℝ) + 1) = r := by
    simp only [r]; push_cast; ring
  set t := Real.pi / r with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by linarith)]; linarith [Real.pi_lt_four]
  -- `2 - 2 cos t ≥ t² (1 - 5 t²/48)`
  have hcos := Real.cos_bound (x := t) (by rw [abs_of_pos htpos]; exact ht1)
  rw [abs_of_pos htpos] at hcos
  have hlow : t ^ 2 * (1 - 5 * t ^ 2 / 48) ≤ 2 - 2 * Real.cos t := by
    have := (abs_le.mp hcos).2; nlinarith
  have hδ : 5 * t ^ 2 / 48 = 5 * Real.pi ^ 2 / (48 * r ^ 2) := by
    rw [ht, div_pow]; field_simp
  have hδlt : 5 * t ^ 2 / 48 < 1 := by nlinarith
  have hpos : 0 < t ^ 2 * (1 - 5 * t ^ 2 / 48) := by
    apply mul_pos (by positivity); linarith
  have hinv : 1 / (2 - 2 * Real.cos t) ≤
      r ^ 2 / Real.pi ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * r ^ 2))⁻¹ := by
    have e : t ^ 2 * (1 - 5 * t ^ 2 / 48) =
        Real.pi ^ 2 / r ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * r ^ 2)) := by
      rw [hδ, ht, div_pow]
    calc 1 / (2 - 2 * Real.cos t) ≤ 1 / (t ^ 2 * (1 - 5 * t ^ 2 / 48)) :=
          one_div_le_one_div_of_le hpos hlow
      _ = _ := by rw [e, one_div, mul_inv, inv_div]
  have hρ : 1 / fermiRayWeightFloor m = 1 + 1 / (2 : ℝ) ^ (m + 1) := by
    unfold fermiRayWeightFloor; field_simp
  have hK : fermiAllBoundaryRayConstant N m ≤
      (r ^ 2 / Real.pi ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * r ^ 2))⁻¹ + 1) *
        (1 + 1 / (2 : ℝ) ^ (m + 1)) := by
    unfold fermiAllBoundaryRayConstant
    rw [hcast, ← ht, div_eq_mul_one_div _ (fermiRayWeightFloor m), hρ]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact ⟨h1.trans hK, h2.trans hK⟩

/-! ### The limits -/

private theorem tendsto_log2_floor :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun N hN => Nat.le_log_of_pow_le (by norm_num) hN⟩)

private theorem tendsto_lower_profile :
    Tendsto (fun x : ℝ => (1 - 4 / (x + 2)) / Real.pi ^ 2) atTop (𝓝 (1 / Real.pi ^ 2)) := by
  have h : Tendsto (fun x : ℝ => 4 / (x + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_id)
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h).div_const (Real.pi ^ 2)
  rwa [sub_zero] at this

private theorem tendsto_upper_profile (c : ℝ) :
    Tendsto (fun x : ℝ => ((x + c) ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * (x + c) ^ 2))⁻¹ +
      Real.pi ^ 2) / x ^ 2) atTop (𝓝 1) := by
  have hxc : Tendsto (fun x : ℝ => x + c) atTop atTop := tendsto_atTop_add_const_right _ c tendsto_id
  have hsq : Tendsto (fun x : ℝ => (x + c) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp hxc
  have hδ : Tendsto (fun x : ℝ => 5 * Real.pi ^ 2 / (48 * (x + c) ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hsq.const_mul_atTop (by norm_num))
  have hinv : Tendsto (fun x : ℝ => (1 - 5 * Real.pi ^ 2 / (48 * (x + c) ^ 2))⁻¹) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hδ).inv₀ (by norm_num)
    simpa using this
  have hratio : Tendsto (fun x : ℝ => 1 + c / x) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
    simpa using this
  have hπ : Tendsto (fun x : ℝ => Real.pi ^ 2 / x ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have hlim := ((hratio.pow 2).mul hinv).add hπ
  simp only [one_pow, one_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- **Sharp all-boundary conditioning.** `K^all_N / (log₂ N)² → 1/π²`, for real coefficients
and for nonnegative coefficients. -/
theorem fermiAllBoundaryInverseConstant_logb_limit :
    Tendsto (fun N : ℕ => fermiAllBoundaryInverseConstant N / (Real.logb 2 N) ^ 2)
        atTop (𝓝 (1 / Real.pi ^ 2)) ∧
      Tendsto (fun N : ℕ => fermiNonnegativeAllBoundaryInverseConstant N / (Real.logb 2 N) ^ 2)
        atTop (𝓝 (1 / Real.pi ^ 2)) := by
  have hπ := Real.pi_pos
  -- a common two-sided argument for any constant squeezed between the explicit bounds
  have key : ∀ K : ℕ → ℝ,
      (∀ N, 4 ≤ N → (1 - 4 / ((Nat.log 2 N : ℝ) + 2)) * ((Nat.log 2 N : ℝ) + 2) ^ 2 /
        Real.pi ^ 2 ≤ K N) →
      (∀ N m, m ≤ Nat.log 2 N + 1 → K N ≤
        ((((Nat.log 2 N : ℝ) + m + 6) ^ 2 / Real.pi ^ 2 *
          (1 - 5 * Real.pi ^ 2 / (48 * ((Nat.log 2 N : ℝ) + m + 6) ^ 2))⁻¹ + 1) *
          (1 + 1 / (2 : ℝ) ^ (m + 1)))) →
      Tendsto (fun N : ℕ => K N / (Real.logb 2 N) ^ 2) atTop (𝓝 (1 / Real.pi ^ 2)) := by
    intro K hlo hup
    rw [tendsto_order]
    constructor
    · intro a ha
      have hl := (tendsto_lower_profile.comp tendsto_log2_floor).eventually
        (eventually_gt_nhds ha)
      filter_upwards [hl, eventually_ge_atTop 4] with N hN h4
      simp only [Function.comp] at hN
      obtain ⟨hx1, hx2⟩ := logb_bounds (show 1 ≤ N by omega)
      have hL2 : (2 : ℝ) ≤ (Nat.log 2 N : ℝ) := by
        have : 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
        exact_mod_cast this
      set L : ℝ := (Nat.log 2 N : ℝ)
      have hxpos : 0 < Real.logb 2 N := by linarith
      have hfac : 0 ≤ 1 - 4 / (L + 2) := by
        rw [sub_nonneg, div_le_one (by positivity)]; linarith
      have hK := hlo N h4
      rw [lt_div_iff₀ (by positivity)]
      have hsq : Real.logb 2 N ^ 2 ≤ (L + 2) ^ 2 := pow_le_pow_left₀ hxpos.le (by linarith) 2
      have : a * Real.logb 2 N ^ 2 < (1 - 4 / (L + 2)) / Real.pi ^ 2 * (L + 2) ^ 2 := by
        calc a * Real.logb 2 N ^ 2 < (1 - 4 / (L + 2)) / Real.pi ^ 2 * Real.logb 2 N ^ 2 :=
              mul_lt_mul_of_pos_right hN (by positivity)
          _ ≤ (1 - 4 / (L + 2)) / Real.pi ^ 2 * (L + 2) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
      calc a * Real.logb 2 N ^ 2 < (1 - 4 / (L + 2)) / Real.pi ^ 2 * (L + 2) ^ 2 := this
        _ = (1 - 4 / (L + 2)) * (L + 2) ^ 2 / Real.pi ^ 2 := by ring
        _ ≤ K N := hK
    · intro b hb
      -- choose a cutoff with `(1 + 2^-(m+1))/π² < b`
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
      have hγ : 1 < γ := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      have hu := ((tendsto_upper_profile ((m : ℝ) + 6)).comp tendsto_log2_floor).eventually
        (eventually_lt_nhds hγ)
      filter_upwards [hu, eventually_ge_atTop (2 ^ (m + 2))] with N hN hNm
      simp only [Function.comp] at hN
      have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hNm
      have hLm : m + 2 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hNm
      obtain ⟨hx1, hx2⟩ := logb_bounds hN1
      have hLpos : (2 : ℝ) ≤ (Nat.log 2 N : ℝ) := by
        have : 2 ≤ Nat.log 2 N := by omega
        exact_mod_cast this
      set L : ℝ := (Nat.log 2 N : ℝ)
      have hK := hup N m (by omega)
      have hxpos : 0 < Real.logb 2 N := by linarith
      rw [div_lt_iff₀ (by positivity)]
      have hsq : L ^ 2 ≤ Real.logb 2 N ^ 2 := pow_le_pow_left₀ (by linarith) hx1 2
      have hcol : L + ((m : ℝ) + 6) = L + m + 6 := by ring
      rw [hcol] at hN
      set U := ((L + m + 6) ^ 2 * (1 - 5 * Real.pi ^ 2 / (48 * (L + m + 6) ^ 2))⁻¹ +
        Real.pi ^ 2) / L ^ 2
      have hUeq : ((L + m + 6) ^ 2 / Real.pi ^ 2 *
          (1 - 5 * Real.pi ^ 2 / (48 * (L + m + 6) ^ 2))⁻¹ + 1) = U * L ^ 2 / Real.pi ^ 2 := by
        simp only [U]; field_simp
      rw [hUeq] at hK
      have hfac : 0 < 1 + 1 / (2 : ℝ) ^ (m + 1) := by positivity
      calc K N ≤ U * L ^ 2 / Real.pi ^ 2 * (1 + 1 / (2 : ℝ) ^ (m + 1)) := hK
        _ < γ * L ^ 2 / Real.pi ^ 2 * (1 + 1 / (2 : ℝ) ^ (m + 1)) := by
          apply mul_lt_mul_of_pos_right _ hfac
          apply div_lt_div_of_pos_right _ (by positivity)
          exact mul_lt_mul_of_pos_right hN (by positivity)
        _ = b * L ^ 2 := by simp only [γ]; field_simp
        _ ≤ b * Real.logb 2 N ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (lt_trans (by positivity : (0 : ℝ) < 1 / Real.pi ^ 2) hb).le
  exact ⟨key _ (fun N hN => (fermiAllBoundaryInverseConstant_ge N hN).1)
      (fun N m hm => (fermiAllBoundaryInverseConstant_le_explicit N m hm).1),
    key _ (fun N hN => (fermiAllBoundaryInverseConstant_ge N hN).2)
      (fun N m hm => (fermiAllBoundaryInverseConstant_le_explicit N m hm).2)⟩

/-- **The fourfold gain.** The selected trace is asymptotically exactly four times worse
conditioned than the all-boundary trace: `K_N / K^all_N → 4`, also on nonnegative inputs. -/
theorem fermiSelected_div_allBoundary_inverseConstant_limit :
    Tendsto (fun N : ℕ => fermiPhysicalInverseConstant N / fermiAllBoundaryInverseConstant N)
        atTop (𝓝 4) ∧
      Tendsto (fun N : ℕ => fermiNonnegativePhysicalInverseConstant N /
        fermiNonnegativeAllBoundaryInverseConstant N) atTop (𝓝 4) := by
  have hπ : (1 / Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hval : (4 / Real.pi ^ 2) / (1 / Real.pi ^ 2) = (4 : ℝ) := by field_simp
  obtain ⟨hall, hnn⟩ := fermiAllBoundaryInverseConstant_logb_limit
  have hlog : ∀ᶠ N : ℕ in atTop, Real.logb 2 N ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have := (logb_bounds (show 1 ≤ N by omega)).1
    have h1 : (1 : ℝ) ≤ Nat.log 2 N := by
      have : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
      exact_mod_cast this
    linarith
  constructor
  · have h := (fermiPhysicalInverseConstant_logb_limit.div hall hπ)
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [hlog] with N hN
    simp only [Pi.div_apply]
    field_simp
  · have h := (fermiNonnegativePhysicalInverseConstant_logb_limit.div hnn hπ)
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [hlog] with N hN
    simp only [Pi.div_apply]
    field_simp

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
