import GaloisForLFunctions.HTGeometry.PrimeTupleFormationFrame
import GaloisForLFunctions.HTGeometry.HilbertClosedRange

/-!
# Arity-cofinal fracture of the complete formation tower

Every subset rate of grades `λ_1, …, λ_r > 0` is at most the total grade `A = Σ λ_i`, so the
subset-phase law is stochastically larger than the Erlang law of `2^r - 1` phases of rate `A`, and
`H(t) ≤ (At)^{2^r-1}/(2^r-1)!` `(AFD.19)`.  For the first `r` primes Bertrand's postulate gives
`p_k ≤ 2^k` and `A_r ≤ r(r+1)/2 · log 2` `(AFD.20)`, so the channel norms
`σ_{I_r} = ‖H_{I_r}‖_{L²(0,T)}` tend to zero `(AFD.21)`.

Over all finite nonempty sets of primes the formed response is a diagonal history response with
orthogonal arithmetic endpoints: bounded, injective, with dense range in the closed span of its
orthonormal carriers, but not bounded below, hence without closed range (Theorem 6.3).  At a fixed
grade, channels of large primes saturate the horizon, `sup_I σ_I = √T` (Lemma 7.1, `(AFD.24)`);
consequently no positive weight depending only on the grade makes the weighted tower bounded and
bounded below (Theorem 7.2), and a diagonal weighting has closed range exactly when
`inf_I w_I σ_I > 0` `(AFD.25)`.
-/

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

/-! ### The Erlang upper envelope `(AFD.19)` -/

theorem forall₂_le_replicate {L : ℝ} :
    ∀ {l : List ℝ}, (∀ x ∈ l, x ≤ L) → List.Forall₂ (· ≤ ·) l (List.replicate l.length L)
  | [], _ => List.Forall₂.nil
  | x :: _, h => List.Forall₂.cons (h x List.mem_cons_self)
      (forall₂_le_replicate fun y hy => h y (List.mem_cons_of_mem x hy))

theorem le_total_of_mem_subsetRates {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    ∀ x ∈ subsetRates lam, x ≤ ∑ i, lam i := fun x hx => by
  obtain ⟨S, -, rfl⟩ := List.mem_map.1 hx
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun i _ _ => (hlam i).le

/-- **`(AFD.19)`**: `H_r(t) ≤ (A t)^{2^r-1}/(2^r-1)!` with `A = Σ_i λ_i`. -/
theorem subsetCDF_le_pow {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) :
    subsetCDF lam t ≤ ((∑ i, lam i) * t) ^ (2 ^ r - 1) / (2 ^ r - 1).factorial := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [show 2 ^ 0 - 1 = 0 from rfl, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact hypoCDFList_le_one (subsetRates_pos hlam) ht
  have hA : 0 < ∑ i, lam i := Finset.sum_pos (fun i _ => hlam i) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  have h1 := hypoCDFList_mono (forall₂_le_replicate (le_total_of_mem_subsetRates hlam))
    (subsetRates_pos hlam) ht
  rw [length_subsetRates] at h1
  exact h1.trans (hypoCDFList_replicate_le_pow _ hA ht)

/-! ### The first primes and Bertrand's postulate `(AFD.20)` -/

theorem nth_prime_succ_le_two_mul (k : ℕ) :
    Nat.nth Nat.Prime (k + 1) ≤ 2 * Nat.nth Nat.Prime k := by
  obtain ⟨q, hq, hpq, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime k)
    (Nat.prime_nth_prime k).pos.ne'
  have hnext : Nat.nth Nat.Prime (k + 1) ≤ q := by
    by_contra hnot
    exact (not_le_of_gt hpq) (Nat.le_nth_of_lt_nth_succ (Nat.lt_of_not_ge hnot) hq)
  exact hnext.trans hq2

/-- `p_{k+1} ≤ 2^{k+1}` (Bertrand). -/
theorem nth_prime_le_two_pow (k : ℕ) : Nat.nth Nat.Prime k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => rw [Nat.nth_prime_zero_eq_two]; norm_num
  | succ k ih => rw [pow_succ]; linarith [nth_prime_succ_le_two_mul k]

/-- Finite nonempty sets of primes. -/
abbrev PrimeSet : Type := {s : Finset ℕ // s.Nonempty ∧ ∀ p ∈ s, p.Prime}

namespace PrimeSet

/-- The increasing enumeration of a prime set. -/
def prime (I : PrimeSet) (i : Fin I.1.card) : ℕ := I.1.orderEmbOfFin rfl i

theorem prime_prime (I : PrimeSet) (i : Fin I.1.card) : (I.prime i).Prime :=
  I.2.2 _ (Finset.orderEmbOfFin_mem _ _ _)

/-- The grades `log p`. -/
def grades (I : PrimeSet) (i : Fin I.1.card) : ℝ := Real.log (I.prime i)

theorem log_two_le_grades (I : PrimeSet) (i : Fin I.1.card) : Real.log 2 ≤ I.grades i :=
  Real.log_le_log two_pos (by exact_mod_cast (I.prime_prime i).two_le)

theorem grades_pos (I : PrimeSet) (i : Fin I.1.card) : 0 < I.grades i :=
  (Real.log_pos one_lt_two).trans_le (I.log_two_le_grades i)

theorem sum_grades (I : PrimeSet) : ∑ i, I.grades i = ∑ p ∈ I.1, Real.log p := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ I.1 rfl, Finset.sum_map]
  rfl

/-- The arithmetic endpoint `Π_{p ∈ I} p`. -/
def endpoint (I : PrimeSet) : ℕ+ := ⟨∏ p ∈ I.1, p, Finset.prod_pos fun p hp => (I.2.2 p hp).pos⟩

theorem endpoint_injective : Function.Injective endpoint := by
  intro I J h
  have h1 : (∏ p ∈ I.1, p) = ∏ p ∈ J.1, p := congrArg PNat.val h
  apply Subtype.ext
  rw [← Nat.primeFactors_prod I.2.2, ← Nat.primeFactors_prod J.2.2, h1]

/-- The first `r` primes, `r ≥ 1`. -/
def firstPrimes (r : ℕ) (hr : 0 < r) : PrimeSet :=
  ⟨(Finset.range r).map ⟨Nat.nth Nat.Prime, Nat.nth_injective Nat.infinite_setOf_prime⟩,
    by simp [Finset.nonempty_range_iff, hr.ne'], fun p hp => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hp
      exact Nat.prime_nth_prime k⟩

theorem card_firstPrimes (r : ℕ) (hr : 0 < r) : (firstPrimes r hr).1.card = r := by
  simp [firstPrimes]

/-- **`(AFD.20)`**: `A_r = Σ_{k<r} log p_k ≤ r(r+1)/2 · log 2`. -/
theorem sum_grades_firstPrimes_le (r : ℕ) (hr : 0 < r) :
    ∑ i, (firstPrimes r hr).grades i ≤ (r * (r + 1) / 2 : ℝ) * Real.log 2 := by
  rw [sum_grades, firstPrimes, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  calc ∑ k ∈ Finset.range r, Real.log (Nat.nth Nat.Prime k)
      ≤ ∑ k ∈ Finset.range r, ((k : ℝ) + 1) * Real.log 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
        exact Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime k).pos)
          (by exact_mod_cast nth_prime_le_two_pow k)
    _ = (r * (r + 1) / 2 : ℝ) * Real.log 2 := by
        rw [← Finset.sum_mul]
        congr 1
        induction r with
        | zero => simp
        | succ r ih =>
          rcases Nat.eq_zero_or_pos r with rfl | hr'
          · simp
          rw [Finset.sum_range_succ, ih hr']
          push_cast
          ring

end PrimeSet

/-! ### The complete formation tower -/

/-- The formed histories over all finite prime sets `(AFD.22)`. -/
def towerFamily : HistoryFamily PrimeSet where
  endpoint := PrimeSet.endpoint
  endpoint_injective := PrimeSet.endpoint_injective
  weight I t := subsetCDF I.grades (max t 0)
  continuous_weight I := (continuous_hypoCDFList _).comp (continuous_id.max continuous_const)
  abs_weight_le I t := by
    have h0 : 0 ≤ subsetCDF I.grades (max t 0) :=
      hypoCDFList_nonneg (subsetRates_pos I.grades_pos) (le_max_right t 0)
    have h1 : subsetCDF I.grades (max t 0) ≤ 1 :=
      hypoCDFList_le_one (subsetRates_pos I.grades_pos) (le_max_right t 0)
    rw [abs_le]
    exact ⟨by linarith, h1⟩

theorem tower_energy_eq {T : ℝ} (hT : 0 ≤ T) (I : PrimeSet) :
    towerFamily.energy T I = ∫ t in (0 : ℝ)..T, subsetCDF I.grades t ^ 2 := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  show subsetCDF I.grades (max t 0) ^ 2 = _
  rw [max_eq_left ht.1]

/-- The channel norm `σ_I = ‖H_I‖_{L²(0,T)}`. -/
def sigma (T : ℝ) (I : PrimeSet) : ℝ := Real.sqrt (towerFamily.energy T I)

theorem tower_energy_pos {T : ℝ} (hT : 0 < T) (I : PrimeSet) : 0 < towerFamily.energy T I := by
  have hl := Real.log_pos one_lt_two
  rw [tower_energy_eq hT.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (Continuous.intervalIntegrable ((continuous_hypoCDFList _).pow 2) _ _) (fun t ht => ?_) hT
  have := (erlangCDF_pos (2 ^ I.1.card - 1) hl ht.1).trans_le
    (erlangCDF_le_subsetCDF hl I.grades_pos I.log_two_le_grades ht.1.le)
  positivity

theorem sigma_pos {T : ℝ} (hT : 0 < T) (I : PrimeSet) : 0 < sigma T I :=
  Real.sqrt_pos.2 (tower_energy_pos hT I)

theorem sigma_le {T : ℝ} (hT : 0 ≤ T) (I : PrimeSet) : sigma T I ≤ Real.sqrt T :=
  Real.sqrt_le_sqrt (towerFamily.energy_le hT I)

theorem norm_tower_single {T : ℝ} (hT : 0 ≤ T) (I : PrimeSet) (a : ℂ) :
    ‖towerFamily.response T (lp.single 2 I a)‖ = sigma T I * ‖a‖ := by
  have h := towerFamily.norm_response_sq hT (lp.single 2 I a)
  have hsum : ∑' J, towerFamily.energy T J *
      ‖(lp.single 2 I a : HistoryFamily.Controls PrimeSet) J‖ ^ 2 =
      towerFamily.energy T I * ‖a‖ ^ 2 := by
    rw [tsum_eq_single I fun J hJ => by simp [lp.single_apply, hJ]]
    simp [lp.single_apply]
  rw [hsum] at h
  rw [sigma, ← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_mul (towerFamily.energy_nonneg hT I),
    Real.sqrt_sq (norm_nonneg _)]

/-! ### The first-prime channels collapse `(AFD.21)` -/

/-- **Corollary 6.2, `(AFD.21)`**: `σ_{I_r} ≤ √T (A_r T)^{2^r-1}/(2^r-1)!`. -/
theorem sigma_firstPrimes_le {T : ℝ} (hT : 0 ≤ T) (r : ℕ) (hr : 0 < r) :
    sigma T (PrimeSet.firstPrimes r hr) ≤ Real.sqrt T *
      (((r * (r + 1) / 2 : ℝ) * Real.log 2 * T) ^ (2 ^ r - 1) / (2 ^ r - 1).factorial) := by
  set I := PrimeSet.firstPrimes r hr
  have hcard := PrimeSet.card_firstPrimes r hr
  set B := ((r * (r + 1) / 2 : ℝ) * Real.log 2 * T) ^ (2 ^ r - 1) / (2 ^ r - 1).factorial
  have hB0 : 0 ≤ B := by positivity
  have hbound : ∀ t ∈ Icc 0 T, subsetCDF I.grades t ^ 2 ≤ B ^ 2 := fun t ht => by
    have h0 := hypoCDFList_nonneg (subsetRates_pos I.grades_pos) ht.1
    have h1 := subsetCDF_le_pow I.grades_pos ht.1
    have e : 2 ^ I.1.card - 1 = 2 ^ r - 1 := by rw [hcard]
    rw [e] at h1
    have hA := PrimeSet.sum_grades_firstPrimes_le r hr
    have h2 : (∑ i, I.grades i) * t ≤ (r * (r + 1) / 2 : ℝ) * Real.log 2 * T := by
      have hsum0 : 0 ≤ ∑ i, I.grades i := Finset.sum_nonneg fun i _ => (I.grades_pos i).le
      calc (∑ i, I.grades i) * t ≤ (∑ i, I.grades i) * T := mul_le_mul_of_nonneg_left ht.2 hsum0
        _ ≤ _ := mul_le_mul_of_nonneg_right hA hT
    have h3 : ((∑ i, I.grades i) * t) ^ (2 ^ r - 1) / (2 ^ r - 1).factorial ≤ B := by
      refine div_le_div_of_nonneg_right (pow_le_pow_left₀ ?_ h2 _) (by positivity)
      exact mul_nonneg (Finset.sum_nonneg fun i _ => (I.grades_pos i).le) ht.1
    exact pow_le_pow_left₀ h0 (h1.trans h3) 2
  have hE : towerFamily.energy T I ≤ T * B ^ 2 := by
    rw [tower_energy_eq hT]
    calc ∫ t in (0 : ℝ)..T, subsetCDF I.grades t ^ 2 ≤ ∫ _ in (0 : ℝ)..T, B ^ 2 :=
          intervalIntegral.integral_mono_on hT
            (Continuous.intervalIntegrable ((continuous_hypoCDFList _).pow 2) _ _)
            intervalIntegrable_const hbound
      _ = T * B ^ 2 := by simp
  calc sigma T I ≤ Real.sqrt (T * B ^ 2) := Real.sqrt_le_sqrt hE
    _ = Real.sqrt T * B := by rw [Real.sqrt_mul hT, Real.sqrt_sq hB0]

theorem tendsto_firstPrimes_bound {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun r : ℕ => ((r * (r + 1) / 2 : ℝ) * Real.log 2 * T) ^ (2 ^ r - 1) /
      (2 ^ r - 1).factorial) atTop (𝓝 0) := by
  set c : ℝ := Real.log 2 * T
  have hc : 0 ≤ c := mul_nonneg (Real.log_pos one_lt_two).le hT
  -- `x^N/N! ≤ (e x/N)^N`
  have hkey : ∀ N : ℕ, 0 < N → ∀ x : ℝ, 0 ≤ x →
      x ^ N / N.factorial ≤ (Real.exp 1 * x / N) ^ N := fun N hN x hx => by
    have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    rw [div_le_iff₀ hfac] at h
    rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one, div_le_div_iff₀ hfac (by positivity)]
    calc x ^ N * (N : ℝ) ^ N ≤ x ^ N * (Real.exp N * N.factorial) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg hx N)
      _ = Real.exp N * x ^ N * N.factorial := by ring
  -- the base tends to zero
  have hbase : Tendsto (fun r : ℕ => Real.exp 1 * ((r * (r + 1) / 2 : ℝ) * c) /
      ((2 ^ r - 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (one_lt_two : (1 : ℝ) < 2)).add
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (one_lt_two : (1 : ℝ) < 2))
    rw [zero_add] at h1
    have h2 := h1.const_mul (Real.exp 1 * c)
    rw [mul_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun r => by positivity) ?_ h2
    filter_upwards [eventually_ge_atTop 1] with r hr
    have h2r : (2 : ℝ) ^ r ≥ 2 := by
      calc (2 : ℝ) ^ r ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hr
        _ = 2 := by norm_num
    have hcast : ((2 ^ r - 1 : ℕ) : ℝ) = (2 : ℝ) ^ r - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]; norm_num
    rw [hcast, div_le_iff₀ (by linarith)]
    have hpos : 0 ≤ Real.exp 1 * c := by positivity
    have : (r * (r + 1) / 2 : ℝ) ≤
        ((r : ℝ) ^ 2 / 2 ^ r + (r : ℝ) ^ 1 / 2 ^ r) * ((2 : ℝ) ^ r - 1) := by
      rw [← add_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith [pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr]
    calc Real.exp 1 * ((r * (r + 1) / 2 : ℝ) * c) = (Real.exp 1 * c) * (r * (r + 1) / 2 : ℝ) := by
          ring
      _ ≤ (Real.exp 1 * c) * (((r : ℝ) ^ 2 / 2 ^ r + (r : ℝ) ^ 1 / 2 ^ r) * ((2 : ℝ) ^ r - 1)) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  have hhalf : ∀ᶠ r : ℕ in atTop, Real.exp 1 * ((r * (r + 1) / 2 : ℝ) * c) /
      ((2 ^ r - 1 : ℕ) : ℝ) ≤ 1 / 2 := hbase.eventually (eventually_le_nhds (by norm_num))
  have hgeom : Tendsto (fun r : ℕ => (1 / 2 : ℝ) ^ r) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun r => by positivity) ?_ hgeom
  filter_upwards [hhalf, eventually_ge_atTop 1] with r hr hr1
  have hN : 0 < 2 ^ r - 1 := by have := Nat.one_lt_two_pow (n := r) (by omega); omega
  have hNr : r ≤ 2 ^ r - 1 := by have := Nat.lt_two_pow_self (n := r); omega
  calc ((r * (r + 1) / 2 : ℝ) * Real.log 2 * T) ^ (2 ^ r - 1) / (2 ^ r - 1).factorial
      ≤ (Real.exp 1 * ((r * (r + 1) / 2 : ℝ) * c) / ((2 ^ r - 1 : ℕ) : ℝ)) ^ (2 ^ r - 1) := by
        have := hkey (2 ^ r - 1) hN ((r * (r + 1) / 2 : ℝ) * c) (by positivity)
        simpa [c, mul_assoc] using this
    _ ≤ (1 / 2 : ℝ) ^ (2 ^ r - 1) := pow_le_pow_left₀ (by positivity) hr _
    _ ≤ (1 / 2 : ℝ) ^ r := pow_le_pow_of_le_one (by norm_num) (by norm_num) hNr

/-- **The first-prime channel norms tend to zero.** -/
theorem tendsto_sigma_firstPrimes {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun r : ℕ => sigma T (PrimeSet.firstPrimes (r + 1) r.succ_pos)) atTop (𝓝 0) := by
  have h := ((tendsto_firstPrimes_bound hT).comp (tendsto_add_atTop_nat 1)).const_mul
    (Real.sqrt T)
  rw [mul_zero] at h
  exact squeeze_zero (fun r => Real.sqrt_nonneg _)
    (fun r => sigma_firstPrimes_le hT (r + 1) r.succ_pos) h


/-! ### Diagonal operators on an orthonormal family `(AFD.25)` -/

section OrthonormalDiagonal

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- An operator sending `e_i ↦ μ_i v_i` sends `c ↦ Σ_i c_i μ_i v_i`. -/
theorem hasSum_apply_of_basis {A : lp (fun _ : ι => ℂ) 2 →L[ℂ] E} {μ : ι → ℂ} {v : ι → E}
    (hA : ∀ i, A (lp.single 2 i 1) = μ i • v i) (c : lp (fun _ : ι => ℂ) 2) :
    HasSum (fun i => (c i * μ i) • v i) (A c) := by
  have h := (lp.hasSum_single (p := 2) (by norm_num) c).mapL A
  have hs : ∀ i, A (lp.single 2 i (c i)) = (c i * μ i) • v i := fun i => by
    have e : lp.single (E := fun _ : ι => ℂ) 2 i (c i) = c i • lp.single 2 i (1 : ℂ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [e, map_smul, hA, smul_smul]
  simpa only [hs] using h

omit [CompleteSpace E] in
/-- The coefficients of `A c` along an orthonormal family: `⟨v_j, A c⟩ = c_j μ_j`. -/
theorem inner_apply_of_basis {A : lp (fun _ : ι => ℂ) 2 →L[ℂ] E} {μ : ι → ℂ} {v : ι → E}
    (hv : Orthonormal ℂ v) (hA : ∀ i, A (lp.single 2 i 1) = μ i • v i) (j : ι)
    (c : lp (fun _ : ι => ℂ) 2) : ⟪v j, A c⟫_ℂ = c j * μ j := by
  have h := (hasSum_apply_of_basis hA c).mapL (innerSL ℂ (v j))
  simp only [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.mp hv] at h
  refine h.unique ?_
  have e : (fun i => c i * μ i * if j = i then (1 : ℂ) else 0) =
      fun i => if i = j then c j * μ j else 0 := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [e]
  exact hasSum_ite_eq j _

omit [CompleteSpace E] in
/-- With nonzero multipliers the operator is injective. -/
theorem injective_of_basis {A : lp (fun _ : ι => ℂ) 2 →L[ℂ] E} {μ : ι → ℂ} {v : ι → E}
    (hv : Orthonormal ℂ v) (hA : ∀ i, A (lp.single 2 i 1) = μ i • v i) (hμ : ∀ i, μ i ≠ 0) :
    Function.Injective A := by
  refine (injective_iff_map_eq_zero A).2 fun c hc => lp.ext (funext fun j => ?_)
  have h := inner_apply_of_basis hv hA j c
  rw [hc, inner_zero_right] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (hμ j)

omit [CompleteSpace E] in
/-- A uniform lower bound `m ≤ |μ_i|` gives `m ‖c‖ ≤ ‖A c‖` (Bessel). -/
theorem mul_norm_le_apply_of_basis {A : lp (fun _ : ι => ℂ) 2 →L[ℂ] E} {μ : ι → ℂ} {v : ι → E}
    (hv : Orthonormal ℂ v) (hA : ∀ i, A (lp.single 2 i 1) = μ i • v i) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ i, m ≤ ‖μ i‖) (c : lp (fun _ : ι => ℂ) 2) : m * ‖c‖ ≤ ‖A c‖ := by
  have hb := hv.tsum_inner_products_le (A c)
  have hs := hv.inner_products_summable (A c)
  simp_rw [inner_apply_of_basis hv hA] at hb hs
  have h2 : (m * ‖c‖) ^ 2 ≤ ‖A c‖ ^ 2 := by
    rw [mul_pow, HistoryFamily.lp_norm_sq c, ← tsum_mul_left]
    refine le_trans (Summable.tsum_le_tsum (fun i => ?_)
      ((HistoryFamily.summable_norm_sq c).mul_left _) hs) hb
    rw [norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 (hm i) 2) (by positivity)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2

/-- **`(AFD.25)`: diagonal classification.**  For nonzero multipliers `μ_i` on an orthonormal
family, a bounded operator with `e_i ↦ μ_i v_i` and closed range exists exactly when
`0 < inf_i |μ_i| ≤ sup_i |μ_i| < ∞`. -/
theorem exists_closedRange_of_basis_iff {μ : ι → ℂ} {v : ι → E} (hv : Orthonormal ℂ v)
    (hμ : ∀ i, μ i ≠ 0) :
    (∃ A : lp (fun _ : ι => ℂ) 2 →L[ℂ] E, (∀ i, A (lp.single 2 i 1) = μ i • v i) ∧
      IsClosed (Set.range A)) ↔ ∃ m > 0, ∃ M, ∀ i, m ≤ ‖μ i‖ ∧ ‖μ i‖ ≤ M := by
  constructor
  · rintro ⟨A, hA, hcl⟩
    obtain ⟨m, hm, hb⟩ := (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range A).2 hcl
    have hker : LinearMap.ker (A : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] E) = ⊥ :=
      LinearMap.ker_eq_bot.2 (injective_of_basis hv hA hμ)
    refine ⟨m, hm, ‖A‖, fun i => ⟨?_, ?_⟩⟩
    · have h := hb (lp.single 2 i 1) (by rw [hker, Submodule.bot_orthogonal_eq_top]; trivial)
      rwa [hA, norm_smul, hv.1 i, mul_one, lp.norm_single (by norm_num), norm_one, mul_one] at h
    · have h := A.le_opNorm (lp.single 2 i 1)
      rwa [hA, norm_smul, hv.1 i, mul_one, lp.norm_single (by norm_num), norm_one, mul_one] at h
  · rintro ⟨m, hm, M, hb⟩
    set V := hv.orthogonalFamily.linearIsometry
    set A := V.toContinuousLinearMap.comp (ellTwoDiagonal μ fun i => (hb i).2)
    have hA : ∀ i, A (lp.single 2 i 1) = μ i • v i := fun i => by
      have hd : ellTwoDiagonal μ (fun i => (hb i).2) (lp.single 2 i 1) = lp.single 2 i (μ i) := by
        refine lp.ext (funext fun j => ?_)
        rw [ellTwoDiagonal_apply, lp.single_apply, lp.single_apply]
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      simp only [A, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, hd,
        V, OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply]
    refine ⟨A, hA, (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range A).1
      ⟨m, hm, fun x _ => mul_norm_le_apply_of_basis hv hA hm.le (fun i => (hb i).1) x⟩⟩

end OrthonormalDiagonal

/-! ### Theorem 6.3: the full tower has dense nonclosed range -/

theorem response_tower_single {T : ℝ} (hT : 0 < T) (I : PrimeSet) (a : ℂ) :
    towerFamily.response T (lp.single 2 I a) = ((sigma T I : ℂ) * a) • towerFamily.carrier T I := by
  have hs : (sigma T I : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sigma_pos hT I).ne'
  refine Lp.ext ((towerFamily.coeFn_response T _).trans ?_)
  refine (EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm)
  refine ((towerFamily.memLp_carrierProfile T I).coeFn_toLp.mono fun t ht => ?_)
  simp only [Pi.smul_apply]
  rw [show (towerFamily.carrier T I : ℝ → ArithSpace) t = towerFamily.carrierProfile T I t from ht,
    towerFamily.profile_single, HistoryFamily.carrierProfile, smul_smul]
  congr 1
  rw [← sigma]
  push_cast
  field_simp

theorem orthonormal_tower_carrier {T : ℝ} (hT : 0 < T) :
    Orthonormal ℂ (towerFamily.carrier T) :=
  towerFamily.orthonormal_carrier hT.le (tower_energy_pos hT)

/-- The channel space `Y_T`: the closed span of the normalized channel profiles `f_I`. -/
def channelSpace (T : ℝ) : Submodule ℂ (ResponseSpace T) :=
  (Submodule.span ℂ (Set.range (towerFamily.carrier T))).topologicalClosure

/-- **Theorem 6.3, full-tower properness fracture.**  The complete formed response
`e_I ↦ σ_I f_I` over all finite prime sets is bounded by `√T`, injective, has dense range in the
channel space `Y_T`, and does not have closed range. -/
theorem tower_fracture {T : ℝ} (hT : 0 < T) :
    (∀ c, ‖towerFamily.response T c‖ ≤ Real.sqrt T * ‖c‖) ∧
      Function.Injective (towerFamily.response T) ∧
      (LinearMap.range (towerFamily.response T : HistoryFamily.Controls PrimeSet →ₗ[ℂ]
        ResponseSpace T)).topologicalClosure = channelSpace T ∧
      ¬ IsClosed (Set.range (towerFamily.response T)) := by
  have hA : ∀ I, towerFamily.response T (lp.single 2 I 1) =
      (sigma T I : ℂ) • towerFamily.carrier T I := fun I => by
    rw [response_tower_single hT, mul_one]
  have hμ : ∀ I, (sigma T I : ℂ) ≠ 0 := fun I => Complex.ofReal_ne_zero.2 (sigma_pos hT I).ne'
  refine ⟨fun c => ?_, injective_of_basis (orthonormal_tower_carrier hT) hA hμ, ?_, ?_⟩
  · have h := (towerFamily.frame_bounds hT.le (m := 0) (fun I => towerFamily.energy_nonneg hT.le I)
      (fun I => towerFamily.energy_le hT.le I) c).2
    have h2 : ‖towerFamily.response T c‖ ^ 2 ≤ (Real.sqrt T * ‖c‖) ^ 2 := by
      rwa [mul_pow, Real.sq_sqrt hT.le]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  · refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_
      (Submodule.isClosed_topologicalClosure _)) (Submodule.topologicalClosure_mono ?_)
    · rintro _ ⟨c, rfl⟩
      refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
        (hasSum_apply_of_basis hA c) (.of_forall fun s => Submodule.sum_mem _ fun I _ => ?_)
      exact Submodule.le_topologicalClosure _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨I, rfl⟩
      refine ⟨lp.single 2 I ((sigma T I : ℂ)⁻¹), ?_⟩
      rw [ContinuousLinearMap.coe_coe, response_tower_single hT, mul_inv_cancel₀ (hμ I), one_smul]
  · intro hcl
    obtain ⟨m, hm, _, hb⟩ := (exists_closedRange_of_basis_iff (orthonormal_tower_carrier hT) hμ).1
      ⟨_, hA, hcl⟩
    have hlim := tendsto_sigma_firstPrimes (T := T) hT.le
    obtain ⟨r, hr⟩ := (hlim.eventually (gt_mem_nhds hm)).exists
    have := (hb (PrimeSet.firstPrimes (r + 1) r.succ_pos)).1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sigma_pos hT _)] at this
    linarith

/-! ### Lemma 7.1: high-prime channels saturate the horizon `(AFD.24)` -/

theorem tendsto_erlangCDF_atTop (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun l => erlangCDF N l t) atTop (𝓝 1) := by
  have hx : Tendsto (fun l : ℝ => l * t) atTop atTop := tendsto_id.atTop_mul_const ht
  have h0 : Tendsto (fun l : ℝ => Real.exp (-(l * t)) *
      ∑ j ∈ Finset.range N, (l * t) ^ j / j.factorial) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range N) fun j _ =>
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp hx).div_const (j.factorial : ℝ)
    simp only [zero_div, Finset.sum_const_zero] at h
    refine h.congr fun l => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    ring
  have := h0.const_sub 1
  rw [sub_zero] at this
  exact this

theorem erlangCDF_nonneg (N : ℕ) {l t : ℝ} (hl : 0 < l) (ht : 0 ≤ t) : 0 ≤ erlangCDF N l t := by
  rw [← hypoCDFList_replicate]
  exact hypoCDFList_nonneg (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hl) ht

theorem erlangCDF_le_one (N : ℕ) {l t : ℝ} (hl : 0 < l) (ht : 0 ≤ t) : erlangCDF N l t ≤ 1 := by
  rw [← hypoCDFList_replicate]
  exact hypoCDFList_le_one (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hl) ht

/-- `∫₀ᵀ G_{N,l}(t)² dt → T` as the Erlang rate `l → ∞`. -/
theorem tendsto_integral_erlangCDF_sq (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun l => ∫ t in (0 : ℝ)..T, erlangCDF N l t ^ 2) atTop (𝓝 T) := by
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := T) (l := atTop) (F := fun l t => erlangCDF N l t ^ 2) (f := fun _ => 1)
    (fun _ => 1)
    (.of_forall fun l => by
      refine Continuous.aestronglyMeasurable ?_
      unfold erlangCDF
      fun_prop)
    (by
      filter_upwards [eventually_gt_atTop 0] with l hl
      refine ae_of_all _ fun t ht => ?_
      rw [uIoc_of_le hT] at ht
      have h0 := erlangCDF_nonneg N hl ht.1.le
      have h1 := erlangCDF_le_one N hl ht.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith)
    intervalIntegrable_const
    (ae_of_all _ fun t ht => by
      rw [uIoc_of_le hT] at ht
      simpa using (tendsto_erlangCDF_atTop N ht.1).pow 2)
  simpa using h

namespace PrimeSet

/-- The prime block `p_{k+1}, …, p_{k+r+1}`. -/
def block (k r : ℕ) : PrimeSet :=
  ⟨(Finset.Ico k (k + r + 1)).map ⟨Nat.nth Nat.Prime, Nat.nth_injective Nat.infinite_setOf_prime⟩,
    by simp, fun p hp => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hp
      exact Nat.prime_nth_prime j⟩

theorem card_block (k r : ℕ) : (block k r).1.card = r + 1 := by
  simp [block]
  omega

theorem log_le_grades_block (k r : ℕ) (i : Fin (block k r).1.card) :
    Real.log (Nat.nth Nat.Prime k) ≤ (block k r).grades i := by
  have hmem : (block k r).prime i ∈ (block k r).1 := Finset.orderEmbOfFin_mem _ _ _
  obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 hmem
  have hk : k ≤ j := (Finset.mem_Ico.1 hj).1
  rw [grades, ← hji]
  exact Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime k).pos)
    (by exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hk)

end PrimeSet

theorem tendsto_log_nth_prime : Tendsto (fun k => Real.log (Nat.nth Nat.Prime k)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
    (Nat.nth_strictMono Nat.infinite_setOf_prime).tendsto_atTop)

/-- The prime blocks of a fixed grade saturate the horizon: `σ_{I_k} → √T`. -/
theorem tendsto_sigma_block {T : ℝ} (hT : 0 ≤ T) (r : ℕ) :
    Tendsto (fun k => sigma T (PrimeSet.block k r)) atTop (𝓝 (Real.sqrt T)) := by
  refine (Real.continuous_sqrt.tendsto T).comp ?_
  have hlow : ∀ k, ∫ t in (0 : ℝ)..T, erlangCDF (2 ^ (r + 1) - 1)
      (Real.log (Nat.nth Nat.Prime k)) t ^ 2 ≤ towerFamily.energy T (PrimeSet.block k r) :=
      fun k => by
    rw [tower_energy_eq hT]
    have hl : 0 < Real.log (Nat.nth Nat.Prime k) :=
      Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime k).one_lt)
    refine intervalIntegral.integral_mono_on hT
      (Continuous.intervalIntegrable (by unfold erlangCDF; fun_prop) _ _)
      (Continuous.intervalIntegrable ((continuous_hypoCDFList _).pow 2) _ _) fun t ht => ?_
    have h := erlangCDF_le_subsetCDF hl (PrimeSet.grades_pos _) (PrimeSet.log_le_grades_block k r)
      ht.1
    have e : 2 ^ (PrimeSet.block k r).1.card - 1 = 2 ^ (r + 1) - 1 := by
      rw [PrimeSet.card_block]
    rw [e] at h
    exact pow_le_pow_left₀ (erlangCDF_nonneg _ hl ht.1) h 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((tendsto_integral_erlangCDF_sq _ hT).comp tendsto_log_nth_prime) tendsto_const_nhds hlow
    fun k => towerFamily.energy_le hT _

/-- **Lemma 7.1, `(AFD.24)`**: at every grade `r + 1`, `sup_{|I| = r+1} σ_I = √T`. -/
theorem isLUB_sigma_grade {T : ℝ} (hT : 0 ≤ T) (r : ℕ) :
    IsLUB {s | ∃ I : PrimeSet, I.1.card = r + 1 ∧ sigma T I = s} (Real.sqrt T) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨I, -, rfl⟩
    exact sigma_le hT I
  · exact le_of_tendsto' (tendsto_sigma_block hT r) fun k =>
      hb ⟨PrimeSet.block k r, PrimeSet.card_block k r, rfl⟩

/-! ### Theorem 7.2: no grade-only weighting repairs the tower -/

/-- **Source-dependent weights `(AFD.25)`.**  For positive weights `w_I`, a bounded operator with
`e_I ↦ w_I σ_I f_I` and closed range exists exactly when `0 < inf w_I σ_I ≤ sup w_I σ_I < ∞`. -/
theorem sourceWeight_closedRange_iff {T : ℝ} (hT : 0 < T) {w : PrimeSet → ℝ} (hw : ∀ I, 0 < w I) :
    (∃ A : HistoryFamily.Controls PrimeSet →L[ℂ] ResponseSpace T,
      (∀ I, A (lp.single 2 I 1) = ((w I * sigma T I : ℝ) : ℂ) • towerFamily.carrier T I) ∧
      IsClosed (Set.range A)) ↔
      ∃ m > 0, ∃ M, ∀ I, m ≤ w I * sigma T I ∧ w I * sigma T I ≤ M := by
  have hpos : ∀ I, 0 < w I * sigma T I := fun I => mul_pos (hw I) (sigma_pos hT I)
  rw [exists_closedRange_of_basis_iff (orthonormal_tower_carrier hT)
    fun I => Complex.ofReal_ne_zero.2 (hpos I).ne']
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]

/-- **Theorem 7.2, grade-only renormalization no-go.**  For no positive weight `w_r` depending
only on the grade is there a bounded operator `e_I ↦ w_{|I|} σ_I f_I` with closed range. -/
theorem no_gradeOnly_weight {T : ℝ} (hT : 0 < T) {w : ℕ → ℝ} (hw : ∀ r, 0 < w r) :
    ¬ ∃ A : HistoryFamily.Controls PrimeSet →L[ℂ] ResponseSpace T,
      (∀ I, A (lp.single 2 I 1) = ((w I.1.card * sigma T I : ℝ) : ℂ) • towerFamily.carrier T I) ∧
      IsClosed (Set.range A) := by
  intro h
  obtain ⟨m, hm, M, hb⟩ := (sourceWeight_closedRange_iff hT (w := fun I => w I.1.card)
    fun I => hw _).1 h
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  -- boundedness on high-prime channels bounds every weight
  have hwM : ∀ r, w (r + 1) ≤ M / Real.sqrt T := fun r => by
    rw [le_div_iff₀ hsT, mul_comm]
    have hub : Real.sqrt T ≤ M / w (r + 1) := (isLUB_sigma_grade hT.le r).2 fun _ ⟨I, hI, hs⟩ => by
      rw [← hs, le_div_iff₀ (hw _), mul_comm, ← hI]
      exact (hb I).2
    rwa [le_div_iff₀ (hw _)] at hub
  -- the first-prime channels then violate the lower bound
  have hlim := (tendsto_sigma_firstPrimes (T := T) hT.le).const_mul (M / Real.sqrt T)
  rw [mul_zero] at hlim
  obtain ⟨r, hr⟩ := (hlim.eventually (gt_mem_nhds hm)).exists
  have h1 := (hb (PrimeSet.firstPrimes (r + 1) r.succ_pos)).1
  rw [PrimeSet.card_firstPrimes] at h1
  have h2 := mul_le_mul_of_nonneg_right (hwM r) (sigma_pos hT (PrimeSet.firstPrimes (r + 1)
    r.succ_pos)).le
  linarith

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
