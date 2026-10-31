import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff

/-!
# Explicit constants for rough harmonic conditioning

The finite-sieve ground moment bounds the reciprocal Euler product without an
asymptotic threshold. Thin-shell estimates then give an explicit uniform
prime-fibre variance constant and an explicit conditioning error.
-/

noncomputable section

open Finset Filter
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

/-- The prime-prefix sieve density is the usual finite Mertens product. -/
theorem sieveDensity_primePrefix_succ (n : ℕ) :
    sieveDensity (primePrefixSieve (n + 1)) = RHTower.mertensPrimeProduct n := by
  unfold sieveDensity primePrefixSieve RHTower.mertensPrimeProduct
  change (∏ p ∈ ((range (n + 1)).filter Nat.Prime).subtype Nat.Prime,
    (1 - ((p : ℕ) : ℝ)⁻¹)) = _
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => 1 - (p : ℝ)⁻¹)
    (fun p hp => (mem_filter.mp hp).2), prod_filter]
  congr 1
  ext k
  simp only [mem_range, mem_Icc, Nat.zero_le, true_and]
  omega

/-- The Euler correction gives the numerical bound `P(n) log n ≥ 1/128`. -/
theorem mertensPrimeProduct_mul_log_ge_one_div_128 {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / 128 ≤ RHTower.mertensPrimeProduct n * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hnext : Real.log (n + 1 : ℕ) ≤ Real.log n + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ))
      (show ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * 2 by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        push_cast
        linarith only [hn1])
    rwa [Real.log_mul hn0.ne' (by norm_num)] at h
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hL := ladderConstant_le_log (show 1 ≤ n + 1 by omega)
  have hfactor : Real.log 2 + 2 * ladderConstant (n + 1) + 4 ≤ 64 * Real.log n := by
    rw [hlog4] at hL
    linarith only [hL, hnext, hlogn, hlog2]
  have hmass := sievedHarmonic_le_density_log_euler (primePrefixSieve (n + 1)) 1
  rw [sievedHarmonic_primePrefix_eq, sieveDensity_primePrefix_succ,
    sieveEuler_primePrefix_sub_euler] at hmass
  have hone : roughHarmonic (n + 1) 1 = 1 := by
    have hR : roughInterval (n + 1) 1 = {1} := by
      ext k
      constructor
      · intro hk
        have h := mem_roughInterval.mp hk
        exact mem_singleton.mpr (by omega)
      · intro hk
        rw [mem_singleton.mp hk]
        exact one_mem_roughInterval _ le_rfl
    rw [roughHarmonic, hR, sum_singleton]
    norm_num
  rw [hone] at hmass
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hmass
  have hprod := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ 2 * RHTower.mertensPrimeProduct n by
      exact mul_nonneg zero_le_two (RHTower.mertensPrimeProduct_pos n).le)
  nlinarith only [hmass, hprod]

/-- A closed-form upper bound for the harmonic mass of every multiplicative rough shell. -/
def roughShellMassConstant : ℝ :=
  24 / Real.log 2 + 1715 * (1 / (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ)))

theorem roughShellMassConstant_nonneg : 0 ≤ roughShellMassConstant := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : (2 : ℝ) ^ (-(1 / 4) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold roughShellMassConstant
  positivity

/-- The dyadic Selberg bound summed with its explicit geometric remainder. -/
theorem roughHarmonic_shell_le_explicit : ∀ p : ℕ, p.Prime → ∀ Y X : ℕ, 1 ≤ Y →
    X ≤ p * (Y + 1) →
      ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => Y < K), (1 : ℝ) / K ≤
        roughShellMassConstant := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 4) : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro p hp Y X hY hX
  have hp2 := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  set a := max Y p
  have ha1 : p ≤ a := le_max_right _ _
  have haY : Y ≤ a := le_max_left _ _
  set I := Nat.log 2 p + 2
  -- the shell lies in `(a, 2^I a]`
  have hsub : (roughInterval (p + 1) X).filter (fun K => Y < K) ⊆
      (roughInterval (p + 1) X).filter (fun K => a < K ∧ K ≤ 2 ^ I * a) := by
    intro K hK
    obtain ⟨hKR, hYK⟩ := mem_filter.mp hK
    have hKp : p + 1 ≤ K := lt_of_mem_roughInterval hKR (by omega)
    have hKX := (mem_roughInterval.mp hKR).2.1
    have hpow : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
    have hI : 2 ^ I = 2 * 2 ^ (Nat.log 2 p + 1) := by rw [pow_succ]; ring
    have hXa : X ≤ 2 ^ I * a := by
      have h1 : p * (Y + 1) ≤ p * (2 * a) := Nat.mul_le_mul_left p (by omega)
      have h2 : p * (2 * a) ≤ 2 ^ (Nat.log 2 p + 1) * (2 * a) := Nat.mul_le_mul_right _ hpow.le
      rw [hI]
      calc X ≤ p * (Y + 1) := hX
        _ ≤ 2 ^ (Nat.log 2 p + 1) * (2 * a) := h1.trans h2
        _ = 2 * 2 ^ (Nat.log 2 p + 1) * a := by ring
    exact mem_filter.mpr ⟨hKR, by omega, hKX.trans hXa⟩
  have hblock : ∀ i ∈ range I, ∑ K ∈ (roughInterval (p + 1) X).filter
      (fun K => 2 ^ i * a < K ∧ K ≤ 2 * (2 ^ i * a)), (1 : ℝ) / K ≤
        8 / Real.log p + 1715 * r ^ i := by
    intro i _
    set x := 2 ^ i * a
    have hxa : a ≤ x := Nat.le_mul_of_pos_left a (by positivity)
    have hxp : (p : ℝ) ≤ x := by exact_mod_cast ha1.trans hxa
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx2 : (2 : ℝ) ^ (i + 1) ≤ x := by
      have : 2 ^ (i + 1) ≤ x := by
        rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
      exact_mod_cast this
    set z : ℝ := min (p : ℝ) ((x : ℝ) ^ (1 / 4 : ℝ))
    have hz1 : (p : ℝ) ^ (1 / 4 : ℝ) ≤ z := le_min
      (by simpa using Real.rpow_le_rpow_of_exponent_le hp1.le (show (1 / 4 : ℝ) ≤ 1 by norm_num))
      (Real.rpow_le_rpow (by positivity) hxp (by norm_num))
    have hpz : 1 < (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow hp1 (by norm_num)
    have hz : 1 < z := hpz.trans_le hz1
    have hlz : (1 / 4) * Real.log p ≤ Real.log z := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) hz1
    have hmain : 2 / Real.log z ≤ 8 / Real.log p := by
      have hlp : 0 < Real.log p := Real.log_pos hp1
      calc 2 / Real.log z ≤ 2 / ((1 / 4) * Real.log p) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hlz
        _ = 8 / Real.log p := by field_simp; ring
    have herr : 5 * z * (1 + Real.log z) ^ 3 / x ≤ 1715 * r ^ i := by
      refine (sieve_error_le hx1 hz.le (min_le_right _ _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc (x : ℝ) ^ (-(1 / 4) : ℝ) ≤ ((2 : ℝ) ^ (i + 1)) ^ (-(1 / 4) : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hx2 (by norm_num)
        _ = r ^ (i + 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), mul_comm]
        _ ≤ r ^ i := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ i)
    have hx0 : 0 < x := by positivity
    calc _ ≤ 2 / Real.log z + 5 * z * (1 + Real.log z) ^ 3 / x :=
          sum_roughInterval_block_le hp X x hx0 hz (min_le_left _ _)
      _ ≤ 8 / Real.log p + 1715 * r ^ i := add_le_add hmain herr
  have hgeom : ∑ i ∈ range I, r ^ i ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := I) hr0 hr1
    rwa [← range_eq_Ico, pow_zero] at this
  have hIlog : (I : ℝ) * (8 / Real.log p) ≤ 24 / Real.log 2 := by
    have hn : (Nat.log 2 p : ℝ) ≤ Real.log p / Real.log 2 := by
      have := Real.natLog_le_logb p 2
      rwa [Real.logb] at this
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have : (I : ℝ) = Nat.log 2 p + 2 := by simp [I]
    rw [this]
    calc ((Nat.log 2 p : ℝ) + 2) * (8 / Real.log p)
        ≤ (Real.log p / Real.log 2 + 2) * (8 / Real.log p) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 8 / Real.log 2 + 16 / Real.log p := by field_simp; ring
      _ ≤ 8 / Real.log 2 + 16 / Real.log 2 := by
          gcongr
      _ = 24 / Real.log 2 := by ring
  calc ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => Y < K), (1 : ℝ) / K
      ≤ ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => a < K ∧ K ≤ 2 ^ I * a), (1 : ℝ) / K :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ i ∈ range I, ∑ K ∈ (roughInterval (p + 1) X).filter
          (fun K => 2 ^ i * a < K ∧ K ≤ 2 * (2 ^ i * a)), (1 : ℝ) / K := sum_filter_dyadic _ _ a I
    _ ≤ ∑ i ∈ range I, (8 / Real.log p + 1715 * r ^ i) := sum_le_sum hblock
    _ = (I : ℝ) * (8 / Real.log p) + 1715 * ∑ i ∈ range I, r ^ i := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ 24 / Real.log 2 + 1715 * (1 / (1 - r)) := by gcongr


/-- Explicit coefficient controlling the prime-peeling shell rate. -/
def explicitRoughShellConstant : ℝ := max 1 (4 * roughShellMassConstant / (1 / 128))

theorem explicitRoughShellConstant_ge_one : 1 ≤ explicitRoughShellConstant := le_max_left _ _

/-- Both shell-rate bounds hold with the same closed-form constant. -/
theorem shellTau_le_explicit : ∀ p X : ℕ, p.Prime → p ≤ X →
    shellTau p X ≤ explicitRoughShellConstant * (Real.log p / (p * Real.log X)) ∧
      shellTau p X ≤ 1 - 1 / (1 + 2 * explicitRoughShellConstant) := by
  let Cs := roughShellMassConstant
  have hCs0 := roughShellMassConstant_nonneg
  have hCs := roughHarmonic_shell_le_explicit
  let cM : ℝ := 1 / 128
  have hcM : 0 < cM := by norm_num [cM]
  have hM : ∀ n : ℕ, 2 ≤ n → cM ≤ RHTower.mertensPrimeProduct n * Real.log n :=
    fun _ hn => mertensPrimeProduct_mul_log_ge_one_div_128 hn
  let C := explicitRoughShellConstant
  intro p X hp hpX
  have hp2 := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hlp : 0 < Real.log p := Real.log_pos hp1
  set F0 := roughHarmonic (p + 1) X
  have hF1 : 1 ≤ F0 := one_le_roughHarmonic _ (by omega)
  have hF0 : 0 < F0 := by linarith
  -- `F_0 ≥ c_M log X/log p`
  have hFlow : cM * Real.log X / Real.log p ≤ F0 := by
    have h1 := mertensPrimeProduct_mul_log_le_roughHarmonic p X
    have h2 := hM p hp2
    have hlog : Real.log X ≤ Real.log (X + 1) := Real.log_le_log (by linarith) (by linarith)
    have hMp := mertensPrimeProduct_pos p
    rw [div_le_iff₀ hlp]
    calc cM * Real.log X ≤ RHTower.mertensPrimeProduct p * Real.log p * Real.log X :=
          mul_le_mul_of_nonneg_right h2 hlX.le
      _ = Real.log X * RHTower.mertensPrimeProduct p * Real.log p := by ring
      _ ≤ Real.log (X + 1) * RHTower.mertensPrimeProduct p * Real.log p := by gcongr
      _ ≤ F0 * Real.log p := mul_le_mul_of_nonneg_right h1 hlp.le
  -- termwise: `p^{−j}(F_0 − F_j)/F_0 ≤ (C_s/F_0) j p^{−j}`
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hterm : ∀ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (1 / (p : ℝ)) ^ j *
      ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0) ≤ Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := by
    intro j hj
    have h := roughHarmonic_sub_level_le hCs hp (mem_filter.mp hj).2
    have hpj : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ j := pow_nonneg hr0 _
    calc (1 / (p : ℝ)) ^ j * ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0)
        ≤ (1 / (p : ℝ)) ^ j * (j * Cs / F0) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hF0.le) hpj
      _ = Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := by ring
  have hsumj : ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (j : ℝ) * (1 / (p : ℝ)) ^ j ≤
      (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 := by
    have hhs := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / (p : ℝ)))
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    exact sum_le_hasSum _ (fun i _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _)) hhs
  have hgeo : (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 ≤ 4 / p := by
    have hp0 : (0 : ℝ) < p := by linarith
    have e : (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 = p / ((p : ℝ) - 1) ^ 2 := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [e, div_le_div_iff₀ (by nlinarith) hp0]
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    nlinarith
  have hτ1 : shellTau p X ≤ Cs / F0 * (4 / p) := by
    calc shellTau p X ≤ ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := sum_le_sum hterm
      _ = Cs / F0 * ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (j : ℝ) * (1 / (p : ℝ)) ^ j := by rw [mul_sum]
      _ ≤ Cs / F0 * (4 / p) :=
          mul_le_mul_of_nonneg_left (hsumj.trans hgeo) (div_nonneg hCs0 hF0.le)
  have hτ2 : shellTau p X ≤ C * (Real.log p / (p * Real.log X)) := by
    have hinv : 1 / F0 ≤ Real.log p / (cM * Real.log X) := by
      rw [div_le_div_iff₀ hF0 (by positivity), one_mul]
      rw [div_le_iff₀ hlp] at hFlow
      linarith
    have hCge : 4 * Cs / cM ≤ C := le_max_right _ _
    calc shellTau p X ≤ Cs / F0 * (4 / p) := hτ1
      _ = 4 * Cs * (1 / F0) / p := by ring
      _ ≤ 4 * Cs * (Real.log p / (cM * Real.log X)) / p := by gcongr
      _ = 4 * Cs / cM * (Real.log p / (p * Real.log X)) := by field_simp
      _ ≤ C * (Real.log p / (p * Real.log X)) := by gcongr
  refine ⟨hτ2, ?_⟩
  -- the uniform bound: `τ ≤ 1 − 1/F_0` and either `log X ≥ 2C` or `F_0 ≤ 1 + 2C`
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hτ3 : shellTau p X ≤ 1 - 1 / F0 := by
    have hterm' : ∀ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (1 / (p : ℝ)) ^ j *
        ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0) ≤
          (1 - 1 / F0) * (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [F0]
      rw [if_neg hj0.ne']
      have hlev : 1 ≤ roughHarmonic (p + 1) (X / p ^ j) :=
        one_le_roughHarmonic _ ((Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr
          (by rw [one_mul]; exact (mem_filter.mp hj).2))
      have : (F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0 ≤ 1 - 1 / F0 := by
        rw [sub_div, div_self hF0.ne']
        exact sub_le_sub_left (div_le_div_of_nonneg_right hlev hF0.le) 1
      calc (1 / (p : ℝ)) ^ j * ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0)
          ≤ (1 / (p : ℝ)) ^ j * (1 - 1 / F0) := mul_le_mul_of_nonneg_left this (pow_nonneg hr0 _)
        _ = (1 - 1 / F0) * (1 / (p : ℝ)) ^ j := by ring
    have hgeom : ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
        (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) ≤ 1 := by
      calc ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
            (if j = 0 then 0 else (1 / (p : ℝ)) ^ j)
          ≤ ∑ j ∈ range (X + 1), (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => by
              split_ifs <;> positivity
        _ = (1 / (p : ℝ)) * ∑ j ∈ range X, (1 / (p : ℝ)) ^ j := by
            rw [Finset.sum_range_succ', if_pos rfl, add_zero, mul_sum]
            exact sum_congr rfl fun j _ => by rw [if_neg (Nat.succ_ne_zero j), pow_succ]; ring
        _ ≤ (1 / (p : ℝ)) * (1 / (1 - 1 / p)) := by
            refine mul_le_mul_of_nonneg_left ?_ hr0
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := X) hr0 hr1
            rwa [← range_eq_Ico, pow_zero] at this
        _ ≤ 1 := by
            have hp0 : (0 : ℝ) < p := by linarith
            have hq : (0 : ℝ) < 1 - 1 / p := by linarith
            rw [mul_one_div, div_le_one hq]
            have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
            rw [div_le_iff₀ hp0]
            have : 1 / (p : ℝ) * p = 1 := by field_simp
            nlinarith
    have hnn : 0 ≤ 1 - 1 / F0 := by
      have : 1 / F0 ≤ 1 := by rw [div_le_one hF0]; exact hF1
      linarith
    calc shellTau p X ≤ ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (1 - 1 / F0) * (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := sum_le_sum hterm'
      _ = (1 - 1 / F0) * ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := by rw [mul_sum]
      _ ≤ (1 - 1 / F0) * 1 := mul_le_mul_of_nonneg_left hgeom hnn
      _ = 1 - 1 / F0 := mul_one _
  have h12 : 1 / (1 + 2 * C) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  by_cases hbig : 2 * C ≤ Real.log X
  · -- `τ ≤ C log p/(p log X) ≤ C/log X ≤ 1/2`
    have hlpp : Real.log p / p ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have : C * (Real.log p / (p * Real.log X)) ≤ 1 / 2 := by
      have e : C * (Real.log p / (p * Real.log X)) = C * (Real.log p / p) / Real.log X := by
        field_simp
      rw [e, div_le_iff₀ hlX]
      nlinarith
    linarith
  · -- `F_0 ≤ 1 + log X < 1 + 2C`
    replace hbig := not_le.mp hbig
    have hFle : F0 ≤ 1 + 2 * C := (roughHarmonic_le_one_add_log _ _).trans (by linarith)
    have : 1 / (1 + 2 * C) ≤ 1 / F0 := one_div_le_one_div_of_le hF0 hFle
    linarith

/-- A uniform variance constant obtained by explicit prime peeling. -/
def explicitRoughConditioningConstant : ℝ :=
  (1 + 4 * explicitRoughShellConstant) *
    Real.exp (3 * ((1 + 1 / (4 * explicitRoughShellConstant)) *
      explicitRoughShellConstant * (4 * explicitRoughShellConstant + 2)))

theorem explicitRoughConditioningConstant_pos : 0 < explicitRoughConditioningConstant := by
  have h := explicitRoughShellConstant_ge_one
  unfold explicitRoughConditioningConstant
  positivity

/-- Horizon-uniform harmonic tensorization with no unspecified constants. -/
theorem rough_harmonicVar_le_glauberForm_explicit : ∀ Q X : ℕ, ∀ f : ℕ → ℝ,
    harmonicVar Q X f ≤ explicitRoughConditioningConstant * glauberForm Q X f := by
  let Cτ := explicitRoughShellConstant
  have hCτ1 := explicitRoughShellConstant_ge_one
  have hCτ0 : 0 < Cτ := zero_lt_one.trans_le hCτ1
  have hτ := shellTau_le_explicit
  set η := 4 * Cτ
  have hη : 0 < η := by positivity
  set δs := (4 * Cτ + 1) / (4 * Cτ + 2)
  set A := (1 + 1 / η) * Cτ * (4 * Cτ + 2)
  have hA : 0 ≤ A := by positivity
  set K := (1 + η) * Real.exp (3 * A)
  have hK : 0 < K := by positivity
  set S : ℕ → ℝ := fun Q => ∑ q ∈ Nat.primesBelow Q, Real.log q / q
  have hS0 : ∀ Q, 0 ≤ S Q := fun Q => sum_nonneg fun q _ => div_nonneg
    (Real.log_natCast_nonneg q) (Nat.cast_nonneg q)
  set Ψ : ℕ → ℕ → ℝ := fun Q X => -A * S Q / Real.log X
  -- the claim, by strong induction on `X + 1 − Q`
  have claim : ∀ k Q X, X + 1 - Q ≤ k → 2 ≤ X → ∀ f : ℕ → ℝ,
      harmonicVar Q X f ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro Q X hk hX f
    have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hRHS : 0 ≤ K * Real.exp (Ψ Q X) * glauberForm Q X f :=
      mul_nonneg (by positivity) (glauberForm_nonneg _ _ _)
    by_cases hQX : X < Q
    · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK hQX)]
      exact hRHS
    rw [not_lt] at hQX
    by_cases hQ : Q.Prime
    · -- peel `p = Q`
      have hp2 := hQ.two_le
      set p := Q
      set Bc := K * Real.exp (-A * S (p + 1) / Real.log X)
      have hBc : 0 ≤ Bc := by positivity
      have hSp : S (p + 1) = S p + Real.log p / p := by
        simp only [S, primesBelow_succ_eq, if_pos hQ]
        rw [sum_insert (fun h => by simp [Nat.primesBelow] at h)]
        ring
      -- the level bound
      have hlev : ∀ j ∈ range (X + 1), harmonicVar (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) ≤
          Bc * glauberForm (p + 1) (X / p ^ j) (fun K => f (p ^ j * K)) := by
        intro j _
        set Y := X / p ^ j
        by_cases hY : Y ≤ p
        · rw [harmonicVar_eq_zero_of_le_one (fun K hK => eq_one_of_mem_roughInterval_of_le hK
            (by omega))]
          exact mul_nonneg hBc (glauberForm_nonneg _ _ _)
        · have hYX : Y ≤ X := Nat.div_le_self _ _
          have hih := ih (Y + 1 - (p + 1)) (by omega) (p + 1) Y le_rfl (by omega)
            (fun K => f (p ^ j * K))
          refine hih.trans (mul_le_mul_of_nonneg_right ?_ (glauberForm_nonneg _ _ _))
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          have hlY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
          have hlYX : Real.log Y ≤ Real.log X :=
            Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hYX)
          simp only [Ψ]
          rw [div_le_div_iff₀ hlY hlX]
          have hmon := mul_nonneg (mul_nonneg hA (hS0 (p + 1))) (sub_nonneg.mpr hlYX)
          nlinarith only [hmon]
      -- the shell rate
      obtain ⟨hτ1, hτ2⟩ := hτ p X hQ hQX
      have hτ0 := shellTau_nonneg p X
      set δ := (1 + 1 / η) * shellTau p X
      have hδ0 : 0 ≤ δ := by positivity
      have hδs : δ ≤ δs := by
        have e : (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) = δs := by
          simp only [δs, η]
          field_simp [hCτ0.ne',
            (by positivity : (1 + 2 * Cτ) ≠ 0),
            (by positivity : (4 * Cτ + 2) ≠ 0)]
          ring
        calc δ ≤ (1 + 1 / η) * (1 - 1 / (1 + 2 * Cτ)) :=
              mul_le_mul_of_nonneg_left hτ2 (by positivity)
          _ = δs := e
      have hδs1 : 1 - δs = 1 / (4 * Cτ + 2) := by
        simp only [δs]
        field_simp [(by positivity : (4 * Cτ + 2) ≠ 0)]
        ring
      have hδ1 : 0 < 1 - δ := by
        have : δs < 1 := by
          have : 0 < 1 / (4 * Cτ + 2) := by positivity
          linarith
        linarith
      have hδA : δ / (1 - δs) ≤ A * (Real.log p / (p * Real.log X)) := by
        rw [hδs1, div_div_eq_mul_div, div_one]
        have h := mul_le_mul_of_nonneg_left hτ1 (show 0 ≤ 1 + 1 / η by positivity)
        have hpos : 0 ≤ Real.log p / (p * Real.log X) := by
          have : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          positivity
        calc δ * (4 * Cτ + 2) ≤ (1 + 1 / η) * (Cτ * (Real.log p / (p * Real.log X))) *
              (4 * Cτ + 2) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = A * (Real.log p / (p * Real.log X)) := by simp only [A]; ring
      -- `B ≥ 1 + η`
      have hBη : 1 + η ≤ Bc := by
        have hm := RHTower.mertens_first_upper (n := p) (by have := hQ.two_le; omega)
        have hSle : S (p + 1) ≤ Real.log p + Real.log 4 := hm
        have hlp : Real.log p ≤ Real.log X :=
          Real.log_le_log (by exact_mod_cast hQ.pos) (by exact_mod_cast hQX)
        have hl2 : Real.log 2 ≤ Real.log X :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hX)
        have hl4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have h3 : S (p + 1) / Real.log X ≤ 3 := by
          rw [div_le_iff₀ hlX]
          linarith only [hSle, hlp, hl4, hl2]
        have : 0 ≤ 3 * A + -A * S (p + 1) / Real.log X := by
          rw [neg_mul, neg_div, mul_div_assoc]
          nlinarith only [mul_nonneg hA (sub_nonneg.mpr h3)]
        calc 1 + η = (1 + η) * 1 := (mul_one _).symm
          _ ≤ (1 + η) * Real.exp (3 * A + -A * S (p + 1) / Real.log X) :=
              mul_le_mul_of_nonneg_left (Real.one_le_exp this) (by positivity)
          _ = Bc := by simp only [Bc, K]; rw [Real.exp_add]; ring
      have hpeel := peel hQ hQX f hη hBc hlev
      rw [max_eq_left hBη] at hpeel
      -- `V ≤ B/(1 − δ) G ≤ B e^{δ/(1−δ*)} G ≤ K e^{Ψ} G`
      have hV : harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδ1]
        linarith
      have hexp : 1 / (1 - δ) ≤ Real.exp (A * (Real.log p / (p * Real.log X))) := by
        have h1 : 1 / (1 - δ) = 1 + δ / (1 - δ) := by field_simp; ring
        have h2 : δ / (1 - δ) ≤ δ / (1 - δs) :=
          div_le_div_of_nonneg_left hδ0 (by
            have : 0 < 1 / (4 * Cτ + 2) := by positivity
            linarith) (by linarith)
        rw [h1]
        linarith [Real.add_one_le_exp (A * (Real.log p / (p * Real.log X)))]
      have hBK : Bc * Real.exp (A * (Real.log p / (p * Real.log X))) = K * Real.exp (Ψ p X) := by
        simp only [Bc, Ψ, mul_assoc, ← Real.exp_add]
        congr 2
        rw [hSp]
        field_simp
        ring
      calc harmonicVar p X f ≤ Bc / (1 - δ) * glauberForm p X f := hV
        _ = Bc * (1 / (1 - δ)) * glauberForm p X f := by ring
        _ ≤ Bc * Real.exp (A * (Real.log p / (p * Real.log X))) * glauberForm p X f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hBc)
              (glauberForm_nonneg _ _ _)
        _ = K * Real.exp (Ψ p X) * glauberForm p X f := by rw [hBK]
    · -- `Q` is not prime: pass to `Q + 1`
      have hR : roughInterval (Q + 1) X = roughInterval Q X := roughInterval_succ_of_not_prime hQ X
      have hP : (Icc (Q + 1) X).filter Nat.Prime = (Icc Q X).filter Nat.Prime := by
        ext q
        simp only [mem_filter, mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases h1.lt_or_eq with h | h
          · exact ⟨⟨h, h2⟩, h3⟩
          · exact absurd (h ▸ h3) hQ
      have hS : S (Q + 1) = S Q := by
        simp only [S, primesBelow_succ_eq, if_neg hQ]
      have hih := ih (X + 1 - (Q + 1)) (by omega) (Q + 1) X le_rfl hX f
      have hG : glauberForm (Q + 1) X f = glauberForm Q X f := by
        rw [glauberForm, glauberForm, hP, hR]
      rw [harmonicVar, ← hR]
      calc wVar (roughInterval (Q + 1) X) (fun n => 1 / (n : ℝ)) f = harmonicVar (Q + 1) X f := rfl
        _ ≤ K * Real.exp (Ψ (Q + 1) X) * glauberForm (Q + 1) X f := hih
        _ = K * Real.exp (Ψ Q X) * glauberForm Q X f := by simp only [Ψ, hS, hG]
  intro Q X f
  change harmonicVar Q X f ≤ K * glauberForm Q X f
  by_cases hX : 2 ≤ X
  · have h := claim (X + 1 - Q) Q X le_rfl hX f
    have hlog : 0 ≤ Real.log X := Real.log_natCast_nonneg X
    have hΨ : Ψ Q X ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (hS0 Q)) hlog
    have hexp : Real.exp (Ψ Q X) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hΨ
    exact h.trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hK.le)
      (glauberForm_nonneg Q X f))
  · rw [harmonicVar_eq_zero_of_le_one fun n hn => by
      have := mem_roughInterval.mp hn; omega]
    exact mul_nonneg hK.le (glauberForm_nonneg _ _ _)

/-- The explicit tensorization constant pays rough variance by the literal prime defect. -/
theorem rough_harmonicVar_le_primeDefect_explicit : ∀ Q : ℕ, 2 ≤ Q → ∀ N : ℕ, ∀ x : ℕ → ℝ,
    harmonicVar Q N (poleGauge x) ≤
      explicitRoughConditioningConstant / Real.log Q * roughPoleDefect Q N x := by
  let C := explicitRoughConditioningConstant
  have hC := explicitRoughConditioningConstant_pos
  have hvar := rough_harmonicVar_le_glauberForm_explicit
  intro Q hQ N x
  have hlog : 0 < Real.log Q :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have henergy := log_mul_glauberForm_le_roughPoleDefect hQ N x
  have hbound : glauberForm Q N (poleGauge x) ≤ roughPoleDefect Q N x / Real.log Q := by
    rw [le_div_iff₀ hlog]
    simpa only [mul_comm] using henergy
  calc harmonicVar Q N (poleGauge x) ≤ C * glauberForm Q N (poleGauge x) := hvar Q N _
    _ ≤ C * (roughPoleDefect Q N x / Real.log Q) := mul_le_mul_of_nonneg_left hbound hC.le
    _ = C / Real.log Q * roughPoleDefect Q N x := by ring

/-- Smooth-part conditioning has explicit error constant at every horizon. -/
theorem smoothRoughPoleProjection_error_le_explicit : ∀ Q : ℕ, 2 ≤ Q → ∀ N : ℕ, ∀ x : ℕ → ℝ,
    (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection Q N x n) ^ 2) ≤
      explicitRoughConditioningConstant / Real.log Q * poleDefect N x := by
  let C := explicitRoughConditioningConstant
  have hrough := rough_harmonicVar_le_primeDefect_explicit
  intro Q hQ N x
  rw [← smoothRoughFibreError_eq_sum_sq]
  unfold smoothRoughFibreError
  calc
    _ ≤ ∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
        (C / Real.log Q * roughPoleDefect Q (N / d)
          (fun k => Real.sqrt d * x (d * k))) := by
      refine sum_le_sum fun d _ => ?_
      have h := hrough Q hQ (N / d) (fun k => Real.sqrt d * x (d * k))
      have heq : poleGauge (fun k => Real.sqrt d * x (d * k)) =
          fun k => poleGauge x (d * k) := funext (poleGauge_smooth_fibre d x)
      rw [heq] at h
      exact mul_le_mul_of_nonneg_left h (div_nonneg zero_le_one (Nat.cast_nonneg d))
    _ = C / Real.log Q * (∑ d ∈ Nat.smoothNumbersUpTo N Q, 1 / (d : ℝ) *
        roughPoleDefect Q (N / d) (fun k => Real.sqrt d * x (d * k))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [sum_smoothRough_roughPoleDefect]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.mertensPrimeProduct_mul_log_ge_one_div_128

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.smoothRoughPoleProjection_error_le_explicit
