import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.EventuallyRankLeRpowOfLtOneDivFiftytwo
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

/-! The auxiliary primes eventually exceed the polynomial rank threshold. -/

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions WindowedLandauTheory.MainNotions.Inhab WindowedLandauTheory.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.T3.eventually_r_le_rpow_five :
    ∃ x₀ : ℝ, ∀ (s : Scale) (R : Ranks), x₀ ≤ s.x → RankVal s R →
      (R.r : ℝ) ≤ s.x ^ (5 : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 10)).eventually_ge_atTop 4)
  refine ⟨x₀, fun s R hx hR => ?_⟩
  have hx1 := s.one_lt_alt.le
  have hx0 := zero_lt_one.trans_le hx1
  have he := s.eps_lt
  have hmono := Real.rpow_le_rpow_of_exponent_le hx1
    (show 9 / 2 + 10 * s.eps ≤ (47 / 10 : ℝ) by linarith only [he])
  have hrk : R.r ≤ 2 * R.k := by
    have := R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hrk' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast hrk
  obtain ⟨-, -, ⟨-, hk⟩, -⟩ := hR
  have hbound : (R.r : ℝ) ≤ 4 * s.x ^ (47 / 10 : ℝ) := by linarith only [hrk', hk, hmono]
  calc (R.r : ℝ) ≤ 4 * s.x ^ (47 / 10 : ℝ) := hbound
    _ ≤ s.x ^ (3 / 10 : ℝ) * s.x ^ (47 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right (hx₀ s.x hx) (by positivity)
    _ = _ := by rw [← Real.rpow_add hx0]; norm_num

private theorem mul_log_le_rpow_eventually (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ a := by
  have h := (isLittleO_log_rpow_atTop ha).bound (show (0:ℝ) < 1 / C by positivity)
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp h
  refine ⟨max x1 1, fun x hx => ?_⟩
  have hx1' := hx1 x (le_trans (le_max_left _ _) hx)
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hpow : 0 ≤ x ^ a := Real.rpow_nonneg (by linarith) a
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hpow] at hx1'
  calc C * Real.log x ≤ C * (1 / C * x ^ a) := by gcongr
    _ = x ^ a := by field_simp

theorem UpperTheory.T3.qdBig :
    ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (Y : ℝ) (q d : ℕ), s.eps = eps → x0 ≤ s.x →
      RankVal s R → s.J ≤ C0 → PairWin s Y → WinPair eps Y q d → (4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) ∧ 100 ≤ d := by
  intro eps C0 he0 he1
  obtain ⟨xr, hxr⟩ := UpperTheory.T3.eventually_r_le_rpow_five
  obtain ⟨xt, hxt⟩ := UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo eps he0 he1
  let x1 := max xr xt
  have hC1pos : 0 < max C0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨x2, hx2⟩ := mul_log_le_rpow_eventually (eps / 5 / max C0 1) 814 (by positivity) (by norm_num)
  refine ⟨max (max x1 x2) 6, ?_⟩
  intro s R Y q d hs hx hR hJ hP hW
  have hxx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx6 : (6:ℝ) ≤ s.x := le_trans (le_max_right _ _) hx
  have hX0 : 0 < s.x := by linarith
  have hr5 := hxr s R ((le_max_left xr xt).trans hxx1) hR
  have ht401 : (R.t : ℝ) ≤ s.x ^ (401 : ℝ) :=
    (hxt s R hs ((le_max_right xr xt).trans hxx1) hR).trans
      (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by norm_num))
  rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast] at hr5
  rw [show (401:ℝ) = ((401:ℕ):ℝ) by norm_num, Real.rpow_natCast] at ht401
  have hJ1 : s.J ≤ max C0 1 := le_trans hJ (le_max_left _ _)
  have hYlo : s.x ^ (1 / max C0 1) ≤ Y := hP.rpow_inv_le hJ1
  have hYe : s.x ^ (eps / 5 / max C0 1) ≤ Y ^ (eps / 5) := by
    have h : s.x ^ (eps / 5 / max C0 1) = (s.x ^ (1 / max C0 1)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hX0.le]
      congr 1
      field_simp
    rw [h]
    exact Real.rpow_le_rpow (by positivity) hYlo (by positivity)
  have hlogx := hx2 s.x hxx2
  have hq := hW.q_lo
  have hqlog : 407 * Real.log s.x < Real.log q := by linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast hW.q_prime.pos
  have hqbig : s.x ^ (407:ℕ) < (q:ℝ) := by
    rw [← Real.log_lt_log_iff (by positivity) hq0, Real.log_pow]
    push_cast
    linarith
  have ht0 : (0:ℝ) ≤ R.t := by positivity
  have hr0 : (0:ℝ) ≤ R.r := by positivity
  have htr : (R.t:ℝ) * R.r ≤ s.x ^ 401 * s.x ^ 5 := mul_le_mul ht401 hr5 hr0 (by positivity)
  have e1 : s.x ^ 401 * s.x ^ 5 = s.x ^ 406 := by ring
  have e2 : s.x ^ 407 = s.x * s.x ^ 406 := by ring
  have h3 : (216:ℝ) ≤ s.x ^ 406 := by
    have a1 : s.x ^ 3 ≤ s.x ^ 406 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have a2 : (6:ℝ) ^ 3 ≤ s.x ^ 3 := pow_le_pow_left₀ (by norm_num) hx6 3
    norm_num at a2
    linarith
  have h4 : 6 * s.x ^ 406 ≤ s.x * s.x ^ 406 := mul_le_mul_of_nonneg_right hx6 (by positivity)
  have hqR : ((4 * R.t * R.r + 2 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqR' : ((102 : ℕ) : ℝ) < q := by
    push_cast
    nlinarith
  have hqN : 4 * R.t * R.r + 2 < q := by exact_mod_cast hqR
  have hqN' : 102 < q := by exact_mod_cast hqR'
  have hqd : q ≤ d + 1 := Nat.le_of_dvd (Nat.succ_pos _) hW.d_q
  generalize 4 * R.t * R.r = P at *
  omega
