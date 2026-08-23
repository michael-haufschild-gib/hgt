import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import GaloisForLFunctions.RHTower.Sieve.GallagherAlmostDiagonal

/-!
# The adaptive Gallagher--Brun--Titchmarsh mean square

Choosing the Selberg sieve level `√H` separately at each prime makes the Brun--Titchmarsh error a
bounded multiple of its main term, so the number of multiplicative neighbours of a prime `p ≥ T²`
inside a window of logarithmic radius `1/T` is `O(p/(T log p))`.  Gallagher's almost-diagonal mean
value theorem then costs only one `log p` per coefficient.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The quartic-in-`u` majorant behind the Brun--Titchmarsh error absorption. -/
theorem cube_mul_le_exp_half {u : ℝ} (hu : 0 ≤ u) :
    6 * (1 + u / 2) ^ 3 * u ≤ 288 * Real.exp (u / 2) := by
  have hu2 : (0 : ℝ) ≤ u / 2 := by linarith
  have h := Real.sum_le_exp_of_nonneg hu2 6
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [h, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, hu]

/-- **The Brun--Titchmarsh error term is a bounded multiple of the main term.**  For every
`H > 1`, `6√H (1 + log √H)³ ≤ 288 H / log H`. -/
theorem bt_error_le_main {H : ℝ} (hH : 1 < H) :
    6 * Real.sqrt H * (1 + Real.log (Real.sqrt H)) ^ 3 ≤ 288 * H / Real.log H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hu : (0 : ℝ) < Real.log H := Real.log_pos hH
  have hs : Real.sqrt H = Real.exp (Real.log H / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hH0]
    congr 1
    ring
  have hls : Real.log (Real.sqrt H) = Real.log H / 2 := by
    rw [hs, Real.log_exp]
  have hstep := cube_mul_le_exp_half (u := Real.log H) hu.le
  rw [← hs] at hstep
  rw [hls]
  rw [le_div_iff₀ hu]
  have hsq : Real.sqrt H * Real.sqrt H = H := Real.mul_self_sqrt hH0.le
  have hspos : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH0
  nlinarith [hstep, hspos, hu, hsq]

/-- **Brun--Titchmarsh in `H/log H` form.**  The sieve level `√H` makes the error term a bounded
multiple of the main term. -/
theorem primesBetween_le_div_log {a H : ℝ} (ha : 0 < a) (hH : 1 < H) :
    (BrunTitchmarsh.primesBetween a (a + H) : ℝ) ≤ 292 * H / Real.log H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hu : (0 : ℝ) < Real.log H := Real.log_pos hH
  have hZ : (1 : ℝ) < Real.sqrt H := by
    have h1 : Real.sqrt 1 < Real.sqrt H := by
      refine Real.sqrt_lt_sqrt (by norm_num) hH
    simpa using h1
  have hbt := BrunTitchmarsh.primesBetween_le a H (Real.sqrt H) ha hH0 hZ
  have hls : Real.log (Real.sqrt H) = Real.log H / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hH0]
    ring
  rw [hls] at hbt
  have hmain : 2 * H / (Real.log H / 2) = 4 * H / Real.log H := by
    field_simp
    ring
  rw [hmain] at hbt
  have herr := bt_error_le_main hH
  rw [hls] at herr
  have hsum : 4 * H / Real.log H + 288 * H / Real.log H = 292 * H / Real.log H := by
    field_simp
    ring
  linarith [hbt, herr, hsum.le, hsum.ge]

theorem exp_le_one_add_two_mul {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    Real.exp δ ≤ 1 + 2 * δ := by
  have h1 : (1 : ℝ) - δ ≤ Real.exp (-δ) := by
    have := Real.add_one_le_exp (-δ)
    linarith
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  have hexp : Real.exp δ * Real.exp (-δ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hE : (0 : ℝ) < Real.exp δ := Real.exp_pos _
  nlinarith [h1, hexp, hE, hpos]

theorem one_sub_le_exp_neg_self {δ : ℝ} : (1 : ℝ) - δ ≤ Real.exp (-δ) := by
  have := Real.add_one_le_exp (-δ)
  linarith

/-- **The adaptive Brun--Titchmarsh neighbour count.**  For a prime-supported index set and a
prime `p ≥ T²`, the number of multiplicative neighbours within `1/T` is `O(p/(T log p))`. -/
theorem logNeighbourCount_le_of_prime {T : ℝ} (hT : 2 ≤ T) {s : Finset ℕ}
    (hs : ∀ m ∈ s, Nat.Prime m) {p : ℕ} (hp : Nat.Prime p) (hpT : T ^ 2 ≤ (p : ℝ)) :
    (logNeighbourCount s (1 / T) p : ℝ) ≤ 1800 * (p : ℝ) / (T * Real.log p) := by
  classical
  set δ : ℝ := 1 / T with hδdef
  have hT0 : (0 : ℝ) < T := by linarith
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hT0 (by norm_num)]
    linarith
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : (0 : ℝ) < Real.log p := Real.log_pos (by linarith)
  have hTle : T ≤ Real.sqrt (p : ℝ) := by
    rw [Real.le_sqrt hT0.le]
    · exact hpT
    · exact le_of_lt (by exact_mod_cast hp0)
  have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hs0 : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  set a : ℝ := (p : ℝ) * (1 - δ) with hadef
  set H : ℝ := 3 * δ * (p : ℝ) with hHdef
  have ha0 : (0 : ℝ) < a := by
    rw [hadef]
    have : (0 : ℝ) < 1 - δ := by linarith
    positivity
  have hHge : 3 * Real.sqrt (p : ℝ) ≤ H := by
    have hkey : Real.sqrt (p : ℝ) ≤ (p : ℝ) / T := by
      rw [le_div_iff₀ hT0]
      nlinarith [hTle, hs0, hsq]
    have hrw : H = 3 * ((p : ℝ) / T) := by
      rw [hHdef, hδdef]; ring
    rw [hrw]
    linarith
  have hH1 : (1 : ℝ) < H := by
    have : (1 : ℝ) < 3 * Real.sqrt (p : ℝ) := by
      have h2 : Real.sqrt 2 ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hpR
      have h3 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  have hlogH : Real.log (p : ℝ) / 2 ≤ Real.log H := by
    have hstep : Real.log (Real.sqrt (p : ℝ)) ≤ Real.log H :=
      Real.log_le_log hs0 (by linarith)
    rwa [Real.sqrt_eq_rpow, Real.log_rpow hp0, show (1 : ℝ) / 2 * Real.log (p : ℝ)
      = Real.log (p : ℝ) / 2 by ring] at hstep
  -- the neighbour set is inside the additive window
  have hsub : s.filter (fun m : ℕ => |Real.log (p : ℝ) - Real.log (m : ℝ)| < δ)
      ⊆ (Finset.Icc ⌈a⌉₊ ⌊a + H⌋₊).filter Nat.Prime := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    obtain ⟨hms, hmlog⟩ := hm
    have hmp := hs m hms
    have hm2 : 2 ≤ m := hmp.two_le
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    rw [abs_lt] at hmlog
    obtain ⟨hlow, hhigh⟩ := hmlog
    have hlogm1 : Real.log (p : ℝ) - δ < Real.log (m : ℝ) := by linarith
    have hlogm2 : Real.log (m : ℝ) < Real.log (p : ℝ) + δ := by linarith
    have hmlow : (p : ℝ) * Real.exp (-δ) < (m : ℝ) := by
      have h := Real.exp_lt_exp.mpr hlogm1
      rw [Real.exp_sub, Real.exp_log hp0, Real.exp_log hm0] at h
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact h
    have hmhigh : (m : ℝ) < (p : ℝ) * Real.exp δ := by
      have h := Real.exp_lt_exp.mpr hlogm2
      rw [Real.exp_add, Real.exp_log hp0, Real.exp_log hm0] at h
      exact h
    have hA : a ≤ (m : ℝ) := by
      have hexpn := one_sub_le_exp_neg_self (δ := δ)
      rw [hadef]
      nlinarith [hmlow, hp0]
    have hB : (m : ℝ) ≤ a + H := by
      have hexpp := exp_le_one_add_two_mul hδ0.le hδhalf
      rw [hadef, hHdef]
      nlinarith [hmhigh, hp0]
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hA, Nat.le_floor hB⟩, hmp⟩
  have hcard : (logNeighbourCount s δ p : ℝ)
      ≤ (BrunTitchmarsh.primesBetween a (a + H) : ℝ) := by
    rw [logNeighbourCount, BrunTitchmarsh.primesBetween]
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans hcard (le_trans (primesBetween_le_div_log ha0 hH1) ?_)
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  rw [div_le_div_iff₀ hlogH0 (by positivity)]
  have hHle : H = 3 * (p : ℝ) / T := by
    rw [hHdef, hδdef]; ring
  rw [hHle] at hlogH ⊢
  have hlhs : 292 * (3 * (p : ℝ) / T) * (T * Real.log p) = 876 * (p : ℝ) * Real.log p := by
    field_simp; ring
  rw [hlhs]
  nlinarith [hlogH, hp0]

/-- **Lemma B: the adaptive Gallagher--Brun--Titchmarsh mean square.**  For a prime-supported
Dirichlet polynomial whose primes all exceed `T²`, the frequency mean square over a window of
length `T` costs only `p/log p` per coefficient — one logarithm, not two. -/
theorem gallagher_bt_mean_square {T : ℝ} (hT : 2 ≤ T) {s : Finset ℕ}
    (hs : ∀ m ∈ s, Nat.Prime m) (hsT : ∀ m ∈ s, T ^ 2 ≤ (m : ℝ)) (b : ℕ → ℂ) :
    (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)), ‖logPoly b s w‖ ^ 2)
      ≤ 2250 * ∑ p ∈ s, (p : ℝ) / Real.log p * ‖b p‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : (0 : ℝ) < 1 / T := by positivity
  have hWδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    have : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) = 1 := by field_simp
    rw [this]
  have hbase := integral_Icc_normSq_logPoly_le_count b s hδ hWδ
  refine le_trans hbase ?_
  have hstep : ∀ p ∈ s, (logNeighbourCount s (1 / T) p : ℝ) * ‖b p‖ ^ 2
      ≤ (1800 * (p : ℝ) / (T * Real.log p)) * ‖b p‖ ^ 2 := by
    intro p hp
    exact mul_le_mul_of_nonneg_right
      (logNeighbourCount_le_of_prime hT hs (hs p hp) (hsT p hp)) (by positivity)
  have hsum := Finset.sum_le_sum hstep
  have hcoef : (0 : ℝ) ≤ 5 / (4 * (1 / T)) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hcoef) ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp2 : 2 ≤ p := (hs p hp).two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hlogp : (0 : ℝ) < Real.log p := Real.log_pos (by linarith)
  have hidem : 5 / (4 * (1 / T)) * (1800 * (p : ℝ) / (T * Real.log p) * ‖b p‖ ^ 2)
      = 2250 * ((p : ℝ) / Real.log p * ‖b p‖ ^ 2) := by
    field_simp
    ring
  rw [hidem]

/-- **Lemma B, equation (B1).**  In the card's coefficient normalization `b_p = a_p log p / p`,
the right-hand side carries exactly one `log p`. -/
theorem gallagher_bt_mean_square_coeff {T : ℝ} (hT : 2 ≤ T) {s : Finset ℕ}
    (hs : ∀ m ∈ s, Nat.Prime m) (hsT : ∀ m ∈ s, T ^ 2 ≤ (m : ℝ)) (a : ℕ → ℂ) :
    (∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
        ‖logPoly (fun p : ℕ => a p * ((Real.log p : ℝ) : ℂ) / (p : ℂ)) s w‖ ^ 2)
      ≤ 2250 * ∑ p ∈ s, ‖a p‖ ^ 2 * Real.log p / (p : ℝ) := by
  refine le_trans (gallagher_bt_mean_square hT hs hsT _) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) (by norm_num)
  have hp2 : 2 ≤ p := (hs p hp).two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : (0 : ℝ) < Real.log p := Real.log_pos (by linarith)
  have hnorm : ‖a p * ((Real.log p : ℝ) : ℂ) / (p : ℂ)‖ ^ 2
      = ‖a p‖ ^ 2 * (Real.log p) ^ 2 / (p : ℝ) ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogp.le, Complex.norm_natCast, div_pow, mul_pow]
  rw [hnorm]
  have hid : (p : ℝ) / Real.log p * (‖a p‖ ^ 2 * Real.log p ^ 2 / (p : ℝ) ^ 2)
      = ‖a p‖ ^ 2 * Real.log p / (p : ℝ) := by
    field_simp
  rw [hid]

end

end RHTower.Sieve