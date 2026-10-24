import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowFrobeniusBound
import GaloisForLFunctions.TransThresholdPairCorrelation.ArchimedeanEndEffectAndSurplusSplitting
import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfSurplus
import GaloisForLFunctions.RHTower.ZetaThreeQuartersReduction

/-!
# The Smooth-Weighted Certificate at Bandwidth `4/3`

Run the rank–trace certificate of `ζ` at bandwidth `λ = 4/3` with grid weights `u_T(τ_k)` from a
window profile of collar `ε₁` (`seamA_weighted`). The weighted trace loses only its collar
(`rtrace_profile_ge`), and the weighted Frobenius norm is the smooth-window form of `ν_X`
(`frobSq_profile_le`), whose channels are the archimedean and prime diagonals, the coalescent
band, and errors of lower order. The diagonals are the unconditional bandwidth-`4/3` core `43/36`.
-/

open MeasureTheory Real Set Finset Filter Topology
open scoped BigOperators ArithmeticFunction

open Zeta23 Zeta23.PrimeSide Zeta23.ThmE Zeta23.Assembly RHTower RHLinalg

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {ε₁ : ℝ} {u : ℝ → ℝ}

/-- The grid weights `u_T(τ_k)` of the bandwidth-`4/3` Gram matrix. -/
def profileGrid (u : ℝ → ℝ) (T : ℝ) : Fin (params43.d T) → ℝ :=
  fun k => profileU u T (params43.tau T k)

theorem abs_profileGrid_le (hu : WindowProfile ε₁ u) (T : ℝ) (k : Fin (params43.d T)) :
    |profileGrid u T k| ≤ 1 := by
  unfold profileGrid profileU
  rw [abs_of_nonneg (hu.nonneg _)]; exact hu.le_one _

/-- The weighted trace as a sum over the grid. -/
theorem rtrace_profile_eq (T : ℝ) :
    rtrace (params43.hat T (wmat (profileGrid u T) (params43.Gp T)))
      = (params43.a T * params43.L T ^ 2)⁻¹
        * ∑ k ∈ Finset.range (params43.toSetting T).d,
            profileW u T ((params43.toSetting T).tau k)
              * GentryA (params43.toSetting T) (params43.localFun T) k k := by
  rw [rtrace_hat_wmat_Gp]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun k => profileW u T ((params43.toSetting T).tau k)
    * GentryA (params43.toSetting T) (params43.localFun T) k k)]
  rfl

/-- The weighted Frobenius norm as a grid-weighted Frobenius sum. -/
theorem frobSq_profile_eq (T : ℝ) :
    frobSq (params43.hat T (wmat (profileGrid u T) (params43.Gp T)))
      = ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2
        * ∑ k : Fin (params43.toSetting T).d, ∑ l : Fin (params43.toSetting T).d,
            gridW (params43.toSetting T) (profileW u T) k * gridW (params43.toSetting T) (profileW u T) l
              * GentryNu (Zeta23.nuX (params43.toSetting T).X) (params43.toSetting T)
                (params43.localFun T) k l ^ 2 := by
  rw [frobSq_hat_wmat_Gp]
  rfl

variable {cϱ : ℝ}

/-- **The weighted trace at one height.** With `C` bounding the archimedean and pole parts of
the diagonal and `0 < B ≤ log 2`,
`tr Ĝ_w ≥ (aL²)⁻¹ (L tr G̃ − (4ε₁T/h + 2) C − 2(L · (1 + 2ℓ₀)L/(2B) · Σ a_n
  + B d Σ_{y_n > L − B} a_n))`. -/
theorem rtrace_profile_ge {T : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hT : 2 ≤ T)
    (hu : WindowProfile ε₁ u) {ℓ₀ : ℝ} (hℓ₀ : 0 ≤ ℓ₀) (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k ∈ Finset.range (params43.toSetting T).d,
      |(∫ r, (params43.localFun T).phiHat r ^ 2 * Zeta23.mu ((params43.toSetting T).tau k + r))
        + ∫ r, (params43.localFun T).phiHat r ^ 2
          * Zeta23.PiX (params43.toSetting T).X ((params43.toSetting T).tau k + r)| ≤ C)
    {B : ℝ} (hB : 0 < B) (hB2 : B ≤ Real.log 2) :
    (params43.a T * params43.L T ^ 2)⁻¹
        * ((params43.toSetting T).L * trGtA (params43.toSetting T) (params43.localFun T)
          - (4 * ε₁ * T / (params43.toSetting T).h + 2) * C
          - 2 * ((params43.toSetting T).L * ((1 + 2 * ℓ₀ / T * T) * (params43.toSetting T).L / (2 * B))
              * ∑ n ∈ primeRange (params43.toSetting T).X, acoef n
            + B * (params43.toSetting T).d
              * ∑ n ∈ (primeRange (params43.toSetting T).X).filter
                  (fun n => (params43.toSetting T).L - B < ycoef n), acoef n))
      ≤ rtrace (params43.hat T (wmat (profileGrid u T) (params43.Gp T))) := by
  set p := params43.toSetting T with hp
  set F := params43.localFun T with hFdef
  have hpT : p.T = T := rfl
  have hT0 : 0 < T := by linarith
  have hL := hF.L_pos
  have hh := h_pos hF
  have hε := hu.pos
  have hε8 := hu.le
  rw [rtrace_profile_eq]
  have hc : 0 < (params43.a T * params43.L T ^ 2)⁻¹ := by
    have ha : 0 < params43.a T :=
      lt_of_lt_of_le (by norm_num : (0:ℝ) < 1 / 2) (hF.b_ge_half.trans hF.b_le_a)
    have : 0 < params43.L T := hL
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  -- the collar form
  set W : ℕ → ℝ := fun k => profileW u T (p.tau k) with hW
  have hWh := heightWeight_profileW hu hlip hT0
  set S := (Finset.range p.d).filter
    (fun k : ℕ => p.tau k ∈ Icc (p.T + 2 * ε₁ * p.T) (2 * p.T - 2 * ε₁ * p.T)) with hS
  have hSW : ∀ k ∈ S, W k = 1 := by
    intro k hk
    rw [Finset.mem_filter] at hk
    simp only [hW, profileW]
    rw [profileU_eq_one hu hT0 (by rw [← hpT]; exact hk.2)]; norm_num
  have htr := sum_weighted_trace_ge hF (by rw [hpT]; exact hT0) (W := W)
    (fun k => hWh.nonneg _) (fun k => hWh.le_one _) S hSW hC0 hC
  have hcard := card_collar_le (p := p) (by rw [hpT]; exact hT0) hL hε.le (by linarith)
  rw [hpT] at hcard
  -- the prime part of the collar
  have hPc := abs_weighted_P_part_le_lipschitz hF (by rw [hpT]; exact hT0.le) (c := fun k => 1 - W k)
    (ℓ := 2 * ℓ₀ / T) (by positivity) hB hB2
    (fun k => by
      have h0 := hWh.nonneg (p.tau k); have h1 := hWh.le_one (p.tau k)
      simp only [hW]; rw [abs_le]; constructor <;> linarith)
    (fun k => by
      have h := hWh.lipschitz (p.tau k) (p.tau ((k + 1 : ℕ) : ℤ))
      have hd : p.tau k - p.tau ((k + 1 : ℕ) : ℤ) = -p.h := by
        unfold Setting.tau; push_cast; ring
      rw [hd, abs_neg, abs_of_pos hh] at h
      show |1 - profileW u T (p.tau ((k + 1 : ℕ) : ℤ)) - (1 - profileW u T (p.tau k))| ≤ _
      rw [show 1 - profileW u T (p.tau ((k + 1 : ℕ) : ℤ)) - (1 - profileW u T (p.tau k))
          = profileW u T (p.tau k) - profileW u T (p.tau ((k + 1 : ℕ) : ℤ)) by ring]
      exact h)
  rw [hpT] at hPc
  -- the unweighted trace
  have hsum : ∑ k ∈ Finset.range p.d, GentryA p F k k = p.L * trGtA p F := by
    unfold trGtA
    rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
    exact (Fin.sum_univ_eq_sum_range (fun k => GentryA p F k k) p.d).symm
  have hcol : ((Finset.range p.d \ S).card : ℝ) * C ≤ (4 * ε₁ * T / p.h + 2) * C :=
    mul_le_mul_of_nonneg_right hcard hC0
  rw [← hsum]
  linarith

/-! ## Rates

All errors are bounded in the scale `v = T^{1/12}` against `lT = log T`. -/

theorem pow_le_pow_of_one_le {x : ℝ} (hx : 1 ≤ x) {a b : ℕ} (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  pow_le_pow_right₀ hx hab

/-- A product bound `x y ≤ X Y` for nonnegative factors. -/
theorem mul_le_mul_of_le_of_le' {x y X Y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxX : x ≤ X) (hyY : y ≤ Y) :
    x * y ≤ X * Y := mul_le_mul hxX hyY hy (hx.trans hxX)

/-- **The channel errors are `O(lT⁶ v¹¹)`.** -/
theorem channelError_le {lT v A E CΦ IΦ S s₀ L M Sh D θ₀ X IP IC KE KC KS KD KP KIC : ℝ} {k : ℕ}
    (hlT : 1 ≤ lT) (hv : 1 ≤ v)
    (hA0 : 0 ≤ A) (hA : A ≤ 3 * v ^ 8) (hE0 : 0 ≤ E) (hE : E ≤ KE * lT)
    (hC0 : 0 ≤ CΦ) (hC : CΦ ≤ KC * lT) (hI0 : 0 ≤ IΦ) (hI : IΦ ≤ 13 * lT)
    (hS0 : 0 ≤ S) (hS : S ≤ v ^ 12) (hs₀ : v ^ 12 ≤ s₀) (hL0 : 0 ≤ L) (hL : L ≤ 2 * lT)
    (hM0 : 0 ≤ M) (hM : M ≤ lT) (hSh0 : 0 ≤ Sh) (hSh : Sh ≤ KS * lT)
    (hsX : Real.sqrt X ≤ v ^ 8) (hIP : IP ≤ KP * lT ^ 3 * v ^ 16)
    (hIC : IC ≤ KIC * lT ^ 5 * v ^ 16)
    (hD : (1 / π) * (L * D) * ((θ₀ ^ k)⁻¹ + 1) * A ^ 2 ≤ KD * lT * v ^ 4)
    (hKE : 0 ≤ KE) (hKC : 0 ≤ KC) (hKS : 0 ≤ KS) (hKP : 0 ≤ KP) (hKIC : 0 ≤ KIC) (hKD : 0 ≤ KD) :
    channelError A E CΦ IΦ S s₀ L M Sh D θ₀ X IP IC k
      ≤ (KE + 3 * KC + 12 * KS + 3 * (13 + KE) + 9 * KC + 6 * Real.sqrt KIC
          + (39 * KS + 3 * KE) + 3 * KC * Real.sqrt KP + KD) * lT ^ 6 * v ^ 11 := by
  have hv0 : 0 < v := by linarith
  have hv12 : 0 < v ^ 12 := by positivity
  have hs₀0 : 0 < s₀ := lt_of_lt_of_le hv12 hs₀
  have hsX0 := Real.sqrt_nonneg X
  -- powers
  have p1 : lT ≤ lT ^ 6 := by simpa using pow_le_pow_of_one_le hlT (a := 1) (b := 6) (by norm_num)
  have p2 : lT ^ 2 ≤ lT ^ 6 := pow_le_pow_of_one_le hlT (by norm_num)
  have p3 : lT ^ 3 ≤ lT ^ 6 := pow_le_pow_of_one_le hlT (by norm_num)
  have q0 : (1:ℝ) ≤ v ^ 11 := one_le_pow₀ hv
  have q4 : v ^ 4 ≤ v ^ 11 := pow_le_pow_of_one_le hv (by norm_num)
  have q8 : v ^ 8 ≤ v ^ 11 := pow_le_pow_of_one_le hv (by norm_num)
  have q10 : v ^ 10 ≤ v ^ 11 := pow_le_pow_of_one_le hv (by norm_num)
  have l6 : 1 ≤ lT ^ 6 := one_le_pow₀ hlT
  -- quotients by `s₀`
  have hdiv : ∀ {x : ℝ}, 0 ≤ x → x / s₀ ≤ x / v ^ 12 := fun hx =>
    div_le_div_of_nonneg_left hx hv12 hs₀
  have hX3 : 3 * Real.sqrt X / s₀ ≤ 3 * v ^ 8 / v ^ 12 :=
    (hdiv (by positivity)).trans (div_le_div_of_nonneg_right (by linarith) hv12.le)
  have hSq : Real.sqrt S ≤ v ^ 6 := by
    rw [show v ^ 12 = (v ^ 6) ^ 2 by ring] at hS
    exact (Real.sqrt_le_sqrt hS).trans (by rw [Real.sqrt_sq (by positivity)])
  have hICq : Real.sqrt IC ≤ Real.sqrt KIC * lT ^ 3 * v ^ 8 := by
    have h1 : IC ≤ (Real.sqrt KIC * lT ^ 3 * v ^ 8) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hKIC]
      have : lT ^ 5 ≤ (lT ^ 3) ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_of_one_le hlT (by norm_num)
      calc IC ≤ KIC * lT ^ 5 * v ^ 16 := hIC
        _ ≤ KIC * (lT ^ 3) ^ 2 * (v ^ 8) ^ 2 := by
            rw [← pow_mul (v) 8 2]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hKIC) (by positivity)
    exact (Real.sqrt_le_sqrt h1).trans (by rw [Real.sqrt_sq (by positivity)])
  have hIPq : Real.sqrt IP ≤ Real.sqrt KP * lT ^ 2 * v ^ 8 := by
    have h1 : IP ≤ (Real.sqrt KP * lT ^ 2 * v ^ 8) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hKP]
      have : lT ^ 3 ≤ (lT ^ 2) ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_of_one_le hlT (by norm_num)
      calc IP ≤ KP * lT ^ 3 * v ^ 16 := hIP
        _ ≤ KP * (lT ^ 2) ^ 2 * (v ^ 8) ^ 2 := by
            rw [← pow_mul (v) 8 2]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hKP) (by positivity)
    exact (Real.sqrt_le_sqrt h1).trans (by rw [Real.sqrt_sq (by positivity)])
  have e12 : v ^ 12 / v ^ 12 = 1 := div_self hv12.ne'
  -- the nine channels
  have c1 : S * M * E / s₀ ≤ KE * lT ^ 2 := by
    calc S * M * E / s₀ ≤ S * M * E / v ^ 12 := hdiv (by positivity)
      _ ≤ v ^ 12 * lT * (KE * lT) / v ^ 12 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_le_of_le' (by positivity) hE0
            (mul_le_mul_of_le_of_le' hS0 hM0 hS hM) hE) hv12.le
      _ = KE * lT ^ 2 := by field_simp
  have c2 : S * M * (3 * Real.sqrt X * CΦ / s₀) ≤ 3 * KC * lT ^ 2 * v ^ 8 := by
    have h : 3 * Real.sqrt X * CΦ / s₀ ≤ 3 * v ^ 8 * (KC * lT) / v ^ 12 :=
      (hdiv (by positivity)).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_le_of_le' (by positivity) hC0 (by linarith) hC) hv12.le)
    calc S * M * (3 * Real.sqrt X * CΦ / s₀) ≤ v ^ 12 * lT * (3 * v ^ 8 * (KC * lT) / v ^ 12) :=
          mul_le_mul_of_le_of_le' (by positivity) (by positivity)
            (mul_le_mul_of_le_of_le' hS0 hM0 hS hM) h
      _ = 3 * KC * lT ^ 2 * v ^ 8 := by field_simp; try ring
  have c3 : 2 * L * A * Sh ≤ 12 * KS * lT ^ 2 * v ^ 8 := by
    calc 2 * L * A * Sh ≤ 2 * (2 * lT) * (3 * v ^ 8) * (KS * lT) :=
          mul_le_mul_of_le_of_le' (by positivity) hSh0
            (mul_le_mul_of_le_of_le' (by positivity) hA0 (by linarith) hA) hSh
      _ = 12 * KS * lT ^ 2 * v ^ 8 := by ring
  have c4 : S * (3 * Real.sqrt X / s₀) * (M * IΦ + E / s₀) ≤ 3 * (13 + KE) * lT ^ 2 * v ^ 8 := by
    have hE' : E / s₀ ≤ KE * lT := by
      refine (div_le_self hE0 ?_).trans hE
      exact (one_le_pow₀ hv).trans hs₀
    have hMI : M * IΦ + E / s₀ ≤ (13 + KE) * lT ^ 2 := by
      have h1 : M * IΦ ≤ lT * (13 * lT) := mul_le_mul_of_le_of_le' hM0 hI0 hM hI
      have hll : lT ≤ lT ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (zero_le_one.trans hlT) hlT
      have h2 : KE * lT ≤ KE * lT ^ 2 := mul_le_mul_of_nonneg_left hll hKE
      have e1 : lT * (13 * lT) = 13 * lT ^ 2 := by ring
      have e2 : (13 + KE) * lT ^ 2 = 13 * lT ^ 2 + KE * lT ^ 2 := by ring
      linarith
    calc S * (3 * Real.sqrt X / s₀) * (M * IΦ + E / s₀)
        ≤ v ^ 12 * (3 * v ^ 8 / v ^ 12) * ((13 + KE) * lT ^ 2) :=
          mul_le_mul_of_le_of_le' (by positivity) (by positivity)
            (mul_le_mul_of_le_of_le' hS0 (by positivity) hS hX3) hMI
      _ = 3 * (13 + KE) * lT ^ 2 * v ^ 8 := by field_simp; try ring
  have c5 : S * (3 * Real.sqrt X / s₀) * (3 * Real.sqrt X * CΦ / s₀) ≤ 9 * KC * lT * v ^ 4 := by
    have h : 3 * Real.sqrt X * CΦ / s₀ ≤ 3 * v ^ 8 * (KC * lT) / v ^ 12 :=
      (hdiv (by positivity)).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_le_of_le' (by positivity) hC0 (by linarith) hC) hv12.le)
    calc S * (3 * Real.sqrt X / s₀) * (3 * Real.sqrt X * CΦ / s₀)
        ≤ v ^ 12 * (3 * v ^ 8 / v ^ 12) * (3 * v ^ 8 * (KC * lT) / v ^ 12) :=
          mul_le_mul_of_le_of_le' (by positivity) (by positivity)
            (mul_le_mul_of_le_of_le' hS0 (by positivity) hS hX3) h
      _ = 9 * KC * lT * v ^ 4 := by field_simp; try ring
  have c6 : 2 * (3 * Real.sqrt X / s₀) * (Real.sqrt S * Real.sqrt IC)
      ≤ 6 * Real.sqrt KIC * lT ^ 3 * v ^ 10 := by
    calc 2 * (3 * Real.sqrt X / s₀) * (Real.sqrt S * Real.sqrt IC)
        ≤ 2 * (3 * v ^ 8 / v ^ 12) * (v ^ 6 * (Real.sqrt KIC * lT ^ 3 * v ^ 8)) :=
          mul_le_mul_of_le_of_le' (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hX3 (by norm_num))
            (mul_le_mul_of_le_of_le' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hSq hICq)
      _ = 6 * Real.sqrt KIC * lT ^ 3 * v ^ 10 := by field_simp; try ring
  have c7 : IΦ * ((1 / π) * A * Sh) + (1 / π) * A * S * E / s₀
      ≤ (39 * KS * lT ^ 2 + 3 * KE * lT) * v ^ 8 := by
    have hπ1 : 1 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
    have h1 : IΦ * ((1 / π) * A * Sh) ≤ 13 * lT * (3 * v ^ 8 * (KS * lT)) := by
      refine mul_le_mul_of_le_of_le' hI0 (by positivity) hI ?_
      calc (1 / π) * A * Sh ≤ 1 * (3 * v ^ 8) * (KS * lT) :=
            mul_le_mul_of_le_of_le' (by positivity) hSh0
              (mul_le_mul_of_le_of_le' (by positivity) hA0 hπ1 hA) hSh
        _ = 3 * v ^ 8 * (KS * lT) := by ring
    have h2 : (1 / π) * A * S * E / s₀ ≤ 3 * v ^ 8 * (KE * lT) := by
      calc (1 / π) * A * S * E / s₀ ≤ (1 / π) * A * S * E / v ^ 12 := hdiv (by positivity)
        _ ≤ 1 * (3 * v ^ 8) * v ^ 12 * (KE * lT) / v ^ 12 := by
            refine div_le_div_of_nonneg_right ?_ hv12.le
            exact mul_le_mul_of_le_of_le' (by positivity) hE0
              (mul_le_mul_of_le_of_le' (by positivity) hS0
                (mul_le_mul_of_le_of_le' (by positivity) hA0 hπ1 hA) hS) hE
        _ = 3 * v ^ 8 * (KE * lT) := by field_simp
    have e1 : 13 * lT * (3 * v ^ 8 * (KS * lT)) = 39 * KS * lT ^ 2 * v ^ 8 := by ring
    have e2 : 3 * v ^ 8 * (KE * lT) = 3 * KE * lT * v ^ 8 := by ring
    have e3 : (39 * KS * lT ^ 2 + 3 * KE * lT) * v ^ 8 = 39 * KS * lT ^ 2 * v ^ 8 + 3 * KE * lT * v ^ 8 := by
      ring
    linarith
  have c8 : 3 * Real.sqrt X * CΦ / s₀ * (Real.sqrt S * Real.sqrt IP)
      ≤ 3 * KC * Real.sqrt KP * lT ^ 3 * v ^ 10 := by
    have h : 3 * Real.sqrt X * CΦ / s₀ ≤ 3 * v ^ 8 * (KC * lT) / v ^ 12 :=
      (hdiv (by positivity)).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_le_of_le' (by positivity) hC0 (by linarith) hC) hv12.le)
    calc 3 * Real.sqrt X * CΦ / s₀ * (Real.sqrt S * Real.sqrt IP)
        ≤ 3 * v ^ 8 * (KC * lT) / v ^ 12 * (v ^ 6 * (Real.sqrt KP * lT ^ 2 * v ^ 8)) :=
          mul_le_mul_of_le_of_le' (by positivity) (by positivity) h
            (mul_le_mul_of_le_of_le' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hSq hIPq)
      _ = 3 * KC * Real.sqrt KP * lT ^ 3 * v ^ 10 := by field_simp; try ring
  -- raise every exponent to `lT⁶ v¹¹`
  have r : ∀ {K : ℝ} {a b : ℕ}, 0 ≤ K → a ≤ 6 → b ≤ 11 → K * lT ^ a * v ^ b ≤ K * lT ^ 6 * v ^ 11 :=
    fun hK ha hb => mul_le_mul_of_le_of_le' (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_one_le hlT ha) hK) (pow_le_pow_of_one_le hv hb)
  have r1 := r (K := KE) (a := 2) (b := 0) hKE (by norm_num) (by norm_num)
  have r2 := r (K := 3 * KC) (a := 2) (b := 8) (by positivity) (by norm_num) (by norm_num)
  have r3 := r (K := 12 * KS) (a := 2) (b := 8) (by positivity) (by norm_num) (by norm_num)
  have r4 := r (K := 3 * (13 + KE)) (a := 2) (b := 8) (by positivity) (by norm_num) (by norm_num)
  have r5 := r (K := 9 * KC) (a := 1) (b := 4) (by positivity) (by norm_num) (by norm_num)
  have r6 := r (K := 6 * Real.sqrt KIC) (a := 3) (b := 10) (by positivity) (by norm_num) (by norm_num)
  have r7a := r (K := 39 * KS) (a := 2) (b := 8) (by positivity) (by norm_num) (by norm_num)
  have r7b := r (K := 3 * KE) (a := 1) (b := 8) (by positivity) (by norm_num) (by norm_num)
  have r8 := r (K := 3 * KC * Real.sqrt KP) (a := 3) (b := 10) (by positivity) (by norm_num)
    (by norm_num)
  have r9 := r (K := KD) (a := 1) (b := 4) hKD (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one, pow_one] at r1 r5 r7b r9
  unfold channelError
  have e : (KE + 3 * KC + 12 * KS + 3 * (13 + KE) + 9 * KC + 6 * Real.sqrt KIC
          + (39 * KS + 3 * KE) + 3 * KC * Real.sqrt KP + KD) * lT ^ 6 * v ^ 11
      = KE * lT ^ 6 * v ^ 11 + 3 * KC * lT ^ 6 * v ^ 11 + 12 * KS * lT ^ 6 * v ^ 11
        + 3 * (13 + KE) * lT ^ 6 * v ^ 11 + 9 * KC * lT ^ 6 * v ^ 11
        + 6 * Real.sqrt KIC * lT ^ 6 * v ^ 11
        + (39 * KS * lT ^ 6 * v ^ 11 + 3 * KE * lT ^ 6 * v ^ 11)
        + 3 * KC * Real.sqrt KP * lT ^ 6 * v ^ 11 + KD * lT ^ 6 * v ^ 11 := by ring
  have e7 : (39 * KS * lT ^ 2 + 3 * KE * lT) * v ^ 8 = 39 * KS * lT ^ 2 * v ^ 8 + 3 * KE * lT * v ^ 8 := by
    ring
  rw [e]
  linarith [c1, c2, c3, c4, c5, c6, c7, c8, hD, r1, r2, r3, r4, r5, r6, r7a, r7b, r8, r9, e7]

/-- The bracket of the first grid comparison is `O(L/v⁶)`. -/
theorem grid_bracket_le {v L sℓ h d T Kℓ : ℝ} (hv : 1 ≤ v) (hL8 : 8 ≤ L) (hsℓ0 : 0 ≤ sℓ)
    (hsℓ : sℓ ≤ Kℓ / v ^ 6) (hh : h = 2 * π / L) (hd0 : 0 ≤ d) (hd : d ≤ L * T / (2 * π))
    (hT : T = v ^ 12) :
    π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2)) + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))
      ≤ π * (42 * Kℓ + 1) * L / v ^ 6 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by rw [hT]; positivity
  have hv6 : (1:ℝ) ≤ v ^ 6 := one_le_pow₀ hv
  have hTv : v ^ 6 ≤ T := by rw [hT]; exact pow_le_pow_of_one_le hv (by norm_num)
  have hinvh : 1 / h = L / (2 * π) := by rw [hh]; field_simp
  have hdT : 32 * d / (9 * T ^ 2) ≤ L / v ^ 6 := by
    have h1 : 32 * d / (9 * T ^ 2) ≤ 32 * (L * T / (2 * π)) / (9 * T ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : 32 * (L * T / (2 * π)) / (9 * T ^ 2) = 16 / (9 * π) * (L / T) := by field_simp; ring
    have h3 : 16 / (9 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h4 : L / T ≤ L / v ^ 6 := div_le_div_of_nonneg_left hL0.le (by positivity) hTv
    rw [h2] at h1
    calc _ ≤ 16 / (9 * π) * (L / T) := h1
      _ ≤ 1 * (L / v ^ 6) := mul_le_mul h3 h4 (by positivity) zero_le_one
      _ = L / v ^ 6 := one_mul _
  have e1 : 40 * π * sℓ / h = 20 * L * sℓ := by
    rw [div_eq_mul_one_div, hinvh]; field_simp; ring
  have e2 : 20 * π / h = 10 * L := by rw [div_eq_mul_one_div, hinvh]; field_simp; ring
  have hL6 : L / v ^ 6 ≤ L := div_le_self hL0.le hv6
  have hb1 : π * (20 * L * sℓ + 32 * d / (9 * T ^ 2)) ≤ π * (20 * L * (Kℓ / v ^ 6) + L / v ^ 6) :=
    mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hsℓ (by positivity)) hdT) hπ.le
  have hb2 : 2 * π * sℓ * (10 * L + 32 * d / (9 * T ^ 2)) ≤ 2 * π * (Kℓ / v ^ 6) * (11 * L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsℓ (by positivity)) (by linarith only [hdT, hL6])
      (by positivity) (mul_nonneg (by positivity) (hsℓ0.trans hsℓ))
  rw [e1, e2]
  have e3 : π * (42 * Kℓ + 1) * L / v ^ 6
      = π * (20 * L * (Kℓ / v ^ 6) + L / v ^ 6) + 2 * π * (Kℓ / v ^ 6) * (11 * L) := by ring
  rw [e3]
  exact add_le_add hb1 hb2

/-- The first grid comparison is `O(L⁵ lT³ v¹⁰)`. -/
theorem grid_first_le {lT v L Ac sℓ h d T Iν Kℓ KI : ℝ} (hv : 1 ≤ v) (hL8 : 8 ≤ L) (hAc0 : 0 ≤ Ac)
    (hAc : Ac ≤ 2 * L) (hsℓ0 : 0 ≤ sℓ) (hsℓ : sℓ ≤ Kℓ / v ^ 6) (hh : h = 2 * π / L) (hd0 : 0 ≤ d)
    (hd : d ≤ L * T / (2 * π)) (hT : T = v ^ 12) (hIν0 : 0 ≤ Iν) (hIν : Iν ≤ KI * lT ^ 3 * v ^ 16) :
    L ^ 2 * Ac ^ 2 * (π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
        + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))) * Iν
      ≤ 4 * π * (42 * Kℓ + 1) * KI * L ^ 5 * lT ^ 3 * v ^ 10 := by
  have hπ := Real.pi_pos
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hh0 : 0 < h := by rw [hh]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  have hAc2 : Ac ^ 2 ≤ 4 * L ^ 2 := by
    have := pow_le_pow_left₀ hAc0 hAc 2
    nlinarith
  have hbr := grid_bracket_le hv hL8 hsℓ0 hsℓ hh hd0 hd hT
  have hbr0 : 0 ≤ π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
      + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2)) := by positivity
  calc L ^ 2 * Ac ^ 2 * (π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
        + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))) * Iν
      ≤ L ^ 2 * (4 * L ^ 2) * (π * (42 * Kℓ + 1) * L / v ^ 6) * (KI * lT ^ 3 * v ^ 16) :=
        mul_le_mul_of_le_of_le' (by positivity) hIν0
          (mul_le_mul_of_le_of_le' (by positivity) hbr0
            (mul_le_mul_of_nonneg_left hAc2 (by positivity)) hbr) hIν
    _ = 4 * π * (42 * Kℓ + 1) * KI * L ^ 5 * lT ^ 3 * v ^ 10 := by field_simp; try ring

/-- The second grid comparison is `O(L⁵ v¹⁰)`. -/
theorem grid_second_le {v L Ac d T R₀ Bc c₁ S KR : ℝ} (hv : 1 ≤ v) (hL8 : 8 ≤ L) (hAc0 : 0 ≤ Ac)
    (hAc : Ac ≤ 2 * L) (hd0 : 0 ≤ d) (hd : d ≤ L * T / (2 * π)) (hT : T = v ^ 12)
    (hR₀0 : 0 ≤ R₀) (hR₀ : R₀ ≤ KR * L / v ^ 18) (hBc0 : 0 ≤ Bc) (hBc : Bc ≤ 5 * v ^ 8)
    (hc₁ : 0 ≤ c₁) (hS0 : 0 ≤ S) (hS : S ≤ v ^ 12) :
    L * R₀ * Bc * (π * Bc + c₁) * (Ac ^ 2 * (d * π) + L * Ac * S)
      ≤ 20 * KR * (5 * π + c₁) * L ^ 5 * v ^ 10 := by
  have hπ := Real.pi_pos
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have hAc2 : Ac ^ 2 ≤ 4 * L ^ 2 := by
    have := pow_le_pow_left₀ hAc0 hAc 2
    nlinarith
  have hsum : Ac ^ 2 * (d * π) + L * Ac * S ≤ 4 * L ^ 3 * v ^ 12 := by
    have h1 : Ac ^ 2 * (d * π) ≤ (4 * L ^ 2) * ((L * T / (2 * π)) * π) :=
      mul_le_mul_of_le_of_le' (by positivity) (by positivity) hAc2
        (mul_le_mul_of_nonneg_right hd hπ.le)
    have e1 : (4 * L ^ 2) * ((L * T / (2 * π)) * π) = 2 * L ^ 3 * v ^ 12 := by
      rw [hT]; field_simp; try ring
    have h2 : L * Ac * S ≤ L * (2 * L) * v ^ 12 :=
      mul_le_mul_of_le_of_le' (by positivity) hS0 (mul_le_mul_of_nonneg_left hAc hL0.le) hS
    have h3 : L * (2 * L) * v ^ 12 ≤ 2 * L ^ 3 * v ^ 12 := by
      have : L ^ 2 ≤ L ^ 3 := pow_le_pow_of_one_le (by linarith) (by norm_num)
      have e : L * (2 * L) * v ^ 12 = 2 * L ^ 2 * v ^ 12 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) (by positivity)
    linarith only [h1, e1, h2, h3]
  have hBB : π * Bc + c₁ ≤ (5 * π + c₁) * v ^ 8 := by
    have hv8 : (1:ℝ) ≤ v ^ 8 := one_le_pow₀ hv
    nlinarith
  have hKR : 0 ≤ KR := by
    have : 0 ≤ KR * L / v ^ 18 := hR₀0.trans hR₀
    have h1 : 0 ≤ KR * L := by
      have := mul_nonneg this (by positivity : (0:ℝ) ≤ v ^ 18)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    exact nonneg_of_mul_nonneg_left h1 hL0
  calc L * R₀ * Bc * (π * Bc + c₁) * (Ac ^ 2 * (d * π) + L * Ac * S)
      ≤ L * (KR * L / v ^ 18) * (5 * v ^ 8) * ((5 * π + c₁) * v ^ 8) * (4 * L ^ 3 * v ^ 12) :=
        mul_le_mul_of_le_of_le' (by positivity) (by positivity)
          (mul_le_mul_of_le_of_le' (by positivity) (by positivity)
            (mul_le_mul_of_le_of_le' (by positivity) hBc0
              (mul_le_mul_of_nonneg_left hR₀ hL0.le) hBc) hBB) hsum
    _ = 20 * KR * (5 * π + c₁) * L ^ 5 * v ^ 10 := by field_simp; try ring

/-- **The grid-comparison errors are `O(lT⁶ v¹¹)`** after the normalisation `(aL²)⁻²`. -/
theorem gridError_le {lT v L Ac sℓ h d T Iν R₀ Bc c₁ S a Kℓ KI KR : ℝ}
    (hlT : 1 ≤ lT) (hv : 1 ≤ v) (hL8 : 8 ≤ L) (hL : L ≤ 2 * lT) (hAc0 : 0 ≤ Ac) (hAc : Ac ≤ 2 * L)
    (hsℓ0 : 0 ≤ sℓ) (hsℓ : sℓ ≤ Kℓ / v ^ 6) (hh : h = 2 * π / L) (hd0 : 0 ≤ d)
    (hd : d ≤ L * T / (2 * π)) (hT : T = v ^ 12) (hIν0 : 0 ≤ Iν) (hIν : Iν ≤ KI * lT ^ 3 * v ^ 16)
    (hR₀0 : 0 ≤ R₀) (hR₀ : R₀ ≤ KR * L / v ^ 18) (hBc0 : 0 ≤ Bc) (hBc : Bc ≤ 5 * v ^ 8)
    (hc₁ : 0 ≤ c₁) (hS0 : 0 ≤ S) (hS : S ≤ v ^ 12) (ha : 1 / 2 ≤ a)
    (hKℓ : 0 ≤ Kℓ) (hKI : 0 ≤ KI) (hKR : 0 ≤ KR) :
    ((a * L ^ 2)⁻¹) ^ 2 * (L ^ 2 * Ac ^ 2 * (π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
        + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))) * Iν
      + L * R₀ * Bc * (π * Bc + c₁) * (Ac ^ 2 * (d * π) + L * Ac * S))
      ≤ (32 * π * (42 * Kℓ + 1) * KI + 160 * KR * (5 * π + c₁)) * lT ^ 6 * v ^ 11 := by
  have hπ := Real.pi_pos
  have hv0 : 0 < v := by linarith only [hv]
  have hL0 : 0 < L := by linarith only [hL8]
  have hh0 : 0 < h := by rw [hh]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  have hG1 := grid_first_le (lT := lT) hv hL8 hAc0 hAc hsℓ0 hsℓ hh hd0 hd hT hIν0 hIν (KI := KI)
  have hG2 := grid_second_le hv hL8 hAc0 hAc hd0 hd hT hR₀0 hR₀ hBc0 hBc hc₁ hS0 hS
  have hnorm : ((a * L ^ 2)⁻¹) ^ 2 ≤ 4 / L ^ 4 := by
    have ha0 : 0 < a := by linarith only [ha]
    have hL4 : 0 < L ^ 4 := by positivity
    have e : ((a * L ^ 2)⁻¹) ^ 2 = 1 / (a ^ 2 * L ^ 4) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hL4]
    have h1 : (1 / 2) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
    have h2 := mul_le_mul_of_nonneg_right h1 hL4.le
    have e2 : (1 / 2 : ℝ) ^ 2 * L ^ 4 = L ^ 4 / 4 := by ring
    linarith only [h2, e2]
  have hG0 : 0 ≤ L ^ 2 * Ac ^ 2 * (π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
        + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))) * Iν
      + L * R₀ * Bc * (π * Bc + c₁) * (Ac ^ 2 * (d * π) + L * Ac * S) := by
    positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 4 * π * (42 * Kℓ + 1) * KI * lT ^ 3 * v ^ 10
      + 20 * KR * (5 * π + c₁) * v ^ 10 := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by
    have h1 : 0 ≤ 42 * Kℓ + 1 := by linarith only [hKℓ]
    have h2 : 0 ≤ 5 * π + c₁ := by linarith only [hc₁, hπ]
    have hl3 : 0 ≤ lT ^ 3 := pow_nonneg (by linarith only [hlT]) 3
    have hv10 : 0 ≤ v ^ 10 := pow_nonneg hv0.le 10
    rw [hQ]
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h1) hKI) hl3) hv10)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKR) h2) hv10)
  have hGQ : L ^ 2 * Ac ^ 2 * (π * (40 * π * sℓ / h + 32 * d / (9 * T ^ 2))
        + 2 * π * sℓ * (20 * π / h + 32 * d / (9 * T ^ 2))) * Iν
      + L * R₀ * Bc * (π * Bc + c₁) * (Ac ^ 2 * (d * π) + L * Ac * S) ≤ L ^ 5 * Q := by
    have e : L ^ 5 * Q = 4 * π * (42 * Kℓ + 1) * KI * L ^ 5 * lT ^ 3 * v ^ 10
        + 20 * KR * (5 * π + c₁) * L ^ 5 * v ^ 10 := by rw [hQ]; ring
    rw [e]; linarith only [hG1, hG2]
  have h1 := mul_le_mul_of_le_of_le' (by positivity) hG0 hnorm hGQ
  have e1 : 4 / L ^ 4 * (L ^ 5 * Q) = 4 * L * Q := by
    have : L ^ 4 ≠ 0 := by positivity
    field_simp
  have h2 : 4 * L * Q ≤ 8 * lT * Q :=
    mul_le_mul_of_nonneg_right (by linarith only [hL]) hQ0
  have hfin : 8 * lT * Q ≤ (32 * π * (42 * Kℓ + 1) * KI + 160 * KR * (5 * π + c₁)) * lT ^ 6 * v ^ 11 := by
    have p4 : lT ^ 4 ≤ lT ^ 6 := pow_le_pow_of_one_le hlT (by norm_num)
    have p1 : lT ≤ lT ^ 6 := by simpa using pow_le_pow_of_one_le hlT (a := 1) (b := 6) (by norm_num)
    have q : v ^ 10 ≤ v ^ 11 := pow_le_pow_of_one_le hv (by norm_num)
    have hA0 : 0 ≤ 32 * π * (42 * Kℓ + 1) * KI := by
      have : 0 ≤ 42 * Kℓ + 1 := by linarith only [hKℓ]
      positivity
    have hB0 : 0 ≤ 160 * KR * (5 * π + c₁) := by
      have : 0 ≤ 5 * π + c₁ := by linarith only [hc₁, hπ]
      positivity
    have e2 : 8 * lT * Q = (32 * π * (42 * Kℓ + 1) * KI) * lT ^ 4 * v ^ 10
        + (160 * KR * (5 * π + c₁)) * lT * v ^ 10 := by rw [hQ]; ring
    have f1 : (32 * π * (42 * Kℓ + 1) * KI) * lT ^ 4 * v ^ 10
        ≤ (32 * π * (42 * Kℓ + 1) * KI) * lT ^ 6 * v ^ 11 :=
      mul_le_mul_of_le_of_le' (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left p4 hA0) q
    have f2 : (160 * KR * (5 * π + c₁)) * lT * v ^ 10 ≤ (160 * KR * (5 * π + c₁)) * lT ^ 6 * v ^ 11 :=
      mul_le_mul_of_le_of_le' (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left p1 hB0) q
    rw [e2, add_mul, add_mul]
    linarith only [f1, f2]
  linarith only [h1, e1, h2, hfin]

/-- **The alias band carries few primes.** For `0 < B ≤ log 2` and `X ≥ 1`:
`Σ_{n ≤ X, log n > log X − B} a_n ≤ √2 log X (B X + 2)/√X`. -/
theorem sum_acoef_alias_le {X B : ℝ} (hX : 1 ≤ X) (hB : 0 < B) (hB2 : B ≤ Real.log 2) :
    ∑ n ∈ (primeRange X).filter (fun n => Real.log X - B < ycoef n), acoef n
      ≤ Real.sqrt 2 * Real.log X * (B * X + 2) / Real.sqrt X := by
  have hX0 : 0 < X := by linarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have heB : X / 2 ≤ X * Real.exp (-B) := by
    have : Real.exp (-Real.log 2) ≤ Real.exp (-B) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
    nlinarith
  -- each term is at most `√2 log X / √X`
  have hterm : ∀ n ∈ (primeRange X).filter (fun n => Real.log X - B < ycoef n),
      acoef n ≤ Real.sqrt 2 * Real.log X / Real.sqrt X := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hn1 := one_le_of_mem_primeRange hn.1
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hlt : X * Real.exp (-B) < n := by
      have h := hn.2
      unfold ycoef at h
      have := Real.exp_lt_exp.mpr h
      rw [Real.exp_log hn0, Real.exp_sub, Real.exp_log hX0, div_eq_mul_inv, ← Real.exp_neg] at this
      exact this
    have hsn : Real.sqrt X / Real.sqrt 2 ≤ Real.sqrt n := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num)), ← Real.sqrt_mul hn0.le]
      exact Real.sqrt_le_sqrt (by linarith)
    refine (acoef_le_log_div_sqrt hX hn.1).trans ?_
    calc Real.log X / Real.sqrt n ≤ Real.log X / (Real.sqrt X / Real.sqrt 2) :=
          div_le_div_of_nonneg_left hlogX (by positivity) hsn
      _ = Real.sqrt 2 * Real.log X / Real.sqrt X := by field_simp
  -- and there are at most `BX + 2` of them
  have hsub : (primeRange X).filter (fun n => Real.log X - B < ycoef n)
      ⊆ (primeRange X).filter (fun m : ℕ => X * Real.exp (-B) < m ∧ (m : ℝ) < X + 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_, ?_⟩
    · have hn0 : (0:ℝ) < n := by exact_mod_cast one_le_of_mem_primeRange hn.1
      have h := hn.2
      unfold ycoef at h
      have := Real.exp_lt_exp.mpr h
      rw [Real.exp_log hn0, Real.exp_sub, Real.exp_log hX0, div_eq_mul_inv, ← Real.exp_neg] at this
      exact this
    · have := (Finset.mem_Ioc.mp hn.1).2
      have h2 : (n : ℝ) ≤ X := (Nat.cast_le.mpr this).trans (Nat.floor_le hX0.le)
      linarith
  have hcard := card_filter_Ioo_le (primeRange X) (A := X * Real.exp (-B)) (B := X + 1)
    (by positivity) (by nlinarith [Real.exp_le_one_iff.mpr (by linarith : -B ≤ 0)])
  have hexp : X + 1 - X * Real.exp (-B) + 1 ≤ B * X + 2 := by
    have := Real.add_one_le_exp (-B)
    nlinarith
  calc ∑ n ∈ (primeRange X).filter (fun n => Real.log X - B < ycoef n), acoef n
      ≤ ∑ _n ∈ (primeRange X).filter (fun n => Real.log X - B < ycoef n),
          Real.sqrt 2 * Real.log X / Real.sqrt X := Finset.sum_le_sum hterm
    _ = ((primeRange X).filter (fun n => Real.log X - B < ycoef n)).card
          * (Real.sqrt 2 * Real.log X / Real.sqrt X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (B * X + 2) * (Real.sqrt 2 * Real.log X / Real.sqrt X) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 : (((primeRange X).filter (fun n => Real.log X - B < ycoef n)).card : ℝ)
            ≤ (((primeRange X).filter (fun m : ℕ => X * Real.exp (-B) < m ∧ (m : ℝ) < X + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        linarith
    _ = Real.sqrt 2 * Real.log X * (B * X + 2) / Real.sqrt X := by ring

/-- **The collar of the trace.** With `C = 2πaLl + C_r`, the collar costs exactly `4ε₁Tl` plus
`(aL²)⁻¹((4ε₁T/h) C_r + 2C)`. -/
theorem collar_split {a L l T ε₁ Cr : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (a * L ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / L) + 2) * (2 * π * a * L * l + Cr))
      = 4 * ε₁ * T * l + (a * L ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / L)) * Cr
        + 2 * (2 * π * a * L * l + Cr)) := by
  field_simp
  ring

/-- **The prime part of the collar is `O(T)`.** For `B = v⁻⁴`, `T = v¹²`, `1 ≤ √X ≤ v⁸`,
`A ≤ 3√X` and `a ≥ 1/2`: the collar prime error is at most `(6(1 + 2ℓ₀) + 4) T`. -/
theorem primeCollar_le {a L ℓ₀ A Aal d T X v : ℝ} (ha : 1 / 2 ≤ a) (hL : 8 ≤ L) (hℓ₀ : 0 ≤ ℓ₀)
    (hA : A ≤ 3 * Real.sqrt X) (hAal0 : 0 ≤ Aal)
    (hAal : Aal ≤ Real.sqrt 2 * L * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X) (hd0 : 0 ≤ d)
    (hd : d ≤ L * T / (2 * π)) (hv : 1 ≤ v) (hT : T = v ^ 12) (hX1 : 1 ≤ Real.sqrt X)
    (hsX : Real.sqrt X ≤ v ^ 8) :
    (a * L ^ 2)⁻¹ * (2 * (L * ((1 + 2 * ℓ₀ / T * T) * L / (2 * v⁻¹ ^ 4)) * A + v⁻¹ ^ 4 * d * Aal))
      ≤ (6 * (1 + 2 * ℓ₀) + 4) * T := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hv0 : 0 < v := by linarith
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < a := by linarith
  have hT0 : 0 < T := by rw [hT]; positivity
  have hsX0 : 0 < Real.sqrt X := by linarith
  have hX0 : 0 ≤ X := by
    by_contra h; push Not at h; rw [Real.sqrt_eq_zero'.mpr h.le] at hX1; norm_num at hX1
  have hXs : X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
  have e1 : 1 + 2 * ℓ₀ / T * T = 1 + 2 * ℓ₀ := by field_simp
  rw [e1]
  have hv4 : v⁻¹ ^ 4 * v ^ 4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hv0.ne', one_pow]
  -- the first piece: `(aL²)⁻¹ · 2 L (1 + 2ℓ₀) L A v⁴/2 ≤ 6(1 + 2ℓ₀) T`
  have h1 : (a * L ^ 2)⁻¹ * (2 * (L * ((1 + 2 * ℓ₀) * L / (2 * v⁻¹ ^ 4)) * A))
      = (1 + 2 * ℓ₀) * A * v ^ 4 / a := by
    rw [inv_pow]
    field_simp
  have h1' : (1 + 2 * ℓ₀) * A * v ^ 4 / a ≤ 6 * (1 + 2 * ℓ₀) * T := by
    rw [div_le_iff₀ ha0]
    have hA' : A ≤ 3 * v ^ 8 := hA.trans (by linarith)
    have e : T = v ^ 8 * v ^ 4 := by rw [hT]; ring
    have hc : 0 ≤ 1 + 2 * ℓ₀ := by positivity
    calc (1 + 2 * ℓ₀) * A * v ^ 4 ≤ (1 + 2 * ℓ₀) * (3 * v ^ 8) * v ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA' hc) (by positivity)
      _ = 3 * (1 + 2 * ℓ₀) * T := by rw [e]; ring
      _ ≤ 6 * (1 + 2 * ℓ₀) * T * a := by
          have := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ 6 * (1 + 2 * ℓ₀) * T)
          linarith
  -- the second piece: the alias band
  have h2 : (a * L ^ 2)⁻¹ * (2 * (v⁻¹ ^ 4 * d * Aal)) ≤ 4 * T := by
    have hq : (a * L ^ 2)⁻¹ ≤ 2 / L ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      rw [div_le_iff₀ (by norm_num)]
      nlinarith [sq_nonneg L]
    have hvi : 0 ≤ v⁻¹ ^ 4 := by positivity
    have hvi1 : v⁻¹ ^ 4 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hv)
    have hb : v⁻¹ ^ 4 * d * Aal ≤ v⁻¹ ^ 4 * (L * T / (2 * π))
        * (Real.sqrt 2 * L * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd hvi) hAal hAal0 (by positivity)
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hinner : v⁻¹ ^ 4 * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X ≤ 3 := by
      rw [div_le_iff₀ hsX0]
      have hXv : v⁻¹ ^ 4 * v⁻¹ ^ 4 * X ≤ Real.sqrt X := by
        have h8 : v⁻¹ ^ 4 * v⁻¹ ^ 4 * v ^ 8 = 1 := by
          rw [inv_pow]; field_simp
        have hle : v⁻¹ ^ 4 * v⁻¹ ^ 4 * Real.sqrt X ≤ 1 := by
          calc v⁻¹ ^ 4 * v⁻¹ ^ 4 * Real.sqrt X ≤ v⁻¹ ^ 4 * v⁻¹ ^ 4 * v ^ 8 :=
                mul_le_mul_of_nonneg_left hsX (by positivity)
            _ = 1 := h8
        have e2 : v⁻¹ ^ 4 * v⁻¹ ^ 4 * X = (v⁻¹ ^ 4 * v⁻¹ ^ 4 * Real.sqrt X) * Real.sqrt X := by
          rw [mul_assoc (v⁻¹ ^ 4 * v⁻¹ ^ 4), Real.mul_self_sqrt hX0]
        rw [e2]
        calc (v⁻¹ ^ 4 * v⁻¹ ^ 4 * Real.sqrt X) * Real.sqrt X ≤ 1 * Real.sqrt X :=
              mul_le_mul_of_nonneg_right hle hsX0.le
          _ = Real.sqrt X := one_mul _
      have h2' : 2 * v⁻¹ ^ 4 ≤ 2 * Real.sqrt X := by linarith
      have e3 : v⁻¹ ^ 4 * (v⁻¹ ^ 4 * X + 2) = v⁻¹ ^ 4 * v⁻¹ ^ 4 * X + 2 * v⁻¹ ^ 4 := by ring
      rw [e3]
      linarith
    calc (a * L ^ 2)⁻¹ * (2 * (v⁻¹ ^ 4 * d * Aal))
        ≤ 2 / L ^ 2 * (2 * (v⁻¹ ^ 4 * (L * T / (2 * π))
          * (Real.sqrt 2 * L * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X))) :=
          mul_le_mul hq (by linarith) (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 / π * T * (v⁻¹ ^ 4 * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X) := by
          field_simp
      _ ≤ 4 / 3 * T * 3 := by
          have hc : 2 * Real.sqrt 2 / π ≤ 4 / 3 := by
            rw [div_le_div_iff₀ hπ (by norm_num)]; nlinarith
          have hin0 : 0 ≤ v⁻¹ ^ 4 * (v⁻¹ ^ 4 * X + 2) / Real.sqrt X := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_right hc hT0.le) hinner hin0 (by positivity)
      _ = 4 * T := by ring
  have esplit : (a * L ^ 2)⁻¹ * (2 * (L * ((1 + 2 * ℓ₀) * L / (2 * v⁻¹ ^ 4)) * A + v⁻¹ ^ 4 * d * Aal))
      = (a * L ^ 2)⁻¹ * (2 * (L * ((1 + 2 * ℓ₀) * L / (2 * v⁻¹ ^ 4)) * A))
        + (a * L ^ 2)⁻¹ * (2 * (v⁻¹ ^ 4 * d * Aal)) := by ring
  rw [esplit, h1]
  linarith

/-! ## Instantiation at one height -/

/-- The window is dominated by five times the window Lorentz weight. -/
theorem integral_profileΩ_mul_le (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hfc : Continuous f) (hf0 : ∀ τ, 0 ≤ f τ) (hfi : Integrable fun τ => lorentzW T (3 * T / 2) τ * f τ) :
    ∫ τ, profileΩ u T τ * f τ ≤ 5 * ∫ τ, lorentzW T (3 * T / 2) τ * f τ := by
  have hε := hu.pos
  have hε8 := hu.le
  have hΩS : ∀ τ, τ ∉ Icc (T + ε₁ * T) (2 * T - ε₁ * T) → profileΩ u T τ = 0 := fun τ hτ => by
    unfold profileΩ; rw [profileU_eq_zero hu hT hτ]; norm_num
  have hΩc : Continuous (profileΩ u T) := (contDiff_profileΩ hu T 0).continuous
  have hI1 : Integrable fun τ => profileΩ u T τ * f τ := integrable_window_mul hΩc hΩS hfc
  rw [← integral_const_mul]
  refine integral_mono hI1 (hfi.const_mul 5) fun τ => ?_
  by_cases hτ : τ ∈ Icc (T + ε₁ * T) (2 * T - ε₁ * T)
  · have hW : 1 / 5 ≤ lorentzW T (3 * T / 2) τ := lorentzW_ge_fifth hT (by
      rw [abs_le]; constructor <;> nlinarith [hτ.1, hτ.2])
    have hΩ1 : profileΩ u T τ ≤ 1 := by
      unfold profileΩ; exact pow_le_one₀ (hu.nonneg _) (hu.le_one _)
    simp only
    nlinarith [hf0 τ, mul_le_mul_of_nonneg_right hΩ1 (hf0 τ), mul_le_mul_of_nonneg_right hW (hf0 τ)]
  · simp only [hΩS τ hτ, zero_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg (lorentzW_nonneg _ _ _) (hf0 τ))

/-- `Σ_{n≤X} Λ(n)/n ≤ (log²X/2 + C log X)/log 2` from the second Chebyshev–Mertens moment. -/
theorem sum_vonMangoldt_div_le {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
      ≤ C * Real.log x) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ primeRange X, (Λ n : ℝ) / n ≤ (Real.log X ^ 2 / 2 + C * Real.log X) / Real.log 2 := by
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [le_div_iff₀ hl2, Finset.sum_mul]
  have hterm : ∀ n ∈ primeRange X, (Λ n : ℝ) / n * Real.log 2 ≤ (Λ n : ℝ) ^ 2 / n := by
    intro n _
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hΛ0 : (0:ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    rcases eq_or_ne (Λ n) 0 with h0 | h0
    · simp [h0]
    · have hge : Real.log 2 ≤ (Λ n : ℝ) := by
        have hpow := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
        obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
        rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
      calc (Λ n : ℝ) / n * Real.log 2 ≤ (Λ n : ℝ) / n * Λ n :=
            mul_le_mul_of_nonneg_left hge (div_nonneg hΛ0 hn)
        _ = (Λ n : ℝ) ^ 2 / n := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have h := (abs_le.mp (hC X hX)).2
  unfold primeRange
  linarith

/-- The derivative mass of the window on an interval. -/
theorem integral_iteratedDeriv_profileΩ_le (hu : WindowProfile ε₁ u) {T : ℝ} (hT : 0 < T) (k : ℕ)
    {M : ℝ} (hM : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ M) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, |iteratedDeriv k (profileΩ u T) τ| ≤ (b - a) * (M * (T⁻¹) ^ k) := by
  have hc : Continuous (iteratedDeriv k (profileΩ u T)) :=
    (contDiff_profileΩ hu T k).continuous_iteratedDeriv k le_rfl
  calc ∫ τ in a..b, |iteratedDeriv k (profileΩ u T) τ| ≤ ∫ _τ in a..b, M * (T⁻¹) ^ k :=
        intervalIntegral.integral_mono_on hab (hc.abs.intervalIntegrable a b) intervalIntegrable_const
          fun τ _ => abs_iteratedDeriv_profileΩ_le hu hT k hM τ
    _ = (b - a) * (M * (T⁻¹) ^ k) := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- **Far pairs and sum frequencies.** With `θ₀ = T^{−1+η}`, `ηk ≥ 2`, `k ≥ 2` and
`D ≤ 2T M_k T^{−k}`: `π⁻¹ L D (θ₀^{−k} + 1) A² ≤ 24 M_k lT v⁴`. -/
theorem farPair_le {T v L lT D A X Mk η : ℝ} {k : ℕ} (hv : 1 ≤ v) (hT : T = v ^ 12) (hlT : 0 ≤ lT)
    (hL : L ≤ 2 * lT) (hD0 : 0 ≤ D) (hD : D ≤ 2 * T * (Mk * (T⁻¹) ^ k))
    (hMk : 0 ≤ Mk) (hk : 2 ≤ k) (hηk : 2 ≤ η * k) (hA2 : A ^ 2 ≤ 9 * X)
    (hX : X ≤ v ^ 16) :
    (1 / π) * (L * D) * (((T ^ (-1 + η)) ^ k)⁻¹ + 1) * A ^ 2 ≤ 24 * Mk * lT * v ^ 4 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hv0 : 0 < v := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ hv
  have hT0 : 0 < T := by linarith
  have e1 : ((T ^ (-1 + η)) ^ k)⁻¹ = T ^ ((1 - η) * k) := by
    rw [← Real.rpow_mul_natCast hT0.le, ← Real.rpow_neg hT0.le]; ring_nf
  have e2 : (T⁻¹) ^ k = T ^ (-(k : ℝ)) := by rw [Real.rpow_neg hT0.le, Real.rpow_natCast, inv_pow]
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have key1 : T * (T⁻¹) ^ k * T ^ ((1 - η) * k) ≤ T⁻¹ := by
    rw [e2]
    calc T * T ^ (-(k : ℝ)) * T ^ ((1 - η) * k) = T ^ ((1:ℝ) + -(k : ℝ) + (1 - η) * k) := by
          rw [Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
      _ = T⁻¹ := Real.rpow_neg_one T
  have key2 : T * (T⁻¹) ^ k ≤ T⁻¹ := by
    rw [e2]
    calc T * T ^ (-(k : ℝ)) = T ^ ((1:ℝ) + -(k : ℝ)) := by rw [Real.rpow_add hT0, Real.rpow_one]
      _ ≤ T ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = T⁻¹ := Real.rpow_neg_one T
  have hθ : D * (((T ^ (-1 + η)) ^ k)⁻¹ + 1) ≤ 4 * Mk * T⁻¹ := by
    rw [e1]
    have h0 : 0 ≤ T ^ ((1 - η) * k) + 1 := by positivity
    calc D * (T ^ ((1 - η) * k) + 1) ≤ 2 * T * (Mk * (T⁻¹) ^ k) * (T ^ ((1 - η) * k) + 1) :=
          mul_le_mul_of_nonneg_right hD h0
      _ = 2 * Mk * (T * (T⁻¹) ^ k * T ^ ((1 - η) * k) + T * (T⁻¹) ^ k) := by ring
      _ ≤ 2 * Mk * (T⁻¹ + T⁻¹) := mul_le_mul_of_nonneg_left (add_le_add key1 key2) (by positivity)
      _ = 4 * Mk * T⁻¹ := by ring
  have hXT : X * T⁻¹ ≤ v ^ 4 := by
    rw [hT, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc X ≤ v ^ 16 := hX
      _ = v ^ 4 * v ^ 12 := by ring
  have hθ0 : 0 ≤ D * (((T ^ (-1 + η)) ^ k)⁻¹ + 1) := by
    rw [e1]; positivity
  calc (1 / π) * (L * D) * (((T ^ (-1 + η)) ^ k)⁻¹ + 1) * A ^ 2
      = (1 / π) * L * (D * (((T ^ (-1 + η)) ^ k)⁻¹ + 1)) * A ^ 2 := by ring
    _ ≤ (1 / π) * (2 * lT) * (4 * Mk * T⁻¹) * (9 * X) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hθ hθ0
          (by positivity)) hA2 (sq_nonneg _) (by positivity)
    _ = 72 / π * Mk * lT * (X * T⁻¹) := by ring
    _ ≤ 72 / π * Mk * lT * v ^ 4 := mul_le_mul_of_nonneg_left hXT (by positivity)
    _ ≤ 24 * Mk * lT * v ^ 4 := by
        have h1 : 72 / π ≤ 24 := by rw [div_le_iff₀ hπ]; linarith
        have h2 : 0 ≤ Mk * lT * v ^ 4 := by positivity
        nlinarith

/-- **Rates for the Lorentz mean values.** `I ≤ K L^j (3ψ + T S)` with `ψ ≤ C_ψ X`,
`S ≤ (L²/2 + C₁L)/log 2` gives `I ≤ 2^j K (3C_ψ + (2 + 2C₁)/log 2) lT^{j+2} v¹⁶`. -/
theorem meanSquare_rate {I L T X ψ S lT v Cψ C1 K : ℝ} {j : ℕ} (hI : I ≤ K * L ^ j * (3 * ψ + T * S))
    (hK : 0 ≤ K) (hψ : ψ ≤ Cψ * X) (hS : S ≤ (L ^ 2 / 2 + C1 * L) / Real.log 2)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 * lT) (hlT : 1 ≤ lT) (hX : X ≤ v ^ 16) (hT0 : 0 ≤ T)
    (hT : T ≤ v ^ 16) (hCψ : 0 ≤ Cψ) (hC1 : 0 ≤ C1) :
    I ≤ 2 ^ j * K * (3 * Cψ + (2 + 2 * C1) / Real.log 2) * lT ^ (j + 2) * v ^ 16 := by
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hv16 : 0 ≤ v ^ 16 := hT0.trans hT
  have hlT0 : 0 ≤ lT := by linarith
  have hLj : L ^ j ≤ 2 ^ j * lT ^ j := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hL0 hL j
  have hS' : S ≤ (2 + 2 * C1) / Real.log 2 * lT ^ 2 := by
    refine hS.trans ?_
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hl2.le
    have h1 : L ^ 2 ≤ 4 * lT ^ 2 := by
      have := pow_le_pow_left₀ hL0 hL 2
      nlinarith
    have hll : lT ≤ lT ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hlT0 hlT
    have h2 : C1 * L ≤ 2 * C1 * lT ^ 2 := by
      calc C1 * L ≤ C1 * (2 * lT) := mul_le_mul_of_nonneg_left hL hC1
        _ = 2 * C1 * lT := by ring
        _ ≤ 2 * C1 * lT ^ 2 := mul_le_mul_of_nonneg_left hll (by positivity)
    have e : (2 + 2 * C1) * lT ^ 2 = 2 * lT ^ 2 + 2 * C1 * lT ^ 2 := by ring
    linarith
  have hbr : 3 * ψ + T * S ≤ (3 * Cψ + (2 + 2 * C1) / Real.log 2) * lT ^ 2 * v ^ 16 := by
    have h1 : 3 * ψ ≤ 3 * Cψ * lT ^ 2 * v ^ 16 := by
      have : Cψ * X ≤ Cψ * v ^ 16 := mul_le_mul_of_nonneg_left hX hCψ
      have hl2' : (1:ℝ) ≤ lT ^ 2 := one_le_pow₀ hlT
      nlinarith [mul_le_mul_of_nonneg_left hl2' (by positivity : (0:ℝ) ≤ 3 * Cψ * v ^ 16)]
    have hS0' : 0 ≤ (2 + 2 * C1) / Real.log 2 * lT ^ 2 := by positivity
    have h2 : T * S ≤ v ^ 16 * ((2 + 2 * C1) / Real.log 2 * lT ^ 2) := by
      rcases le_or_gt 0 S with hS0 | hS0
      · exact mul_le_mul hT hS' hS0 hv16
      · nlinarith [mul_nonneg hv16 hS0']
    nlinarith
  calc I ≤ K * L ^ j * (3 * ψ + T * S) := hI
    _ ≤ K * (2 ^ j * lT ^ j) * ((3 * Cψ + (2 + 2 * C1) / Real.log 2) * lT ^ 2 * v ^ 16) := by
        rcases le_or_gt 0 (3 * ψ + T * S) with h0 | h0
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hLj hK) hbr h0 (by positivity)
        · have : 0 ≤ K * (2 ^ j * lT ^ j) * ((3 * Cψ + (2 + 2 * C1) / Real.log 2) * lT ^ 2 * v ^ 16) := by
            positivity
          nlinarith [mul_nonneg hK (pow_nonneg hL0 j)]
    _ = 2 ^ j * K * (3 * Cψ + (2 + 2 * C1) / Real.log 2) * lT ^ (j + 2) * v ^ 16 := by ring

/-- The constant of the channel errors. -/
def chanConst (cϱ ℓ₀ K C1 Cψ Mk : ℝ) : ℝ :=
  let KE := K * (8 + 4 * cϱ) + 80 + 20 * cϱ ^ 2
  let KC := 4 * π + 8 + 4 * cϱ
  let KS := 20 * ℓ₀ + 5 * K + 250
  let KP := 2 ^ 1 * (20 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2)
  let KIC := 2 ^ 3 * (20 * π ^ 3 * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2)
  let KD := 24 * Mk
  KE + 3 * KC + 12 * KS + 3 * (13 + KE) + 9 * KC + 6 * Real.sqrt KIC
    + (39 * KS + 3 * KE) + 3 * KC * Real.sqrt KP + KD

section Instantiation

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- `∫Φ²|x| ≤ (8 + 4c_ϱ) lT` and `∫Φ²x² ≤ (8 + 2c_ϱ²) lT` when `L ≤ 2 lT`. -/
theorem Phi_moments_le (hF : LocalHypsCoreW cϱ p F) {lT : ℝ} (hlT : 1 ≤ lT) (hL : p.L ≤ 2 * lT) :
    (∫ x, F.Phi x ^ 2 * |x|) ≤ (8 + 4 * cϱ) * lT ∧ (∫ x, F.Phi x ^ 2 * x ^ 2) ≤ (8 + 2 * cϱ ^ 2) * lT
      ∧ (∫ x, F.Phi x ^ 2) ≤ 4 * π * lT := by
  have hc := hF.four_le_cϱ
  have hw := hF.one_le_w
  have hL0 := hF.L_pos
  refine ⟨?_, ?_, ?_⟩
  · have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * lT / 2 := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < cϱ * p.L / (4 * p.w))
      have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have h3 : cϱ * p.L / 4 ≤ cϱ * lT / 2 := by nlinarith
      linarith
    have := hF.integral_Phi_sq_mul_abs_le
    nlinarith
  · have h1 := hF.integral_Phi_sq_mul_sq_le
    have h2 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith)
    nlinarith
  · have h1 := hF.integral_Phi_sq_le
    nlinarith [Real.pi_pos]

/-- `|g| ≤ L`. -/
theorem abs_g_le (hF : LocalHypsCoreW cϱ p F) (y : ℝ) : |F.g y| ≤ p.L := by
  rw [abs_of_nonneg (hF.g_nonneg y)]
  exact (hF.g_le_Aphi y).trans ((hF.Aphi_le y).trans (max_le (by linarith [abs_nonneg y]) hF.L_pos.le))

/-- The window mean squares of `P_X` and `C_g` at one height. -/
theorem windowMeanSquares_le (hF : LocalHypsCoreW cϱ p F) (hu : WindowProfile ε₁ u)
    {C1 Cψ v : ℝ} (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) (hv : 1 ≤ v) (hvT : p.T = v ^ 12)
    (hlT : 1 ≤ Real.log p.T) (hL : p.L ≤ 2 * Real.log p.T) (hsX : Real.sqrt p.X ≤ v ^ 8)
    (hψ : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ≤ Cψ * p.X)
    (hS : ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n ≤ (p.L ^ 2 / 2 + C1 * p.L) / Real.log 2) :
    (∫ τ, profileΩ u p.T τ * Zeta23.PX p.X τ ^ 2)
        ≤ 2 ^ 1 * (20 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2)
          * Real.log p.T ^ (1 + 2) * v ^ 16
      ∧ (∫ τ, profileΩ u p.T τ * primeDirichletCos F.g p.X τ ^ 2)
        ≤ 2 ^ 3 * (20 * π ^ 3 * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2)
          * Real.log p.T ^ (3 + 2) * v ^ 16 := by
  have hT0 : 0 < p.T := by rw [hvT]; positivity
  have hT1 : 1 ≤ p.T := by rw [hvT]; exact one_le_pow₀ hv
  have hX0 : 0 < p.X := Setting.X_pos p
  have hX1 : 1 ≤ p.X := by
    unfold Setting.X; exact Real.one_le_exp hF.L_pos.le
  have hlogX : Real.log p.X = p.L := Real.log_exp _
  have hXv : p.X ≤ v ^ 16 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsX 2
    rw [Real.sq_sqrt hX0.le, ← pow_mul] at h
    exact h
  have hTv : p.T ≤ v ^ 16 := by rw [hvT]; exact pow_le_pow_right₀ hv (by norm_num)
  have hL0 := hF.L_pos.le
  have hψ0 : 0 ≤ ∑ n ∈ primeRange p.X, (Λ n : ℝ) :=
    Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  constructor
  · have hPc := continuous_PX' p.X
    have hPi : Integrable fun τ => lorentzW p.T (3 * p.T / 2) τ * Zeta23.PX p.X τ ^ 2 :=
      (integrable_lorentzW hT0 _).mul_bdd (c := ((1 / π) * ∑ n ∈ primeRange p.X, acoef n) ^ 2)
        ((hPc.pow 2).aestronglyMeasurable) (Eventually.of_forall fun τ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_PX_le' p.X τ) 2)
    have h1 := integral_profileΩ_mul_le hu hT0 (hPc.pow 2) (fun τ => sq_nonneg _) hPi
    have h2 := integral_lorentz_mul_PX_sq_le hT1 (3 * p.T / 2) hX1
    rw [hlogX] at h2
    refine meanSquare_rate (j := 1) (K := 20 * π * Real.sqrt (Real.exp 1)) ?_ (by positivity) hψ hS
      hL0 hL hlT hXv hT0.le hTv hCψ hC1
    calc _ ≤ 5 * ∫ τ, lorentzW p.T (3 * p.T / 2) τ * Zeta23.PX p.X τ ^ 2 := h1
      _ ≤ 5 * (4 * π * Real.sqrt (Real.exp 1) * p.L * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
            + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 20 * π * Real.sqrt (Real.exp 1) * p.L ^ 1 * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
            + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n) := by ring
  · have hCc := continuous_primeDirichletCos F.g p.X
    have hgb : ∀ y, |F.g y| ≤ p.L := abs_g_le hF
    have hCi : Integrable fun τ => lorentzW p.T (3 * p.T / 2) τ * primeDirichletCos F.g p.X τ ^ 2 :=
      (integrable_lorentzW hT0 _).mul_bdd (c := (p.L * ∑ n ∈ primeRange p.X, acoef n) ^ 2)
        ((hCc.pow 2).aestronglyMeasurable) (Eventually.of_forall fun τ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_primeDirichletCos_le hgb p.X τ) 2)
    have h1 := integral_profileΩ_mul_le hu hT0 (hCc.pow 2) (fun τ => sq_nonneg _) hCi
    have h2 := integral_lorentz_mul_primeDirichletCos_sq_le hT1 (3 * p.T / 2) hX1 hgb
    rw [hlogX] at h2
    refine meanSquare_rate (j := 3) (K := 20 * π ^ 3 * Real.sqrt (Real.exp 1)) ?_ (by positivity) hψ hS
      hL0 hL hlT hXv hT0.le hTv hCψ hC1
    calc _ ≤ 5 * ∫ τ, lorentzW p.T (3 * p.T / 2) τ * primeDirichletCos F.g p.X τ ^ 2 := h1
      _ ≤ 5 * (4 * π ^ 3 * p.L ^ 2 * Real.sqrt (Real.exp 1) * p.L * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
            + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 20 * π ^ 3 * Real.sqrt (Real.exp 1) * p.L ^ 3 * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
            + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n) := by ring

/-- The shift constant of the cosine channels at one height. -/
theorem shiftConst_le {T ε₁ ℓ₀ K l lT : ℝ} (hT0 : 0 < T) (hε : 0 < ε₁) (hε8 : ε₁ ≤ 1 / 8)
    (hT40 : 40 ≤ T) (hl0 : 0 ≤ l) (hl : l ≤ lT) (hlT : 1 ≤ lT) (hℓ₀ : 0 ≤ ℓ₀) (hK : 0 ≤ K) :
    0 ≤ (1 / 2) * (((2 * T - ε₁ * T) - (T + ε₁ * T) + 5)
        * (4 * ℓ₀ / T * 5 * l + (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T)))
      ∧ (1 / 2) * (((2 * T - ε₁ * T) - (T + ε₁ * T) + 5)
        * (4 * ℓ₀ / T * 5 * l + (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T)))
      ≤ (20 * ℓ₀ + 5 * K + 250) * lT := by
  have hεT : ε₁ * T ≤ T / 8 := by
    have := mul_le_mul_of_nonneg_right hε8 hT0.le; linarith only [this]
  have hεT0 : 0 ≤ ε₁ * T := by positivity
  have hS0 : 0 ≤ (2 * T - ε₁ * T) - (T + ε₁ * T) + 5 := by linarith only [hεT, hT0]
  have h1 : (2 * T - ε₁ * T) - (T + ε₁ * T) + 5 ≤ 2 * T := by linarith only [hεT0, hT40]
  have hs₀ : T ≤ T + ε₁ * T := by linarith only [hεT0]
  have h3 : 0 ≤ 4 * ℓ₀ / T * 5 * l + (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T) := by positivity
  refine ⟨by positivity, ?_⟩
  have a1 : 4 * ℓ₀ / T * 5 * l ≤ 20 * ℓ₀ * lT / T := by
    rw [show 4 * ℓ₀ / T * 5 * l = 20 * ℓ₀ * l / T by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by positivity)) hT0.le
  have a2 : (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T) ≤ (5 * K + 250) / T :=
    (div_le_div_of_nonneg_left (by positivity) hT0 hs₀).trans (le_of_eq (by ring))
  have h2 : 4 * ℓ₀ / T * 5 * l + (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T)
      ≤ (20 * ℓ₀ * lT + 5 * K + 250) / T := by
    have e : (20 * ℓ₀ * lT + 5 * K + 250) / T = 20 * ℓ₀ * lT / T + (5 * K + 250) / T := by ring
    rw [e]; linarith only [a1, a2]
  calc (1 / 2) * (((2 * T - ε₁ * T) - (T + ε₁ * T) + 5)
        * (4 * ℓ₀ / T * 5 * l + (K * 5 + 10 * 5 ^ 2) / (T + ε₁ * T)))
      ≤ (1 / 2) * (2 * T * ((20 * ℓ₀ * lT + 5 * K + 250) / T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 h3 (by positivity)) (by norm_num)
    _ = 20 * ℓ₀ * lT + 5 * K + 250 := by field_simp
    _ ≤ (20 * ℓ₀ + 5 * K + 250) * lT := by
        have h5 : 5 * K ≤ 5 * K * lT := le_mul_of_one_le_right (by positivity) hlT
        have h6 : (250:ℝ) ≤ 250 * lT := by linarith only [hlT]
        linarith only [h5, h6]

/-- **The channel errors at one height.** -/
theorem channelError_profile_le (hF : LocalHypsCoreW cϱ p F) (hu : WindowProfile ε₁ u)
    {ℓ₀ K C1 Cψ Mk η v : ℝ} {k : ℕ} (hℓ₀ : 0 ≤ ℓ₀) (hK : 0 ≤ K) (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ)
    (hMk0 : 0 ≤ Mk) (hMk : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ Mk) (hk : 2 ≤ k)
    (hηk : 2 ≤ η * k) (hv : 1 ≤ v) (hvT : p.T = v ^ 12) (hlT : 1 ≤ Real.log p.T)
    (hl : p.l ≤ Real.log p.T) (hL : p.L ≤ 2 * Real.log p.T) (hsX : Real.sqrt p.X ≤ v ^ 8)
    (hA : ∑ n ∈ primeRange p.X, acoef n ≤ 3 * Real.sqrt p.X)
    (hψ : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ≤ Cψ * p.X)
    (hS : ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n ≤ (p.L ^ 2 / 2 + C1 * p.L) / Real.log 2)
    (hD5 : 5 ≤ ε₁ * p.T) :
    channelError (∑ n ∈ primeRange p.X, acoef n)
            (K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2)
            ((∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x|) (∫ x, F.Phi x ^ 2)
            ((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T)) (p.T + ε₁ * p.T) p.L p.l
            ((1 / 2) * (((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T) + 5)
              * (4 * ℓ₀ / p.T * 5 * p.l + (K * 5 + 10 * 5 ^ 2) / (p.T + ε₁ * p.T))))
            (∫ τ in (p.T + ε₁ * p.T - 1)..(2 * p.T - ε₁ * p.T + 1),
              |iteratedDeriv k (profileΩ u p.T) τ|) (p.T ^ (-1 + η)) p.X
            (∫ τ, profileΩ u p.T τ * Zeta23.PX p.X τ ^ 2)
            (∫ τ, profileΩ u p.T τ * primeDirichletCos F.g p.X τ ^ 2) k
      ≤ chanConst cϱ ℓ₀ K C1 Cψ Mk * Real.log p.T ^ 6 * v ^ 11 := by
  have hc := hF.four_le_cϱ
  have hε := hu.pos
  have hε8 := hu.le
  have hT0 : 0 < p.T := by rw [hvT]; positivity
  have hεT : ε₁ * p.T ≤ p.T / 8 := by
    have := mul_le_mul_of_nonneg_right hε8 hT0.le; linarith only [this]
  have hT40 : 40 ≤ p.T := by linarith only [hεT, hD5]
  have hX0 : 0 < p.X := Setting.X_pos p
  have hl0 : 0 ≤ p.l := by linarith only [hF.one_le_l]
  have hL0 : 0 ≤ p.L := hF.L_pos.le
  obtain ⟨hm1, hm2, hm0⟩ := Phi_moments_le hF hlT hL
  have hI0 : 0 ≤ ∫ x, F.Phi x ^ 2 := integral_nonneg fun x => by positivity
  have hXv : p.X ≤ v ^ 16 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsX 2
    rw [Real.sq_sqrt hX0.le, ← pow_mul] at h
    exact h
  obtain ⟨hIP, hIC⟩ := windowMeanSquares_le hF hu hC1 hCψ hv hvT hlT hL hsX hψ hS
  have hA0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n := Finset.sum_nonneg fun n _ => acoef_nonneg n
  -- the derivative mass
  have hεT0 : 0 ≤ ε₁ * p.T := by positivity
  have hab : p.T + ε₁ * p.T - 1 ≤ 2 * p.T - ε₁ * p.T + 1 := by linarith only [hεT, hT0]
  have hD := integral_iteratedDeriv_profileΩ_le hu hT0 k hMk hab
  have hD' : (∫ τ in (p.T + ε₁ * p.T - 1)..(2 * p.T - ε₁ * p.T + 1),
      |iteratedDeriv k (profileΩ u p.T) τ|) ≤ 2 * p.T * (Mk * (p.T⁻¹) ^ k) :=
    hD.trans (mul_le_mul_of_nonneg_right (by linarith only [hεT0, hT40]) (by positivity))
  have hD0 : 0 ≤ ∫ τ in (p.T + ε₁ * p.T - 1)..(2 * p.T - ε₁ * p.T + 1),
      |iteratedDeriv k (profileΩ u p.T) τ| :=
    intervalIntegral.integral_nonneg hab fun τ _ => abs_nonneg _
  have hA2 : (∑ n ∈ primeRange p.X, acoef n) ^ 2 ≤ 9 * p.X := by
    have := pow_le_pow_left₀ hA0 hA 2
    rw [mul_pow, Real.sq_sqrt hX0.le] at this
    linarith only [this]
  have hfar := farPair_le (L := p.L) hv hvT (by linarith only [hlT]) hL hD0 hD' hMk0 hk hηk hA2 hXv
  obtain ⟨hSh0, hSh⟩ := shiftConst_le hT0 hε hε8 hT40 hl0 hl hlT hℓ₀ hK (l := p.l)
  have hE : K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2
      ≤ (K * (8 + 4 * cϱ) + 80 + 20 * cϱ ^ 2) * Real.log p.T := by
    have h1 := mul_le_mul_of_nonneg_left hm1 hK
    have e : (K * (8 + 4 * cϱ) + 80 + 20 * cϱ ^ 2) * Real.log p.T
        = K * ((8 + 4 * cϱ) * Real.log p.T) + 10 * ((8 + 2 * cϱ ^ 2) * Real.log p.T) := by ring
    linarith only [h1, hm2, e]
  have hC : (∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x| ≤ (4 * π + 8 + 4 * cϱ) * Real.log p.T := by
    have e : (4 * π + 8 + 4 * cϱ) * Real.log p.T = 4 * π * Real.log p.T + (8 + 4 * cϱ) * Real.log p.T := by
      ring
    linarith only [hm0, hm1, e]
  have hI : (∫ x, F.Phi x ^ 2) ≤ 13 * Real.log p.T := by
    have := Real.pi_lt_d2
    linarith only [hm0, this, hlT, show 4 * π * Real.log p.T ≤ 13 * Real.log p.T from
      mul_le_mul_of_nonneg_right (by linarith only [this]) (by linarith only [hlT])]
  have hE0 : 0 ≤ K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
    have h1 : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := integral_nonneg fun x => by positivity
    have h2 : 0 ≤ ∫ x, F.Phi x ^ 2 * x ^ 2 := integral_nonneg fun x => by positivity
    positivity
  have hC0 : 0 ≤ (∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x| := by
    have h1 : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := integral_nonneg fun x => by positivity
    positivity
  have hS0 : 0 ≤ (2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T) := by linarith only [hεT, hT0]
  have hSv : (2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T) ≤ v ^ 12 := by
    rw [← hvT]; linarith only [hεT0]
  have hs₀ : v ^ 12 ≤ p.T + ε₁ * p.T := by rw [← hvT]; linarith only [hεT0]
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hKP : 0 ≤ 2 ^ 1 * (20 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2) := by
    positivity
  have hKIC : 0 ≤ 2 ^ 3 * (20 * π ^ 3 * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2) := by
    positivity
  unfold chanConst
  exact channelError_le hlT hv hA0 (hA.trans (by linarith only [hsX])) hE0 hE hC0 hC hI0 hI
    hS0 hSv hs₀ hL0 hL hl0 hl hSh0 hSh hsX hIP hIC hfar (by positivity) (by positivity)
    (by positivity) hKP hKIC (by positivity)

/-- The constant of the grid-comparison errors. -/
def gridConst (cϱ ℓ₀ ε₁ C₀ C1 Cψ : ℝ) : ℝ :=
  let c₁ := ∫ r, lor1 r * Real.sqrt |r|
  let KI := 6 * π * C₀ ^ 2 + 48 * c₁ + 27 * π
    + 2 ^ 1 * (12 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2)
  let KR := cϱ * Real.sqrt (8 / ε₁ ^ 3)
  32 * π * (42 * Real.sqrt (2 * ℓ₀) + 1) * KI + 160 * KR * (5 * π + c₁)

/-- `l ≤ √X` at every bandwidth: `e^{x} ≥ 1 + x + x²/2`. -/
theorem l_le_sqrt_X (hF : LocalHypsCoreW cϱ p F) (hlam : p.lam = 4 / 3) : p.l ≤ Real.sqrt p.X := by
  have hl0 : 0 ≤ p.l := by linarith only [hF.one_le_l]
  have hsX : Real.sqrt p.X = Real.exp (p.L / 2) := by
    unfold Setting.X
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hL : p.L = 4 / 3 * p.l := by unfold Setting.L; rw [hlam]
  rw [hsX, hL]
  have h := Real.quadratic_le_exp_of_nonneg (x := 4 / 3 * p.l / 2) (by positivity)
  nlinarith [sq_nonneg (p.l - 3 / 2)]

/-- **The deficit radius at distance `ε₁T`** is `O(L/v¹⁸)`. -/
theorem deficitRadius_le (hF : LocalHypsCoreW cϱ p F) {v : ℝ} (hv : 1 ≤ v) (hvT : p.T = v ^ 12)
    (hε : 0 < ε₁) (hD : 2 ≤ ε₁ * p.T) :
    deficitRadius cϱ p (ε₁ * p.T) ≤ cϱ * Real.sqrt (8 / ε₁ ^ 3) * p.L / v ^ 18 := by
  have hc := hF.four_le_cϱ
  have hw := hF.one_le_w
  have hL8 := hF.eight_le_L
  have hL0 : 0 < p.L := by linarith only [hL8]
  have hv0 : 0 < v := by linarith only [hv]
  have hT0 : 0 < p.T := by rw [hvT]; positivity
  have hh : p.h = 2 * π / p.L := rfl
  have h3 : 3 + 1 / p.h ≤ p.L := by
    rw [hh, one_div_div]
    have := Real.pi_gt_three
    have : p.L / (2 * π) ≤ p.L / 6 := div_le_div_of_nonneg_left hL0.le (by norm_num) (by linarith)
    linarith only [this, hL8]
  have hD1 : ε₁ * p.T / 2 ≤ ε₁ * p.T - 1 := by linarith only [hD]
  have hD10 : 0 < ε₁ * p.T / 2 := by positivity
  have hcube : (ε₁ * p.T / 2) ^ 3 ≤ (ε₁ * p.T - 1) ^ 3 := pow_le_pow_left₀ hD10.le hD1 3
  have hin : (3 + 1 / p.h) / (ε₁ * p.T - 1) ^ 3 ≤ (Real.sqrt (8 / ε₁ ^ 3) * p.L / v ^ 18) ^ 2 := by
    have hpos : 0 < (ε₁ * p.T - 1) ^ 3 := lt_of_lt_of_le (by positivity) hcube
    have hsq : (Real.sqrt (8 / ε₁ ^ 3) * p.L / v ^ 18) ^ 2 = 8 / ε₁ ^ 3 * p.L ^ 2 / v ^ 36 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    rw [hsq]
    calc (3 + 1 / p.h) / (ε₁ * p.T - 1) ^ 3 ≤ p.L / (ε₁ * p.T / 2) ^ 3 :=
          div_le_div₀ hL0.le h3 (by positivity) hcube
      _ = 8 / ε₁ ^ 3 * p.L / v ^ 36 := by rw [hvT]; field_simp; ring
      _ ≤ 8 / ε₁ ^ 3 * p.L ^ 2 / v ^ 36 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  unfold deficitRadius
  have hcw : cϱ / p.w ≤ cϱ := div_le_self (by linarith only [hc]) hw
  have hs := (Real.sqrt_le_sqrt hin).trans (le_of_eq (Real.sqrt_sq (by positivity)))
  calc cϱ / p.w * Real.sqrt ((3 + 1 / p.h) / (ε₁ * p.T - 1) ^ 3)
      ≤ cϱ * (Real.sqrt (8 / ε₁ ^ 3) * p.L / v ^ 18) :=
        mul_le_mul hcw hs (Real.sqrt_nonneg _) (by linarith only [hc])
    _ = cϱ * Real.sqrt (8 / ε₁ ^ 3) * p.L / v ^ 18 := by ring

/-- The Lorentz mean square of `ν_X` is `O(lT³ v¹⁶)`. -/
theorem lorentz_nuX_le (hF : LocalHypsCoreW cϱ p F) {C₀ C1 Cψ v : ℝ} (hC₀ : 0 ≤ C₀) (hC1 : 0 ≤ C1)
    (hCψ : 0 ≤ Cψ) (hμ : NuBound p (C₀ * p.l) Zeta23.mu) (hv : 1 ≤ v) (hvT : p.T = v ^ 12)
    (hlT : 1 ≤ Real.log p.T) (hl : p.l ≤ Real.log p.T) (hL : p.L ≤ 2 * Real.log p.T)
    (hsX : Real.sqrt p.X ≤ v ^ 8) (hψ : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ≤ Cψ * p.X)
    (hS : ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n ≤ (p.L ^ 2 / 2 + C1 * p.L) / Real.log 2) :
    (∫ τ, lorentzW p.T (3 * p.T / 2) τ * Zeta23.nuX p.X τ ^ 2)
      ≤ (6 * π * C₀ ^ 2 + 48 * (∫ r, lor1 r * Real.sqrt |r|) + 27 * π
          + 2 ^ 1 * (12 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2))
        * Real.log p.T ^ 3 * v ^ 16 := by
  have hT0 : 0 < p.T := by rw [hvT]; positivity
  have hT1 : 1 ≤ p.T := by rw [hvT]; exact one_le_pow₀ hv
  have hX0 : 0 < p.X := Setting.X_pos p
  have hX1 : 1 ≤ p.X := by unfold Setting.X; exact Real.one_le_exp hF.L_pos.le
  have hlogX : Real.log p.X = p.L := Real.log_exp _
  have hXv : p.X ≤ v ^ 16 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsX 2
    rw [Real.sq_sqrt hX0.le, ← pow_mul] at h
    exact h
  have hTv : p.T ≤ v ^ 16 := by rw [hvT]; exact pow_le_pow_right₀ hv (by norm_num)
  have hl0 : 0 ≤ p.l := by linarith only [hF.one_le_l]
  have hlT0 : 0 ≤ Real.log p.T := by linarith only [hlT]
  have hc₁ : 0 ≤ ∫ r, lor1 r * Real.sqrt |r| :=
    integral_nonneg fun r => mul_nonneg (lor1_pos r).le (Real.sqrt_nonneg _)
  have h := integral_lorentz_mul_nuX_sq_le hF hC₀ hμ Zeta23.mu_smooth.continuous hT1 hX1
  rw [hlogX] at h
  have hP := meanSquare_rate (j := 1) (K := 12 * π * Real.sqrt (Real.exp 1))
    (I := 12 * π * Real.sqrt (Real.exp 1) * p.L ^ 1 * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
      + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n)) le_rfl (by positivity) hψ hS hF.L_pos.le hL hlT
    hXv hT0.le hTv hCψ hC1
  -- each piece against `lT³ v¹⁶`
  have hl3 : (1:ℝ) ≤ Real.log p.T ^ 3 := one_le_pow₀ hlT
  have hv16 : 0 ≤ v ^ 16 := hT0.le.trans hTv
  have hlT2 : Real.log p.T ^ 2 ≤ Real.log p.T ^ 3 := pow_le_pow_right₀ hlT (by norm_num)
  have p1 : 2 * (C₀ * p.l) ^ 2 * (p.T * π) ≤ 2 * π * C₀ ^ 2 * Real.log p.T ^ 3 * v ^ 16 := by
    have a : (C₀ * p.l) ^ 2 ≤ C₀ ^ 2 * Real.log p.T ^ 3 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hl0 hl 2).trans hlT2) (sq_nonneg _)
    have b := mul_le_mul a hTv hT0.le (by positivity)
    nlinarith [Real.pi_pos]
  have p2 : 16 * (p.T * ∫ r, lor1 r * Real.sqrt |r|)
      ≤ 16 * (∫ r, lor1 r * Real.sqrt |r|) * Real.log p.T ^ 3 * v ^ 16 := by
    have := mul_le_mul hTv hl3 zero_le_one hv16
    nlinarith
  have p3 : 9 * π * p.X ≤ 9 * π * Real.log p.T ^ 3 * v ^ 16 := by
    have := mul_le_mul hl3 hXv hX0.le (by positivity)
    nlinarith [Real.pi_pos]
  have e : 4 * π * Real.sqrt (Real.exp 1) * p.L * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
        + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n) * 3
      = 12 * π * Real.sqrt (Real.exp 1) * p.L ^ 1 * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ)
        + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n) := by ring
  have hfin : 3 * (2 * (C₀ * p.l) ^ 2 * (p.T * π) + 16 * (p.T * ∫ r, lor1 r * Real.sqrt |r|)
        + 9 * π * p.X + 4 * π * Real.sqrt (Real.exp 1) * p.L
          * (3 * ∑ n ∈ primeRange p.X, (Λ n : ℝ) + p.T * ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n))
      ≤ (6 * π * C₀ ^ 2 + 48 * (∫ r, lor1 r * Real.sqrt |r|) + 27 * π
          + 2 ^ 1 * (12 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2))
        * Real.log p.T ^ 3 * v ^ 16 := by
    have e2 : 1 + 2 = 3 := rfl
    rw [e2] at hP
    nlinarith [p1, p2, p3, hP, e]
  exact h.trans hfin

/-- **The grid-comparison errors at one height.** -/
theorem gridError_profile_le (hF : LocalHypsCoreW cϱ p F) (hlam : p.lam = 4 / 3)
    (hu : WindowProfile ε₁ u) {ℓ₀ C₀ C1 Cψ v : ℝ} (hC₀ : 0 ≤ C₀) (hC1 : 0 ≤ C1)
    (hCψ : 0 ≤ Cψ) (hμ : NuBound p (C₀ * p.l) Zeta23.mu) (hv : 1 ≤ v) (hvT : p.T = v ^ 12)
    (hlT : 1 ≤ Real.log p.T) (hl : p.l ≤ Real.log p.T) (hL : p.L ≤ 2 * Real.log p.T)
    (hLc : cϱ ≤ p.L) (hsX : Real.sqrt p.X ≤ v ^ 8)
    (hψ : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ≤ Cψ * p.X)
    (hS : ∑ n ∈ primeRange p.X, (Λ n : ℝ) / n ≤ (p.L ^ 2 / 2 + C1 * p.L) / Real.log 2)
    (hD : 2 ≤ ε₁ * p.T) :
    ((F.a * p.L ^ 2)⁻¹) ^ 2 * (p.L ^ 2 * (p.L + cϱ / p.w) ^ 2
            * (π * (40 * π * Real.sqrt (2 * ℓ₀ / p.T) / p.h + 32 * p.d / (9 * p.T ^ 2))
              + 2 * π * Real.sqrt (2 * ℓ₀ / p.T) * (20 * π / p.h + 32 * p.d / (9 * p.T ^ 2)))
            * (∫ τ, lorentzW p.T (3 * p.T / 2) τ * Zeta23.nuX p.X τ ^ 2)
          + p.L * deficitRadius cϱ p (ε₁ * p.T) * Bconst p
            * (π * Bconst p + ∫ r, lor1 r * Real.sqrt |r|)
            * ((p.L + cϱ / p.w) ^ 2 * (p.d * π)
              + p.L * (p.L + cϱ / p.w) * ((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T))))
      ≤ gridConst cϱ ℓ₀ ε₁ C₀ C1 Cψ * Real.log p.T ^ 6 * v ^ 11 := by
  have hc := hF.four_le_cϱ
  have hw := hF.one_le_w
  have hL8 := hF.eight_le_L
  have hL0 : 0 < p.L := by linarith only [hL8]
  have hv0 : 0 < v := by linarith only [hv]
  have hT0 : 0 < p.T := by rw [hvT]; positivity
  have hε := hu.pos
  have hε8 := hu.le
  have hεT : ε₁ * p.T ≤ p.T / 8 := by
    have := mul_le_mul_of_nonneg_right hε8 hT0.le; linarith only [this]
  have hεT0 : 0 ≤ ε₁ * p.T := by positivity
  have hX0 : 0 < p.X := Setting.X_pos p
  have hAc : p.L + cϱ / p.w ≤ 2 * p.L := by
    have : cϱ / p.w ≤ cϱ := div_le_self (by linarith only [hc]) hw
    linarith only [this, hLc]
  have hAc0 : 0 ≤ p.L + cϱ / p.w := by
    have : 0 ≤ cϱ / p.w := div_nonneg (by linarith only [hc]) (by linarith only [hw])
    linarith only [this, hL0]
  have hsℓ : Real.sqrt (2 * ℓ₀ / p.T) ≤ Real.sqrt (2 * ℓ₀) / v ^ 6 := by
    rw [Real.sqrt_div' _ hT0.le, hvT, show v ^ 12 = (v ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hd : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := by
    unfold Setting.d; exact Nat.floor_le (by positivity)
  have hIν := lorentz_nuX_le hF hC₀ hC1 hCψ hμ hv hvT hlT hl hL hsX hψ hS
  have hIν0 : 0 ≤ ∫ τ, lorentzW p.T (3 * p.T / 2) τ * Zeta23.nuX p.X τ ^ 2 :=
    integral_nonneg fun τ => mul_nonneg (lorentzW_nonneg _ _ _) (sq_nonneg _)
  have hR₀ := deficitRadius_le hF hv hvT hε hD
  have hR₀0 := (deficitRadius_pos hF hD).le
  have hBc : Bconst p ≤ 5 * v ^ 8 := by
    unfold Bconst
    have := l_le_sqrt_X hF hlam
    linarith only [this, hsX]
  have hBc0 : 0 ≤ Bconst p := by unfold Bconst; have := hF.one_le_l; positivity
  have hc₁ : 0 ≤ ∫ r, lor1 r * Real.sqrt |r| :=
    integral_nonneg fun r => mul_nonneg (lor1_pos r).le (Real.sqrt_nonneg _)
  have ha : 1 / 2 ≤ F.a := hF.b_ge_half.trans hF.b_le_a
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hKI : 0 ≤ 6 * π * C₀ ^ 2 + 48 * (∫ r, lor1 r * Real.sqrt |r|) + 27 * π
      + 2 ^ 1 * (12 * π * Real.sqrt (Real.exp 1)) * (3 * Cψ + (2 + 2 * C1) / Real.log 2) := by positivity
  unfold gridConst
  exact gridError_le hlT hv hL8 hL hAc0 hAc (Real.sqrt_nonneg _) hsℓ rfl (Nat.cast_nonneg _) hd hvT
    hIν0 hIν hR₀0 hR₀ hBc0 hBc hc₁ (by linarith only [hεT, hT0])
    (by rw [← hvT]; linarith only [hεT0]) ha (Real.sqrt_nonneg _) hKI (by positivity)

/-- `∫φ̂²|r| ≤ (8 + 4c_ϱ) lT` and `∫φ̂²r² ≤ (8 + 2c_ϱ²) lT`. -/
theorem phiHat_moments_le (hF : LocalHypsCoreW cϱ p F) {lT : ℝ} (hlT : 1 ≤ lT) (hL : p.L ≤ 2 * lT) :
    (∫ r, F.phiHat r ^ 2 * |r|) ≤ (8 + 4 * cϱ) * lT ∧ (∫ r, F.phiHat r ^ 2 * r ^ 2) ≤ (8 + 2 * cϱ ^ 2) * lT := by
  have hc := hF.four_le_cϱ
  have hw := hF.one_le_w
  have hL0 := hF.L_pos
  refine ⟨?_, ?_⟩
  · have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * lT / 2 := by
      have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < cϱ * p.L / (4 * p.w))
      have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      have h3 : cϱ * p.L / 4 ≤ cϱ * lT / 2 := by nlinarith
      linarith
    have := hF.integral_phiHat_sq_mul_abs_le
    nlinarith
  · have h1 := hF.integral_phiHat_sq_mul_sq_le
    have h2 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith)
    nlinarith

end Instantiation

/-- The error part of the diagonal core. -/
theorem core_err_le {a L l T CΓ C2 M₂ ℓ₁ : ℝ} (ha : 1 / 2 ≤ a) (hL8 : 8 ≤ L) (hT0 : 0 < T)
    (hl1 : 1 ≤ l) (hM₂ : M₂ = T * ℓ₁ ^ 2 / (4 * π ^ 2)) (hℓ0 : 0 ≤ ℓ₁) (hℓ2 : ℓ₁ ≤ 2 * l) :
    ((a * L) ^ 2)⁻¹ * (2 * π * L * (|CΓ| * M₂ / l ^ 2) + T / π * (|C2| * L ^ 2))
      ≤ (|CΓ| + 2 * |C2|) * T := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hL0 : 0 < L := by linarith only [hL8]
  have ha0 : 0 < a := by linarith only [ha]
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  have hq4 : ((a * L) ^ 2)⁻¹ ≤ 4 / L ^ 2 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num), mul_pow]
    have h1 : (1 / 2) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg L)
    have e : (1 / 2 : ℝ) ^ 2 * L ^ 2 = L ^ 2 / 4 := by ring
    linarith only [h2, e]
  have hE0 : 0 ≤ 2 * π * L * (|CΓ| * M₂ / l ^ 2) + T / π * (|C2| * L ^ 2) := by positivity
  refine (mul_le_mul_of_nonneg_right hq4 hE0).trans ?_
  have hM₂l : M₂ / l ^ 2 ≤ T / π ^ 2 := by
    rw [hM₂, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ℓ₁ ^ 2 ≤ 4 * l ^ 2 := by
      have := pow_le_pow_left₀ hℓ0 hℓ2 2
      linarith only [this, show (2 * l) ^ 2 = 4 * l ^ 2 by ring]
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ T * π ^ 2)
    have e1 : T * ℓ₁ ^ 2 * π ^ 2 = T * π ^ 2 * ℓ₁ ^ 2 := by ring
    have e2 : T * (4 * π ^ 2 * l ^ 2) = T * π ^ 2 * (4 * l ^ 2) := by ring
    linarith only [h2, e1, e2]
  have h1 : 4 / L ^ 2 * (2 * π * L * (|CΓ| * M₂ / l ^ 2)) ≤ 8 / (π * L) * |CΓ| * T := by
    have e : 4 / L ^ 2 * (2 * π * L * (|CΓ| * M₂ / l ^ 2)) = 8 * π / L * |CΓ| * (M₂ / l ^ 2) := by
      field_simp; ring
    rw [e]
    calc 8 * π / L * |CΓ| * (M₂ / l ^ 2) ≤ 8 * π / L * |CΓ| * (T / π ^ 2) :=
          mul_le_mul_of_nonneg_left hM₂l (by positivity)
      _ = 8 / (π * L) * |CΓ| * T := by field_simp
  have h2 : 8 / (π * L) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith only [hL8, hπ3]
  have h3 : 4 / L ^ 2 * (T / π * (|C2| * L ^ 2)) = 4 / π * |C2| * T := by field_simp
  have h4 : 4 / π ≤ 2 := by rw [div_le_iff₀ hπ]; linarith only [hπ3]
  have h5 : 8 / (π * L) * |CΓ| * T ≤ 1 * |CΓ| * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hT0.le
  have h6 : 4 / π * |C2| * T ≤ 2 * |C2| * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (abs_nonneg _)) hT0.le
  rw [mul_add]
  linarith only [h1, h3, h5, h6]

/-- **The diagonal core at one height** is `43/36` of the normalisation up to `ε'/2` and `O(T)`. -/
theorem core_le_at {T ε' cϱ : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hT0 : 0 < T)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hl14 : 14 / ε' ≤ Zeta23.l T)
    {CΓ C2 : ℝ}
    (hΓ : |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * π ^ 2)|
      ≤ CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2)
    (hC2 : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
      - Real.log x ^ 3 / 6| ≤ C2 * Real.log x ^ 2)
    (ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T) :
    ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * (params43.L T ^ 2
        * ((∫ x, (params43.localFun T).Phi x ^ 2) * (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
          + (1 / π) * T * sumA2g (params43.toSetting T).X (params43.localFun T).g))
      ≤ (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) + (|CΓ| + 2 * |C2|) * T := by
  have hLl : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hpL : (params43.toSetting T).L = params43.L T := rfl
  have hπ := Real.pi_pos
  have h14 : 14 ≤ 14 / ε' := by rw [le_div_iff₀ hε']; linarith only [hε'1]
  have hl1 : 1 ≤ Zeta23.l T := by linarith only [h14, hl14]
  have hL8 : 8 ≤ params43.L T := by rw [hLl]; linarith only [h14, hl14]
  have hL0 : 0 < params43.L T := by linarith only [hL8]
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hc₁ : 2 * Real.log 2 - 1 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
  have hell : ell1 T = Zeta23.l T + (2 * Real.log 2 - 1) := by unfold ell1; ring
  have hell0 : 0 ≤ ell1 T := by rw [hell]; linarith only [hl1, hc₀]
  have hell2 : ell1 T ≤ 2 * Zeta23.l T := by rw [hell]; linarith only [hl1, hc₁]
  have ha2 : 1 / 2 ≤ params43.a T := by
    have h2 : 2 / (4 / 3 * Zeta23.l T) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [hL8, hLl]
    linarith only [ha, h2]
  have ha0 : 0 < params43.a T := by linarith only [ha2]
  -- the archimedean diagonal
  have hb1 : (params43.localFun T).b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hIΦ : (∫ x, (params43.localFun T).Phi x ^ 2) ≤ 2 * π * params43.L T := by
    rw [hF.Phi_sq_integral, hpL]
    have := mul_le_mul_of_nonneg_left hb1 (by positivity : (0:ℝ) ≤ 2 * π * params43.L T)
    linarith only [this]
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℝ, M₂ = T * ell1 T ^ 2 / (4 * π ^ 2) := ⟨_, rfl⟩
  rw [← hM₂] at hΓ
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  have hμ2 : (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) ≤ M₂ + |CΓ| * M₂ / Zeta23.l T ^ 2 := by
    have h := (abs_le.mp hΓ).2
    have : CΓ * M₂ / Zeta23.l T ^ 2 ≤ |CΓ| * M₂ / Zeta23.l T ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM₂0) (by positivity)
    linarith only [h, this]
  have hμ0 : 0 ≤ ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith only [hT0]) fun τ _ => sq_nonneg _
  -- the prime diagonal
  have hX2 : 2 ≤ (params43.toSetting T).X := by
    unfold Setting.X
    have : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith only [this]
    exact this.trans (Real.exp_le_exp.mpr (by rw [hpL]; linarith only [hL8]))
  have hsum := sumA2g_le_wide hC2 hF hX2
  rw [hpL] at hsum
  have hsum' : sumA2g (params43.toSetting T).X (params43.localFun T).g
      ≤ params43.L T ^ 3 / 6 + |C2| * params43.L T ^ 2 := by
    have : C2 * params43.L T ^ 2 ≤ |C2| * params43.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    linarith only [hsum, this]
  -- the core
  have hcore : (∫ x, (params43.localFun T).Phi x ^ 2) * (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
        + (1 / π) * T * sumA2g (params43.toSetting T).X (params43.localFun T).g
      ≤ T * params43.L T / (2 * π) * (ell1 T ^ 2 + params43.L T ^ 2 / 3)
        + (2 * π * params43.L T * (|CΓ| * M₂ / Zeta23.l T ^ 2) + T / π * (|C2| * params43.L T ^ 2)) := by
    have h1 : (∫ x, (params43.localFun T).Phi x ^ 2) * (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
        ≤ 2 * π * params43.L T * (M₂ + |CΓ| * M₂ / Zeta23.l T ^ 2) :=
      mul_le_mul hIΦ hμ2 hμ0 (by positivity)
    have h2 : (1 / π) * T * sumA2g (params43.toSetting T).X (params43.localFun T).g
        ≤ (1 / π) * T * (params43.L T ^ 3 / 6 + |C2| * params43.L T ^ 2) :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    have e : T * params43.L T / (2 * π) * (ell1 T ^ 2 + params43.L T ^ 2 / 3)
        + (2 * π * params43.L T * (|CΓ| * M₂ / Zeta23.l T ^ 2) + T / π * (|C2| * params43.L T ^ 2))
        = 2 * π * params43.L T * (M₂ + |CΓ| * M₂ / Zeta23.l T ^ 2)
          + (1 / π) * T * (params43.L T ^ 3 / 6 + |C2| * params43.L T ^ 2) := by
      rw [hM₂]; field_simp; ring
    linarith only [h1, h2, e]
  have hmain := diagonal_main_le (ε := ε') hε' hε'1 hl14 hl1 hc₀ hc₁ ha hT0
  rw [← hell, ← hLl] at hmain
  -- the normalisation
  have hq : ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * params43.L T ^ 2
      = ((params43.a T * params43.L T) ^ 2)⁻¹ := by field_simp
  have hq0 : 0 ≤ ((params43.a T * params43.L T) ^ 2)⁻¹ := by positivity
  rw [← mul_assoc, hq]
  have hfirst : ((params43.a T * params43.L T) ^ 2)⁻¹
      * (T * params43.L T / (2 * π) * (ell1 T ^ 2 + params43.L T ^ 2 / 3))
      ≤ (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) := by
    have h := mul_le_mul_of_nonneg_left hmain hq0
    have e : ((params43.a T * params43.L T) ^ 2)⁻¹ * ((43 / 36 + ε' / 2)
        * (params43.a T * params43.L T) ^ 2 * (T * ell1 T / (2 * π)))
        = (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) := by field_simp
    linarith only [h, e]
  have hsecond := core_err_le (CΓ := CΓ) (C2 := C2) ha2 hL8 hT0 hl1 hM₂ hell0 hell2
  have hfin := mul_le_mul_of_nonneg_left hcore hq0
  rw [mul_add] at hfin
  linarith only [hfin, hfirst, hsecond]

/-- The constant of the trace errors. -/
def traceConst (cϱ Kq Ct : ℝ) : ℝ :=
  6 * Ct + 3 * π + (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2))

theorem trem_Q_le {L sX Kq I₁ I₂ lT v cϱ : ℝ} (hKq : 0 ≤ Kq) (hc : 0 ≤ cϱ) (hI₁ : I₁ ≤ (8 + 4 * cϱ) * lT)
    (hI₂0 : 0 ≤ I₂) (hI₂ : I₂ ≤ (8 + 2 * cϱ ^ 2) * lT) (hL : L ≤ 2 * lT) (hlT : 1 ≤ lT) (hv : 1 ≤ v)
    (hsX0 : 0 ≤ sX) (hsX : sX ≤ v ^ 8) :
    Kq * (I₁ + I₂) + 12 * π * L * sX + 12 * sX * I₂
      ≤ (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)) * (lT * v ^ 8) := by
  have hπ := Real.pi_pos
  have hv8 : 1 ≤ v ^ 8 := one_le_pow₀ hv
  have hlT0 : 0 ≤ lT := by linarith only [hlT]
  have h1 : Kq * (I₁ + I₂) ≤ Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) * (lT * v ^ 8) := by
    have a1 : I₁ + I₂ ≤ (16 + 4 * cϱ + 2 * cϱ ^ 2) * lT := by
      have e : (16 + 4 * cϱ + 2 * cϱ ^ 2) * lT = (8 + 4 * cϱ) * lT + (8 + 2 * cϱ ^ 2) * lT := by ring
      linarith only [hI₁, hI₂, e]
    have a2 : (16 + 4 * cϱ + 2 * cϱ ^ 2) * lT ≤ (16 + 4 * cϱ + 2 * cϱ ^ 2) * (lT * v ^ 8) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hlT0 hv8) (by positivity)
    have a3 := mul_le_mul_of_nonneg_left (a1.trans a2) hKq
    have e : Kq * ((16 + 4 * cϱ + 2 * cϱ ^ 2) * (lT * v ^ 8))
        = Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) * (lT * v ^ 8) := by ring
    linarith only [a3, e]
  have h2 : 12 * π * L * sX ≤ 24 * π * (lT * v ^ 8) := by
    have a := mul_le_mul hL hsX hsX0 (by linarith only [hlT])
    have e1 : 12 * π * L * sX = 12 * π * (L * sX) := by ring
    have e2 : 24 * π * (lT * v ^ 8) = 12 * π * (2 * lT * v ^ 8) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left a (by positivity)
  have h3 : 12 * sX * I₂ ≤ 12 * (8 + 2 * cϱ ^ 2) * (lT * v ^ 8) := by
    have a := mul_le_mul hsX hI₂ hI₂0 (by positivity)
    have e1 : 12 * sX * I₂ = 12 * (sX * I₂) := by ring
    have e2 : 12 * (8 + 2 * cϱ ^ 2) * (lT * v ^ 8) = 12 * (v ^ 8 * ((8 + 2 * cϱ ^ 2) * lT)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left a (by norm_num)
  have e : (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)) * (lT * v ^ 8)
      = Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) * (lT * v ^ 8) + 24 * π * (lT * v ^ 8)
        + 12 * (8 + 2 * cϱ ^ 2) * (lT * v ^ 8) := by ring
  linarith only [h1, h2, h3, e]

theorem trem_Cr_le {a L T sX Kq I₁ I₂ : ℝ} (ha1 : a ≤ 1) (hL0 : 0 < L) (hT1 : 1 ≤ T) (hsX0 : 0 ≤ sX)
    (hI₂0 : 0 ≤ I₂) :
    Kq * (I₁ + I₂) / T + ((6 * sX / T) * (2 * π * a * L) + (12 * sX / T ^ 2) * I₂)
      ≤ (Kq * (I₁ + I₂) + 12 * π * L * sX + 12 * sX * I₂) / T := by
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by linarith only [hT1]
  have h1 : 12 * sX / T ^ 2 * I₂ ≤ 12 * sX * I₂ / T := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hT0]
    have hTT : T ≤ T * T := le_mul_of_one_le_right hT0.le hT1
    have := mul_le_mul_of_nonneg_left hTT (by positivity : (0:ℝ) ≤ 12 * sX * I₂)
    have e : 12 * sX * I₂ * T ^ 2 = 12 * sX * I₂ * (T * T) := by ring
    linarith only [this, e]
  have h2 : 6 * sX / T * (2 * π * a * L) ≤ 12 * π * L * sX / T := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hT0.le
    have := mul_le_mul_of_nonneg_left ha1 (by positivity : (0:ℝ) ≤ 12 * π * L * sX)
    have e : 6 * sX * (2 * π * a * L) = 12 * π * L * sX * a := by ring
    linarith only [this, e]
  have e : (Kq * (I₁ + I₂) + 12 * π * L * sX + 12 * sX * I₂) / T
      = Kq * (I₁ + I₂) / T + 12 * π * L * sX / T + 12 * sX * I₂ / T := by ring
  rw [e]
  linarith only [h1, h2]

theorem trem_p1 {a Ct lT sX v : ℝ} (ha : 1 / 2 ≤ a) (hCt : 0 ≤ Ct) (hlT : 1 ≤ lT) (hv : 1 ≤ v)
    (hsX0 : 0 ≤ sX) (hsX : sX ≤ v ^ 8) :
    Ct / a * (1 + lT + sX) ≤ 6 * Ct * (lT * v ^ 8) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hv8 : 1 ≤ v ^ 8 := one_le_pow₀ hv
  have h1 : Ct / a ≤ 2 * Ct := by
    rw [div_le_iff₀ ha0]
    have := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ 2 * Ct)
    linarith only [this]
  have h2 : 1 + lT + sX ≤ 3 * (lT * v ^ 8) := by
    have a1 : lT ≤ lT * v ^ 8 := le_mul_of_one_le_right (by linarith only [hlT]) hv8
    have a2 : sX ≤ lT * v ^ 8 := hsX.trans (le_mul_of_one_le_left (by positivity) hlT)
    have a3 : 1 ≤ lT * v ^ 8 := one_le_mul_of_one_le_of_one_le hlT hv8
    linarith only [a1, a2, a3]
  calc Ct / a * (1 + lT + sX) ≤ 2 * Ct * (3 * (lT * v ^ 8)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 6 * Ct * (lT * v ^ 8) := by ring

theorem trem_p2 {a L T ε₁ Cr Q : ℝ} (ha : 1 / 2 ≤ a) (hL8 : 8 ≤ L) (hT0 : 0 < T) (hε0 : 0 ≤ ε₁)
    (hε8 : ε₁ ≤ 1 / 8) (hCr0 : 0 ≤ Cr) (hCr : Cr ≤ Q / T) (hQ0 : 0 ≤ Q) :
    (a * L ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / L)) * Cr) ≤ Q / 4 := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hL0 : 0 < L := by linarith only [hL8]
  have ha0 : 0 < a := by linarith only [ha]
  have hinv : (a * L ^ 2)⁻¹ ≤ 2 / L ^ 2 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg L)
    linarith only [this]
  have h1 : 4 * ε₁ * T / (2 * π / L) ≤ T * L := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have h4 : 4 * ε₁ ≤ 2 * π := by linarith only [hε8, hπ3]
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ T * L)
    linarith only [this]
  calc (a * L ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / L)) * Cr) ≤ 2 / L ^ 2 * (T * L * (Q / T)) :=
        mul_le_mul hinv (mul_le_mul h1 hCr hCr0 (by positivity)) (by positivity) (by positivity)
    _ = 2 * Q / L := by field_simp
    _ ≤ Q / 4 := by
        rw [div_le_div_iff₀ hL0 (by norm_num)]
        have := mul_le_mul_of_nonneg_left hL8 hQ0
        linarith only [this]

theorem trem_p3 {a L l T Cr Q : ℝ} (ha : 1 / 2 ≤ a) (hL8 : 8 ≤ L) (hl : l ≤ L) (hT1 : 1 ≤ T)
    (hCr : Cr ≤ Q / T) (hQ0 : 0 ≤ Q) :
    (a * L ^ 2)⁻¹ * (2 * (2 * π * a * L * l + Cr)) ≤ 4 * π + Q / 16 := by
  have hπ := Real.pi_pos
  have hL0 : 0 < L := by linarith only [hL8]
  have ha0 : 0 < a := by linarith only [ha]
  have hinv : (a * L ^ 2)⁻¹ ≤ 2 / L ^ 2 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_right ha (sq_nonneg L)
    linarith only [this]
  have e : (a * L ^ 2)⁻¹ * (2 * (2 * π * a * L * l + Cr))
      = 4 * π * (l / L) + (a * L ^ 2)⁻¹ * (2 * Cr) := by field_simp; ring
  have h1 : l / L ≤ 1 := by rw [div_le_one hL0]; exact hl
  have hQT : Q / T ≤ Q := div_le_self hQ0 hT1
  have h2 : (a * L ^ 2)⁻¹ * (2 * Cr) ≤ Q / 16 := by
    rcases le_or_gt 0 Cr with hC0 | hC0
    · have hL2 : 64 ≤ L ^ 2 := by nlinarith only [hL8]
      calc (a * L ^ 2)⁻¹ * (2 * Cr) ≤ 2 / L ^ 2 * (2 * Q) :=
            mul_le_mul hinv (by linarith only [hCr, hQT]) (by positivity) (by positivity)
        _ ≤ 2 / 64 * (2 * Q) :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL2)
              (by positivity)
        _ = Q / 16 := by ring
    · have : (a * L ^ 2)⁻¹ * (2 * Cr) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith only [hC0])
      have : 0 ≤ Q / 16 := by positivity
      linarith
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 4 * π)
  linarith only [this, h2]

/-- **The remainder of the trace at one height.** -/
theorem trace_rem_le {a L l T sX Ct Kq I₁ I₂ ε₁ lT v cϱ : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (hL8 : 8 ≤ L) (hl : l ≤ L) (hT1 : 1 ≤ T) (hε0 : 0 ≤ ε₁) (hε8 : ε₁ ≤ 1 / 8) (hCt : 0 ≤ Ct)
    (hKq : 0 ≤ Kq) (hc : 0 ≤ cϱ) (hI₁0 : 0 ≤ I₁) (hI₁ : I₁ ≤ (8 + 4 * cϱ) * lT) (hI₂0 : 0 ≤ I₂)
    (hI₂ : I₂ ≤ (8 + 2 * cϱ ^ 2) * lT) (hL : L ≤ 2 * lT) (hlT : 1 ≤ lT) (hv : 1 ≤ v)
    (hsX0 : 0 ≤ sX) (hsX : sX ≤ v ^ 8) :
    Ct / a * (1 + lT + sX)
        + (a * L ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / L))
            * (Kq * (I₁ + I₂) / T + ((6 * sX / T) * (2 * π * a * L) + (12 * sX / T ^ 2) * I₂))
          + 2 * (2 * π * a * L * l
            + (Kq * (I₁ + I₂) / T + ((6 * sX / T) * (2 * π * a * L) + (12 * sX / T ^ 2) * I₂))))
      ≤ traceConst cϱ Kq Ct * lT ^ 6 * v ^ 11 := by
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by linarith only [hT1]
  have hL0 : 0 < L := by linarith only [hL8]
  have hv8 : 1 ≤ v ^ 8 := one_le_pow₀ hv
  have hl6 : lT * v ^ 8 ≤ lT ^ 6 * v ^ 11 :=
    mul_le_mul (by simpa using pow_le_pow_right₀ hlT (by norm_num : 1 ≤ 6))
      (pow_le_pow_right₀ hv (by norm_num)) (by positivity) (by positivity)
  have hlv : 1 ≤ lT * v ^ 8 := one_le_mul_of_one_le_of_one_le hlT hv8
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Kq * (I₁ + I₂) + 12 * π * L * sX + 12 * sX * I₂ := ⟨_, rfl⟩
  have hQb := trem_Q_le hKq hc hI₁ hI₂0 hI₂ hL hlT hv hsX0 hsX
  rw [← hQ] at hQb
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : ℝ, Cr = Kq * (I₁ + I₂) / T
      + ((6 * sX / T) * (2 * π * a * L) + (12 * sX / T ^ 2) * I₂) := ⟨_, rfl⟩
  have hCr := trem_Cr_le (Kq := Kq) (I₁ := I₁) ha1 hL0 hT1 hsX0 hI₂0
  rw [← hQ, ← hCrdef] at hCr
  have hCr0 : 0 ≤ Cr := by rw [hCrdef]; have := (by linarith only [ha] : (0:ℝ) < a); positivity
  rw [← hCrdef]
  have p1 := trem_p1 ha hCt hlT hv hsX0 hsX
  have p2 := trem_p2 ha hL8 hT0 hε0 hε8 hCr0 hCr hQ0
  have p3 := trem_p3 ha hL8 hl hT1 hCr hQ0
  have k1 := mul_le_mul_of_nonneg_left hl6 (by positivity : (0:ℝ) ≤ 6 * Ct)
  have k2 := mul_le_mul_of_nonneg_left (hlv.trans hl6) (by positivity : (0:ℝ) ≤ 3 * π)
  have hK3 : 0 ≤ Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2) := by positivity
  have k3 := mul_le_mul_of_nonneg_left hl6 hK3
  have hπ4 := Real.pi_lt_four
  have hq : Q / 4 + 4 * π + Q / 16 ≤ 3 * π * (lT ^ 6 * v ^ 11)
      + (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)) * (lT ^ 6 * v ^ 11) := by
    have a1 : Q ≤ (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)) * (lT ^ 6 * v ^ 11) :=
      hQb.trans k3
    have a2 : 4 * π ≤ 3 * π * (lT ^ 6 * v ^ 11) + π := by
      have : 3 * π ≤ 3 * π * (lT ^ 6 * v ^ 11) := by nlinarith only [hlv.trans hl6, hπ]
      linarith only [this]
    have hW := hlv.trans hl6
    have a3 : π ≤ 11 / 16 * ((Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2))
        * (lT ^ 6 * v ^ 11)) := by
      have b1 : 24 * π ≤ Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2) := by
        have : 0 ≤ Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) := by positivity
        have : 0 ≤ 12 * (8 + 2 * cϱ ^ 2) := by positivity
        linarith
      have b2 := mul_le_mul b1 hW (by norm_num) (by linarith only [b1, hπ])
      linarith only [b2, hπ]
    linarith only [a1, a2, a3, hQ0]
  unfold traceConst
  have e : (6 * Ct + 3 * π + (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)))
      * lT ^ 6 * v ^ 11 = 6 * Ct * (lT ^ 6 * v ^ 11) + 3 * π * (lT ^ 6 * v ^ 11)
        + (Kq * (16 + 4 * cϱ + 2 * cϱ ^ 2) + 24 * π + 12 * (8 + 2 * cϱ ^ 2)) * (lT ^ 6 * v ^ 11) := by
    ring
  rw [e]
  linarith only [p1, p2, p3, k1, hq]

/-- **The weighted trace at one height**: `tr Ĝ_w ≥ N − 4ε₁Tl − O(T) − O(lT⁶ v¹¹)`. -/
theorem trace_ge_at {T cϱ : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hu : WindowProfile ε₁ u)
    {ℓ₀ Kq Ct N v : ℝ} (hℓ₀ : 0 ≤ ℓ₀) (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) (hKq0 : 0 ≤ Kq)
    (hKq : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq 0 1 (t + r) - muq 0 1 t| ≤ Kq * (|r| + r ^ 2) / t)
    (hμl : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T) (hCt : 0 ≤ Ct)
    (htr : |trGtA (params43.toSetting T) (params43.localFun T) - params43.a T * params43.L T * N|
      ≤ Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))))
    (hv : 2 ≤ v) (hvT : T = v ^ 12) (hlT : 1 ≤ Real.log T) (hL : params43.L T ≤ 2 * Real.log T)
    (hsX : Real.sqrt (params43.X T) ≤ v ^ 8)
    (hA : ∑ n ∈ primeRange (params43.X T), acoef n ≤ 3 * Real.sqrt (params43.X T)) :
    N - 4 * ε₁ * T * Zeta23.l T - (6 * (1 + 2 * ℓ₀) + 4) * T
        - traceConst cϱ Kq Ct * Real.log T ^ 6 * v ^ 11
      ≤ rtrace (params43.hat T (wmat (profileGrid u T) (params43.Gp T))) := by
  have hpT : (params43.toSetting T).T = T := rfl
  have hpL : (params43.toSetting T).L = params43.L T := rfl
  have hpX : (params43.toSetting T).X = params43.X T := rfl
  have hpl : (params43.toSetting T).l = Zeta23.l T := rfl
  have hpa : (params43.localFun T).a = params43.a T := rfl
  have hph : (params43.toSetting T).h = 2 * π / params43.L T := rfl
  have hLl : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hc := hF.four_le_cϱ
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have hL0 : 0 < params43.L T := by linarith only [hL8]
  have hv1 : 1 ≤ v := by linarith only [hv]
  have hT1 : 1 ≤ T := by rw [hvT]; exact one_le_pow₀ hv1
  have hT2 : 2 ≤ T := by rw [hvT]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hv 12]
  have hT0 : 0 < T := by linarith only [hT1]
  have hε := hu.pos
  have hε8 := hu.le
  have ha : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have ha1 : params43.a T ≤ 1 := hF.a_le_one
  have ha0 : 0 < params43.a T := by linarith only [ha]
  have hl1 : 1 ≤ Zeta23.l T := hF.one_le_l
  have hlL : Zeta23.l T ≤ params43.L T := by rw [hLl]; linarith only [hl1]
  have hX0 : 0 < params43.X T := Setting.X_pos (params43.toSetting T)
  have hX1 : 1 ≤ params43.X T := by
    show 1 ≤ (params43.toSetting T).X
    unfold Setting.X; exact Real.one_le_exp hF.L_pos.le
  have hsX1 : 1 ≤ Real.sqrt (params43.X T) := by rw [Real.one_le_sqrt]; exact hX1
  have hlogX : Real.log (params43.X T) = params43.L T := Real.log_exp _
  -- the pointwise constant `C = 2πaLl + C_r`
  obtain ⟨hI₁, hI₂⟩ := phiHat_moments_le hF hlT (by rw [hpL]; exact hL)
  have hI₁0 : 0 ≤ ∫ r, (params43.localFun T).phiHat r ^ 2 * |r| := integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2 := integral_nonneg fun r => by positivity
  have hC := fun k (hk : k ∈ Finset.range (params43.toSetting T).d) =>
    abs_mu_add_Pi_part_le hF (by rw [hpT]; exact hT2) hKq0 hKq (M := Zeta23.l T)
      (by rw [hpT]; exact hμl) hk
  have hC0 : 0 ≤ 2 * π * (params43.localFun T).a * (params43.toSetting T).L * Zeta23.l T
      + Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
        + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / (params43.toSetting T).T
      + ((6 * Real.sqrt (params43.toSetting T).X / (params43.toSetting T).T)
          * (2 * π * (params43.localFun T).a * (params43.toSetting T).L)
        + (12 * Real.sqrt (params43.toSetting T).X / (params43.toSetting T).T ^ 2)
          * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) := by
    rw [hpT, hpa, hpL]; positivity
  -- the alias weight
  have hvi : 0 < v⁻¹ ^ 4 := by positivity
  have hvi2 : v⁻¹ ^ 4 ≤ Real.log 2 := by
    have h1 : v⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hv
    have h2 : v⁻¹ ^ 4 ≤ (2⁻¹) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
    have e : ((2:ℝ)⁻¹) ^ 4 = 1 / 16 := by norm_num
    have := Real.log_two_gt_d9
    linarith only [h2, this, e]
  have htr0 := rtrace_profile_ge hF hT2 hu hℓ₀ hlip hC0 hC hvi hvi2
  rw [hpT, hpL, hpX, hpa, hph] at htr0
  -- the unweighted trace
  have hc0 : 0 < (params43.a T * params43.L T ^ 2)⁻¹ := by positivity
  have hmain : (params43.a T * params43.L T ^ 2)⁻¹
      * (params43.L T * trGtA (params43.toSetting T) (params43.localFun T))
      ≥ N - Ct / params43.a T * (1 + Real.log T + Real.sqrt (params43.X T)) := by
    have h1 := (abs_le.mp htr).1
    have h2 : params43.L T * (params43.a T * params43.L T * N
          - Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))))
        ≤ params43.L T * trGtA (params43.toSetting T) (params43.localFun T) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1]) hL0.le
    have h3 := mul_le_mul_of_nonneg_left h2 hc0.le
    have e : (params43.a T * params43.L T ^ 2)⁻¹ * (params43.L T * (params43.a T * params43.L T * N
          - Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T)))))
        = N - Ct / params43.a T * (1 + Real.log T + Real.sqrt (params43.X T)) := by
      field_simp
    linarith only [h3, e]
  -- the collar
  have hcol := collar_split (a := params43.a T) (L := params43.L T) (l := Zeta23.l T) (T := T)
    (ε₁ := ε₁) (Cr := Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
        + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / T
      + ((6 * Real.sqrt (params43.X T) / T) * (2 * π * params43.a T * params43.L T)
        + (12 * Real.sqrt (params43.X T) / T ^ 2) * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2))
    ha0 hL0
  -- the prime collar
  have hal := sum_acoef_alias_le hX1 hvi hvi2
  rw [hlogX] at hal
  have hd : ((params43.toSetting T).d : ℝ) ≤ params43.L T * T / (2 * π) := by
    unfold Setting.d; rw [hpL, hpT]; exact Nat.floor_le (by positivity)
  have hpc := primeCollar_le ha hL8 hℓ₀ hA (Finset.sum_nonneg fun n _ => acoef_nonneg n) hal
    (Nat.cast_nonneg _) hd hv1 hvT hsX1 hsX
  -- the remainder
  have hrem := trace_rem_le ha ha1 hL8 hlL hT1 hε.le hε8 hCt hKq0 (by linarith only [hc]) hI₁0 hI₁ hI₂0 hI₂
    hL hlT hv1 (Real.sqrt_nonneg _) hsX (cϱ := cϱ)
  -- assemble
  have e1 : (params43.a T * params43.L T ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / params43.L T) + 2)
      * (2 * π * params43.a T * params43.L T * Zeta23.l T
        + (Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
            + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / T
          + ((6 * Real.sqrt (params43.X T) / T) * (2 * π * params43.a T * params43.L T)
            + (12 * Real.sqrt (params43.X T) / T ^ 2) * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2))))
      = (params43.a T * params43.L T ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / params43.L T) + 2)
        * (2 * π * params43.a T * params43.L T * Zeta23.l T
          + Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
              + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / T
          + ((6 * Real.sqrt (params43.X T) / T) * (2 * π * params43.a T * params43.L T)
            + (12 * Real.sqrt (params43.X T) / T ^ 2) * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2))) := by
    ring
  have hsplit : (params43.a T * params43.L T ^ 2)⁻¹ * (params43.L T * trGtA (params43.toSetting T) (params43.localFun T)
      - (4 * ε₁ * T / (2 * π / params43.L T) + 2)
        * (2 * π * params43.a T * params43.L T * Zeta23.l T
          + Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
              + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / T
          + ((6 * Real.sqrt (params43.X T) / T) * (2 * π * params43.a T * params43.L T)
            + (12 * Real.sqrt (params43.X T) / T ^ 2) * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2))
      - 2 * (params43.L T * ((1 + 2 * ℓ₀ / T * T) * params43.L T / (2 * v⁻¹ ^ 4))
          * ∑ n ∈ primeRange (params43.X T), acoef n
        + v⁻¹ ^ 4 * ((params43.toSetting T).d : ℝ)
          * ∑ n ∈ (primeRange (params43.X T)).filter (fun n => params43.L T - v⁻¹ ^ 4 < ycoef n), acoef n))
      = (params43.a T * params43.L T ^ 2)⁻¹ * (params43.L T * trGtA (params43.toSetting T) (params43.localFun T))
        - (params43.a T * params43.L T ^ 2)⁻¹ * ((4 * ε₁ * T / (2 * π / params43.L T) + 2)
        * (2 * π * params43.a T * params43.L T * Zeta23.l T
          + Kq * ((∫ r, (params43.localFun T).phiHat r ^ 2 * |r|)
              + ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2) / T
          + ((6 * Real.sqrt (params43.X T) / T) * (2 * π * params43.a T * params43.L T)
            + (12 * Real.sqrt (params43.X T) / T ^ 2) * ∫ r, (params43.localFun T).phiHat r ^ 2 * r ^ 2)))
        - (params43.a T * params43.L T ^ 2)⁻¹ * (2 * (params43.L T * ((1 + 2 * ℓ₀ / T * T) * params43.L T
            / (2 * v⁻¹ ^ 4)) * ∑ n ∈ primeRange (params43.X T), acoef n
          + v⁻¹ ^ 4 * ((params43.toSetting T).d : ℝ)
            * ∑ n ∈ (primeRange (params43.X T)).filter (fun n => params43.L T - v⁻¹ ^ 4 < ycoef n),
              acoef n)) := by ring
  rw [hsplit] at htr0
  have hl := hlT
  linarith only [htr0, hmain, hcol, e1, hpc, hrem]

theorem chanConst_nonneg {cϱ ℓ₀ K C1 Cψ Mk : ℝ} (hc : 0 ≤ cϱ) (hℓ₀ : 0 ≤ ℓ₀) (hK : 0 ≤ K)
    (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) (hMk : 0 ≤ Mk) : 0 ≤ chanConst cϱ ℓ₀ K C1 Cψ Mk := by
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hπ := Real.pi_pos
  simp only [chanConst]
  positivity

theorem gridConst_nonneg {cϱ ℓ₀ ε₁ C₀ C1 Cψ : ℝ} (hc : 0 ≤ cϱ) (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) :
    0 ≤ gridConst cϱ ℓ₀ ε₁ C₀ C1 Cψ := by
  have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hπ := Real.pi_pos
  have hc₁ : 0 ≤ ∫ r, lor1 r * Real.sqrt |r| :=
    integral_nonneg fun r => mul_nonneg (lor1_pos r).le (Real.sqrt_nonneg _)
  simp only [gridConst]
  positivity

/-- Combination of the four Frobenius pieces. -/
theorem frob_combine {S q L X co ch G bX cs bch bG : ℝ} (hS : S ≤ L ^ 2 * (X + co + ch) + G)
    (hq0 : 0 ≤ q) (hqL0 : 0 ≤ q * L ^ 2) (hqL : q * L ^ 2 ≤ 1) (hX : q * (L ^ 2 * X) ≤ bX)
    (hco : q * L ^ 2 * co = cs) (hch : ch ≤ bch) (hbch : 0 ≤ bch) (hG : q * G ≤ bG) :
    q * S ≤ bX + cs + bch + bG := by
  have h1 := mul_le_mul_of_nonneg_left hS hq0
  have h2 : q * L ^ 2 * ch ≤ bch := by
    calc q * L ^ 2 * ch ≤ q * L ^ 2 * bch := mul_le_mul_of_nonneg_left hch hqL0
      _ ≤ 1 * bch := mul_le_mul_of_nonneg_right hqL hbch
      _ = bch := one_mul _
  have e : q * (L ^ 2 * (X + co + ch) + G) = q * (L ^ 2 * X) + q * L ^ 2 * co + q * L ^ 2 * ch + q * G := by
    ring
  linarith only [h1, e, hX, hco, h2, hG]

/-- **The coalescent surplus** at height `T`: the smooth-window coalescent pair sum over
`0 < |log(n/m)| ≤ T^{−1+η}`, normalised by `(aL)²`. -/
def coalescentSurplus (u : ℝ → ℝ) (η T : ℝ) : ℝ :=
  coalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))
    / (params43.a T * params43.L T) ^ 2

/-- **The weighted Frobenius norm at one height.** -/
theorem frob_le_at {T cϱ : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hT : 2 * π ≤ T)
    (hu : WindowProfile ε₁ u) {ℓ₀ K C₀ C1 Cψ Mk η v ε' CΓ C2 : ℝ} {k : ℕ} (hℓ₀ : 0 ≤ ℓ₀)
    (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) (hℓ1 : 2 * ℓ₀ / T ≤ 1) (hD5 : 5 ≤ ε₁ * T)
    (hK : 0 ≤ K)
    (hμinc : ∀ t, 2 ≤ t → ∀ r, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hμl : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T) (hC₀ : 0 ≤ C₀)
    (hμ : NuBound (params43.toSetting T) (C₀ * Zeta23.l T) Zeta23.mu)
    (hν : NuBound (params43.toSetting T) (Bconst (params43.toSetting T)) (Zeta23.nuX (params43.X T)))
    (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) (hMk0 : 0 ≤ Mk)
    (hMk : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ Mk) (hk : 2 ≤ k) (hηk : 2 ≤ η * k)
    (hv : 1 ≤ v) (hvT : T = v ^ 12) (hlT : 1 ≤ Real.log T) (hl : Zeta23.l T ≤ Real.log T)
    (hL : params43.L T ≤ 2 * Real.log T) (hLc : cϱ ≤ params43.L T)
    (hsX : Real.sqrt (params43.X T) ≤ v ^ 8)
    (hA : ∑ n ∈ primeRange (params43.X T), acoef n ≤ 3 * Real.sqrt (params43.X T))
    (hψ : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) ≤ Cψ * params43.X T)
    (hS : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) / n
      ≤ (params43.L T ^ 2 / 2 + C1 * params43.L T) / Real.log 2)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hl14 : 14 / ε' ≤ Zeta23.l T)
    (hΓ : |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * π ^ 2)|
      ≤ CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2)
    (hC2 : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
      - Real.log x ^ 3 / 6| ≤ C2 * Real.log x ^ 2)
    (ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T) :
    frobSq (params43.hat T (wmat (profileGrid u T) (params43.Gp T)))
      ≤ (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) + coalescentSurplus u η T
        + (|CΓ| + 2 * |C2|) * T
        + (chanConst cϱ ℓ₀ K C1 Cψ Mk + gridConst cϱ ℓ₀ ε₁ C₀ C1 Cψ) * Real.log T ^ 6 * v ^ 11 := by
  have hπ := Real.pi_pos
  have hθ₀ : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos (by linarith only [hT, hπ]) _
  have hW := weightedFrobenius_le hF hT hu hℓ₀ hlip hℓ1 hD5 (k := k) hK hμinc hμl hC₀ hμ hν hθ₀
  have hch := channelError_profile_le hF hu hℓ₀ hK hC1 hCψ hMk0 hMk hk hηk hv hvT hlT hl hL hsX hA hψ hS hD5
    (η := η)
  have hgr := gridError_profile_le hF rfl hu hC₀ hC1 hCψ hμ hv hvT hlT hl hL hLc hsX hψ hS
    (show (2:ℝ) ≤ ε₁ * T by linarith only [hD5]) (ℓ₀ := ℓ₀)
  have hco := core_le_at hF (by linarith only [hT, hπ]) hε' hε'1 hl14 hΓ hC2 ha
  have hpT : (params43.toSetting T).T = T := rfl
  rw [hpT] at hch hgr
  rw [frobSq_profile_eq]
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have hq0 : 0 ≤ ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 := sq_nonneg _
  have hq1 : ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * params43.L T ^ 2 ≤ 1 := by
    have e : ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * params43.L T ^ 2
        = ((params43.a T * params43.L T) ^ 2)⁻¹ := by field_simp
    rw [e]
    apply inv_le_one_of_one_le₀
    have h4 : 4 ≤ params43.a T * params43.L T := by nlinarith only [ha2, hL8]
    nlinarith only [h4]
  have hcs : ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * params43.L T ^ 2
      * coalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η))
      = coalescentSurplus u η T := by
    unfold coalescentSurplus
    field_simp
  have hc0 : 0 ≤ cϱ := by linarith only [hF.four_le_cϱ]
  have hW0 : 0 ≤ Real.log T ^ 6 * v ^ 11 := by
    have : 0 ≤ Real.log T := by linarith only [hlT]
    positivity
  have hchn : 0 ≤ chanConst cϱ ℓ₀ K C1 Cψ Mk * Real.log T ^ 6 * v ^ 11 := by
    have := chanConst_nonneg hc0 hℓ₀ hK hC1 hCψ hMk0
    rw [mul_assoc]; exact mul_nonneg this hW0
  have hql0 : 0 ≤ ((params43.a T * params43.L T ^ 2)⁻¹) ^ 2 * params43.L T ^ 2 := by positivity
  have hfin := frob_combine hW hq0 hql0 hq1 hco hcs hch hchn hgr
  have hgn := gridConst_nonneg (ℓ₀ := ℓ₀) (ε₁ := ε₁) (C₀ := C₀) hc0 hC1 hCψ
  have e : (chanConst cϱ ℓ₀ K C1 Cψ Mk + gridConst cϱ ℓ₀ ε₁ C₀ C1 Cψ) * Real.log T ^ 6 * v ^ 11
      = chanConst cϱ ℓ₀ K C1 Cψ Mk * Real.log T ^ 6 * v ^ 11
        + gridConst cϱ ℓ₀ ε₁ C₀ C1 Cψ * Real.log T ^ 6 * v ^ 11 := by ring
  rw [e]
  exact hfin.trans_eq (by ring)

/-- **The seam, combined.** If the coalescent surplus is below `N` the Frobenius norm is at most
`3N`; otherwise the bound is negative and holds trivially. -/
theorem certificate_combine {N N₀ tr f cs M Et Ef E₀ NII B ε ε' ε₁ Tl : ℝ}
    (hseam : 4 * tr - f - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt f + B) ≤ N₀)
    (htr : N - 4 * ε₁ * Tl - Et ≤ tr) (hf : f ≤ (43 / 36 + ε' / 2) * M + cs + Ef)
    (hM : M ≤ N + E₀) (hTl : Tl ≤ 2 * π * M) (hN0 : 0 ≤ N) (hN₀ : 0 ≤ N₀) (hε₁ : 0 ≤ ε₁)
    (hε'0 : 0 ≤ ε') (hε'1 : ε' ≤ 1) (hε'ε : ε' ≤ ε)
    (hE : 4 * Et + Ef + (43 / 36 + ε' / 2 + 32 * π * ε₁) * E₀ + 3 * NII ≤ ε / 4 * N)
    (hB0 : 0 ≤ B) (hB : B * (4 + 4 * Real.sqrt N + B) ≤ ε / 4 * N)
    (hEf : Ef ≤ N / 10) (hE₀0 : 0 ≤ E₀) (hE₀ : E₀ ≤ N / 10) :
    (29 / 36 - 32 * π * ε₁ - ε) * N - cs ≤ N₀ := by
  have hπ := Real.pi_pos
  have hε0 : 0 ≤ ε := hε'0.trans hε'ε
  have h32 : 0 ≤ 32 * π * ε₁ := by positivity
  rcases le_or_gt N cs with hcs | hcs
  · -- a large coalescent surplus makes the bound trivial
    have : (29 / 36 - 32 * π * ε₁ - ε) * N ≤ 29 / 36 * N := by
      have := mul_nonneg (add_nonneg h32 hε0) hN0
      linarith only [this]
    linarith only [this, hcs, hN0, hN₀]
  · have hf3 : f ≤ 3 * N := by
      have h1 : (43 / 36 + ε' / 2) * M ≤ (43 / 36 + 1 / 2) * (N + N / 10) := by
        have a : (43 / 36 + ε' / 2) * M ≤ (43 / 36 + ε' / 2) * (N + E₀) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have b : (43 / 36 + ε' / 2) * (N + E₀) ≤ (43 / 36 + 1 / 2) * (N + N / 10) :=
          mul_le_mul (by linarith only [hε'1]) (by linarith only [hE₀]) (by linarith only [hN0, hE₀0])
            (by norm_num)
        linarith only [a, b]
      linarith only [h1, hcs, hEf, hN0, hf]
    have hsf : Real.sqrt f ≤ 2 * Real.sqrt N := by
      have h1 : Real.sqrt f ≤ Real.sqrt (3 * N) := Real.sqrt_le_sqrt hf3
      rw [Real.sqrt_mul (by norm_num)] at h1
      have h3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg N)
      linarith only [h1, this]
    have hBf : B * (4 + 2 * Real.sqrt f + B) ≤ B * (4 + 4 * Real.sqrt N + B) :=
      mul_le_mul_of_nonneg_left (by linarith only [hsf]) hB0
    have hM1 : (43 / 36 + ε' / 2) * M ≤ (43 / 36 + ε' / 2) * (N + E₀) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have hTl1 : 16 * ε₁ * Tl ≤ 32 * π * ε₁ * (N + E₀) := by
      have a : 16 * ε₁ * Tl ≤ 16 * ε₁ * (2 * π * M) := mul_le_mul_of_nonneg_left hTl (by positivity)
      have b : 16 * ε₁ * (2 * π * M) ≤ 16 * ε₁ * (2 * π * (N + E₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM (by positivity)) (by positivity)
      have e : 16 * ε₁ * (2 * π * (N + E₀)) = 32 * π * ε₁ * (N + E₀) := by ring
      linarith only [a, b, e]
    have hε'N : ε' / 2 * N ≤ ε / 2 * N := mul_le_mul_of_nonneg_right (by linarith only [hε'ε]) hN0
    have e1 : (43 / 36 + ε' / 2) * (N + E₀) = 43 / 36 * N + ε' / 2 * N + (43 / 36 + ε' / 2) * E₀ := by ring
    have e2 : 32 * π * ε₁ * (N + E₀) = 32 * π * ε₁ * N + 32 * π * ε₁ * E₀ := by ring
    have e3 : (43 / 36 + ε' / 2 + 32 * π * ε₁) * E₀ = (43 / 36 + ε' / 2) * E₀ + 32 * π * ε₁ * E₀ := by ring
    have e4 : (29 / 36 - 32 * π * ε₁ - ε) * N = 29 / 36 * N - 32 * π * ε₁ * N - ε * N := by ring
    linarith only [hseam, htr, hf, hBf, hB, hM1, hTl1, hε'N, hE, e1, e2, e3, e4]

/-- **The certificate at one height.** -/
theorem certificate_at {T : ℝ}
    (hF : LocalHypsCoreW params43.crho (params43.toSetting T) (params43.localFun T))
    (hT300 : Tail.T₀ ≤ T) (hwL : 8 * params43.w ≤ params43.L T) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hu : WindowProfile ε₁ u) {ℓ₀ K Kq C₀ C1 Cψ C2 CΓ Ct Mk η v ε ε' CR : ℝ} {k : ℕ}
    (hℓ₀ : 0 ≤ ℓ₀) (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) (hℓ1 : 2 * ℓ₀ / T ≤ 1)
    (hD5 : 5 ≤ ε₁ * T) (hK : 0 ≤ K)
    (hμinc : ∀ t, 2 ≤ t → ∀ r, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hKq0 : 0 ≤ Kq)
    (hKq : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq 0 1 (t + r) - muq 0 1 t| ≤ Kq * (|r| + r ^ 2) / t)
    (hμl : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T) (hC₀ : 0 ≤ C₀)
    (hμ : NuBound (params43.toSetting T) (C₀ * Zeta23.l T) Zeta23.mu)
    (hν : NuBound (params43.toSetting T) (Bconst (params43.toSetting T)) (Zeta23.nuX (params43.X T)))
    (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) (hMk0 : 0 ≤ Mk)
    (hMk : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ Mk) (hk : 2 ≤ k) (hηk : 2 ≤ η * k)
    (hv : 2 ≤ v) (hvT : T = v ^ 12) (hlT : 1 ≤ Real.log T) (hl : Zeta23.l T ≤ Real.log T)
    (hL : params43.L T ≤ 2 * Real.log T) (hLc : params43.crho ≤ params43.L T)
    (hsX : Real.sqrt (params43.X T) ≤ v ^ 8)
    (hA : ∑ n ∈ primeRange (params43.X T), acoef n ≤ 3 * Real.sqrt (params43.X T))
    (hψ : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) ≤ Cψ * params43.X T)
    (hS : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) / n
      ≤ (params43.L T ^ 2 / 2 + C1 * params43.L T) / Real.log 2)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hε'ε : ε' ≤ ε) (hl14 : 14 / ε' ≤ Zeta23.l T)
    (hΓ : |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * π ^ 2)|
      ≤ CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2)
    (hC2 : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
      - Real.log x ^ 3 / 6| ≤ C2 * Real.log x ^ 2)
    (ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T) (hCt : 0 ≤ Ct)
    (htr : |trGtA (params43.toSetting T) (params43.localFun T)
        - params43.a T * params43.L T * (zetaZeroConfig.N T (2 * T) : ℝ)|
      ≤ Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))))
    (hRv : |(zetaZeroConfig.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)| ≤ CR * Real.log T)
    (hCR : 0 ≤ CR)
    (hE : 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
            * Real.log T ^ 6 * v ^ 11)
        + (43 / 36 + ε' / 2 + 32 * π * ε₁) * (CR * Real.log T) + 3 * (NII zetaZeroConfig T : ℝ)
      ≤ ε / 4 * (zetaZeroConfig.N T (2 * T) : ℝ))
    (hB : Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T / (params43.a T * params43.L T)
        * (4 + 4 * Real.sqrt (zetaZeroConfig.N T (2 * T) : ℝ)
          + Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T / (params43.a T * params43.L T))
      ≤ ε / 4 * (zetaZeroConfig.N T (2 * T) : ℝ))
    (hEf : (|CΓ| + 2 * |C2|) * T
        + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
          * Real.log T ^ 6 * v ^ 11 ≤ (zetaZeroConfig.N T (2 * T) : ℝ) / 10)
    (hE₀ : CR * Real.log T ≤ (zetaZeroConfig.N T (2 * T) : ℝ) / 10) :
    (29 / 36 - 32 * π * ε₁ - ε) * (zetaZeroConfig.N T (2 * T) : ℝ) - coalescentSurplus u η T
      ≤ (zetaZeroConfig.N0star T (2 * T) : ℝ) := by
  have hP := paramsValidFam_params43
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by have : (300:ℝ) ≤ T := hT300; linarith only [this]
  have hT2π : 2 * π * 1 ≤ T := by have : (300:ℝ) ≤ T := hT300; linarith only [this, Real.pi_lt_four]
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have ha0 : 0 < params43.a T := by linarith only [ha2]
  -- the weighted seam
  have Htail : Tail.TailHyp zetaZeroConfig params43 T A₀ (params43.C1 T) :=
    { hT := hT300, hL := by linarith only [hL8], hA₀ := hA₀, hloc := hloc,
      hC₁ := Tail.C1_nonneg _ T,
      hdecay := fun r y hy hz => norm_phiHat_sub_I_mul_le_fam hP hwL r y hy hz }
  have hseam := seamA_weighted hT0.le Htail (fun z => GzGp.phiHat_conj params43 T z)
    (fun r => GzGp.phiHat_ofReal params43 T r) (poissonSq_fam hP hwL) ha0
    (w := profileGrid u T) (abs_profileGrid_le hu T)
  have hGzGp : zetaZeroConfig.Gz params43 T = params43.Gp T := by
    refine zetaZeroConfig.Gz_eq_Gp params43 T paperInputs_zeta.EF (by linarith only [hL8]) ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp
        (Taper.phi_contDiff hP.taper hP.w_pos (hP.two_w_le hwL))).of_le (by norm_num)
    · exact closure_minimal (Taper.phi_support_subset hP.taper hP.w_pos) isClosed_Icc
  rw [hGzGp] at hseam
  -- the trace and the Frobenius norm
  have htrb := trace_ge_at hF hu hℓ₀ hlip hKq0 hKq hμl hCt htr hv hvT hlT hL hsX hA
  have hfb := frob_le_at hF (by linarith only [hT2π]) hu hℓ₀ hlip hℓ1 hD5 hK hμinc hμl hC₀ hμ hν
    hC1 hCψ hMk0 hMk hk hηk (by linarith only [hv]) hvT hlT hl hL hLc hsX hA hψ hS hε' hε'1 hl14 hΓ hC2
    ha (η := η) (CΓ := CΓ) (C2 := C2)
  -- the counts
  have hM : T * ell1 T / (2 * π) ≤ (zetaZeroConfig.N T (2 * T) : ℝ) + CR * Real.log T := by
    have := (abs_le.mp hRv).1; linarith only [this]
  have hTl : T * Zeta23.l T ≤ 2 * π * (T * ell1 T / (2 * π)) := by
    have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
    have e : 2 * π * (T * ell1 T / (2 * π)) = T * ell1 T := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by unfold ell1; linarith only [hc₀]) hT0.le
  have hN0 : (0:ℝ) ≤ (zetaZeroConfig.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hN₀ : (0:ℝ) ≤ (zetaZeroConfig.N0star T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hB0 : 0 ≤ Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T
      / (params43.a T * params43.L T) :=
    div_nonneg (Htail.tailInputs ha0 (fun z => Params.phiHat_conj z)).theta_nonneg (by positivity)
  have htr' : (zetaZeroConfig.N T (2 * T) : ℝ) - 4 * ε₁ * (T * Zeta23.l T)
      - ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
      ≤ rtrace (params43.hat T (wmat (profileGrid u T) (params43.Gp T))) := by
    have e : 4 * ε₁ * (T * Zeta23.l T) = 4 * ε₁ * T * Zeta23.l T := by ring
    linarith only [htrb, e]
  have hfb' : frobSq (params43.hat T (wmat (profileGrid u T) (params43.Gp T)))
      ≤ (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) + coalescentSurplus u η T
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
            * Real.log T ^ 6 * v ^ 11) := by
    linarith only [hfb]
  exact certificate_combine hseam htr' hfb' hM hTl hN0 hN₀ hu.pos.le hε'.le hε'1 hε'ε hE hB0 hB hEf
    (by positivity) hE₀

/-- The regime of a large height: the scale `v = T^{1/12}`. -/
theorem scale_facts {T : ℝ} (hT : 4096 ≤ T) (hl : Zeta23.l T ≤ Real.log T) :
    2 ≤ T ^ (1 / 12 : ℝ) ∧ T = (T ^ (1 / 12 : ℝ)) ^ 12
      ∧ Real.sqrt (params43.X T) ≤ (T ^ (1 / 12 : ℝ)) ^ 8
      ∧ (T ^ (1 / 12 : ℝ)) ^ 11 = T ^ (11 / 12 : ℝ) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hpow : ∀ n : ℕ, (T ^ (1 / 12 : ℝ)) ^ n = T ^ ((n : ℝ) / 12) := fun n => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (4096:ℝ) ^ (1 / 12 : ℝ) = 2 := by
      rw [show (4096:ℝ) = 2 ^ (12:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← h1]
    exact Real.rpow_le_rpow (by norm_num) hT (by norm_num)
  · rw [hpow]; norm_num
  · have h := sqrt_exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 hl
    rw [hpow]
    refine le_of_le_of_eq h ?_
    norm_num
  · rw [hpow]; norm_num

/-- **The smooth-weighted certificate at bandwidth `4/3`: three quarters up to the coalescent band.**
For every window profile `u` of collar `ε₁`, every `η > 0` and `ε > 0`, for all large `T`,
`N₀*(T, 2T) ≥ (29/36 − 32πε₁ − ε) N(T, 2T) − coalescentSurplus u η T`.
The unconditional bandwidth-`4/3` core `43/36` gives `2 − 43/36 = 29/36 > 3/4`; every prime pair
outside the coalescent band `0 < |log(n/m)| ≤ T^{−1+η}`, every sum frequency, every cross
channel and the whole grid end effect are paid by the window. -/
theorem zeta_coalescent_certificate_four_thirds (hu : WindowProfile ε₁ u) {η : ℝ} (hη : 0 < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (29 / 36 - 32 * π * ε₁ - ε) * (Ncount T (2 * T) : ℝ) - coalescentSurplus u η T
      ≤ (N0star T (2 * T) : ℝ) := by
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hπ := Real.pi_pos
  have hP := paramsValidFam_params43
  have H := paperInputs_zeta
  have hε₁ := hu.pos
  obtain ⟨CR, TR, hRvM⟩ := H.RvM.main
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨CN, hNII⟩ := Tail.eventually_NII_le zetaZeroConfig hA₀ hloc
  obtain ⟨Ct, Tt, hCt, htrW⟩ := prop_trace_zeta_wide (cϱ := params43.crho)
    (by norm_num : (0:ℝ) < 4 / 3) |CR|
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨R, hRdef⟩ : ∃ x : ℝ, x = Taper.l1Deriv2 stdProfile := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound gammaFacts
  obtain ⟨Kq, hKq0, hKq⟩ := muq_increment_bound
    (GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl) le_rfl
  obtain ⟨C₀, Tm, hC₀1, hμB⟩ := mu_nuBound
  obtain ⟨Tμ, hμl⟩ := mu_abs_le_l gammaFacts
  obtain ⟨TB, hνB⟩ := nuBound_eventually (4 / 3) gammaFacts (by norm_num : (0:ℝ) < 4 / 3)
  obtain ⟨x₀, hx₀⟩ := H.cheb.cheb1b
  obtain ⟨Cψ, hψ⟩ := H.cheb.cheb1a
  obtain ⟨C1, hC1⟩ := H.cheb.cheb2a
  obtain ⟨C2, hC2⟩ := H.cheb.cheb2b
  obtain ⟨CΓ, TΓ, hΓsq⟩ := gammaFacts.int_mu_sq
  obtain ⟨ℓ₀, hℓ₀, hlip⟩ := hu.exists_lipschitz
  obtain ⟨k, hk2, hηk⟩ : ∃ k : ℕ, 2 ≤ k ∧ 2 ≤ η * k := by
    refine ⟨max 2 ⌈2 / η⌉₊, le_max_left _ _, ?_⟩
    have h1 : 2 / η ≤ (⌈2 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 / η⌉₊ : ℕ) : ℝ) ≤ ((max 2 ⌈2 / η⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h3 : η * (2 / η) = 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hη.le]
  obtain ⟨Mk, hMk0, hMk⟩ := hu.exists_iteratedDeriv_pow_four_le k
  -- the constants
  set cr := params43.crho with hcr
  have hcr4 : 4 ≤ cr := (hTL (max TL 0) (le_max_left _ _)).four_le_cϱ
  set Kpow := 4 * traceConst cr Kq Ct + (chanConst cr ℓ₀ K |C1| |Cψ| Mk
    + gridConst cr ℓ₀ ε₁ C₀ |C1| |Cψ|) with hKpow
  have hKpow0 : 0 ≤ Kpow := by
    have h1 : 0 ≤ traceConst cr Kq Ct := by unfold traceConst; positivity
    have h2 := chanConst_nonneg (by linarith only [hcr4]) hℓ₀ hK0 (abs_nonneg C1) (abs_nonneg Cψ) hMk0
      (cϱ := cr)
    have h3 := gridConst_nonneg (ℓ₀ := ℓ₀) (ε₁ := ε₁) (C₀ := C₀) (by linarith only [hcr4]) (abs_nonneg C1)
      (abs_nonneg Cψ) (cϱ := cr)
    rw [hKpow]; positivity
  set Klin := 4 * (6 * (1 + 2 * ℓ₀) + 4) + (|CΓ| + 2 * |C2|) with hKlin
  have hKlin0 : 0 ≤ Klin := by rw [hKlin]; positivity
  set Kc := 43 / 36 + 1 / 2 + 32 * π * ε₁ with hKc
  have hKc1 : 1 ≤ Kc := by rw [hKc]; have : 0 ≤ 32 * π * ε₁ := by positivity
                           linarith only [this]
  -- the eventual regime
  have hl := Real.tendsto_log_atTop
  have e1 := eventually_l_bounds
  have e2 := eventually_ge_atTop (max (max (max TR Tt) (max TL Tm)) (max (max Tμ TB) (max TΓ 4096)))
  have e3 := eventually_ge_atTop (max (max (5 / ε₁) (2 * ℓ₀)) (max (8 * π * |CR|)
    (max (256 * π * Kc * |CR| / ε') (8 * π * (1024 / ε' ^ 2 + 40 / ε')))))
  have e4 := hl.eventually_ge_atTop (max (max (28 / ε' + 12) (3 * cr / 2 + 12))
    (max (3 * (|x₀| + 2) / 2) (256 * π * Klin / ε')))
  have e5 := eventually_log_pow_rpow_le 6 (by norm_num : (11:ℝ) / 12 < 1) hKpow0
    (by positivity : (0:ℝ) < ε' / (256 * π))
  have e6 := eventually_log_pow_rpow_le 0 (by norm_num : (1:ℝ) / 2 < 1)
    (by positivity : (0:ℝ) ≤ 3 * |CN|) (by positivity : (0:ℝ) < ε' / (256 * π))
  have e7 := eventually_log_pow_rpow_le_const 1 (by norm_num : (4:ℝ) / 3 / 2 - 1 < 0)
    (by positivity : (0:ℝ) ≤ 32 * A₀ * R ^ 2) (by norm_num : (0:ℝ) < 1)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, hNII] with T ⟨hlog1, hl1, hlo, hhi⟩ hT1 hT2 hlogT hrate
    hrate2 hrate3 hNIIT
  -- unpacking the thresholds
  have hTR : TR ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT1))
  have hTt : Tt ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT1))
  have hTLT : TL ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT1))
  have hTm : Tm ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT1))
  have hTμ : Tμ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hT1))
  have hTB : TB ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hT1))
  have hTΓ : TΓ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT1))
  have hT4096 : (4096:ℝ) ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT1))
  have hTε : 5 / ε₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT2)
  have hTℓ : 2 * ℓ₀ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT2)
  have hTCR : 8 * π * |CR| ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT2)
  have hTKc : 256 * π * Kc * |CR| / ε' ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT2))
  have hTN : 8 * π * (1024 / ε' ^ 2 + 40 / ε') ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT2))
  have hlε : 28 / ε' + 12 ≤ Real.log T := (le_max_left _ _).trans ((le_max_left _ _).trans hlogT)
  have hlc : 3 * cr / 2 + 12 ≤ Real.log T := (le_max_right _ _).trans ((le_max_left _ _).trans hlogT)
  have hlx : 3 * (|x₀| + 2) / 2 ≤ Real.log T := (le_max_left _ _).trans ((le_max_right _ _).trans hlogT)
  have hlK : 256 * π * Klin / ε' ≤ Real.log T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogT)
  have hT0 : 0 < T := by linarith only [hT4096]
  have hF := hTL T hTLT
  -- the parameters
  have hLl : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hw : params43.w = 1 := rfl
  have hL8 : 8 ≤ params43.L T := by
    have : 12 ≤ Real.log T := by have := (by positivity : (0:ℝ) ≤ 28 / ε'); linarith only [this, hlε]
    rw [hLl]; linarith only [this, hlo]
  have hwL : 8 * params43.w ≤ params43.L T := by rw [hw]; linarith only [hL8]
  have hL : params43.L T ≤ 2 * Real.log T := by rw [hLl]; linarith only [hhi, hl1]
  have hLc : cr ≤ params43.L T := by rw [hLl]; linarith only [hlo, hlc]
  obtain ⟨hv2, hvT, hsX, hv11⟩ := scale_facts hT4096 hhi
  set v := T ^ (1 / 12 : ℝ) with hvdef
  have hXL : params43.X T = Real.exp (params43.L T) := rfl
  have hlogX : Real.log (params43.X T) = params43.L T := by rw [hXL, Real.log_exp]
  have hXx : max x₀ 2 ≤ params43.X T := by
    rw [hXL]
    have h1 : params43.L T + 1 ≤ Real.exp (params43.L T) := Real.add_one_le_exp _
    have h2 : |x₀| + 2 ≤ params43.L T := by rw [hLl]; linarith only [hlo, hlx]
    exact max_le (by linarith only [le_abs_self x₀, h1, h2]) (by linarith only [h1, h2, abs_nonneg x₀])
  have hX2 : 2 ≤ params43.X T := (le_max_right _ _).trans hXx
  have hA : ∑ n ∈ primeRange (params43.X T), acoef n ≤ 3 * Real.sqrt (params43.X T) := by
    have := hx₀ (params43.X T) ((le_max_left _ _).trans hXx)
    unfold primeRange acoef; exact this
  have hψ' : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) ≤ |Cψ| * params43.X T := by
    have := hψ (params43.X T) hX2
    have h2 : Cψ * params43.X T ≤ |Cψ| * params43.X T :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hX2])
    unfold primeRange; linarith only [this, h2]
  have hS : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) / n
      ≤ (params43.L T ^ 2 / 2 + |C1| * params43.L T) / Real.log 2 := by
    have h := sum_vonMangoldt_div_le hC1 hX2
    rw [hlogX] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le)
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) (by linarith only [hL8] : (0:ℝ) ≤ params43.L T)
    linarith only [this]
  have hΓ := hΓsq T hTΓ
  have ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T := by
    have := one_sub_le_a_params43 hwL
    rw [hw, hLl] at this; simpa using this
  have hε₁T : 5 ≤ ε₁ * T := by
    rw [div_le_iff₀ hε₁] at hTε; linarith only [hTε]
  have hℓ1 : 2 * ℓ₀ / T ≤ 1 := by rw [div_le_one hT0]; exact hTℓ
  have hl14 : 14 / ε' ≤ Zeta23.l T := by
    have e : 14 / ε' = (28 / ε') / 2 := by ring
    linarith only [hlo, hlε, e]
  have hμ : NuBound (params43.toSetting T) (C₀ * Zeta23.l T) Zeta23.mu := hμB _ hTm
  have hν := hνB (params43.toSetting T) rfl hTB
  have hμl' : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T := hμl (params43.toSetting T) hTμ
  -- the counts
  set N : ℝ := (zetaZeroConfig.N T (2 * T) : ℝ) with hNdef
  have hRv0 := hRvM T hTR
  have hRv : |N - T * ell1 T / (2 * π)| ≤ |CR| * Real.log T := by
    rw [show T * ell1 T / (2 * π) = T / (2 * π) * ell1 T by ring]
    exact hRv0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hlog1]))
  have htr := htrW (params43.toSetting T) (params43.localFun T) rfl hTt hF N (by
    have e : (params43.toSetting T).T = T := rfl
    rw [e, ← ell1_eq_ell1q T]
    rw [show T * ell1 T / (2 * π) = T / (2 * π) * ell1 T by ring] at hRv
    exact hRv)
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hMlow : T * Real.log T / (4 * π) ≤ T * ell1 T / (2 * π) := by
    have h1 : Real.log T ≤ 2 * ell1 T := by unfold ell1; linarith only [hlo, hc₀]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ T * (2 * π))
    nlinarith only [this, hT0, hπ]
  have hCRlog : |CR| * Real.log T ≤ T * Real.log T / (8 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hTCR (by linarith only [hlog1] : (0:ℝ) ≤ Real.log T)
    linarith only [this]
  have hNlow : T * Real.log T / (8 * π) ≤ N := by
    have h1 := (abs_le.mp hRv).1
    have e : T * Real.log T / (4 * π) = 2 * (T * Real.log T / (8 * π)) := by ring
    linarith only [h1, hMlow, hCRlog, e]
  -- the error budget
  set U := T * Real.log T / (8 * π) with hU
  have hU0 : 0 ≤ U := by positivity
  have hTU : ε' / (256 * π) * T ≤ ε' / 32 * U := by
    rw [hU]
    have : ε' / (256 * π) * T * 1 ≤ ε' / (256 * π) * T * Real.log T :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = ε' / (256 * π) * T * Real.log T := by
      field_simp; ring
    linarith only [this, e]
  have hW : Kpow * (Real.log T ^ 6 * v ^ 11) ≤ ε' / 32 * U := by
    rw [hv11]
    have := hrate
    linarith only [this, hTU, show Kpow * (Real.log T ^ 6 * T ^ (11 / 12 : ℝ))
      = Kpow * Real.log T ^ 6 * T ^ (11 / 12 : ℝ) by ring]
  have hlin : Klin * T ≤ ε' / 32 * U := by
    rw [hU]
    rw [div_le_iff₀ hε'0] at hlK
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = T * (ε' * Real.log T) / (256 * π) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlK hT0.le
    nlinarith only [this]
  have hCRb : Kc * (|CR| * Real.log T) ≤ ε' / 32 * U := by
    rw [hU]
    rw [div_le_iff₀ hε'0] at hTKc
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = (ε' * T) * Real.log T / (256 * π) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hTKc (by linarith only [hlog1] : (0:ℝ) ≤ Real.log T)
    nlinarith only [this]
  have hNIIb : 3 * (NII zetaZeroConfig T : ℝ) ≤ ε' / 32 * U := by
    have h1 : (NII zetaZeroConfig T : ℝ) ≤ |CN| * Real.sqrt T * Real.log T := by
      refine hNIIT.trans ?_
      have hsT := Real.sqrt_nonneg T
      calc CN * Real.sqrt T * Zeta23.l T ≤ |CN| * Real.sqrt T * Zeta23.l T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsT)
              (by linarith only [hl1])
        _ ≤ |CN| * Real.sqrt T * Real.log T :=
            mul_le_mul_of_nonneg_left hhi (mul_nonneg (abs_nonneg _) hsT)
    have h2 : 3 * |CN| * Real.sqrt T ≤ ε' / (256 * π) * T := by
      rw [Real.sqrt_eq_rpow]
      simpa using hrate2
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith only [hlog1] : (0:ℝ) ≤ Real.log T)
    have e : ε' / 32 * U = ε' / (256 * π) * T * Real.log T := by rw [hU]; field_simp; ring
    nlinarith only [h1, h3, e]
  -- the tail parameter
  have hC1T : params43.C1 T ≤ 2 * R := by rw [hRdef]; exact C1_le_fam hP hwL
  have hθ := theta0_le_fam hP (show Tail.T₀ ≤ T by show (300:ℝ) ≤ T; linarith only [hT4096])
    (by linarith only [hA₀]) (Tail.C1_nonneg _ T) hC1T
  have hθ1 : Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T ≤ 1 := by
    have hlam : params43.lam / 2 - 1 = (4 / 3 : ℝ) / 2 - 1 := rfl
    rw [hlam] at hθ
    have hT13 : 0 ≤ T ^ ((4 / 3 : ℝ) / 2 - 1) := by positivity
    have h2 : 32 * A₀ * R ^ 2 * Zeta23.l T * T ^ ((4 / 3 : ℝ) / 2 - 1)
        ≤ 32 * A₀ * R ^ 2 * Real.log T * T ^ ((4 / 3 : ℝ) / 2 - 1) := by
      apply mul_le_mul_of_nonneg_right _ hT13
      exact mul_le_mul_of_nonneg_left hhi (by have := zero_le_one.trans hA₀; positivity)
    simp only [pow_one] at hrate3
    linarith only [hθ, h2, hrate3]
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have haL : 4 ≤ params43.a T * params43.L T := by nlinarith only [ha2, hL8]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T
      / (params43.a T * params43.L T) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have ha0 : 0 < params43.a T := by linarith only [ha2]
    have Htail : Tail.TailHyp zetaZeroConfig params43 T A₀ (params43.C1 T) :=
      { hT := show (300:ℝ) ≤ T by linarith only [hT4096], hL := by linarith only [hL8], hA₀ := hA₀,
        hloc := hloc, hC₁ := Tail.C1_nonneg _ T,
        hdecay := fun r y hy hz => norm_phiHat_sub_I_mul_le_fam hP hwL r y hy hz }
    exact div_nonneg (Htail.tailInputs ha0 (fun z => Params.phiHat_conj z)).theta_nonneg (by positivity)
  have hB1 : B ≤ 1 := by
    rw [hBdef, div_le_one (by positivity)]; linarith only [hθ1, haL]
  have hNbig : 1024 / ε' ^ 2 + 40 / ε' ≤ N := by
    have h1 : 1024 / ε' ^ 2 + 40 / ε' ≤ T / (8 * π) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hTN]
    have h2 : T / (8 * π) ≤ U := by
      rw [hU, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0:ℝ) ≤ T * (8 * π))
      nlinarith only [this]
    linarith only [h1, h2, hNlow]
  have hN0 : 0 ≤ N := by
    have : 0 ≤ 1024 / ε' ^ 2 + 40 / ε' := by positivity
    linarith only [this, hNbig]
  have hBb : B * (4 + 4 * Real.sqrt N + B) ≤ ε / 4 * N := by
    have h1 : B * (4 + 4 * Real.sqrt N + B) ≤ 1 * (4 + 4 * Real.sqrt N + 1) :=
      mul_le_mul hB1 (by linarith only [hB1]) (by positivity) zero_le_one
    have hN40 : 40 / ε' ≤ N := by
      have : 0 ≤ 1024 / ε' ^ 2 := by positivity
      linarith only [this, hNbig]
    have hN1024 : 1024 / ε' ^ 2 ≤ N := by
      have : 0 ≤ 40 / ε' := by positivity
      linarith only [this, hNbig]
    have h5 : 5 ≤ ε' / 8 * N := by
      rw [div_le_iff₀ hε'0] at hN40; nlinarith only [hN40]
    have h6 : 4 * Real.sqrt N ≤ ε' / 8 * N := by
      have hsN : 32 / ε' ≤ Real.sqrt N := by
        rw [Real.le_sqrt (by positivity) hN0]
        have e : (32 / ε') ^ 2 = 1024 / ε' ^ 2 := by field_simp; norm_num
        rw [e]; exact hN1024
      have hsN0 := Real.sqrt_nonneg N
      have hNsq : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0).symm
      rw [div_le_iff₀ hε'0] at hsN
      nlinarith only [hsN, hNsq, hsN0, hε'0]
    have h7 : ε' / 4 * N ≤ ε / 4 * N := mul_le_mul_of_nonneg_right (by linarith only [hε'ε]) hN0
    linarith only [h1, h5, h6, h7]
  -- the four budget inequalities
  have hcoef : 43 / 36 + ε' / 2 + 32 * π * ε₁ ≤ Kc := by rw [hKc]; linarith only [hε'1]
  have hCRlog0 : 0 ≤ |CR| * Real.log T := by have := abs_nonneg CR; nlinarith only [this, hlog1]
  have hcoefb : (43 / 36 + ε' / 2 + 32 * π * ε₁) * (|CR| * Real.log T) ≤ Kc * (|CR| * Real.log T) :=
    mul_le_mul_of_nonneg_right hcoef hCRlog0
  have hUN : ε' / 32 * U ≤ ε' / 32 * N := mul_le_mul_of_nonneg_left hNlow (by positivity)
  have hε'N : ε' / 8 * N ≤ ε / 4 * N := mul_le_mul_of_nonneg_right (by linarith only [hε'ε, hε]) hN0
  have hN10 : ε' / 32 * N ≤ N / 32 := by
    have := mul_le_mul_of_nonneg_right hε'1 hN0; linarith only [this]
  have hKpowW : Kpow * (Real.log T ^ 6 * v ^ 11)
      = 4 * (traceConst cr Kq Ct * Real.log T ^ 6 * v ^ 11)
        + (chanConst cr ℓ₀ K |C1| |Cψ| Mk + gridConst cr ℓ₀ ε₁ C₀ |C1| |Cψ|) * Real.log T ^ 6 * v ^ 11 := by
    rw [hKpow]; ring
  have hKlinT : Klin * T = 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T) + (|CΓ| + 2 * |C2|) * T := by
    rw [hKlin]; ring
  have hE : 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K |C1| |Cψ| Mk + gridConst params43.crho ℓ₀ ε₁ C₀ |C1| |Cψ|)
            * Real.log T ^ 6 * v ^ 11)
        + (43 / 36 + ε' / 2 + 32 * π * ε₁) * (|CR| * Real.log T) + 3 * (NII zetaZeroConfig T : ℝ)
      ≤ ε / 4 * N := by
    linarith only [hKpowW, hKlinT, hW, hlin, hcoefb, hCRb, hNIIb, hUN, hε'N]
  have hEf : (|CΓ| + 2 * |C2|) * T
        + (chanConst params43.crho ℓ₀ K |C1| |Cψ| Mk + gridConst params43.crho ℓ₀ ε₁ C₀ |C1| |Cψ|)
          * Real.log T ^ 6 * v ^ 11 ≤ N / 10 := by
    have h4 : 0 ≤ 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T) := by positivity
    have h5 : 0 ≤ 4 * (traceConst cr Kq Ct * Real.log T ^ 6 * v ^ 11) := by
      have : 0 ≤ traceConst cr Kq Ct := by unfold traceConst; positivity
      have : 0 ≤ Real.log T := by linarith only [hlog1]
      positivity
    linarith only [hKpowW, hKlinT, hW, hlin, hUN, hN10, h4, h5, hN0]
  have hE₀ : |CR| * Real.log T ≤ N / 10 := by
    have : |CR| * Real.log T ≤ Kc * (|CR| * Real.log T) := le_mul_of_one_le_left hCRlog0 hKc1
    linarith only [this, hCRb, hUN, hN10, hN0]
  -- the certificate
  have hcert := certificate_at hF (show Tail.T₀ ≤ T by show (300:ℝ) ≤ T; linarith only [hT4096]) hwL hA₀
    hloc hu hℓ₀ hlip hℓ1 hε₁T hK0 hK hKq0 hKq hμl' (by linarith only [hC₀1]) hμ hν (abs_nonneg C1)
    (abs_nonneg Cψ) hMk0 hMk hk2 hηk hv2 hvT hlog1 hhi hL hLc hsX hA hψ' hS hε'0 hε'1 hε'ε hl14 hΓ hC2 ha
    hCt htr hRv (abs_nonneg CR) (η := η) (hE := hE) (hB := by rw [← hBdef]; exact hBb) hEf hE₀
  rw [zetaZeroConfig_N, zetaZeroConfig_N0star] at hcert
  exact hcert

/-- **Open problem 2: the bandwidth-`4/3` certificate localized to the coalescent band.** For every
`ε > 0` and `η > 0` there is a smooth window profile `u` such that for all large `T`
`N₀*(T, 2T) ≥ (29/36 − ε) N(T, 2T) − coalescentSurplus u η T`. -/
theorem zeta_coalescent_certificate {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) - coalescentSurplus u η T ≤ (N0star T (2 * T) : ℝ) := by
  have hπ := Real.pi_pos
  set ε₁ := min (ε / (64 * π)) (1 / 8) with hε₁
  have h0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have h1 : ε₁ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨u, hu⟩ := exists_windowProfile h0 h1
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [zeta_coalescent_certificate_four_thirds hu hη (by positivity : (0:ℝ) < ε / 2)]
    with T hT
  have hN : (0:ℝ) ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : 32 * π * ε₁ ≤ ε / 2 := by
    have : ε₁ ≤ ε / (64 * π) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 32 * π)
    have e : 32 * π * (ε / (64 * π)) = ε / 2 := by field_simp; ring
    linarith
  have h3 : (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) ≤ (29 / 36 - 32 * π * ε₁ - ε / 2) * (Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
