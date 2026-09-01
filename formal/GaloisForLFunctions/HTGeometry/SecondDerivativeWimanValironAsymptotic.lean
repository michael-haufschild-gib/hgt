import GaloisForLFunctions.HTGeometry.SecondDerivativeWimanValironRadius
import GaloisForLFunctions.HTGeometry.WimanValironSmallWindow
import GaloisForLFunctions.HTGeometry.WimanValironAsymptotic

/-!
# The order-two Wiman--Valiron asymptotic

The parameter tying, the small-window bound and the Borel selection of the order-one asymptotic,
carried through with the order-two conclusion alongside.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- **The second-moment constant is polynomial in the sampling scale.** -/
theorem wv_second_moment_le {N : ℕ} {L s K : ℝ} (hs : (100 : ℝ) ≤ s)
    (hK : K = 3 * Real.log s) (hL : L = s ^ 2 / K)
    (hN2 : 2 * s ≤ (N : ℝ)) (hN4 : (N : ℝ) ≤ 4 * s) :
    wvSecondMomentBound N L ≤ 148 * (s ^ 2 * Real.sqrt s) := by
  obtain ⟨hden, -, htail⟩ := wv_tail_ratios_le_one hs hK hL hN2 hN4
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt s := Real.one_le_sqrt.mpr hs1
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- the first summand
  have hroot : Real.sqrt (2 * (N : ℝ) + 1) ≤ 3 * Real.sqrt s := by
    have hle : 2 * (N : ℝ) + 1 ≤ 9 * s := by nlinarith [hN4, hs1]
    calc Real.sqrt (2 * (N : ℝ) + 1) ≤ Real.sqrt (9 * s) := Real.sqrt_le_sqrt hle
      _ = 3 * Real.sqrt s := by
          rw [show (9 : ℝ) * s = 3 ^ 2 * s by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
  have hfirst : (N : ℝ) ^ 2 * Real.sqrt (2 * (N : ℝ) + 1) ≤ 48 * (s ^ 2 * Real.sqrt s) := by
    have hN2s : (N : ℝ) ^ 2 ≤ 16 * s ^ 2 := by nlinarith [hN4, hNnn, hs0]
    nlinarith [hroot, hN2s, Real.sqrt_nonneg s, sq_nonneg ((N : ℝ))]
  -- the tail summand
  have hsecond : 2 * (2 * ((N : ℝ) + 1) ^ 2
      * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3)
      ≤ 100 * (s ^ 2 * Real.sqrt s) := by
    have hfac : 2 * ((N : ℝ) + 1) ^ 2
        * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3
        = (2 * ((N : ℝ) + 1) ^ 2)
          * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
            / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3) := by ring
    rw [hfac]
    have hNsq : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) ^ 2 := by positivity
    have hstep : (2 * ((N : ℝ) + 1) ^ 2)
        * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ 3)
        ≤ 2 * ((N : ℝ) + 1) ^ 2 := by
      nlinarith [htail, hNsq]
    have hbig : 2 * ((N : ℝ) + 1) ^ 2 ≤ 50 * (s ^ 2 * Real.sqrt s) := by
      have h1 : ((N : ℝ) + 1) ^ 2 ≤ 25 * s ^ 2 := by nlinarith [hN4, hNnn, hs1]
      nlinarith [h1, hsqrt1, sq_nonneg s, hs0]
    linarith
  rw [wvSecondMomentBound]
  linarith

set_option maxHeartbeats 800000 in
/-- **Both estimates with the free parameters tied together.** -/
theorem exists_radius_point_secondDeriv_bound
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hs : 0 < s)
    (hLdef : L = 2 * s / H) (hhdef : h = H / 2)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN2s : 2 * s ≤ (N : ℝ)) (hN4s : (N : ℝ) ≤ 4 * s) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ wvClosedBound a x N L h ∧
      ‖z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z
          - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
        ≤ wvSecondMomentBound N L
          + (2 * (centralIndex a (Real.exp x) : ℝ) + 1) * wvClosedBound a x N L h := by
  subst hLdef
  subst hhdef
  have hHne : H ≠ 0 := ne_of_gt hH
  have hN0 : 0 < N := by
    by_contra hcon
    have hN : N = 0 := by omega
    rw [hN] at hN2s
    simp at hN2s
    linarith
  refine exists_radius_point_secondDeriv_le_closed ha hn₀ (v₀ := H / 2)
    hcd hH (by positivity) hs (by positivity) ?_ (by positivity) le_rfl (by linarith) hsmall
    hN0 ?_ ?_
  · have heq : 2 * s / H * (H / 2) = s := by field_simp
    exact le_of_eq heq.symm
  · calc 2 * (2 * s / H) * (H / 2) = 2 * s := by field_simp
      _ ≤ (N : ℝ) := hN2s
  · calc (N : ℝ) ≤ 4 * s := hN4s
      _ = 2 * (2 * s / H) * H := by
          field_simp
          norm_num

set_option maxHeartbeats 1000000 in
/-- **Both estimates at a logarithmic window of width `6 (log s)/s`.** -/
theorem exists_radius_point_secondDeriv_small_window
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d s : ℝ}
    (hcd : c ≤ d) (hs : (100 : ℝ) ≤ s)
    (hsmall : 2 * (2 * (3 * Real.log s) / s)
        * ((centralIndex a (Real.exp (d + 2 * (2 * (3 * Real.log s) / s))) : ℝ)
          - (centralIndex a (Real.exp c) : ℝ)) / s < d - c) :
    ∃ x ∈ Set.Icc (c + 2 * (3 * Real.log s) / s) (d + 2 * (3 * Real.log s) / s), ∃ z : ℂ,
      ‖z‖ = Real.exp x ∧ maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ 30 * (s * Real.sqrt s)
            * (1 + Real.log ((centralIndex a (Real.exp x) : ℝ) + 4 * s) / Real.log s) ∧
      ‖z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z
          - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
        ≤ 148 * (s ^ 2 * Real.sqrt s)
          + (2 * (centralIndex a (Real.exp x) : ℝ) + 1)
            * (30 * (s * Real.sqrt s)
              * (1 + Real.log ((centralIndex a (Real.exp x) : ℝ) + 4 * s) / Real.log s)) := by
  have hs0 : (0 : ℝ) < s := by linarith
  set K : ℝ := 3 * Real.log s with hKdef
  have hlogs : (4 : ℝ) ≤ Real.log s := by
    have hlog : Real.log 100 ≤ Real.log s := Real.log_le_log (by norm_num) hs
    have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
      have he : Real.exp 4 ≤ 100 := by
        have h2 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
        calc Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 4
          _ ≤ 100 := by norm_num
      have := Real.log_le_log (Real.exp_pos 4) he
      rwa [Real.log_exp] at this
    linarith
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; linarith
  set H : ℝ := 2 * K / s with hHdef
  have hH : (0 : ℝ) < H := by rw [hHdef]; positivity
  set N : ℕ := ⌈2 * s⌉₊ with hNdef
  have hN2 : 2 * s ≤ (N : ℝ) := Nat.le_ceil _
  have hN4 : (N : ℝ) ≤ 4 * s := by
    have h1 : (N : ℝ) < 2 * s + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one (by positivity)
    linarith
  obtain ⟨x, hx, z, hz, hfz, hbound, h2bound⟩ :=
    exists_radius_point_secondDeriv_bound ha hn₀ hcd hH hs0 rfl rfl hsmall hN2 hN4
  have hL : 2 * s / H = s ^ 2 / K := by rw [hHdef]; field_simp
  have hh : H / 2 = K / s := by rw [hHdef]; field_simp
  have hone : wvClosedBound a x N (2 * s / H) (H / 2)
      ≤ 30 * (s * Real.sqrt s)
        * (1 + Real.log ((centralIndex a (Real.exp x) : ℝ) + 4 * s) / Real.log s) := by
    rw [wvClosedBound]
    exact wv_rhs_le hs hKdef hL hh hN2 hN4 (Nat.cast_nonneg _)
  have htwo : wvSecondMomentBound N (2 * s / H) ≤ 148 * (s ^ 2 * Real.sqrt s) :=
    wv_second_moment_le hs hKdef hL hN2 hN4
  have hνnn : (0 : ℝ) ≤ 2 * (centralIndex a (Real.exp x) : ℝ) + 1 := by positivity
  refine ⟨x, hx, z, hz, hfz, le_trans hbound hone, le_trans h2bound ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hone hνnn
  linarith

/-- **The second-moment constant is below `ε/2` times the squared central index.** -/
theorem wv_second_error_le {w eps nu : ℝ} (hw : (40 : ℝ) ≤ w) (heps : 0 < eps)
    (hweps : 1184 / eps ≤ w ^ 40) (hlow : w ^ 100 / 2 ≤ nu) :
    148 * ((w ^ 64) ^ 2 * Real.sqrt (w ^ 64)) ≤ eps / 2 * nu ^ 2 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hsqrt : Real.sqrt (w ^ 64) = w ^ 32 := by
    rw [show w ^ 64 = (w ^ 32) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hLHS : 148 * ((w ^ 64) ^ 2 * Real.sqrt (w ^ 64)) = 148 * w ^ 160 := by
    rw [hsqrt]; ring
  have h160 : (0 : ℝ) < w ^ 160 := by positivity
  have hkey : 1184 * w ^ 160 ≤ eps * w ^ 200 := by
    have h1 : 1184 / eps * w ^ 160 ≤ w ^ 40 * w ^ 160 :=
      mul_le_mul_of_nonneg_right hweps h160.le
    have h2 : w ^ 40 * w ^ 160 = w ^ 200 := by ring
    rw [h2] at h1
    have h3 : eps * (1184 / eps * w ^ 160) = 1184 * w ^ 160 := by field_simp
    nlinarith [h1, heps]
  have hnupos : (0 : ℝ) < nu := by
    have : (0 : ℝ) < w ^ 100 := by positivity
    linarith
  have hnu2 : w ^ 200 / 4 ≤ nu ^ 2 := by
    have h1 : (0 : ℝ) < w ^ 100 := by positivity
    nlinarith [hlow, h1, hnupos]
  rw [hLHS]
  nlinarith [hkey, hnu2, heps.le, h160]

set_option maxHeartbeats 1000000 in
/-- **The order-two Wiman--Valiron asymptotic.**  For a transcendental entire function, at
arbitrarily large radii there is a point of the maximum circle at which `z f′/f` agrees with the
central index and `z² f″/f` with its falling factorial, to any prescribed relative accuracy. -/
theorem exists_radius_point_secondDeriv_close_centralIndex
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {eps : ℝ} (heps : 0 < eps) (R : ℝ) :
    ∃ x, R ≤ x ∧ ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) ∧
      ‖z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z
          - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
        ≤ eps * (centralIndex a (Real.exp x) : ℝ) ^ 2 := by
  classical
  have heps6 : (0 : ℝ) < eps / 6 := by linarith
  -- the scale threshold
  set w₀ : ℝ := max 40 (max ((155 / (eps / 6)) ^ ((1 : ℝ) / 4))
    ((1184 / eps) ^ ((1 : ℝ) / 40))) with hw₀def
  have hw₀40 : (40 : ℝ) ≤ w₀ := le_max_left _ _
  have hw₀0 : (0 : ℝ) < w₀ := by linarith
  have hw₀eps : 155 / (eps / 6) ≤ w₀ ^ 4 := by
    have hge : ((155 / (eps / 6)) ^ ((1 : ℝ) / 4)) ≤ w₀ :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hnn : (0 : ℝ) ≤ 155 / (eps / 6) := by positivity
    have hpow : ((155 / (eps / 6)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = 155 / (eps / 6) := by
      rw [← Real.rpow_natCast ((155 / (eps / 6)) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hnn]
      norm_num
    calc 155 / (eps / 6) = ((155 / (eps / 6)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hpow.symm
      _ ≤ w₀ ^ 4 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hge 4
  have hw₀eps2 : 1184 / eps ≤ w₀ ^ 40 := by
    have hge : ((1184 / eps) ^ ((1 : ℝ) / 40)) ≤ w₀ :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hnn : (0 : ℝ) ≤ 1184 / eps := by positivity
    have hpow : ((1184 / eps) ^ ((1 : ℝ) / 40)) ^ (40 : ℕ) = 1184 / eps := by
      rw [← Real.rpow_natCast ((1184 / eps) ^ ((1 : ℝ) / 40)) 40, ← Real.rpow_mul hnn]
      norm_num
    calc 1184 / eps = ((1184 / eps) ^ ((1 : ℝ) / 40)) ^ (40 : ℕ) := hpow.symm
      _ ≤ w₀ ^ 40 := pow_le_pow_left₀ (Real.rpow_nonneg hnn _) hge 40
  -- a radius beyond which the central index exceeds the threshold
  have htop : Filter.Tendsto (fun x : ℝ => centralIndex a (Real.exp x)) Filter.atTop
      Filter.atTop := (tendsto_centralIndex_atTop ha htrans).comp Real.tendsto_exp_atTop
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop ⌈w₀ ^ (100 : ℕ)⌉₊)
  have hR₁' : ∀ x : ℝ, R₁ ≤ x → w₀ ^ (100 : ℕ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
    intro x hx
    have h := hR₁ x hx
    have hcast : ((⌈w₀ ^ (100 : ℕ)⌉₊ : ℕ) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) := by
      exact_mod_cast h
    exact le_trans (Nat.le_ceil _) hcast
  -- Borel selection
  set Tlog : ℝ → ℝ := fun y => (centralIndex a (Real.exp y) : ℝ) + 1 with hTdef
  have hTmono : Monotone Tlog := by
    intro p q hpq
    have := monotone_centralIndex_exp ha hn₀ hpq
    rw [hTdef]
    simpa using this
  have hT1 : ∀ y, 1 ≤ Tlog y := by
    intro y
    rw [hTdef]
    have : (0 : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨x, hxR, hborel⟩ :=
    Nevanlinna.exists_ge_lt_two_mul_rpow hTmono hT1 (by norm_num : (0:ℝ) < 1/4) (max R R₁)
  have hxR0 : R ≤ x := le_trans (le_max_left _ _) hxR
  have hxR1 : R₁ ≤ x := le_trans (le_max_right _ _) hxR
  set T₀ : ℝ := Tlog x with hT₀def
  have hT₀0 : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (hT1 x)
  set w : ℝ := T₀ ^ ((1 : ℝ) / 100) with hwdef
  have hw100 : w ^ (100 : ℕ) = T₀ := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 100, ← Real.rpow_mul hT₀0.le]
    norm_num
  have hT₀big : w₀ ^ (100 : ℕ) ≤ T₀ := by
    have := hR₁' x hxR1
    rw [hT₀def, hTdef]
    linarith
  have hwpos : (0 : ℝ) < w := by
    rw [hwdef]
    exact Real.rpow_pos_of_pos hT₀0 _
  have hw₀w : w₀ ≤ w := by
    by_contra hcon
    push Not at hcon
    have hlt : w ^ (100 : ℕ) < w₀ ^ (100 : ℕ) :=
      pow_lt_pow_left₀ hcon hwpos.le (by norm_num)
    rw [hw100] at hlt
    linarith [hT₀big]
  have hw40 : (40 : ℝ) ≤ w := le_trans hw₀40 hw₀w
  have hweps : 155 / (eps / 6) ≤ w ^ 4 := by
    refine le_trans hw₀eps ?_
    exact pow_le_pow_left₀ hw₀0.le hw₀w 4
  have hweps2 : 1184 / eps ≤ w ^ 40 := by
    refine le_trans hw₀eps2 ?_
    exact pow_le_pow_left₀ hw₀0.le hw₀w 40
  -- the Borel step length
  have hw25 : w ^ (25 : ℕ) = T₀ ^ ((1 : ℝ) / 4) := by
    rw [hwdef, ← Real.rpow_natCast (T₀ ^ ((1 : ℝ) / 100)) 25, ← Real.rpow_mul hT₀0.le]
    norm_num
  set δ : ℝ := T₀ ^ (-((1 : ℝ) / 4)) with hδdef
  have hδ25 : δ = (w ^ (25 : ℕ))⁻¹ := by
    rw [hδdef, hw25, ← Real.rpow_neg hT₀0.le]
  have hδ0 : (0 : ℝ) < δ := by
    rw [hδ25]
    positivity
  have hνδ : (centralIndex a (Real.exp (x + δ)) : ℝ) < 2 * T₀ - 1 := by
    have h := hborel
    rw [hTdef] at h
    simp only at h
    linarith [h]
  -- the parameters
  set s : ℝ := w ^ (64 : ℕ) with hsdef
  have hs100 : (100 : ℝ) ≤ s := by
    have h2 : (100 : ℝ) ≤ w ^ 2 := by nlinarith [hw40]
    have h64 : w ^ 2 ≤ w ^ 64 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hsdef]
    linarith
  set Hw : ℝ := 2 * (3 * Real.log s) / s with hHdef
  have hHle : Hw ≤ δ / 4 := by
    rw [hHdef, hsdef, hδ25]
    exact wv_window_le hw40
  have hHpos : (0 : ℝ) < Hw := by
    rw [hHdef, hsdef]
    have hlog : (0 : ℝ) < Real.log (w ^ (64 : ℕ)) := by
      rw [Real.log_pow]
      have : (3 : ℝ) ≤ Real.log w := (wv_scale_facts hw40).2.1
      positivity
    positivity
  have hmono := monotone_centralIndex_exp ha hn₀
  -- the selection condition
  have hsmall : 2 * (2 * (3 * Real.log s) / s)
      * ((centralIndex a (Real.exp (x + δ / 2 + 2 * (2 * (3 * Real.log s) / s))) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ)) / s < x + δ / 2 - x := by
    have hle : x + δ / 2 + 2 * Hw ≤ x + δ := by linarith
    have hν1 : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) := hmono hle
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]
      ring
    have hΔ : (centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
        - (centralIndex a (Real.exp x) : ℝ) ≤ w ^ (100 : ℕ) := by
      rw [hνx, hw100]
      linarith [hν1, hνδ]
    have hstep : 2 * Hw * ((centralIndex a (Real.exp (x + δ / 2 + 2 * Hw)) : ℝ)
          - (centralIndex a (Real.exp x) : ℝ)) / s
        ≤ 2 * Hw * w ^ (100 : ℕ) / s := by
      refine div_le_div_of_nonneg_right ?_ (by linarith : (0:ℝ) ≤ s)
      exact mul_le_mul_of_nonneg_left hΔ (by linarith)
    have hkey : 2 * Hw * w ^ (100 : ℕ) / s < δ / 2 := by
      rw [hHdef, hsdef, hδ25]
      exact wv_selection_lt hw40
    have hrw : x + δ / 2 - x = δ / 2 := by ring
    rw [hrw, ← hHdef]
    linarith [hstep, hkey]
  -- apply the narrow-window estimate
  obtain ⟨y, hy, z, hz, hfz, hbound, h2bound⟩ :=
    exists_radius_point_secondDeriv_small_window ha hn₀ (by linarith : x ≤ x + δ / 2)
      hs100 (by rw [hsdef] at hsmall ⊢; exact hsmall)
  rw [← hHdef] at hy
  have hy1 : x ≤ y := by
    have := hy.1
    linarith
  have hy2 : y ≤ x + δ := by
    have := hy.2
    linarith
  have hνlow : w ^ (100 : ℕ) / 2 ≤ (centralIndex a (Real.exp y) : ℝ) := by
    have h1 : (centralIndex a (Real.exp x) : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := hmono hy1
    have hνx : (centralIndex a (Real.exp x) : ℝ) = T₀ - 1 := by
      rw [hT₀def, hTdef]; ring
    have h2 : (2 : ℝ) ≤ w ^ (100 : ℕ) := by
      have : (2 : ℝ) ≤ w := by linarith
      calc (2 : ℝ) ≤ w := this
        _ = w ^ (1 : ℕ) := by ring
        _ ≤ w ^ (100 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [hνx] at h1
    rw [hw100] at h2
    rw [hw100]
    linarith
  have hνhigh : (centralIndex a (Real.exp y) : ℝ) ≤ 2 * w ^ (100 : ℕ) := by
    have h1 : (centralIndex a (Real.exp y) : ℝ) ≤ (centralIndex a (Real.exp (x + δ)) : ℝ) :=
      hmono hy2
    rw [hw100]
    linarith [hνδ]
  have hν1 : (1 : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) := by
    have h2 : (2 : ℝ) ≤ w ^ (100 : ℕ) := by
      have : (2 : ℝ) ≤ w := by linarith
      calc (2 : ℝ) ≤ w := this
        _ = w ^ (1 : ℕ) := by ring
        _ ≤ w ^ (100 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith [hνlow]
  have herr : 30 * (s * Real.sqrt s)
      * (1 + Real.log ((centralIndex a (Real.exp y) : ℝ) + 4 * s) / Real.log s)
      ≤ eps / 6 * (centralIndex a (Real.exp y) : ℝ) := by
    rw [hsdef]
    exact wv_error_le hw40 heps6 hweps hνlow hνhigh
  have hsec : 148 * (s ^ 2 * Real.sqrt s)
      ≤ eps / 2 * (centralIndex a (Real.exp y) : ℝ) ^ 2 := by
    rw [hsdef]
    exact wv_second_error_le hw40 heps hweps2 hνlow
  refine ⟨y, le_trans hxR0 hy1, z, hz, hfz, ?_, ?_⟩
  · refine le_trans hbound (le_trans herr ?_)
    nlinarith [hν1, heps]
  · refine le_trans h2bound ?_
    have hνnn : (0 : ℝ) ≤ 2 * (centralIndex a (Real.exp y) : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left herr hνnn
    have hνsq : (0 : ℝ) ≤ (centralIndex a (Real.exp y) : ℝ) ^ 2
        - (centralIndex a (Real.exp y) : ℝ) := by nlinarith [hν1]
    have hprod : (0 : ℝ) ≤ eps / 6 * ((centralIndex a (Real.exp y) : ℝ) ^ 2
        - (centralIndex a (Real.exp y) : ℝ)) := mul_nonneg (by linarith) hνsq
    have hstep : (2 * (centralIndex a (Real.exp y) : ℝ) + 1)
        * (eps / 6 * (centralIndex a (Real.exp y) : ℝ))
        ≤ eps / 2 * (centralIndex a (Real.exp y) : ℝ) ^ 2 := by nlinarith [hprod]
    linarith [hsec, hmul, hstep]

end GaloisForLFunctions.HTGeometry
