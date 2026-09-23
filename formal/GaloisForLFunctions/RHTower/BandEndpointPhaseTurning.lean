import GaloisForLFunctions.RHTower.BandEndpointPhase

/-!
# The band phase at the turning scale

The leakage ladder needs the size of `1 − Ξ_s(2√s)` as `s → 0`, where
`Ξ_s(y) = ∫_{arcsin y}^{π/2} √(sin²θ − s) dθ` is the band phase and `Ξ_0(0) = 1`.

The whole content is the elementary integral `∫ dθ/sin θ`, whose antiderivative is
`½·log((1+cos θ)/(1−cos θ))`.  Splitting the defect `sin θ − √(sin²θ − s)` at a point where
`sin θ = K√s`:

* below the split the defect is at most `sin θ`, and the interval is short, contributing `O(K²s)`;
* above it `√(sin²θ − s) ≥ √(1 − K⁻²)·sin θ`, so the defect is at most
  `s/(2√(1−K⁻²)·sin θ)`, and the logarithmic integral contributes
  `(s/(2√(1−K⁻²)))·(½ log(1/s) + log 2 − log K)`.

Letting `K` grow makes the coefficient of `s·log(1/s)` approach the sharp `1/4`.
-/

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- An antiderivative of `−1/sin` on `(0, π)`. -/
def invSinAntideriv (θ : ℝ) : ℝ :=
  (Real.log (1 + Real.cos θ) - Real.log (1 - Real.cos θ)) / 2

theorem invSinAntideriv_pi_div_two : invSinAntideriv (Real.pi / 2) = 0 := by
  rw [invSinAntideriv, Real.cos_pi_div_two]
  norm_num

theorem hasDerivAt_invSinAntideriv {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi) :
    HasDerivAt invSinAntideriv (-(1 / Real.sin θ)) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 h1
  have hcsq : Real.cos θ ^ (2 : ℕ) < 1 := by nlinarith [Real.sin_sq_add_cos_sq θ, hs]
  have hc1 : Real.cos θ < 1 := by nlinarith [hcsq]
  have hcm1 : -1 < Real.cos θ := by nlinarith [hcsq]
  have hA : (0 : ℝ) < 1 + Real.cos θ := by linarith
  have hB : (0 : ℝ) < 1 - Real.cos θ := by linarith
  have hcos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have h1' : HasDerivAt (fun x => Real.log (1 + Real.cos x))
      ((-Real.sin θ) / (1 + Real.cos θ)) θ := by
    have hd : HasDerivAt (fun x => 1 + Real.cos x) (-Real.sin θ) θ := by
      simpa using hcos.const_add 1
    simpa using hd.log (ne_of_gt hA)
  have h2' : HasDerivAt (fun x => Real.log (1 - Real.cos x))
      (Real.sin θ / (1 - Real.cos θ)) θ := by
    have hd : HasDerivAt (fun x => 1 - Real.cos x) (Real.sin θ) θ := by
      simpa using hcos.const_sub 1
    simpa using hd.log (ne_of_gt hB)
  have h := (h1'.sub h2').div_const 2
  refine h.congr_deriv ?_
  have hsq : Real.sin θ ^ (2 : ℕ) = (1 + Real.cos θ) * (1 - Real.cos θ) := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  field_simp
  nlinarith [hsq, hs]

theorem continuousOn_inv_sin {θ₀ : ℝ} (h0 : 0 < θ₀) (h1 : θ₀ ≤ Real.pi / 2) :
    ContinuousOn (fun θ : ℝ => 1 / Real.sin θ) (uIcc θ₀ (Real.pi / 2)) := by
  refine ContinuousOn.div continuousOn_const Real.continuous_sin.continuousOn fun θ hθ => ?_
  rw [uIcc_of_le h1] at hθ
  have hθ0 : 0 < θ := lt_of_lt_of_le h0 hθ.1
  have hθπ : θ < Real.pi := by
    have := hθ.2
    have hpi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
    linarith
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)

/-- **The elementary logarithmic integral.** -/
theorem integral_inv_sin {θ₀ : ℝ} (h0 : 0 < θ₀) (h1 : θ₀ ≤ Real.pi / 2) :
    (∫ θ in θ₀..(Real.pi / 2), 1 / Real.sin θ) = invSinAntideriv θ₀ := by
  have hderiv : ∀ θ ∈ uIcc θ₀ (Real.pi / 2),
      HasDerivAt (fun x => -invSinAntideriv x) (1 / Real.sin θ) θ := by
    intro θ hθ
    rw [uIcc_of_le h1] at hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le h0 hθ.1
    have hθπ : θ < Real.pi := by
      have := hθ.2
      have hpi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
      linarith
    have h := (hasDerivAt_invSinAntideriv hθ0 hθπ).neg
    refine h.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun θ : ℝ => 1 / Real.sin θ) MeasureTheory.volume
      θ₀ (Real.pi / 2) :=
    (continuousOn_inv_sin h0 h1).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h, invSinAntideriv_pi_div_two]
  ring

/-- **The logarithmic integral, bounded by the split height.** -/
theorem integral_inv_sin_le {θ₀ : ℝ} (h0 : 0 < θ₀) (h1 : θ₀ ≤ Real.pi / 2) :
    (∫ θ in θ₀..(Real.pi / 2), 1 / Real.sin θ)
      ≤ Real.log 2 - Real.log (Real.sin θ₀) := by
  rw [integral_inv_sin h0 h1]
  have hs : 0 < Real.sin θ₀ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hc1 : Real.cos θ₀ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ₀, hs, Real.cos_le_one θ₀]
  have hcm1 : -1 < Real.cos θ₀ := by
    nlinarith [Real.sin_sq_add_cos_sq θ₀, hs, Real.neg_one_le_cos θ₀]
  have hA : (0 : ℝ) < 1 + Real.cos θ₀ := by linarith
  have hB : (0 : ℝ) < 1 - Real.cos θ₀ := by linarith
  have hsq : Real.sin θ₀ ^ (2 : ℕ) = (1 + Real.cos θ₀) * (1 - Real.cos θ₀) := by
    nlinarith [Real.sin_sq_add_cos_sq θ₀]
  have hle : (1 : ℝ) + Real.cos θ₀ ≤ 2 := by linarith [Real.cos_le_one θ₀]
  have hkey : Real.log (1 + Real.cos θ₀) - Real.log (1 - Real.cos θ₀)
      ≤ 2 * (Real.log 2 - Real.log (Real.sin θ₀)) := by
    have hlogsq : Real.log (Real.sin θ₀ ^ (2 : ℕ))
        = Real.log (1 + Real.cos θ₀) + Real.log (1 - Real.cos θ₀) := by
      rw [hsq, Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
    have hlogsq' : Real.log (Real.sin θ₀ ^ (2 : ℕ)) = 2 * Real.log (Real.sin θ₀) := by
      rw [Real.log_pow]
      push_cast
      ring
    have hlog2 : Real.log (1 + Real.cos θ₀) ≤ Real.log 2 :=
      Real.log_le_log hA hle
    linarith [hlogsq, hlogsq', hlog2]
  rw [invSinAntideriv]
  linarith

/-! ## The defect above the split -/

/-- **The phase defect above the split height.**  Where `sin θ ≥ K√s` the square root is within a
factor `√(1 − K⁻²)` of `sin θ`, so the defect is at most `s/(2√(1−K⁻²)·sin θ)`. -/
theorem sin_sub_sqrt_le {s K u : ℝ} (hs : 0 < s) (hK : 2 ≤ K) (hu : K * Real.sqrt s ≤ u) :
    u - Real.sqrt (u ^ (2 : ℕ) - s) ≤ s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) * u) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hKu : K ^ (2 : ℕ) * s ≤ u ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hu (le_of_lt (by positivity : (0:ℝ) < K * Real.sqrt s))
    have hsqs : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    nlinarith [hu, hsq0, hK0, hsqs]
  have hfrac : (1 : ℝ) - 1 / K ^ (2 : ℕ) ≥ 0 := by
    have : (1 : ℝ) ≤ K ^ (2 : ℕ) := by nlinarith
    have hK2 : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
    rw [ge_iff_le, sub_nonneg, div_le_one hK2]
    exact this
  have hfracpos : (0 : ℝ) < 1 - 1 / K ^ (2 : ℕ) := by
    have hK2 : (4 : ℝ) ≤ K ^ (2 : ℕ) := by nlinarith
    have hK2p : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
    rw [sub_pos, div_lt_one hK2p]
    linarith
  have hrt : 0 < Real.sqrt (1 - 1 / K ^ (2 : ℕ)) := Real.sqrt_pos.2 hfracpos
  have hrt1 : Real.sqrt (1 - 1 / K ^ (2 : ℕ)) ≤ 1 := by
    have hinvpos : (0 : ℝ) ≤ 1 / K ^ (2 : ℕ) := by positivity
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) - 1 / K ^ (2 : ℕ) ≤ 1 by linarith)
    rwa [Real.sqrt_one] at h
  have hnn : 0 ≤ u ^ (2 : ℕ) - s := by
    have hK2 : (4 : ℝ) ≤ K ^ (2 : ℕ) := by nlinarith
    nlinarith [hKu]
  set v : ℝ := Real.sqrt (u ^ (2 : ℕ) - s) with hvdef
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hvsq : v ^ (2 : ℕ) = u ^ (2 : ℕ) - s := Real.sq_sqrt hnn
  have hvu : u * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) ≤ v := by
    have hkey : (u * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) ^ (2 : ℕ) ≤ u ^ (2 : ℕ) - s := by
      have hsqsq : Real.sqrt (1 - 1 / K ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - 1 / K ^ (2 : ℕ) := Real.sq_sqrt hfrac
      have hK2p : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
      have : u ^ (2 : ℕ) * (1 - 1 / K ^ (2 : ℕ)) ≤ u ^ (2 : ℕ) - s := by
        rw [mul_sub, mul_one]
        have : s ≤ u ^ (2 : ℕ) / K ^ (2 : ℕ) := by
          rw [le_div_iff₀ hK2p]
          linarith [hKu]
        have heq : u ^ (2 : ℕ) * (1 / K ^ (2 : ℕ)) = u ^ (2 : ℕ) / K ^ (2 : ℕ) := by ring
        linarith [heq]
      calc (u * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) ^ (2 : ℕ) = u ^ (2 : ℕ) * (1 - 1 / K ^ (2 : ℕ)) := by
            rw [mul_pow, hsqsq]
        _ ≤ u ^ (2 : ℕ) - s := this
    nlinarith [hkey, hv0, hvsq, mul_nonneg hu0.le hrt.le]
  have hvle : v ≤ u := by nlinarith [hvsq, hv0, hu0, hs]
  have hden : 2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) * u ≤ u + v := by
    nlinarith [hvu, hrt1, hu0, hrt]
  have hprod : (u - v) * (u + v) = s := by nlinarith [hvsq]
  have hdenpos : 0 < 2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) * u := by positivity
  rw [le_div_iff₀ hdenpos]
  nlinarith [hden, hprod, hvle, sub_nonneg.2 hvle]

/-! ## The phase defect at the turning scale -/

theorem one_sub_sqrt_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 1 - Real.sqrt (1 - x) ≤ x := by
  have hx : (0 : ℝ) ≤ 1 - x := by linarith
  have hsq : (1 - x) ^ (2 : ℕ) ≤ 1 - x := by nlinarith
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hx] at h
  linarith

/-- **The band phase at the turning scale.**  Splitting the defect at the height `K√s`, the
logarithmic part carries the coefficient `1/(2√(1−K⁻²))`, which approaches the sharp `1/2`. -/
theorem one_sub_bandEndpointPhase_turning_le {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hKs : K * Real.sqrt s ≤ 1 / 2) :
    1 - bandEndpointPhase s (2 * Real.sqrt s)
      ≤ 4 * s + K ^ (2 : ℕ) * s
        + s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)))
          * (Real.log 2 - Real.log (K * Real.sqrt s)) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsqs : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  set y : ℝ := 2 * Real.sqrt s with hy
  set z : ℝ := K * Real.sqrt s with hz
  have hy0 : 0 < y := by positivity
  have hyz : y ≤ z := by
    rw [hy, hz]
    nlinarith [hsq0]
  have hz1 : z ≤ 1 / 2 := hKs
  have hy1 : y ≤ 1 := by linarith
  have hzsq : z ^ (2 : ℕ) = K ^ (2 : ℕ) * s := by
    rw [hz]
    nlinarith [hsqs]
  have hysq : y ^ (2 : ℕ) = 4 * s := by
    rw [hy]
    nlinarith [hsqs]
  set θy : ℝ := Real.arcsin y with hθy
  set θz : ℝ := Real.arcsin z with hθz
  have hθy0 : 0 < θy := Real.arcsin_pos.2 hy0
  have hθyz : θy ≤ θz := Real.arcsin_le_arcsin hyz
  have hθz2 : θz ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two z
  have hθy2 : θy ≤ Real.pi / 2 := le_trans hθyz hθz2
  have hsinθy : Real.sin θy = y := Real.sin_arcsin (by linarith) hy1
  have hsinθz : Real.sin θz = z := Real.sin_arcsin (by linarith) (by linarith)
  have hcosθy : Real.cos θy = Real.sqrt (1 - y ^ (2 : ℕ)) := Real.cos_arcsin y
  have hcosθz : Real.cos θz = Real.sqrt (1 - z ^ (2 : ℕ)) := Real.cos_arcsin z
  -- continuity data
  have hcs : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hcsin : Continuous Real.sin := Real.continuous_sin
  -- the total mass
  have hone : (1 : ℝ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ := by
    rw [integral_sin, Real.cos_zero, Real.cos_pi_div_two]
    ring
  have hadj : (∫ θ in (0 : ℝ)..θy, Real.sin θ) + ∫ θ in θy..(Real.pi / 2), Real.sin θ
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcsin.intervalIntegrable _ _) (hcsin.intervalIntegrable _ _)
  have hphase : bandEndpointPhase s y = ∫ θ in θy..(Real.pi / 2),
      Real.sqrt (Real.sin θ ^ (2 : ℕ) - s) := rfl
  have hdiff : (∫ θ in θy..(Real.pi / 2), Real.sin θ)
      - ∫ θ in θy..(Real.pi / 2), Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)
      = ∫ θ in θy..(Real.pi / 2), (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) :=
    (intervalIntegral.integral_sub (hcsin.intervalIntegrable _ _)
      (hcs.intervalIntegrable _ _)).symm
  have hdecomp : 1 - bandEndpointPhase s y
      = (∫ θ in (0 : ℝ)..θy, Real.sin θ)
        + ∫ θ in θy..(Real.pi / 2), (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) := by
    rw [hphase, ← hdiff, hone, ← hadj]
    ring
  -- the head
  have hhead : (∫ θ in (0 : ℝ)..θy, Real.sin θ) ≤ 4 * s := by
    rw [integral_sin, Real.cos_zero, hcosθy, hysq]
    have h4 : (0 : ℝ) ≤ 4 * s := by positivity
    have h41 : 4 * s ≤ 1 := by nlinarith [hysq, hy1, hy0]
    have := one_sub_sqrt_le h4 h41
    linarith
  -- split the tail
  have hsplit : (∫ θ in θy..(Real.pi / 2), (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)))
      = (∫ θ in θy..θz, (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)))
        + ∫ θ in θz..(Real.pi / 2), (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hcsin.sub hcs).intervalIntegrable _ _) ((hcsin.sub hcs).intervalIntegrable _ _)).symm
  -- the middle piece
  have hmid : (∫ θ in θy..θz, (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s))) ≤ K ^ (2 : ℕ) * s := by
    have hmono : (∫ θ in θy..θz, (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)))
        ≤ ∫ θ in θy..θz, Real.sin θ := by
      refine intervalIntegral.integral_mono_on hθyz ((hcsin.sub hcs).intervalIntegrable _ _)
        (hcsin.intervalIntegrable _ _) fun θ _ => ?_
      have := Real.sqrt_nonneg (Real.sin θ ^ (2 : ℕ) - s)
      linarith
    have hval : (∫ θ in θy..θz, Real.sin θ) = Real.sqrt (1 - y ^ (2 : ℕ)) - Real.sqrt (1 - z ^ (2 : ℕ)) := by
      rw [integral_sin, hcosθy, hcosθz]
    have hz2 : (0 : ℝ) ≤ z ^ (2 : ℕ) := sq_nonneg z
    have hz21 : z ^ (2 : ℕ) ≤ 1 := by nlinarith [hz1, hy0, hyz]
    have hb1 : Real.sqrt (1 - y ^ (2 : ℕ)) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) - y ^ (2 : ℕ) ≤ 1 by nlinarith [sq_nonneg y])
      rwa [Real.sqrt_one] at h
    have hb2 := one_sub_sqrt_le hz2 hz21
    rw [hval] at hmono
    rw [← hzsq]
    linarith
  -- the tail piece
  have hconst : (0 : ℝ) < 2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) := by
    have hK2 : (4 : ℝ) ≤ K ^ (2 : ℕ) := by nlinarith
    have hK2p : (0 : ℝ) < K ^ (2 : ℕ) := by positivity
    have : (0 : ℝ) < 1 - 1 / K ^ (2 : ℕ) := by
      rw [sub_pos, div_lt_one hK2p]
      linarith
    positivity
  have htail : (∫ θ in θz..(Real.pi / 2), (Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)))
      ≤ s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (Real.log 2 - Real.log z) := by
    have hptw : ∀ θ ∈ Icc θz (Real.pi / 2),
        Real.sin θ - Real.sqrt (Real.sin θ ^ (2 : ℕ) - s)
          ≤ s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (1 / Real.sin θ) := by
      intro θ hθ
      have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
      have hθzpos : 0 < θz := lt_of_lt_of_le hθy0 hθyz
      have hlowz : -(Real.pi / 2) ≤ θz := by linarith
      have hlowθ : -(Real.pi / 2) ≤ θ := by linarith [hθ.1]
      have hmemz : θz ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hlowz, hθz2⟩
      have hmemθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hlowθ, hθ.2⟩
      have hsinle : z ≤ Real.sin θ := by
        rw [← hsinθz]
        exact Real.strictMonoOn_sin.monotoneOn hmemz hmemθ hθ.1
      have hu : K * Real.sqrt s ≤ Real.sin θ := by
        rw [← hz]
        exact hsinle
      have h := sin_sub_sqrt_le hs hK hu
      have hsinpos : 0 < Real.sin θ := lt_of_lt_of_le (by rw [hz]; positivity) hsinle
      have heq : s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ)) * Real.sin θ)
          = s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (1 / Real.sin θ) := by
        field_simp
      rw [← heq]
      exact h
    have hcont : ContinuousOn (fun θ : ℝ =>
        s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (1 / Real.sin θ))
        (uIcc θz (Real.pi / 2)) := continuousOn_const.mul (continuousOn_inv_sin
          (lt_of_lt_of_le hθy0 hθyz) hθz2)
    have hcontint : IntervalIntegrable (fun θ : ℝ =>
        s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (1 / Real.sin θ)) MeasureTheory.volume
        θz (Real.pi / 2) := hcont.intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hθz2
      ((hcsin.sub hcs).intervalIntegrable _ _) hcontint hptw
    have hpull : (∫ θ in θz..(Real.pi / 2),
        s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * (1 / Real.sin θ))
        = s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) * ∫ θ in θz..(Real.pi / 2), 1 / Real.sin θ :=
      intervalIntegral.integral_const_mul _ _
    rw [hpull] at hmono
    refine le_trans hmono ?_
    have hle := integral_inv_sin_le (lt_of_lt_of_le hθy0 hθyz) hθz2
    rw [hsinθz] at hle
    have hnn : (0 : ℝ) ≤ s / (2 * Real.sqrt (1 - 1 / K ^ (2 : ℕ))) := by positivity
    exact mul_le_mul_of_nonneg_left hle hnn
  rw [hdecomp, hsplit]
  linarith

end GaloisForLFunctions.RHTower

end
