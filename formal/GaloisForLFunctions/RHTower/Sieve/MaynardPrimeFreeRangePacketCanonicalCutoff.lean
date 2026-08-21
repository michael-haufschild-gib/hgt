import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCutoffSchedule
import GaloisForLFunctions.RHTower.Sieve.MaynardMobiusAllShort

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

open Filter Topology

namespace RHTower.Sieve

noncomputable section

theorem card_heathBrownBoxChoice_mono_left
    {L X k : ℕ} (hLX : L ≤ X) :
    Fintype.card (HeathBrownBoxChoice L X k) ≤
      Fintype.card (HeathBrownBoxChoice X X k) := by
  rw [card_heathBrownBoxChoice, card_heathBrownBoxChoice]
  apply Finset.sum_le_sum
  intro m _hm
  gcongr

theorem heathBrownWindowRelevantFixedPolylogBound_mono_left
    {L X k : ℕ} {N sigma : ℝ} (hX : 1 ≤ X) (hN : 0 ≤ N) (hLX : L ≤ X) :
    heathBrownWindowRelevantFixedPolylogBound L X k N sigma ≤
      heathBrownWindowRelevantFixedPolylogBound X X k N sigma := by
  let M : ℝ := (((2 ^ (2 * k) * X : ℕ) : ℝ))
  let R : ℝ := ((2 ^ k : ℕ) : ℝ) * Real.log M *
    (M * (1 + Real.log M) ^ (2 ^ (2 * k + 1) - 1))
  have hM1 : 1 ≤ M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hcard :
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) ≤
        (Fintype.card (HeathBrownBoxChoice X X k) : ℝ) := by
    exact_mod_cast card_heathBrownBoxChoice_mono_left hLX
  have hleft :
      (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
          (((2 ^ k : ℕ) : ℝ)) * Real.log M *
            (M * (1 + Real.log M) ^ (2 ^ (2 * k + 1) - 1)) =
        (Fintype.card (HeathBrownBoxChoice L X k) : ℝ) * R := by
    dsimp only [R]
    ring
  have hright :
      (Fintype.card (HeathBrownBoxChoice X X k) : ℝ) *
          (((2 ^ k : ℕ) : ℝ)) * Real.log M *
            (M * (1 + Real.log M) ^ (2 ^ (2 * k + 1) - 1)) =
        (Fintype.card (HeathBrownBoxChoice X X k) : ℝ) * R := by
    dsimp only [R]
    ring
  simp only [heathBrownWindowRelevantFixedPolylogBound]
  change (N / (2 ^ (2 * k) : ℝ)) ^ (-sigma) *
      ((Fintype.card (HeathBrownBoxChoice L X k) : ℝ) *
        (((2 ^ k : ℕ) : ℝ)) * Real.log M *
          (M * (1 + Real.log M) ^ (2 ^ (2 * k + 1) - 1))) ≤
    (N / (2 ^ (2 * k) : ℝ)) ^ (-sigma) *
      ((Fintype.card (HeathBrownBoxChoice X X k) : ℝ) *
        (((2 ^ k : ℕ) : ℝ)) * Real.log M *
          (M * (1 + Real.log M) ^ (2 ^ (2 * k + 1) - 1)))
  rw [hleft, hright]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hR)
    (Real.rpow_nonneg (div_nonneg hN (by positivity)) _)

theorem eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed_leftCutoff
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (x : ℝ) (L X : ℕ), 1 ≤ x → 1 ≤ L → 1 ≤ X → L ≤ X →
        (X : ℝ) ≤ 4 * x → (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        heathBrownWindowRelevantFixedPolylogBound L X 60 x 1 ≤ T ^ eta := by
  have hmajor :=
    eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed heta
  filter_upwards [hmajor] with T hmajorT
  intro x L X hx _hL hX hLX hXx hXscale
  exact (heathBrownWindowRelevantFixedPolylogBound_mono_left hX
    (zero_le_one.trans hx) hLX).trans (hmajorT x X hx hX hXx hXscale)

/-- The order-50 scalar cutoff remains automatic for every receiver-compatible Möbius cutoff
`L ≤ X`; the earlier `L = X` theorem is a uniform majorant, not a required schedule. -/
theorem eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_leftCutoff
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L : ℕ, 1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        heathBrownWindowRelevantFixedPolylogBound
              L (routeTPrimeGapPacketSupport T) 60
              (routeTPrimeGapPacketBase T) 1 *
            (C * (1 / routeTPrimeGapPacketWidth lambda) ^ (51 : ℕ) *
              (routeTPrimeGapPacketCutoff T : ℝ) ^ (-(50 : ℝ))) ≤
          ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
            (2 * (1 +
              Real.log ((1 / 4) / routeTPrimeGapPacketWidth lambda) / Real.log 2)) := by
  have hmajor := eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff C hC
  filter_upwards [hmajor, Filter.eventually_ge_atTop (2 : ℝ)] with T hmajorT hT
  intro L _hL hLX lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let H0 : ℝ := routeTPrimeGapPacketWidth lambda
  let K : ℕ := routeTPrimeGapPacketCutoff T
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hP := heathBrownWindowRelevantFixedPolylogBound_mono_left
    (k := 60) (N := x) (sigma := 1) hX hx0.le (show L ≤ X from hLX)
  have hH0 : 0 < H0 := by
    dsimp only [H0, routeTPrimeGapPacketWidth]
    have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
    positivity
  have htail0 : 0 ≤
      C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg hC (pow_nonneg (one_div_nonneg.mpr hH0.le) _))
      (Real.rpow_nonneg (Nat.cast_nonneg K) _)
  have hmono := mul_le_mul_of_nonneg_right hP htail0
  exact hmono.trans (by
    simpa only [x, X, H0, K] using hmajorT lambda hlambda)

/-- Receiver-compatible form of the strict-gap packet producer.  One canonical degree-60
Möbius cutoff is selected with the exact short-factor bound required by the Route-T count corpus. -/
theorem exists_eventually_routeT_strictGapSplit_primeFree_large_range_packet_canonicalCutoff :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∃ L : ℕ, 1 ≤ L ∧
          routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
          (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
          ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
              (2 * routeTPrimeGapPacketBase T),
            Chebyshev.theta
                  (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
                Chebyshev.theta lambda = 0 →
            ∃ J : ℕ, 0 < J ∧
              (((2 ^ (J - 1) : ℕ) : ℝ)) ≤
                  (1 / 4) / routeTPrimeGapPacketWidth lambda ∧
              ∃ j ∈ Finset.range J,
                (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
                    (J : ℝ)) / 8 ≤
                  ‖maynardFixedAmbientPhysicalDefectPacket
                      (Finset.range (routeTPrimeGapPacketCutoff T))
                      (fun y : ℝ ↦
                        heathBrownWindowRelevantEligibleDyadicAggregate
                          L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                          (routeTPrimeGapPacketBase T)
                          ((1 : ℂ) + (y : ℝ) * Complex.I))
                      lambda 1
                      (routeTComparableWidthLadder
                        (routeTPrimeGapPacketWidth lambda) (1 / 4) j)
                      (routeTComparableWidthLadder
                        (routeTPrimeGapPacketWidth lambda) (1 / 4) (j + 1)) 1‖ := by
  obtain ⟨C50, hC50, hpacket⟩ :=
    exists_eventually_routeT_proportional_primeFree_large_range_packet_natOrder
      50 (by norm_num) (theta := (31 / 80 : ℝ)) (by norm_num)
  refine ⟨C50, hC50, ?_⟩
  obtain ⟨lambda0, hlambda0⟩ := Filter.eventually_atTop.1 hpacket
  have hbaseTop :
      Filter.Tendsto routeTPrimeGapPacketBase Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseThreshold : ∀ᶠ T : ℝ in Filter.atTop,
      lambda0 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop lambda0
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop,
      16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have hwidthSmall : ∀ᶠ T : ℝ in Filter.atTop,
      (routeTPrimeGapPacketBase T) ^ (-(49 / 80 : ℝ)) ≤ 1 / 4 := by
    have hlim := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
    exact Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim
  have hscale : ∀ᶠ T : ℝ in Filter.atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hleftScale : ∀ᶠ T : ℝ in Filter.atTop,
      4 ≤ T ^ (118 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 118 / 75)).eventually_ge_atTop 4
  have hcut := eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_leftCutoff
    C50 (zero_le_one.trans hC50)
  filter_upwards [hbaseThreshold, hbaseLarge, hwidthSmall, hscale, hleftScale, hcut,
    Filter.eventually_ge_atTop (2 : ℝ)] with T hthreshold hbase16 hwidthBase
      hscaleT hleftScaleT hcutT hT
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hT0 : 0 < T := by linarith
  have hTone : 1 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x] at hbase16 ⊢
    linarith
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXx : (X : ℝ) ≤ 4 * x := by linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    rw [← hxscale]
    exact hXx
  have hXscale' : (X : ℝ) ≤ T ^ (120 * (1 / 75 : ℝ)) := by
    convert hXscale using 1 <;> norm_num
  obtain ⟨L, hL, hXL, hLscale⟩ :=
    exists_maynardMoebiusCutoff_sixty (T0 := T) (t := (1 / 75 : ℝ)) (X := X)
      hTone (by norm_num) hXscale'
  have hLscale' : (L : ℝ) ≤ T ^ (2 / 75 : ℝ) := by
    convert hLscale using 1 <;> norm_num
  have hleftMul :
      T ^ (2 / 75 : ℝ) ≤ T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := by
    have hmul := mul_le_mul_of_nonneg_right hleftScaleT
      (div_nonneg (Real.rpow_nonneg hT0.le (2 / 75 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 4))
    calc
      T ^ (2 / 75 : ℝ) = 4 * (T ^ (2 / 75 : ℝ) / 4) := by ring
      _ ≤ T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := hmul
  have hleftBase : T ^ (2 / 75 : ℝ) ≤ x := by
    calc
      T ^ (2 / 75 : ℝ) ≤
          T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := hleftMul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) =
          (T ^ (118 / 75 : ℝ) * T ^ (2 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
  have hLXreal : (L : ℝ) ≤ (X : ℝ) := by
    exact hLscale'.trans (hleftBase.trans (by linarith [hceilLower, hx0]))
  have hLX : L ≤ X := by exact_mod_cast hLXreal
  refine ⟨L, hL, by simpa only [X] using hXL, hLscale', ?_⟩
  intro lambda hlambda hprimeFree
  let H0 : ℝ := routeTPrimeGapPacketWidth lambda
  let K : ℕ := routeTPrimeGapPacketCutoff T
  have hlambdaPos : 0 < lambda := hx0.trans_le hlambda.1
  have hH0 : 0 < H0 := by
    dsimp only [H0, routeTPrimeGapPacketWidth]
    positivity
  have hH0quarter : H0 ≤ 1 / 4 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    dsimp only [H0, routeTPrimeGapPacketWidth]
    exact hanti.trans (by simpa only [x] using hwidthBase)
  have hfloorLower : T / 2 ≤ (K : ℝ) := by
    have hlt := Nat.lt_floor_add_one T
    dsimp only [K, routeTPrimeGapPacketCutoff]
    linarith
  have hKreal : (0 : ℝ) < (K : ℝ) := by
    exact (by positivity : (0 : ℝ) < T / 2).trans_le hfloorLower
  have hK : 0 < K := by exact_mod_cast hKreal
  have hscaleLambda :
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) ≤ lambda := by
    have hmul :
        (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) ≤
          T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hscaleT
        (div_nonneg (Real.rpow_nonneg hT0.le (1 / 75 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 4))
    calc
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) =
          (4 * (((2 ^ 120 : ℕ) : ℝ))) *
            (T ^ (1 / 75 : ℝ) / 4) := by norm_num; ring
      _ ≤ T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) := hmul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) =
          (T ^ (119 / 75 : ℝ) * T ^ (1 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
      _ ≤ lambda := hlambda.1
  have hpower : lambda ^ (31 / 80 : ℝ) ≤ lambda * H0 := by
    have heq : lambda ^ (31 / 80 : ℝ) = lambda * H0 := by
      dsimp only [H0, routeTPrimeGapPacketWidth]
      calc
        lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
          congr 1
          norm_num
        _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
          Real.rpow_add hlambdaPos 1 (-(49 / 80 : ℝ))
        _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
    exact heq.le
  have hsupport : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hpacketLambda := hlambda0 lambda (hthreshold.trans hlambda.1)
  have hresult := hpacketLambda L X 60 K hX hx0 hlambda hH0 hH0quarter hK hXL
    (by linarith : (1 : ℝ) < T) hscaleLambda hpower hsupport
    (hcutT L hL hLX lambda hlambda) hprimeFree
  simpa only [x, X, H0, K] using hresult

end

end RHTower.Sieve
