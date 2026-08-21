import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthCanonicalCutoff

/-!
# Canonical fixed-width Route-T packet

For every fixed proportional shell width above the minimal Route-T power scale, one canonical
degree-60 cutoff produces a literal finite packet whose normalized widths are fixed before the
physical base varies.  This is the fixed-ambient packet geometry required by spatial equation-(111).
-/

noncomputable section
namespace RHTower.Sieve

/-- One canonical cutoff per height works simultaneously for all admissible fixed shell widths.
Prime-freeness then produces a large packet with both normalized widths independent of `lambda`. -/
theorem exists_eventually_routeT_fixedWidth_primeFree_large_range_packet_canonicalCutoff :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∃ L : ℕ, 1 ≤ L ∧
          routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
          (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
          ∀ H0 : ℝ, 0 < H0 → H0 ≤ 1 / 4 →
            routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
            ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
                (2 * routeTPrimeGapPacketBase T),
              Chebyshev.theta (lambda + 2 * (lambda * H0)) -
                  Chebyshev.theta lambda = 0 →
              ∃ J : ℕ, 0 < J ∧
                (((2 ^ (J - 1) : ℕ) : ℝ)) ≤ (1 / 4) / H0 ∧
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
                        (routeTComparableWidthLadder H0 (1 / 4) j)
                        (routeTComparableWidthLadder H0 (1 / 4) (j + 1)) 1‖ := by
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
      16 ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop 16
  have hscale : ∀ᶠ T : ℝ in Filter.atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hleftScale : ∀ᶠ T : ℝ in Filter.atTop,
      4 ≤ T ^ (118 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 118 / 75)).eventually_ge_atTop 4
  have hcut := eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_fixedWidth
    C50 (zero_le_one.trans hC50)
  filter_upwards [hbaseThreshold, hbaseLarge, hscale, hleftScale, hcut,
    Filter.eventually_ge_atTop (2 : ℝ)] with T hthreshold hbase16 hscaleT
      hleftScaleT hcutT hT
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hT0 : 0 < T := by linarith
  have hTone : 1 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
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
  intro H0 hH0 hH0quarter hwidth lambda hlambda hprimeFree
  let K : ℕ := routeTPrimeGapPacketCutoff T
  have hlambdaPos : 0 < lambda := hx0.trans_le hlambda.1
  have hKreal : (0 : ℝ) < (K : ℝ) := by
    have hfloorLower : T / 2 ≤ (K : ℝ) := by
      have hlt := Nat.lt_floor_add_one T
      dsimp only [K, routeTPrimeGapPacketCutoff]
      linarith
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
  have hwidthLambda : lambda ^ (-(49 / 80 : ℝ)) ≤ H0 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    exact hanti.trans (by
      simpa only [routeTPrimeGapPacketWidth, x] using hwidth)
  have hpower : lambda ^ (31 / 80 : ℝ) ≤ lambda * H0 := by
    have heq : lambda ^ (31 / 80 : ℝ) =
        lambda * lambda ^ (-(49 / 80 : ℝ)) := by
      calc
        lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
          congr 1
          norm_num
        _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
          Real.rpow_add hlambdaPos 1 (-(49 / 80 : ℝ))
        _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hwidthLambda hlambdaPos.le
  have hsupport : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hpacketLambda := hlambda0 lambda (hthreshold.trans hlambda.1)
  have hresult := hpacketLambda L X 60 K (T0 := T) (t := (1 / 75 : ℝ))
    (x := x) (H0 := H0) hX hx0 hlambda hH0 hH0quarter hK hXL hTone
    hscaleLambda hpower hsupport
    (hcutT L hL hLX H0 hH0 hH0quarter (by simpa only [x] using hwidth))
    hprimeFree
  simpa only [x, X, K] using hresult

end RHTower.Sieve
