import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCanonicalCutoff
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthTailMonotonicity

/-!
# Canonical cutoff uniform over fixed shell widths

The canonical Route-T cutoff was previously certified only at the minimal power width.  Tail
monotonicity extends that same certificate to every wider fixed proportional shell width, which is
the geometry required by spatial equation-(111).
-/

noncomputable section
namespace RHTower.Sieve

/-- The order-50 canonical scalar cutoff is uniform over every fixed relative width between the
minimal Route-T power width and `1/4`, for every receiver-compatible physical cutoff `L`. -/
theorem eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_fixedWidth
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ L : ℕ, 1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ H0 : ℝ, 0 < H0 → H0 ≤ 1 / 4 →
        routeTPrimeGapPacketWidth (routeTPrimeGapPacketBase T) ≤ H0 →
        heathBrownWindowRelevantFixedPolylogBound
              L (routeTPrimeGapPacketSupport T) 60
              (routeTPrimeGapPacketBase T) 1 *
            (C * (1 / H0) ^ (51 : ℕ) *
              (routeTPrimeGapPacketCutoff T : ℝ) ^ (-(50 : ℝ))) ≤
          ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
            (2 * (1 + Real.log ((1 / 4) / H0) / Real.log 2)) := by
  have hminimal :=
    eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff_leftCutoff C hC
  filter_upwards [hminimal, Filter.eventually_ge_atTop (2 : ℝ)] with
    T hminimalT hT
  intro L hL hLX H0 hH0 hH0quarter hwidth
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let K : ℕ := routeTPrimeGapPacketCutoff T
  let h : ℝ := routeTPrimeGapPacketWidth x
  let A : ℝ := (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)
  have hx : 0 < x := by dsimp only [x, routeTPrimeGapPacketBase]; positivity
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hh : 0 < h := by
    dsimp only [h, routeTPrimeGapPacketWidth]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hP : 0 ≤ heathBrownWindowRelevantFixedPolylogBound L X 60 x 1 := by
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X 60 hX T (1 / 75) x 1 0 hx (by norm_num))
  have hcut := hminimalT L hL hLX x (by
    constructor
    · exact le_rfl
    · linarith)
  have hcut' :
      heathBrownWindowRelevantFixedPolylogBound L X 60 x 1 *
          (C * (1 / h) ^ (50 + 1) * (K : ℝ) ^ (-(50 : ℝ))) ≤
        A / (2 * (1 + Real.log ((1 / 4) / h) / Real.log 2)) := by
    simpa only [h, x, X, K, A, Nat.reduceAdd] using hcut
  have hmono := maynardNatOrderTailEnvelope_mono_width 50
    hP hC (Nat.cast_nonneg K) hA hh hH0 hH0quarter
    (by simpa only [h, x] using hwidth) hcut'
  simpa only [x, X, K, Nat.reduceAdd, Nat.cast_ofNat] using hmono

end RHTower.Sieve
