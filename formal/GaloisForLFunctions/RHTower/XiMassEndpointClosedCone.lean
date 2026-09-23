import GaloisForLFunctions.RHTower.XiMassTruePrimeCoboundaryBridge
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic

/-!
# The closed strip-endpoint prime cone

The moving prime cone of depth `d` is defined for every `d`, but the bounded-coboundary estimate
is proved only in the open range `1/2 < d < a`.  This file closes the range at its endpoint.

Two facts do the work.

The first is that the eight majorants of the coboundary identity are *uniform* on `[d₀, a)` for any
interior floor `d₀`: five of them do not see `d` at all, two are the affine deep-shift moment
divided by `d - 1/2`, and one is the integer-face bound `C₀ + C₁/(d - 1/2)`.  The deep-shift moment
`(1/2)∫e^{-σ|x|} + ∫(|x|+d)e^{-σ|x|}` is exactly `Z_σ + d·J_σ`, hence monotone in `d`, so all eight
are majorized by their values at `d₀` and `a`.

The second is that the cone cutoff `e^{du/(d-1/2)}` decreases to `e^{au/(a-1/2)}` and the
arithmetic prefix `{n ≤ e^{du/(d-1/2)}}` is a set of integers: once `d` is close enough to `a` the
prefix has already reached its endpoint value, because the endpoint cutoff is strictly below the
next integer.  So for each fixed `u` the depth-`d` cone equals the endpoint cone for all `d` in a
left neighbourhood of `a`, and the uniform bound passes to the limit.

The endpoint cone is therefore the closed cone `0 ≤ log p ≤ au/(a-1/2)`, and it carries both the
bounded-coboundary law and the quadrature-defect criterion.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-! ## The deep-shift moment is affine in the depth -/

/-- The deep-shift moment splits into the zero-shift moment plus the depth times the total mass. -/
theorem xiMassCriticalOutgoingDeepShiftBound_eq {sigma : ℝ} (hsigma : 0 < sigma) (d : ℝ) :
    xiMassCriticalOutgoingDeepShiftBound sigma d
      = xiMassCriticalOutgoingZeroShiftBound sigma
        + d * ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
  have hE := integrable_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hsigma
  have hA := integrable_abs_mul_exp_neg_mul_abs_weightedEulerStripFourierAnalytic hsigma
  have hpt : ∀ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|))
      = |x| * Real.exp (-(sigma * |x|)) + d * Real.exp (-(sigma * |x|)) := fun x => by ring
  have hsplit : (∫ x : ℝ, (|x| + d) * Real.exp (-(sigma * |x|)))
      = (∫ x : ℝ, |x| * Real.exp (-(sigma * |x|))) + d * ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_add hA (hE.const_mul d), MeasureTheory.integral_const_mul]
  rw [xiMassCriticalOutgoingDeepShiftBound, xiMassCriticalOutgoingZeroShiftBound, hsplit]
  ring

/-- The deep-shift moment increases with the depth. -/
theorem xiMassCriticalOutgoingDeepShiftBound_mono {sigma d d' : ℝ} (hsigma : 0 < sigma)
    (h : d ≤ d') :
    xiMassCriticalOutgoingDeepShiftBound sigma d
      ≤ xiMassCriticalOutgoingDeepShiftBound sigma d' := by
  rw [xiMassCriticalOutgoingDeepShiftBound_eq hsigma d,
    xiMassCriticalOutgoingDeepShiftBound_eq hsigma d']
  have hJ0 : (0 : ℝ) ≤ ∫ x : ℝ, Real.exp (-(sigma * |x|)) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  nlinarith

/-! ## Uniform interior bounds -/

/-- The prime-square prefix bound holds with one constant for every interior depth. -/
theorem exists_uniform_norm_xiMassCriticalSquareCone_bound {a sigma d₀ : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hd₀ : 1 / 2 < d₀) :
    ∃ B : ℝ, ∀ d : ℝ, d₀ ≤ d → d < a → ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalSquareCone a sigma d u‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := exists_norm_xiMassPrimeSquareLayer_vertical_bound ha hsigma
  refine ⟨B₀ + (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p) *
    (∫ x : ℝ, Real.exp (-(sigma * |x|))), fun d hdd hda u hu => ?_⟩
  have hdhalf : 1 / 2 < d := lt_of_lt_of_le hd₀ hdd
  have hsplit := xiMassPrimeSquareLayer_eq_cone_add_tail hdhalf hda hsigma hu
  have hsolve : xiMassCriticalSquareCone a sigma d u
      = xiMassPrimeSquareLayer a ((sigma : ℂ) + u * I)
        - xiMassCriticalPrimeSquareConeTail a sigma d u := by
    rw [hsplit]; ring
  rw [hsolve]
  exact (norm_sub_le _ _).trans
    (add_le_add (hB₀ u) (norm_xiMassCriticalPrimeSquareConeTail_le hdhalf hda hsigma hu))

/-- **(14.4, uniform form) One coboundary constant for every interior depth.**  The eight majorants
of the coboundary identity are all bounded on `[d₀, a)` by their values at the two ends. -/
theorem exists_uniform_norm_truePrimeCone_sub_outgoingFlux_bound {a sigma d₀ : ℝ}
    (hd₀ : 1 / 2 < d₀) (hd₀a : d₀ < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ d : ℝ, d₀ ≤ d → d < a → ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma d u - xiMassCriticalOutgoingFlux a sigma u‖ ≤ B := by
  have ha : 0 < a := lt_trans (by norm_num) (lt_trans hd₀ hd₀a)
  have hahalf : 1 / 2 < a := lt_trans hd₀ hd₀a
  have hd₀pos : (0 : ℝ) < d₀ - 1 / 2 := by linarith
  obtain ⟨BQ, hBQ⟩ := exists_uniform_norm_xiMassCriticalSquareCone_bound ha hsigma hd₀
  set J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|)) with hJ
  have hJ0 : (0 : ℝ) ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  set Z : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma with hZdef
  set BI : ℝ := 2 * Real.pi + 2 * J / (d₀ - 1 / 2) + 3 * J + 2 * Z with hBI
  set BR : ℝ := (∑' pk : Nat.Primes × ℕ, xiMassPrimePowerCriticalWeight pk.1 (pk.2 + 2)) * J
    with hBR
  set BE : ℝ := 8 * xiMassCriticalOutgoingDeepShiftBound sigma a / (d₀ - 1 / 2) with hBE
  refine ⟨J + BI + 8 * J + BE + BQ + BR + BE + 2 * Z, fun d hdd hda u hu => ?_⟩
  have hdhalf : 1 / 2 < d := lt_of_lt_of_le hd₀ hdd
  have hdpos : (0 : ℝ) < d - 1 / 2 := by linarith
  rw [xiMassCriticalTruePrimeCone_sub_outgoingFlux_eq hdhalf hda hsigma hu]
  have hK0 : ‖xiMassCriticalDampedFourierProfile a sigma u 0‖ ≤ J := by
    simpa only [hJ] using norm_xiMassCriticalDampedFourierProfile_zero_le ha hsigma
  have hdivJ : J / (d - 1 / 2) ≤ J / (d₀ - 1 / 2) :=
    div_le_div_of_nonneg_left hJ0 hd₀pos (by linarith)
  have hI : ‖xiMassCriticalIntegerConeSum a sigma d u‖ ≤ BI := by
    have hraw : ‖xiMassCriticalIntegerConeSum a sigma d u‖
        ≤ 2 * Real.pi + 2 * J / (d - 1 / 2) + 3 * J + 2 * Z := by
      simpa only [hJ, hZdef] using
        norm_xiMassCriticalIntegerConeSum_le hahalf hsigma hdhalf hda hu
    have hstep : 2 * J / (d - 1 / 2) ≤ 2 * J / (d₀ - 1 / 2) := by
      rw [mul_div_assoc, mul_div_assoc]
      linarith
    rw [hBI]
    linarith
  have hZterm : ‖(psiRemainder (⌊Real.exp (d * u / (d - 1 / 2))⌋₊) : ℂ)
      * xiMassCriticalDampedFourierProfile a sigma u
        (Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1))‖ ≤ 8 * J := by
    simpa only [hJ] using norm_xiMassCriticalDiscreteRemainder_terminalFlux_le
      hdhalf hda hsigma hu
  have hdeep : 8 * xiMassCriticalOutgoingDeepShiftBound sigma d / (d - 1 / 2) ≤ BE := by
    have hmono := xiMassCriticalOutgoingDeepShiftBound_mono (d := d) (d' := a) hsigma hda.le
    have hnn : 0 ≤ xiMassCriticalOutgoingDeepShiftBound sigma d :=
      xiMassCriticalOutgoingDeepShiftBound_nonneg (by linarith)
    rw [hBE, div_le_div_iff₀ hdpos hd₀pos]
    nlinarith
  have hE : ‖xiMassCriticalDiscreteRemainderConeOverflow a sigma d u‖ ≤ BE :=
    le_trans (norm_xiMassCriticalDiscreteRemainderConeOverflow_le hdhalf hda hsigma hu) hdeep
  have hRhigh : ‖xiMassCriticalHighCone a sigma d u‖ ≤ BR := by
    simpa only [hBR, hJ] using norm_xiMassCriticalHighCone_le ha hsigma d u
  have hT : ‖xiMassCriticalDiscreteRemainderTailFlux a sigma u (d * u / (d - 1 / 2))‖ ≤ BE :=
    le_trans (norm_xiMassCriticalDiscreteRemainder_superluminalTailFlux_le hdhalf hda hsigma hu)
      hdeep
  have hA : ‖xiMassCriticalFloorSawtoothFlux a sigma u‖ ≤ 2 * Z :=
    norm_xiMassCriticalFloorSawtoothFlux_le ha hsigma u
  have hoct : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : ℂ,
      ‖x₁ + x₂ + x₃ + x₄ - x₅ - x₆ - x₇ - x₈‖
        ≤ ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ + ‖x₆‖ + ‖x₇‖ + ‖x₈‖ := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈
    have e1 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅ - x₆ - x₇) x₈
    have e2 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅ - x₆) x₇
    have e3 := norm_sub_le (x₁ + x₂ + x₃ + x₄ - x₅) x₆
    have e4 := norm_sub_le (x₁ + x₂ + x₃ + x₄) x₅
    have e5 := norm_add_le (x₁ + x₂ + x₃) x₄
    have e6 := norm_add_le (x₁ + x₂) x₃
    have e7 := norm_add_le x₁ x₂
    linarith
  have hQ := hBQ d hdd hda u hu
  have hchain := hoct (xiMassCriticalDampedFourierProfile a sigma u 0)
    (xiMassCriticalIntegerConeSum a sigma d u)
    ((psiRemainder (⌊Real.exp (d * u / (d - 1 / 2))⌋₊) : ℂ)
      * xiMassCriticalDampedFourierProfile a sigma u
        (Real.log ((⌊Real.exp (d * u / (d - 1 / 2))⌋₊ : ℝ) + 1)))
    (xiMassCriticalDiscreteRemainderConeOverflow a sigma d u)
    (xiMassCriticalSquareCone a sigma d u)
    (xiMassCriticalHighCone a sigma d u)
    (xiMassCriticalDiscreteRemainderTailFlux a sigma u (d * u / (d - 1 / 2)))
    (xiMassCriticalFloorSawtoothFlux a sigma u)
  linarith [hchain, hK0, hI, hZterm, hE, hQ, hRhigh, hT, hA]

/-! ## Stabilization of the arithmetic prefix -/

/-- Equal cutoff floors give equal cone atoms: the atom only sees which integers lie below the
cutoff. -/
theorem xiMassCriticalConeAtom_eq_of_floor_eq {a sigma d d' u : ℝ}
    (hfl : ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ = ⌊Real.exp (d' * u / (d' - 1 / 2))⌋₊) (n : ℕ) :
    xiMassCriticalConeAtom a sigma d u n = xiMassCriticalConeAtom a sigma d' u n := by
  have hiff : ((n : ℝ) ≤ Real.exp (d * u / (d - 1 / 2)))
      ↔ ((n : ℝ) ≤ Real.exp (d' * u / (d' - 1 / 2))) := by
    rw [← Nat.le_floor_iff (Real.exp_pos _).le, ← Nat.le_floor_iff (Real.exp_pos _).le, hfl]
  unfold xiMassCriticalConeAtom
  by_cases hc : (n : ℝ) ≤ Real.exp (d * u / (d - 1 / 2))
  · rw [if_pos hc, if_pos (hiff.1 hc)]
  · rw [if_neg hc, if_neg fun hx => hc (hiff.2 hx)]

/-- Equal cutoff floors give the same true-prime cone. -/
theorem xiMassCriticalTruePrimeCone_eq_of_floor_eq {a sigma d d' u : ℝ}
    (hfl : ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ = ⌊Real.exp (d' * u / (d' - 1 / 2))⌋₊) :
    xiMassCriticalTruePrimeCone a sigma d u = xiMassCriticalTruePrimeCone a sigma d' u :=
  tsum_congr fun p => xiMassCriticalConeAtom_eq_of_floor_eq hfl (p : ℕ)

/-- For each height there is an interior depth at which the cone has already reached its endpoint
value. -/
theorem exists_interior_depth_eq_endpoint {a sigma d₀ u : ℝ} (hd₀ : 1 / 2 < d₀) (hd₀a : d₀ < a)
    (hu : 0 ≤ u) :
    ∃ d : ℝ, d₀ ≤ d ∧ d < a ∧
      xiMassCriticalTruePrimeCone a sigma d u = xiMassCriticalTruePrimeCone a sigma a u ∧
      ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ = ⌊Real.exp (a * u / (a - 1 / 2))⌋₊ := by
  have hahalf : 1 / 2 < a := lt_trans hd₀ hd₀a
  obtain ⟨d₁, hd₁half, hd₁a, hstab⟩ := exists_depth_floor_stabilizes (a := a) (u := u) hahalf hu
  refine ⟨max d₀ d₁, le_max_left _ _, max_lt hd₀a hd₁a, ?_, ?_⟩
  · exact xiMassCriticalTruePrimeCone_eq_of_floor_eq
      (hstab _ (le_max_right _ _) (max_lt hd₀a hd₁a))
  · exact hstab _ (le_max_right _ _) (max_lt hd₀a hd₁a)

/-! ## The closed endpoint cone -/

/-- **(14.10) The closed strip-limited cone is the same class as the outgoing current.**  The cone
at the strip endpoint `d = a` differs from the outgoing Chebyshev current by a uniformly bounded
family. -/
theorem exists_norm_endpointTruePrimeCone_sub_outgoingFlux_bound {a sigma : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma a u - xiMassCriticalOutgoingFlux a sigma u‖ ≤ B := by
  set d₀ : ℝ := 1 / 2 + (a - 1 / 2) / 2 with hd₀def
  have hd₀ : 1 / 2 < d₀ := by rw [hd₀def]; linarith
  have hd₀a : d₀ < a := by rw [hd₀def]; linarith
  obtain ⟨B, hB⟩ := exists_uniform_norm_truePrimeCone_sub_outgoingFlux_bound hd₀ hd₀a hsigma
  refine ⟨B, fun u hu => ?_⟩
  obtain ⟨d, hdd, hda, hcone, -⟩ :=
    exists_interior_depth_eq_endpoint (a := a) (sigma := sigma) hd₀ hd₀a hu
  rw [← hcone]
  exact hB d hdd hda u hu

/-- The line-bound property of the closed endpoint cone. -/
def XiMassCriticalEndpointConeLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalTruePrimeCone a sigma a u‖ ≤ C

/-- **(14.11) The closed-cone criterion.**  RH is equivalent to uniform boundedness of the
strip-endpoint prime cone. -/
theorem riemannHypothesis_iff_xiMassCriticalEndpointConeLineBound {a c sigma : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔ XiMassCriticalEndpointConeLineBound a sigma := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  set d₀ : ℝ := 1 / 2 + (a - 1 / 2) / 2 with hd₀def
  have hd₀ : 1 / 2 < d₀ := by rw [hd₀def]; linarith
  have hd₀a : d₀ < a := by rw [hd₀def]; linarith
  obtain ⟨B₁, hB₁⟩ := exists_norm_endpointTruePrimeCone_sub_outgoingFlux_bound ha hsigma
  obtain ⟨B₂, hB₂⟩ := exists_norm_truePrimeCone_sub_outgoingFlux_bound hd₀ hd₀a hsigma
  have hdiff : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalTruePrimeCone a sigma a u
        - xiMassCriticalTruePrimeCone a sigma d₀ u‖ ≤ B₁ + B₂ := by
    intro u hu
    have hsolve : xiMassCriticalTruePrimeCone a sigma a u
        - xiMassCriticalTruePrimeCone a sigma d₀ u
        = (xiMassCriticalTruePrimeCone a sigma a u - xiMassCriticalOutgoingFlux a sigma u)
          - (xiMassCriticalTruePrimeCone a sigma d₀ u
              - xiMassCriticalOutgoingFlux a sigma u) := by ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hB₁ u hu) (hB₂ u hu))
  rw [riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound hhalf hca hsigma hd₀ hd₀a]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + (B₁ + B₂), fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma a u
        = xiMassCriticalTruePrimeCone a sigma d₀ u
          + (xiMassCriticalTruePrimeCone a sigma a u
              - xiMassCriticalTruePrimeCone a sigma d₀ u) := by ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hdiff u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + (B₁ + B₂), fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma d₀ u
        = xiMassCriticalTruePrimeCone a sigma a u
          - (xiMassCriticalTruePrimeCone a sigma a u
              - xiMassCriticalTruePrimeCone a sigma d₀ u) := by ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hdiff u hu))

/-! ## The closed-cone quadrature defect -/

/-- **(14.13) The continuum integral over the closed cone is uniformly bounded.**  The endpoint
cutoff is reached by an interior depth, and the interior bound is uniform there. -/
theorem norm_integral_growingFourierProfile_at_endpointCone_le {a sigma : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u →
      ‖∫ h in (0 : ℝ)..xiMassCriticalConeEdge a u,
        xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤ B := by
  set d₀ : ℝ := 1 / 2 + (a - 1 / 2) / 2 with hd₀def
  have hd₀ : 1 / 2 < d₀ := by rw [hd₀def]; linarith
  have hd₀a : d₀ < a := by rw [hd₀def]; linarith
  have hd₀pos : (0 : ℝ) < d₀ - 1 / 2 := by linarith
  set J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|)) with hJ
  have hJ0 : (0 : ℝ) ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨2 * Real.pi + 2 * J / (d₀ - 1 / 2) + 2 * J, fun u hu => ?_⟩
  obtain ⟨d, hdd, hda, -, hfl⟩ :=
    exists_interior_depth_eq_endpoint (a := a) (sigma := sigma) hd₀ hd₀a hu
  have hdhalf : 1 / 2 < d := lt_of_lt_of_le hd₀ hdd
  have hedge : xiMassCriticalConeEdge d u = xiMassCriticalConeEdge a u := by
    rw [xiMassCriticalConeEdge, xiMassCriticalConeEdge, hfl]
  have hraw := norm_integral_xiMassCriticalGrowingFourierProfile_at_cone_le
    hdhalf hda hsigma hu (hedge ▸ xiMassCriticalConeEdge_ge d u)
  have hdivJ : J / (d - 1 / 2) ≤ J / (d₀ - 1 / 2) :=
    div_le_div_of_nonneg_left hJ0 hd₀pos (by linarith)
  have hstep : 2 * J / (d - 1 / 2) ≤ 2 * J / (d₀ - 1 / 2) := by
    rw [mul_div_assoc, mul_div_assoc]
    linarith
  rw [← hJ] at hraw
  linarith

/-- The line-bound property of the closed-cone quadrature defect. -/
def XiMassCriticalEndpointQuadratureDefectLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → ‖xiMassCriticalPrimeQuadratureDefect a sigma a u‖ ≤ C

/-- **(14.14) The closed-cone quadrature-defect criterion.**  RH is equivalent to uniform
boundedness of the quadrature defect of the closed endpoint cone against its continuum density. -/
theorem riemannHypothesis_iff_xiMassCriticalEndpointQuadratureDefectLineBound {a c sigma : ℝ}
    (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔ XiMassCriticalEndpointQuadratureDefectLineBound a sigma := by
  have ha : 1 / 2 < a := lt_trans hhalf hca
  obtain ⟨B, hB⟩ := norm_integral_growingFourierProfile_at_endpointCone_le ha hsigma
  rw [riemannHypothesis_iff_xiMassCriticalEndpointConeLineBound hhalf hca hsigma]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    rw [xiMassCriticalPrimeQuadratureDefect]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hB u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsolve : xiMassCriticalTruePrimeCone a sigma a u
        = xiMassCriticalPrimeQuadratureDefect a sigma a u
          + ∫ h in (0 : ℝ)..xiMassCriticalConeEdge a u,
              xiMassCriticalGrowingFourierProfile a sigma u h := by
      rw [xiMassCriticalPrimeQuadratureDefect]
      ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hB u hu))

/-- **(14.13) The closed-cone Stieltjes pairing.**  The endpoint cone is the atomic pairing of the
damped profile against the true-prime logarithmic measure at the endpoint cutoff. -/
theorem integral_dampedProfile_endpointPrimeLogMeasure (a sigma u : ℝ) :
    (∫ h, xiMassCriticalDampedFourierProfile a sigma u h
        ∂(xiMassCriticalPrimeLogMeasure a u))
      = xiMassCriticalTruePrimeCone a sigma a u :=
  integral_dampedProfile_primeLogMeasure a sigma a u

end

end RHTower
