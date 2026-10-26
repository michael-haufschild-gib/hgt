import GaloisForLFunctions.ArithmeticCorrelationGeometry.AlmostEveryGaugePointCancelsToTheSquareRoot
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheMoebiusBoundarySeparatesGaugeTwins
import GaloisForLFunctions.BezoutValuationIncidence.TheExtremeVaughanCutoffReadsItsHarmonicSum
import GaloisForLFunctions.RHTower.MobiusDiscretePacketEdgeEstimates

/-!
# Charged boundaries are critical at a quarter

The boundary of a finite presentation at weight `σ` reads a source on the escaped cells
`M < j ≤ N` with the weight `j^{−2σ}`. For an unsigned source the dilation boundary is finite and
nonzero exactly at `σ = ½` (`exists_pos_tendsto_escapedMass_iff`): the archimedean place.

* **Gauge charge halves the critical weight** (`integral_normSq_twistedFlatBoundary`,
  `exists_pos_tendsto_twistedFlatBoundary_iff`). The gauge mean square of the twisted flat boundary
  at weight `σ` is the unsigned escaped mass at weight `2σ`; it has a finite nonzero
  horizon-uniform limit (`log a`) exactly at `σ = ¼`.
* **Abel transfer** (`norm_sum_Ioc_mul_rpow_neg_le`). Partial sums `O((n+1)^α)` give weighted blocks
  `Σ_{M<j≤N} c_j j^{−s} = O((M+1)^{α−s})` for `α < s`, uniformly in `N`.
* **The square-root boundary law of the Möbius orbit** (`moebius_boundary_trichotomy`). The law
  `|Σ_{M<j≤N} μ(j) χ_x(j)/j| ≤ C_θ (M+1)^{−θ}` for every `θ < ½` holds at Haar-almost every gauge point,
  fails at the Liouville twin, and at the gauge point `0` is equivalent to the Riemann hypothesis.
  At almost every gauge point every boundary of weight `σ > ¼` decays
  (`ae_norm_chargedBoundary_le`).

Gauge status: the boundary of a gauge-charged source has its normalisation at `σ = ¼`, half the
archimedean weight. The actual Möbius boundary vanishes unconditionally only down to `σ = ½`
(the prime number theorem, `TheMoebiusBoundarySeparatesGaugeTwins`); RH says that it behaves at
square-root scale like the boundary of a typical point of its orbit.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### Gauge charge halves the critical weight -/

/-- The gauge mean square of the twisted flat boundary at weight `σ` is the escaped mass at
weight `2σ`. -/
theorem integral_normSq_twistedFlatBoundary (N a b : ℕ) (σ : ℝ) :
    ∫ x, ‖twistSum (Ioc ((N - b) / a) N) (fun j => (((j : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) x‖ ^ 2
      ∂gaugeHaar = escapedMass N a b (2 * σ) := by
  rw [integral_normSq_twistSum (fun n hn => Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _)
    (mem_Ioc.mp hn).1)), escapedMass]
  refine sum_congr rfl fun j hj => ?_
  have hj : (0 : ℝ) < j := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hj).1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hj.le,
    ← Real.rpow_neg hj.le]
  norm_num
  ring_nf

/-- **The critical weight of a charged boundary is `¼`.** The gauge mean square of the twisted flat
boundary of a dilation `a ≥ 2` has a finite nonzero horizon limit iff `σ = ¼`. -/
theorem exists_pos_tendsto_twistedFlatBoundary_iff {a b : ℕ} (ha : 2 ≤ a) (σ : ℝ) :
    (∃ c, 0 < c ∧ Tendsto (fun N => ∫ x, ‖twistSum (Ioc ((N - b) / a) N)
      (fun j => (((j : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) x‖ ^ 2 ∂gaugeHaar) atTop (𝓝 c)) ↔ σ = 1 / 4 := by
  simp_rw [integral_normSq_twistedFlatBoundary]
  rw [exists_pos_tendsto_escapedMass_iff ha (2 * σ)]
  constructor <;> intro h <;> linarith

/-! ### Abel transfer to weighted blocks -/

/-- Abel summation on `(M, N]` with partial sums `S_n = Σ_{j ≤ n} c_j`. -/
theorem sum_Ioc_mul_eq_abel (c : ℕ → ℂ) (w : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ j ∈ Ioc M N, c j * w j =
      (∑ i ∈ range (N + 1), c i) * w (N + 1) - (∑ i ∈ range (M + 1), c i) * w (M + 1) +
        ∑ j ∈ Ioc M N, (∑ i ∈ range (j + 1), c i) * (w j - w (j + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [sum_Ioc_succ_top (by omega), sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ c (N + 1)]
    ring

/-- Telescoping on `(M, N]`. -/
theorem sum_Ioc_sub_succ (f : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ j ∈ Ioc M N, (f j - f (j + 1)) = f (M + 1) - f (N + 1) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    ring

/-- **Abel transfer.** If `|Σ_{j ≤ n} c_j| ≤ C (n+1)^α` and `0 ≤ α < s`, the weighted block
`Σ_{M<j≤N} c_j j^{−s}` is at most `C (2 + s 2^{s+1}/(s−α)) (M+1)^{α−s}`, uniformly in `N`. -/
theorem norm_sum_Ioc_mul_rpow_neg_le {c : ℕ → ℂ} {C α s : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hαs : α < s) (hS : ∀ n : ℕ, ‖∑ i ∈ range (n + 1), c i‖ ≤ C * ((n : ℝ) + 1) ^ α) (M N : ℕ) :
    ‖∑ j ∈ Ioc M N, c j * (((j : ℝ) ^ (-s) : ℝ) : ℂ)‖ ≤
      C * (2 + s * 2 ^ (s + 1) / (s - α)) * ((M : ℝ) + 1) ^ (α - s) := by
  have hs : 0 < s := by linarith
  have hθ : 0 < s - α := by linarith
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hfac : 0 ≤ C * ((M : ℝ) + 1) ^ (α - s) := mul_nonneg hC (Real.rpow_nonneg hM1.le _)
  rcases lt_or_ge N M with hNM | hMN
  · rw [Ioc_eq_empty (by omega), sum_empty, norm_zero]
    have : 0 ≤ 2 + s * 2 ^ (s + 1) / (s - α) := by positivity
    nlinarith
  rw [sum_Ioc_mul_eq_abel c _ hMN]
  set w : ℕ → ℝ := fun j => (j : ℝ) ^ (-s)
  -- the two boundary terms
  have hend : ∀ n : ℕ, M ≤ n → ‖(∑ i ∈ range (n + 1), c i) * (((((n + 1 : ℕ) : ℝ) ^ (-s)) : ℝ) : ℂ)‖
      ≤ C * ((M : ℝ) + 1) ^ (α - s) := by
    intro n hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    push_cast
    calc ‖∑ i ∈ range (n + 1), c i‖ * ((n : ℝ) + 1) ^ (-s)
        ≤ C * ((n : ℝ) + 1) ^ α * ((n : ℝ) + 1) ^ (-s) :=
          mul_le_mul_of_nonneg_right (hS n) (Real.rpow_nonneg hn1.le _)
      _ = C * ((n : ℝ) + 1) ^ (α - s) := by
          rw [mul_assoc, ← Real.rpow_add hn1, sub_eq_add_neg]
      _ ≤ C * ((M : ℝ) + 1) ^ (α - s) := by
          have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (x := (M : ℝ) + 1)
            (y := (n : ℝ) + 1) (z := α - s) hM1 (by linarith) (by linarith)) hC
  -- the Abel sum
  have hdiff : ∀ j : ℕ, 1 ≤ j → 0 ≤ w j - w (j + 1) ∧ w j - w (j + 1) ≤
      s * 2 ^ (s + 1) * ((j : ℝ) + 1) ^ (-(s + 1)) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hle : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hup := RHTower.DiscretePacket.rpow_neg_sub_rpow_neg_le hj0 hle hs.le
    have hlo := RHTower.DiscretePacket.le_rpow_neg_sub_rpow_neg hj0 hle hs.le
    simp only [w]
    push_cast
    refine ⟨le_trans (by positivity) hlo, hup.trans ?_⟩
    rw [add_sub_cancel_left, mul_one]
    -- `j^{−(s+1)} ≤ 2^{s+1} (j+1)^{−(s+1)}` since `(j+1)/2 ≤ j`
    have hhalf : ((j : ℝ) + 1) / 2 ≤ j := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have h1 : (j : ℝ) ^ (-(s + 1)) ≤ (((j : ℝ) + 1) / 2) ^ (-(s + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul] at h1
    calc s * (j : ℝ) ^ (-(s + 1)) ≤ s * (((j : ℝ) + 1) ^ (-(s + 1)) * 2 ^ (s + 1)) :=
          mul_le_mul_of_nonneg_left h1 hs.le
      _ = s * 2 ^ (s + 1) * ((j : ℝ) + 1) ^ (-(s + 1)) := by ring
  have htel : ∀ j : ℕ, 1 ≤ j → ((j : ℝ) + 1) ^ (α - s - 1) ≤
      ((j : ℝ) ^ (-(s - α)) - ((j : ℝ) + 1) ^ (-(s - α))) / (s - α) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have := RHTower.DiscretePacket.le_rpow_neg_sub_rpow_neg hj0 (by linarith : (j : ℝ) ≤ j + 1)
      hθ.le
    rw [add_sub_cancel_left, mul_one, show -(s - α + 1) = α - s - 1 by ring] at this
    rw [le_div_iff₀ hθ]
    linarith
  have hsum : ‖∑ j ∈ Ioc M N, (∑ i ∈ range (j + 1), c i) * (((w j : ℝ) : ℂ) - ((w (j + 1) : ℝ) : ℂ))‖
      ≤ C * (s * 2 ^ (s + 1) / (s - α)) * ((M : ℝ) + 1) ^ (α - s) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Ioc M N, ‖(∑ i ∈ range (j + 1), c i) * (((w j : ℝ) : ℂ) - ((w (j + 1) : ℝ) : ℂ))‖
        ≤ C * (s * 2 ^ (s + 1)) * (((j : ℝ) ^ (-(s - α)) - ((j : ℝ) + 1) ^ (-(s - α))) / (s - α)) := by
      intro j hj
      have hj1 : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
      obtain ⟨hd0, hd1⟩ := hdiff j hj1
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0]
      calc ‖∑ i ∈ range (j + 1), c i‖ * (w j - w (j + 1))
          ≤ C * ((j : ℝ) + 1) ^ α * (s * 2 ^ (s + 1) * ((j : ℝ) + 1) ^ (-(s + 1))) :=
            mul_le_mul (hS j) hd1 hd0 (by positivity)
        _ = C * (s * 2 ^ (s + 1)) * ((j : ℝ) + 1) ^ (α - s - 1) := by
            rw [show α - s - 1 = α + -(s + 1) by ring, Real.rpow_add hj0]
            ring
        _ ≤ _ := by
            gcongr
            exact htel j hj1
    refine (sum_le_sum hterm).trans ?_
    have htele := sum_Ioc_sub_succ (fun j : ℕ => (j : ℝ) ^ (-(s - α))) hMN
    push_cast at htele
    rw [← mul_sum, ← sum_div, htele]
    have hN1 : 0 ≤ ((N : ℝ) + 1) ^ (-(s - α)) := Real.rpow_nonneg (by positivity) _
    have hkey : (((M : ℝ) + 1) ^ (-(s - α)) - ((N : ℝ) + 1) ^ (-(s - α))) / (s - α) ≤
        ((M : ℝ) + 1) ^ (α - s) / (s - α) := by
      rw [show α - s = -(s - α) by ring]
      gcongr
      linarith
    calc C * (s * 2 ^ (s + 1)) * ((((M : ℝ) + 1) ^ (-(s - α)) - ((N : ℝ) + 1) ^ (-(s - α))) /
          (s - α)) ≤ C * (s * 2 ^ (s + 1)) * (((M : ℝ) + 1) ^ (α - s) / (s - α)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = C * (s * 2 ^ (s + 1) / (s - α)) * ((M : ℝ) + 1) ^ (α - s) := by ring
  have hwN : (((w (N + 1) : ℝ)) : ℂ) = (((((N + 1 : ℕ) : ℝ) ^ (-s)) : ℝ) : ℂ) := rfl
  have hwM : (((w (M + 1) : ℝ)) : ℂ) = (((((M + 1 : ℕ) : ℝ) ^ (-s)) : ℝ) : ℂ) := rfl
  have hsplit : ∀ j : ℕ, ((((j : ℝ) ^ (-s)) : ℝ) : ℂ) - ((((j + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) =
      ((w j : ℝ) : ℂ) - ((w (j + 1) : ℝ) : ℂ) := fun j => rfl
  simp_rw [hsplit]
  calc ‖(∑ i ∈ range (N + 1), c i) * ((((N + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) -
        (∑ i ∈ range (M + 1), c i) * ((((M + 1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) +
        ∑ j ∈ Ioc M N, (∑ i ∈ range (j + 1), c i) * (((w j : ℝ) : ℂ) - ((w (j + 1) : ℝ) : ℂ))‖
      ≤ C * ((M : ℝ) + 1) ^ (α - s) + C * ((M : ℝ) + 1) ^ (α - s) +
          C * (s * 2 ^ (s + 1) / (s - α)) * ((M : ℝ) + 1) ^ (α - s) :=
        (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (hend N hMN) (hend M le_rfl))) hsum)
    _ = C * (2 + s * 2 ^ (s + 1) / (s - α)) * ((M : ℝ) + 1) ^ (α - s) := by ring

/-! ### Boundaries of the gauge orbit -/

/-- The charged boundary at weight `σ`: `Σ_{M<j≤N} a_j χ_x(j) j^{−2σ}`. -/
def chargedBoundary (a : ℕ → ℂ) (σ : ℝ) (M N : ℕ) (x : GaugeTorus) : ℂ :=
  ∑ j ∈ Ioc M N, a j * twist x j * (((j : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)

/-- **The half-power law controls every boundary above `¼`.** At a gauge point with the half-power
law, the boundary at weight `σ > ¼` is `O((M+1)^{−θ})` for every `θ < 2σ − ½`, uniformly in `N`. -/
theorem norm_chargedBoundary_le_of_halfPowerLaw {a : ℕ → ℂ} {x : GaugeTorus}
    (h : GaugeHalfPowerLaw a x) {σ θ : ℝ} (hθ : 0 < θ) (hθσ : θ < 2 * σ - 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℕ, ‖chargedBoundary a σ M N x‖ ≤ C * ((M : ℝ) + 1) ^ (-θ) := by
  obtain ⟨C, hC, hS⟩ := h (2 * σ - θ - 1 / 2) (by linarith)
  refine ⟨C * (2 + (2 * σ) * 2 ^ (2 * σ + 1) / (2 * σ - (2 * σ - θ))), by
    have : 0 < 2 * σ := by linarith
    have : 0 < 2 * σ - (2 * σ - θ) := by linarith
    positivity, fun M N => ?_⟩
  have hb := norm_sum_Ioc_mul_rpow_neg_le (c := fun j => a j * twist x j) hC (by linarith)
    (show 2 * σ - θ < 2 * σ by linarith)
    (fun n => by simpa [show (1 / 2 : ℝ) + (2 * σ - θ - 1 / 2) = 2 * σ - θ by ring] using hS n) M N
  rw [show 2 * σ - θ - 2 * σ = -θ by ring] at hb
  exact hb

/-- **At almost every gauge point every boundary above `¼` decays.** -/
theorem ae_norm_chargedBoundary_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, ∀ σ θ : ℝ, 0 < θ → θ < 2 * σ - 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℕ, ‖chargedBoundary a σ M N x‖ ≤ C * ((M : ℝ) + 1) ^ (-θ) := by
  filter_upwards [ae_gaugeHalfPowerLaw a ha] with x hx σ θ hθ hθσ
  exact norm_chargedBoundary_le_of_halfPowerLaw hx hθ hθσ

/-- **The square-root boundary law** at a gauge point: the critical boundary against the flat
source is `O((M+1)^{−θ})` for every `θ < ½`, uniformly in the horizon. -/
def GaugeBoundaryLaw (a : ℕ → ℂ) (x : GaugeTorus) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M N : ℕ, ‖chargedBoundary a (1 / 2) M N x‖ ≤ C * ((M : ℝ) + 1) ^ (-θ)

theorem gaugeBoundaryLaw_of_halfPowerLaw {a : ℕ → ℂ} {x : GaugeTorus} (h : GaugeHalfPowerLaw a x) :
    GaugeBoundaryLaw a x := fun θ hθ hθ2 =>
  norm_chargedBoundary_le_of_halfPowerLaw h hθ (by linarith)

/-- The critical Möbius boundary at the gauge point `0` is a difference of harmonic sums. -/
theorem chargedBoundary_moebius_zero {M N : ℕ} (hMN : M ≤ N) :
    chargedBoundary (fun n => ((μ n : ℤ) : ℂ)) (1 / 2) M N 0 =
      ((RHTower.deningerHarmonicPartial N - RHTower.deningerHarmonicPartial M : ℝ) : ℂ) := by
  have hsplit : RHTower.deningerHarmonicPartial N - RHTower.deningerHarmonicPartial M =
      ∑ j ∈ Ioc M N, ((μ j : ℤ) : ℝ) / j := by
    simp only [RHTower.deningerHarmonicPartial]
    rw [range_eq_Ico, range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (M + 1))
      (show M + 1 ≤ N + 1 by omega), Ico_add_one_add_one_eq_Ioc]
    ring
  rw [hsplit, chargedBoundary]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [twist_zero, mul_one, show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  push_cast
  rw [div_eq_mul_inv]

/-- **At the gauge point `0` the square-root boundary law is the Riemann hypothesis.** -/
theorem gaugeBoundaryLaw_moebius_zero_iff :
    GaugeBoundaryLaw (fun n => ((μ n : ℤ) : ℂ)) 0 ↔ RiemannHypothesis := by
  constructor
  · intro h
    rw [← RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis]
    intro δ hδ
    set θ := max (1 / 2 - δ) (1 / 4) with hθdef
    have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hθ2 : θ < 1 / 2 := max_lt (by linarith) (by norm_num)
    obtain ⟨C, hC, hB⟩ := h θ hθ0 hθ2
    -- the harmonic partial sums decay like `M^{−θ}`
    have hH : ∀ n : ℕ, 1 ≤ n → |RHTower.deningerHarmonicPartial n| ≤ C * (n : ℝ) ^ (-θ) := by
      intro n hn
      have hlim : Tendsto (fun N => |RHTower.deningerHarmonicPartial N -
          RHTower.deningerHarmonicPartial n|) atTop (𝓝 |0 - RHTower.deningerHarmonicPartial n|) :=
        ((RHTower.tendsto_sum_range_succ_moebius_div.sub_const _).abs)
      have hbd : ∀ᶠ N in atTop, |RHTower.deningerHarmonicPartial N -
          RHTower.deningerHarmonicPartial n| ≤ C * ((n : ℝ) + 1) ^ (-θ) := by
        filter_upwards [eventually_ge_atTop n] with N hN
        have := hB n N
        rwa [chargedBoundary_moebius_zero hN, Complex.norm_real, Real.norm_eq_abs] at this
      have h1 := le_of_tendsto hlim hbd
      rw [zero_sub, abs_neg] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by linarith) (by linarith)
    have hK : 0 ≤ C * (2 + 1 / (1 - θ)) := by
      have : 0 < 1 - θ := by linarith
      positivity
    refine ⟨C * (2 + 1 / (1 - θ)), hK, fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have h0 : RHTower.mobiusMertensPartialSum 0 = 0 := by
        simp [RHTower.mobiusMertensPartialSum, RHTower.mobiusComplexCoefficient]
      rw [h0, norm_zero]
      exact mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
    have hM := BezoutValuationIncidence.abs_sum_moebiusReal_le_of_harmonic_power hθ0 (by linarith)
      hC hH hN
    have hsum : RHTower.mobiusMertensPartialSum N =
        ((∑ n ∈ Icc 1 N, BezoutValuationIncidence.moebiusReal n : ℝ) : ℂ) := by
      simp only [RHTower.mobiusMertensPartialSum, RHTower.mobiusComplexCoefficient,
        BezoutValuationIncidence.moebiusReal]
      have hIcc : Icc 1 N = Ico 1 (N + 1) := by ext n; simp only [mem_Icc, mem_Ico]; omega
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos N), hIcc]
      push_cast
      simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
    rw [hsum, Complex.norm_real, Real.norm_eq_abs]
    refine hM.trans (mul_le_mul_of_nonneg_left ?_ hK)
    calc (N : ℝ) ^ (1 - θ) ≤ ((N : ℝ) + 1) ^ (1 - θ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
            (by linarith [le_max_left (1 / 2 - δ) (1 / 4)])
  · intro hRH
    exact gaugeBoundaryLaw_of_halfPowerLaw (gaugeHalfPowerLaw_moebius_zero_iff.mpr hRH)

/-- **The Liouville twin has no square-root boundary law**: its dyadic boundaries carry
`Σ_{K<j≤2K} μ(j)²/j ≥ 1/100`. -/
theorem not_gaugeBoundaryLaw_moebius_liouville {x : GaugeTorus}
    (hx : ∀ n, n ≠ 0 → twist x n = (-1 : ℂ) ^ ArithmeticFunction.cardFactors n) :
    ¬ GaugeBoundaryLaw (fun n => ((μ n : ℤ) : ℂ)) x := by
  intro h
  obtain ⟨C, hC, hB⟩ := h (1 / 4) (by norm_num) (by norm_num)
  have hblock : ∀ K : ℕ, 1 ≤ K → (1 / 100 : ℝ) ≤ C * ((K : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
    intro K hK
    refine (sum_dyadic_moebius_sq_div_ge hK).trans ?_
    have hval : chargedBoundary (fun n => ((μ n : ℤ) : ℂ)) (1 / 2) K (2 * K) x =
        ((∑ j ∈ Ioc K (2 * K), (μ j : ℝ) ^ 2 / j : ℝ) : ℂ) := by
      rw [chargedBoundary]
      push_cast
      refine sum_congr rfl fun j hj => ?_
      have hj0 : j ≠ 0 := by have := (mem_Ioc.mp hj).1; omega
      rw [hx j hj0, moebius_mul_neg_one_pow_cardFactors, show -(2 * (1 / 2 : ℝ)) = -1 by norm_num,
        Real.rpow_neg_one]
      push_cast
      rw [div_eq_mul_inv]
    have := hB K (2 * K)
    rwa [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun j _ => by
      positivity)] at this
  -- `(K+1)^{−1/4} → 0`
  have hlim : Tendsto (fun K : ℕ => C * ((K : ℝ) + 1) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using this.const_mul C
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))).and
    (eventually_ge_atTop 1) |>.exists
  exact absurd (hblock K hK.2) (not_le.mpr hK.1)

/-- **The Möbius boundary trichotomy.** The square-root boundary law holds at Haar-almost every
point of the Möbius gauge orbit, fails at the Liouville twin, and holds at `0` exactly under RH. -/
theorem moebius_boundary_trichotomy :
    (∀ᵐ x ∂gaugeHaar, GaugeBoundaryLaw (fun n => ((μ n : ℤ) : ℂ)) x) ∧
    (∃ x : GaugeTorus, ¬ GaugeBoundaryLaw (fun n => ((μ n : ℤ) : ℂ)) x) ∧
    (GaugeBoundaryLaw (fun n => ((μ n : ℤ) : ℂ)) 0 ↔ RiemannHypothesis) := by
  obtain ⟨hae, ⟨x, -, hx⟩, -⟩ := moebius_gauge_trichotomy
  exact ⟨hae.mono fun _ => gaugeBoundaryLaw_of_halfPowerLaw,
    ⟨x, not_gaugeBoundaryLaw_moebius_liouville hx⟩, gaugeBoundaryLaw_moebius_zero_iff⟩

end GaloisForLFunctions.ArithmeticCorrelationGeometry
