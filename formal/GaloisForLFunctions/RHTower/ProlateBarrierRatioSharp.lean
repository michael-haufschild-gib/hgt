import GaloisForLFunctions.RHTower.ProlateBarrierRatioTwoSided
import GaloisForLFunctions.RHTower.BesselIZeroUpperBound

/-!
# The barrier ratio from above, at the sharp collar value

The collar comparison `Phi ≤ 3 I₀(c Xi)` was previously used only in its lower half; composing its
upper half with the matching upper bound for `I₀` replaces the loss-free endpoint transport
`Phi(alpha) ≤ exp(c Xi_s(alpha))` by

```text
Phi(alpha)  ≤  3 exp(c Xi_s(alpha)) sqrt(pi / (2 c Xi_s(alpha))) ,
```

which is smaller by a full half power of the bandwidth.  Carrying it through the band transport
divides the squared upper bound of `ProlateBarrierRatioTwoSided` by `c Xi_s(alpha)`:

```text
Phi(y₀)²  ≤  C · (9 pi / 2) / (c Xi_s(alpha)) · exp(2 c Xi_s(y₀) + Lambda) .
```

Against the lower bound of `prolate_band_barrier_ratio_lower`, whose prefactor is
`1/(36 pi² c Xi_s(alpha))`, the two now differ by an absolute constant times `exp(Lambda)` only:
the `c Xi_s(alpha)` cancels exactly.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

section

variable {s c α : ℝ} {Φ : ℝ → ℝ}

/-- **The mode at the collar edge, from above.**  The trapping by `I₀` and the `I₀` upper bound
combine into an explicit exponential with a half power of the bandwidth in the denominator. -/
theorem prolateBand_collar_le_exp_div (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ 2) * deriv (deriv Φ) x - 2 * x * deriv Φ x
        + (s * c ^ 2 - c ^ 2 * x ^ 2) * Φ x = 0)
    (hΦ1 : Φ 1 = 1)
    (hz : 0 < c * bandEndpointPhase s α) :
    Φ α ≤ 3 * (Real.exp (c * bandEndpointPhase s α)
      * Real.sqrt (Real.pi / (2 * (c * bandEndpointPhase s α)))) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hΦc : ContinuousOn Φ (Icc α 1) := hd1.continuous.continuousOn
  have hDΦc : ContinuousOn (deriv Φ) (Icc α 1) := hd2.continuous.continuousOn
  have hΦd : ∀ x ∈ Ioo α 1, HasDerivAt Φ (deriv Φ x) x := fun x _ => (hd1 x).hasDerivAt
  have hDΦd : ∀ x ∈ Ioo α 1, HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x :=
    fun x _ => (hd2 x).hasDerivAt
  have hmain := prolateBand_le_and_le (s := s) (c := c) (Φ := Φ) (DΦ := deriv Φ)
    (DDΦ := deriv (deriv Φ)) hs0 hs1 hc hα hα1 hcollar hΦc hDΦc hΦd hDΦd hode hΦ1
    α ⟨le_rfl, hα1.le⟩
  have hV : bandModel s c α = besselI0 (c * bandEndpointPhase s α) := rfl
  have hup : Φ α ≤ 3 * besselI0 (c * bandEndpointPhase s α) := by
    rw [← hV]
    exact hmain.2
  have hI := besselI0_le_exp_div_sqrt hz
  linarith [hup, mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 3)]

/-- The squared form of the collar bound. -/
theorem prolateBand_collar_sq_le (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ 2) * deriv (deriv Φ) x - 2 * x * deriv Φ x
        + (s * c ^ 2 - c ^ 2 * x ^ 2) * Φ x = 0)
    (hΦ1 : Φ 1 = 1)
    (hz : 0 < c * bandEndpointPhase s α) (hΦα0 : 0 ≤ Φ α) :
    Φ α ^ 2 ≤ 9 * Real.pi / 2 * Real.exp (2 * (c * bandEndpointPhase s α))
        / (c * bandEndpointPhase s α) := by
  have hbase := prolateBand_collar_le_exp_div hs0 hs1 hc hα hα1 hcollar hsm hode hΦ1 hz
  set z : ℝ := c * bandEndpointPhase s α with hzdef
  have hsq := pow_le_pow_left₀ hΦα0 hbase 2
  have hval : (3 * (Real.exp z * Real.sqrt (Real.pi / (2 * z)))) ^ 2
      = 9 * Real.pi / 2 * Real.exp (2 * z) / z := by
    have harg : (0 : ℝ) ≤ Real.pi / (2 * z) := by
      have := Real.pi_pos
      positivity
    have hs2 : Real.sqrt (Real.pi / (2 * z)) ^ 2 = Real.pi / (2 * z) := Real.sq_sqrt harg
    have hexp : Real.exp z ^ 2 = Real.exp (2 * z) := by
      rw [two_mul, Real.exp_add, sq]
    have hexpand : (3 * (Real.exp z * Real.sqrt (Real.pi / (2 * z)))) ^ 2
        = 9 * (Real.exp z ^ 2 * Real.sqrt (Real.pi / (2 * z)) ^ 2) := by ring
    rw [hexpand, hs2, hexp]
    field_simp
  rwa [hval] at hsq

end

/-- **The barrier ratio from above, at the sharp collar value.**  The same statement as
`prolateBand_sq_le_exp_bandPhase` with the loss-free endpoint transport replaced by the collar
comparison, which divides the bound by `c Xi_s(alpha)`. -/
theorem prolateBand_sq_le_exp_bandPhase_sharp {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs8 : s ≤ 1 / 8) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hsy0 : s < y₀ ^ 2) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hz : 0 < c * bandEndpointPhase s α)
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc y₀ α, HasDerivAt (fun u => (1 - u ^ 2) * DΦ u)
      (-(c ^ 2 * (s - t ^ 2) * Φ t)) t) :
    Φ y₀ ^ 2
      ≤ (1 + (1 - α ^ 2) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ 2
            / (c ^ 2 * (α ^ 2 - s)))
        * (9 * Real.pi / 2 / (c * bandEndpointPhase s α))
        * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by
  have hs1 : s < 1 := by linarith
  have hα0 : 0 < α := lt_trans (by norm_num) hα
  have hsα : s < α ^ 2 := by nlinarith
  have hαpos : ∀ u ∈ Icc α 1, 0 < Φ u := fun u hu =>
    hposΦ u ⟨le_trans hy0α hu.1, hu.2⟩
  -- the ordinary differential equation on the collar, from the eigenvalue relation
  have hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ 2) * deriv (deriv Φ) x - 2 * x * deriv Φ x
        + (s * c ^ 2 - c ^ 2 * x ^ 2) * Φ x = 0 := by
    intro x hx
    have hmem : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1, hα], hx.2.le⟩
    have h := heig x hmem
    rw [prolateSLAction] at h
    linarith [h]
  -- the anchor value, now at the sharp collar value
  have hΦα0 : 0 ≤ Φ α := (hαpos α ⟨le_rfl, hα1.le⟩).le
  have hZ : Φ α ^ 2 ≤ 9 * Real.pi / 2 * Real.exp (2 * (c * bandEndpointPhase s α))
      / (c * bandEndpointPhase s α) :=
    prolateBand_collar_sq_le hs0.le hs8 hc hα hα1 hcollar hsm hode hΦ1 hz hΦα0
  have hB := abs_prolateLogDeriv_le_band hc hs0.le hs1 hcs hsm heig hΦ1 hα0 hα1 hsα hαpos
  have hGα := prolateBandAmplitude_anchor_le (c := c) (s := s) (α := α)
    (B := prolateRadialBarrier c s α + 6 / (1 - α)) hc hα0.le hα1 hsα
    (hαpos α ⟨le_rfl, hα1.le⟩) hΦd hB
  set C : ℝ := 1 + (1 - α ^ 2) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ 2
      / (c ^ 2 * (α ^ 2 - s)) with hCdef
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < α ^ 2 - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
    rw [hCdef]
    positivity
  set K : ℝ := 9 * Real.pi / 2 * Real.exp (2 * (c * bandEndpointPhase s α))
      / (c * bandEndpointPhase s α) with hKdef
  have hGZ : prolateBandAmplitude c s Φ DΦ α ≤ C * K := by
    refine le_trans hGα ?_
    have := mul_le_mul_of_nonneg_right hZ hCnn
    linarith [this]
  -- the transport to `y₀`
  have hposband : ∀ t ∈ Icc y₀ α, Φ t ≠ 0 := fun t ht =>
    (hposΦ t ⟨ht.1, le_trans ht.2 hα1.le⟩).ne'
  have hband := prolateBandAmplitude_le_uniform (c := c) (s := s) (y := y₀) hc hy00 hsy0
    le_rfl hy0α hα1 hΦd hfluxd hposband
  have hsq : Φ y₀ ^ 2 ≤ prolateBandAmplitude c s Φ DΦ y₀ := by
    have hK : 0 < prolateBandScale c s y₀ :=
      prolateBandScale_pos hc hsy0 (by nlinarith [hy0α, hα1, hy00])
    exact sq_le_sturmAmplitudeVar hK
  set X : ℝ := 2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + prolateScaleLog s y₀ α with hXdef
  have hexpX : (0 : ℝ) < Real.exp X := Real.exp_pos _
  have hexpsplit : Real.exp (2 * (c * bandEndpointPhase s α)) * Real.exp X
      = Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by
    rw [← Real.exp_add, hXdef]
    congr 1
    ring
  have hzne : c * bandEndpointPhase s α ≠ 0 := hz.ne'
  have hfinal : C * K * Real.exp X
      = C * (9 * Real.pi / 2 / (c * bandEndpointPhase s α))
        * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := by
    rw [hKdef, ← hexpsplit]
    field_simp
  calc Φ y₀ ^ 2 ≤ prolateBandAmplitude c s Φ DΦ y₀ := hsq
    _ ≤ prolateBandAmplitude c s Φ DΦ α * Real.exp X := hband
    _ ≤ (C * K) * Real.exp X := mul_le_mul_of_nonneg_right hGZ hexpX.le
    _ = C * (9 * Real.pi / 2 / (c * bandEndpointPhase s α))
        * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α) := hfinal


/-- **The barrier ratio between two apertures of the same bandwidth.**  The sharp collar upper bound
for one mode and the collar lower bound for another have the *same* `c Xi_s(alpha)` prefactor, which
therefore cancels: the quotient of the two squared amplitudes at a common band point is an absolute
constant times the barrier factor, the exponential of the phase difference, and the band-scale
logarithm. -/
theorem prolateBand_sq_ratio_le {c sn sm y₀ α : ℝ} {Φn DΦn Φm : ℝ → ℝ}
    (hc : 0 < c) (hsn0 : 0 < sn) (hsn8 : sn ≤ 1 / 8) (hcsn : 4 ≤ c * sn)
    (hsmn0 : 0 ≤ sm) (hsm8 : sm ≤ 1 / 8)
    (hsmn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φn)
    (heign : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φn y = -(sn * c ^ 2) * Φn y)
    (hΦn1 : Φn 1 = 1)
    (hsmm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φm)
    (heigm : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φm y = -(sm * c ^ 2) * Φm y)
    (hΦm1 : Φm 1 = 1)
    (hsy0n : sn < y₀ ^ 2) (hsy0m : sm < y₀ ^ 2) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hzn : 0 < c * bandEndpointPhase sn α) (hzm : 1 ≤ c * bandEndpointPhase sm α)
    (hposn : ∀ t ∈ Icc y₀ 1, 0 < Φn t) (hposm : ∀ t ∈ Icc y₀ 1, 0 < Φm t)
    (hΦnd : ∀ t, HasDerivAt Φn (DΦn t) t)
    (hfluxn : ∀ t ∈ Icc y₀ α, HasDerivAt (fun u => (1 - u ^ 2) * DΦn u)
      (-(c ^ 2 * (sn - t ^ 2) * Φn t)) t)
    (hphase : bandEndpointPhase sn α = bandEndpointPhase sm α) :
    Φn y₀ ^ 2
      ≤ 162 * Real.pi ^ 3
          * (1 + (1 - α ^ 2) * (prolateRadialBarrier c sn α + 6 / (1 - α)) ^ 2
              / (c ^ 2 * (α ^ 2 - sn)))
          * Real.exp (2 * c * (bandEndpointPhase sn y₀ - bandEndpointPhase sm y₀)
              + prolateScaleLog sn y₀ α
              - 12 * (Real.log (1 - α) - Real.log (1 - y₀)))
          * Φm y₀ ^ 2 := by
  have hup := prolateBand_sq_le_exp_bandPhase_sharp hc hsn0 hsn8 hcsn hsmn heign hΦn1 hsy0n hy00
    hy0α hα hα1 hcollar hzn hposn hΦnd hfluxn
  have hlow := prolateBand_barrier_ratio_lower (s := sm) (c := c) (α := α) (y₀ := y₀) (Φ := Φm)
    hsmn0 hsm8 hc hα hα1 hcollar hsmm heigm hΦm1 hy00.le hy0α hsy0m hposm hzm
  set z : ℝ := c * bandEndpointPhase sm α with hzdef
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hzm
  have hzn' : c * bandEndpointPhase sn α = z := by rw [hzdef, hphase]
  set E : ℝ := Real.exp (c * bandEndpointPhase sm y₀
      + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hden : (0 : ℝ) < 6 * Real.pi * Real.sqrt z := by
    have h1 : (0 : ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz0
    have := Real.pi_pos
    positivity
  -- the squared lower bound
  have hlow2 : E ^ 2 / (36 * Real.pi ^ 2 * z) ≤ Φm y₀ ^ 2 := by
    have hbase : E / (6 * Real.pi * Real.sqrt z) ≤ Φm y₀ := hlow
    have hnn : 0 ≤ E / (6 * Real.pi * Real.sqrt z) := le_of_lt (by positivity)
    have hsq := pow_le_pow_left₀ hnn hbase 2
    have hval : (E / (6 * Real.pi * Real.sqrt z)) ^ 2 = E ^ 2 / (36 * Real.pi ^ 2 * z) := by
      rw [div_pow, mul_pow, mul_pow]
      rw [Real.sq_sqrt hz0.le]
      norm_num
    rwa [hval] at hsq
  -- rewrite the upper bound with the common prefactor
  set C : ℝ := 1 + (1 - α ^ 2) * (prolateRadialBarrier c sn α + 6 / (1 - α)) ^ 2
      / (c ^ 2 * (α ^ 2 - sn)) with hCdef
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < α ^ 2 - sn := by nlinarith [hy0α, hy00, hsy0n]
    have h2 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
    rw [hCdef]
    positivity
  rw [hzn'] at hup
  set W : ℝ := Real.exp (2 * c * (bandEndpointPhase sn y₀ - bandEndpointPhase sm y₀)
      + prolateScaleLog sn y₀ α
      - 12 * (Real.log (1 - α) - Real.log (1 - y₀))) with hWdef
  have hWpos : 0 < W := Real.exp_pos _
  have hsplit : Real.exp (2 * c * bandEndpointPhase sn y₀ + prolateScaleLog sn y₀ α)
      = W * E ^ 2 := by
    rw [hWdef, hEdef, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit] at hup
  -- assemble
  have hstep : C * (9 * Real.pi / 2 / z) * (W * E ^ 2)
      ≤ 162 * Real.pi ^ 3 * C * W * Φm y₀ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlow2
      (le_of_lt (by positivity : (0 : ℝ) < 162 * Real.pi ^ 3 * C * W + 1))
    have hkey : 162 * Real.pi ^ 3 * C * W * (E ^ 2 / (36 * Real.pi ^ 2 * z))
        = C * (9 * Real.pi / 2 / z) * (W * E ^ 2) := by
      have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
      field_simp
      ring
    calc C * (9 * Real.pi / 2 / z) * (W * E ^ 2)
        = 162 * Real.pi ^ 3 * C * W * (E ^ 2 / (36 * Real.pi ^ 2 * z)) := hkey.symm
      _ ≤ 162 * Real.pi ^ 3 * C * W * Φm y₀ ^ 2 := by
          refine mul_le_mul_of_nonneg_left hlow2 ?_
          have := Real.pi_pos
          positivity
  exact le_trans hup hstep

end GaloisForLFunctions.RHTower

end
