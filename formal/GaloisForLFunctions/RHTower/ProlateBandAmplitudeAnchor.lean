import GaloisForLFunctions.RHTower.ProlateBandAmplitudeTransport
import GaloisForLFunctions.RHTower.ProlateEndpointUpperBound
import GaloisForLFunctions.RHTower.ProlateTurningLayer
import GaloisForLFunctions.RHTower.ProlateAnchorActionUpperBound

/-!
# The band amplitude at an anchor is comparable to the value there

The amplitude `G = Phi² + ((1−y²)Phi')²/K` differs from `Phi²` only through the flux, and in the
forbidden band the flux is controlled by the value: the logarithmic derivative is trapped between
the two barriers already available,

```text
W(y) − 6/(1 − y)  ≤  −Phi'/Phi  ≤  c sqrt(1−s) y / sqrt(1 − y²) ,
```

the first from the endpoint upper bound and the second from the radial barrier.  Since `W ≥ 0`, both
give `|Phi'/Phi| ≤ barrier + 6/(1 − y)`, and at the band scale `K = c²(y²−s)(1−y²)` the flux term is
then a bounded multiple of `Phi²`:

```text
G(α)  ≤  Phi(α)² · (1 + (1 − α²) B² / (c²(α² − s))) ,      B = barrier(α) + 6/(1 − α) .
```

For an anchor at fixed distance from the endpoint the bracket is an absolute constant: `B` is of
order `c`, and the `c²` in the denominator absorbs it.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The logarithmic derivative is trapped in the band.**  The upper barrier is the radial one,
the lower is the endpoint bound; the WKB profile being nonnegative, the latter degenerates to
`−6/(1 − α)`. -/
theorem abs_prolateLogDeriv_le_band {c s α : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1) (hα0 : 0 < α) (hα1 : α < 1) (hsα : s < α ^ 2)
    (hpos : ∀ u ∈ Icc α 1, 0 < Φ u) :
    |prolateLogDeriv Φ α| ≤ prolateRadialBarrier c s α + 6 / (1 - α) := by
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hupper : prolateLogDeriv Φ α ≤ prolateRadialBarrier c s α :=
    prolateLogDeriv_le_radialBarrier_of_endpoint_normalized hc hs0 hs1 hcs hα0 hα1 hsm heig hΦ1
      hpos
  have hcχ : (0 : ℝ) ≤ c ^ 2 + -(s * c ^ 2) := by nlinarith [sq_nonneg c]
  have hturn : ∀ u ∈ Icc α 1, (0 : ℝ) ≤ -(s * c ^ 2) + c ^ 2 * u ^ 2 := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hα0.le hu.1
    have hsq : α ^ 2 ≤ u ^ 2 := by nlinarith [hu.1, hα0]
    nlinarith [mul_nonneg (sq_nonneg c) (by linarith : (0:ℝ) ≤ u ^ 2 - s)]
  have hQ0 : (0 : ℝ) < -(s * c ^ 2) + c ^ 2 * α ^ 2 := by
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsα)]
  have hlower := prolateWKB_sub_six_div_le_prolateLogDeriv (c := c) (χ := -(s * c ^ 2))
    hsm heig hcχ hα0.le hα1 hpos hturn hQ0
  have hWnn : (0 : ℝ) ≤ prolateWKB c (-(s * c ^ 2)) α := Real.sqrt_nonneg _
  have hbar : (0 : ℝ) ≤ prolateRadialBarrier c s α := by
    rw [prolateRadialBarrier]
    have h2 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
    have h3 : (0 : ℝ) < Real.sqrt (1 - α ^ 2) := Real.sqrt_pos.2 h2
    have h4 : (0 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
    positivity
  have hsix : (0 : ℝ) < 6 / (1 - α) := by positivity
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The anchor amplitude is a bounded multiple of the anchor value.** -/
theorem prolateBandAmplitude_anchor_le {c s α B : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hα0 : 0 ≤ α) (hα1 : α < 1) (hsα : s < α ^ 2)
    (hΦpos : 0 < Φ α) (hDΦ : ∀ y, HasDerivAt Φ (DΦ y) y)
    (hB : |prolateLogDeriv Φ α| ≤ B) :
    prolateBandAmplitude c s Φ DΦ α
      ≤ Φ α ^ 2 * (1 + (1 - α ^ 2) * B ^ 2 / (c ^ 2 * (α ^ 2 - s))) := by
  have h2 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have h1 : (0 : ℝ) < α ^ 2 - s := by linarith
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hderiv : deriv Φ α = DΦ α := (hDΦ α).deriv
  have hflux : DΦ α = -(prolateLogDeriv Φ α) * Φ α := by
    rw [prolateLogDeriv, hderiv]
    field_simp
  have hsq : DΦ α ^ 2 ≤ B ^ 2 * Φ α ^ 2 := by
    rw [hflux]
    have habs : |(-(prolateLogDeriv Φ α)) * Φ α| ≤ B * |Φ α| := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    have hBnn : 0 ≤ B := le_trans (abs_nonneg _) hB
    nlinarith [sq_abs ((-(prolateLogDeriv Φ α)) * Φ α), sq_abs (Φ α), abs_nonneg (Φ α),
      abs_nonneg ((-(prolateLogDeriv Φ α)) * Φ α), habs, hBnn]
  rw [prolateBandAmplitude, sturmAmplitudeVar, prolateBandScale]
  have hKpos : (0 : ℝ) < c ^ 2 * (α ^ 2 - s) * (1 - α ^ 2) := by positivity
  have hnum : ((1 - α ^ 2) * DΦ α) ^ 2 ≤ (1 - α ^ 2) ^ 2 * (B ^ 2 * Φ α ^ 2) := by
    have : ((1 - α ^ 2) * DΦ α) ^ 2 = (1 - α ^ 2) ^ 2 * DΦ α ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have hdiv : ((1 - α ^ 2) * DΦ α) ^ 2 / (c ^ 2 * (α ^ 2 - s) * (1 - α ^ 2))
      ≤ (1 - α ^ 2) ^ 2 * (B ^ 2 * Φ α ^ 2) / (c ^ 2 * (α ^ 2 - s) * (1 - α ^ 2)) := by
    gcongr
  have hval : (1 - α ^ 2) ^ 2 * (B ^ 2 * Φ α ^ 2) / (c ^ 2 * (α ^ 2 - s) * (1 - α ^ 2))
      = Φ α ^ 2 * ((1 - α ^ 2) * B ^ 2 / (c ^ 2 * (α ^ 2 - s))) := by
    field_simp
  rw [hval] at hdiv
  nlinarith [hdiv]

/-! ## The two transports -/

/-- **The crude transport across a short window.**  The radial barrier is finite at the turning
point, so it can carry the solution across the turning layer; over a window of width `O(s)` its
integral is `O(cs)`. -/
theorem prolate_le_mul_exp_radialBarrier {c s a b : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1) (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    (hpos : ∀ y ∈ Icc a 1, 0 < Φ y) :
    Φ a ≤ Φ b * Real.exp (c * Real.sqrt (1 - s)
      * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2))) := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hsub : Icc a b ⊆ Icc a 1 := Icc_subset_Icc le_rfl hb1.le
  have hp : ∀ y ∈ Icc a b, (0 : ℝ) < 1 - y ^ 2 := by
    intro y hy
    have h1 : 0 < y := lt_of_lt_of_le ha0 hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb1
    nlinarith
  have hf : ∀ t ∈ Icc a b, HasDerivAt Φ (deriv Φ t) t := fun t _ => (hd1 t).hasDerivAt
  have hposab : ∀ t ∈ Icc a b, 0 < Φ t := fun t ht => hpos t (hsub ht)
  have hL : ContinuousOn (fun y : ℝ => -prolateRadialBarrier c s y) (Icc a b) :=
    (continuousOn_prolateRadialBarrier hp).neg
  have hbound : ∀ t ∈ Icc a b, (-prolateRadialBarrier c s t) * Φ t ≤ deriv Φ t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hb1
    have hpost : ∀ u ∈ Icc t 1, 0 < Φ u := fun u hu =>
      hpos u ⟨le_trans ht.1 hu.1, hu.2⟩
    have hlog := prolateLogDeriv_le_radialBarrier_of_endpoint_normalized hc hs0 hs1 hcs ht0 ht1
      hsm heig hΦ1 hpost
    rw [prolateLogDeriv] at hlog
    have hΦt : 0 < Φ t := hposab t ht
    have hdiv : -prolateRadialBarrier c s t ≤ deriv Φ t / Φ t := by linarith
    rwa [le_div_iff₀ hΦt] at hdiv
  have hmain := mul_exp_integral_le_of_logDeriv_ge' hab hf hposab hL hbound
  have hint : (∫ y in a..b, -prolateRadialBarrier c s y)
      = -(c * Real.sqrt (1 - s) * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2))) := by
    rw [intervalIntegral.integral_neg,
      integral_prolateRadialBarrier hab (by linarith) hb1]
  rw [hint, Real.exp_neg, ← div_eq_mul_inv] at hmain
  have hexp : (0 : ℝ) < Real.exp (c * Real.sqrt (1 - s)
      * (Real.sqrt (1 - a ^ 2) - Real.sqrt (1 - b ^ 2))) := Real.exp_pos _
  exact (div_le_iff₀ hexp).mp hmain

/-- **The sharp transport to the endpoint.**  Between an anchor in the slowly-varying part of the
band and the endpoint the loss is exactly the band phase at the anchor, with no correction. -/
theorem prolate_anchor_le_exp_bandPhase {c s a : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hc : 0 < c) (hs1 : s < 1) (hsa : s ≤ a ^ 2) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hpos : ∀ y ∈ Icc a 1, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a 1, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2)) :
    Φ a ≤ Φ 1 * Real.exp (c * bandEndpointPhase s a) := by
  have hΦcont : Continuous Φ := hsm.continuous
  have hΦ1 : 0 < Φ 1 := hpos 1 (right_mem_Icc.mpr ha1.le)
  have hev : ∀ᶠ b in 𝓝[<] (1 : ℝ),
      Φ a * Real.exp (-(c * (bandEndpointPhase s a - bandEndpointPhase s b))) ≤ Φ b := by
    filter_upwards [eventually_prolateLogDeriv_le_prolateWKB (c := c) (s := s) hsm hΦ1 hc hs1,
      self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds ha1)] with b hinit hb1 hab
    have hb : b < 1 := hb1
    have hsub : Icc a b ⊆ Icc a 1 := Icc_subset_Icc le_rfl hb.le
    have hmain := le_endpoint_prolateWKB hsm heig hab.le ha0 (by linarith) hb
      (fun y hy => hpos y (hsub hy)) (fun y hy => hQ y (hsub hy))
      (fun y hy => houter y (hsub hy)) hinit
    have hprof : (∫ t in a..b, prolateWKB c (-(s * c ^ 2)) t)
        = c * (bandEndpointPhase s a - bandEndpointPhase s b) := by
      have hfun : (∫ t in a..b, prolateWKB c (-(s * c ^ 2)) t)
          = ∫ t in a..b, c * prolateWKBProfile s t :=
        intervalIntegral.integral_congr fun t _ => prolateWKB_eq_mul_profile hc.le
      rw [hfun, intervalIntegral.integral_const_mul,
        bandEndpointPhase_sub_eq_integral ha0 hab.le hb hsa]
    rwa [hprof] at hmain
  have hlim1 : Tendsto (fun b : ℝ =>
      Φ a * Real.exp (-(c * (bandEndpointPhase s a - bandEndpointPhase s b))))
      (𝓝[<] (1 : ℝ)) (𝓝 (Φ a * Real.exp (-(c * (bandEndpointPhase s a - bandEndpointPhase s 1))))) := by
    have hcont : Continuous (fun b : ℝ =>
        Φ a * Real.exp (-(c * (bandEndpointPhase s a - bandEndpointPhase s b)))) :=
      continuous_const.mul (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_const.sub (continuous_bandEndpointPhase s))).neg))
    exact (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto Φ (𝓝[<] (1 : ℝ)) (𝓝 (Φ 1)) :=
    (hΦcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2 hev
  rw [bandEndpointPhase_one, sub_zero] at hle
  have hexp : (0 : ℝ) < Real.exp (c * bandEndpointPhase s a) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv] at hle
  exact (div_le_iff₀ hexp).mp hle

/-! ## The sharp bound at the turning point -/

/-- **The turning-point amplitude at the sharp action.**  The three transports compose: the sharp
endpoint bound down to the collar anchor, the variable-scale amplitude envelope across the band, and
the crude radial barrier over the last window of width `O(s)`.  The exponent is `2 c Xi_s(y₀)` — the
sharp action up to the turning layer — plus the logarithm of the scale ratio and the `O(cs)` cost of
the last window. -/
theorem prolate_turningPoint_sq_le_exp {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hsy0 : s < y₀ ^ 2) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ y ∈ Icc α 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2))
    (hpos : ∀ y ∈ Icc (Real.sqrt s) 1, 0 < Φ y)
    (hDΦ : ∀ y, HasDerivAt Φ (DΦ y) y)
    (hfluxd : ∀ y ∈ Icc y₀ α, HasDerivAt (fun t => (1 - t ^ 2) * DΦ t)
      (-(c ^ 2 * (s - y ^ 2) * Φ y)) y) :
    Φ (Real.sqrt s) ^ 2
      ≤ (1 + (1 - α ^ 2) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ 2
            / (c ^ 2 * (α ^ 2 - s)))
        * Real.exp (2 * c * bandEndpointPhase s y₀
            + ((Real.log (α ^ 2 - s) - Real.log (y₀ ^ 2 - s))
              + (Real.log (1 - y₀ ^ 2) - Real.log (1 - α ^ 2)))
            + 2 * (c * Real.sqrt (1 - s)
                * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ 2)))) := by
  have hs0' : 0 < s := by nlinarith
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0
  have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0'
  have hsy : Real.sqrt s ≤ y₀ := by nlinarith [hsq, hy00]
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ 2 := by nlinarith [hy0α, hy00]
  have hαmem : ∀ y ∈ Icc α 1, 0 < Φ y := fun y hy =>
    hpos y ⟨le_trans (le_trans hsy hy0α) hy.1, hy.2⟩
  have hy0mem : ∀ y ∈ Icc y₀ α, 0 < Φ y := fun y hy =>
    hpos y ⟨le_trans hsy hy.1, le_trans hy.2 hα1.le⟩
  have hQα : ∀ y ∈ Icc α 1, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2 := by
    intro y hy
    have hsqy : α ^ 2 ≤ y ^ 2 := by nlinarith [hy.1, hα0]
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsα)]
  -- (1) the sharp endpoint bound at the anchor
  have h1 : Φ α ≤ Real.exp (c * bandEndpointPhase s α) := by
    have := prolate_anchor_le_exp_bandPhase hsm heig hc hs1 hsα.le hα0.le hα1 hαmem hQα houter
    rwa [hΦ1, one_mul] at this
  -- (2) the anchor amplitude
  have hB := abs_prolateLogDeriv_le_band hc hs0 hs1 hcs hsm heig hΦ1 hα0 hα1 hsα hαmem
  have h2 := prolateBandAmplitude_anchor_le (c := c) (s := s) (α := α)
    (B := prolateRadialBarrier c s α + 6 / (1 - α)) hc hα0.le hα1 hsα
    (hαmem α ⟨le_rfl, hα1.le⟩) hDΦ hB
  -- (3) the band transport
  have h3 := prolateBand_amplitude_le (c := c) (s := s) hc hy00.le hsy0 hy0α hα1
    (fun y _ => hDΦ y) hfluxd (fun y hy => (hy0mem y hy).ne')
  -- (4) the value at the anchor
  have h4 : Φ y₀ ^ 2 ≤ prolateBandAmplitude c s Φ DΦ y₀ := by
    have hKpos : 0 < prolateBandScale c s y₀ :=
      prolateBandScale_pos hc hsy0 (by nlinarith [hy0α, hα1, hy00])
    exact sq_le_sturmAmplitudeVar hKpos
  -- (5) the crude window
  have h5 : Φ (Real.sqrt s) ≤ Φ y₀ * Real.exp (c * Real.sqrt (1 - s)
      * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ 2))) := by
    have := prolate_le_mul_exp_radialBarrier hc hs0 hs1 hcs hsm heig hΦ1 hsqrt0 hsy
      (by nlinarith [hy0α, hα1]) hpos
    rwa [hsq] at this
  -- assemble
  set C : ℝ := 1 + (1 - α ^ 2) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ 2
      / (c ^ 2 * (α ^ 2 - s)) with hCdef
  set E : ℝ := 2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + (Real.log (α ^ 2 - s) - Real.log (y₀ ^ 2 - s))
      + (Real.log (1 - y₀ ^ 2) - Real.log (1 - α ^ 2)) with hEdef
  set D : ℝ := c * Real.sqrt (1 - s) * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ 2)) with hDdef
  have hΦy0 : 0 < Φ y₀ := hy0mem y₀ ⟨le_rfl, hy0α⟩
  have hexpD : (0 : ℝ) < Real.exp D := Real.exp_pos _
  have hexpE : (0 : ℝ) < Real.exp E := Real.exp_pos _
  have hstep5 : Φ (Real.sqrt s) ^ 2 ≤ Φ y₀ ^ 2 * Real.exp (2 * D) := by
    have hnn : 0 ≤ Φ (Real.sqrt s) := (hpos _ ⟨le_rfl, by nlinarith [hsq]⟩).le
    have hprod : 0 ≤ Φ y₀ * Real.exp D := by positivity
    have hsq2 : Φ (Real.sqrt s) ^ 2 ≤ (Φ y₀ * Real.exp D) ^ 2 := by
      exact pow_le_pow_left₀ hnn h5 2
    have hval : (Φ y₀ * Real.exp D) ^ 2 = Φ y₀ ^ 2 * Real.exp (2 * D) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    linarith [hsq2, hval.le, hval.ge]
  have hstep34 : Φ y₀ ^ 2 ≤ prolateBandAmplitude c s Φ DΦ α * Real.exp E :=
    le_trans h4 h3
  have hstep2 : prolateBandAmplitude c s Φ DΦ α ≤ Real.exp (c * bandEndpointPhase s α) ^ 2 * C := by
    refine le_trans h2 ?_
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      have h1' : (0 : ℝ) < α ^ 2 - s := by linarith
      have h2' : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
      positivity
    have hΦαnn : 0 ≤ Φ α := (hαmem α ⟨le_rfl, hα1.le⟩).le
    have := pow_le_pow_left₀ hΦαnn h1 2
    nlinarith [this, hCnn]
  have hexpα : Real.exp (c * bandEndpointPhase s α) ^ 2
      = Real.exp (2 * (c * bandEndpointPhase s α)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [hexpα] at hstep2
  -- collect the exponentials
  have hfinal : Real.exp (2 * (c * bandEndpointPhase s α)) * Real.exp E * Real.exp (2 * D)
      = Real.exp (2 * c * bandEndpointPhase s y₀
          + ((Real.log (α ^ 2 - s) - Real.log (y₀ ^ 2 - s))
            + (Real.log (1 - y₀ ^ 2) - Real.log (1 - α ^ 2)))
          + 2 * D) := by
    rw [← Real.exp_add, ← Real.exp_add, hEdef]
    congr 1
    ring
  calc Φ (Real.sqrt s) ^ 2 ≤ Φ y₀ ^ 2 * Real.exp (2 * D) := hstep5
    _ ≤ (prolateBandAmplitude c s Φ DΦ α * Real.exp E) * Real.exp (2 * D) := by
        exact mul_le_mul_of_nonneg_right hstep34 (Real.exp_pos _).le
    _ ≤ ((Real.exp (2 * (c * bandEndpointPhase s α)) * C) * Real.exp E) * Real.exp (2 * D) := by
        gcongr
    _ = C * (Real.exp (2 * (c * bandEndpointPhase s α)) * Real.exp E * Real.exp (2 * D)) := by
        ring
    _ = C * Real.exp (2 * c * bandEndpointPhase s y₀
          + ((Real.log (α ^ 2 - s) - Real.log (y₀ ^ 2 - s))
            + (Real.log (1 - y₀ ^ 2) - Real.log (1 - α ^ 2)))
          + 2 * D) := by rw [hfinal]

/-! ## The interior mass at the sharp action -/

/-- **The aperture mass at the sharp action.**  Composing the turning-point bound with the corpus's
uniform envelope replaces the crude clock `exp(2c(1−s))` by the sharp `exp(2 c Xi_s(y₀))`, at the
cost of the scale ratio and the `O(cs)` window — both polynomial in `c` for a fixed mode. -/
theorem integral_sq_le_exp_sharp_action {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hscale : 1 ≤ c * Real.sqrt s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ 2) (hy00 : 0 < y₀) (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ y ∈ Icc α 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2))
    (hpos : ∀ y ∈ Icc (Real.sqrt s) 1, 0 < Φ y)
    (hDΦ : ∀ y, HasDerivAt Φ (DΦ y) y)
    (hfluxd : ∀ y ∈ Icc y₀ α, HasDerivAt (fun t => (1 - t ^ 2) * DΦ t)
      (-(c ^ 2 * (s - y ^ 2) * Φ y)) y) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ 2)
      ≤ 4 * Real.exp 1 * (c / Real.sqrt s)
        * ((1 + (1 - α ^ 2) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ 2
              / (c ^ 2 * (α ^ 2 - s)))
          * Real.exp (2 * c * bandEndpointPhase s y₀
              + ((Real.log (α ^ 2 - s) - Real.log (y₀ ^ 2 - s))
                + (Real.log (1 - y₀ ^ 2) - Real.log (1 - α ^ 2)))
              + 2 * (c * Real.sqrt (1 - s)
                  * (Real.sqrt (1 - s) - Real.sqrt (1 - y₀ ^ 2))))) := by
  have hs0' : 0 < s := by nlinarith
  have henv := integral_sq_le_turning_amplitude_envelope hc hs0' hs1 hcs hscale hsm heig hΦ1 heven
  have hturn := prolate_turningPoint_sq_le_exp hc hs0 hs1 hcs hsm heig hΦ1 hsy0 hy00 hy0α hα1
    houter hpos hDΦ hfluxd
  have hfac : (0 : ℝ) ≤ 4 * Real.exp 1 * (c / Real.sqrt s) := by
    have h1 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs0'
    positivity
  exact le_trans henv (mul_le_mul_of_nonneg_left hturn hfac)

/-! ## The leakage from below -/

/-- **The leakage lower bound from a mass sandwich.**  Any lower bound on the exterior mass and any
upper bound on the interior mass give a lower bound on the leakage. -/
theorem leakage_lower_of_mass_bounds {outside inside value leakage Lout Uin : ℝ}
    (hLout : 0 ≤ Lout) (hout : Lout ≤ outside) (hin : inside ≤ Uin) (hUin : 0 < Uin)
    (hvalue : 1 / 2 ≤ value ^ 2) (hleak : 0 ≤ leakage)
    (hmass : outside = inside * leakage / value ^ 2) :
    Lout / (2 * Uin) ≤ leakage := by
  have hv0 : (0 : ℝ) < value ^ 2 := by linarith
  have hvne : value ≠ 0 := by
    intro h
    rw [h] at hv0
    simp at hv0
  have hkey : outside * value ^ 2 = inside * leakage := by
    rw [hmass]
    field_simp
  have h1 : Lout * value ^ 2 ≤ outside * value ^ 2 :=
    mul_le_mul_of_nonneg_right hout hv0.le
  have h2 : Lout / 2 ≤ Lout * value ^ 2 := by nlinarith [hLout, hvalue]
  have h3 : inside * leakage ≤ Uin * leakage := mul_le_mul_of_nonneg_right hin hleak
  have h4 : Lout / 2 ≤ Uin * leakage := by linarith [h1, h2, h3, hkey.le, hkey.ge]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Uin)]
  linarith

end GaloisForLFunctions.RHTower

end
