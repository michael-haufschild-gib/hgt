import GaloisForLFunctions.RHTower.ProlateGroundLeakageUpper
import GaloisForLFunctions.RHTower.ProlateLeakageRatioBounds

/-!
# The leakage ladder separates: consecutive Fourier-even leakages have vanishing ratio

Both explicit leakage bounds are a power of the bandwidth times the common factor `e^{-2c}`:

```text
d_m(a) ≤ C_U · c^{1 + c s_m/(2 sqrt(1 - K^{-2}))} · e^{-2c} · (bounded)
d_n(a) ≥ C_L · c^{-2 + c s_n/2}               · e^{-2c} · (bounded)
```

Because `c·s_k → 4k+1`, the two exponents approach `1 + (4m+1)/(2 sqrt(1-K^{-2}))` and
`(4n+1)/2 - 2`.  Taking `K` large makes the first as close to `1 + (4m+1)/2` as wanted, so the
ratio carries the bandwidth power `3 + (4m+1)/2 - (4n+1)/2 = 3 - 2(n-m)`, which is negative as soon
as `n ≥ m + 2`.

Both remaining factors converge — the bandwidth-free part of the upper action is a continuous
function of `c·s_m` alone, and the lower one of `c·s_n` alone — so the whole ratio is a convergent
factor times a negative power of the bandwidth.

Consecutive *Fourier-even* indices jump the corpus index by two, which is exactly the `n = m + 2`
needed; an extra half power of the bandwidth (the aperture itself) is still affordable, which is
what the aperture-weighted tail of the constrained transfer consumes.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-! ## Eventual size of the separation ratio -/

theorem eventually_signedModeRadialData_s_pos (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, 0 < (signedModeRadialData a n).s := by
  have hlimit := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hpos : ∀ᶠ a : ℝ in atTop,
      0 < signedModeRadialBandwidth a * (signedModeRadialData a n).s :=
    hlimit.eventually (eventually_gt_nhds (by positivity))
  filter_upwards [hpos, tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
    with a hcs hc
  nlinarith [hcs, hc]

theorem eventually_signedModeRadialData_s_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, (signedModeRadialData a n).s ≤ ε := by
  have hlimit := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hhi : ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s < 4 * (n : ℝ) + 2 :=
    hlimit.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hhi, tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop
    (max 1 ((4 * (n : ℝ) + 2) / ε))] with a hcs hc
  have hc1 : (1 : ℝ) ≤ signedModeRadialBandwidth a := le_trans (le_max_left _ _) hc
  have hcε : (4 * (n : ℝ) + 2) / ε ≤ signedModeRadialBandwidth a :=
    le_trans (le_max_right _ _) hc
  have hcpos : (0 : ℝ) < signedModeRadialBandwidth a := by linarith
  have hkey : 4 * (n : ℝ) + 2 ≤ ε * signedModeRadialBandwidth a := by
    rw [div_le_iff₀ hε] at hcε
    linarith
  nlinarith [hcs, hkey, hcpos]

/-! ## The two explicit bounds, as powers of the bandwidth -/

/-- The constant of the upper power bound. -/
def leakageLadderUpperConst : ℝ := 2 * Real.exp 1 * leakageUpperConst

theorem leakageLadderUpperConst_nonneg : 0 ≤ leakageLadderUpperConst := by
  have h := leakageUpperConst_nonneg
  have h1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  rw [leakageLadderUpperConst]
  positivity

/-- **The leakage of any fixed mode is a power of the bandwidth times `e^{-2c}`.** -/
theorem eventually_signedLeakage_le_pow (m : ℕ) {K : ℝ} (hK : 2 ≤ K) :
    ∀ᶠ a : ℝ in atTop,
      evenProlateSignedLeakage a m
        ≤ leakageLadderUpperConst * signedModeRadialBandwidth a
            * Real.exp (-(2 * signedModeRadialBandwidth a))
            * Real.exp (phaseTail K
                (signedModeRadialBandwidth a * (signedModeRadialData a m).s))
            * signedModeRadialBandwidth a
              ^ (signedModeRadialBandwidth a * (signedModeRadialData a m).s
                  / (2 * Real.sqrt (1 - 1 / K ^ 2))) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hεK : (0 : ℝ) < 1 / (4 * K ^ 2) := by positivity
  filter_upwards [eventually_signedLeakage_upper m,
    eventually_signedModeRadialData_s_pos m,
    eventually_signedModeRadialData_s_le m (show (0 : ℝ) < 1 / 64 by norm_num),
    eventually_signedModeRadialData_s_le m hεK,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (64 : ℝ)]
    with a hup hs0 hs64 hsK hc64
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set s : ℝ := (signedModeRadialData a m).s with hsdef
  have hc8 : (8 : ℝ) ≤ c := by linarith
  have hshift := prolateLeakageUpperShift_le (c := c) (s := s) hc64 hs0 hs64
  have hbase := prolateLeakageUpper_le (c := c) (s := s) hc8 hs0 hs64
  have hKs : K * Real.sqrt s ≤ 1 / 2 := by
    have hsq : Real.sqrt s ≤ 1 / (2 * K) := by
      have h := Real.sqrt_le_sqrt hsK
      have hval : Real.sqrt (1 / (4 * K ^ 2)) = 1 / (2 * K) := by
        rw [show (1 : ℝ) / (4 * K ^ 2) = (1 / (2 * K)) ^ 2 by field_simp; ring,
          Real.sqrt_sq (by positivity)]
      rwa [hval] at h
    have h2K : (0 : ℝ) < 2 * K := by linarith
    calc K * Real.sqrt s ≤ K * (1 / (2 * K)) :=
          mul_le_mul_of_nonneg_left hsq hK0.le
      _ = 1 / 2 := by field_simp
  have hphase := exp_neg_two_mul_phase_le (c := c) (s := s) (K := K) hc8 hs0 hK hKs
  have hUnn : (0 : ℝ) ≤ leakageUpperConst * c := by
    have := leakageUpperConst_nonneg
    positivity
  have hpowval : c ^ (c * s / (2 * Real.sqrt (1 - 1 / K ^ 2)))
      = Real.exp (c * s / (2 * Real.sqrt (1 - 1 / K ^ 2)) * Real.log c) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < c)]
    ring_nf
  have hstep : evenProlateSignedLeakage a m ≤ 2 * (Real.exp 1 * prolateLeakageUpper c s) := by
    linarith [hup, hshift]
  have hchain : evenProlateSignedLeakage a m
      ≤ 2 * (Real.exp 1 * (leakageUpperConst * c
          * Real.exp (-(2 * c * bandEndpointPhase s (2 * Real.sqrt s))))) := by
    refine le_trans hstep ?_
    have hexp1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have := mul_le_mul_of_nonneg_left hbase hexp1.le
    linarith
  refine le_trans hchain ?_
  rw [leakageLadderUpperConst, hpowval]
  have hexp1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hkey := mul_le_mul_of_nonneg_left hphase hUnn
  nlinarith [hkey, hexp1, hUnn]

/-- The constant of the lower power bound. -/
def leakageLadderLowerConst (n : ℕ) : ℝ := 2 * leakageLowerConst * (4 * (n : ℝ))

theorem leakageLadderLowerConst_pos {n : ℕ} (hn : 1 ≤ n) : 0 < leakageLadderLowerConst n := by
  have h := leakageLowerConst_pos
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [leakageLadderLowerConst]
  positivity

/-- **Every excited leakage is at least a power of the bandwidth times `e^{-2c}`.** -/
theorem eventually_signedLeakage_ge_pow (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ a : ℝ in atTop,
      leakageLadderLowerConst n * signedModeRadialBandwidth a ^ (-2 : ℝ)
          * Real.exp (-(2 * signedModeRadialBandwidth a))
          * Real.exp (-(10 * (signedModeRadialBandwidth a * (signedModeRadialData a n).s))
              - (signedModeRadialBandwidth a * (signedModeRadialData a n).s) / 2
                * Real.log (signedModeRadialBandwidth a * (signedModeRadialData a n).s))
          * signedModeRadialBandwidth a
            ^ (signedModeRadialBandwidth a * (signedModeRadialData a n).s / 2)
        ≤ evenProlateSignedLeakage a n := by
  have hlimit := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hlo : ∀ᶠ a : ℝ in atTop,
      4 * (n : ℝ) < signedModeRadialBandwidth a * (signedModeRadialData a n).s :=
    hlimit.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [eventually_signedLeakage_two_sided n hn,
    eventually_signedModeRadialData_s_pos n,
    eventually_signedModeRadialData_s_le n (show (0 : ℝ) < 1 / 64 by norm_num), hlo,
    tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (8 : ℝ)]
    with a htwo hs0 hs64 hcs hc8
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  set s : ℝ := (signedModeRadialData a n).s with hsdef
  have hc0 : (0 : ℝ) < c := by linarith
  have hlow := prolateLeakageLower_ge (c := c) (s := s) hc8 hs0 hs64
  have hact := exp_lower_action_eq (c := c) (s := s) hc0 hs0
  have hpow2 : c ^ (-2 : ℝ) = 1 / c ^ 2 := by
    rw [Real.rpow_neg hc0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
  have hpowval : c ^ (c * s / 2) = Real.exp (c * s / 2 * Real.log c) := by
    rw [Real.rpow_def_of_pos hc0]
    ring_nf
  -- the separation quotient dominates the inverse square of the bandwidth
  have hsc : 4 * (n : ℝ) * (1 / c ^ 2) ≤ s / c := by
    have hgoal : s / c - 4 * (n : ℝ) * (1 / c ^ 2) = (c * s - 4 * (n : ℝ)) / c ^ 2 := by
      field_simp
    have hnn : (0 : ℝ) ≤ (c * s - 4 * (n : ℝ)) / c ^ 2 :=
      div_nonneg (by linarith) (by positivity)
    linarith [hgoal, hnn]
  set E : ℝ := Real.exp (-(2 * c))
      * Real.exp (-(10 * (c * s)) - c * s / 2 * Real.log (c * s))
      * Real.exp (c * s / 2 * Real.log c) with hE
  have hEpos : 0 < E := by rw [hE]; positivity
  have hLpos : (0 : ℝ) < leakageLowerConst := leakageLowerConst_pos
  have hcoef : leakageLadderLowerConst n * c ^ (-2 : ℝ) ≤ 2 * (leakageLowerConst * (s / c)) := by
    rw [hpow2, leakageLadderLowerConst]
    calc 2 * leakageLowerConst * (4 * (n : ℝ)) * (1 / c ^ 2)
        = 2 * leakageLowerConst * (4 * (n : ℝ) * (1 / c ^ 2)) := by ring
      _ ≤ 2 * leakageLowerConst * (s / c) :=
          mul_le_mul_of_nonneg_left hsc (by positivity)
      _ = 2 * (leakageLowerConst * (s / c)) := by ring
  have hlhs : leakageLadderLowerConst n * c ^ (-2 : ℝ) * Real.exp (-(2 * c))
        * Real.exp (-(10 * (c * s)) - c * s / 2 * Real.log (c * s))
        * c ^ (c * s / 2)
      = leakageLadderLowerConst n * c ^ (-2 : ℝ) * E := by
    rw [hpowval, hE]; ring
  have hrhs : 2 * (leakageLowerConst * (s / c)) * E
      = 2 * (leakageLowerConst * (s / c)
          * Real.exp (-(2 * c * (1 + s / 4 * Real.log s) + 10 * (c * s)))) := by
    rw [hact, hE]; ring
  have hchain : leakageLadderLowerConst n * c ^ (-2 : ℝ) * Real.exp (-(2 * c))
        * Real.exp (-(10 * (c * s)) - c * s / 2 * Real.log (c * s))
        * c ^ (c * s / 2)
      ≤ 2 * (leakageLowerConst * (s / c)
          * Real.exp (-(2 * c * (1 + s / 4 * Real.log s) + 10 * (c * s)))) := by
    rw [hlhs, ← hrhs]
    exact mul_le_mul_of_nonneg_right hcoef hEpos.le
  have hhalf : prolateLeakageLower c s ≤ evenProlateSignedLeakage a n / 2 := htwo.1
  linarith [hchain, hlow, hhalf]

/-! ## The vanishing ratio -/

/-- **The leakage ratio vanishes with an affordable extra bandwidth power.**  The hypothesis is
exactly the exponent bookkeeping: the upper exponent of index `m`, inflated by the phase split,
plus `p + 3`, must stay below the lower exponent of index `n`. -/
theorem tendsto_signedLeakage_ratio_pow (m n : ℕ) (hn : 1 ≤ n) (p K : ℝ) (hK : 2 ≤ K)
    (hgap : p + 3 + (4 * (m : ℝ) + 1) / (2 * Real.sqrt (1 - 1 / K ^ 2))
        - (4 * (n : ℝ) + 1) / 2 < 0) :
    Tendsto (fun a : ℝ => signedModeRadialBandwidth a ^ p
      * (evenProlateSignedLeakage a m / evenProlateSignedLeakage a n)) atTop (𝓝 0) := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hrpos : (0 : ℝ) < 1 - 1 / K ^ 2 := by
    have h1 : (1 : ℝ) / K ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    linarith
  set rK : ℝ := Real.sqrt (1 - 1 / K ^ 2) with hrK
  have hrK0 : 0 < rK := Real.sqrt_pos.2 hrpos
  set μm : ℝ := 4 * (m : ℝ) + 1 with hμm
  set μn : ℝ := 4 * (n : ℝ) + 1 with hμn
  set CU : ℝ := leakageLadderUpperConst with hCU
  set CL : ℝ := leakageLadderLowerConst n with hCL
  have hCU0 : 0 ≤ CU := leakageLadderUpperConst_nonneg
  have hCL0 : 0 < CL := leakageLadderLowerConst_pos hn
  -- the two convergent factors and the exponent
  set Tm : ℝ → ℝ := fun a => signedModeRadialBandwidth a * (signedModeRadialData a m).s with hTm
  set Tn : ℝ → ℝ := fun a => signedModeRadialBandwidth a * (signedModeRadialData a n).s with hTn
  have hlimM : Tendsto Tm atTop (𝓝 μm) := tendsto_signedModeRadialBandwidth_mul_s_atTop m
  have hlimN : Tendsto Tn atTop (𝓝 μn) := tendsto_signedModeRadialBandwidth_mul_s_atTop n
  have hμm0 : 0 < μm := by rw [hμm]; positivity
  have hμn0 : 0 < μn := by rw [hμn]; positivity
  set P1 : ℝ → ℝ := fun a => Real.exp (phaseTail K (Tm a)) with hP1
  set P2 : ℝ → ℝ := fun a => Real.exp (-(10 * Tn a) - Tn a / 2 * Real.log (Tn a)) with hP2
  set N : ℝ → ℝ := fun a => CU / CL * (P1 a / P2 a) with hN
  set G : ℝ → ℝ := fun a => p + 3 + Tm a / (2 * rK) - Tn a / 2 with hG
  -- limits
  have hlogM : Tendsto (fun a => Real.log (Tm a)) atTop (𝓝 (Real.log μm)) :=
    (Real.continuousAt_log (ne_of_gt hμm0)).tendsto.comp hlimM
  have hlogN : Tendsto (fun a => Real.log (Tn a)) atTop (𝓝 (Real.log μn)) :=
    (Real.continuousAt_log (ne_of_gt hμn0)).tendsto.comp hlimN
  have htail : Tendsto (fun a => phaseTail K (Tm a)) atTop (𝓝 (phaseTail K μm)) := by
    simp only [phaseTail]
    exact (((hlimM.const_mul 8).add (hlimM.const_mul (2 * K ^ 2))).add
      ((hlimM.div_const _).mul tendsto_const_nhds)).sub ((hlimM.div_const _).mul hlogM)
  have hP1lim : Tendsto P1 atTop (𝓝 (Real.exp (phaseTail K μm))) :=
    (Real.continuous_exp.tendsto _).comp htail
  have hP2lim : Tendsto P2 atTop
      (𝓝 (Real.exp (-(10 * μn) - μn / 2 * Real.log μn))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    exact (hlimN.const_mul 10).neg.sub ((hlimN.div_const 2).mul hlogN)
  set N₀ : ℝ := CU / CL * (Real.exp (phaseTail K μm)
    / Real.exp (-(10 * μn) - μn / 2 * Real.log μn)) with hN₀
  have hNlim : Tendsto N atTop (𝓝 N₀) :=
    tendsto_const_nhds.mul (hP1lim.div hP2lim (ne_of_gt (Real.exp_pos _)))
  set G₀ : ℝ := p + 3 + μm / (2 * rK) - μn / 2 with hG₀
  have hG₀neg : G₀ < 0 := hgap
  have hGlim : Tendsto G atTop (𝓝 G₀) :=
    ((tendsto_const_nhds.add (hlimM.div_const (2 * rK))).sub (hlimN.div_const 2))
  have hN₀nn : 0 ≤ N₀ := by
    rw [hN₀]
    have : (0 : ℝ) ≤ CU / CL := div_nonneg hCU0 hCL0.le
    positivity
  -- the majorant
  have hmaj : Tendsto (fun a : ℝ => (N₀ + 1) * signedModeRadialBandwidth a ^ (G₀ / 2))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < -(G₀ / 2) by linarith)).comp
      tendsto_signedModeRadialBandwidth_atTop
    have h2 : Tendsto (fun a : ℝ => signedModeRadialBandwidth a ^ (G₀ / 2)) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_neg] using h
    simpa using h2.const_mul (N₀ + 1)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ)]
      with a hc1
    have hcnn : (0 : ℝ) ≤ signedModeRadialBandwidth a := by linarith
    have h1 : (0 : ℝ) ≤ signedModeRadialBandwidth a ^ p := Real.rpow_nonneg hcnn p
    have h2 : (0 : ℝ) ≤ evenProlateSignedLeakage a m / evenProlateSignedLeakage a n :=
      div_nonneg (evenProlateSignedLeakage_nonneg a m) (evenProlateSignedLeakage_nonneg a n)
    positivity
  · filter_upwards [eventually_signedLeakage_le_pow m hK, eventually_signedLeakage_ge_pow n hn,
      tendsto_signedModeRadialBandwidth_atTop.eventually_ge_atTop (1 : ℝ),
      (hNlim.eventually (eventually_lt_nhds (show N₀ < N₀ + 1 by linarith))).mono
        fun _ h => h.le,
      (hGlim.eventually (eventually_lt_nhds (show G₀ < G₀ / 2 by linarith))).mono
        fun _ h => h.le]
      with a hupA hloA hc1 hNle hGle
    set c : ℝ := signedModeRadialBandwidth a with hcdef
    have hc0 : (0 : ℝ) < c := by linarith
    set E2 : ℝ := Real.exp (-(2 * c)) with hE2
    have hE20 : 0 < E2 := Real.exp_pos _
    set g1 : ℝ := Tm a / (2 * rK) with hg1
    set g2 : ℝ := Tn a / 2 with hg2
    set U : ℝ := CU * c * E2 * P1 a * c ^ g1 with hU
    set L : ℝ := CL * c ^ (-2 : ℝ) * E2 * P2 a * c ^ g2 with hL
    have hP10 : 0 < P1 a := Real.exp_pos _
    have hP20 : 0 < P2 a := Real.exp_pos _
    have hLpos : 0 < L := by
      rw [hL]
      have h1 : (0 : ℝ) < c ^ (-2 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have h2 : (0 : ℝ) < c ^ g2 := Real.rpow_pos_of_pos hc0 _
      positivity
    have hUnn : 0 ≤ U := by
      rw [hU]
      have h2 : (0 : ℝ) < c ^ g1 := Real.rpow_pos_of_pos hc0 _
      positivity
    have hnumle : evenProlateSignedLeakage a m ≤ U := hupA
    have hdenge : L ≤ evenProlateSignedLeakage a n := hloA
    have hden0 : 0 < evenProlateSignedLeakage a n := lt_of_lt_of_le hLpos hdenge
    have hratio : evenProlateSignedLeakage a m / evenProlateSignedLeakage a n ≤ U / L :=
      div_le_div₀ hUnn hnumle hLpos hdenge
    have hcp : (0 : ℝ) ≤ c ^ p := (Real.rpow_pos_of_pos hc0 p).le
    have hstep : c ^ p * (evenProlateSignedLeakage a m / evenProlateSignedLeakage a n)
        ≤ c ^ p * (U / L) := mul_le_mul_of_nonneg_left hratio hcp
    -- the identity turning the quotient into a single power
    have hCLne : CL ≠ 0 := ne_of_gt hCL0
    have hP2ne : P2 a ≠ 0 := ne_of_gt hP20
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hpowsum : c ^ (p + 3 + g1 - g2) * c ^ (-2 : ℝ) * c ^ g2 = c ^ p * c * c ^ g1 := by
      have h1 : c ^ (p + 3 + g1 - g2) * c ^ (-2 : ℝ) * c ^ g2 = c ^ (p + 1 + g1) := by
        rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]
        congr 1
        ring
      have h2 : c ^ p * c * c ^ g1 = c ^ (p + 1 + g1) := by
        rw [← Real.rpow_add_one (ne_of_gt hc0) p, ← Real.rpow_add hc0]
      rw [h1, h2]
    have hGa : G a = p + 3 + g1 - g2 := rfl
    have hNa : N a = CU / CL * (P1 a / P2 a) := rfl
    have hid : N a * c ^ G a * L = c ^ p * U := by
      rw [hNa, hGa, hU, hL]
      have hEq : CU / CL * (P1 a / P2 a) * c ^ (p + 3 + g1 - g2)
            * (CL * c ^ (-2 : ℝ) * E2 * P2 a * c ^ g2)
          = CU * P1 a * E2 * (c ^ (p + 3 + g1 - g2) * c ^ (-2 : ℝ) * c ^ g2) := by
        field_simp
      have hEq2 : c ^ p * (CU * c * E2 * P1 a * c ^ g1)
          = CU * P1 a * E2 * (c ^ p * c * c ^ g1) := by ring
      rw [hEq, hEq2, hpowsum]
    have hquot : c ^ p * (U / L) = N a * c ^ G a := by
      rw [← mul_div_assoc, ← hid, mul_div_assoc, div_self hLne, mul_one]
    rw [hquot] at hstep
    refine le_trans hstep ?_
    have hNnn : 0 ≤ N a := by
      rw [hN]
      have : (0 : ℝ) ≤ CU / CL := div_nonneg hCU0 hCL0.le
      positivity
    have hpowle : c ^ G a ≤ c ^ (G₀ / 2) := Real.rpow_le_rpow_of_exponent_le hc1 hGle
    have hpownn : (0 : ℝ) ≤ c ^ (G₀ / 2) := (Real.rpow_pos_of_pos hc0 _).le
    calc N a * c ^ G a ≤ N a * c ^ (G₀ / 2) := mul_le_mul_of_nonneg_left hpowle hNnn
      _ ≤ (N₀ + 1) * c ^ (G₀ / 2) := mul_le_mul_of_nonneg_right hNle hpownn

end RHTower

end
