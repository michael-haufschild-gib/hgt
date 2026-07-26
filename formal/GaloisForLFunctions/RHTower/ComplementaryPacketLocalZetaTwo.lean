import GaloisForLFunctions.RHTower.ComplementaryPacketKernelIntegrability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# Local expansion of the boundary packet modulus

At infinitesimal separation the two-point modulus of the boundary complementary packet is governed
by the jump structure of its kernel rather than by its cofinal slope.  The kernel

```text
k_ω(t) = e^(-(1+ω)t) ∑_{m ≤ e^t} m^ω − 1/(1+ω)
```

is smooth off the discrete set `{log m : m ≥ 2}` and jumps by `1/m` at `log m`; the swept branch of
the modulus carries the remaining unit jump at the origin.  Each jump of size `j` contributes
`j² a + O(a²)` to the modulus at separation `a`, so

```text
lim_{a → 0+} D_ω(a) / a = ∑_{m ≥ 1} 1/m² = π²/6 .
```

Since `π²/6 > 1`, the packet is **locally expansive**: no pointwise contraction `D_ω(a) ≤ a` holds
near zero.  The successful metric law is the cofinal one of `ComplementaryPacketCofinalIsometry`,
not this local one.

The proof is an explicit two-region estimate.  On `(0, log N)` the translation window meets at most
one jump once `a ≤ 1/(2(N+1))`, which linearises the square of the increment; beyond `log N` the
increment is controlled by the counting function `⌊e^(r+a)⌋ − ⌊e^r⌋`, whose exponentially weighted
integral is `O(a/N)`.
-/

open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ### The step profile and the increment identity -/

/-- The step profile of the boundary packet: the power sum truncated at `e^t`. -/
def packetStepSum (ω t : ℝ) : ℝ := ∑ i ∈ Finset.range (⌊Real.exp t⌋₊ + 1), (i : ℝ) ^ ω

theorem complementaryPacketKernel_add_const (ω : ℝ) (hω : 0 ≤ ω) (t : ℝ) :
    complementaryPacketKernel ω t + complementaryPacketConstant ω
      = Real.exp (-(1 + ω) * t) * packetStepSum ω t := by
  rw [complementaryPacketKernel_eq ω hω t, complementaryPacketConstant, packetStepSum]
  ring

theorem packetStepSum_sub (ω : ℝ) {t s : ℝ} (hts : t ≤ s) :
    packetStepSum ω s - packetStepSum ω t
      = ∑ i ∈ Finset.Ico (⌊Real.exp t⌋₊ + 1) (⌊Real.exp s⌋₊ + 1), (i : ℝ) ^ ω := by
  have hle : ⌊Real.exp t⌋₊ + 1 ≤ ⌊Real.exp s⌋₊ + 1 :=
    Nat.succ_le_succ (Nat.floor_mono (Real.exp_le_exp.mpr hts))
  rw [Finset.sum_Ico_eq_sub _ hle]
  rfl

/-- The jump mass swept by a translation of size `a` at clock time `r`. -/
def packetJump (ω a r : ℝ) : ℝ :=
  Real.exp (-(1 + ω) * (r + a)) *
    ∑ i ∈ Finset.Ico (⌊Real.exp r⌋₊ + 1) (⌊Real.exp (r + a)⌋₊ + 1), (i : ℝ) ^ ω

/-- **Increment identity.**  The packet increment splits into the jump mass swept by the
translation and an exponential drift of the incoming profile. -/
theorem complementaryPacketKernel_sub_eq (ω : ℝ) (hω : 0 ≤ ω) (r : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r
      = packetJump ω a r
        + (Real.exp (-(1 + ω) * a) - 1) *
            (complementaryPacketKernel ω r + complementaryPacketConstant ω) := by
  have hE : Real.exp (-(1 + ω) * (r + a))
      = Real.exp (-(1 + ω) * a) * Real.exp (-(1 + ω) * r) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 := complementaryPacketKernel_add_const ω hω (r + a)
  have h2 := complementaryPacketKernel_add_const ω hω r
  have hgoal : complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r
      = (complementaryPacketKernel ω (r + a) + complementaryPacketConstant ω)
        - (complementaryPacketKernel ω r + complementaryPacketConstant ω) := by ring
  rw [packetJump, hgoal, ← packetStepSum_sub ω (show r ≤ r + a by linarith), h1, h2, hE]
  ring

/-! ### Pointwise bounds -/

private theorem rpow_two_le_two {ω : ℝ} (hω : ω ≤ 1) : (2 : ℝ) ^ ω ≤ 2 := by
  calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hω
    _ = 2 := Real.rpow_one 2

private theorem abs_sub_le_abs_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  calc |x - y| = |x + -y| := by ring_nf
    _ ≤ |x| + |-y| := abs_add_le _ _
    _ = |x| + |y| := by rw [abs_neg]

theorem abs_packetIncomingProfile_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {r : ℝ}
    (hr : 0 ≤ r) :
    |complementaryPacketKernel ω r + complementaryPacketConstant ω| ≤ 3 := by
  have henv := abs_complementaryPacketKernel_le ω hω0 hr
  have h2ω : (2 : ℝ) ^ ω ≤ 2 := rpow_two_le_two (by linarith)
  have h2ω0 : (0 : ℝ) ≤ (2 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
  have hexp0 : (0 : ℝ) < Real.exp (-r) := Real.exp_pos _
  have hexp : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hk : |complementaryPacketKernel ω r| ≤ 2 := by
    refine henv.trans ?_
    nlinarith
  have hc : |complementaryPacketConstant ω| ≤ 1 := by
    rw [complementaryPacketConstant, abs_of_nonneg (by positivity)]
    rw [div_le_one (by linarith)]
    linarith
  calc |complementaryPacketKernel ω r + complementaryPacketConstant ω|
      ≤ |complementaryPacketKernel ω r| + |complementaryPacketConstant ω| := abs_add_le _ _
    _ ≤ 3 := by linarith

/-- Uniform bound on the drift term of the increment identity. -/
theorem abs_packetDrift_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) :
    |(Real.exp (-(1 + ω) * a) - 1) *
        (complementaryPacketKernel ω r + complementaryPacketConstant ω)| ≤ 5 * a := by
  have hprof := abs_packetIncomingProfile_le hω0 hω hr
  have hnn : (0 : ℝ) ≤ (1 + ω) * a := by positivity
  have h1 : |Real.exp (-(1 + ω) * a) - 1| ≤ (1 + ω) * a := by
    have hle : Real.exp (-(1 + ω) * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hge : 1 - (1 + ω) * a ≤ Real.exp (-(1 + ω) * a) := by
      have h := Real.add_one_le_exp (-(1 + ω) * a)
      linarith
    rw [abs_le]
    constructor <;> linarith
  have habs0 : (0 : ℝ) ≤ |Real.exp (-(1 + ω) * a) - 1| := abs_nonneg _
  rw [abs_mul]
  nlinarith

theorem packetJump_nonneg (ω : ℝ) (_hω : 0 ≤ ω) (a r : ℝ) : 0 ≤ packetJump ω a r :=
  mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) ω)

/-- The swept jump mass is at most the number of integers crossed, discounted exponentially. -/
theorem packetJump_le (ω : ℝ) (hω : 0 ≤ ω) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    packetJump ω a r
      ≤ ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) := by
  have hfl : ⌊Real.exp r⌋₊ ≤ ⌊Real.exp (r + a)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hbound : ∀ i ∈ Finset.Ico (⌊Real.exp r⌋₊ + 1) (⌊Real.exp (r + a)⌋₊ + 1),
      (i : ℝ) ^ ω ≤ Real.exp ((r + a) * ω) := by
    intro i hi
    have hi2 : i ≤ ⌊Real.exp (r + a)⌋₊ := by
      have h := (Finset.mem_Ico.mp hi).2
      omega
    have hile : (i : ℝ) ≤ Real.exp (r + a) :=
      le_trans (Nat.cast_le.mpr hi2) (Nat.floor_le (Real.exp_pos _).le)
    calc (i : ℝ) ^ ω ≤ (Real.exp (r + a)) ^ ω :=
          Real.rpow_le_rpow (Nat.cast_nonneg i) hile hω
      _ = Real.exp ((r + a) * ω) := (Real.exp_mul (r + a) ω).symm
  have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
  rw [Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((⌊Real.exp (r + a)⌋₊ + 1 - (⌊Real.exp r⌋₊ + 1) : ℕ) : ℝ)
      = (⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ) := by
    rw [show ⌊Real.exp (r + a)⌋₊ + 1 - (⌊Real.exp r⌋₊ + 1) = ⌊Real.exp (r + a)⌋₊ - ⌊Real.exp r⌋₊ by
      omega]
    exact Nat.cast_sub hfl
  rw [hcard] at hsum
  have hexpnn : (0 : ℝ) < Real.exp (-(1 + ω) * (r + a)) := Real.exp_pos _
  have hstep : packetJump ω a r
      ≤ Real.exp (-(1 + ω) * (r + a)) *
          (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp ((r + a) * ω)) :=
    mul_le_mul_of_nonneg_left hsum hexpnn.le
  have hcollapse : Real.exp (-(1 + ω) * (r + a)) * Real.exp ((r + a) * ω)
      = Real.exp (-(r + a)) := by
    rw [← Real.exp_add]
    ring_nf
  have hmono : Real.exp (-(r + a)) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)
  have hdiffnn : (0 : ℝ) ≤ (⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ) := by
    have := Nat.cast_le (α := ℝ).mpr hfl
    linarith
  calc packetJump ω a r
      ≤ Real.exp (-(1 + ω) * (r + a)) *
          (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp ((r + a) * ω)) := hstep
    _ = ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-(r + a)) := by
        rw [← hcollapse]; ring
    _ ≤ ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_left hmono hdiffnn

/-- Envelope of the packet increment. -/
theorem abs_complementaryPacketKernel_sub_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2)
    {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r| ≤ 4 * Real.exp (-r) := by
  have h1 := abs_complementaryPacketKernel_le ω hω0 (show (0 : ℝ) ≤ r + a by linarith)
  have h2 := abs_complementaryPacketKernel_le ω hω0 hr
  have h2ω : (2 : ℝ) ^ ω ≤ 2 := rpow_two_le_two (by linarith)
  have h2ω0 : (0 : ℝ) ≤ (2 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
  have hmono : Real.exp (-(r + a)) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)
  have hexp0 : (0 : ℝ) < Real.exp (-(r + a)) := Real.exp_pos _
  have hexp1 : (0 : ℝ) < Real.exp (-r) := Real.exp_pos _
  calc |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r|
      ≤ |complementaryPacketKernel ω (r + a)| + |complementaryPacketKernel ω r| :=
        abs_sub_le_abs_add_abs _ _
    _ ≤ 2 ^ ω * Real.exp (-(r + a)) + 2 ^ ω * Real.exp (-r) := by linarith
    _ ≤ 4 * Real.exp (-r) := by nlinarith

/-! ### Integrability of the increment square -/

private theorem integrableOn_exp_neg_Ioi (c : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi c) := by
  have h := exp_neg_integrableOn_Ioi c (b := 1) one_pos
  simpa using h

theorem measurable_complementaryPacketKernel_sub (ω : ℝ) (hω : 0 ≤ ω) (a : ℝ) :
    Measurable fun r : ℝ =>
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
  have hk := measurable_complementaryPacketKernel ω hω
  exact ((hk.comp (measurable_id.add_const a)).sub hk).pow_const 2

theorem integrableOn_complementaryPacketKernel_sub_sq {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2)
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul 16)
    (measurable_complementaryPacketKernel_sub ω hω0 a).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have henv := abs_complementaryPacketKernel_sub_le hω0 hω hr0 ha
  have habs : (0 : ℝ) ≤ |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r| :=
    abs_nonneg _
  have hexp1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp0 : (0 : ℝ) < Real.exp (-r) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
      ≤ (4 * Real.exp (-r)) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ habs henv 2
  nlinarith

/-! ### The tail beyond the first `N` jumps -/

/-- The exponentially weighted integer count `⌊e^u⌋ e^(-2u)`. -/
private def floorExpWeight (u : ℝ) : ℝ := (⌊Real.exp u⌋₊ : ℝ) * Real.exp (-2 * u)

private theorem measurable_floorExpWeight : Measurable floorExpWeight := by
  have hfloor : Measurable fun u : ℝ => ⌊Real.exp u⌋₊ :=
    Nat.measurable_floor.comp Real.measurable_exp
  have hcast : Measurable fun u : ℝ => ((⌊Real.exp u⌋₊ : ℕ) : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hfloor
  exact hcast.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))

private theorem floorExpWeight_nonneg (u : ℝ) : 0 ≤ floorExpWeight u :=
  mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

private theorem floorExpWeight_le (u : ℝ) : floorExpWeight u ≤ Real.exp (-u) := by
  have hfl : (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hpos : (0 : ℝ) < Real.exp (-2 * u) := Real.exp_pos _
  have hcollapse : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
    rw [← Real.exp_add]
    ring_nf
  calc floorExpWeight u ≤ Real.exp u * Real.exp (-2 * u) :=
        mul_le_mul_of_nonneg_right hfl hpos.le
    _ = Real.exp (-u) := hcollapse

private theorem integrableOn_floorExpWeight (c : ℝ) : IntegrableOn floorExpWeight (Ioi c) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi c)
    measurable_floorExpWeight.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (floorExpWeight_nonneg u)]
  exact floorExpWeight_le u

private theorem setIntegral_floorExpWeight_le (c : ℝ) :
    (∫ u in Ioi c, floorExpWeight u) ≤ Real.exp (-c) := by
  have h : (∫ u in Ioi c, floorExpWeight u) ≤ ∫ u in Ioi c, Real.exp (-u) :=
    setIntegral_mono_on (integrableOn_floorExpWeight c) (integrableOn_exp_neg_Ioi c)
      measurableSet_Ioi fun u _ => floorExpWeight_le u
  rwa [integral_exp_neg_Ioi c] at h

private theorem setIntegral_floorExpWeight_nonneg (c : ℝ) :
    0 ≤ ∫ u in Ioi c, floorExpWeight u :=
  setIntegral_nonneg measurableSet_Ioi fun u _ => floorExpWeight_nonneg u

private theorem exp_two_mul_sub_one_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    Real.exp (2 * a) - 1 ≤ 6 * a := by
  have hle3 : Real.exp (2 * a) ≤ 3 := by
    have h1 : Real.exp (2 * a) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.exp_one_lt_d9
    linarith
  have hlin : Real.exp (2 * a) - 2 * a * Real.exp (2 * a) ≤ 1 := by
    have h := Real.add_one_le_exp (-(2 * a))
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (2 * a)).le
    have hcancel : Real.exp (-(2 * a)) * Real.exp (2 * a) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith
  nlinarith

/-- The exponentially weighted integer count crossed by a translation of size `a` beyond `L`. -/
private theorem setIntegral_floorCount_le {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (L : ℝ) :
    (∫ r in Ioi L, ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
      ≤ 6 * a * Real.exp (-L) := by
  have hAmeas : Measurable fun r : ℝ => (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r) := by
    have hfloor : Measurable fun r : ℝ => ⌊Real.exp (r + a)⌋₊ :=
      Nat.measurable_floor.comp (Real.measurable_exp.comp (measurable_id.add_const a))
    have hcast : Measurable fun r : ℝ => ((⌊Real.exp (r + a)⌋₊ : ℕ) : ℝ) :=
      (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hfloor
    exact hcast.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hAeq : ∀ r : ℝ, (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r)
      = Real.exp (2 * a) * floorExpWeight (r + a) := by
    intro r
    rw [floorExpWeight]
    have hcollapse : Real.exp (2 * a) * Real.exp (-2 * (r + a)) = Real.exp (-2 * r) := by
      rw [← Real.exp_add]
      ring_nf
    rw [← hcollapse]
    ring
  have hAint : IntegrableOn (fun r : ℝ => (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r))
      (Ioi L) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi L).const_mul (Real.exp a))
      hAmeas.aestronglyMeasurable ?_
    filter_upwards with r
    have hnn : (0 : ℝ) ≤ (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hAeq r]
    have h := floorExpWeight_le (r + a)
    have hcollapse : Real.exp (2 * a) * Real.exp (-(r + a)) = Real.exp a * Real.exp (-r) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    calc Real.exp (2 * a) * floorExpWeight (r + a)
        ≤ Real.exp (2 * a) * Real.exp (-(r + a)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = Real.exp a * Real.exp (-r) := hcollapse
  have hBint : IntegrableOn floorExpWeight (Ioi L) := integrableOn_floorExpWeight L
  have hsplit : (∫ r in Ioi L, ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
      = (∫ r in Ioi L, (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r))
        - ∫ r in Ioi L, floorExpWeight r := by
    rw [← integral_sub hAint hBint]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [floorExpWeight]
    ring
  have htrans : (∫ r in Ioi L, (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r))
      = Real.exp (2 * a) * ∫ u in Ioi (L + a), floorExpWeight u := by
    calc (∫ r in Ioi L, (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r))
        = ∫ r in Ioi L, Real.exp (2 * a) * floorExpWeight (r + a) :=
          setIntegral_congr_fun measurableSet_Ioi fun r _ => hAeq r
      _ = Real.exp (2 * a) * ∫ r in Ioi L, floorExpWeight (r + a) := integral_const_mul _ _
      _ = Real.exp (2 * a) * ∫ u in Ioi (L + a), floorExpWeight u := by
          rw [setIntegral_Ioi_comp_add_right' floorExpWeight L a]
  have hmono : (∫ u in Ioi (L + a), floorExpWeight u) ≤ ∫ u in Ioi L, floorExpWeight u := by
    refine setIntegral_mono_set hBint ?_ ?_
    · filter_upwards with u using floorExpWeight_nonneg u
    · exact Filter.Eventually.of_forall (Ioi_subset_Ioi (by linarith))
  have hIle := setIntegral_floorExpWeight_le L
  have hI0 := setIntegral_floorExpWeight_nonneg L
  have hexp := exp_two_mul_sub_one_le ha ha2
  have hexppos : (0 : ℝ) < Real.exp (2 * a) := Real.exp_pos _
  rw [hsplit, htrans]
  nlinarith [setIntegral_floorExpWeight_nonneg (L + a)]

/-- **Tail bound.**  Beyond the first `N` jumps the translation modulus of the packet kernel is
`O(a/N)`, uniformly in the shift. -/
theorem setIntegral_complementaryPacketKernel_sub_sq_tail {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    (∫ r in Ioi (Real.log N),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      ≤ 50 * a / N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hexpL : Real.exp (-Real.log N) = 1 / (N : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hNpos, one_div]
  -- pointwise bound
  have hpt : ∀ r ∈ Ioi (Real.log N),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
        ≤ 4 * (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
          + 20 * a * Real.exp (-r) := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_trans hL0 (le_of_lt hr)
    have henv := abs_complementaryPacketKernel_sub_le hω0 hω hr0 ha
    have hid := complementaryPacketKernel_sub_eq ω hω0 r ha
    have hjump := packetJump_le ω hω0 ha r
    have hjump0 := packetJump_nonneg ω hω0 a r
    have hdrift := abs_packetDrift_le hω0 hω hr0 ha
    have habs : |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r|
        ≤ ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) + 5 * a := by
      rw [hid]
      calc |packetJump ω a r
              + (Real.exp (-(1 + ω) * a) - 1) *
                (complementaryPacketKernel ω r + complementaryPacketConstant ω)|
          ≤ |packetJump ω a r|
            + |(Real.exp (-(1 + ω) * a) - 1) *
                (complementaryPacketKernel ω r + complementaryPacketConstant ω)| := abs_add_le _ _
        _ ≤ ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) + 5 * a := by
            rw [abs_of_nonneg hjump0]
            linarith
    have hcollapse : Real.exp (-r) * Real.exp (-r) = Real.exp (-2 * r) := by
      rw [← Real.exp_add]
      ring_nf
    have hexp0 : (0 : ℝ) < Real.exp (-r) := Real.exp_pos _
    have hcount0 : (0 : ℝ) ≤ ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) := by
      have hfl : ⌊Real.exp r⌋₊ ≤ ⌊Real.exp (r + a)⌋₊ :=
        Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
      have : ((⌊Real.exp r⌋₊ : ℕ) : ℝ) ≤ ((⌊Real.exp (r + a)⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr hfl
      have hnn : (0 : ℝ) ≤ (⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ) := by linarith
      positivity
    have hsq : (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
        ≤ (4 * Real.exp (-r)) *
            (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) + 5 * a) := by
      have hsqabs : (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
          = |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r|
            * |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r| := by
        rw [← sq_abs, pow_two]
      rw [hsqabs]
      exact mul_le_mul henv habs (abs_nonneg _) (by positivity)
    calc (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
        ≤ (4 * Real.exp (-r)) *
            (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-r) + 5 * a) := hsq
      _ = 4 * (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ))
            * (Real.exp (-r) * Real.exp (-r))) + 20 * a * Real.exp (-r) := by ring
      _ = 4 * (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
            + 20 * a * Real.exp (-r) := by rw [hcollapse]
  -- integrability of the two sides
  have hlhs : IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ioi (Real.log N)) :=
    ((integrableOn_complementaryPacketKernel_sub_sq hω0 hω ha).mono_set
      (fun r hr => le_trans hL0 (le_of_lt hr)))
  have hcountint : IntegrableOn
      (fun r : ℝ => ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
      (Ioi (Real.log N)) := by
    have hAmeas : Measurable fun r : ℝ => (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r) := by
      have hfloor : Measurable fun r : ℝ => ⌊Real.exp (r + a)⌋₊ :=
        Nat.measurable_floor.comp (Real.measurable_exp.comp (measurable_id.add_const a))
      have hcast : Measurable fun r : ℝ => ((⌊Real.exp (r + a)⌋₊ : ℕ) : ℝ) :=
        (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp hfloor
      exact hcast.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))
    have hAint : IntegrableOn (fun r : ℝ => (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r))
        (Ioi (Real.log N)) := by
      refine Integrable.mono' ((integrableOn_exp_neg_Ioi (Real.log N)).const_mul (Real.exp a))
        hAmeas.aestronglyMeasurable ?_
      filter_upwards with r
      have hnn : (0 : ℝ) ≤ (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
      have hfl : (⌊Real.exp (r + a)⌋₊ : ℝ) ≤ Real.exp (r + a) :=
        Nat.floor_le (Real.exp_pos _).le
      have hcollapse : Real.exp (r + a) * Real.exp (-2 * r) = Real.exp a * Real.exp (-r) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r)
          ≤ Real.exp (r + a) * Real.exp (-2 * r) :=
            mul_le_mul_of_nonneg_right hfl (Real.exp_pos _).le
        _ = Real.exp a * Real.exp (-r) := hcollapse
    have hBint : IntegrableOn floorExpWeight (Ioi (Real.log N)) :=
      integrableOn_floorExpWeight _
    have := hAint.sub hBint
    refine this.congr_fun ?_ measurableSet_Ioi
    intro r _
    show (⌊Real.exp (r + a)⌋₊ : ℝ) * Real.exp (-2 * r) - floorExpWeight r
        = ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r)
    rw [floorExpWeight]
    ring
  have hrhs : IntegrableOn
      (fun r : ℝ => 4 * (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
        + 20 * a * Real.exp (-r)) (Ioi (Real.log N)) :=
    (hcountint.const_mul 4).add ((integrableOn_exp_neg_Ioi (Real.log N)).const_mul (20 * a))
  have hmono := setIntegral_mono_on hlhs hrhs measurableSet_Ioi hpt
  have hval : (∫ r in Ioi (Real.log N),
        (4 * (((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
          + 20 * a * Real.exp (-r)))
      = 4 * (∫ r in Ioi (Real.log N),
          ((⌊Real.exp (r + a)⌋₊ : ℝ) - (⌊Real.exp r⌋₊ : ℝ)) * Real.exp (-2 * r))
        + 20 * a * Real.exp (-Real.log N) := by
    rw [integral_add (hcountint.const_mul 4)
      ((integrableOn_exp_neg_Ioi (Real.log N)).const_mul (20 * a)), integral_const_mul,
      integral_const_mul, integral_exp_neg_Ioi]
  have hcount := setIntegral_floorCount_le ha ha2 (Real.log N)
  rw [hval, hexpL] at hmono
  rw [hexpL] at hcount
  have hNinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have : (∫ r in Ioi (Real.log N),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      ≤ 4 * (6 * a * (1 / (N : ℝ))) + 20 * a * (1 / (N : ℝ)) := by
    linarith
  calc (∫ r in Ioi (Real.log N),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      ≤ 4 * (6 * a * (1 / (N : ℝ))) + 20 * a * (1 / (N : ℝ)) := this
    _ ≤ 50 * a / (N : ℝ) := by
        have hrw : (50 : ℝ) * a / (N : ℝ) = 50 * a * (1 / (N : ℝ)) := by ring
        rw [hrw]
        nlinarith

/-! ### The main region: one jump per translation window -/

private theorem exp_le_one_add_three_mul {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp a ≤ 1 + 3 * a := by
  have h3 : Real.exp a ≤ 3 := by
    have h1 : Real.exp a ≤ Real.exp 1 := Real.exp_le_exp.mpr ha1
    have h2 := Real.exp_one_lt_d9
    norm_num at h2
    linarith
  have hlin : Real.exp a - a * Real.exp a ≤ 1 := by
    have h := Real.add_one_le_exp (-a)
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos a).le
    have hcancel : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith
  nlinarith

/-- On `[log m, log (m+1))` the exponential has floor `m`. -/
theorem floor_exp_eq {m : ℕ} (hm : 1 ≤ m) {r : ℝ}
    (h1 : Real.log (m : ℝ) ≤ r) (h2 : r < Real.log ((m : ℝ) + 1)) : ⌊Real.exp r⌋₊ = m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlow : (m : ℝ) ≤ Real.exp r := by
    have h := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hmpos] at h
  have hhigh : Real.exp r < (m : ℝ) + 1 := by
    have h := Real.exp_lt_exp.mpr h2
    rwa [Real.exp_log (by linarith)] at h
  exact (Nat.floor_eq_iff (Real.exp_pos r).le).mpr ⟨hlow, hhigh⟩

/-- Under `a ≤ 1/(4(m+1))` a translation of size `a` never carries `log m` past `log (m+1)`. -/
private theorem log_add_le_log_succ {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a)
    (haM : a ≤ 1 / (4 * ((m : ℝ) + 1))) :
    Real.log (m : ℝ) + a ≤ Real.log ((m : ℝ) + 1) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmul : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
  have ha1 : a ≤ 1 := by
    have h8 : (8 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by linarith
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h8
    linarith
  have hea : Real.exp a ≤ 1 + 3 * a := exp_le_one_add_three_mul ha ha1
  have hkey : (m : ℝ) * Real.exp a ≤ (m : ℝ) + 1 := by
    have h3 : 3 * a * (m : ℝ) ≤ 1 := by
      have hle : a * (4 * ((m : ℝ) + 1)) ≤ 1 := by
        rw [← le_div_iff₀ hmul]
        exact haM
      nlinarith
    nlinarith
  have hexp : Real.exp (Real.log (m : ℝ) + a) ≤ Real.exp (Real.log ((m : ℝ) + 1)) := by
    rw [Real.exp_add, Real.exp_log hmpos, Real.exp_log (by linarith)]
    exact hkey
  exact Real.exp_le_exp.mp hexp

private theorem log_succ_add_le_log_succ_succ {m : ℕ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a)
    (haM : a ≤ 1 / (4 * ((m : ℝ) + 1))) :
    Real.log ((m : ℝ) + 1) + a ≤ Real.log ((m : ℝ) + 2) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmul : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
  have ha1 : a ≤ 1 := by
    have h8 : (8 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by linarith
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h8
    linarith
  have hea : Real.exp a ≤ 1 + 3 * a := exp_le_one_add_three_mul ha ha1
  have hle : a * (4 * ((m : ℝ) + 1)) ≤ 1 := by
    rw [← le_div_iff₀ hmul]
    exact haM
  have hkey : ((m : ℝ) + 1) * Real.exp a ≤ (m : ℝ) + 2 := by nlinarith
  have hexp : Real.exp (Real.log ((m : ℝ) + 1) + a) ≤ Real.exp (Real.log ((m : ℝ) + 2)) := by
    rw [Real.exp_add, Real.exp_log (by linarith), Real.exp_log (by linarith)]
    exact hkey
  exact Real.exp_le_exp.mp hexp

private theorem log_succ_sub_log_le_one {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hle : Real.log ((m : ℝ) + 1) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmul : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log (m : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith [hle, hmul.le, hmul.ge]

/-- **Window value.**  On the translation window at the jump `log (m+1)` the increment is within
`7a` of the jump size `1/(m+1)`. -/
private theorem abs_packetDiff_sub_jump_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {m : ℕ}
    (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) (haM : a ≤ 1 / (4 * ((m : ℝ) + 1))) {r : ℝ}
    (hr1 : Real.log ((m : ℝ) + 1) - a ≤ r) (hr2 : r < Real.log ((m : ℝ) + 1)) :
    |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r - 1 / ((m : ℝ) + 1)|
      ≤ 7 * a := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmul : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
  have ha8 : a ≤ 1 / 8 := by
    have h8 : (8 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by linarith
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h8
    linarith
  have hlog2 : Real.log 2 ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlog2' := Real.log_two_gt_d9
  have hr0 : (0 : ℝ) ≤ r := by
    norm_num at hlog2'
    linarith
  have hgap := log_add_le_log_succ hm ha.le haM
  have hfl1 : ⌊Real.exp r⌋₊ = m := floor_exp_eq hm (by linarith) hr2
  have hfl2 : ⌊Real.exp (r + a)⌋₊ = m + 1 := by
    have hup := log_succ_add_le_log_succ_succ hm ha.le haM
    have h1 : Real.log ((m + 1 : ℕ) : ℝ) ≤ r + a := by
      push_cast
      linarith
    have h2 : r + a < Real.log (((m + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      have : ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 := by ring
      rw [this]
      linarith
    exact floor_exp_eq (by omega) h1 h2
  have hIco : ∑ i ∈ Finset.Ico (m + 1) (m + 1 + 1), (i : ℝ) ^ ω = ((m + 1 : ℕ) : ℝ) ^ ω := by
    rw [Finset.sum_Ico_succ_top (le_refl (m + 1)), Finset.Ico_self, Finset.sum_empty, zero_add]
  have hxrpow : Real.exp (-(1 + ω) * Real.log ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ ω
      = ((m : ℝ) + 1)⁻¹ := by
    have h1 : Real.exp (-(1 + ω) * Real.log ((m : ℝ) + 1)) = ((m : ℝ) + 1) ^ (-(1 + ω)) := by
      rw [Real.rpow_def_of_pos hxpos]
      ring_nf
    rw [h1, ← Real.rpow_add hxpos, show -(1 + ω) + ω = (-1 : ℝ) by ring, Real.rpow_neg_one]
  have hjumpval : packetJump ω a r
      = ((m : ℝ) + 1)⁻¹ * Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) := by
    have hsplit : Real.exp (-(1 + ω) * (r + a))
        = Real.exp (-(1 + ω) * Real.log ((m : ℝ) + 1))
          * Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) := by
      rw [← Real.exp_add]
      ring_nf
    have hcast : ((m + 1 : ℕ) : ℝ) ^ ω = ((m : ℝ) + 1) ^ ω := by
      norm_num
    rw [packetJump, hfl1, hfl2, hIco, hcast]
    calc Real.exp (-(1 + ω) * (r + a)) * ((m : ℝ) + 1) ^ ω
        = (Real.exp (-(1 + ω) * Real.log ((m : ℝ) + 1)) * ((m : ℝ) + 1) ^ ω)
            * Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) := by
          rw [hsplit]; ring
      _ = ((m : ℝ) + 1)⁻¹ * Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) := by
          rw [hxrpow]
  have hu0 : (0 : ℝ) ≤ r + a - Real.log ((m : ℝ) + 1) := by linarith
  have hua : r + a - Real.log ((m : ℝ) + 1) < a := by linarith
  have hdecay : |Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) - 1| ≤ 2 * a := by
    have hle : Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hge : 1 - (1 + ω) * (r + a - Real.log ((m : ℝ) + 1))
        ≤ Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) := by
      have h := Real.add_one_le_exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1)))
      linarith
    rw [abs_le]
    constructor <;> nlinarith
  have hxinv : ((m : ℝ) + 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hxpos (by norm_num)]
    linarith
  have hxinv0 : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
  have hjumpdiff : |packetJump ω a r - 1 / ((m : ℝ) + 1)| ≤ 2 * a := by
    rw [hjumpval, one_div]
    have hfac : ((m : ℝ) + 1)⁻¹ * Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1)))
        - ((m : ℝ) + 1)⁻¹
        = ((m : ℝ) + 1)⁻¹
          * (Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) - 1) := by ring
    rw [hfac, abs_mul, abs_of_nonneg hxinv0.le]
    nlinarith [abs_nonneg (Real.exp (-(1 + ω) * (r + a - Real.log ((m : ℝ) + 1))) - 1)]
  have hid := complementaryPacketKernel_sub_eq ω hω0 r ha.le
  have hdrift := abs_packetDrift_le hω0 hω hr0 ha.le
  rw [hid]
  calc |packetJump ω a r
          + (Real.exp (-(1 + ω) * a) - 1) *
            (complementaryPacketKernel ω r + complementaryPacketConstant ω)
          - 1 / ((m : ℝ) + 1)|
      = |(packetJump ω a r - 1 / ((m : ℝ) + 1))
          + (Real.exp (-(1 + ω) * a) - 1) *
            (complementaryPacketKernel ω r + complementaryPacketConstant ω)| := by ring_nf
    _ ≤ |packetJump ω a r - 1 / ((m : ℝ) + 1)|
          + |(Real.exp (-(1 + ω) * a) - 1) *
            (complementaryPacketKernel ω r + complementaryPacketConstant ω)| := abs_add_le _ _
    _ ≤ 7 * a := by linarith

/-- Off the translation window the increment is pure drift. -/
private theorem abs_packetDiff_off_window_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {m : ℕ}
    (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) (_haM : a ≤ 1 / (4 * ((m : ℝ) + 1))) {r : ℝ}
    (hr1 : Real.log (m : ℝ) ≤ r) (hr2 : r < Real.log ((m : ℝ) + 1) - a) :
    |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r| ≤ 5 * a := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hr0 : (0 : ℝ) ≤ r := le_trans hlogm0 hr1
  have hfl1 : ⌊Real.exp r⌋₊ = m := floor_exp_eq hm hr1 (by linarith)
  have hfl2 : ⌊Real.exp (r + a)⌋₊ = m := floor_exp_eq hm (by linarith) (by linarith)
  have hjump0 : packetJump ω a r = 0 := by
    rw [packetJump, hfl1, hfl2, Finset.Ico_self, Finset.sum_empty, mul_zero]
  have hid := complementaryPacketKernel_sub_eq ω hω0 r ha.le
  have hdrift := abs_packetDrift_le hω0 hω hr0 ha.le
  rw [hid, hjump0, zero_add]
  exact hdrift

/-- **One jump per piece.**  The contribution of the clock interval `[log m, log (m+1))` to the
translation modulus is `a/(m+1)² + O(a²)`. -/
private theorem abs_setIntegral_piece_sub_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {m : ℕ}
    (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a) (haM : a ≤ 1 / (4 * ((m : ℝ) + 1))) :
    |(∫ r in Ico (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1)),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      - a * (1 / ((m : ℝ) + 1) ^ 2)| ≤ 50 * a ^ 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have hmul : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
  have ha8 : a ≤ 1 / 8 := by
    have h8 : (8 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by linarith
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h8
    linarith
  have hgap := log_add_le_log_succ hm ha.le haM
  set β : ℝ := Real.log ((m : ℝ) + 1) - a with hβ
  have hβ1 : Real.log (m : ℝ) ≤ β := by simp only [hβ]; linarith
  have hβ2 : β ≤ Real.log ((m : ℝ) + 1) := by simp only [hβ]; linarith
  have hglob := integrableOn_complementaryPacketKernel_sub_sq hω0 hω ha.le
  have hint1 : IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ico (Real.log (m : ℝ)) β) :=
    hglob.mono_set fun r hr => le_trans hlogm0 hr.1
  have hint2 : IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ico β (Real.log ((m : ℝ) + 1))) :=
    hglob.mono_set fun r hr => le_trans (le_trans hlogm0 hβ1) hr.1
  have hunion : (∫ r in Ico (Real.log (m : ℝ)) (Real.log ((m : ℝ) + 1)),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      = (∫ r in Ico (Real.log (m : ℝ)) β,
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
        + ∫ r in Ico β (Real.log ((m : ℝ) + 1)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
    rw [← setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico hint1 hint2,
      Ico_union_Ico_eq_Ico hβ1 hβ2]
  -- the drift piece
  have hvol1 : volume.real (Ico (Real.log (m : ℝ)) β) ≤ 1 := by
    rw [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    have := log_succ_sub_log_le_one hm
    simp only [hβ]
    linarith
  have hvol1nn : 0 ≤ volume.real (Ico (Real.log (m : ℝ)) β) := by positivity
  have hdrift : ‖(∫ r in Ico (Real.log (m : ℝ)) β,
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)‖
      ≤ 25 * a ^ 2 * volume.real (Ico (Real.log (m : ℝ)) β) := by
    refine norm_setIntegral_le_of_norm_le_const measure_Ico_lt_top fun r hr => ?_
    have hb := abs_packetDiff_off_window_le hω0 hω hm ha haM hr.1 (by simpa only [hβ] using hr.2)
    have habs0 : (0 : ℝ) ≤ |complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r| :=
      abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith
  have hdrift' : |(∫ r in Ico (Real.log (m : ℝ)) β,
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)| ≤ 25 * a ^ 2 := by
    rw [← Real.norm_eq_abs]
    refine hdrift.trans ?_
    nlinarith
  -- the window piece
  have hvol2 : volume.real (Ico β (Real.log ((m : ℝ) + 1))) = a := by
    rw [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by simp only [hβ]; linarith)]
    simp only [hβ]
    ring
  have hconst : IntegrableOn (fun _ : ℝ => 1 / ((m : ℝ) + 1) ^ 2)
      (Ico β (Real.log ((m : ℝ) + 1))) := integrableOn_const (hs := measure_Ico_lt_top.ne)
  have hshift : (∫ r in Ico β (Real.log ((m : ℝ) + 1)),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      - a * (1 / ((m : ℝ) + 1) ^ 2)
      = ∫ r in Ico β (Real.log ((m : ℝ) + 1)),
          ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
            - 1 / ((m : ℝ) + 1) ^ 2) := by
    rw [integral_sub hint2 hconst, setIntegral_const, hvol2, smul_eq_mul]
  have hwin : |(∫ r in Ico β (Real.log ((m : ℝ) + 1)),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      - a * (1 / ((m : ℝ) + 1) ^ 2)| ≤ 14 * a ^ 2 := by
    rw [hshift, ← Real.norm_eq_abs]
    have hb : ‖∫ r in Ico β (Real.log ((m : ℝ) + 1)),
        ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
          - 1 / ((m : ℝ) + 1) ^ 2)‖
        ≤ 14 * a * volume.real (Ico β (Real.log ((m : ℝ) + 1))) := by
      refine norm_setIntegral_le_of_norm_le_const measure_Ico_lt_top fun r hr => ?_
      have hjump := abs_packetDiff_sub_jump_le hω0 hω hm ha haM
        (by simpa only [hβ] using hr.1) hr.2
      have hxinv : 1 / ((m : ℝ) + 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hxinv0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have hsq : (1 : ℝ) / ((m : ℝ) + 1) ^ 2 = (1 / ((m : ℝ) + 1)) ^ 2 := by
        rw [div_pow, one_pow]
      have hfac : (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2
          - (1 / ((m : ℝ) + 1)) ^ 2
          = ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
              - 1 / ((m : ℝ) + 1))
            * ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
              + 1 / ((m : ℝ) + 1)) := by ring
      have hsum : |(complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
          + 1 / ((m : ℝ) + 1)| ≤ 7 * a + 2 * (1 / ((m : ℝ) + 1)) := by
        have hrw : (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
            + 1 / ((m : ℝ) + 1)
            = ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
                - 1 / ((m : ℝ) + 1)) + 2 * (1 / ((m : ℝ) + 1)) := by ring
        rw [hrw]
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 / ((m : ℝ) + 1)))]
        linarith
      rw [Real.norm_eq_abs, hsq, hfac, abs_mul]
      nlinarith [abs_nonneg ((complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r)
        - 1 / ((m : ℝ) + 1)), abs_nonneg ((complementaryPacketKernel ω (r + a)
        - complementaryPacketKernel ω r) + 1 / ((m : ℝ) + 1))]
    rw [hvol2] at hb
    refine hb.trans ?_
    nlinarith
  rw [hunion]
  have hsplit : (∫ r in Ico (Real.log (m : ℝ)) β,
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      + (∫ r in Ico β (Real.log ((m : ℝ) + 1)),
        (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      - a * (1 / ((m : ℝ) + 1) ^ 2)
      = (∫ r in Ico (Real.log (m : ℝ)) β,
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
        + ((∫ r in Ico β (Real.log ((m : ℝ) + 1)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          - a * (1 / ((m : ℝ) + 1) ^ 2)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  nlinarith [sq_nonneg a]

/-! ### Summation over the pieces -/

private theorem abs_setIntegral_main_sub_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω : ω ≤ 1 / 2) {a : ℝ}
    (ha : 0 < a) : ∀ M : ℕ, a ≤ 1 / (4 * ((M : ℝ) + 1)) →
      |(∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
        - a * ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2| ≤ 50 * M * a ^ 2 := by
  have hglob := integrableOn_complementaryPacketKernel_sub_sq hω0 hω ha.le
  intro M
  induction M with
  | zero =>
      intro _
      rw [show ((0 : ℕ) : ℝ) + 1 = 1 by norm_num, Real.log_one, Set.Ico_self]
      simp
  | succ M ih =>
      intro haM
      have hcast1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      have hcast2 : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      have hprev : a ≤ 1 / (4 * ((M : ℝ) + 1)) := by
        refine haM.trans ?_
        rw [hcast2]
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      have hpiece := abs_setIntegral_piece_sub_le hω0 hω (m := M + 1) (Nat.le_add_left 1 M) ha haM
      rw [hcast2, hcast1] at hpiece
      have hL1 : (0 : ℝ) ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
      have hL2 : Real.log ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hint1 : IntegrableOn
          (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          (Ico (0 : ℝ) (Real.log ((M : ℝ) + 1))) := hglob.mono_set fun r hr => hr.1
      have hint2 : IntegrableOn
          (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          (Ico (Real.log ((M : ℝ) + 1)) (Real.log ((M : ℝ) + 2))) :=
        hglob.mono_set fun r hr => le_trans hL1 hr.1
      have hunion : (∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 2)),
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          = (∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
              (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
            + ∫ r in Ico (Real.log ((M : ℝ) + 1)) (Real.log ((M : ℝ) + 2)),
                (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
        rw [← setIntegral_union Ico_disjoint_Ico_same measurableSet_Ico hint1 hint2,
          Ico_union_Ico_eq_Ico hL1 hL2]
      rw [hcast2, Finset.sum_range_succ, hcast1, hunion]
      have hreassoc : ((∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          + ∫ r in Ico (Real.log ((M : ℝ) + 1)) (Real.log ((M : ℝ) + 2)),
              (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          - a * ((∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2) + 1 / ((M : ℝ) + 2) ^ 2)
          = ((∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
              (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
              - a * ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2)
            + ((∫ r in Ico (Real.log ((M : ℝ) + 1)) (Real.log ((M : ℝ) + 2)),
                (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
              - a * (1 / ((M : ℝ) + 2) ^ 2)) := by ring
      rw [hreassoc]
      refine (abs_add_le _ _).trans ?_
      have hih := ih hprev
      have hnum : 50 * ((M : ℝ) + 1) * a ^ 2 = 50 * (M : ℝ) * a ^ 2 + 50 * a ^ 2 := by ring
      rw [hnum]
      linarith

/-! ### The swept branch -/

private theorem abs_setIntegral_swept_sub_le {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) {a : ℝ}
    (ha : 0 < a) (ha4 : a ≤ 1 / 4) :
    |(∫ r in Ioc (0 : ℝ) a,
        (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2) - a| ≤ 3 * a ^ 2 := by
  have hlog2 := Real.log_two_gt_d9
  have halog : a < Real.log 2 := by
    norm_num at hlog2
    linarith
  have hvol : volume.real (Ioc (0 : ℝ) a) = a := by
    rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ha.le]
  have hprofile : ∀ r ∈ Ioc (0 : ℝ) a,
      complementaryPacketKernel ω r + complementaryPacketConstant ω
        = Real.exp (-(1 + ω) * r) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hfl : ⌊Real.exp r⌋₊ = 1 := by
      refine (Nat.floor_eq_iff (Real.exp_pos r).le).mpr ⟨?_, ?_⟩
      · rw [Nat.cast_one]
        exact Real.one_le_exp hr0.le
      · rw [Nat.cast_one]
        have h := Real.exp_lt_exp.mpr (show r < Real.log 2 by linarith [hr.2])
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
        linarith
    have hstep : packetStepSum ω r = 1 := by
      rw [packetStepSum, hfl, Finset.sum_range_succ, Finset.sum_range_one, Nat.cast_zero,
        Nat.cast_one, Real.zero_rpow (ne_of_gt hω0), Real.one_rpow]
      norm_num
    rw [complementaryPacketKernel_add_const ω hω0.le r, hstep, mul_one]
  have hbound : ∀ r ∈ Ioc (0 : ℝ) a,
      ‖(complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 - 1‖ ≤ 3 * a := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr.1
    have hra : r ≤ a := hr.2
    rw [hprofile r hr]
    have hsq : Real.exp (-(1 + ω) * r) ^ 2 = Real.exp (-(2 * (1 + ω) * r)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hsq, Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ 2 * (1 + ω) * r := by positivity
    have hle : Real.exp (-(2 * (1 + ω) * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hge : 1 - 2 * (1 + ω) * r ≤ Real.exp (-(2 * (1 + ω) * r)) := by
      have h := Real.add_one_le_exp (-(2 * (1 + ω) * r))
      linarith
    rw [abs_le]
    constructor <;> nlinarith
  have hmeas : Measurable fun r : ℝ =>
      (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 :=
    ((measurable_complementaryPacketKernel ω hω0.le).add_const _).pow_const 2
  have hint : IntegrableOn
      (fun r => (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2)
      (Ioc (0 : ℝ) a) := by
    refine Integrable.mono' (integrableOn_const (C := (9 : ℝ)) (hs := measure_Ioc_lt_top.ne))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hprof := abs_packetIncomingProfile_le hω0.le hω hr.1.le
    have habs0 : (0 : ℝ) ≤ |complementaryPacketKernel ω r + complementaryPacketConstant ω| :=
      abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) a) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hshift : (∫ r in Ioc (0 : ℝ) a,
        (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2) - a
      = ∫ r in Ioc (0 : ℝ) a,
          ((complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 - 1) := by
    rw [integral_sub hint hconst, setIntegral_const, hvol, smul_eq_mul, mul_one]
  rw [hshift, ← Real.norm_eq_abs]
  have h : ‖∫ r in Ioc (0 : ℝ) a,
      ((complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2 - 1)‖
      ≤ 3 * a * volume.real (Ioc (0 : ℝ) a) :=
    norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hbound
  rw [hvol] at h
  refine h.trans ?_
  nlinarith

/-! ### The partial sums of `ζ(2)` -/

private theorem sum_range_add_two (M : ℕ) :
    ∑ n ∈ Finset.range (M + 2), 1 / (n : ℝ) ^ 2
      = 1 + ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2 := by
  induction M with
  | zero => norm_num [Finset.sum_range_succ]
  | succ M ih =>
      rw [show M + 1 + 2 = (M + 2) + 1 by ring, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      push_cast
      ring

/-! ### The local expansion -/

/-- **Local expansion, quantitative form.**  At separation `a` the two-point modulus of the
boundary packet is `a` times the `N`-th partial sum of `ζ(2)`, up to `O(N a²) + O(a/N)`. -/
theorem abs_complementaryPacketModulus_sub_partialZeta_le {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 1 ≤ N) (haN : a ≤ 1 / (4 * ((N : ℝ) + 1))) :
    |packetTranslationModulus (complementaryPacketKernel ω) (complementaryPacketConstant ω) a
        - a * ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2|
      ≤ 60 * N * a ^ 2 + 50 * a / N := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hNpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have haM : a ≤ 1 / (4 * ((M : ℝ) + 1)) := by
    refine haN.trans ?_
    rw [hcast]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have ha4 : a ≤ 1 / 4 := by
    refine haM.trans ?_
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have ha2 : a ≤ 1 / 2 := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) := Real.log_nonneg (by rw [hcast]; linarith)
  have hglob := integrableOn_complementaryPacketKernel_sub_sq hω0.le hω ha.le
  have hintIoc : IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ioc (0 : ℝ) (Real.log ((M + 1 : ℕ) : ℝ))) := hglob.mono_set fun r hr => hr.1.le
  have hintIoi : IntegrableOn
      (fun r => (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      (Ioi (Real.log ((M + 1 : ℕ) : ℝ))) := hglob.mono_set fun r hr => le_trans hL0 (le_of_lt hr)
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.log ((M + 1 : ℕ) : ℝ)))
      (Ioi (Real.log ((M + 1 : ℕ) : ℝ))) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx.2 (not_le.mpr hx2)
  have hsplitI : (∫ r in Ioi (0 : ℝ),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      = (∫ r in Ioc (0 : ℝ) (Real.log ((M + 1 : ℕ) : ℝ)),
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
        + ∫ r in Ioi (Real.log ((M + 1 : ℕ) : ℝ)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
    rw [← setIntegral_union hdisj measurableSet_Ioi hintIoc hintIoi,
      Ioc_union_Ioi_eq_Ioi hL0]
  have hIocIco : (∫ r in Ioc (0 : ℝ) (Real.log ((M + 1 : ℕ) : ℝ)),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
      = ∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
    rw [hcast, integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  have hmain := abs_setIntegral_main_sub_le hω0.le hω ha M haM
  have htail := setIntegral_complementaryPacketKernel_sub_sq_tail hω0.le hω ha.le ha2
    (N := M + 1) (by omega)
  have htail0 : 0 ≤ ∫ r in Ioi (Real.log ((M + 1 : ℕ) : ℝ)),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun r _ => sq_nonneg _
  have hswept := abs_setIntegral_swept_sub_le hω0 hω ha ha4
  have hzeta := sum_range_add_two M
  rw [packetTranslationModulus, hsplitI, hIocIco, show M + 1 + 1 = M + 2 by ring, hzeta]
  have hreassoc : ((∫ r in Ioc (0 : ℝ) a,
        (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2)
      + ((∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
          (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
        + ∫ r in Ioi (Real.log ((M + 1 : ℕ) : ℝ)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2))
      - a * (1 + ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2)
      = (((∫ r in Ioc (0 : ℝ) a,
            (complementaryPacketKernel ω r + complementaryPacketConstant ω) ^ 2) - a)
        + ((∫ r in Ico (0 : ℝ) (Real.log ((M : ℝ) + 1)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2)
          - a * ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 2) ^ 2))
        + ∫ r in Ioi (Real.log ((M + 1 : ℕ) : ℝ)),
            (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2 := by
    ring
  rw [hreassoc]
  refine (abs_add_le _ _).trans ?_
  have habs2 : |∫ r in Ioi (Real.log ((M + 1 : ℕ) : ℝ)),
      (complementaryPacketKernel ω (r + a) - complementaryPacketKernel ω r) ^ 2|
      ≤ 50 * a / ((M + 1 : ℕ) : ℝ) := by
    rw [abs_of_nonneg htail0]
    exact htail
  refine le_trans (add_le_add ((abs_add_le _ _).trans (add_le_add hswept hmain)) habs2) ?_
  have hnum : 60 * ((M + 1 : ℕ) : ℝ) * a ^ 2 = 60 * (M : ℝ) * a ^ 2 + 60 * a ^ 2 := by
    rw [hcast]; ring
  rw [hnum]
  nlinarith [sq_nonneg a]

/-- **Local `ζ(2)` expansion.**  The two-point modulus of the boundary complementary packet has
local slope `ζ(2) = π²/6` at zero separation, for every shift `0 < ω ≤ 1/2`. -/
theorem tendsto_complementaryPacketModulus_div_nhdsGT {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) :
    Filter.Tendsto (fun a : ℝ =>
        packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) a / a)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.pi ^ 2 / 6)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hZ : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ 2) Filter.atTop
      (nhds (Real.pi ^ 2 / 6)) := hasSum_zeta_two.tendsto_sum_nat
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hZ (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (150 / ε)
  set N : ℕ := max (max N₁ N₂) 1 with hNdef
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNN₂ : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h50 : 50 * (1 / (N : ℝ)) < ε / 3 := by
    have h : (150 : ℝ) / ε < (N : ℝ) := lt_of_lt_of_le hN₂ (by exact_mod_cast hNN₂)
    rw [div_lt_iff₀ hε] at h
    rw [mul_one_div, div_lt_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hZN : |(∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2) - Real.pi ^ 2 / 6| < ε / 3 := by
    have h := hN₁ (N + 1) (by omega)
    rwa [Real.dist_eq] at h
  refine ⟨min (1 / (4 * ((N : ℝ) + 1))) (ε / (180 * N)), lt_min (by positivity) (by positivity), ?_⟩
  intro x hx hdist
  have hx0 : (0 : ℝ) < x := hx
  have hdx : x < min (1 / (4 * ((N : ℝ) + 1))) (ε / (180 * N)) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx0] at hdist
    exact hdist
  have hx1 : x ≤ 1 / (4 * ((N : ℝ) + 1)) := le_of_lt (lt_of_lt_of_le hdx (min_le_left _ _))
  have hx2 : x < ε / (180 * N) := lt_of_lt_of_le hdx (min_le_right _ _)
  have hq := abs_complementaryPacketModulus_sub_partialZeta_le hω0 hω hx0 hN1 hx1
  have hdiv : |packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) x / x
      - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2|
      ≤ 60 * N * x + 50 * (1 / (N : ℝ)) := by
    have hrw : packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) x / x
        - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2
        = (packetTranslationModulus (complementaryPacketKernel ω)
            (complementaryPacketConstant ω) x
          - x * ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2) / x := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    refine hq.trans ?_
    rw [div_eq_mul_one_div]
    ring_nf
    nlinarith [hx0.le]
  have hsmall : 60 * (N : ℝ) * x < ε / 3 := by
    have hprod : 60 * (N : ℝ) * x < 60 * (N : ℝ) * (ε / (180 * (N : ℝ))) := by
      have h60 : (0 : ℝ) < 60 * (N : ℝ) := by linarith
      exact mul_lt_mul_of_pos_left hx2 h60
    have hval : 60 * (N : ℝ) * (ε / (180 * (N : ℝ))) = ε / 3 := by
      field_simp
      ring
    linarith [hprod, hval.le, hval.ge]
  rw [Real.dist_eq]
  have htri : packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) x / x - Real.pi ^ 2 / 6
      = (packetTranslationModulus (complementaryPacketKernel ω)
          (complementaryPacketConstant ω) x / x
        - ∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2)
        + ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℝ) ^ 2) - Real.pi ^ 2 / 6) := by ring
  rw [htri]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  linarith

/-- **The boundary packet is locally expansive.**  Near zero separation the two-point modulus
strictly exceeds the separation, so no pointwise contraction `D_ω(a) ≤ a` is available. -/
theorem eventually_lt_complementaryPacketModulus {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0),
      a < packetTranslationModulus (complementaryPacketKernel ω)
        (complementaryPacketConstant ω) a := by
  have hpi : (1 : ℝ) < Real.pi ^ 2 / 6 := by
    have h := Real.pi_gt_three
    nlinarith [Real.pi_pos]
  have hlim := tendsto_complementaryPacketModulus_div_nhdsGT hω0 hω
  have hev := hlim.eventually_const_lt hpi
  filter_upwards [hev, self_mem_nhdsWithin] with a hha ha
  have ha0 : (0 : ℝ) < a := ha
  rw [lt_div_iff₀ ha0] at hha
  linarith

end

end RHTower
