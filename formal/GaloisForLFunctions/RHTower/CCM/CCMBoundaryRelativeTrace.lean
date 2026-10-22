import GaloisForLFunctions.RHTower.CCM.CCMHankelGapTraceSlope

/-!
# The four-unit target is a boundary relative-trace density

The mass removed from a Hankel kernel `k (x, y) = ℓ (x + y)` by a one-sided output cutoff at `u`
has, on the antidiagonal `x + y = t`, exactly the strip length `min (t, u)`.  So the boundary block
energy is `∫ min (t, u) |ℓ|²`, an unconditional `ℝ≥0∞` quantity requiring no trace-class hypothesis.

Splitting the weight at `u` exhibits it as a local corner plus a cutoff-interface (commutator) term,
and identifies it with the increment of the shifted Hankel gap profile.  Its density at the origin
is the residue energy, the local corner contributes nothing at first order, the incoming Euler pole
has relative trace exactly `4 (1 − e^{−u})`, and for a finite right-half divisor packet the
nonexpansive density criterion holds exactly when the packet is empty.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

open scoped ENNReal

noncomputable section

variable {ℓ : ℝ → ℂ}

/-- **Equation (6).**  The boundary relative trace of a Hankel kernel. -/
def boundaryRelativeTrace (ℓ : ℝ → ℂ) (u : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), min t u * leakDensity ℓ t

/-- The local corner block, equation `(8b)`. -/
def cornerTrace (ℓ : ℝ → ℂ) (u : ℝ) : ℝ := ∫ t in Ioc (0 : ℝ) u, t * leakDensity ℓ t

/-- The cutoff-interface block: the projection-commutator energy of equation `(8a)`. -/
def crossTrace (ℓ : ℝ → ℂ) (u : ℝ) : ℝ := u * tailLeakEnergy ℓ u

/-! ## Integrability of the `min (t, u)` weight -/

theorem integrableOn_min_mul_Ioc (h : LeakProfile ℓ) {u : ℝ} (_hu : 0 < u) :
    IntegrableOn (fun t => min t u * leakDensity ℓ t) (Ioc (0 : ℝ) u) volume := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_shifted h (le_refl (0 : ℝ))).mono_set Ioc_subset_Ioi_self) ?_
    measurableSet_Ioc
  intro t ht
  show (t - 0) * leakDensity ℓ t = min t u * leakDensity ℓ t
  rw [sub_zero, min_eq_left ht.2]

theorem integrableOn_min_mul_Ioi (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t => min t u * leakDensity ℓ t) (Ioi u) volume := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_tail h (le_of_lt hu)).const_mul u) ?_ measurableSet_Ioi
  intro t ht
  show u * leakDensity ℓ t = min t u * leakDensity ℓ t
  rw [min_eq_right (le_of_lt ht)]

theorem integrableOn_min_mul (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t => min t u * leakDensity ℓ t) (Ioi (0 : ℝ)) volume := by
  have hun := (integrableOn_min_mul_Ioc h hu).union (integrableOn_min_mul_Ioi h hu)
  rwa [Ioc_union_Ioi_eq_Ioi (le_of_lt hu)] at hun

/-! ## The corner-plus-interface splitting -/

/-- **Equations (7) and (8a).**  The relative trace splits into the local corner and the
cutoff-interface (projection-commutator) term. -/
theorem boundaryRelativeTrace_eq (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace ℓ u = cornerTrace ℓ u + crossTrace ℓ u := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 u ∪ Ioi u := (Ioc_union_Ioi_eq_Ioi (le_of_lt hu)).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) u) (Ioi u) := Ioc_disjoint_Ioi le_rfl
  unfold boundaryRelativeTrace cornerTrace crossTrace tailLeakEnergy
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi (integrableOn_min_mul_Ioc h hu)
    (integrableOn_min_mul_Ioi h hu)]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [min_eq_left ht.2]
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [min_eq_right (le_of_lt ht)]

/-- **Equation (11).**  The relative trace is the increment of the shifted Hankel gap profile. -/
theorem boundaryRelativeTrace_eq_gap_sub (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace ℓ u = hankelGapProfile ℓ 0 - hankelGapProfile ℓ u := by
  have hcorner : (∫ t in Ioc (0 : ℝ) u, (t - 0) * leakDensity ℓ t)
      = ∫ t in Ioc (0 : ℝ) u, t * leakDensity ℓ t :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ => by
      show (t - 0) * leakDensity ℓ t = t * leakDensity ℓ t
      rw [sub_zero]
  rw [boundaryRelativeTrace_eq h hu, hankelGapProfile_sub h (le_refl (0 : ℝ)) hu, hcorner,
    sub_zero]
  unfold cornerTrace crossTrace
  ring

/-- **Equation (9).**  The relative-trace difference quotient is the `min (t/u, 1)`-weighted
residue integral. -/
theorem boundaryRelativeTrace_div {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace ℓ u / u = ∫ t in Ioi (0 : ℝ), min (t / u) 1 * leakDensity ℓ t := by
  unfold boundaryRelativeTrace
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  show min t u * leakDensity ℓ t / u = min (t / u) 1 * leakDensity ℓ t
  have hmin : min (t / u) 1 = min t u / u := by
    rw [show (1 : ℝ) = u / u from (div_self (ne_of_gt hu)).symm, min_div_div_right (le_of_lt hu)]
  rw [hmin]
  ring

/-- **Equation (10).**  The relative-trace density at the origin is the residue energy. -/
theorem tendsto_boundaryRelativeTrace_div (h : LeakProfile ℓ) :
    Tendsto (fun u : ℝ => boundaryRelativeTrace ℓ u / u) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Ioi (0 : ℝ), leakDensity ℓ t)) := by
  refine (tendsto_initial_slope h).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [boundaryRelativeTrace_eq_gap_sub h hu]

/-- **Equation (8c).**  The local corner is negligible at first order. -/
theorem cornerTrace_div_le (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    cornerTrace ℓ u / u ≤ tailLeakEnergy ℓ 0 - tailLeakEnergy ℓ u := by
  have hintCorner : IntegrableOn (fun t => t * leakDensity ℓ t) (Ioc (0 : ℝ) u) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_shifted h (le_refl (0 : ℝ))).mono_set Ioc_subset_Ioi_self) ?_
      measurableSet_Ioc
    intro t _
    show (t - 0) * leakDensity ℓ t = t * leakDensity ℓ t
    rw [sub_zero]
  have hbound : cornerTrace ℓ u ≤ u * ∫ t in Ioc (0 : ℝ) u, leakDensity ℓ t := by
    unfold cornerTrace
    rw [← integral_const_mul]
    refine setIntegral_mono_on hintCorner
      (((integrableOn_tail h (le_refl (0 : ℝ))).mono_set Ioc_subset_Ioi_self).const_mul u)
      measurableSet_Ioc fun t ht => ?_
    have hd := leakDensity_nonneg ℓ t
    nlinarith [ht.2]
  have heq := tailLeakEnergy_sub h (le_refl (0 : ℝ)) hu
  rw [div_le_iff₀ hu, heq, mul_comm]
  exact hbound

/-- **Equation (8d).**  The whole first-order charge crosses the cutoff interface: the
projection-commutator density is the full residue energy. -/
theorem tendsto_crossTrace_div (h : LeakProfile ℓ) :
    Tendsto (fun u : ℝ => crossTrace ℓ u / u) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Ioi (0 : ℝ), leakDensity ℓ t)) := by
  have hcong : ∀ u : ℝ, 0 < u → crossTrace ℓ u / u = tailLeakEnergy ℓ u := by
    intro u hu
    unfold crossTrace
    field_simp
  have hlim := tendsto_tailLeakEnergy_right h (le_refl (0 : ℝ))
  refine (hlim.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [hcong u hu]

/-! ## The one-sided output boundary block -/

/-- **Equation (5a).**  The squared Hilbert–Schmidt mass of the output-boundary block `Q_u H_ℓ` of
the Hankel kernel `k (x, y) = ℓ (x + y)`, as an unconditional `ℝ≥0∞`-valued energy: no trace-class
hypothesis is needed to define it. -/
def boundaryBlockEnergy (ℓ : ℝ → ℂ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) u, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (leakDensity ℓ (x + y))

/-- Translating the half-line moves the base point. -/
theorem lintegral_Ioi_shift (g : ℝ → ℝ≥0∞) (x : ℝ) :
    ∫⁻ y in Ioi (0 : ℝ), g (x + y) = ∫⁻ t in Ioi x, g t := by
  have hmp : MeasurePreserving (fun y : ℝ => x + y) volume volume :=
    measurePreserving_add_left volume x
  have hemb : MeasurableEmbedding (fun y : ℝ => x + y) :=
    (Homeomorph.addLeft x).measurableEmbedding
  have hpre : (fun y : ℝ => x + y) ⁻¹' Ioi x = Ioi (0 : ℝ) := by ext y; simp
  have hcomp := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi x)
  rw [hpre] at hcomp
  exact hcomp

/-- **Equations (5a)–(6), kernel form.**  On the antidiagonal `x + y = t` the removed output strip
has length `min (t, u)`, so the boundary block energy is the `min (t, u)`-weighted leak integral.
This is the geometric core of the card: the three-block relative trace equals the one-sided
output-boundary trace, whose kernel is `min (t, u)`. -/
theorem boundaryBlockEnergy_eq_lintegral (hℓ : Measurable ℓ) {u : ℝ} (hu : 0 ≤ u) :
    boundaryBlockEnergy ℓ u
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min t u * leakDensity ℓ t) := by
  have hd : Measurable fun t : ℝ => ENNReal.ofReal (leakDensity ℓ t) :=
    (hℓ.norm.pow_const 2).ennreal_ofReal
  have hcut : Measurable (Function.uncurry
      fun x t : ℝ => if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    exact hd.comp measurable_snd
  have hinner : EqOn (fun x : ℝ => ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (leakDensity ℓ (x + y)))
      (fun x : ℝ => ∫⁻ t in Ioi (0 : ℝ),
        if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0) (Ioo (0 : ℝ) u) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx.1
    show (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (leakDensity ℓ (x + y)))
      = ∫⁻ t in Ioi (0 : ℝ), if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0
    rw [lintegral_Ioi_shift (fun t => ENNReal.ofReal (leakDensity ℓ t)) x]
    have hind : (fun t : ℝ => if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0)
        = (Ioi x).indicator fun t => ENNReal.ofReal (leakDensity ℓ t) := by
      funext t
      simp [Set.indicator_apply, Set.mem_Ioi]
    rw [hind, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left hx0]
  unfold boundaryBlockEnergy
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner,
    lintegral_lintegral_swap (f := fun x t : ℝ =>
      if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0) hcut.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hind : (fun x : ℝ => if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0)
      = (Iio t).indicator fun _ => ENNReal.ofReal (leakDensity ℓ t) := by
    funext x
    simp [Set.indicator_apply, Set.mem_Iio]
  show (∫⁻ x in Ioo (0 : ℝ) u, if x < t then ENNReal.ofReal (leakDensity ℓ t) else 0)
    = ENNReal.ofReal (min t u * leakDensity ℓ t)
  rw [hind, lintegral_indicator measurableSet_Iio, setLIntegral_const,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Iio t ∩ Ioo (0 : ℝ) u = Ioo (0 : ℝ) (min t u) := by
    ext x
    constructor
    · rintro ⟨hxt, hx0, hxu⟩
      exact ⟨hx0, lt_min hxt hxu⟩
    · rintro ⟨hx0, hxm⟩
      exact ⟨lt_of_lt_of_le hxm (min_le_left _ _), hx0, lt_of_lt_of_le hxm (min_le_right _ _)⟩
  rw [hset, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul (le_min (le_of_lt ht0) hu), mul_comm]

/-- **Equations (5a)–(7).**  Under the sole `L²` hypothesis the boundary block energy is finite and
equals the boundary relative trace. -/
theorem boundaryBlockEnergy_eq (hℓ : Measurable ℓ) (h : LeakProfile ℓ) {u : ℝ} (hu : 0 < u) :
    boundaryBlockEnergy ℓ u = ENNReal.ofReal (boundaryRelativeTrace ℓ u) := by
  rw [boundaryBlockEnergy_eq_lintegral hℓ (le_of_lt hu)]
  refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrableOn_min_mul h hu) ?_).symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (le_min (le_of_lt ht) (le_of_lt hu)) (leakDensity_nonneg ℓ t)

/-! ## The incoming Euler pole -/

/-- The gap profile of the incoming Euler pole. -/
theorem hankelGapProfile_polePacket {u : ℝ} (hu : 0 ≤ u) :
    hankelGapProfile polePacketProfile u = 4 * Real.exp (-u) := by
  have hb : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have hcomplex := integral_Ioi_sub_mul_cexp_neg_mul (b := 1) hb hu
  have hpt : ∀ t : ℝ, (((t - u) * leakDensity polePacketProfile t : ℝ) : ℂ)
      = 4 * (((t : ℂ) - (u : ℂ)) * Complex.exp (-(1 * (t : ℂ)))) := by
    intro t
    have hE : Complex.exp (-(1 * (t : ℂ))) = ((Real.exp (-1 * t) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [leakDensity_polePacketProfile, hE]
    push_cast
    ring
  have hcast : ((hankelGapProfile polePacketProfile u : ℝ) : ℂ)
      = ((4 * Real.exp (-u) : ℝ) : ℂ) := by
    unfold hankelGapProfile
    calc ((∫ t in Ioi u, (t - u) * leakDensity polePacketProfile t : ℝ) : ℂ)
        = ∫ t in Ioi u, (((t - u) * leakDensity polePacketProfile t : ℝ) : ℂ) :=
          integral_complex_ofReal.symm
      _ = ∫ t in Ioi u, 4 * (((t : ℂ) - (u : ℂ)) * Complex.exp (-(1 * (t : ℂ)))) :=
          setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t
      _ = 4 * ∫ t in Ioi u, ((t : ℂ) - (u : ℂ)) * Complex.exp (-(1 * (t : ℂ))) :=
          integral_const_mul _ _
      _ = 4 * (Complex.exp (-(1 * (u : ℂ))) * (1 : ℂ)⁻¹ ^ 2) := by rw [hcomplex]
      _ = ((4 * Real.exp (-u) : ℝ) : ℂ) := by
          have hE : Complex.exp (-(1 * (u : ℂ))) = ((Real.exp (-u) : ℝ) : ℂ) := by
            rw [Complex.ofReal_exp]
            congr 1
            push_cast
            ring
          rw [hE]
          push_cast
          ring
  exact_mod_cast hcast

/-- **Equation (13).**  The incoming Euler pole has boundary relative trace exactly
`4 (1 − e^{−u})`. -/
theorem boundaryRelativeTrace_polePacket {u : ℝ} (hu : 0 < u) :
    boundaryRelativeTrace polePacketProfile u = 4 * (1 - Real.exp (-u)) := by
  rw [boundaryRelativeTrace_eq_gap_sub leakProfile_polePacket hu,
    hankelGapProfile_polePacket (le_refl (0 : ℝ)), hankelGapProfile_polePacket (le_of_lt hu),
    neg_zero, Real.exp_zero]
  ring

/-- **Equation (14).**  The four-unit source budget is an initial boundary-layer density. -/
theorem tendsto_boundaryRelativeTrace_div_polePacket :
    Tendsto (fun u : ℝ => boundaryRelativeTrace polePacketProfile u / u) (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  have h := tendsto_boundaryRelativeTrace_div leakProfile_polePacket
  rwa [show (∫ t in Ioi (0 : ℝ), leakDensity polePacketProfile t)
      = tailLeakEnergy polePacketProfile 0 from rfl, tailLeakEnergy_polePacket_zero] at h

/-! ## The completed divisor and the exact criterion -/

/-- The boundary relative-trace density of a finite right-half divisor packet is its Cauchy
residue energy, equation `(16)`. -/
theorem tendsto_boundaryRelativeTrace_div_divisorPacket {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    Tendsto (fun u : ℝ => boundaryRelativeTrace (divisorPacketProfile lam m) u / u)
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorPacketEnergy lam m)) := by
  refine (tendsto_initial_slope_divisorPacket hlam).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [boundaryRelativeTrace_eq_gap_sub (leakProfile_divisorPacket hlam) hu]

/-- **Equation (17), ratio form.**  The completed-to-pole relative-trace ratio has a limit at the
origin, namely a quarter of the residue energy. -/
theorem tendsto_boundaryRelativeTrace_ratio {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    Tendsto (fun u : ℝ => boundaryRelativeTrace (divisorPacketProfile lam m) u
        / boundaryRelativeTrace polePacketProfile u)
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorPacketEnergy lam m / 4)) := by
  have hnum := tendsto_boundaryRelativeTrace_div_divisorPacket (m := m) hlam
  have hden := tendsto_boundaryRelativeTrace_div_polePacket
  refine (hnum.div hden (by norm_num)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact div_div_div_cancel_right₀ (ne_of_gt hu) _ _

/-- **Equations (16)–(17).**  Nonexpansive infinitesimal boundary relative trace — the completed
source does not increase the pole's boundary density — holds exactly when the off-line divisor is
empty. -/
theorem boundaryRelativeTrace_ratio_le_one_iff {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) (hstrip : ∀ j, (lam j).re < 1 / 2) (hm : ∀ j, 0 < m j) :
    divisorPacketEnergy lam m / 4 ≤ 1 ↔ r = 0 := by
  rw [div_le_one (by norm_num : (0 : ℝ) < 4)]
  exact divisorPacketEnergy_le_four_iff hlam hstrip hm

/-- **Equation (17), density form.**  Every limit of the boundary relative-trace difference quotient
of a finite right-half divisor packet is at most four exactly when the packet is empty. -/
theorem boundaryRelativeTrace_density_le_four_iff {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) (hstrip : ∀ j, (lam j).re < 1 / 2) (hm : ∀ j, 0 < m j) :
    (∀ L : ℝ, Tendsto (fun u : ℝ => boundaryRelativeTrace (divisorPacketProfile lam m) u / u)
        (𝓝[>] (0 : ℝ)) (𝓝 L) → L ≤ 4) ↔ r = 0 := by
  have hlim := tendsto_boundaryRelativeTrace_div_divisorPacket (m := m) hlam
  constructor
  · intro hall
    exact (divisorPacketEnergy_le_four_iff hlam hstrip hm).1 (hall _ hlim)
  · intro hr L hL
    have hLE : L = divisorPacketEnergy lam m := tendsto_nhds_unique hL hlim
    rw [hLE]
    exact (divisorPacketEnergy_le_four_iff hlam hstrip hm).2 hr

end

end GaloisForLFunctions.RHTower
