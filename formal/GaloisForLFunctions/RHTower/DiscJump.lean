import GaloisForLFunctions.RHTower.WindowLadder

/-!
# The DISC jump divisor on the critical line

The box order sum `boxOrderSum T = ∑ orders of ξ-zeros in {½<Re<1, 0≤Im<T}` is a step function of
the height `T`, built entirely from the bulk (the analytic ξ): it is monotone, constant on every
height interval free of box zeros, and jumps by the total order of the zeros it crosses.  Reduced
modulo `2^k` it is the **DISC census** `discCensusH k T`, locally constant off the zero heights.

The increments of this step function assemble into a discrete object on the line, the **jump
divisor** `discJump : ℝ → ℕ`: `discJump t` is the total ξ-order at height `t`, so its support is
the set of zero heights and its partial sums recover the census —
`boxOrderSum T = ∑_{t below T} discJump t`.  This is the object the boundary program interrogates:
a locally finite ℕ-valued divisor on ℝ, made from bulk data, whose `2^k`-divisibility is the rung
and whose emptiness is RH.  Off the zero heights the census is flat; the rung certificate forces
every jump to be `2^k`-divisible and the census to vanish.
-/

namespace RHTower

open Complex Set Metric

/-! ## The box order sum as a step function of the height -/

/-- The finite set of box-window ξ-zeros below height `T`. -/
noncomputable def boxFinset (T : ℝ) : Finset ℂ := (boxZeros_finite T).toFinset

theorem mem_boxFinset {T : ℝ} {z : ℂ} : z ∈ boxFinset T ↔ z ∈ boxZeros T := by
  rw [boxFinset, Set.Finite.mem_toFinset]

/-- The total ξ-vanishing order enclosed in the box window below height `T`. -/
noncomputable def boxOrderSum (T : ℝ) : ℕ :=
  ∑ z ∈ boxFinset T, (analyticOrderAt xi z).toNat

theorem boxFinset_subset {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : boxFinset T₁ ⊆ boxFinset T₂ := by
  intro z hz
  rw [mem_boxFinset] at hz ⊢
  exact boxZeros_mono h hz

/-- The order sum is monotone in the height. -/
theorem boxOrderSum_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : boxOrderSum T₁ ≤ boxOrderSum T₂ :=
  Finset.sum_le_sum_of_subset (boxFinset_subset h)

/-- Members of the height slice `[T₁, T₂)` are exactly the newly enclosed zeros. -/
theorem mem_boxFinset_sdiff {T₁ T₂ : ℝ} {z : ℂ} :
    z ∈ boxFinset T₂ \ boxFinset T₁ ↔ z ∈ boxZeros T₂ ∧ T₁ ≤ z.im := by
  rw [Finset.mem_sdiff, mem_boxFinset, mem_boxFinset]
  constructor
  · rintro ⟨hz2, hz1⟩
    refine ⟨hz2, ?_⟩
    by_contra hlt
    exact hz1 ⟨⟨hz2.1.1, hz2.1.2.1, hz2.1.2.2.1, not_le.mp hlt⟩, hz2.2⟩
  · rintro ⟨hz2, hge⟩
    refine ⟨hz2, fun hz1 => absurd hz1.1.2.2.2 (not_lt.mpr hge)⟩

/-- **The jump formula.**  Raising the height from `T₁` to `T₂` adds exactly the total order of the
zeros with height in `[T₁, T₂)`. -/
theorem boxOrderSum_add_sdiff {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    boxOrderSum T₁ + ∑ z ∈ boxFinset T₂ \ boxFinset T₁, (analyticOrderAt xi z).toNat
      = boxOrderSum T₂ := by
  rw [boxOrderSum, boxOrderSum, add_comm]
  exact Finset.sum_sdiff (boxFinset_subset h)

/-- **Local constancy.**  On a height interval with no box zeros the order sum does not change. -/
theorem boxOrderSum_const_of_no_zeros {T₁ T₂ : ℝ} (h : T₁ ≤ T₂)
    (hno : ∀ z ∈ boxZeros T₂, z.im < T₁) :
    boxOrderSum T₁ = boxOrderSum T₂ := by
  have hsdiff : boxFinset T₂ \ boxFinset T₁ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_boxFinset_sdiff] at hz
    exact absurd (hno z hz.1) (not_lt.mpr hz.2)
  have hkey := boxOrderSum_add_sdiff h
  rw [hsdiff, Finset.sum_empty, add_zero] at hkey
  exact hkey

/-! ## The jump divisor -/

/-- The ξ-zeros of the box at exactly height `t`. -/
def boxHeightZeros (t : ℝ) : Set ℂ :=
  {z : ℂ | 1 / 2 < z.re ∧ z.re < 1 ∧ z.im = t ∧ xi z = 0}

/-- Only finitely many box ξ-zeros sit at any one height. -/
theorem boxHeightZeros_finite (t : ℝ) : (boxHeightZeros t).Finite := by
  apply (xi_zeros_finite_ball 2 (|t| + 2)).subset
  rintro z ⟨h1, h2, him, hz⟩
  refine ⟨?_, hz⟩
  rw [mem_ball, dist_eq_norm]
  calc ‖z - 2‖ ≤ |(z - 2).re| + |(z - 2).im| := norm_le_abs_re_add_abs_im _
    _ = |z.re - 2| + |z.im| := by simp
    _ < |t| + 2 := by
        have ha : |z.re - 2| < 2 := by rw [abs_lt]; constructor <;> linarith
        have hb : |z.im| = |t| := by rw [him]
        linarith

/-- **The jump divisor**: the total ξ-vanishing order at height `t`.  A locally finite `ℕ`-valued
divisor on the line whose value at `t` is the size of the step the order sum takes at height `t`. -/
noncomputable def discJump (t : ℝ) : ℕ :=
  ∑ z ∈ (boxHeightZeros_finite t).toFinset, (analyticOrderAt xi z).toNat

/-- **The support of the divisor is the set of zero heights.**  `discJump t = 0` exactly when the
box carries no ξ-zero at height `t`. -/
theorem discJump_eq_zero_iff (t : ℝ) : discJump t = 0 ↔ boxHeightZeros t = ∅ := by
  rw [discJump, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact xi_order_toNat_ne_zero hz.2.2.2 (h z ((Set.Finite.mem_toFinset _).mpr hz))
  · intro h z hz
    rw [Set.Finite.mem_toFinset, h] at hz
    exact absurd hz (Set.notMem_empty z)

private theorem sum_fiber_im (s : Finset ℂ) (f : ℂ → ℕ) :
    ∑ y ∈ s.image Complex.im, ∑ z ∈ s.filter (fun z => z.im = y), f z = ∑ z ∈ s, f z :=
  Finset.sum_image' f fun _ _ => rfl

/-- The height slice of `boxFinset T` at a height `t` present in it is precisely the height-`t`
zero set. -/
theorem boxFinset_fiber {T t : ℝ} (ht : t ∈ (boxFinset T).image Complex.im) :
    (boxFinset T).filter (fun z => z.im = t) = (boxHeightZeros_finite t).toFinset := by
  rw [Finset.mem_image] at ht
  obtain ⟨w, hw, hwt⟩ := ht
  rw [mem_boxFinset] at hw
  have ht0 : 0 ≤ t := hwt ▸ hw.1.2.2.1
  have htT : t < T := hwt ▸ hw.1.2.2.2
  ext z
  rw [Finset.mem_filter, mem_boxFinset, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨⟨h1, h2, _, _⟩, hz⟩, him⟩
    exact ⟨h1, h2, him, hz⟩
  · rintro ⟨h1, h2, him, hz⟩
    exact ⟨⟨⟨h1, h2, by rw [him]; exact ht0, by rw [him]; exact htT⟩, hz⟩, him⟩

/-- **The partial sums of the divisor recover the order sum.**  The box order sum below `T` is the
sum of the jump divisor over the (finitely many) heights it visits. -/
theorem boxOrderSum_eq_sum_discJump (T : ℝ) :
    boxOrderSum T = ∑ t ∈ (boxFinset T).image Complex.im, discJump t := by
  rw [boxOrderSum, ← sum_fiber_im (boxFinset T) (fun z => (analyticOrderAt xi z).toNat)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [discJump, boxFinset_fiber ht]

/-! ## The DISC census as a function of the height -/

/-- **The DISC census at height `T`**: the box order sum reduced modulo `2^k`, valued in the finite
ring `ZMod (2^k)`. -/
noncomputable def discCensusH (k : ℕ) (T : ℝ) : ZMod (2 ^ k) := (boxOrderSum T : ZMod (2 ^ k))

/-- **The census is locally constant off the zero heights.** -/
theorem discCensusH_const_of_no_zeros {k : ℕ} {T₁ T₂ : ℝ} (h : T₁ ≤ T₂)
    (hno : ∀ z ∈ boxZeros T₂, z.im < T₁) :
    discCensusH k T₁ = discCensusH k T₂ := by
  rw [discCensusH, discCensusH, boxOrderSum_const_of_no_zeros h hno]

/-- **The certificate divides every jump.**  If the level-`k` height-`T` certificate holds, every
jump at a height below `T` is `2^k`-divisible: the divisor is entrywise a multiple of `2^k`. -/
theorem dvd_discJump_of_windowCertificate {k : ℕ} {T : ℝ} (hc : WindowCertificate k T)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < T) :
    2 ^ k ∣ discJump t := by
  rw [discJump]
  refine Finset.dvd_sum (fun z hz => ?_)
  rw [Set.Finite.mem_toFinset] at hz
  have him : z.im = t := hz.2.2.1
  have hmem : z ∈ boxZeros T :=
    ⟨⟨hz.1, hz.2.1, by rw [him]; exact ht0, by rw [him]; exact ht⟩, hz.2.2.2⟩
  have hdvd := hc z hmem
  have hcoe : analyticOrderAt xi z = (((analyticOrderAt xi z).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top z)).symm
  rw [hcoe] at hdvd
  exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

/-- **The certificate flattens the census.**  Under the level-`k` height-`T` certificate the DISC
census vanishes: every enclosed order is `2^k`-divisible, so is their sum. -/
theorem discCensusH_eq_zero_of_windowCertificate {k : ℕ} {T : ℝ} (hc : WindowCertificate k T) :
    discCensusH k T = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  rw [discCensusH, ZMod.natCast_eq_zero_iff, boxOrderSum]
  refine Finset.dvd_sum (fun z hz => ?_)
  rw [mem_boxFinset] at hz
  have hdvd := hc z hz
  have hcoe : analyticOrderAt xi z = (((analyticOrderAt xi z).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top z)).symm
  rw [hcoe] at hdvd
  exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvd

/-! ## RH as the emptiness of the jump divisor -/

/-- The jump divisor is empty at every height iff the box is zero-free at every height: an off-axis
ξ-zero contributes at its own height, and conjugation carries the lower half-plane to the upper. -/
theorem forall_boxHeightZeros_empty_iff :
    (∀ t : ℝ, boxHeightZeros t = ∅) ↔ ∀ T : ℝ, boxZeros T = ∅ := by
  constructor
  · intro h T
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨h1, h2, _, _⟩, hz⟩
    have : z ∈ boxHeightZeros z.im := ⟨h1, h2, rfl, hz⟩
    rw [h z.im] at this
    exact absurd this (Set.notMem_empty z)
  · intro h t
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨h1, h2, him, hz⟩
    rcases le_or_gt 0 z.im with hpos | hneg
    · have hmem : z ∈ boxZeros (z.im + 1) :=
        ⟨⟨h1, h2, hpos, lt_add_one z.im⟩, hz⟩
      rw [h (z.im + 1)] at hmem
      exact absurd hmem (Set.notMem_empty z)
    · have hcz : xi ((starRingEnd ℂ) z) = 0 := by rw [xi_conj, hz, map_zero]
      have hmem : (starRingEnd ℂ) z ∈ boxZeros (-z.im + 1) := by
        refine ⟨⟨?_, ?_, ?_, ?_⟩, hcz⟩
        · rwa [Complex.conj_re]
        · rwa [Complex.conj_re]
        · rw [Complex.conj_im]; linarith
        · rw [Complex.conj_im]; linarith
      rw [h (-z.im + 1)] at hmem
      exact absurd hmem (Set.notMem_empty _)

/-- **RH as an empty divisor.**  The Riemann Hypothesis holds iff the jump divisor vanishes
identically — no ξ-order accrues at any height off the critical line.  The boundary program can
therefore interrogate the discrete jump divisor on the line in place of the ξ-zeros in the
plane. -/
theorem rh_iff_forall_discJump_eq_zero : RiemannHypothesis ↔ ∀ t : ℝ, discJump t = 0 := by
  rw [rh_iff_forall_boxZeros_empty, ← forall_boxHeightZeros_empty_iff]
  exact forall_congr' fun t => (discJump_eq_zero_iff t).symm

end RHTower
