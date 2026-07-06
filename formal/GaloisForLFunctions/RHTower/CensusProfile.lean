import GaloisForLFunctions.RHTower.DiscJump
import GaloisForLFunctions.RHTower.DiscCensus

/-!
# The census profile as a right-continuous step function

The box order sum with a **closed** height cutoff, `boxOrderSumLe T = ∑ orders of ξ-zeros in
{½<Re<1, 0≤Im≤T}`, is the right-continuous normalisation of the census: its value at `T` includes
the zeros sitting exactly at height `T`, so it is constant just to the right of every height and
jumps as the height is approached from the left.  Reduced mod `2^k` it is the **census profile**
`censusProfile k : ℝ → ZMod (2^k)`, a right-continuous `ZMod (2^k)`-valued step function whose jump
at `T` is the jump divisor `discJump T` and which is locally constant off the zero heights.

Two refinements bind the profile to the seam:

* **(a) the finite-carrier census profile** — for a supplied family of reflection-closed
  `completedGN N` configurations `G T` enclosing the same height slice, with the two boundary
  congruences at every height, the ξ profile EQUALS the decidable finite-carrier profile
  `T ↦ windowDiscBit k (G T) mg` as functions into `ZMod (2^k)` (`censusProfile_eq_finiteCensusProfile`).
* **(b) the divisor difference** — `jumpDiff t = discJump t − (finite-carrier jump at t)`, a signed
  divisor on ℝ supported where the two carriers' zero heights disagree, whose value is a multiple of
  `2^k` at every height carrying the transported rung datum (`two_pow_dvd_jumpDiff`).
-/

namespace RHTower

open Complex Set Metric Filter Topology

/-! ## The closed-cutoff box order sum -/

/-- Box ξ-zeros with height at most `T` (closed cutoff). -/
def boxZerosLe (T : ℝ) : Set ℂ :=
  {z : ℂ | 1 / 2 < z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im ≤ T ∧ xi z = 0}

theorem boxZerosLe_finite (T : ℝ) : (boxZerosLe T).Finite := by
  apply (boxZeros_finite (T + 1)).subset
  rintro z ⟨h1, h2, h3, h4, hz⟩
  exact ⟨⟨h1, h2, h3, by linarith⟩, hz⟩

/-- The finite set of box ξ-zeros with height at most `T`. -/
noncomputable def boxFinsetLe (T : ℝ) : Finset ℂ := (boxZerosLe_finite T).toFinset

theorem mem_boxFinsetLe {T : ℝ} {z : ℂ} : z ∈ boxFinsetLe T ↔ z ∈ boxZerosLe T :=
  (boxZerosLe_finite T).mem_toFinset

/-- The total ξ-order enclosed in the box up to and including height `T`. -/
noncomputable def boxOrderSumLe (T : ℝ) : ℕ :=
  ∑ z ∈ boxFinsetLe T, (analyticOrderAt xi z).toNat

theorem boxFinsetLe_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : boxFinsetLe T₁ ⊆ boxFinsetLe T₂ := by
  intro z hz
  rw [mem_boxFinsetLe] at hz ⊢
  obtain ⟨h1, h2, h3, h4, hz0⟩ := hz
  exact ⟨h1, h2, h3, le_trans h4 h, hz0⟩

theorem boxOrderSumLe_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : boxOrderSumLe T₁ ≤ boxOrderSumLe T₂ :=
  Finset.sum_le_sum_of_subset (boxFinsetLe_mono h)

/-- **The closed cutoff splits into the open sum plus the height's jump.**  At a nonnegative height
the closed box order sum is the open box order sum plus the jump divisor at that height. -/
theorem boxOrderSumLe_eq_add_discJump {T : ℝ} (hT : 0 ≤ T) :
    boxOrderSumLe T = boxOrderSum T + discJump T := by
  have hdisj : Disjoint (boxFinset T) ((boxHeightZeros_finite T).toFinset) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_boxFinset] at hz
    rw [Set.Finite.mem_toFinset] at hz'
    exact absurd hz'.2.2.1 (ne_of_lt hz.1.2.2.2)
  have hunion : boxFinsetLe T = boxFinset T ∪ (boxHeightZeros_finite T).toFinset := by
    ext z
    rw [mem_boxFinsetLe, Finset.mem_union, mem_boxFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2, h3, h4, hz0⟩
      rcases lt_or_eq_of_le h4 with hlt | heq
      · exact Or.inl ⟨⟨h1, h2, h3, hlt⟩, hz0⟩
      · exact Or.inr ⟨h1, h2, heq, hz0⟩
    · rintro (⟨⟨h1, h2, h3, h4⟩, hz0⟩ | ⟨h1, h2, heq, hz0⟩)
      · exact ⟨h1, h2, h3, le_of_lt h4, hz0⟩
      · exact ⟨h1, h2, heq ▸ hT, le_of_eq heq, hz0⟩
  rw [boxOrderSumLe, hunion, Finset.sum_union hdisj, boxOrderSum, discJump]

/-- **Local constancy.**  On a height interval carrying no box zeros the closed order sum is
constant. -/
theorem boxOrderSumLe_const_of_no_zeros {T₁ T₂ : ℝ} (h : T₁ ≤ T₂)
    (hno : ∀ z ∈ boxZerosLe T₂, z.im ≤ T₁) :
    boxOrderSumLe T₁ = boxOrderSumLe T₂ := by
  refine le_antisymm (boxOrderSumLe_mono h) ?_
  apply Finset.sum_le_sum_of_subset
  intro z hz
  rw [mem_boxFinsetLe] at hz ⊢
  obtain ⟨h1, h2, h3, h4, hz0⟩ := hz
  exact ⟨h1, h2, h3, hno z ⟨h1, h2, h3, h4, hz0⟩, hz0⟩

/-! ## Right-continuity -/

/-- **The closed order sum is eventually constant to the right.**  Finitely many zeros sit in any
bounded height band, so there is a gap above `T` before the next zero height. -/
theorem boxOrderSumLe_eventuallyConst_right (T : ℝ) :
    ∃ δ > 0, ∀ T' ∈ Set.Ico T (T + δ), boxOrderSumLe T' = boxOrderSumLe T := by
  classical
  set Hgt : Finset ℂ := (boxFinsetLe (T + 1)).filter (fun z => T < z.im) with hHgt
  have hgap : ∃ δ > 0, δ ≤ 1 ∧ ∀ z ∈ Hgt, T + δ ≤ z.im := by
    by_cases hne : (Hgt.image Complex.im).Nonempty
    · set μ : ℝ := (Hgt.image Complex.im).min' hne with hμ
      have hμT : T < μ := by
        obtain ⟨z0, hz0, hz0eq⟩ := Finset.mem_image.mp ((Hgt.image Complex.im).min'_mem hne)
        rw [hHgt, Finset.mem_filter] at hz0
        rw [hμ, ← hz0eq]; exact hz0.2
      refine ⟨min (μ - T) 1, lt_min (by linarith) one_pos, min_le_right _ _, fun z hz => ?_⟩
      have hle : μ ≤ z.im := by
        have := (Hgt.image Complex.im).min'_le z.im (Finset.mem_image_of_mem _ hz)
        rw [← hμ] at this; exact this
      have hmid : T + min (μ - T) 1 ≤ μ := by have := min_le_left (μ - T) 1; linarith
      linarith
    · exact ⟨1, one_pos, le_refl 1, fun z hz => absurd ⟨z.im, Finset.mem_image_of_mem _ hz⟩ hne⟩
  obtain ⟨δ, hδ, hδ1, hgaple⟩ := hgap
  refine ⟨δ, hδ, fun T' hT' => ?_⟩
  obtain ⟨hT'ge, hT'lt⟩ := hT'
  refine (boxOrderSumLe_const_of_no_zeros hT'ge ?_).symm
  intro z hz
  obtain ⟨h1, h2, h3, h4, hz0⟩ := hz
  by_contra hgt
  have hTz : T < z.im := not_le.mp hgt
  have hz1 : z.im ≤ T + 1 := by linarith
  have hzHgt : z ∈ Hgt := by
    rw [hHgt, Finset.mem_filter, mem_boxFinsetLe]
    exact ⟨⟨h1, h2, h3, hz1, hz0⟩, hTz⟩
  have hge := hgaple z hzHgt
  linarith

/-! ## The census profile -/

/-- **The census profile at height `T`**: the closed box order sum reduced mod `2^k`, a
right-continuous `ZMod (2^k)`-valued step function of the height. -/
noncomputable def censusProfile (k : ℕ) (T : ℝ) : ZMod (2 ^ k) := (boxOrderSumLe T : ZMod (2 ^ k))

/-- **Right-continuity of the census profile.**  Into the discrete ring `ZMod (2^k)`, the profile
is continuous within `[T, ∞)` at `T`: it is constant on a right neighbourhood. -/
theorem censusProfile_continuousWithinAt (k : ℕ) (T : ℝ) :
    ContinuousWithinAt (censusProfile k) (Set.Ici T) T := by
  obtain ⟨δ, hδ, hconst⟩ := boxOrderSumLe_eventuallyConst_right T
  have hcont : ContinuousWithinAt (fun _ => censusProfile k T) (Set.Ici T) T :=
    continuousWithinAt_const
  refine hcont.congr_of_eventuallyEq ?_ rfl
  have hmem : Set.Ico T (T + δ) ∈ 𝓝[≥] T := Ico_mem_nhdsGE (by linarith)
  filter_upwards [hmem] with T' hT'
  show censusProfile k T' = censusProfile k T
  rw [censusProfile, censusProfile, hconst T' hT']

/-- The census profile is locally constant off the zero heights. -/
theorem censusProfile_const_of_no_zeros {k : ℕ} {T₁ T₂ : ℝ} (h : T₁ ≤ T₂)
    (hno : ∀ z ∈ boxZerosLe T₂, z.im ≤ T₁) :
    censusProfile k T₁ = censusProfile k T₂ := by
  rw [censusProfile, censusProfile, boxOrderSumLe_const_of_no_zeros h hno]

/-- **The jump of the profile is the jump divisor.**  At a nonnegative height the right-continuous
profile exceeds its left value `discCensusH k T` by exactly `discJump T` mod `2^k`. -/
theorem censusProfile_eq_left_add_discJump {k : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    censusProfile k T = discCensusH k T + (discJump T : ZMod (2 ^ k)) := by
  rw [censusProfile, discCensusH, boxOrderSumLe_eq_add_discJump hT, Nat.cast_add]

/-! ## The reflection-closed strip configuration of the profile -/

/-- Strip ξ-zeros with height at most `T` — reflection-closed, right-half equal to `boxZerosLe`. -/
def stripZerosLe (T : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ 0 ≤ z.im ∧ z.im ≤ T ∧ xi z = 0}

theorem stripZerosLe_finite (T : ℝ) : (stripZerosLe T).Finite := by
  apply (stripZeros_finite (T + 1)).subset
  rintro z ⟨h1, h2, h3, h4, hz⟩
  exact ⟨⟨h1, h2, h3, by linarith⟩, hz⟩

/-- The finite reflection-closed strip configuration up to height `T`. -/
noncomputable def stripFinsetLe (T : ℝ) : Finset ℂ := (stripZerosLe_finite T).toFinset

theorem mem_stripFinsetLe {T : ℝ} {z : ℂ} : z ∈ stripFinsetLe T ↔ z ∈ stripZerosLe T :=
  (stripZerosLe_finite T).mem_toFinset

theorem lineReflect_mem_stripFinsetLe {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetLe T) :
    lineReflect z ∈ stripFinsetLe T := by
  rw [mem_stripFinsetLe] at hz ⊢
  obtain ⟨h1, h2, h3, h4, hz0⟩ := hz
  have him : (lineReflect z).im = z.im := by simp [lineReflect]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lineReflect_re]; linarith
  · rw [lineReflect_re]; linarith
  · rw [him]; exact h3
  · rw [him]; exact h4
  · simp only [lineReflect]; rw [xi_one_sub, xi_conj, hz0, map_zero]

/-- The right half of the strip configuration is the box configuration. -/
theorem stripFinsetLe_filter_right (T : ℝ) :
    (stripFinsetLe T).filter (fun z => 1 / 2 < z.re) = boxFinsetLe T := by
  ext z
  rw [Finset.mem_filter, mem_stripFinsetLe, mem_boxFinsetLe]
  constructor
  · rintro ⟨⟨_, h2, h3, h4, hz0⟩, hre⟩
    exact ⟨hre, h2, h3, h4, hz0⟩
  · rintro ⟨h1, h2, h3, h4, hz0⟩
    exact ⟨⟨by linarith, h2, h3, h4, hz0⟩, h1⟩

/-- The profile is the ξ window census of the reflection-closed strip configuration. -/
theorem censusProfile_eq_windowDiscBit (k : ℕ) (T : ℝ) :
    censusProfile k T
      = windowDiscBit k (stripFinsetLe T) (fun z => (analyticOrderAt xi z).toNat) := by
  rw [censusProfile, windowDiscBit, windowRightSum, stripFinsetLe_filter_right, boxOrderSumLe]

/-! ## (a) The finite-carrier census profile agrees with the ξ profile -/

/-- **Height-indexed transport data.**  A family of reflection-closed `completedGN N`
configurations enclosing each height slice, order-pinned, with the two boundary congruences to the
ξ strip configuration at every height. -/
def TransportedProfile (N k : ℕ) (G : ℝ → Finset ℂ) (mg : ℂ → ℕ) : Prop :=
  ∀ T : ℝ,
    (∀ z ∈ G T, 0 < z.re ∧ z.re < 1) ∧
    (∀ z ∈ G T, (mg z : ℕ∞) = analyticOrderAt (completedGN N) z) ∧
    (∀ z ∈ G T, lineReflect z ∈ G T) ∧
    (∑ z ∈ stripFinsetLe T, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ G T, mg z [MOD 2 ^ (k + 1)]) ∧
    (∑ z ∈ (stripFinsetLe T).filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat
      ≡ ∑ z ∈ (G T).filter (fun z => z.re = 1 / 2), mg z [MOD 2 ^ (k + 1)])

/-- **(a) The finite-carrier census profile equals the ξ profile.**  Given height-indexed
transport data, the ξ census profile agrees, as a function into `ZMod (2^k)`, with the decidable
finite-carrier profile `T ↦ windowDiscBit k (G T) mg`.  Each value on the right is a finite
computation on the finite carrier's window zeros; the equality at every height is exactly the two
transported congruences. -/
theorem censusProfile_eq_finiteCensusProfile {N k : ℕ} {G : ℝ → Finset ℂ} {mg : ℂ → ℕ}
    (hdata : TransportedProfile N k G mg) :
    censusProfile k = fun T => windowDiscBit k (G T) mg := by
  funext T
  obtain ⟨hstrip, hmg, hcl, hD, hL⟩ := hdata T
  rw [censusProfile_eq_windowDiscBit]
  exact windowDiscBit_transport (N := N) k
    (fun z _ => ENat.coe_toNat (xi_order_ne_top z))
    (fun z hz => lineReflect_mem_stripFinsetLe hz)
    hstrip hmg hcl hD hL

/-! ## (b) The divisor difference between the two carriers -/

/-- Strip ξ-zeros at exactly height `t` — reflection-closed (reflection preserves the height),
right-half equal to `boxHeightZeros`. -/
def stripHeightZeros (t : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ z.im = t ∧ xi z = 0}

theorem stripHeightZeros_finite (t : ℝ) : (stripHeightZeros t).Finite := by
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

/-- The finite reflection-closed strip configuration at exactly height `t`. -/
noncomputable def stripHeightFinset (t : ℝ) : Finset ℂ := (stripHeightZeros_finite t).toFinset

theorem mem_stripHeightFinset {t : ℝ} {z : ℂ} : z ∈ stripHeightFinset t ↔ z ∈ stripHeightZeros t :=
  (stripHeightZeros_finite t).mem_toFinset

theorem lineReflect_mem_stripHeightFinset {t : ℝ} {z : ℂ} (hz : z ∈ stripHeightFinset t) :
    lineReflect z ∈ stripHeightFinset t := by
  rw [mem_stripHeightFinset] at hz ⊢
  obtain ⟨h1, h2, him, hz0⟩ := hz
  have himr : (lineReflect z).im = z.im := by simp [lineReflect]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lineReflect_re]; linarith
  · rw [lineReflect_re]; linarith
  · rw [himr]; exact him
  · simp only [lineReflect]; rw [xi_one_sub, xi_conj, hz0, map_zero]

/-- The right half of the height-`t` strip configuration is the box height-`t` zero set, so its ξ
order sum is the jump divisor. -/
theorem windowRightSum_stripHeightFinset (t : ℝ) :
    windowRightSum (stripHeightFinset t) (fun z => (analyticOrderAt xi z).toNat) = discJump t := by
  rw [windowRightSum, discJump]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext z
  rw [Finset.mem_filter, mem_stripHeightFinset, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨_, h2, him, hz0⟩, hre⟩
    exact ⟨hre, h2, him, hz0⟩
  · rintro ⟨h1, h2, him, hz0⟩
    exact ⟨⟨by linarith, h2, him, hz0⟩, h1⟩

/-- The finite carrier's jump at height `t`: the right-half order sum of its height-`t`
configuration. -/
noncomputable def finiteDiscJump (H : ℝ → Finset ℂ) (mg : ℂ → ℕ) (t : ℝ) : ℕ :=
  windowRightSum (H t) mg

/-- **The signed divisor difference** of the two carriers' jump divisors at height `t`. -/
noncomputable def jumpDiff (H : ℝ → Finset ℂ) (mg : ℂ → ℕ) (t : ℝ) : ℤ :=
  (discJump t : ℤ) - (finiteDiscJump H mg t : ℤ)

/-- **Support of the difference.**  Where neither carrier has a zero at height `t`, the divisor
difference vanishes: its support lies in the union of the two carriers' zero-height sets. -/
theorem jumpDiff_eq_zero_of_no_zeros {H : ℝ → Finset ℂ} {mg : ℂ → ℕ} {t : ℝ}
    (hxi : boxHeightZeros t = ∅)
    (hfin : (H t).filter (fun z => 1 / 2 < z.re) = ∅) :
    jumpDiff H mg t = 0 := by
  rw [jumpDiff, finiteDiscJump, windowRightSum, hfin, Finset.sum_empty,
    (discJump_eq_zero_iff t).mpr hxi]
  simp

/-- **(b) The divisor difference is `2^k`-valued.**  For a reflection-closed height-`t` finite
carrier configuration with the two boundary congruences, `2^k` divides the signed jump difference:
the ξ and finite-carrier jump divisors agree mod `2^k`, so their difference is a discrete measure on
the line taking values in `2^k·ℤ`, its `2^k`-classes carrying the transported rung datum. -/
theorem two_pow_dvd_jumpDiff {N k : ℕ} {H : ℝ → Finset ℂ} {mg : ℂ → ℕ} (t : ℝ)
    (hstrip : ∀ z ∈ H t, 0 < z.re ∧ z.re < 1)
    (hmg : ∀ z ∈ H t, (mg z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl : ∀ z ∈ H t, lineReflect z ∈ H t)
    (hD : ∑ z ∈ stripHeightFinset t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ H t, mg z
        [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ (stripHeightFinset t).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt xi z).toNat
        ≡ ∑ z ∈ (H t).filter (fun z => z.re = 1 / 2), mg z [MOD 2 ^ (k + 1)]) :
    (2 ^ k : ℤ) ∣ jumpDiff H mg t := by
  have htrans := windowDiscBit_transport (N := N) k
    (fun z _ => ENat.coe_toNat (xi_order_ne_top z))
    (fun z hz => lineReflect_mem_stripHeightFinset hz)
    hstrip hmg hcl hD hL
  rw [windowDiscBit, windowDiscBit, windowRightSum_stripHeightFinset] at htrans
  have hmod : discJump t ≡ finiteDiscJump H mg t [MOD 2 ^ k] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp htrans
  have hdvd : ((2 ^ k : ℕ) : ℤ) ∣ ((finiteDiscJump H mg t : ℤ) - (discJump t : ℤ)) :=
    (Nat.modEq_iff_dvd).mp hmod
  push_cast at hdvd
  rw [jumpDiff]
  have h2 : (discJump t : ℤ) - (finiteDiscJump H mg t : ℤ)
      = -((finiteDiscJump H mg t : ℤ) - (discJump t : ℤ)) := by ring
  rw [h2]
  exact (dvd_neg).mpr hdvd

end RHTower
