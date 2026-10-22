import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AsymptoticNodeReadingsCannotResolveNodePositivity

/-!
# The node face has a unit, and it is a reciprocal prime power

The node face was the one face of the programme whose entry was pure vacuity: no density resolves
node positivity, but with no number attached. The number is supplied here, and it turns out to be
the same `½` that the aperture, height and parity faces produce — appearing for a completely
different reason.

The **node scale** of a node set is the largest reciprocal of a prime power it omits,
`nodeScale 𝒩 = sup {1/m : m a prime power, m ∉ 𝒩}`. It lies in `[0, ½]`
(`nodeScale_le_half`) because the smallest prime power is `2`, and:

* `nodeScale_eq_zero_iff` — it vanishes exactly when `𝒩` contains every prime power;
* `nodeScale_eq_zero_of_zeroPoleBlindPositiveOn` — node positivity *forces* it to vanish,
  unconditionally: a node set missing one prime power is never positive. So `nodeScale = 0` is a
  necessary condition for the node face, as `width = 0` is for the aperture face;
* `resolutionLimit_nodeScale_asymptoticReading` — and every asymptotic reading has resolution limit
  exactly `½` for it. Deleting the single node `2` is a finite modification, invisible to every
  density, and it moves the node scale from `0` to its maximum.

So the node face's floor is `(the smallest prime power)⁻¹`. The incidence structure of the integers
fixes the number: it is `½` because `2` is the first prime power, exactly as the aperture floor is
`½` because `½` is the deepest an off-line zero can sit. The programme's recurring `½` has two
independent arithmetic sources, and this is the second.
-/

open Set

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open GaloisForLFunctions.BiScaleUncertainty

set_option autoImplicit false

/-! ### 1. The node scale -/

/-- The prime powers a node set omits. -/
def missingPrimePowers (𝒩 : Set ℕ) : Set ℕ := {m : ℕ | IsPrimePow m ∧ m ∉ 𝒩}

/-- The **node scale**: the largest reciprocal prime power the node set omits. It is `0` for a set
carrying every prime power and `½` for one missing the node `2`. -/
noncomputable def nodeScale (𝒩 : Set ℕ) : ℝ :=
  sSup ((fun m : ℕ => ((m : ℝ))⁻¹) '' missingPrimePowers 𝒩)

theorem bddAbove_nodeScale_image (𝒩 : Set ℕ) :
    BddAbove ((fun m : ℕ => ((m : ℝ))⁻¹) '' missingPrimePowers 𝒩) := by
  refine ⟨1 / 2, ?_⟩
  rintro x ⟨m, ⟨hm, -⟩, rfl⟩
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.two_le
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le two_pos h2
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
    inv_le_inv₀ hm0 (by norm_num : (0 : ℝ) < 2)]
  exact h2

theorem nodeScale_le_half (𝒩 : Set ℕ) : nodeScale 𝒩 ≤ 1 / 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro x ⟨m, ⟨hm, -⟩, rfl⟩
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.two_le
  have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le two_pos h2
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
    inv_le_inv₀ hm0 (by norm_num : (0 : ℝ) < 2)]
  exact h2

theorem nodeScale_nonneg (𝒩 : Set ℕ) : 0 ≤ nodeScale 𝒩 := by
  rcases Set.eq_empty_or_nonempty (missingPrimePowers 𝒩) with h | ⟨m, hm⟩
  · unfold nodeScale
    rw [h, Set.image_empty, Real.sSup_empty]
  · have hpos : (0 : ℝ) < ((m : ℝ))⁻¹ := by
      have : (0 : ℝ) < (m : ℝ) := by
        have := hm.1.two_le
        exact_mod_cast lt_of_lt_of_le two_pos this
      positivity
    exact hpos.le.trans (le_csSup (bddAbove_nodeScale_image 𝒩) ⟨m, hm, rfl⟩)

/-- **The node scale vanishes exactly on the sets carrying every prime power.** -/
theorem nodeScale_eq_zero_iff (𝒩 : Set ℕ) :
    nodeScale 𝒩 = 0 ↔ ∀ m : ℕ, IsPrimePow m → m ∈ 𝒩 := by
  refine ⟨fun h m hm => ?_, fun h => ?_⟩
  · by_contra hmem
    have hpos : (0 : ℝ) < ((m : ℝ))⁻¹ := by
      have : (0 : ℝ) < (m : ℝ) := by
        have := hm.two_le
        exact_mod_cast lt_of_lt_of_le two_pos this
      positivity
    have hle : ((m : ℝ))⁻¹ ≤ nodeScale 𝒩 :=
      le_csSup (bddAbove_nodeScale_image 𝒩) ⟨m, ⟨hm, hmem⟩, rfl⟩
    rw [h] at hle
    exact absurd hle (not_le.mpr hpos)
  · have hempty : missingPrimePowers 𝒩 = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun m hm => hm.2 (h m hm.1)
    unfold nodeScale
    rw [hempty, Set.image_empty, Real.sSup_empty]

/-! ### 2. The node scale of the extremal sets -/

theorem nodeScale_primePowers : nodeScale {n : ℕ | IsPrimePow n} = 0 :=
  (nodeScale_eq_zero_iff _).mpr fun _ hm => hm

/-- Deleting the node `2` moves the node scale to its maximum. -/
theorem nodeScale_deleteNode_two : nodeScale (deleteNode 2 {n : ℕ | IsPrimePow n}) = 1 / 2 := by
  have hset : missingPrimePowers (deleteNode 2 {n : ℕ | IsPrimePow n}) = {2} := by
    ext m
    simp only [missingPrimePowers, deleteNode, mem_setOf_eq, Set.mem_sdiff,
      Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h => h.2 h.1, fun h => ⟨by subst h; decide, fun _ => h⟩⟩
  unfold nodeScale
  rw [hset, Set.image_singleton]
  norm_num

/-! ### 3. Node positivity forces the scale to vanish -/

/-- **Necessity of a vanishing node scale.** A node set missing one prime power is never
zero-pole positive, so node positivity forces every prime power to be present. -/
theorem nodeScale_eq_zero_of_zeroPoleBlindPositiveOn {𝒩 : Set ℕ}
    (h : ZeroPoleBlindPositiveOn 𝒩) : nodeScale 𝒩 = 0 := by
  refine (nodeScale_eq_zero_iff 𝒩).mpr fun m hm => ?_
  by_contra hmem
  have hdiff : deleteNode m 𝒩 = 𝒩 := by
    simp only [deleteNode]
    exact Set.sdiff_singleton_eq_self hmem
  exact not_zeroPoleBlindPositiveOn_deleteNode hm 𝒩 (by rw [hdiff]; exact h)

/-! ### 4. The unit of the node face -/

/-- **The node face floor.** Every asymptotic reading — every density, counting function, sieve
level — has resolution limit exactly `½` for the node scale: the reciprocal of the smallest prime
power. The node face now has a number, and it is the trivial bound in its own unit. -/
theorem resolutionLimit_nodeScale_asymptoticReading {O : Type*} {r : Set ℕ → O}
    (h : AsymptoticReading r) :
    resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 := by
  have hbdd : BddAbove (nodeScale '' shadow r {n : ℕ | IsPrimePow n}) :=
    ⟨1 / 2, by rintro x ⟨𝒩, -, rfl⟩; exact nodeScale_le_half 𝒩⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty nodeScale r _) ?_) ?_
  · rintro x ⟨𝒩, -, rfl⟩
    exact nodeScale_le_half 𝒩
  · have hmem : deleteNode 2 {n : ℕ | IsPrimePow n} ∈ shadow r {n : ℕ | IsPrimePow n} :=
      invisible_deleteNode_of_asymptoticReading h 2 _
    exact nodeScale_deleteNode_two ▸ le_csSup hbdd ⟨_, hmem, rfl⟩

/-- An asymptotic reading certifies the bound `β` on the node scale exactly when `β ≥ ½`. -/
theorem certifies_nodeScale_asymptoticReading_iff {O : Type*} {r : Set ℕ → O}
    (h : AsymptoticReading r) {β : ℝ} :
    Certifies nodeScale r {n : ℕ | IsPrimePow n} β ↔ 1 / 2 ≤ β := by
  rw [certifies_iff_resolutionLimit_le
      ⟨1 / 2, by rintro x ⟨𝒩, -, rfl⟩; exact nodeScale_le_half 𝒩⟩,
    resolutionLimit_nodeScale_asymptoticReading h]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
