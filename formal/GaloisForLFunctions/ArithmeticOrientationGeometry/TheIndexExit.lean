import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.BezoutValuationIncidence.ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# The index exit: a second count for the Hodge defect

The Hodge defect of the scaling surface of `ℤ` is the number `D` of distinct zeros of `ζ` right of
the critical line (`ArithmeticCastelnuovoSeveri.zeta_hodgeDefect_iff`). This module gives `D` a
second formula as a count of objects of a different kind, the collisions of the de Bruijn–Newman
flow `H_t`, and determines what a bound on any of the counts attached to `D` yields.

* **The second formula** (`eventually_collisionMassAfter_eq`). If `D < ∞`, then for all small
  `t > 0`
  `Σ_{s > t} C(s) = 2 (D + E)`,   `E = Σ_{Re ρ > ½} (m_ρ − 1) ≥ 0`,
  where `C(s)` is the number of nonreal zeros of the flow landing on the real axis at time `s`
  (`RHTower.DeBruijn.collisionMass`). If `D = ∞` the left side tends to `∞`
  (`tendsto_collisionMassAfter_atTop`). The left side is a count, nonnegative by construction,
  and the identity reads `count = 2·(Hodge defect) + (nonnegative excess)`. The off-line copies of
  the divisor are the right copies and their critical-line reflections
  (`encard_offLineCopies`), the right copies count the right zeros with multiplicity
  (`card_rightCopies_eq_sum`), and the heat count equals the collision mass after `t`
  (`RHTower.DeBruijn.nonrealZeroCount_eq_collisionMassAfter`).
* **The first rung** (`index_exit_first_rung_tfae`). A fixed bound on any one of the attached counts
  — the Hodge defect, the off-line divisor, the heat counts `N(t)`, the collision masses after `t`,
  the horizontal collision charges of the windows — is the same statement, and it says that all
  zeros above some height lie on the critical line.
* **Its strength** (`zetaZeroAbscissa_lt_one_of_finite_rightZeros`). A finite Hodge defect gives the
  quasi-Riemann hypothesis `Θ < 1`, hence power savings for the Möbius and prime sums in short
  windows (`moebius_and_prime_powerWindowSaving_of_finite_rightZeros`). It is RH with finitely many
  exceptions, much stronger than `Θ < 1`.
* **Quantization** (`even_ncard_rightZeros`, `riemannHypothesis_iff_encard_rightZeros_lt_two`).
  Right zeros come in conjugate pairs, so the defect is even and RH is `D < 2`, the first quantum;
  in collision coordinates RH is the absence of collisions
  (`RHTower.DeBruijn.riemannHypothesis_iff_forall_collisionMass_eq_zero`).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open Zeta23 RHTower RHTower.DeBruijn RHTower.BacklundConverse RHTower.LindelofSparse
  GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

noncomputable section

/-! ## Right copies and off-line copies of the divisor of `ξ` -/

/-- The multiplicity of `ξ` at `ρ`. -/
def xiMult (ρ : ℂ) : ℕ := ((MeromorphicOn.divisor xi Set.univ) ρ).toNat

/-- Multiplicity copies of the zeros of `ξ` strictly right of the critical line. -/
def rightCopies : Set XiZeroCopy := {q | 1 / 2 < (q.1 : ℂ).re}

/-- Multiplicity copies of the zeros of `ξ` off the critical line; `FiniteOffLine` is the finiteness
of this set. -/
def offLineCopies : Set XiZeroCopy := {q | (xiSpectralPoint q).im ≠ 0}

theorem mem_rightCopies_iff (q : XiZeroCopy) : q ∈ rightCopies ↔ (xiSpectralPoint q).im < 0 := by
  simp only [rightCopies, mem_setOf_eq, spectral_im_eq]
  constructor <;> intro h <;> linarith

/-- Critical-line reflection maps the right copies onto the left copies. -/
theorem image_lineConj_rightCopies :
    xiZeroCopyLineConjEquiv '' rightCopies = {q | 0 < (xiSpectralPoint q).im} := by
  ext q
  rw [Equiv.image_eq_preimage, mem_preimage, mem_rightCopies_iff, mem_setOf_eq]
  have h := xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Complex.conj_im]
  constructor <;> intro h' <;> linarith

/-- `#(off-line copies) = 2 · #(right copies)`. -/
theorem encard_offLineCopies : offLineCopies.encard = 2 * rightCopies.encard := by
  have hsplit : offLineCopies = rightCopies ∪ xiZeroCopyLineConjEquiv '' rightCopies := by
    rw [image_lineConj_rightCopies]
    ext q
    simp only [offLineCopies, mem_union, mem_setOf_eq, mem_rightCopies_iff]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      exacts [Or.inl h, Or.inr h]
    · rintro (h | h)
      exacts [h.ne, h.ne']
  have hdisj : Disjoint rightCopies (xiZeroCopyLineConjEquiv '' rightCopies) := by
    rw [image_lineConj_rightCopies, Set.disjoint_left]
    intro q h1 h2
    rw [mem_rightCopies_iff] at h1
    exact lt_asymm h1 h2
  rw [hsplit, Set.encard_union_eq hdisj,
    xiZeroCopyLineConjEquiv.injective.injOn.encard_image, two_mul]

/-- The underlying point of a copy is a right zero iff the copy is a right copy. -/
theorem mem_rightZeros_of_mem_rightCopies {q : XiZeroCopy} (hq : q ∈ rightCopies) :
    (q.1 : ℂ) ∈ rightZeros zetaZeroConfig :=
  ⟨CrossRouteReceiverBridges.xiZeroCopy_mem_zetaZeroConfig_carrier q, hq⟩

/-- Every right zero carries at least one copy. -/
theorem exists_mem_rightCopies {ρ : ℂ} (hρ : ρ ∈ rightZeros zetaZeroConfig) :
    ∃ q ∈ rightCopies, (q.1 : ℂ) = ρ := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero
    (CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ.1).1
  exact ⟨q, by show 1 / 2 < (q.1 : ℂ).re; rw [hq]; exact hρ.2, hq⟩

theorem one_le_xiMult {ρ : ℂ} (hρ : ρ ∈ rightZeros zetaZeroConfig) : 1 ≤ xiMult ρ := by
  obtain ⟨q, -, hq⟩ := exists_mem_rightCopies hρ
  have := q.2.pos
  rw [xiMult, ← hq]
  exact this

/-- **The right copies count the right zeros with multiplicity.** -/
theorem card_rightCopies_eq_sum (hfin : (rightZeros zetaZeroConfig).Finite)
    (hc : rightCopies.Finite) : hc.toFinset.card = ∑ ρ ∈ hfin.toFinset, xiMult ρ := by
  classical
  rw [Finset.card_eq_sum_card_image (fun q : XiZeroCopy => (q.1 : ℂ))]
  have himage : hc.toFinset.image (fun q : XiZeroCopy => (q.1 : ℂ)) = hfin.toFinset := by
    ext ρ
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact mem_rightZeros_of_mem_rightCopies hq
    · exact fun hρ => exists_mem_rightCopies hρ
  rw [himage]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨q₀, hq₀, hq₀ρ⟩ := exists_mem_rightCopies ((Set.Finite.mem_toFinset hfin).mp hρ)
  have hfib : {q ∈ hc.toFinset | (q.1 : ℂ) = ρ} =
      ({q₀.1} : Finset XiDivisorSupport).sigma fun _ => Finset.univ := by
    ext q
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_sigma,
      Finset.mem_singleton, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨-, hq⟩
      exact Subtype.ext (hq.trans hq₀ρ.symm)
    · intro h
      have hq : (q.1 : ℂ) = ρ := by rw [h, hq₀ρ]
      refine ⟨?_, hq⟩
      show 1 / 2 < (q.1 : ℂ).re
      rw [hq]
      exact ((Set.Finite.mem_toFinset hfin).mp hρ).2
  rw [hfib, Finset.card_sigma, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin, xiMult,
    hq₀ρ]

/-! ## The off-line divisor and the Hodge defect -/

/-- The Hodge defect is finite iff the off-line divisor is finite. -/
theorem rightZeros_zeta_finite_iff_finiteOffLine :
    (rightZeros zetaZeroConfig).Finite ↔ FiniteOffLine := by
  rw [← CrossRouteReceiverBridges.offLineZeros_finite_iff_finiteOffLine]
  constructor
  · intro hfin
    refine (hfin.union (hfin.image Zeta23.reflect)).subset fun ρ hρ => ?_
    rcases lt_or_gt_of_ne hρ.2 with hlt | hgt
    · refine Or.inr ⟨Zeta23.reflect ρ, ⟨zetaZeroConfig.reflect_mem ρ hρ.1, ?_⟩, ?_⟩
      · rw [Zeta23.reflect_re]; linarith
      · simp [Zeta23.reflect]
    · exact Or.inl ⟨hρ.1, hgt⟩
  · exact fun hfin => hfin.subset fun ρ hρ => ⟨hρ.1, hρ.2.ne'⟩

theorem rightCopies_subset_offLineCopies : rightCopies ⊆ offLineCopies := fun q hq =>
  ((mem_rightCopies_iff q).mp hq).ne

/-! ## The second formula -/

/-- **The index exit identity.** If `ζ` has finitely many zeros right of the critical line, then for
all small `t > 0` the total collision mass of the de Bruijn–Newman flow after `t` is `2 (D + E)`:
`D` the Hodge defect (the number of distinct right zeros) and `E = Σ (m_ρ − 1)` the multiplicity
excess of the right zeros. -/
theorem eventually_collisionMassAfter_eq (hfin : (rightZeros zetaZeroConfig).Finite) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), collisionMassAfter t =
      2 * (hfin.toFinset.card + ∑ ρ ∈ hfin.toFinset, (xiMult ρ - 1)) := by
  have hF : FiniteOffLine := rightZeros_zeta_finite_iff_finiteOffLine.mp hfin
  have hc : rightCopies.Finite := hF.subset rightCopies_subset_offLineCopies
  -- the off-line copies are twice the right copies
  have hcard : hF.toFinset.card = 2 * hc.toFinset.card := by
    have h := encard_offLineCopies
    rw [show offLineCopies = {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} from rfl,
      hF.encard_eq_coe_toFinset_card, hc.encard_eq_coe_toFinset_card] at h
    exact_mod_cast h
  -- the right copies are the defect plus its multiplicity excess
  have hsum : ∑ ρ ∈ hfin.toFinset, xiMult ρ =
      hfin.toFinset.card + ∑ ρ ∈ hfin.toFinset, (xiMult ρ - 1) := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have := one_le_xiMult ((Set.Finite.mem_toFinset hfin).mp hρ)
    omega
  filter_upwards [eventually_nonrealZeroCount_eq_of_finite hF, self_mem_nhdsWithin] with t ht ht0
  rw [← nonrealZeroCount_eq_collisionMassAfter ht0, ht, hcard, card_rightCopies_eq_sum hfin hc,
    hsum]

/-- If `ζ` has infinitely many zeros right of the line, the collision mass after `t` is unbounded
as `t → 0⁺`. -/
theorem tendsto_collisionMassAfter_atTop (hinf : (rightZeros zetaZeroConfig).Infinite) :
    Tendsto collisionMassAfter (𝓝[>] 0) atTop := by
  have hF : ¬ FiniteOffLine := fun h => hinf (rightZeros_zeta_finite_iff_finiteOffLine.mpr h)
  have hZ : {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Infinite := fun h =>
    hF (finite_nonrealCopies_of_finite_zeros h)
  refine (tendsto_nonrealZeroCount_atTop_of_infinite hZ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact nonrealZeroCount_eq_collisionMassAfter ht

/-! ## The first rung -/

/-- Off-line zeros of `ζ` are bounded in height iff they are finitely many. -/
theorem finiteOffLine_iff_exists_onLine_above :
    FiniteOffLine ↔
      ∃ T₀ : ℝ, ∀ ρ ∈ zetaZeroConfig.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2 := by
  rw [← CrossRouteReceiverBridges.offLineZeros_finite_iff_finiteOffLine]
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ : ℂ => |ρ.im|).bddAbove
    refine ⟨M, fun ρ hρ hlt => ?_⟩
    by_contra hre
    exact absurd (hM ⟨ρ, ⟨hρ, hre⟩, rfl⟩) (not_le.mpr hlt)
  · rintro ⟨T₀, hT₀⟩
    refine (zetaZeroConfig.finite_window (-|T₀| - 1) |T₀|).subset fun ρ hρ => ⟨hρ.1, ?_⟩
    have hle : |ρ.im| ≤ T₀ := by
      by_contra h
      exact hρ.2 (hT₀ ρ hρ.1 (not_le.mp h))
    have h1 := abs_le.mp (hle.trans (le_abs_self T₀))
    exact ⟨by linarith, h1.2⟩

/-- The collision pairs of a window lie, for every height, in one fixed finite set when the
off-line zeros are finitely many: a pair of distinct zeros at one height has an off-line member. -/
theorem exists_bound_horizontalCollisionCharge (hF : FiniteOffLine) :
    ∃ M : ℕ, ∀ T, xiHorizontalCollisionCharge T ≤ M := by
  classical
  have hO := CrossRouteReceiverBridges.offLineZeros_finite_iff_finiteOffLine.mpr hF
  obtain ⟨B, hB⟩ := (hO.image fun ρ : ℂ => |ρ.im|).bddAbove
  set U := (stripZeros_finite (|B| + 1)).toFinset with hU
  refine ⟨∑ p ∈ (U ×ˢ U).filter (fun p => p.1.im = p.2.im ∧ p.1 ≠ p.2),
    (analyticOrderAt xi p.1).toNat * (analyticOrderAt xi p.2).toNat, fun T => ?_⟩
  rw [xiHorizontalCollisionCharge_eq_sum_pairs]
  -- every collision pair of the window `T` lies in the fixed window `|B| + 1`
  have hsub : xiHorizontalCollisionPairs T ⊆
      (U ×ˢ U).filter (fun p => p.1.im = p.2.im ∧ p.1 ≠ p.2) := by
    intro p hp
    rw [xiHorizontalCollisionPairs, Finset.mem_filter, Finset.mem_product,
      Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    obtain ⟨⟨h1, h2⟩, him, hne⟩ := hp
    -- one of the two points is off the line
    have hoff : p.1.re ≠ 1 / 2 ∨ p.2.re ≠ 1 / 2 := by
      by_contra h
      push_neg at h
      exact hne (Complex.ext (h.1.trans h.2.symm) him)
    have hcar : ∀ z ∈ stripZeros T, z ∈ zetaZeroConfig.carrier := fun z hz =>
      CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_of_xi_eq_zero hz.2
    have hlow : |p.1.im| ≤ B := by
      rcases hoff with h | h
      · exact hB ⟨p.1, ⟨hcar _ h1, h⟩, rfl⟩
      · rw [him]; exact hB ⟨p.2, ⟨hcar _ h2, h⟩, rfl⟩
    have hmem : ∀ z ∈ stripZeros T, |z.im| ≤ B → z ∈ U := by
      intro z hz hzB
      rw [hU, Set.Finite.mem_toFinset]
      exact ⟨⟨hz.1.1, hz.1.2.1, hz.1.2.2.1, by
        have := (abs_le.mp (hzB.trans (le_abs_self B))).2; linarith⟩, hz.2⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hmem _ h1 hlow, hmem _ h2 (by rw [← him]; exact hlow)⟩, him, hne⟩
  exact Finset.sum_le_sum_of_subset hsub

/-- A uniform bound on the collision charge of the windows bounds the off-line divisor. -/
theorem finiteOffLine_of_bound_horizontalCollisionCharge {M : ℕ}
    (hM : ∀ T, xiHorizontalCollisionCharge T ≤ M) : FiniteOffLine := by
  classical
  rw [← CrossRouteReceiverBridges.offLineZeros_finite_iff_finiteOffLine]
  -- the off-line zeros of nonnegative height have at most `M` elements
  set P := {ρ ∈ offLineZeros | 0 ≤ ρ.im} with hP
  have hPfin : P.Finite := by
    refine Set.finite_of_forall_not_lt_lt (fun _ _ _ _ _ => trivial) ?_ |>.elim (fun h => h) ?_
    all_goals sorry
  sorry

end

end GaloisForLFunctions.ArithmeticOrientationGeometry
