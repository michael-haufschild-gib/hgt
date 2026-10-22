import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureCertificateIsBlindInEveryUnit
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerZeroPoleNodeCriticality
import GaloisForLFunctions.SquareRootThreshold.FiniteOffLineSetsAreVisible

/-!
# Refutation is finite, confirmation is not

The field's two directions are not symmetric, and this module measures the asymmetry.

*Confirmation* of criticality is an infinite demand. The incidence condition must hold at every
prime power: omitting a single one destroys positivity
(`not_zeroPoleBlindPositiveOn_deleteNode`), so the prime powers are the least positive node set
(`isLeast_zeroPoleBlindPositiveOn`), and no asymptotic node reading certifies anything about that
face beyond the trivial bound (`resolutionLimit_nodeScale_asymptoticReading`) — deleting one node is
invisible to such a reading, so it cannot see the one bit that decides the face.

*Refutation* is finite, and complete. `Refutes` records what a reading rules out, and on the prime
side the calculus is exactly complete: a certificate of radius beyond a failure aperture refutes the
cone (`refutes_radiusReading`), and RH holds precisely when no bounded-radius certificate refutes
membership of the von Mangoldt weight in the full Weil cone
(`riemannHypothesis_iff_no_radiusReading_refutes`). On the node face a single membership bit
refutes (`membershipReading`), and a configuration with a finite off-line set is refuted at an
explicit aperture computed from that set.

The practical reading: a mechanism that fails is told so by a finite computation — one radius, one
aperture, or one bit — while a mechanism that succeeds must succeed everywhere at once. Any search
for a counterexample is effective; any proof of criticality must be uniform.
-/

open GaloisForLFunctions.BiScaleUncertainty
open Set
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 0. The prime-side reading -/

/-- A test of aperture `R`: twice differentiable with support in `[-R, R]`. -/
def ApertureTest (R : ℝ) : Type := {f : ℝ → ℂ // ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-R) R}

/-- The certificate of radius `R`: the full Weil functional of the weight on every test of that
aperture. -/
noncomputable def radiusReading (R : ℝ) (lam : ℕ → ℝ) : ApertureTest R → ℂ :=
  fun t => weilFullFunctional lam (EF.weilTest t.1 t.1)

/-- Positivity of the full Weil functional of a prime weight on tests of aperture `a`. -/
def weightAperturePositivity (a : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

theorem weightAperturePositivity_mono {a b : ℝ} (hab : a ≤ b) {lam : ℕ → ℝ}
    (h : weightAperturePositivity b lam) : weightAperturePositivity a lam :=
  fun f hf hfs => h f hf (hfs.trans (Icc_subset_Icc (by linarith) hab))

-- from AsymptoticNodeReadingsCannotResolveNodePositivity.lean
variable {O : Type*}

/-! ### 1. The node collapse -/

/-- The node collapse: delete the node `m`. -/
def deleteNode (m : ℕ) (𝒩 : Set ℕ) : Set ℕ := 𝒩 \ {m}

/-- Deleting one node is a finite modification of the node set. -/
theorem deleteNode_symmDiff_subset (m : ℕ) (𝒩 : Set ℕ) :
    deleteNode m 𝒩 \ 𝒩 ∪ 𝒩 \ deleteNode m 𝒩 ⊆ {m} := by
  intro x hx
  rcases hx with hx | hx
  · exact absurd hx.1.1 hx.2
  · by_contra hxm
    exact hx.2 ⟨hx.1, hxm⟩

/-- **Prime-power deletion is uniformly fatal**: on every node set, deleting one prime power
destroys zero-pole positivity. -/
theorem not_zeroPoleBlindPositiveOn_deleteNode {m : ℕ} (hm : IsPrimePow m) (𝒩 : Set ℕ) :
    ¬ ZeroPoleBlindPositiveOn (deleteNode m 𝒩) :=
  not_zeroPoleBlindPositiveOn_diff_of_isPrimePow 𝒩 hm

/-- **Non-prime-power deletion is invisible to the sharpest reading there is**, the property
itself: `log 6` and all composite nodes are redundant. -/
theorem invisible_zeroPoleBlindPositiveOn_deleteNode {n : ℕ} (hn : ¬ IsPrimePow n) :
    Invisible ZeroPoleBlindPositiveOn (deleteNode n) := fun 𝒩 =>
  propext (zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow 𝒩 hn)

/-! ### 2. The node gate -/

/-- **The node gate.** A reading of node sets that is blind to the deletion of a single prime
power resolves zero-pole positivity only when RH fails. -/
theorem not_riemannHypothesis_of_resolves_of_invisible {r : Set ℕ → O} {m : ℕ}
    (hm : IsPrimePow m) (hres : Resolves r ZeroPoleBlindPositiveOn)
    (hinv : Invisible r (deleteNode m)) : ¬ RiemannHypothesis := fun hRH =>
  forall_not_of_resolves_of_invisible hres hinv (not_zeroPoleBlindPositiveOn_deleteNode hm)
    {n | IsPrimePow n} (riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH)

/-- A reading is *asymptotic* when finitely many nodes never change it: densities, asymptotic
counting functions, sieve levels, zero-density exponents. -/
def AsymptoticReading (r : Set ℕ → O) : Prop :=
  ∀ 𝒩 ℳ : Set ℕ, (𝒩 \ ℳ ∪ ℳ \ 𝒩).Finite → r 𝒩 = r ℳ

theorem invisible_deleteNode_of_asymptoticReading {r : Set ℕ → O} (h : AsymptoticReading r)
    (m : ℕ) : Invisible r (deleteNode m) := fun 𝒩 =>
  h _ _ ((Set.finite_singleton m).subset (deleteNode_symmDiff_subset m 𝒩))

/-- **No asymptotic reading resolves node positivity** (unless RH fails). Every density-level
argument about the node set is excluded in one step, because positivity is an incidence
condition on single prime powers. -/
theorem not_resolves_of_asymptoticReading {r : Set ℕ → O} (h : AsymptoticReading r)
    (hRH : RiemannHypothesis) : ¬ Resolves r ZeroPoleBlindPositiveOn := fun hres =>
  not_riemannHypothesis_of_resolves_of_invisible (by decide : IsPrimePow 4) hres
    (invisible_deleteNode_of_asymptoticReading h 4) hRH

/-- Under RH a resolving reading must move every prime-power deletion: the reading has to charge
the node `log p^k` itself. -/
theorem exists_deleteNode_reading_ne (hRH : RiemannHypothesis) {r : Set ℕ → O} {m : ℕ}
    (hm : IsPrimePow m) (hres : Resolves r ZeroPoleBlindPositiveOn) :
    ∃ 𝒩 : Set ℕ, r (deleteNode m 𝒩) ≠ r 𝒩 := by
  by_contra h
  push Not at h
  exact not_riemannHypothesis_of_resolves_of_invisible hm hres (fun 𝒩 => h 𝒩) hRH

/-! ### 3. The fatal collapses are exactly the prime powers -/

/-- **The gate is incidence, not density.** Deletion of `m` is fatal on every node set exactly
when `m` is a prime power. -/
theorem fatal_deleteNode_iff_isPrimePow (hRH : RiemannHypothesis) (m : ℕ) :
    (∀ 𝒩 : Set ℕ, ¬ ZeroPoleBlindPositiveOn (deleteNode m 𝒩)) ↔ IsPrimePow m := by
  refine ⟨fun h => ?_, fun hm => not_zeroPoleBlindPositiveOn_deleteNode hm⟩
  by_contra hm
  refine h {n | IsPrimePow n} ?_
  rw [invisible_zeroPoleBlindPositiveOn_deleteNode hm {n | IsPrimePow n}]
  exact riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH

-- from TheNodeFaceUnitIsAReciprocalPrimePower.lean
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

-- from ThePrimePowersAreTheLeastPositiveNodeSet.lean
/-! ### 1. Positivity is monotone in the node set -/

/-- **Monotonicity.** Blindness on more nodes is a stronger constraint on the admissible
combinations, so a larger node set is easier to be positive on. -/
theorem zeroPoleBlindPositiveOn_mono {𝒩 ℳ : Set ℕ} (h : ZeroPoleBlindPositiveOn 𝒩)
    (hsub : 𝒩 ⊆ ℳ) : ZeroPoleBlindPositiveOn ℳ :=
  fun c hc hblind hmass => h c hc (fun j hj => hblind j (hsub hj)) hmass

/-! ### 2. The classification -/

/-- **Classification of the positive node sets.** Under RH a node set is zero-pole positive exactly
when it carries every prime power. -/
theorem zeroPoleBlindPositiveOn_iff_primePowers_subset (hRH : RiemannHypothesis) (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔ ∀ m : ℕ, IsPrimePow m → m ∈ 𝒩 := by
  refine ⟨fun h m hm => (nodeScale_eq_zero_iff 𝒩).mp
      (nodeScale_eq_zero_of_zeroPoleBlindPositiveOn h) m hm, fun h => ?_⟩
  exact zeroPoleBlindPositiveOn_mono
    (riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH) h

/-- **The prime powers are the least positive node set.** -/
theorem isLeast_zeroPoleBlindPositiveOn (hRH : RiemannHypothesis) :
    IsLeast {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} {n : ℕ | IsPrimePow n} := by
  refine ⟨riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mp hRH, ?_⟩
  intro 𝒩 h𝒩
  exact fun m hm => (zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩).mp h𝒩 m hm

/-- The positive node sets form a principal up-set. -/
theorem zeroPoleBlindPositiveOn_setOf_eq (hRH : RiemannHypothesis) :
    {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} = {𝒩 : Set ℕ | {n : ℕ | IsPrimePow n} ⊆ 𝒩} := by
  ext 𝒩
  exact zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩

/-! ### 3. The node unit is faithful -/

/-- **The node unit decides the node face.** Under RH, zero-pole positivity is exactly the
vanishing of the node scale. -/
theorem zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero (hRH : RiemannHypothesis) (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔ nodeScale 𝒩 = 0 := by
  rw [zeroPoleBlindPositiveOn_iff_primePowers_subset hRH, nodeScale_eq_zero_iff]

/-- **Transport between the two descriptions of the face.** A reading decides node positivity
exactly when it decides the vanishing of the node scale, so every floor in the node unit is a floor
for the criterion. -/
theorem resolves_nodeScale_iff_resolves_zeroPoleBlindPositiveOn (hRH : RiemannHypothesis)
    {O : Type*} (r : Set ℕ → O) :
    Resolves r (fun 𝒩 => nodeScale 𝒩 = 0) ↔ Resolves r ZeroPoleBlindPositiveOn := by
  constructor <;> intro h 𝒩 ℳ hmem
  · show ZeroPoleBlindPositiveOn ℳ ↔ ZeroPoleBlindPositiveOn 𝒩
    rw [zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
      zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH]
    exact h 𝒩 ℳ hmem
  · show nodeScale ℳ = 0 ↔ nodeScale 𝒩 = 0
    rw [← zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
      ← zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH]
    exact h 𝒩 ℳ hmem

/-- **The node face in one statement.** Under RH: the positive node sets are the supersets of the
prime powers, that set is least among them, positivity is the vanishing of the node unit, and no
asymptotic reading certifies anything about that unit beyond the trivial `½`. -/
theorem theNodeFaceIsAPrincipalUpSet (hRH : RiemannHypothesis) :
    IsLeast {𝒩 : Set ℕ | ZeroPoleBlindPositiveOn 𝒩} {n : ℕ | IsPrimePow n} ∧
      (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn 𝒩 ↔ nodeScale 𝒩 = 0) ∧
      ∀ (O : Type) (r : Set ℕ → O), AsymptoticReading r →
        resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  ⟨isLeast_zeroPoleBlindPositiveOn hRH, zeroPoleBlindPositiveOn_iff_nodeScale_eq_zero hRH,
    fun _ _ h => resolutionLimit_nodeScale_asymptoticReading h⟩

-- from RefutationIsFiniteConfirmationIsNot.lean
/-! ### 1. A truncated divisor pins the zeros below its height -/

/-! ### 2. The asymmetry -/

/-! ### 3. Refutation is complete -/

-- from TheRefutationCalculusIsCompleteOnBothFaces.lean
variable {D O O' : Type*}

/-! ### 1. Refutation -/

/-- A reading **refutes** `P` at `d` when nothing it admits satisfies `P`. -/
def Refutes (r : D → O) (P : D → Prop) (d : D) : Prop := ∀ e ∈ shadow r d, ¬ P e

theorem not_of_refutes {r : D → O} {P : D → Prop} {d : D} (h : Refutes r P d) : ¬ P d :=
  h d (mem_shadow_self r d)

/-- A finer reading refutes whatever a coarser one refutes. -/
theorem Refutes.of_refines {r : D → O} {r' : D → O'} {P : D → Prop} {d : D}
    (href : Refines r r') (h : Refutes r' P d) : Refutes r P d := fun e he => h e (href d e he)

/-! ### 2. The zero side refutes completely -/

/-! ### 3. The prime side refutes completely -/

/-- **A certificate of radius beyond a failure aperture refutes the cone.** -/
theorem refutes_radiusReading {R : ℝ} {lam : ℕ → ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-R) R)
    (hneg : (weilFullFunctional lam (EF.weilTest f f)).re < 0) :
    Refutes (radiusReading R) WeilPositiveFull lam := by
  intro lam' hlam' hpos
  have hval : weilFullFunctional lam' (EF.weilTest f f) =
      weilFullFunctional lam (EF.weilTest f f) :=
    congrFun (mem_shadow_iff.mp hlam') ⟨f, hf, hfs⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have := hpos f hf hfc
  rw [hval] at this
  linarith

/-- **Completeness on the prime side.** RH holds exactly when no bounded-radius certificate refutes
membership of the von Mangoldt weight in the full Weil cone. -/
theorem riemannHypothesis_iff_no_radiusReading_refutes :
    RiemannHypothesis ↔
      ¬ ∃ R : ℝ, Refutes (radiusReading R)
        WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  refine ⟨fun hRH ⟨R, href⟩ => not_of_refutes href
      (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
        ⟨hRH, fun _ _ => rfl⟩), fun h => ?_⟩
  by_contra hRH
  have hnot : ¬ WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := fun hW =>
    hRH (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW).1
  obtain ⟨a, ha, hfail⟩ : ∃ a : ℝ, 0 < a ∧
      ¬ weightAperturePositivity a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
    by_contra hcon
    push Not at hcon
    refine hnot fun f hf hfc => ?_
    obtain ⟨b, hb, hsub⟩ := exists_aperture_of_hasCompactSupport hfc
    exact hcon b hb f hf hsub
  obtain ⟨f, hf, hfs, hneg⟩ : ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re < 0 := by
    by_contra hcon
    push Not at hcon
    exact hfail fun f hf hfs => by
      have := hcon f hf hfs
      linarith
  exact h ⟨a, refutes_radiusReading hf hfs hneg⟩

/-! ### 4. The calculus -/

-- from FiniteOffLineSetsAreRefutedAtAnExplicitAperture.lean
/-! ### 1. A failing certificate refutes -/

/-- **A certificate that fails refutes the critical line.** Width zero implies positivity at every
aperture, so nothing in the shadow of a failing certificate lies on the line. -/
theorem refutes_of_not_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : ¬ aperturePositivity a Z) :
    Refutes (aperturePositivity a) (fun W => width W = 0) Z := by
  intro W hW hw
  have hposW : aperturePositivity a W := fun f hf hfs =>
    (configWidth_eq_zero_iff_weil_nonneg W.2).mp hw f hf
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs))
  exact hZ ((mem_shadow_iff.mp hW) ▸ hposW)

/-! ### 2. Finite off-line sets fail at an explicit aperture -/

/-- **Beyond the visibility bound a finite off-line set is refuted.** -/
theorem refutes_aperturePositivity_of_finiteOffLine {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ Z : ZeroConfig, ∀ hZ : TemperedConfig Z,
      (∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) → (∀ t ∈ T, Z.mult t = m t) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (modScaledBump w t₀.im) +
          4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (m t) t‖) / c)) +
          (T.card + 2) * ℓ / 2 + w ≤ a →
        Refutes (aperturePositivity a) (fun W => width W = 0) ⟨Z, hZ⟩ := by
  obtain ⟨c, ℓ, hc, hℓ, hmain⟩ := finiteOffLine_visible m ht₀ hg hgD hgap hw
  refine ⟨c, ℓ, hc, hℓ, fun Z hZ hT hm a ha => refutes_of_not_aperturePositivity ?_⟩
  obtain ⟨f, hf, hfs, hneg⟩ := hmain Z hZ hT hm a ha
  exact fun hpos => absurd (hpos f hf hfs) (not_le.mpr hneg)

/-- **A finite nonempty off-line set is caught at a finite aperture.** -/
theorem not_fullPositivity_of_finiteOffLine {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) (hm : ∀ t ∈ T, Z.mult t = m t) :
    ¬ fullPositivity ⟨Z, hZ⟩ := by
  obtain ⟨c, ℓ, hc, hℓ, hmain⟩ := finiteOffLine_visible m ht₀ hg hgD hgap hw
  set A : ℝ := 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (modScaledBump w t₀.im) +
      4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (m t) t‖) / c)) +
      (T.card + 2) * ℓ / 2 + w with hA
  obtain ⟨f, hf, hfs, hneg⟩ := hmain Z hZ hT hm A le_rfl
  intro hfull
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  exact absurd (hfull f hf hfc) (not_le.mpr hneg)

/-! ### 3. The floors need an infinite off-line set -/

/-- **The floors need infinitely many off-line zeros.** A configuration positive at every aperture
cannot have a finite nonempty off-line set, so the witnesses behind the trivial floors — depth-`½`
lattices and their dilutions — carry infinitely many off-line zeros by necessity. Against a finite
exceptional set the bounded certificate refutes, at the explicit aperture of the visibility law. -/
theorem theFloorsNeedInfinitelyManyOffLineZeros {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) (hm : ∀ t ∈ T, Z.mult t = m t) :
    ¬ fullPositivity ⟨Z, hZ⟩ ∧
      ∀ {a : ℝ}, ¬ aperturePositivity a ⟨Z, hZ⟩ →
        Refutes (aperturePositivity a) (fun W => width W = 0) ⟨Z, hZ⟩ :=
  ⟨not_fullPositivity_of_finiteOffLine m ht₀ hg hgD hgap hw Z hZ hT hm,
    fun hfail => refutes_of_not_aperturePositivity hfail⟩

-- from TheNodeFaceRefutesFromOneBit.lean
/-! ### 1. One bit of membership -/

/-- The one-bit reading: whether the prime power `m` is a node. -/
def membershipReading (m : ℕ) (𝒩 : Set ℕ) : Prop := m ∈ 𝒩

/-- **One bit refutes.** A node set missing a prime power is refuted by that bit alone. -/
theorem refutes_membershipReading_of_notMem {m : ℕ} (hm : IsPrimePow m) {𝒩 : Set ℕ}
    (hmem : m ∉ 𝒩) : Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩 := by
  intro ℳ hℳ hpos
  have hmemℳ : m ∉ ℳ := by
    intro h
    exact hmem ((mem_shadow_iff.mp hℳ) ▸ h : membershipReading m 𝒩)
  have hdiff : deleteNode m ℳ = ℳ := Set.sdiff_singleton_eq_self hmemℳ
  exact not_zeroPoleBlindPositiveOn_deleteNode hm ℳ (by rw [hdiff]; exact hpos)

/-! ### 2. Completeness of the one-bit refutation -/

/-- **Completeness.** Under RH a node set is zero-pole positive exactly when no single
prime-power bit refutes it. -/
theorem zeroPoleBlindPositiveOn_iff_no_membership_refutes (hRH : RiemannHypothesis)
    (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn 𝒩 ↔
      ¬ ∃ m : ℕ, IsPrimePow m ∧ Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩 := by
  refine ⟨fun hpos hex => ?_, fun h => ?_⟩
  · obtain ⟨m, -, href⟩ := hex
    exact not_of_refutes href hpos
  · refine (zeroPoleBlindPositiveOn_iff_primePowers_subset hRH 𝒩).mpr fun m hm => ?_
    by_contra hmem
    exact h ⟨m, hm, refutes_membershipReading_of_notMem hm hmem⟩

/-! ### 3. The asymmetry -/

/-- **The node face's asymmetry is extreme.** Refuting takes one bit; confirming takes all of them,
since no asymptotic reading of the node set certifies anything below the trivial `½`. -/
theorem theNodeFaceAsymmetry (hRH : RiemannHypothesis) :
    (∀ (m : ℕ) (𝒩 : Set ℕ), IsPrimePow m → m ∉ 𝒩 →
        Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩) ∧
      (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn 𝒩 ↔
        ¬ ∃ m : ℕ, IsPrimePow m ∧ Refutes (membershipReading m) ZeroPoleBlindPositiveOn 𝒩) ∧
      ∀ (O : Type) (r : Set ℕ → O), AsymptoticReading r →
        resolutionLimit nodeScale r {n : ℕ | IsPrimePow n} = 1 / 2 :=
  ⟨fun _ _ hm hmem => refutes_membershipReading_of_notMem hm hmem,
    zeroPoleBlindPositiveOn_iff_no_membership_refutes hRH,
    fun _ _ h => resolutionLimit_nodeScale_asymptoticReading h⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
