import GaloisForLFunctions.RHTower.CompleteResolutionPrimeNormalHilbertSaturation
import Mathlib.Order.Filter.TendstoCofinite
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Exact finite-fibre grading boundary for the complete prime-normal reader

Let `P j = (p_i⁻¹)^(j+1)` in `ℓ²(ℕ, ℂ)`.  This file proves the sharp
grading law needed at the Route-L source horizon:

* every infinite subset of the exponent packet remains norm-cyclic;
* arbitrary affine centering preserves this subsequence cyclicity;
* a closed graded relation saturates every grade with an infinite exponent
  fibre, in the stronger independently-supported sense;
* if every grade fibre is infinite, the relation has full product vertical
  fibre and factors as its domain times the entire graded target;
* finite grade fibres admit a closed, gradewise-proper product carrier;
* existence of any closed gradewise-proper carrier retaining the packet is
  equivalent to finiteness of every grade fibre.

Thus finite fibres are not a convenient sufficient condition: they are the
exact escape boundary from forced Hilbert saturation.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Algebraic span of prime-normal packets whose exponent belongs to `J`. -/
def completeResolutionPrimeHilbertPacketSpanOn (J : Set ℕ) :
    Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  Submodule.span ℂ (completeResolutionPrimeHilbertPacket '' J)

/-- A corrected packet indexed by `J` lies in the closure of the restricted
packet span once the preceding coordinate vectors have been recovered. -/
theorem completeResolutionPrimeHilbertCorrected_mem_packetSpanOn_closure
    {J : Set ℕ} {k j : ℕ}
    (hj : j ∈ J)
    (hprev : ∀ i < k,
      lp.single 2 i (1 : ℂ) ∈
        (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure) :
    completeResolutionPrimeHilbertCorrected k j ∈
      (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure := by
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    exact
      (completeResolutionPrimeHilbertPacketSpanOn J).le_topologicalClosure
        (Submodule.subset_span ⟨j, hj, rfl⟩)
  · unfold completeResolutionPrimeHilbertEarlier
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _
        (hprev i (Finset.mem_range.mp hi))

/-- Every coordinate vector lies in the closure of the packet span restricted
to an arbitrary infinite exponent set. -/
theorem completeResolutionPrimeHilbert_single_mem_packetSpanOn_closure
    {J : Set ℕ} (hJ : J.Infinite) (k : ℕ) :
    lp.single 2 k (1 : ℂ) ∈
      (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure := by
  let e : ℕ → ℕ := fun n => (hJ.natEmbedding J n : ℕ)
  have heinj : Function.Injective e :=
    Subtype.coe_injective.comp (hJ.natEmbedding J).injective
  have heTop : Tendsto e atTop atTop :=
    heinj.nat_tendsto_atTop
  have heJ : ∀ n : ℕ, e n ∈ J :=
    fun n => (hJ.natEmbedding J n).property
  induction k using Nat.strong_induction_on with
  | h k ih =>
      apply
        (Submodule.isClosed_topologicalClosure
          (completeResolutionPrimeHilbertPacketSpanOn J)).mem_of_tendsto
          ((tendsto_completeResolutionPrimeHilbertCorrected_single k).comp heTop)
      exact Filter.Eventually.of_forall fun n =>
        completeResolutionPrimeHilbertCorrected_mem_packetSpanOn_closure
          (heJ n) ih

/-- **Infinite-subsequence cyclicity.** Every infinite exponent subset of the
complete prime-normal packet has norm-dense complex span in `ℓ²`. -/
theorem completeResolutionPrimeHilbertPacketSpanOn_closure_eq_top
    {J : Set ℕ} (hJ : J.Infinite) :
    (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure = ⊤ := by
  let B : Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
    Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ))
  have hB :
      B ≤ (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    exact completeResolutionPrimeHilbert_single_mem_packetSpanOn_closure hJ k
  have hBclosure :
      B.topologicalClosure ≤
        (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosure :=
    Submodule.topologicalClosure_minimal B hB
      (Submodule.isClosed_topologicalClosure
        (completeResolutionPrimeHilbertPacketSpanOn J))
  have hBdense : B.topologicalClosure = ⊤ :=
    (HilbertSchmidt.lpBasis ℕ).dense_span
  apply top_unique
  rw [← hBdense]
  exact hBclosure

/-- Restricted affine packet span after subtracting a proposed horizon value. -/
def completeResolutionPrimeHilbertAffinePacketSpanOn
    (J : Set ℕ) (y : CompleteResolutionPrimeHilbertSpace) :
    Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  Submodule.span ℂ
    ((fun j : ℕ => completeResolutionPrimeHilbertPacket j - y) '' J)

/-- An arbitrary affine centre does not create an annihilator on an infinite
exponent subset. -/
theorem completeResolutionPrimeHilbertAffinePacketSpanOn_orthogonal_eq_bot
    {J : Set ℕ} (hJ : J.Infinite)
    (y : CompleteResolutionPrimeHilbertSpace) :
    (completeResolutionPrimeHilbertAffinePacketSpanOn J y)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hdiff :
      ∀ j ∈ J,
        inner ℂ (completeResolutionPrimeHilbertPacket j - y) z = 0 := by
    intro j hj
    exact (Submodule.mem_orthogonal _ _).mp hz _
      (Submodule.subset_span ⟨j, hj, rfl⟩)
  have heq :
      ∀ j ∈ J,
        inner ℂ (completeResolutionPrimeHilbertPacket j) z =
          inner ℂ y z := by
    intro j hj
    exact sub_eq_zero.mp (by simpa [inner_sub_left] using hdiff j hj)
  let e : ℕ → ℕ := fun n => (hJ.natEmbedding J n : ℕ)
  have heinj : Function.Injective e :=
    Subtype.coe_injective.comp (hJ.natEmbedding J).injective
  have heTop : Tendsto e atTop atTop :=
    heinj.nat_tendsto_atTop
  have heJ : ∀ n : ℕ, e n ∈ J :=
    fun n => (hJ.natEmbedding J n).property
  have hleft :
      Tendsto
        (fun n : ℕ => inner ℂ (completeResolutionPrimeHilbertPacket (e n)) z)
        atTop (nhds 0) := by
    simpa using
      (tendsto_completeResolutionPrimeHilbertPacket_zero.comp heTop).inner
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (nhds z))
  have hyz : inner ℂ y z = 0 := by
    have hzero :
        Tendsto (fun _ : ℕ => inner ℂ y z) atTop (nhds 0) := by
      convert hleft using 1
      funext n
      exact (heq (e n) (heJ n)).symm
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  have hpacket :
      ∀ j ∈ J, inner ℂ (completeResolutionPrimeHilbertPacket j) z = 0 := by
    intro j hj
    rw [heq j hj, hyz]
  have hzunc :
      z ∈ (completeResolutionPrimeHilbertPacketSpanOn J)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨j, hj, rfl⟩ := hv
        exact hpacket j hj
    | zero => simp
    | add u v _ _ hu hv => simp [inner_add_left, hu, hv]
    | smul c v _ hv => simp [inner_smul_left, hv]
  have hzclosure :
      z ∈ (completeResolutionPrimeHilbertPacketSpanOn J).topologicalClosureᗮ := by
    simpa [Submodule.orthogonal_closure] using hzunc
  rw [completeResolutionPrimeHilbertPacketSpanOn_closure_eq_top hJ,
    Submodule.top_orthogonal_eq_bot] at hzclosure
  exact hzclosure

/-- **Affine infinite-subsequence cyclicity.** Subtracting any proposed
horizon value preserves density on every infinite exponent subset. -/
theorem completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top
    {J : Set ℕ} (hJ : J.Infinite)
    (y : CompleteResolutionPrimeHilbertSpace) :
    (completeResolutionPrimeHilbertAffinePacketSpanOn J y).topologicalClosure =
      ⊤ := by
  calc
    (completeResolutionPrimeHilbertAffinePacketSpanOn J y).topologicalClosure =
        (completeResolutionPrimeHilbertAffinePacketSpanOn J y)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℂ CompleteResolutionPrimeHilbertSpace)ᗮ := by
      rw [completeResolutionPrimeHilbertAffinePacketSpanOn_orthogonal_eq_bot hJ]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- The prime-normal Hilbert target is not finite-dimensional. -/
theorem completeResolutionPrimeHilbertSpace_not_finiteDimensional :
    ¬ FiniteDimensional ℂ CompleteResolutionPrimeHilbertSpace := by
  intro hfinite
  letI : FiniteDimensional ℂ CompleteResolutionPrimeHilbertSpace := hfinite
  exact
    Module.Finite.not_linearIndependent_of_infinite
      (HilbertSchmidt.lpBasis ℕ)
      (HilbertSchmidt.lpBasis ℕ).orthonormal.linearIndependent

/-- A finite affine packet set spans a proper subspace of the prime-normal
Hilbert target. -/
theorem completeResolutionPrimeHilbertAffinePacketSpanOn_ne_top
    {J : Set ℕ} (hJ : J.Finite)
    (y : CompleteResolutionPrimeHilbertSpace) :
    completeResolutionPrimeHilbertAffinePacketSpanOn J y ≠ ⊤ := by
  intro htop
  let V := completeResolutionPrimeHilbertAffinePacketSpanOn J y
  have hgen :
      (((fun j : ℕ => completeResolutionPrimeHilbertPacket j - y) '' J) :
        Set CompleteResolutionPrimeHilbertSpace).Finite :=
    hJ.image _
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ hgen
  have hsurj : Function.Surjective V.subtype := by
    intro z
    have hz : z ∈ V := by
      change z ∈ completeResolutionPrimeHilbertAffinePacketSpanOn J y
      rw [htop]
      trivial
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfinite : FiniteDimensional ℂ CompleteResolutionPrimeHilbertSpace :=
    FiniteDimensional.of_surjective V.subtype hsurj
  exact completeResolutionPrimeHilbertSpace_not_finiteDimensional hfinite

/-- Exact local density classification: the affine packet span on `J` is
dense exactly when `J` is infinite. -/
theorem completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top_iff
    (J : Set ℕ) (y : CompleteResolutionPrimeHilbertSpace) :
    (completeResolutionPrimeHilbertAffinePacketSpanOn J y).topologicalClosure =
        ⊤ ↔
      J.Infinite := by
  constructor
  · intro hclosure
    by_contra hJ
    have hJfinite : J.Finite := not_not.mp hJ
    have hgen :
        (((fun j : ℕ => completeResolutionPrimeHilbertPacket j - y) '' J) :
          Set CompleteResolutionPrimeHilbertSpace).Finite :=
      hJfinite.image _
    letI :
        FiniteDimensional ℂ
          (completeResolutionPrimeHilbertAffinePacketSpanOn J y) :=
      FiniteDimensional.span_of_finite ℂ hgen
    have hclosed :
        IsClosed
          (completeResolutionPrimeHilbertAffinePacketSpanOn J y :
            Set CompleteResolutionPrimeHilbertSpace) :=
      (completeResolutionPrimeHilbertAffinePacketSpanOn J y).closed_of_finiteDimensional
    have htop :
        completeResolutionPrimeHilbertAffinePacketSpanOn J y = ⊤ := by
      rw [← hclosed.submodule_topologicalClosure_eq]
      exact hclosure
    exact
      completeResolutionPrimeHilbertAffinePacketSpanOn_ne_top hJfinite y htop
  · exact fun hJ =>
      completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top hJ y

/-- Product of Hilbert targets indexed by source-horizon grade. -/
abbrev CompleteResolutionPrimeHilbertGradedSpace (G : Type*) :=
  G → CompleteResolutionPrimeHilbertSpace

/-- Algebraic packet span carried by one grade. -/
def completeResolutionPrimeHilbertGradeSpan
    {G : Type*} (g : ℕ → G)
    (y : G → CompleteResolutionPrimeHilbertSpace) (γ : G) :
    Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  completeResolutionPrimeHilbertAffinePacketSpanOn
    {j : ℕ | g j = γ} (y γ)

/-- The supported slice of a graded vertical fibre at grade `γ`. -/
def completeResolutionPrimeHilbertSupportedSlice
    {G X : Type*} [DecidableEq G]
    [AddCommMonoid X] [Module ℂ X]
    (R : Submodule ℂ
      (X × CompleteResolutionPrimeHilbertGradedSpace G))
    (γ : G) :
    Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  (linearRelationVerticalFiber R).comap
    (LinearMap.single ℂ
      (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ)

/-- **Per-grade saturation law.** A closed relation retaining the graded
reader saturates every grade whose exponent fibre is infinite.  The
conclusion is independently supported at that grade, stronger than
surjectivity of a coordinate projection. -/
theorem closedLinearRelation_completeResolutionPrimeHilbert_fullSupportedSlice
    {G X : Type*} [DecidableEq G]
    [AddCommMonoid X] [Module ℂ X] [TopologicalSpace X]
    (R : Submodule ℂ
      (X × CompleteResolutionPrimeHilbertGradedSpace G))
    (hclosed :
      IsClosed
        (R : Set (X × CompleteResolutionPrimeHilbertGradedSpace G)))
    (g : ℕ → G) (u : ℕ → ℕ → X)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : G → CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ,
      (u K j,
        Pi.single (g j) (completeResolutionPrimeHilbertPacket j - y (g j))) ∈ R)
    (γ : G) (hγ : Set.Infinite {j : ℕ | g j = γ})
    (z : CompleteResolutionPrimeHilbertSpace) :
    ((0 : X), Pi.single γ z) ∈ R := by
  let W :=
    completeResolutionPrimeHilbertSupportedSlice R γ
  have hgenerators :
      ∀ j ∈ {j : ℕ | g j = γ},
        completeResolutionPrimeHilbertPacket j - y γ ∈ W := by
    intro j hj
    have hjγ : g j = γ := hj
    have hv :
        Pi.single (g j)
            (completeResolutionPrimeHilbertPacket j - y (g j)) ∈
          linearRelationVerticalFiber R :=
      closedLinearRelation_mem_vertical_of_tendsto_zero R hclosed
        (fun K : ℕ => u K j)
        (Pi.single (g j)
          (completeResolutionPrimeHilbertPacket j - y (g j)))
        (hu j) (fun K => hgraph K j)
    change
      (LinearMap.single ℂ
        (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ)
          (completeResolutionPrimeHilbertPacket j - y γ) ∈
        linearRelationVerticalFiber R
    simpa [LinearMap.single_apply, hjγ] using hv
  have hspan :
      completeResolutionPrimeHilbertGradeSpan g y γ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact hgenerators j hj
  have hWclosed :
      IsClosed (W : Set CompleteResolutionPrimeHilbertSpace) := by
    change
      IsClosed
        ((fun v : CompleteResolutionPrimeHilbertSpace =>
          ((0 : X), Pi.single γ v)) ⁻¹'
            (R : Set
              (X × CompleteResolutionPrimeHilbertGradedSpace G)))
    exact hclosed.preimage
      (continuous_const.prodMk
        (ContinuousLinearMap.single ℂ
          (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ).continuous)
  have hclosure :
      (completeResolutionPrimeHilbertGradeSpan g y γ).topologicalClosure ≤
        W :=
    Submodule.topologicalClosure_minimal
      (completeResolutionPrimeHilbertGradeSpan g y γ) hspan hWclosed
  change z ∈ W
  apply hclosure
  exact
    completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top
      hγ (y γ) ▸ Submodule.mem_top

/-- If every grade fibre is infinite, the graded relation has the entire
product target as vertical fibre. -/
theorem closedLinearRelation_completeResolutionPrimeHilbert_fullGradedVertical
    {G X : Type*} [DecidableEq G]
    [AddCommMonoid X] [Module ℂ X] [TopologicalSpace X]
    (R : Submodule ℂ
      (X × CompleteResolutionPrimeHilbertGradedSpace G))
    (hclosed :
      IsClosed
        (R : Set (X × CompleteResolutionPrimeHilbertGradedSpace G)))
    (g : ℕ → G) (u : ℕ → ℕ → X)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : G → CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ,
      (u K j,
        Pi.single (g j) (completeResolutionPrimeHilbertPacket j - y (g j))) ∈ R)
    (hall : ∀ γ : G, Set.Infinite {j : ℕ | g j = γ})
    (z : CompleteResolutionPrimeHilbertGradedSpace G) :
    ((0 : X), z) ∈ R := by
  let V : Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G) :=
    linearRelationVerticalFiber R
  let S : Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G) :=
    ⨆ γ : G,
      (⊤ : Submodule ℂ CompleteResolutionPrimeHilbertSpace).map
        (LinearMap.single ℂ
          (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ)
  have hSV : S ≤ V := by
    apply iSup_le
    intro γ
    rintro _ ⟨v, _, rfl⟩
    change ((0 : X), Pi.single γ v) ∈ R
    exact
      closedLinearRelation_completeResolutionPrimeHilbert_fullSupportedSlice
        R hclosed g u hu y hgraph γ (hall γ) v
  have hVclosed :
      IsClosed
        (V : Set (CompleteResolutionPrimeHilbertGradedSpace G)) := by
    change
      IsClosed
        ((fun v : CompleteResolutionPrimeHilbertGradedSpace G =>
          ((0 : X), v)) ⁻¹'
            (R : Set
              (X × CompleteResolutionPrimeHilbertGradedSpace G)))
    exact hclosed.preimage (continuous_const.prodMk continuous_id)
  have hclosure : S.topologicalClosure ≤ V :=
    Submodule.topologicalClosure_minimal S hSV hVclosed
  have hStop : S.topologicalClosure = ⊤ := by
    dsimp [S]
    rw [Submodule.topologicalClosure_iSup_map_single]
    rw [isClosed_univ.submodule_topologicalClosure_eq]
    exact Submodule.pi_top Set.univ
  change z ∈ V
  apply hclosure
  rw [hStop]
  trivial

/-- Full graded verticality factorizes the relation as its domain times the
entire product target. -/
theorem closedLinearRelation_completeResolutionPrimeHilbert_graded_eq_domain_prod
    {G X : Type*} [DecidableEq G]
    [AddCommMonoid X] [Module ℂ X] [TopologicalSpace X]
    (R : Submodule ℂ
      (X × CompleteResolutionPrimeHilbertGradedSpace G))
    (hclosed :
      IsClosed
        (R : Set (X × CompleteResolutionPrimeHilbertGradedSpace G)))
    (g : ℕ → G) (u : ℕ → ℕ → X)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : G → CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ,
      (u K j,
        Pi.single (g j) (completeResolutionPrimeHilbertPacket j - y (g j))) ∈ R)
    (hall : ∀ γ : G, Set.Infinite {j : ℕ | g j = γ}) :
    (R : Set (X × CompleteResolutionPrimeHilbertGradedSpace G)) =
      linearRelationDomain R ×ˢ Set.univ := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p.2, hp⟩, Set.mem_univ _⟩
  · rintro ⟨⟨v₀, hv₀⟩, _⟩
    have hv :
        ((0 : X), p.2 - v₀) ∈ R :=
      closedLinearRelation_completeResolutionPrimeHilbert_fullGradedVertical
        R hclosed g u hu y hgraph hall (p.2 - v₀)
    simpa using Submodule.add_mem R hv₀ hv

/-- Canonical product carrier obtained by keeping each grade's algebraic
packet span separate. -/
def completeResolutionPrimeHilbertFiniteFibreCarrier
    {G : Type*} (g : ℕ → G)
    (y : G → CompleteResolutionPrimeHilbertSpace) :
    Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G) :=
  Submodule.pi Set.univ
    (completeResolutionPrimeHilbertGradeSpan g y)

/-- The canonical graded packet is retained by the finite-fibre carrier
without taking any cross-grade closure. -/
theorem completeResolutionPrimeHilbert_gradedPacket_mem_finiteFibreCarrier
    {G : Type*} [DecidableEq G]
    (g : ℕ → G) (y : G → CompleteResolutionPrimeHilbertSpace)
    (j : ℕ) :
    Pi.single (g j) (completeResolutionPrimeHilbertPacket j - y (g j)) ∈
      completeResolutionPrimeHilbertFiniteFibreCarrier g y := by
  unfold completeResolutionPrimeHilbertFiniteFibreCarrier
  rw [Submodule.mem_pi]
  intro γ _
  by_cases hγ : γ = g j
  · subst γ
    simpa [completeResolutionPrimeHilbertGradeSpan,
      completeResolutionPrimeHilbertAffinePacketSpanOn] using
      (Submodule.subset_span
        (R := ℂ)
        (s := (fun n : ℕ =>
          completeResolutionPrimeHilbertPacket n - y (g j)) ''
            {n : ℕ | g n = g j})
        ⟨j, rfl, rfl⟩)
  · rw [Pi.single_eq_of_ne hγ]
    exact Submodule.zero_mem _

/-- With finite grade fibres, the canonical product carrier is closed. -/
theorem completeResolutionPrimeHilbertFiniteFibreCarrier_isClosed
    {G : Type*} (g : ℕ → G)
    (y : G → CompleteResolutionPrimeHilbertSpace)
    (hfinite : ∀ γ : G, Set.Finite {j : ℕ | g j = γ}) :
    IsClosed
      (completeResolutionPrimeHilbertFiniteFibreCarrier g y :
        Set (CompleteResolutionPrimeHilbertGradedSpace G)) := by
  have hgrade :
      ∀ γ : G,
        IsClosed
          (completeResolutionPrimeHilbertGradeSpan g y γ :
            Set CompleteResolutionPrimeHilbertSpace) := by
    intro γ
    have hgen :
        (((fun j : ℕ => completeResolutionPrimeHilbertPacket j - y γ) ''
          {j : ℕ | g j = γ}) :
          Set CompleteResolutionPrimeHilbertSpace).Finite :=
      (hfinite γ).image _
    letI :
        FiniteDimensional ℂ
          (completeResolutionPrimeHilbertGradeSpan g y γ) :=
      FiniteDimensional.span_of_finite ℂ hgen
    exact
      (completeResolutionPrimeHilbertGradeSpan g y γ).closed_of_finiteDimensional
  have hset :
      (completeResolutionPrimeHilbertFiniteFibreCarrier g y :
          Set (CompleteResolutionPrimeHilbertGradedSpace G)) =
        ⋂ γ : G,
          (fun f : CompleteResolutionPrimeHilbertGradedSpace G => f γ) ⁻¹'
            (completeResolutionPrimeHilbertGradeSpan g y γ :
              Set CompleteResolutionPrimeHilbertSpace) := by
    ext f
    simp [completeResolutionPrimeHilbertFiniteFibreCarrier]
  rw [hset]
  exact isClosed_iInter fun γ =>
    (hgrade γ).preimage (continuous_apply γ)

/-- Gradewise properness records that no supported Hilbert grade has already
been swallowed by a carrier. -/
def CompleteResolutionPrimeHilbertCarrier.IsGradewiseProper
    {G : Type*} [DecidableEq G]
    (C : Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G)) : Prop :=
  ∀ γ : G, ∃ z : CompleteResolutionPrimeHilbertSpace,
    (Pi.single γ z : CompleteResolutionPrimeHilbertGradedSpace G) ∉ C

/-- Finite fibres make the canonical carrier proper in every supported
grade, not merely proper as one undifferentiated product subspace. -/
theorem completeResolutionPrimeHilbertFiniteFibreCarrier_isGradewiseProper
    {G : Type*} [DecidableEq G]
    (g : ℕ → G) (y : G → CompleteResolutionPrimeHilbertSpace)
    (hfinite : ∀ γ : G, Set.Finite {j : ℕ | g j = γ}) :
    CompleteResolutionPrimeHilbertCarrier.IsGradewiseProper
      (completeResolutionPrimeHilbertFiniteFibreCarrier g y) := by
  intro γ
  have hproper :
      completeResolutionPrimeHilbertGradeSpan g y γ ≠ ⊤ :=
    completeResolutionPrimeHilbertAffinePacketSpanOn_ne_top
      (hfinite γ) (y γ)
  obtain ⟨z, -, hz⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr hproper)
  refine ⟨z, ?_⟩
  intro hzcarrier
  have hzgrade :
      (Pi.single γ z : CompleteResolutionPrimeHilbertGradedSpace G) γ ∈
        completeResolutionPrimeHilbertGradeSpan g y γ :=
    (Submodule.mem_pi.mp hzcarrier) γ (Set.mem_univ γ)
  exact hz (by simpa using hzgrade)

/-- A closed carrier retaining the packet saturates an independently
supported grade whenever that grade fibre is infinite. -/
theorem closedCarrier_completeResolutionPrimeHilbert_fullSupportedSlice
    {G : Type*} [DecidableEq G]
    (C : Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G))
    (hclosed :
      IsClosed (C : Set (CompleteResolutionPrimeHilbertGradedSpace G)))
    (g : ℕ → G) (y : G → CompleteResolutionPrimeHilbertSpace)
    (hpacket : ∀ j : ℕ,
      Pi.single (g j) (completeResolutionPrimeHilbertPacket j - y (g j)) ∈ C)
    (γ : G) (hγ : Set.Infinite {j : ℕ | g j = γ})
    (z : CompleteResolutionPrimeHilbertSpace) :
    Pi.single γ z ∈ C := by
  let W : Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
    C.comap
      (LinearMap.single ℂ
        (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ)
  have hspan :
      completeResolutionPrimeHilbertGradeSpan g y γ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have hjγ : g j = γ := hj
    change
      Pi.single γ (completeResolutionPrimeHilbertPacket j - y γ) ∈ C
    simpa [hjγ] using hpacket j
  have hWclosed :
      IsClosed (W : Set CompleteResolutionPrimeHilbertSpace) := by
    change
      IsClosed
        ((fun v : CompleteResolutionPrimeHilbertSpace => Pi.single γ v) ⁻¹'
          (C : Set (CompleteResolutionPrimeHilbertGradedSpace G)))
    exact hclosed.preimage
      (ContinuousLinearMap.single ℂ
        (fun _ : G => CompleteResolutionPrimeHilbertSpace) γ).continuous
  have hclosure :
      (completeResolutionPrimeHilbertGradeSpan g y γ).topologicalClosure ≤ W :=
    Submodule.topologicalClosure_minimal
      (completeResolutionPrimeHilbertGradeSpan g y γ) hspan hWclosed
  change z ∈ W
  apply hclosure
  exact
    completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top
      hγ (y γ) ▸ Submodule.mem_top

/-- **Exact finite-fibre escape criterion.** A closed gradewise-proper
carrier retaining every source-defined affine packet exists if and only if
every grade fibre is finite. -/
theorem completeResolutionPrimeHilbert_exists_closed_gradewiseProperCarrier_iff
    {G : Type*} [DecidableEq G]
    (g : ℕ → G) (y : G → CompleteResolutionPrimeHilbertSpace) :
    (∃ C : Submodule ℂ (CompleteResolutionPrimeHilbertGradedSpace G),
        IsClosed (C : Set (CompleteResolutionPrimeHilbertGradedSpace G)) ∧
        (∀ j : ℕ,
          Pi.single (g j)
            (completeResolutionPrimeHilbertPacket j - y (g j)) ∈ C) ∧
        CompleteResolutionPrimeHilbertCarrier.IsGradewiseProper C) ↔
      ∀ γ : G, Set.Finite {j : ℕ | g j = γ} := by
  constructor
  · rintro ⟨C, hclosed, hpacket, hproper⟩ γ
    by_contra hfinite
    have hγ : Set.Infinite {j : ℕ | g j = γ} := hfinite
    obtain ⟨z, hz⟩ := hproper γ
    exact hz
      (closedCarrier_completeResolutionPrimeHilbert_fullSupportedSlice
        C hclosed g y hpacket γ hγ z)
  · intro hfinite
    exact
      ⟨completeResolutionPrimeHilbertFiniteFibreCarrier g y,
        completeResolutionPrimeHilbertFiniteFibreCarrier_isClosed
          g y hfinite,
        completeResolutionPrimeHilbert_gradedPacket_mem_finiteFibreCarrier
          g y,
        completeResolutionPrimeHilbertFiniteFibreCarrier_isGradewiseProper
          g y hfinite⟩

end

end RHTower
