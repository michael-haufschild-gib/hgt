import GaloisForLFunctions.HTGeometry.ConstitutiveSymmetricFormationHomology
import GaloisForLFunctions.HTGeometry.SerialObserverFormationCharge
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The symmetric three-formation complex

Three subspaces `U, W, Z` of a vector space carry an incidence complex

`(U ⊓ W) ⊕ (U ⊓ Z) ⊕ (W ⊓ Z) --d₂--> U ⊕ W ⊕ Z --d₁--> V`

whose first homology is the symmetric formation charge.  This file constructs the complex, proves
`d₁ ∘ d₂ = 0`, computes `ker d₂` as the triple intersection, and identifies the first homology
with the distributivity quotient in each of the three charts, hence with each other; this makes
the charge manifestly permutation-invariant.  When one leg is an observer kernel, the charge is
canonically the overlap created by observation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Degree-one chains of the symmetric three-formation complex. -/
abbrev TriChainOne (U W Z : Submodule K V) : Type _ := ↥U × ↥W × ↥Z

/-- Degree-two chains: the pairwise gluing relations. -/
abbrev TriChainTwo (U W Z : Submodule K V) : Type _ := ↥(U ⊓ W) × ↥(U ⊓ Z) × ↥(W ⊓ Z)

/-- The degree-one differential `d₁(u,w,z) = u + w + z`. -/
def triD1 (U W Z : Submodule K V) : TriChainOne U W Z →ₗ[K] V :=
  U.subtype.coprod (W.subtype.coprod Z.subtype)

@[simp] theorem triD1_apply (U W Z : Submodule K V) (t : TriChainOne U W Z) :
    triD1 U W Z t = (t.1 : V) + ((t.2.1 : V) + (t.2.2 : V)) := rfl

/-- The degree-two differential `d₂(a,b,c) = (a + b, -a + c, -b - c)`. -/
def triD2 (U W Z : Submodule K V) : TriChainTwo U W Z →ₗ[K] TriChainOne U W Z :=
  ((Submodule.inclusion (inf_le_left : U ⊓ W ≤ U)).coprod
      ((Submodule.inclusion (inf_le_left : U ⊓ Z ≤ U)).coprod 0)).prod
    ((((-Submodule.inclusion (inf_le_right : U ⊓ W ≤ W))).coprod
        ((0 : ↥(U ⊓ Z) →ₗ[K] ↥W).coprod (Submodule.inclusion (inf_le_left : W ⊓ Z ≤ W)))).prod
      ((0 : ↥(U ⊓ W) →ₗ[K] ↥Z).coprod
        (((-Submodule.inclusion (inf_le_right : U ⊓ Z ≤ Z))).coprod
          (-Submodule.inclusion (inf_le_right : W ⊓ Z ≤ Z)))))

@[simp] theorem triD2_apply_fst (U W Z : Submodule K V) (s : TriChainTwo U W Z) :
    ((triD2 U W Z s).1 : V) = (s.1 : V) + (s.2.1 : V) := by
  show ((s.1 : V) + ((s.2.1 : V) + 0)) = _
  rw [add_zero]

@[simp] theorem triD2_apply_snd_fst (U W Z : Submodule K V) (s : TriChainTwo U W Z) :
    ((triD2 U W Z s).2.1 : V) = -(s.1 : V) + (s.2.2 : V) := by
  show (-(s.1 : V) + (0 + (s.2.2 : V))) = _
  rw [zero_add]

@[simp] theorem triD2_apply_snd_snd (U W Z : Submodule K V) (s : TriChainTwo U W Z) :
    ((triD2 U W Z s).2.2 : V) = -(s.2.1 : V) + -(s.2.2 : V) := by
  show (0 + (-(s.2.1 : V) + -(s.2.2 : V))) = _
  rw [zero_add]

/-- **Theorem 2.1(1).**  The incidence complex is a complex. -/
theorem triD1_comp_triD2 (U W Z : Submodule K V) :
    (triD1 U W Z).comp (triD2 U W Z) = 0 := by
  refine LinearMap.ext fun s => ?_
  show ((triD2 U W Z s).1 : V) + (((triD2 U W Z s).2.1 : V) + ((triD2 U W Z s).2.2 : V)) = 0
  rw [triD2_apply_fst, triD2_apply_snd_fst, triD2_apply_snd_snd]
  abel

/-- **Theorem 2.1(1).**  The degree-one differential surjects onto the fused carrier. -/
theorem range_triD1 (U W Z : Submodule K V) :
    LinearMap.range (triD1 U W Z) = U ⊔ W ⊔ Z := by
  apply le_antisymm
  · rintro v ⟨t, rfl⟩
    have hU : (t.1 : V) ∈ U ⊔ W ⊔ Z := (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z)
      ((le_sup_left : U ≤ U ⊔ W) t.1.2)
    have hW : (t.2.1 : V) ∈ U ⊔ W ⊔ Z := (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z)
      ((le_sup_right : W ≤ U ⊔ W) t.2.1.2)
    have hZ : (t.2.2 : V) ∈ U ⊔ W ⊔ Z := (le_sup_right : Z ≤ U ⊔ W ⊔ Z) t.2.2.2
    exact Submodule.add_mem _ hU (Submodule.add_mem _ hW hZ)
  · rw [sup_le_iff, sup_le_iff]
    refine ⟨⟨fun u hu => ⟨(⟨u, hu⟩, 0, 0), by simp⟩, fun w hw => ⟨(0, ⟨w, hw⟩, 0), by simp⟩⟩,
      fun z hz => ⟨(0, 0, ⟨z, hz⟩), by simp⟩⟩

/-- The triple intersection, included into the gluing chains as `x ↦ (x, -x, x)`. -/
def triTripleIncl (U W Z : Submodule K V) : ↥(U ⊓ W ⊓ Z) →ₗ[K] TriChainTwo U W Z :=
  (Submodule.inclusion (inf_le_left : U ⊓ W ⊓ Z ≤ U ⊓ W)).prod
    ((-Submodule.inclusion
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ W ⊓ Z ≤ U ⊓ Z)).prod
      (Submodule.inclusion
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ W ⊓ Z ≤ W ⊓ Z)))

@[simp] theorem triTripleIncl_fst (U W Z : Submodule K V) (x : ↥(U ⊓ W ⊓ Z)) :
    ((triTripleIncl U W Z x).1 : V) = (x : V) := rfl

@[simp] theorem triTripleIncl_snd_fst (U W Z : Submodule K V) (x : ↥(U ⊓ W ⊓ Z)) :
    ((triTripleIncl U W Z x).2.1 : V) = -(x : V) := rfl

@[simp] theorem triTripleIncl_snd_snd (U W Z : Submodule K V) (x : ↥(U ⊓ W ⊓ Z)) :
    ((triTripleIncl U W Z x).2.2 : V) = (x : V) := rfl

theorem triTripleIncl_injective (U W Z : Submodule K V) :
    Function.Injective (triTripleIncl U W Z) := by
  intro x y hxy
  refine Subtype.ext ?_
  have := congrArg (fun s : TriChainTwo U W Z => ((s.1 : V))) hxy
  simpa using this

/-- **Theorem 2.1(2).**  The kernel of the gluing differential is the triple intersection. -/
theorem range_triTripleIncl (U W Z : Submodule K V) :
    LinearMap.range (triTripleIncl U W Z) = LinearMap.ker (triD2 U W Z) := by
  apply le_antisymm
  · rintro s ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [triD2_apply_fst, triTripleIncl_fst, triTripleIncl_snd_fst]
      simp
    · rw [triD2_apply_snd_fst, triTripleIncl_fst, triTripleIncl_snd_snd]
      simp
    · rw [triD2_apply_snd_snd, triTripleIncl_snd_fst, triTripleIncl_snd_snd]
      simp
  · intro s hs
    have hz : triD2 U W Z s = 0 := hs
    have h1 : ((triD2 U W Z s).1 : V) = 0 := by rw [hz]; rfl
    have h2 : ((triD2 U W Z s).2.1 : V) = 0 := by rw [hz]; rfl
    rw [triD2_apply_fst] at h1
    rw [triD2_apply_snd_fst] at h2
    have hb : (s.2.1 : V) = -(s.1 : V) := by linear_combination (norm := abel) h1
    have hc : (s.2.2 : V) = (s.1 : V) := by linear_combination (norm := abel) h2
    have hZmem : (s.1 : V) ∈ Z := by
      rw [← hc]
      exact s.2.2.2.2
    have hx : (s.1 : V) ∈ U ⊓ W ⊓ Z := ⟨s.1.2, hZmem⟩
    refine ⟨⟨(s.1 : V), hx⟩, ?_⟩
    refine Prod.ext (Subtype.ext rfl) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [triTripleIncl_snd_fst]
      exact hb.symm
    · rw [triTripleIncl_snd_snd]
      exact hc.symm

/-- **Theorem 2.1(2).**  Explicit form of the kernel. -/
def triKerTwoEquiv (U W Z : Submodule K V) :
    ↥(U ⊓ W ⊓ Z) ≃ₗ[K] LinearMap.ker (triD2 U W Z) :=
  (LinearEquiv.ofInjective _ (triTripleIncl_injective U W Z)).trans
    (LinearEquiv.ofEq _ _ (range_triTripleIncl U W Z))

/-! ## First homology and the three charts -/

/-- Cycles of the symmetric three-formation complex. -/
def triCycle (U W Z : Submodule K V) : Submodule K (TriChainOne U W Z) :=
  LinearMap.ker (triD1 U W Z)

/-- Boundaries of the symmetric three-formation complex. -/
def triBoundary (U W Z : Submodule K V) : Submodule K (TriChainOne U W Z) :=
  LinearMap.range (triD2 U W Z)

theorem triBoundary_le_triCycle (U W Z : Submodule K V) :
    triBoundary U W Z ≤ triCycle U W Z := by
  rintro t ⟨s, rfl⟩
  have := congrArg (fun f : TriChainTwo U W Z →ₗ[K] V => f s) (triD1_comp_triD2 U W Z)
  exact this

/-- **First homology of the symmetric three-formation complex.** -/
abbrev TriHomology (U W Z : Submodule K V) : Type _ :=
  ↥(triCycle U W Z) ⧸ Submodule.comap (triCycle U W Z).subtype (triBoundary U W Z)

theorem triCycle_sum (U W Z : Submodule K V) (t : ↥(triCycle U W Z)) :
    ((t : TriChainOne U W Z).1 : V) + (((t : TriChainOne U W Z).2.1 : V)
      + ((t : TriChainOne U W Z).2.2 : V)) = 0 := t.2

/-- Assemble a homology isomorphism from a surjection onto a formation charge whose kernel is the
boundary space. -/
def triHomologyEquivOfProj {U W Z P Q R : Submodule K V}
    (f : ↥(triCycle U W Z) →ₗ[K] FormationCharge P Q R)
    (hsurj : Function.Surjective f)
    (hker : LinearMap.ker f
      = Submodule.comap (triCycle U W Z).subtype (triBoundary U W Z)) :
    TriHomology U W Z ≃ₗ[K] FormationCharge P Q R :=
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)

/-- The `U`-chart projection of a cycle. -/
def triProjU (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] ↥(formationCore U W Z) :=
  LinearMap.codRestrict (formationCore U W Z)
    (U.subtype.comp ((LinearMap.fst K ↥U (↥W × ↥Z)).comp (triCycle U W Z).subtype))
    (fun t => by
      refine ⟨(t : TriChainOne U W Z).1.2, ?_⟩
      have h := triCycle_sum U W Z t
      have he : ((t : TriChainOne U W Z).1 : V)
          = -(((t : TriChainOne U W Z).2.1 : V) + ((t : TriChainOne U W Z).2.2 : V)) := by
        linear_combination (norm := abel) h
      show ((t : TriChainOne U W Z).1 : V) ∈ W ⊔ Z
      rw [he]
      exact Submodule.neg_mem _ (Submodule.add_mem _
        ((le_sup_left : W ≤ W ⊔ Z) (t : TriChainOne U W Z).2.1.2)
        ((le_sup_right : Z ≤ W ⊔ Z) (t : TriChainOne U W Z).2.2.2)))

@[simp] theorem triProjU_coe (U W Z : Submodule K V) (t : ↥(triCycle U W Z)) :
    ((triProjU U W Z t : ↥(formationCore U W Z)) : V) = ((t : TriChainOne U W Z).1 : V) := rfl

/-- The `U`-chart homology chart map. -/
def triChargeU (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] FormationCharge U W Z :=
  (formationBoundaryInCore U W Z).mkQ.comp (triProjU U W Z)

theorem triChargeU_surjective (U W Z : Submodule K V) :
    Function.Surjective (triChargeU U W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp x.2.2
  have hsum : (x : V) + ((-w) + (-z)) = 0 := by
    rw [← hwz]
    abel
  refine ⟨⟨(⟨(x : V), x.2.1⟩, ⟨-w, Submodule.neg_mem _ hw⟩, ⟨-z, Submodule.neg_mem _ hz⟩),
    hsum⟩, ?_⟩
  show Submodule.Quotient.mk (triProjU U W Z _) = Submodule.Quotient.mk x
  congr 1

theorem ker_triChargeU (U W Z : Submodule K V) :
    LinearMap.ker (triChargeU U W Z)
      = Submodule.comap (triCycle U W Z).subtype (triBoundary U W Z) := by
  apply le_antisymm
  · intro t ht
    have h0 : Submodule.Quotient.mk (triProjU U W Z t)
        = (0 : FormationCharge U W Z) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((t : TriChainOne U W Z).1 : V) ∈ formationBoundary U W Z := h0
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
    set a : ↥(U ⊓ W) := ⟨p, hp⟩ with ha
    set b : ↥(U ⊓ Z) := ⟨q, hq⟩ with hb
    have hcW : ((t : TriChainOne U W Z).2.1 : V) + p ∈ W ⊓ Z := by
      constructor
      · exact Submodule.add_mem _ (t : TriChainOne U W Z).2.1.2 hp.2
      · have hs := triCycle_sum U W Z t
        have : ((t : TriChainOne U W Z).2.1 : V) + p
            = -(((t : TriChainOne U W Z).2.2 : V) + q) := by
          rw [← hpq] at hs
          linear_combination (norm := abel) hs
        rw [this]
        exact Submodule.neg_mem _ (Submodule.add_mem _ (t : TriChainOne U W Z).2.2.2 hq.2)
    set c : ↥(W ⊓ Z) := ⟨((t : TriChainOne U W Z).2.1 : V) + p, hcW⟩ with hc
    refine ⟨(a, b, c), ?_⟩
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [triD2_apply_fst]
      exact hpq
    · rw [triD2_apply_snd_fst]
      show -p + (((t : TriChainOne U W Z).2.1 : V) + p) = ((t : TriChainOne U W Z).2.1 : V)
      abel
    · rw [triD2_apply_snd_snd]
      show -q + -(((t : TriChainOne U W Z).2.1 : V) + p) = ((t : TriChainOne U W Z).2.2 : V)
      have hs := triCycle_sum U W Z t
      rw [← hpq] at hs
      linear_combination (norm := abel) -hs
  · rintro t ht
    obtain ⟨s, hs⟩ := ht
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (triProjU U W Z t) = (0 : FormationCharge U W Z)
    rw [Submodule.Quotient.mk_eq_zero]
    have hv : ((t : TriChainOne U W Z).1 : V) = (s.1 : V) + (s.2.1 : V) := by
      rw [← triD2_apply_fst U W Z s, hs]
      rfl
    show ((t : TriChainOne U W Z).1 : V) ∈ formationBoundary U W Z
    rw [hv]
    exact Submodule.mem_sup.mpr ⟨(s.1 : V), s.1.2, (s.2.1 : V), s.2.1.2, rfl⟩

/-- **Theorem 2.1(4), `U`-chart.**  First homology is the `U`-chart distributivity quotient. -/
def triHomologyEquivU (U W Z : Submodule K V) :
    TriHomology U W Z ≃ₗ[K] FormationCharge U W Z :=
  triHomologyEquivOfProj (triChargeU U W Z) (triChargeU_surjective U W Z) (ker_triChargeU U W Z)

/-- The `W`-chart projection of a cycle. -/
def triProjW (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] ↥(formationCore W U Z) :=
  LinearMap.codRestrict (formationCore W U Z)
    (W.subtype.comp ((LinearMap.fst K ↥W ↥Z).comp
      ((LinearMap.snd K ↥U (↥W × ↥Z)).comp (triCycle U W Z).subtype)))
    (fun t => by
      refine ⟨(t : TriChainOne U W Z).2.1.2, ?_⟩
      have h := triCycle_sum U W Z t
      have he : ((t : TriChainOne U W Z).2.1 : V)
          = -(((t : TriChainOne U W Z).1 : V) + ((t : TriChainOne U W Z).2.2 : V)) := by
        linear_combination (norm := abel) h
      show ((t : TriChainOne U W Z).2.1 : V) ∈ U ⊔ Z
      rw [he]
      exact Submodule.neg_mem _ (Submodule.add_mem _
        ((le_sup_left : U ≤ U ⊔ Z) (t : TriChainOne U W Z).1.2)
        ((le_sup_right : Z ≤ U ⊔ Z) (t : TriChainOne U W Z).2.2.2)))

/-- The `Z`-chart projection of a cycle. -/
def triProjZ (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] ↥(formationCore Z U W) :=
  LinearMap.codRestrict (formationCore Z U W)
    (Z.subtype.comp ((LinearMap.snd K ↥W ↥Z).comp
      ((LinearMap.snd K ↥U (↥W × ↥Z)).comp (triCycle U W Z).subtype)))
    (fun t => by
      refine ⟨(t : TriChainOne U W Z).2.2.2, ?_⟩
      have h := triCycle_sum U W Z t
      have he : ((t : TriChainOne U W Z).2.2 : V)
          = -(((t : TriChainOne U W Z).1 : V) + ((t : TriChainOne U W Z).2.1 : V)) := by
        linear_combination (norm := abel) h
      show ((t : TriChainOne U W Z).2.2 : V) ∈ U ⊔ W
      rw [he]
      exact Submodule.neg_mem _ (Submodule.add_mem _
        ((le_sup_left : U ≤ U ⊔ W) (t : TriChainOne U W Z).1.2)
        ((le_sup_right : W ≤ U ⊔ W) (t : TriChainOne U W Z).2.1.2)))

/-- The `W`-chart homology chart map. -/
def triChargeW (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] FormationCharge W U Z :=
  (formationBoundaryInCore W U Z).mkQ.comp (triProjW U W Z)

/-- The `Z`-chart homology chart map. -/
def triChargeZ (U W Z : Submodule K V) :
    ↥(triCycle U W Z) →ₗ[K] FormationCharge Z U W :=
  (formationBoundaryInCore Z U W).mkQ.comp (triProjZ U W Z)

theorem triChargeW_surjective (U W Z : Submodule K V) :
    Function.Surjective (triChargeW U W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp x.2.2
  have hsum : (-u) + ((x : V) + (-z)) = 0 := by
    rw [← huz]
    abel
  refine ⟨⟨(⟨-u, Submodule.neg_mem _ hu⟩, ⟨(x : V), x.2.1⟩, ⟨-z, Submodule.neg_mem _ hz⟩),
    hsum⟩, ?_⟩
  show Submodule.Quotient.mk (triProjW U W Z _) = Submodule.Quotient.mk x
  congr 1

theorem triChargeZ_surjective (U W Z : Submodule K V) :
    Function.Surjective (triChargeZ U W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp x.2.2
  have hsum : (-u) + ((-w) + (x : V)) = 0 := by
    rw [← huw]
    abel
  refine ⟨⟨(⟨-u, Submodule.neg_mem _ hu⟩, ⟨-w, Submodule.neg_mem _ hw⟩, ⟨(x : V), x.2.1⟩),
    hsum⟩, ?_⟩
  show Submodule.Quotient.mk (triProjZ U W Z _) = Submodule.Quotient.mk x
  congr 1

theorem ker_triChargeW (U W Z : Submodule K V) :
    LinearMap.ker (triChargeW U W Z)
      = Submodule.comap (triCycle U W Z).subtype (triBoundary U W Z) := by
  apply le_antisymm
  · intro t ht
    have h0 : Submodule.Quotient.mk (triProjW U W Z t) = (0 : FormationCharge W U Z) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((t : TriChainOne U W Z).2.1 : V) ∈ formationBoundary W U Z := h0
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
    have hs := triCycle_sum U W Z t
    have hbU : ((t : TriChainOne U W Z).1 : V) + p ∈ U ⊓ Z := by
      constructor
      · exact Submodule.add_mem _ (t : TriChainOne U W Z).1.2 hp.2
      · have hz : ((t : TriChainOne U W Z).1 : V) + p
            = -(((t : TriChainOne U W Z).2.2 : V) + q) := by
          rw [← hpq] at hs
          linear_combination (norm := abel) hs
        rw [hz]
        exact Submodule.neg_mem _ (Submodule.add_mem _ (t : TriChainOne U W Z).2.2.2 hq.2)
    refine ⟨(⟨-p, ⟨Submodule.neg_mem _ hp.2, Submodule.neg_mem _ hp.1⟩⟩,
      ⟨((t : TriChainOne U W Z).1 : V) + p, hbU⟩, ⟨q, ⟨hq.1, hq.2⟩⟩), ?_⟩
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [triD2_apply_fst]
      show -p + (((t : TriChainOne U W Z).1 : V) + p) = ((t : TriChainOne U W Z).1 : V)
      abel
    · rw [triD2_apply_snd_fst]
      show -(-p) + q = ((t : TriChainOne U W Z).2.1 : V)
      rw [← hpq]
      abel
    · rw [triD2_apply_snd_snd]
      show -(((t : TriChainOne U W Z).1 : V) + p) + -q = ((t : TriChainOne U W Z).2.2 : V)
      rw [← hpq] at hs
      linear_combination (norm := abel) -hs
  · rintro t ⟨s, hs⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (triProjW U W Z t) = (0 : FormationCharge W U Z)
    rw [Submodule.Quotient.mk_eq_zero]
    have hv : ((t : TriChainOne U W Z).2.1 : V) = -(s.1 : V) + (s.2.2 : V) := by
      rw [← triD2_apply_snd_fst U W Z s, hs]
      rfl
    show ((t : TriChainOne U W Z).2.1 : V) ∈ formationBoundary W U Z
    rw [hv]
    exact Submodule.mem_sup.mpr ⟨-(s.1 : V), ⟨Submodule.neg_mem _ s.1.2.2,
      Submodule.neg_mem _ s.1.2.1⟩, (s.2.2 : V), ⟨s.2.2.2.1, s.2.2.2.2⟩, rfl⟩

theorem ker_triChargeZ (U W Z : Submodule K V) :
    LinearMap.ker (triChargeZ U W Z)
      = Submodule.comap (triCycle U W Z).subtype (triBoundary U W Z) := by
  apply le_antisymm
  · intro t ht
    have h0 : Submodule.Quotient.mk (triProjZ U W Z t) = (0 : FormationCharge Z U W) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((t : TriChainOne U W Z).2.2 : V) ∈ formationBoundary Z U W := h0
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
    have hs := triCycle_sum U W Z t
    have haUW : ((t : TriChainOne U W Z).1 : V) + p ∈ U ⊓ W := by
      constructor
      · exact Submodule.add_mem _ (t : TriChainOne U W Z).1.2 hp.2
      · have hw : ((t : TriChainOne U W Z).1 : V) + p
            = -(((t : TriChainOne U W Z).2.1 : V) + q) := by
          rw [← hpq] at hs
          linear_combination (norm := abel) hs
        rw [hw]
        exact Submodule.neg_mem _ (Submodule.add_mem _ (t : TriChainOne U W Z).2.1.2 hq.2)
    refine ⟨(⟨((t : TriChainOne U W Z).1 : V) + p, haUW⟩,
      ⟨-p, ⟨Submodule.neg_mem _ hp.2, Submodule.neg_mem _ hp.1⟩⟩,
      ⟨-q, ⟨Submodule.neg_mem _ hq.2,
        Submodule.neg_mem _ hq.1⟩⟩), ?_⟩
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · rw [triD2_apply_fst]
      show (((t : TriChainOne U W Z).1 : V) + p) + -p = ((t : TriChainOne U W Z).1 : V)
      abel
    · rw [triD2_apply_snd_fst]
      show -(((t : TriChainOne U W Z).1 : V) + p) + -q = ((t : TriChainOne U W Z).2.1 : V)
      rw [← hpq] at hs
      linear_combination (norm := abel) -hs
    · rw [triD2_apply_snd_snd]
      show -(-p) + -(-q) = ((t : TriChainOne U W Z).2.2 : V)
      rw [← hpq]
      abel
  · rintro t ⟨s, hs⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (triProjZ U W Z t) = (0 : FormationCharge Z U W)
    rw [Submodule.Quotient.mk_eq_zero]
    have hv : ((t : TriChainOne U W Z).2.2 : V) = -(s.2.1 : V) + -(s.2.2 : V) := by
      rw [← triD2_apply_snd_snd U W Z s, hs]
      rfl
    show ((t : TriChainOne U W Z).2.2 : V) ∈ formationBoundary Z U W
    rw [hv]
    exact Submodule.mem_sup.mpr ⟨-(s.2.1 : V), ⟨Submodule.neg_mem _ s.2.1.2.2,
      Submodule.neg_mem _ s.2.1.2.1⟩, -(s.2.2 : V), ⟨Submodule.neg_mem _ s.2.2.2.2,
      Submodule.neg_mem _ s.2.2.2.1⟩, rfl⟩

/-- **Theorem 2.1(4), `W`-chart.** -/
def triHomologyEquivW (U W Z : Submodule K V) :
    TriHomology U W Z ≃ₗ[K] FormationCharge W U Z :=
  triHomologyEquivOfProj (triChargeW U W Z) (triChargeW_surjective U W Z) (ker_triChargeW U W Z)

/-- **Theorem 2.1(4), `Z`-chart.** -/
def triHomologyEquivZ (U W Z : Submodule K V) :
    TriHomology U W Z ≃ₗ[K] FormationCharge Z U W :=
  triHomologyEquivOfProj (triChargeZ U W Z) (triChargeZ_surjective U W Z) (ker_triChargeZ U W Z)

/-- **Theorem 2.1(3)–(4) `(TFIM.5)`.**  The three distributivity quotients are canonically
isomorphic, so the formation charge does not privilege a leg. -/
def formationChargeEquivW (U W Z : Submodule K V) :
    FormationCharge U W Z ≃ₗ[K] FormationCharge W U Z :=
  (triHomologyEquivU U W Z).symm.trans (triHomologyEquivW U W Z)

/-- **Theorem 2.1(3)–(4) `(TFIM.5)`.** -/
def formationChargeEquivZ (U W Z : Submodule K V) :
    FormationCharge U W Z ≃ₗ[K] FormationCharge Z U W :=
  (triHomologyEquivU U W Z).symm.trans (triHomologyEquivZ U W Z)

/-! ## Observer-created overlap (Theorem 3.1) -/

section Observer

variable {Y : Type*} [AddCommGroup Y] [Module K Y]

/-- Pairs from the two legs whose sum is unobserved. -/
def observerPairs (L : V →ₗ[K] Y) (W Z : Submodule K V) : Submodule K (↥W × ↥Z) :=
  LinearMap.ker (L.comp (W.subtype.coprod Z.subtype))

theorem observerPairs_sum (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (t : ↥(observerPairs L W Z)) :
    L (((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V)) = 0 := t.2

/-- Sending an unobserved pair to the source direction it forms. -/
def pairToCore (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(observerPairs L W Z) →ₗ[K] ↥(formationCore (LinearMap.ker L) W Z) :=
  LinearMap.codRestrict (formationCore (LinearMap.ker L) W Z)
    ((W.subtype.coprod Z.subtype).comp (observerPairs L W Z).subtype)
    (fun t => ⟨observerPairs_sum L W Z t, Submodule.add_mem _
      ((le_sup_left : W ≤ W ⊔ Z) (t : ↥W × ↥Z).1.2)
      ((le_sup_right : Z ≤ W ⊔ Z) (t : ↥W × ↥Z).2.2)⟩)

/-- Sending an unobserved pair to the overlap direction it manufactures. -/
def pairToOverlap (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(observerPairs L W Z) →ₗ[K] ↥(overlapNum L W Z) :=
  LinearMap.codRestrict (overlapNum L W Z)
    ((L.comp W.subtype).comp
      ((LinearMap.fst K ↥W ↥Z).comp (observerPairs L W Z).subtype))
    (fun t => by
      refine ⟨⟨((t : ↥W × ↥Z).1 : V), (t : ↥W × ↥Z).1.2, rfl⟩, ?_⟩
      refine ⟨-((t : ↥W × ↥Z).2 : V), Submodule.neg_mem _ (t : ↥W × ↥Z).2.2, ?_⟩
      have h := observerPairs_sum L W Z t
      rw [map_add] at h
      show L (-((t : ↥W × ↥Z).2 : V)) = L (((t : ↥W × ↥Z).1 : V))
      rw [map_neg]
      linear_combination (norm := abel) -h)

/-- The `U = ker L` chart map from unobserved pairs. -/
def pairCharge (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(observerPairs L W Z) →ₗ[K] FormationCharge (LinearMap.ker L) W Z :=
  (formationBoundaryInCore (LinearMap.ker L) W Z).mkQ.comp (pairToCore L W Z)

/-- The overlap chart map from unobserved pairs. -/
def pairOverlap (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(observerPairs L W Z) →ₗ[K] ObserverOverlap L W Z :=
  (Submodule.comap (overlapNum L W Z).subtype (overlapDen L W Z)).mkQ.comp
    (pairToOverlap L W Z)

theorem pairCharge_surjective (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Function.Surjective (pairCharge L W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp x.2.2
  have hker : L (w + z) = 0 := by
    have : (x : V) ∈ LinearMap.ker L := x.2.1
    rw [hwz]
    exact this
  refine ⟨⟨(⟨w, hw⟩, ⟨z, hz⟩), hker⟩, ?_⟩
  show Submodule.Quotient.mk (pairToCore L W Z _) = Submodule.Quotient.mk x
  congr 1
  exact Subtype.ext hwz

theorem pairOverlap_surjective (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Function.Surjective (pairOverlap L W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ y => ?_
  obtain ⟨w, hw, hwy⟩ := y.2.1
  obtain ⟨z, hz, hzy⟩ := y.2.2
  have hker : L (w + (-z)) = 0 := by
    rw [map_add, map_neg, hwy, hzy, add_neg_cancel]
  refine ⟨⟨(⟨w, hw⟩, ⟨-z, Submodule.neg_mem _ hz⟩), hker⟩, ?_⟩
  show Submodule.Quotient.mk (pairToOverlap L W Z _) = Submodule.Quotient.mk y
  congr 1
  exact Subtype.ext hwy

theorem ker_pairCharge_eq_ker_pairOverlap (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    LinearMap.ker (pairCharge L W Z) = LinearMap.ker (pairOverlap L W Z) := by
  ext t
  constructor
  · intro ht
    have h0 : Submodule.Quotient.mk (pairToCore L W Z t)
        = (0 : FormationCharge (LinearMap.ker L) W Z) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V)
        ∈ formationBoundary (LinearMap.ker L) W Z := by
      have := h0
      exact this
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
    have hint : ((t : ↥W × ↥Z).1 : V) - p ∈ W ⊓ Z := by
      constructor
      · exact Submodule.sub_mem _ (t : ↥W × ↥Z).1.2 hp.2
      · have he : ((t : ↥W × ↥Z).1 : V) - p = q - ((t : ↥W × ↥Z).2 : V) := by
          linear_combination (norm := abel) -hpq
        rw [he]
        exact Submodule.sub_mem _ hq.2 (t : ↥W × ↥Z).2.2
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (pairToOverlap L W Z t) = (0 : ObserverOverlap L W Z)
    rw [Submodule.Quotient.mk_eq_zero]
    show L ((t : ↥W × ↥Z).1 : V) ∈ overlapDen L W Z
    refine ⟨((t : ↥W × ↥Z).1 : V) - p, hint, ?_⟩
    have hp0 : L p = 0 := hp.1
    rw [map_sub, hp0, sub_zero]
  · intro ht
    have h0 : Submodule.Quotient.mk (pairToOverlap L W Z t)
        = (0 : ObserverOverlap L W Z) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : L ((t : ↥W × ↥Z).1 : V) ∈ overlapDen L W Z := h0
    obtain ⟨a, ha, hLa⟩ := hmem
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (pairToCore L W Z t)
      = (0 : FormationCharge (LinearMap.ker L) W Z)
    rw [Submodule.Quotient.mk_eq_zero]
    show ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V)
      ∈ formationBoundary (LinearMap.ker L) W Z
    have hsum := observerPairs_sum L W Z t
    rw [map_add] at hsum
    have hw : ((t : ↥W × ↥Z).1 : V) - a ∈ LinearMap.ker L ⊓ W := by
      refine ⟨?_, Submodule.sub_mem _ (t : ↥W × ↥Z).1.2 ha.1⟩
      show L (((t : ↥W × ↥Z).1 : V) - a) = 0
      rw [map_sub, hLa, sub_self]
    have hz : ((t : ↥W × ↥Z).2 : V) + a ∈ LinearMap.ker L ⊓ Z := by
      refine ⟨?_, Submodule.add_mem _ (t : ↥W × ↥Z).2.2 ha.2⟩
      show L (((t : ↥W × ↥Z).2 : V) + a) = 0
      rw [map_add, hLa]
      linear_combination (norm := abel) hsum
    refine Submodule.mem_sup.mpr ⟨((t : ↥W × ↥Z).1 : V) - a, hw,
      ((t : ↥W × ↥Z).2 : V) + a, hz, ?_⟩
    abel

/-- **Theorem 3.1 `(TFIM.9)`.**  When one leg is an observer kernel, the formation charge is
canonically the overlap manufactured by the observer. -/
def formationChargeEquivObserverOverlap (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    FormationCharge (LinearMap.ker L) W Z ≃ₗ[K] ObserverOverlap L W Z :=
  ((pairCharge L W Z).quotKerEquivOfSurjective (pairCharge_surjective L W Z)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_pairCharge_eq_ker_pairOverlap L W Z)).trans
      ((pairOverlap L W Z).quotKerEquivOfSurjective (pairOverlap_surjective L W Z)))

/-! ### Corollaries of the observer realization -/

theorem formationBoundary_ker_eq_bot (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (hW : Disjoint W (LinearMap.ker L)) (hZ : Disjoint Z (LinearMap.ker L)) :
    formationBoundary (LinearMap.ker L) W Z = ⊥ := by
  rw [formationBoundary, inf_comm (LinearMap.ker L) W, inf_comm (LinearMap.ker L) Z,
    disjoint_iff.mp hW, disjoint_iff.mp hZ, sup_idem]

/-- **Corollary 3.2 `(TFIM.11)`.**  With both legs separately observable, the formation charge is
the excess joint kernel. -/
def formationChargeEquivExcessKernel (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (hW : Disjoint W (LinearMap.ker L)) (hZ : Disjoint Z (LinearMap.ker L)) :
    FormationCharge (LinearMap.ker L) W Z ≃ₗ[K] ↥(LinearMap.ker L ⊓ (W ⊔ Z)) :=
  Submodule.quotEquivOfEqBot _ (by
    show (formationBoundary (LinearMap.ker L) W Z).comap
      (formationCore (LinearMap.ker L) W Z).subtype = ⊥
    rw [formationBoundary_ker_eq_bot L W Z hW hZ, Submodule.comap_bot, Submodule.ker_subtype])

/-- **Corollary 3.2 `(TFIM.12)`.**  Pairwise observability plus exact overlap preservation is
joint observability. -/
theorem disjoint_sup_iff_overlap_le (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (hW : Disjoint W (LinearMap.ker L)) (hZ : Disjoint Z (LinearMap.ker L)) :
    Disjoint (W ⊔ Z) (LinearMap.ker L) ↔ overlapNum L W Z ≤ overlapDen L W Z := by
  have h1 : (∀ q : FormationCharge (LinearMap.ker L) W Z, q = 0)
      ↔ formationCore (LinearMap.ker L) W Z ≤ formationBoundary (LinearMap.ker L) W Z :=
    subQuot_forall_eq_zero_iff _ _
  have hcharge : (∀ q : FormationCharge (LinearMap.ker L) W Z, q = 0)
      ↔ Disjoint (W ⊔ Z) (LinearMap.ker L) := by
    rw [h1, formationBoundary_ker_eq_bot L W Z hW hZ, le_bot_iff, formationCore, disjoint_iff,
      inf_comm]
  have hover : (∀ q : ObserverOverlap L W Z, q = 0) ↔ overlapNum L W Z ≤ overlapDen L W Z :=
    subQuot_forall_eq_zero_iff _ _
  rw [← hcharge, ← hover]
  constructor
  · intro h q
    obtain ⟨p, rfl⟩ := (formationChargeEquivObserverOverlap L W Z).surjective q
    rw [h p, map_zero]
  · intro h p
    have hp := h (formationChargeEquivObserverOverlap L W Z p)
    exact (formationChargeEquivObserverOverlap L W Z).injective (by rw [hp, map_zero])

/-! ### The quotient-created overlap form -/

/-- Subquotients only depend on the submodules. -/
def subQuotCongr {M : Type*} [AddCommGroup M] [Module K M] {N N' D D' : Submodule K M}
    (hN : N = N') (hD : D = D') :
    (↥N ⧸ Submodule.comap N.subtype D) ≃ₗ[K] (↥N' ⧸ Submodule.comap N'.subtype D') := by
  subst hN
  subst hD
  exact LinearEquiv.refl _ _

/-- Formation charge only depends on the three subspaces. -/
def formationChargeCongr {U U' W W' Z Z' : Submodule K V}
    (hU : U = U') (hW : W = W') (hZ : Z = Z') :
    FormationCharge U W Z ≃ₗ[K] FormationCharge U' W' Z' := by
  subst hU
  subst hW
  subst hZ
  exact LinearEquiv.refl _ _

section Correspondence

variable (U : Submodule K V) (A B : Submodule K (V ⧸ U))

/-- Comparison of a subquotient of `V ⧸ U` with the corresponding subquotient of `V`. -/
def mkQSubQuotMap : ↥(Submodule.comap U.mkQ A) →ₗ[K] (↥A ⧸ Submodule.comap A.subtype B) :=
  (Submodule.comap A.subtype B).mkQ.comp
    (LinearMap.codRestrict A (U.mkQ.comp (Submodule.comap U.mkQ A).subtype) fun x => x.2)

theorem mkQSubQuotMap_surjective : Function.Surjective (mkQSubQuotMap U A B) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ a => ?_
  obtain ⟨v, hv⟩ := U.mkQ_surjective (a : V ⧸ U)
  have hva : v ∈ Submodule.comap U.mkQ A := by
    rw [Submodule.mem_comap, hv]
    exact a.2
  refine ⟨⟨v, hva⟩, ?_⟩
  show Submodule.Quotient.mk (⟨U.mkQ v, hva⟩ : ↥A) = Submodule.Quotient.mk a
  congr 1
  exact Subtype.ext hv

theorem ker_mkQSubQuotMap :
    LinearMap.ker (mkQSubQuotMap U A B)
      = Submodule.comap (Submodule.comap U.mkQ A).subtype (Submodule.comap U.mkQ B) := by
  ext x
  constructor
  · intro hx
    have h0 : Submodule.Quotient.mk (⟨U.mkQ (x : V), x.2⟩ : ↥A) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · intro hx
    show Submodule.Quotient.mk (⟨U.mkQ (x : V), x.2⟩ : ↥A) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx

/-- **Subquotients of a quotient are subquotients upstairs.** -/
def mkQSubQuotEquiv :
    (↥(Submodule.comap U.mkQ A) ⧸
        Submodule.comap (Submodule.comap U.mkQ A).subtype (Submodule.comap U.mkQ B))
      ≃ₗ[K] (↥A ⧸ Submodule.comap A.subtype B) :=
  (Submodule.quotEquivOfEq _ _ (ker_mkQSubQuotMap U A B).symm).trans
    ((mkQSubQuotMap U A B).quotKerEquivOfSurjective (mkQSubQuotMap_surjective U A B))

end Correspondence

/-- **Corollary 3.3 `(TFIM.13)`.**  Quotienting by one leg creates an intersection: the formation
charge is the quotient-created overlap. -/
def formationChargeEquivQuotientOverlap (U W Z : Submodule K V) :
    FormationCharge U W Z ≃ₗ[K]
      (↥((U ⊔ W) ⊓ (U ⊔ Z)) ⧸
        Submodule.comap ((U ⊔ W) ⊓ (U ⊔ Z)).subtype (U ⊔ (W ⊓ Z))) := by
  have hnum : Submodule.comap U.mkQ (overlapNum U.mkQ W Z) = (U ⊔ W) ⊓ (U ⊔ Z) := by
    show Submodule.comap U.mkQ (Submodule.map U.mkQ W ⊓ Submodule.map U.mkQ Z) = _
    rw [Submodule.comap_inf, Submodule.comap_map_eq, Submodule.comap_map_eq,
      Submodule.ker_mkQ, sup_comm W U, sup_comm Z U]
  have hden : Submodule.comap U.mkQ (overlapDen U.mkQ W Z) = U ⊔ (W ⊓ Z) := by
    show Submodule.comap U.mkQ (Submodule.map U.mkQ (W ⊓ Z)) = _
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_comm (W ⊓ Z) U]
  exact ((formationChargeCongr (Submodule.ker_mkQ U).symm rfl rfl).trans
    ((formationChargeEquivObserverOverlap U.mkQ W Z).trans
      (mkQSubQuotEquiv U (overlapNum U.mkQ W Z) (overlapDen U.mkQ W Z)).symm)).trans
    (subQuotCongr hnum hden)

/-! ### The observer Mayer--Vietoris complex (Theorem 3.5) -/

theorem map_sup_eq (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Submodule.map L (W ⊔ Z) = Submodule.map L W ⊔ Submodule.map L Z := Submodule.map_sup _ _ _

/-- The diagonal of the observed Mayer--Vietoris complex. -/
def mvDiag (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(Submodule.map L (W ⊓ Z)) →ₗ[K] ↥(Submodule.map L W) × ↥(Submodule.map L Z) :=
  (LinearMap.codRestrict (Submodule.map L W) (Submodule.map L (W ⊓ Z)).subtype
      fun y => Submodule.map_mono inf_le_left y.2).prod
    (-LinearMap.codRestrict (Submodule.map L Z) (Submodule.map L (W ⊓ Z)).subtype
      fun y => Submodule.map_mono inf_le_right y.2)

@[simp] theorem mvDiag_fst (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (y : ↥(Submodule.map L (W ⊓ Z))) : ((mvDiag L W Z y).1 : Y) = (y : Y) := rfl

@[simp] theorem mvDiag_snd (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (y : ↥(Submodule.map L (W ⊓ Z))) : ((mvDiag L W Z y).2 : Y) = -(y : Y) := rfl

theorem mvDiag_injective (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Function.Injective (mvDiag L W Z) := by
  intro x y hxy
  refine Subtype.ext ?_
  have := congrArg (fun s : ↥(Submodule.map L W) × ↥(Submodule.map L Z) => ((s.1 : Y))) hxy
  simpa using this

/-- The addition map of the observed Mayer--Vietoris complex. -/
def mvAdd (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(Submodule.map L W) × ↥(Submodule.map L Z) →ₗ[K] ↥(Submodule.map L (W ⊔ Z)) :=
  LinearMap.codRestrict (Submodule.map L (W ⊔ Z))
    ((Submodule.map L W).subtype.coprod (Submodule.map L Z).subtype)
    (fun s => by
      rw [map_sup_eq]
      exact Submodule.add_mem _
        ((le_sup_left : Submodule.map L W ≤ _) s.1.2)
        ((le_sup_right : Submodule.map L Z ≤ _) s.2.2))

@[simp] theorem mvAdd_coe (L : V →ₗ[K] Y) (W Z : Submodule K V)
    (s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)) :
    ((mvAdd L W Z s : ↥(Submodule.map L (W ⊔ Z))) : Y) = (s.1 : Y) + (s.2 : Y) := rfl

theorem mvAdd_surjective (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Function.Surjective (mvAdd L W Z) := by
  intro y
  have hy : (y : Y) ∈ Submodule.map L W ⊔ Submodule.map L Z := by
    rw [← map_sup_eq]
    exact y.2
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hy
  exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), Subtype.ext hpq⟩

theorem range_mvDiag_le_ker_mvAdd (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    LinearMap.range (mvDiag L W Z) ≤ LinearMap.ker (mvAdd L W Z) := by
  rintro s ⟨y, rfl⟩
  rw [LinearMap.mem_ker]
  refine Subtype.ext ?_
  rw [mvAdd_coe, mvDiag_fst, mvDiag_snd]
  show (y : Y) + -(y : Y) = 0
  rw [add_neg_cancel]

/-- The middle chart map of the observed Mayer--Vietoris complex. -/
def mvMiddle (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    ↥(LinearMap.ker (mvAdd L W Z)) →ₗ[K] ObserverOverlap L W Z :=
  (Submodule.comap (overlapNum L W Z).subtype (overlapDen L W Z)).mkQ.comp
    (LinearMap.codRestrict (overlapNum L W Z)
      ((Submodule.map L W).subtype.comp
        ((LinearMap.fst K ↥(Submodule.map L W) ↥(Submodule.map L Z)).comp
          (LinearMap.ker (mvAdd L W Z)).subtype))
      (fun s => by
        refine ⟨(s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1.2, ?_⟩
        have h0 : (mvAdd L W Z (s : ↥(Submodule.map L W) × ↥(Submodule.map L Z))) = 0 := s.2
        have hz : ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) + ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).2 : Y) = 0 := congrArg Subtype.val h0
        have he : ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) = -((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).2 : Y) := by
          linear_combination (norm := abel) hz
        show ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) ∈ Submodule.map L Z
        rw [he]
        exact Submodule.neg_mem _ (s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).2.2))

theorem mvMiddle_surjective (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    Function.Surjective (mvMiddle L W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ y => ?_
  have hker : mvAdd L W Z (⟨(y : Y), y.2.1⟩, ⟨-(y : Y), Submodule.neg_mem _ y.2.2⟩) = 0 := by
    refine Subtype.ext ?_
    rw [mvAdd_coe]
    show (y : Y) + -(y : Y) = 0
    rw [add_neg_cancel]
  refine ⟨⟨(⟨(y : Y), y.2.1⟩, ⟨-(y : Y), Submodule.neg_mem _ y.2.2⟩), hker⟩, ?_⟩
  show Submodule.Quotient.mk (⟨(y : Y), _⟩ : ↥(overlapNum L W Z)) = Submodule.Quotient.mk y
  congr 1

theorem ker_mvMiddle (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    LinearMap.ker (mvMiddle L W Z)
      = Submodule.comap (LinearMap.ker (mvAdd L W Z)).subtype
        (LinearMap.range (mvDiag L W Z)) := by
  ext s
  constructor
  · intro hs
    have h0 : Submodule.Quotient.mk (⟨((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y), _⟩ : ↥(overlapNum L W Z))
        = (0 : ObserverOverlap L W Z) := hs
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) ∈ overlapDen L W Z := h0
    have hzero : (mvAdd L W Z (s : ↥(Submodule.map L W) × ↥(Submodule.map L Z))) = 0 := s.2
    have hz : ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) + ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).2 : Y) = 0 := congrArg Subtype.val hzero
    refine ⟨⟨((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y), hmem⟩, ?_⟩
    refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
    show -(((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y))
      = ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).2 : Y)
    linear_combination (norm := abel) -hz
  · rintro ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (⟨((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y), _⟩ : ↥(overlapNum L W Z))
      = (0 : ObserverOverlap L W Z)
    rw [Submodule.Quotient.mk_eq_zero]
    have hfst : ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) = (y : Y) := by
      rw [← mvDiag_fst L W Z y, hy]
      rfl
    show ((s : ↥(Submodule.map L W) × ↥(Submodule.map L Z)).1 : Y) ∈ overlapDen L W Z
    rw [hfst]
    exact y.2

/-- **Theorem 3.5 `(TFIM.13e)`.**  Degreewise observation of the Mayer--Vietoris sequence of two
subspaces creates exactly the formation charge as middle homology. -/
def mvMiddleHomologyEquiv (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    (↥(LinearMap.ker (mvAdd L W Z)) ⧸
        Submodule.comap (LinearMap.ker (mvAdd L W Z)).subtype (LinearMap.range (mvDiag L W Z)))
      ≃ₗ[K] ObserverOverlap L W Z :=
  (Submodule.quotEquivOfEq _ _ (ker_mvMiddle L W Z).symm).trans
    ((mvMiddle L W Z).quotKerEquivOfSurjective (mvMiddle_surjective L W Z))

end Observer

/-! ## Rank identities -/

section Ranks

variable [FiniteDimensional K V]

theorem finrank_formationCharge_add (U W Z : Submodule K V) :
    Module.finrank K (FormationCharge U W Z) + Module.finrank K (formationBoundary U W Z)
      = Module.finrank K (formationCore U W Z) := by
  have h := Submodule.finrank_quotient_add_finrank (formationBoundaryInCore U W Z)
  have he := finrank_formationBoundaryInCore U W Z
  have hb : Module.finrank K (↥(formationCore U W Z) ⧸ formationBoundaryInCore U W Z)
      = Module.finrank K (FormationCharge U W Z) := rfl
  omega

/-- **`(TFIM.20)`.**  The exact local-loss plus generated-loss budget. -/
theorem finrank_formationCore_eq (U W Z : Submodule K V) :
    (Module.finrank K (formationCore U W Z) : ℤ)
      = (Module.finrank K ↥(U ⊓ W) : ℤ) + (Module.finrank K ↥(U ⊓ Z) : ℤ)
        - (Module.finrank K ↥(U ⊓ W ⊓ Z) : ℤ)
        + (Module.finrank K (FormationCharge U W Z) : ℤ) := by
  have h1 := finrank_formationCharge_add U W Z
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ W) (U ⊓ Z)
  have h3 : (U ⊓ W) ⊓ (U ⊓ Z) = U ⊓ W ⊓ Z := by
    ext x
    constructor
    · rintro ⟨⟨hu, hw⟩, -, hz⟩
      exact ⟨⟨hu, hw⟩, hz⟩
    · rintro ⟨⟨hu, hw⟩, hz⟩
      exact ⟨⟨hu, hw⟩, hu, hz⟩
  rw [h3] at h2
  have h4 : formationBoundary U W Z = (U ⊓ W) ⊔ (U ⊓ Z) := rfl
  rw [h4] at h1
  omega

variable {Y : Type*} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

/-- **Corollary 3.4 `(TFIM.13b)`, rank form.**  Formation homology is the submodularity slack of
observer rank. -/
theorem finrank_formationCharge_eq_rank_slack (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    (Module.finrank K (FormationCharge (LinearMap.ker L) W Z) : ℤ)
      = (Module.finrank K ↥(Submodule.map L W) : ℤ)
        + (Module.finrank K ↥(Submodule.map L Z) : ℤ)
        - (Module.finrank K ↥(Submodule.map L (W ⊔ Z)) : ℤ)
        - (Module.finrank K ↥(Submodule.map L (W ⊓ Z)) : ℤ) := by
  have hiso : Module.finrank K (FormationCharge (LinearMap.ker L) W Z)
      = overlapRank L W Z :=
    (formationChargeEquivObserverOverlap L W Z).finrank_eq
  rw [hiso]
  exact overlapRank_eq_slack L W Z

/-- **Corollary 3.4 `(TFIM.13b)`, nullity form.**  Equivalently, it is the supermodularity slack
of observer nullity. -/
theorem finrank_formationCharge_eq_nullity_slack (L : V →ₗ[K] Y) (W Z : Submodule K V) :
    (Module.finrank K (FormationCharge (LinearMap.ker L) W Z) : ℤ)
      = (Module.finrank K ↥((W ⊔ Z) ⊓ LinearMap.ker L) : ℤ)
        + (Module.finrank K ↥((W ⊓ Z) ⊓ LinearMap.ker L) : ℤ)
        - (Module.finrank K ↥(W ⊓ LinearMap.ker L) : ℤ)
        - (Module.finrank K ↥(Z ⊓ LinearMap.ker L) : ℤ) := by
  have hslack := finrank_formationCharge_eq_rank_slack L W Z
  have hgen : ∀ A : Submodule K V, Module.finrank K ↥(Submodule.map L A)
      + Module.finrank K ↥(A ⊓ LinearMap.ker L) = Module.finrank K A := by
    intro A
    have hrn := (L.domRestrict A).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrn
    have hEq : Module.finrank K ((LinearMap.ker L).comap A.subtype)
        = Module.finrank K ↥(A ⊓ LinearMap.ker L) := by
      rw [← Submodule.map_comap_subtype A (LinearMap.ker L)]
      exact (Submodule.equivMapOfInjective A.subtype (Submodule.injective_subtype A) _).finrank_eq
    rw [hEq] at hrn
    exact hrn
  have hW := hgen W
  have hZ := hgen Z
  have hS := hgen (W ⊔ Z)
  have hI := hgen (W ⊓ Z)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W Z
  omega

end Ranks

/-! ## The reduced fusion complex (Theorem 4.1) -/

section ReducedFusion

variable (U W Z : Submodule K V)

/-- Degree-two chains of the reduced fusion complex: pre-existing overlap. -/
abbrev RedTwo : Type _ := ↥(W ⊓ Z) ⧸ Submodule.comap (W ⊓ Z).subtype (U ⊓ W ⊓ Z)

/-- Degree-one chains: the two legs reduced by the common recovery kernel. -/
abbrev RedOne : Type _ :=
  (↥W ⧸ Submodule.comap W.subtype (U ⊓ W)) × (↥Z ⧸ Submodule.comap Z.subtype (U ⊓ Z))

/-- Degree-zero chains: the fused carrier reduced after formation. -/
abbrev RedZero : Type _ := ↥(U ⊔ W ⊔ Z) ⧸ Submodule.comap (U ⊔ W ⊔ Z).subtype U

/-- The leg-to-fusion map on the `W` side. -/
def redLegW : (↥W ⧸ Submodule.comap W.subtype (U ⊓ W)) →ₗ[K] RedZero U W Z :=
  Submodule.liftQ _
    ((Submodule.comap (U ⊔ W ⊔ Z).subtype U).mkQ.comp
      (LinearMap.codRestrict (U ⊔ W ⊔ Z) W.subtype
        fun w => (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z) ((le_sup_right : W ≤ U ⊔ W) w.2)))
    (by
      intro w hw
      show Submodule.Quotient.mk (⟨(w : V), _⟩ : ↥(U ⊔ W ⊔ Z)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hw.1)

/-- The leg-to-fusion map on the `Z` side. -/
def redLegZ : (↥Z ⧸ Submodule.comap Z.subtype (U ⊓ Z)) →ₗ[K] RedZero U W Z :=
  Submodule.liftQ _
    ((Submodule.comap (U ⊔ W ⊔ Z).subtype U).mkQ.comp
      (LinearMap.codRestrict (U ⊔ W ⊔ Z) Z.subtype
        fun z => (le_sup_right : Z ≤ U ⊔ W ⊔ Z) z.2))
    (by
      intro z hz
      show Submodule.Quotient.mk (⟨(z : V), _⟩ : ↥(U ⊔ W ⊔ Z)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hz.1)

/-- The degree-one differential of the reduced fusion complex. -/
def redD1 : RedOne U W Z →ₗ[K] RedZero U W Z := (redLegW U W Z).coprod (redLegZ U W Z)

/-- The degree-two differential of the reduced fusion complex. -/
def redD2 : RedTwo U W Z →ₗ[K] RedOne U W Z :=
  Submodule.liftQ _
    (((Submodule.comap W.subtype (U ⊓ W)).mkQ.comp
        (Submodule.inclusion (inf_le_left : W ⊓ Z ≤ W))).prod
      (-((Submodule.comap Z.subtype (U ⊓ Z)).mkQ.comp
        (Submodule.inclusion (inf_le_right : W ⊓ Z ≤ Z)))))
    (by
      intro a ha
      refine Prod.ext ?_ ?_
      · show Submodule.Quotient.mk (⟨(a : V), _⟩ : ↥W) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨ha.1.1, ha.1.2⟩
      · show -Submodule.Quotient.mk (⟨(a : V), _⟩ : ↥Z) = 0
        rw [neg_eq_zero, Submodule.Quotient.mk_eq_zero]
        exact ⟨ha.1.1, ha.2⟩)

theorem redD2_injective : Function.Injective (redD2 U W Z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  induction q using Submodule.Quotient.induction_on with | _ a => ?_
  have h0 : redD2 U W Z (Submodule.Quotient.mk a) = 0 := hq
  have h1 : (Submodule.Quotient.mk (⟨(a : V), (inf_le_left : W ⊓ Z ≤ W) a.2⟩ : ↥W)
      : ↥W ⧸ Submodule.comap W.subtype (U ⊓ W)) = 0 := congrArg Prod.fst h0
  rw [Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨⟨h1.1, a.2.1⟩, a.2.2⟩

theorem redD1_surjective : Function.Surjective (redD1 U W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp x.2
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hp
  have hwmem : w ∈ U ⊔ W ⊔ Z :=
    (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z) ((le_sup_right : W ≤ U ⊔ W) hw)
  have hzmem : z ∈ U ⊔ W ⊔ Z := (le_sup_right : Z ≤ U ⊔ W ⊔ Z) hz
  refine ⟨(Submodule.Quotient.mk ⟨w, hw⟩, Submodule.Quotient.mk ⟨z, hz⟩), ?_⟩
  show (Submodule.Quotient.mk (⟨w, hwmem⟩ : ↥(U ⊔ W ⊔ Z)) : RedZero U W Z)
    + Submodule.Quotient.mk (⟨z, hzmem⟩ : ↥(U ⊔ W ⊔ Z)) = Submodule.Quotient.mk x
  rw [← Submodule.Quotient.mk_add]
  refine (Submodule.Quotient.eq _).mpr ?_
  show w + z - (x : V) ∈ U
  have hx : (x : V) = u + w + z := by rw [← hpz, ← huw]
  rw [hx]
  have hneg : w + z - (u + w + z) = -u := by abel
  rw [hneg]
  exact Submodule.neg_mem _ hu

/-- Pairs of leg vectors whose sum lies in the common recovery kernel. -/
def redPairs : Submodule K (↥W × ↥Z) := Submodule.comap (W.subtype.coprod Z.subtype) U

theorem redPairs_mem (t : ↥(redPairs U W Z)) :
    ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V) ∈ U := t.2

/-- Such a pair forms a direction of the ternary core. -/
def redPairToCore : ↥(redPairs U W Z) →ₗ[K] ↥(formationCore U W Z) :=
  LinearMap.codRestrict (formationCore U W Z)
    ((W.subtype.coprod Z.subtype).comp (redPairs U W Z).subtype)
    (fun t => ⟨redPairs_mem U W Z t, Submodule.add_mem _
      ((le_sup_left : W ≤ W ⊔ Z) (t : ↥W × ↥Z).1.2)
      ((le_sup_right : Z ≤ W ⊔ Z) (t : ↥W × ↥Z).2.2)⟩)

/-- Such a pair is a cycle of the reduced fusion complex. -/
def redPairToCycle : ↥(redPairs U W Z) →ₗ[K] ↥(LinearMap.ker (redD1 U W Z)) :=
  LinearMap.codRestrict (LinearMap.ker (redD1 U W Z))
    ((((Submodule.comap W.subtype (U ⊓ W)).mkQ.comp (LinearMap.fst K ↥W ↥Z)).prod
      ((Submodule.comap Z.subtype (U ⊓ Z)).mkQ.comp (LinearMap.snd K ↥W ↥Z))).comp
        (redPairs U W Z).subtype)
    (fun t => by
      have hmem : ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V) ∈ U := redPairs_mem U W Z t
      have hw : ((t : ↥W × ↥Z).1 : V) ∈ U ⊔ W ⊔ Z :=
        (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z) ((le_sup_right : W ≤ U ⊔ W) (t : ↥W × ↥Z).1.2)
      have hz : ((t : ↥W × ↥Z).2 : V) ∈ U ⊔ W ⊔ Z :=
        (le_sup_right : Z ≤ U ⊔ W ⊔ Z) (t : ↥W × ↥Z).2.2
      rw [LinearMap.mem_ker]
      show (Submodule.Quotient.mk (⟨((t : ↥W × ↥Z).1 : V), hw⟩ : ↥(U ⊔ W ⊔ Z))
          : RedZero U W Z)
        + Submodule.Quotient.mk (⟨((t : ↥W × ↥Z).2 : V), hz⟩ : ↥(U ⊔ W ⊔ Z)) = 0
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
      exact hmem)

/-- The `U`-chart map from unobserved pairs. -/
def redPairCharge : ↥(redPairs U W Z) →ₗ[K] FormationCharge U W Z :=
  (formationBoundaryInCore U W Z).mkQ.comp (redPairToCore U W Z)

/-- The homology map from unobserved pairs. -/
def redPairHomology : ↥(redPairs U W Z) →ₗ[K]
    (↥(LinearMap.ker (redD1 U W Z)) ⧸
      Submodule.comap (LinearMap.ker (redD1 U W Z)).subtype
        (LinearMap.range (redD2 U W Z))) :=
  (Submodule.comap (LinearMap.ker (redD1 U W Z)).subtype
    (LinearMap.range (redD2 U W Z))).mkQ.comp (redPairToCycle U W Z)

theorem redPairCharge_surjective : Function.Surjective (redPairCharge U W Z) := by
  intro q
  induction q using Submodule.Quotient.induction_on with | _ x => ?_
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp x.2.2
  have hmem : ((⟨w, hw⟩ : ↥W) : V) + ((⟨z, hz⟩ : ↥Z) : V) ∈ U := by
    show w + z ∈ U
    rw [hwz]
    exact x.2.1
  refine ⟨⟨(⟨w, hw⟩, ⟨z, hz⟩), hmem⟩, ?_⟩
  show Submodule.Quotient.mk (redPairToCore U W Z _) = Submodule.Quotient.mk x
  congr 1
  exact Subtype.ext hwz

theorem redPairToCycle_surjective : Function.Surjective (redPairToCycle U W Z) := by
  intro c
  obtain ⟨w, hw⟩ := (Submodule.comap W.subtype (U ⊓ W)).mkQ_surjective (c : RedOne U W Z).1
  obtain ⟨z, hz⟩ := (Submodule.comap Z.subtype (U ⊓ Z)).mkQ_surjective (c : RedOne U W Z).2
  have hker : (redD1 U W Z) (c : RedOne U W Z) = 0 := c.2
  have hwmem : ((w : V)) ∈ U ⊔ W ⊔ Z :=
    (le_sup_left : U ⊔ W ≤ U ⊔ W ⊔ Z) ((le_sup_right : W ≤ U ⊔ W) w.2)
  have hzmem : ((z : V)) ∈ U ⊔ W ⊔ Z := (le_sup_right : Z ≤ U ⊔ W ⊔ Z) z.2
  have hsum : (Submodule.Quotient.mk (⟨(w : V), hwmem⟩ : ↥(U ⊔ W ⊔ Z)) : RedZero U W Z)
      + Submodule.Quotient.mk (⟨(z : V), hzmem⟩ : ↥(U ⊔ W ⊔ Z)) = 0 := by
    have hc : (c : RedOne U W Z) = (Submodule.Quotient.mk w, Submodule.Quotient.mk z) :=
      Prod.ext hw.symm hz.symm
    rw [hc] at hker
    exact hker
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero] at hsum
  have hmem : ((w : V)) + ((z : V)) ∈ U := hsum
  refine ⟨⟨(w, z), hmem⟩, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact hw
  · exact hz

theorem ker_redPairCharge_eq_ker_redPairHomology :
    LinearMap.ker (redPairCharge U W Z) = LinearMap.ker (redPairHomology U W Z) := by
  ext t
  constructor
  · intro ht
    have h0 : Submodule.Quotient.mk (redPairToCore U W Z t)
        = (0 : FormationCharge U W Z) := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    have hmem : ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V)
        ∈ formationBoundary U W Z := h0
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hmem
    have haWZ : ((t : ↥W × ↥Z).1 : V) - p ∈ W ⊓ Z := by
      constructor
      · exact Submodule.sub_mem _ (t : ↥W × ↥Z).1.2 hp.2
      · have he : ((t : ↥W × ↥Z).1 : V) - p = q - ((t : ↥W × ↥Z).2 : V) := by
          linear_combination (norm := abel) -hpq
        rw [he]
        exact Submodule.sub_mem _ hq.2 (t : ↥W × ↥Z).2.2
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (redPairToCycle U W Z t) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk ⟨((t : ↥W × ↥Z).1 : V) - p, haWZ⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · show Submodule.Quotient.mk (⟨((t : ↥W × ↥Z).1 : V) - p, haWZ.1⟩ : ↥W)
        = Submodule.Quotient.mk ((t : ↥W × ↥Z).1)
      refine (Submodule.Quotient.eq _).mpr ?_
      show (((t : ↥W × ↥Z).1 : V) - p) - ((t : ↥W × ↥Z).1 : V) ∈ U ⊓ W
      have hn : (((t : ↥W × ↥Z).1 : V) - p) - ((t : ↥W × ↥Z).1 : V) = -p := by abel
      rw [hn]
      exact Submodule.neg_mem _ hp
    · show -Submodule.Quotient.mk (⟨((t : ↥W × ↥Z).1 : V) - p, haWZ.2⟩ : ↥Z)
        = Submodule.Quotient.mk ((t : ↥W × ↥Z).2)
      rw [← Submodule.Quotient.mk_neg]
      refine (Submodule.Quotient.eq _).mpr ?_
      show (-(((t : ↥W × ↥Z).1 : V) - p)) - ((t : ↥W × ↥Z).2 : V) ∈ U ⊓ Z
      have hn : (-(((t : ↥W × ↥Z).1 : V) - p)) - ((t : ↥W × ↥Z).2 : V) = -q := by
        linear_combination (norm := abel) hpq
      rw [hn]
      exact Submodule.neg_mem _ hq
  · intro ht
    have h0 : Submodule.Quotient.mk (redPairToCycle U W Z t) = 0 := ht
    rw [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨d, hd⟩ := h0
    induction d using Submodule.Quotient.induction_on with | _ a => ?_
    have h1 : Submodule.Quotient.mk (⟨(a : V), (inf_le_left : W ⊓ Z ≤ W) a.2⟩ : ↥W)
        = Submodule.Quotient.mk ((t : ↥W × ↥Z).1) := congrArg Prod.fst hd
    have h2 : -Submodule.Quotient.mk (⟨(a : V), (inf_le_right : W ⊓ Z ≤ Z) a.2⟩ : ↥Z)
        = Submodule.Quotient.mk ((t : ↥W × ↥Z).2) := congrArg Prod.snd hd
    rw [← Submodule.Quotient.mk_neg] at h2
    have hp : (a : V) - ((t : ↥W × ↥Z).1 : V) ∈ U ⊓ W := by
      have hh := (Submodule.Quotient.eq _).mp h1
      exact hh
    have hq : (-(a : V)) - ((t : ↥W × ↥Z).2 : V) ∈ U ⊓ Z := by
      have hh := (Submodule.Quotient.eq _).mp h2
      exact hh
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (redPairToCore U W Z t) = (0 : FormationCharge U W Z)
    rw [Submodule.Quotient.mk_eq_zero]
    show ((t : ↥W × ↥Z).1 : V) + ((t : ↥W × ↥Z).2 : V) ∈ formationBoundary U W Z
    refine Submodule.mem_sup.mpr ⟨-((a : V) - ((t : ↥W × ↥Z).1 : V)), Submodule.neg_mem _ hp,
      -((-(a : V)) - ((t : ↥W × ↥Z).2 : V)), Submodule.neg_mem _ hq, ?_⟩
    abel

/-- **Theorem 4.1 `(TFIM.17)`.**  The first homology of the reduced fusion complex is the
formation charge. -/
def redHomologyEquiv :
    (↥(LinearMap.ker (redD1 U W Z)) ⧸
        Submodule.comap (LinearMap.ker (redD1 U W Z)).subtype
          (LinearMap.range (redD2 U W Z)))
      ≃ₗ[K] FormationCharge U W Z := by
  have hsurj : Function.Surjective (redPairHomology U W Z) := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ c => ?_
    obtain ⟨t, ht⟩ := redPairToCycle_surjective U W Z c
    exact ⟨t, by
      show Submodule.Quotient.mk (redPairToCycle U W Z t) = Submodule.Quotient.mk c
      rw [ht]⟩
  exact (((redPairHomology U W Z).quotKerEquivOfSurjective hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _
      (ker_redPairCharge_eq_ker_redPairHomology U W Z).symm).trans
      ((redPairCharge U W Z).quotKerEquivOfSurjective (redPairCharge_surjective U W Z))))

end ReducedFusion

end

end GaloisForLFunctions.HTGeometry
