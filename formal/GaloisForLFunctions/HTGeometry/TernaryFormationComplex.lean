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

end Observer

end

end GaloisForLFunctions.HTGeometry
