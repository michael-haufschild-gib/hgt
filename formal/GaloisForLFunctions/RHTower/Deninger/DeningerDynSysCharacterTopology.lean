import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCharacterPoints
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The topology on the character points of an arbitrary scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §7, Lemmas 7.1 (`t7`)
and 7.2 (`t8`).

For an affine scheme the space `X̂ (C)` carries the topology of pointwise convergence.  For a
general scheme Deninger declares a subset of `X̂ (C)` open exactly when its trace on the points
lying over every affine open is open there.  This is the supremum, in the lattice of topologies, of
the topologies coinduced by the inclusions of those traces, and that is the definition used here.

With it the projection `X̂ (C) → X` is continuous: over an affine open the preimage of an open set
is the union of the loci where a section is invertible, and those are exactly the loci where the
corresponding evaluation is nonzero.  Consequently the points lying over any open subset form an
open subset of `X̂ (C)`, which is Lemma 7.2.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C]

open scoped Classical in
/-- A character of the units of a field, extended by zero. -/
noncomputable def deningerUnitExtend {k : Type u} [Field k] (χ : kˣ →* Cˣ) (a : k) : C :=
  if h : a = 0 then 0 else ((χ (Units.mk0 a h) : Cˣ) : C)

theorem deningerUnitExtend_eq_zero_iff {k : Type u} [Field k] (χ : kˣ →* Cˣ) (a : k) :
    deningerUnitExtend χ a = 0 ↔ a = 0 := by
  classical
  rw [deningerUnitExtend]
  by_cases h : a = 0
  · simp [h]
  · simp [h, Units.ne_zero]

theorem deningerUnitExtend_pow {k : Type u} [Field k] (χ : kˣ →* Cˣ) (a : k) {ν : ℕ}
    (hν : 0 < ν) : deningerUnitExtend (χ ^ ν) a = deningerUnitExtend χ a ^ ν := by
  classical
  rw [deningerUnitExtend, deningerUnitExtend]
  by_cases h : a = 0
  · simp [h, zero_pow hν.ne']
  · rw [dif_neg h, dif_neg h, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]

open scoped Classical in
/-- The value of a character point at a section over an open subset containing it, extended by
zero where the section vanishes or the point does not lie over the open subset. -/
noncomputable def deningerCharEval (U : X.Opens) (f : Γ(X, U)) (P : DeningerCharPoints X C) : C :=
  if h : P.1 ∈ U then deningerUnitExtend P.2 (X.evaluation U P.1 h f) else 0

theorem deningerCharEval_ne_zero_iff (U : X.Opens) (f : Γ(X, U))
    (P : DeningerCharPoints X C) (h : P.1 ∈ U) :
    deningerCharEval U f P ≠ 0 ↔ P.1 ∈ X.basicOpen f := by
  classical
  rw [deningerCharEval, dif_pos h, Ne, deningerUnitExtend_eq_zero_iff,
    X.evaluation_eq_zero_iff_notMem_basicOpen P.1 h f, not_not]

variable [TopologicalSpace C]

/-- The character points lying over an open subset, as a type in its own right so that it can
carry the topology of pointwise convergence of the sections over that open subset. -/
def DeningerCharOver (X : Scheme.{u}) (C : Type u) [Field C] (U : X.Opens) : Type u :=
  {P : DeningerCharPoints X C // P.1 ∈ U}

/-- The underlying character point. -/
def DeningerCharOver.val {U : X.Opens} (P : DeningerCharOver X C U) : DeningerCharPoints X C :=
  P.1

omit [TopologicalSpace C] in
theorem DeningerCharOver.mem {U : X.Opens} (P : DeningerCharOver X C U) : P.val.1 ∈ U := P.2

/-- The topology of pointwise convergence on the character points over an open subset. -/
noncomputable instance deningerCharOverTopology (U : X.Opens) :
    TopologicalSpace (DeningerCharOver X C U) :=
  TopologicalSpace.induced
    (fun P : DeningerCharOver X C U => fun f : Γ(X, U) => deningerCharEval U f P.val) inferInstance

/-- **Deninger, §7.**  The topology on `X̂ (C)`: a subset is open exactly when its trace on the
points lying over every affine open is open for pointwise convergence there. -/
noncomputable instance deningerCharPointsTopology : TopologicalSpace (DeningerCharPoints X C) :=
  ⨆ U : X.affineOpens, TopologicalSpace.coinduced
    (DeningerCharOver.val (X := X) (C := C) (U := U.1)) (deningerCharOverTopology U.1)

theorem deningerCharPoints_isOpen_iff (s : Set (DeningerCharPoints X C)) :
    IsOpen s ↔ ∀ U : X.affineOpens,
      IsOpen (DeningerCharOver.val (X := X) (C := C) (U := U.1) ⁻¹' s) := by
  constructor
  · intro hs U
    exact isOpen_coinduced.1 (isOpen_iSup_iff.1 hs U)
  · intro h
    exact isOpen_iSup_iff.2 fun U => isOpen_coinduced.2 (h U)

theorem deningerCharEval_continuous (U : X.Opens) (f : Γ(X, U)) :
    Continuous fun P : DeningerCharOver X C U => deningerCharEval U f P.val := by
  have h1 : Continuous
      (fun P : DeningerCharOver X C U => fun g : Γ(X, U) => deningerCharEval U g P.val) :=
    continuous_induced_dom
  exact (continuous_apply f).comp h1

/-- **Deninger, Lemma 7.1 (`t7`), for an arbitrary scheme.**  The projection `X̂ (C) → X` is
continuous. -/
theorem deningerCharPointsProj_continuous [T1Space C] :
    Continuous (fun P : DeningerCharPoints X C => P.1) := by
  rw [continuous_iSup_dom]
  intro U
  rw [continuous_coinduced_dom, continuous_def]
  intro W hW
  have hset : ((fun P : DeningerCharPoints X C => P.1) ∘
        (DeningerCharOver.val (X := X) (C := C) (U := U.1))) ⁻¹' W
      = ⋃ f : {f : Γ(X, U.1) // X.basicOpen f ≤ ⟨W, hW⟩},
          {P : DeningerCharOver X C U.1 | deningerCharEval U.1 f.1 P.val ≠ 0} := by
    ext P
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · intro hP
      obtain ⟨f, hf1, hf2⟩ :=
        U.2.exists_basicOpen_le (V := ⟨W, hW⟩) ⟨P.val.1, hP⟩ P.mem
      exact ⟨⟨f, hf1⟩, (deningerCharEval_ne_zero_iff U.1 f P.val P.mem).2 hf2⟩
    · rintro ⟨f, hf⟩
      exact f.2 ((deningerCharEval_ne_zero_iff U.1 f.1 P.val P.mem).1 hf)
  rw [hset]
  refine isOpen_iUnion fun f => ?_
  exact (deningerCharEval_continuous U.1 f.1).isOpen_preimage {c : C | c ≠ 0}
    (isOpen_compl_iff.2 (isClosed_singleton (x := (0 : C))))

/-- **Deninger, Lemma 7.2 (`t8`).**  The character points lying over an open subset form an open
subset of `X̂ (C)`. -/
theorem deningerCharOver_isOpen [T1Space C] (U : X.Opens) :
    IsOpen {P : DeningerCharPoints X C | P.1 ∈ U} :=
  deningerCharPointsProj_continuous.isOpen_preimage (U : Set X) U.isOpen

/-- The inclusion of the character points over an affine open is continuous. -/
theorem deningerCharOverVal_continuous (U : X.affineOpens) :
    Continuous (DeningerCharOver.val (X := X) (C := C) (U := U.1)) := by
  rw [continuous_def]
  intro s hs
  exact (deningerCharPoints_isOpen_iff s).1 hs U

/-! ### The Frobenius operators -/

omit [TopologicalSpace C] in
theorem deningerCharEval_frobenius (U : X.Opens) (f : Γ(X, U)) {ν : ℕ} (hν : 0 < ν)
    (P : DeningerCharPoints X C) :
    deningerCharEval U f (deningerCharFrobenius ν P) = deningerCharEval U f P ^ ν := by
  classical
  simp only [deningerCharEval, deningerCharFrobenius]
  by_cases h : P.1 ∈ U
  · rw [dif_pos h, dif_pos h]
    exact deningerUnitExtend_pow _ _ hν
  · rw [dif_neg h, dif_neg h, zero_pow hν.ne']

/-- The Frobenius operator preserves the points lying over an open subset. -/
noncomputable def deningerCharOverFrobenius (ν : ℕ) {U : X.Opens}
    (P : DeningerCharOver X C U) : DeningerCharOver X C U :=
  ⟨deningerCharFrobenius ν P.val, P.mem⟩

theorem deningerCharOverFrobenius_continuous [ContinuousMul C] {ν : ℕ} (hν : 0 < ν)
    (U : X.Opens) :
    Continuous (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun f => ?_
  have hfun : (fun P : DeningerCharOver X C U =>
      deningerCharEval U f (deningerCharOverFrobenius ν P).val)
      = fun P : DeningerCharOver X C U => deningerCharEval U f P.val ^ ν := by
    funext P
    exact deningerCharEval_frobenius U f hν P.val
  show Continuous fun P : DeningerCharOver X C U =>
    deningerCharEval U f (deningerCharOverFrobenius ν P).val
  rw [hfun]
  exact (continuous_pow ν).comp (deningerCharEval_continuous U f)

/-- **Deninger, Lemma 7.3 (`t9`), for an arbitrary scheme.**  The Frobenius operators on `X̂ (C)`
are continuous. -/
theorem deningerCharFrobenius_continuous [ContinuousMul C] {ν : ℕ} (hν : 0 < ν) :
    Continuous (deningerCharFrobenius (X := X) (C := C) ν) := by
  rw [continuous_iSup_dom]
  intro U
  rw [continuous_coinduced_dom]
  have hcomp : (deningerCharFrobenius (X := X) (C := C) ν) ∘
      (DeningerCharOver.val (X := X) (C := C) (U := U.1))
      = (DeningerCharOver.val (X := X) (C := C) (U := U.1)) ∘
        (deningerCharOverFrobenius ν) := rfl
  rw [hcomp]
  exact (deningerCharOverVal_continuous U).comp (deningerCharOverFrobenius_continuous hν U.1)

/-! ### Restriction to a smaller open subset -/

omit [TopologicalSpace C] in
theorem deningerUnitExtend_mul {k : Type u} [Field k] (χ : kˣ →* Cˣ) (a b : k) :
    deningerUnitExtend χ (a * b) = deningerUnitExtend χ a * deningerUnitExtend χ b := by
  classical
  by_cases ha : a = 0
  · simp [deningerUnitExtend, ha]
  by_cases hb : b = 0
  · simp [deningerUnitExtend, hb]
  rw [deningerUnitExtend, deningerUnitExtend, deningerUnitExtend, dif_neg ha, dif_neg hb,
    dif_neg (mul_ne_zero ha hb), ← Units.val_mul, ← map_mul]
  congr 2
  exact Units.ext rfl

omit [TopologicalSpace C] in
theorem deningerCharEval_mul (U : X.Opens) (f g : Γ(X, U)) (P : DeningerCharPoints X C) :
    deningerCharEval U (f * g) P = deningerCharEval U f P * deningerCharEval U g P := by
  classical
  rw [deningerCharEval, deningerCharEval, deningerCharEval]
  by_cases h : P.1 ∈ U
  · rw [dif_pos h, dif_pos h, dif_pos h, map_mul, deningerUnitExtend_mul]
  · rw [dif_neg h, dif_neg h, dif_neg h, mul_zero]

omit [TopologicalSpace C] in
/-- The evaluation of a character point does not change under restriction of the section. -/
theorem deningerCharEval_res {W U : X.Opens} (hWU : W ≤ U) (f : Γ(X, U))
    (P : DeningerCharPoints X C) (hP : P.1 ∈ W) :
    deningerCharEval W (X.presheaf.map (homOfLE hWU).op f) P = deningerCharEval U f P := by
  classical
  rw [deningerCharEval, deningerCharEval, dif_pos hP, dif_pos (hWU hP)]
  congr 1
  show X.residue P.1 (X.presheaf.germ W P.1 hP (X.presheaf.map (homOfLE hWU).op f))
    = X.residue P.1 (X.presheaf.germ U P.1 (hWU hP) f)
  rw [X.presheaf.germ_res_apply (homOfLE hWU) P.1 hP f]

/-- The inclusion of the points over a smaller open subset. -/
def DeningerCharOver.restrict {W U : X.Opens} (hWU : W ≤ U) (P : DeningerCharOver X C W) :
    DeningerCharOver X C U :=
  ⟨P.val, hWU P.mem⟩

theorem deningerCharOver_restrict_continuous {W U : X.Opens} (hWU : W ≤ U) :
    Continuous (DeningerCharOver.restrict (X := X) (C := C) hWU) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun f => ?_
  have hfun : (fun P : DeningerCharOver X C W =>
      deningerCharEval U f (DeningerCharOver.restrict hWU P).val)
      = fun P : DeningerCharOver X C W =>
        deningerCharEval W (X.presheaf.map (homOfLE hWU).op f) P.val := by
    funext P
    exact (deningerCharEval_res hWU f P.val P.mem).symm
  show Continuous fun P : DeningerCharOver X C W =>
    deningerCharEval U f (DeningerCharOver.restrict hWU P).val
  rw [hfun]
  exact deningerCharEval_continuous W _

/-! ### The affine traces are open subspaces -/

omit [TopologicalSpace C] in
theorem deningerCharEval_one (U : X.Opens) (P : DeningerCharPoints X C) (hP : P.1 ∈ U) :
    deningerCharEval U 1 P = 1 := by
  classical
  rw [deningerCharEval, dif_pos hP, map_one, deningerUnitExtend, dif_neg one_ne_zero]
  simp

omit [TopologicalSpace C] in
theorem deningerCharEval_pow (U : X.Opens) (f : Γ(X, U)) (n : ℕ)
    (P : DeningerCharPoints X C) (hP : P.1 ∈ U) :
    deningerCharEval U (f ^ n) P = deningerCharEval U f P ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, deningerCharEval_one U P hP]
  | succ k ih => rw [pow_succ, pow_succ, deningerCharEval_mul, ih]

/-- The points over a basic open subset of an affine open, topologized as a subspace of the
ambient affine trace. -/
def DeningerCharOverSub (X : Scheme.{u}) (C : Type u) [Field C] {U : X.Opens} (s : Γ(X, U)) :
    Type u := DeningerCharOver X C (X.basicOpen s)

/-- The two descriptions of the points over a basic open subset have the same underlying set. -/
def deningerCharOverSubEquiv {U : X.Opens} (s : Γ(X, U)) :
    DeningerCharOverSub X C s ≃ DeningerCharOver X C (X.basicOpen s) := Equiv.refl _

noncomputable instance deningerCharOverSubTopology {U : X.Opens} (s : Γ(X, U)) :
    TopologicalSpace (DeningerCharOverSub X C s) :=
  TopologicalSpace.induced
    (fun P : DeningerCharOverSub X C s =>
      DeningerCharOver.restrict (X.basicOpen_le s) (deningerCharOverSubEquiv s P))
    (deningerCharOverTopology U)

theorem deningerCharOverSub_continuous_toSub {U : X.Opens} (s : Γ(X, U)) :
    Continuous (fun P : DeningerCharOver X C (X.basicOpen s) =>
      (deningerCharOverSubEquiv s).symm P) := by
  rw [continuous_induced_rng]
  exact deningerCharOver_restrict_continuous (X.basicOpen_le s)

variable [ContinuousMul C] [ContinuousInv₀ C]

/-- **Deninger, Lemma 7.2 (`t8`), the localisation step.**  A section over a basic open subset
becomes, after multiplication by a power of the defining section, the restriction of a section
over the affine open; hence the topology of pointwise convergence over the basic open subset is
induced from the ambient affine trace. -/
theorem deningerCharOverSub_continuous_ofSub {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(X, U)) :
    Continuous (fun P : DeningerCharOverSub X C s => deningerCharOverSubEquiv s P) := by
  haveI := hU.isLocalization_basicOpen s
  rw [continuous_induced_rng]
  refine continuous_pi fun r' => ?_
  obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers s) r'
  obtain ⟨n, hn⟩ := m.2
  have hcoord : ∀ P : DeningerCharOverSub X C s,
      deningerCharEval (X.basicOpen s) r' (deningerCharOverSubEquiv s P).val
        = deningerCharEval U r ((deningerCharOverSubEquiv s P)).val *
          (deningerCharEval U s ((deningerCharOverSubEquiv s P)).val ^ n)⁻¹ := by
    intro P
    set Q : DeningerCharOver X C (X.basicOpen s) := deningerCharOverSubEquiv s P with hQ
    have hmemU : Q.val.1 ∈ U := X.basicOpen_le s Q.mem
    have hane : deningerCharEval U s Q.val ≠ 0 :=
      (deningerCharEval_ne_zero_iff U s Q.val hmemU).2 Q.mem
    have h1 := congrArg (fun z => deningerCharEval (X.basicOpen s) z Q.val) hrm
    simp only at h1
    rw [deningerCharEval_mul] at h1
    have h2 : deningerCharEval (X.basicOpen s)
        (algebraMap Γ(X, U) Γ(X, X.basicOpen s) (m : Γ(X, U))) Q.val
        = deningerCharEval U s Q.val ^ n := by
      rw [show (algebraMap Γ(X, U) Γ(X, X.basicOpen s) (m : Γ(X, U)))
          = X.presheaf.map (homOfLE (X.basicOpen_le s)).op (m : Γ(X, U)) from rfl,
        deningerCharEval_res _ _ _ Q.mem, ← hn, deningerCharEval_pow U s n Q.val hmemU]
    have h3 : deningerCharEval (X.basicOpen s)
        (algebraMap Γ(X, U) Γ(X, X.basicOpen s) r) Q.val = deningerCharEval U r Q.val := by
      rw [show (algebraMap Γ(X, U) Γ(X, X.basicOpen s) r)
          = X.presheaf.map (homOfLE (X.basicOpen_le s)).op r from rfl,
        deningerCharEval_res _ _ _ Q.mem]
    rw [h2, h3] at h1
    field_simp [pow_ne_zero n hane]
    linear_combination h1
  show Continuous fun P : DeningerCharOverSub X C s =>
    deningerCharEval (X.basicOpen s) r' (deningerCharOverSubEquiv s P).val
  simp only [hcoord]
  have hres : Continuous (fun P : DeningerCharOverSub X C s =>
      DeningerCharOver.restrict (X.basicOpen_le s) (deningerCharOverSubEquiv s P)) :=
    continuous_induced_dom
  have hr : Continuous (fun P : DeningerCharOverSub X C s =>
      deningerCharEval U r (deningerCharOverSubEquiv s P).val) :=
    (deningerCharEval_continuous U r).comp hres
  have hs : Continuous (fun P : DeningerCharOverSub X C s =>
      deningerCharEval U s (deningerCharOverSubEquiv s P).val) :=
    (deningerCharEval_continuous U s).comp hres
  exact hr.mul ((hs.pow n).inv₀ fun P =>
    pow_ne_zero n ((deningerCharEval_ne_zero_iff U s (deningerCharOverSubEquiv s P).val
      (X.basicOpen_le s (deningerCharOverSubEquiv s P).mem)).2
      (deningerCharOverSubEquiv s P).mem))

/-- The topology of pointwise convergence over a basic open subset of an affine open is induced
from the ambient affine trace. -/
theorem deningerCharOverTopology_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(X, U)) :
    deningerCharOverTopology (X := X) (C := C) (X.basicOpen s)
      = TopologicalSpace.induced
          (DeningerCharOver.restrict (X := X) (C := C) (X.basicOpen_le s))
          (deningerCharOverTopology U) := by
  refine le_antisymm
    (continuous_iff_le_induced.1 (deningerCharOver_restrict_continuous _)) ?_
  intro a ha
  exact (deningerCharOverSub_continuous_ofSub hU s).isOpen_preimage a ha

omit [TopologicalSpace C] [ContinuousMul C] [ContinuousInv₀ C] in
theorem deningerCharOver_range_restrict {U : X.Opens} (s : Γ(X, U)) :
    Set.range (DeningerCharOver.restrict (X := X) (C := C) (X.basicOpen_le s))
      = {Q : DeningerCharOver X C U | deningerCharEval U s Q.val ≠ 0} := by
  ext Q
  constructor
  · rintro ⟨P, rfl⟩
    exact (deningerCharEval_ne_zero_iff U s P.val (X.basicOpen_le s P.mem)).2 P.mem
  · intro hQ
    exact ⟨⟨Q.val, (deningerCharEval_ne_zero_iff U s Q.val Q.mem).1 hQ⟩, rfl⟩

omit [ContinuousMul C] [ContinuousInv₀ C] in
theorem deningerCharOver_isOpen_range_restrict [T1Space C] {U : X.Opens} (s : Γ(X, U)) :
    IsOpen (Set.range (DeningerCharOver.restrict (X := X) (C := C) (X.basicOpen_le s))) := by
  rw [deningerCharOver_range_restrict]
  exact (deningerCharEval_continuous U s).isOpen_preimage {c : C | c ≠ 0}
    (isOpen_compl_iff.2 (isClosed_singleton (x := (0 : C))))

theorem deningerCharOver_isOpenMap_restrict [T1Space C] {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(X, U)) :
    IsOpenMap (DeningerCharOver.restrict (X := X) (C := C) (X.basicOpen_le s)) := by
  intro a ha
  rw [deningerCharOverTopology_basicOpen hU s] at ha
  obtain ⟨b, hb, rfl⟩ := isOpen_induced_iff.1 ha
  rw [Set.image_preimage_eq_inter_range]
  exact hb.inter (deningerCharOver_isOpen_range_restrict s)

/-- **Deninger, Lemma 7.2 (`t8`).**  The inclusion of the character points over an affine open is
an open map. -/
theorem deningerCharOverVal_isOpenMap [T1Space C] (U : X.affineOpens) :
    IsOpenMap (DeningerCharOver.val (X := X) (C := C) (U := U.1)) := by
  intro a ha
  rw [deningerCharPoints_isOpen_iff]
  intro V
  have hcover : (DeningerCharOver.val (X := X) (C := C) (U := V.1)) ⁻¹'
      (DeningerCharOver.val (X := X) (C := C) (U := U.1) '' a)
      = ⋃ g : {g : Γ(X, V.1) // X.basicOpen g ≤ U.1},
          DeningerCharOver.restrict (X.basicOpen_le g.1) ''
            (DeningerCharOver.restrict (X := X) (C := C) g.2 ⁻¹' a) := by
    ext Q
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨P, hPa, hPQ⟩
      have hQU : Q.val.1 ∈ U.1 := hPQ ▸ P.mem
      obtain ⟨g, hg1, hg2⟩ := V.2.exists_basicOpen_le (V := U.1) ⟨Q.val.1, hQU⟩ Q.mem
      refine ⟨⟨g, hg1⟩, ⟨Q.val, hg2⟩, ?_, rfl⟩
      show DeningerCharOver.restrict hg1 ⟨Q.val, hg2⟩ ∈ a
      have : DeningerCharOver.restrict hg1 (⟨Q.val, hg2⟩ :
          DeningerCharOver X C (X.basicOpen g)) = P := Subtype.ext hPQ.symm
      rw [this]
      exact hPa
    · rintro ⟨g, R, hRa, hRQ⟩
      exact ⟨DeningerCharOver.restrict g.2 R, hRa, congrArg Subtype.val hRQ⟩
  rw [hcover]
  refine isOpen_iUnion fun g => ?_
  exact deningerCharOver_isOpenMap_restrict V.2 g.1 _
    ((deningerCharOver_restrict_continuous g.2).isOpen_preimage a ha)

/-- **Deninger, Lemma 7.2 (`t8`).**  The character points over an affine open form an open
subspace of `X̂ (C)`. -/
theorem deningerCharOverVal_isOpenEmbedding [T1Space C] (U : X.affineOpens) :
    Topology.IsOpenEmbedding (DeningerCharOver.val (X := X) (C := C) (U := U.1)) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (deningerCharOverVal_continuous U) (fun _ _ h => Subtype.ext h)
    (deningerCharOverVal_isOpenMap U)

end RHTower
