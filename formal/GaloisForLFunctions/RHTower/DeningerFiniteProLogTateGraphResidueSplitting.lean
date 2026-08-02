import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Poincaré residue on a finite split pro-log Tate chart

On the finite split chart `D × ℂ` a logarithmic form has the unique normal decomposition
`ω = α + (dz/z) ∧ β`.  The Poincaré residue is `R ω = β|_{z = 0}` and the normal-form section is
`S γ = (dz/z) ∧ π_D^* γ`.  This module represents that data directly:

* `deningerResidue` and `deningerLogSection` are continuous linear maps for the compact-open
  topology, and `R ∘ S = 1`, so `R` is a continuous split surjection;
* `DeningerTransverseCore` is the graph core of a transverse generator `A`: fields whose every
  transverse monomial `A ^ m` stays continuous.  Both `R` and `S` preserve it and commute with
  every monomial;
* every target graph seminorm of `S γ` equals the corresponding source seminorm of `γ`, and every
  graph seminorm of `R ω` is bounded by the source seminorm on the normal zero locus;
* on a chart field holomorphic in the normal coordinate, Cauchy's estimate bounds every normal
  derivative of every transverse monomial at `z = 0` by its supremum on a normal circle;
* restriction to a finite packet `Y ⊆ D` is a continuous split surjection onto `Y → ℂ`, split by
  the interpolating idempotents supplied by Urysohn separation;
* continuous split surjections are stable under finite direct sums, so each finite relative cell
  built from the residue square inherits the splitting.
-/

namespace RHTower

open Metric Set

section Precomposition

variable {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Precomposition with a continuous map is continuous and linear for the compact-open topology. -/
def deningerPrecomp (f : C(X, Y)) : C(Y, V) →L[ℂ] C(X, V) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_precomp f

@[simp]
theorem deningerPrecomp_apply (f : C(X, Y)) (g : C(Y, V)) (x : X) :
    deningerPrecomp (V := V) f g x = g (f x) :=
  rfl

end Precomposition

section SplitChart

variable {D V : Type*} [TopologicalSpace D]
variable [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The normal zero section `x ↦ (x, 0)` of the split chart `D × ℂ`, i.e. the divisor
`D = D × {0}`. -/
def deningerNormalZeroSection : C(D, D × ℂ) :=
  ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

@[simp]
theorem deningerNormalZeroSection_apply (x : D) :
    (deningerNormalZeroSection (D := D)) x = (x, (0 : ℂ)) :=
  rfl

/-- The horizontal projection of the split chart `D × ℂ`. -/
def deningerChartProjection : C(D × ℂ, D) :=
  ⟨Prod.fst, continuous_fst⟩

@[simp]
theorem deningerChartProjection_apply (p : D × ℂ) :
    (deningerChartProjection (D := D)) p = p.1 :=
  rfl

/-- Logarithmic forms on the split chart, presented by the unique normal decomposition
`ω = α + (dz/z) ∧ β`: the first component is `α`, the second is `β`. -/
abbrev DeningerLogForms (D V : Type*) [TopologicalSpace D] [NormedAddCommGroup V]
    [NormedSpace ℂ V] : Type _ :=
  C(D × ℂ, V) × C(D × ℂ, V)

/-- Boundary forms on the divisor `D × {0}`. -/
abbrev DeningerBoundaryForms (D V : Type*) [TopologicalSpace D] [NormedAddCommGroup V]
    [NormedSpace ℂ V] : Type _ :=
  C(D, V)

/-- The Poincaré residue `ω = α + (dz/z) ∧ β ↦ β|_{z = 0}`, continuous and linear for the
compact-open topology. -/
noncomputable def deningerResidue : DeningerLogForms D V →L[ℂ] DeningerBoundaryForms D V :=
  (deningerPrecomp deningerNormalZeroSection).comp (ContinuousLinearMap.snd ℂ _ _)

@[simp]
theorem deningerResidue_apply (ω : DeningerLogForms D V) (x : D) :
    deningerResidue ω x = ω.2 (x, 0) :=
  rfl

/-- The normal-form section `γ ↦ (dz/z) ∧ π_D^* γ`, continuous and linear for the compact-open
topology. -/
noncomputable def deningerLogSection : DeningerBoundaryForms D V →L[ℂ] DeningerLogForms D V :=
  (0 : DeningerBoundaryForms D V →L[ℂ] C(D × ℂ, V)).prod
    (deningerPrecomp deningerChartProjection)

@[simp]
theorem deningerLogSection_fst (γ : DeningerBoundaryForms D V) :
    (deningerLogSection γ).1 = 0 :=
  rfl

@[simp]
theorem deningerLogSection_snd (γ : DeningerBoundaryForms D V) (p : D × ℂ) :
    (deningerLogSection γ).2 p = γ p.1 :=
  rfl

/-- `R S = 1`: the normal-form section splits the Poincaré residue. -/
theorem deningerResidue_comp_logSection :
    deningerResidue.comp (deningerLogSection (D := D) (V := V)) =
      ContinuousLinearMap.id ℂ (DeningerBoundaryForms D V) := by
  ext γ x
  rfl

/-- The Poincaré residue is a surjection, split by the normal-form section. -/
theorem deningerResidue_surjective :
    Function.Surjective (deningerResidue (D := D) (V := V)) := fun γ =>
  ⟨deningerLogSection γ,
    congrArg (fun T : DeningerBoundaryForms D V →L[ℂ] DeningerBoundaryForms D V => T γ)
      deningerResidue_comp_logSection⟩

end SplitChart

section TransverseGraph

variable {X V : Type*} [TopologicalSpace X]
variable [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A continuous transverse-source field lies in the graph core of the transverse generator `A`
when every transverse monomial `A ^ m` leaves it continuous.  For an unbounded generator this is a
proper condition; it is the analytic domain on which the graph seminorms `sup_K ‖A ^ m ω‖` are
defined. -/
def DeningerTransverseCore (A : Module.End ℂ V) (f : C(X, V)) : Prop :=
  ∀ m : ℕ, Continuous fun p : X => (A ^ m) (f p)

/-- The transverse monomial image of a graph-core field, again a continuous field. -/
def deningerTransverseMonomial (A : Module.End ℂ V) {f : C(X, V)}
    (hf : DeningerTransverseCore A f) (m : ℕ) : C(X, V) :=
  ⟨fun p => (A ^ m) (f p), hf m⟩

@[simp]
theorem deningerTransverseMonomial_apply (A : Module.End ℂ V) {f : C(X, V)}
    (hf : DeningerTransverseCore A f) (m : ℕ) (p : X) :
    deningerTransverseMonomial A hf m p = (A ^ m) (f p) :=
  rfl

/-- Precomposition with a continuous map preserves the transverse graph core. -/
theorem DeningerTransverseCore.precomp {Y : Type*} [TopologicalSpace Y]
    {A : Module.End ℂ V} {f : C(X, V)} (hf : DeningerTransverseCore A f) (u : C(Y, X)) :
    DeningerTransverseCore A (f.comp u) := fun m =>
  (hf m).comp u.continuous

/-- The zero field lies in every transverse graph core. -/
theorem deningerTransverseCore_zero (A : Module.End ℂ V) :
    DeningerTransverseCore A (0 : C(X, V)) := fun m => by
  simpa using (continuous_const : Continuous fun _ : X => (0 : V))

end TransverseGraph

section ResidueGraphCompatibility

variable {D V : Type*} [TopologicalSpace D]
variable [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {A : Module.End ℂ V}

/-- The Poincaré residue maps the transverse graph core of the polar part into the transverse
graph core of the boundary forms. -/
theorem deningerResidue_transverseCore {ω : DeningerLogForms D V}
    (h : DeningerTransverseCore A ω.2) :
    DeningerTransverseCore A (deningerResidue ω) :=
  h.precomp deningerNormalZeroSection

/-- The normal-form section maps the transverse graph core of the boundary forms into the
transverse graph core of both components of the log form. -/
theorem deningerLogSection_transverseCore {γ : DeningerBoundaryForms D V}
    (h : DeningerTransverseCore A γ) :
    DeningerTransverseCore A (deningerLogSection γ).1 ∧
      DeningerTransverseCore A (deningerLogSection γ).2 :=
  ⟨deningerTransverseCore_zero A, h.precomp deningerChartProjection⟩

/-- `R P = P R`: the residue commutes with every transverse graph monomial. -/
theorem deningerResidue_transverseMonomial_comm {ω : DeningerLogForms D V}
    (h : DeningerTransverseCore A ω.2) (m : ℕ) :
    deningerTransverseMonomial A (deningerResidue_transverseCore h) m =
      deningerResidue ((0 : C(D × ℂ, V)), deningerTransverseMonomial A h m) := by
  ext x
  rfl

/-- `S P = P S`: the normal-form section commutes with every transverse graph monomial. -/
theorem deningerLogSection_transverseMonomial_comm {γ : DeningerBoundaryForms D V}
    (h : DeningerTransverseCore A γ) (m : ℕ) :
    deningerTransverseMonomial A (deningerLogSection_transverseCore h).2 m =
      (deningerLogSection (deningerTransverseMonomial A h m)).2 := by
  ext p
  rfl

/-- The normal-form section carries every source graph seminorm to the identical target graph
seminorm: a lift with exactly the same transverse bound. -/
theorem deningerLogSection_graphSeminorm_le_iff {γ : DeningerBoundaryForms D V}
    (m : ℕ) (K : Set (D × ℂ)) (C : ℝ) :
    (∀ p ∈ K, ‖(A ^ m) ((deningerLogSection γ).2 p)‖ ≤ C) ↔
      ∀ x ∈ Prod.fst '' K, ‖(A ^ m) (γ x)‖ ≤ C := by
  constructor
  · rintro h x ⟨p, hp, rfl⟩
    exact h p hp
  · intro h p hp
    exact h p.1 ⟨p, hp, rfl⟩

/-- Every graph seminorm of the residue is bounded by the source graph seminorm on the normal zero
locus, with the same constant. -/
theorem deningerResidue_graphSeminorm_le {ω : DeningerLogForms D V}
    (m : ℕ) (K : Set D) (C : ℝ)
    (h : ∀ p ∈ (fun x : D => (x, (0 : ℂ))) '' K, ‖(A ^ m) (ω.2 p)‖ ≤ C) :
    ∀ x ∈ K, ‖(A ^ m) (deningerResidue ω x)‖ ≤ C := fun x hx =>
  h (x, 0) ⟨x, hx, rfl⟩

/-- The normal-form section is constant in the normal coordinate, so all its higher normal
derivatives vanish. -/
theorem deningerLogSection_iteratedDeriv_normal (γ : DeningerBoundaryForms D V)
    (x : D) {j : ℕ} (hj : j ≠ 0) (z : ℂ) :
    iteratedDeriv j (fun w : ℂ => (deningerLogSection γ).2 (x, w)) z = 0 := by
  have : (fun w : ℂ => (deningerLogSection γ).2 (x, w)) = fun _ : ℂ => γ x := rfl
  rw [this, iteratedDeriv_const, if_neg hj]

/-- **Split strictness on the common transverse graph cores.**  Every boundary form in the graph
core of the transverse generator is the Poincaré residue of a source log form that again lies in
the graph core, whose transverse graph seminorms are exactly the boundary ones, and whose higher
normal derivatives all vanish. -/
theorem deningerResidue_splitStrict_graphCore {γ : DeningerBoundaryForms D V}
    (h : DeningerTransverseCore A γ) :
    ∃ ω : DeningerLogForms D V,
      DeningerTransverseCore A ω.1 ∧ DeningerTransverseCore A ω.2 ∧
        deningerResidue ω = γ ∧
        (∀ (m : ℕ) (K : Set (D × ℂ)) (C : ℝ),
          (∀ p ∈ K, ‖(A ^ m) (ω.2 p)‖ ≤ C) ↔ ∀ x ∈ Prod.fst '' K, ‖(A ^ m) (γ x)‖ ≤ C) ∧
        ∀ (x : D) {j : ℕ}, j ≠ 0 → ∀ z : ℂ,
          iteratedDeriv j (fun w : ℂ => ω.2 (x, w)) z = 0 := by
  refine ⟨deningerLogSection γ, (deningerLogSection_transverseCore h).1,
    (deningerLogSection_transverseCore h).2, ?_,
    fun m K C => deningerLogSection_graphSeminorm_le_iff m K C,
    fun x _ hj z => deningerLogSection_iteratedDeriv_normal γ x hj z⟩
  exact congrArg (fun T : DeningerBoundaryForms D V →L[ℂ] DeningerBoundaryForms D V => T γ)
    deningerResidue_comp_logSection

end ResidueGraphCompatibility

section CauchyBoundaryEstimate

variable {D V : Type*} [TopologicalSpace D]
variable [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- **Cauchy's estimate on a normal circle.**  If a chart field is holomorphic in the normal
coordinate, every normal derivative at the divisor is bounded by the supremum of the field on a
normal circle of radius `r`. -/
theorem deningerNormalCircle_iteratedDeriv_le {g : C(D × ℂ, V)}
    (hg : ∀ x : D, Differentiable ℂ fun z : ℂ => g (x, z))
    (x : D) (j : ℕ) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ z : ℂ, ‖z‖ = r → ‖g (x, z)‖ ≤ C) :
    ‖iteratedDeriv j (fun z : ℂ => g (x, z)) 0‖ ≤ j.factorial * C / r ^ j := by
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    ((hg x).diffContOnCl) ?_
  intro z hz
  exact hC z (by simpa [Complex.dist_eq] using mem_sphere_iff_norm.mp hz)

/-- The transverse graph core together with normal holomorphy of every transverse monomial: the
analytic domain of the seminorms `p_{K,j,m}(ω) = sup_K ‖∂_z^j A^m ω‖`. -/
structure DeningerTateGraphField (A : Module.End ℂ V) (f : C(D × ℂ, V)) : Prop where
  /-- Every transverse monomial keeps the field continuous. -/
  core : DeningerTransverseCore A f
  /-- Every transverse monomial keeps the field holomorphic in the normal coordinate. -/
  normalHolomorphic : ∀ (m : ℕ) (x : D), Differentiable ℂ fun z : ℂ => (A ^ m) (f (x, z))

/-- Every boundary derivative seminorm of a Tate graph field is bounded by the transverse graph
seminorm of the same order on a normal circle: the Cauchy estimate at every graph level. -/
theorem deningerTateGraphField_boundary_deriv_le {A : Module.End ℂ V} {f : C(D × ℂ, V)}
    (hf : DeningerTateGraphField A f) (m j : ℕ) (x : D) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ z : ℂ, ‖z‖ = r → ‖(A ^ m) (f (x, z))‖ ≤ C) :
    ‖iteratedDeriv j (fun z : ℂ => (A ^ m) (f (x, z))) 0‖ ≤ j.factorial * C / r ^ j :=
  deningerNormalCircle_iteratedDeriv_le
    (g := deningerTransverseMonomial A hf.core m) (hf.normalHolomorphic m) x j hr hC

omit [CompleteSpace V] in
/-- The normal-form section of a boundary graph-core field is a Tate graph field. -/
theorem deningerLogSection_tateGraphField {A : Module.End ℂ V}
    {γ : DeningerBoundaryForms D V} (h : DeningerTransverseCore A γ) :
    DeningerTateGraphField A (deningerLogSection γ).2 where
  core := (deningerLogSection_transverseCore h).2
  normalHolomorphic := fun m x => by
    have : (fun z : ℂ => (A ^ m) ((deningerLogSection γ).2 (x, z))) =
        fun _ : ℂ => (A ^ m) (γ x) := rfl
    rw [this]
    exact differentiable_const _

end CauchyBoundaryEstimate

section PacketRestriction

variable {D : Type*} [TopologicalSpace D]

/-- Restriction of continuous functions to a finite packet, continuous for the compact-open
topology. -/
noncomputable def deningerPacketRestriction (Y : Finset D) : C(D, ℂ) →L[ℂ] (↥Y → ℂ) where
  toFun f := fun y => f (y : D)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun y => continuous_eval_const (y : D)

@[simp]
theorem deningerPacketRestriction_apply (Y : Finset D) (f : C(D, ℂ)) (y : Y) :
    deningerPacketRestriction Y f y = f (y : D) :=
  rfl

end PacketRestriction

section FinitePacket

variable {D : Type*} [TopologicalSpace D] [T1Space D] [NormalSpace D]

/-- The coordinate algebra separates a finite packet: every packet point carries a continuous
function equal to one there and zero at the other packet points. -/
theorem deningerPacketIdempotent_exists (Y : Finset D) (y : D) :
    ∃ e : C(D, ℂ), e y = 1 ∧ ∀ y' ∈ Y, y' ≠ y → e y' = 0 := by
  have hs : IsClosed ((Y : Set D) \ {y}) :=
    (Y.finite_toSet.subset Set.sdiff_subset).isClosed
  have ht : IsClosed ({y} : Set D) := isClosed_singleton
  have hd : Disjoint ((Y : Set D) \ {y}) ({y} : Set D) := by
    rw [Set.disjoint_singleton_right]
    simp
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  refine ⟨⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩, ?_, ?_⟩
  · have : f y = 1 := hf1 (Set.mem_singleton y)
    simp [this]
  · intro y' hy' hne
    have hmem : y' ∈ (Y : Set D) \ {y} := ⟨hy', by simpa using hne⟩
    have : f y' = 0 := hf0 hmem
    simp [this]

/-- The interpolating idempotent attached to a point of a finite packet. -/
noncomputable def deningerPacketIdempotent (Y : Finset D) (y : Y) : C(D, ℂ) :=
  (deningerPacketIdempotent_exists Y (y : D)).choose

theorem deningerPacketIdempotent_self (Y : Finset D) (y : Y) :
    deningerPacketIdempotent Y y (y : D) = 1 :=
  (deningerPacketIdempotent_exists Y (y : D)).choose_spec.1

theorem deningerPacketIdempotent_of_ne (Y : Finset D) (y : Y) {y' : D}
    (hy' : y' ∈ Y) (hne : y' ≠ (y : D)) :
    deningerPacketIdempotent Y y y' = 0 :=
  (deningerPacketIdempotent_exists Y (y : D)).choose_spec.2 y' hy' hne

/-- The interpolating right inverse of finite packet restriction. -/
noncomputable def deningerPacketSection (Y : Finset D) : (↥Y → ℂ) →L[ℂ] C(D, ℂ) :=
  ∑ y : Y, (ContinuousLinearMap.proj y).smulRight (deningerPacketIdempotent Y y)

theorem deningerPacketSection_apply (Y : Finset D) (c : ↥Y → ℂ) (x : D) :
    deningerPacketSection Y c x = ∑ y : Y, c y * deningerPacketIdempotent Y y x := by
  simp [deningerPacketSection, smul_eq_mul]

/-- Finite packet evaluation is split: the interpolating section is a continuous right inverse. -/
theorem deningerPacketRestriction_comp_section (Y : Finset D) :
    (deningerPacketRestriction Y).comp (deningerPacketSection Y) =
      ContinuousLinearMap.id ℂ (↥Y → ℂ) := by
  ext c y
  rw [ContinuousLinearMap.comp_apply, deningerPacketRestriction_apply,
    deningerPacketSection_apply]
  rw [Finset.sum_eq_single y]
  · rw [deningerPacketIdempotent_self, mul_one]
    rfl
  · intro y' _ hne
    rw [deningerPacketIdempotent_of_ne Y y' y.2 (fun h => hne (Subtype.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- Finite packet evaluation is a continuous surjection onto `Map(Y, ℂ)`. -/
theorem deningerPacketRestriction_surjective (Y : Finset D) :
    Function.Surjective (deningerPacketRestriction Y) := fun c =>
  ⟨deningerPacketSection Y c,
    congrArg (fun T : (↥Y → ℂ) →L[ℂ] (↥Y → ℂ) => T c)
      (deningerPacketRestriction_comp_section Y)⟩

end FinitePacket

section FiniteCell

variable {E F E' F' : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module ℂ E]
variable [AddCommGroup F] [TopologicalSpace F] [Module ℂ F]
variable [AddCommGroup E'] [TopologicalSpace E'] [Module ℂ E']
variable [AddCommGroup F'] [TopologicalSpace F'] [Module ℂ F']

/-- A finite direct sum of continuous split surjections is a continuous split surjection: each
finite relative cell built from the residue square inherits the splitting. -/
theorem deningerSplitSurjection_prodMap
    {T : E →L[ℂ] F} {S : F →L[ℂ] E} (h : T.comp S = ContinuousLinearMap.id ℂ F)
    {T' : E' →L[ℂ] F'} {S' : F' →L[ℂ] E'} (h' : T'.comp S' = ContinuousLinearMap.id ℂ F') :
    (T.prodMap T').comp (S.prodMap S') = ContinuousLinearMap.id ℂ (F × F') := by
  refine ContinuousLinearMap.ext fun w => Prod.ext ?_ ?_
  · exact congrArg (fun U : F →L[ℂ] F => U w.1) h
  · exact congrArg (fun U : F' →L[ℂ] F' => U w.2) h'

end FiniteCell

end RHTower
