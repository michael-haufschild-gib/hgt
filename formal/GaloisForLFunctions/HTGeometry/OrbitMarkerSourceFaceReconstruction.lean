import GaloisForLFunctions.HTGeometry.OrbitResidueVector
import Mathlib.LinearAlgebra.Span.Basic

namespace GaloisForLFunctions

noncomputable section

@[simp]
theorem translateFiniteSupport_zero
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (D : G →₀ A) :
    translateFiniteSupport 0 D = D := by
  rw [translateFiniteSupport]
  rw [show (fun x : G => x + 0) = id by
    funext x
    exact add_zero x]
  exact Finsupp.mapDomain_id

theorem translateFiniteSupport_add
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (p q : G) (D : G →₀ A) :
    translateFiniteSupport (p + q) D =
      translateFiniteSupport p (translateFiniteSupport q D) := by
  rw [translateFiniteSupport, translateFiniteSupport, translateFiniteSupport,
    ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro x _
  dsimp
  abel

@[simp]
theorem translateFiniteSupport_apply_add
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q x : G) (D : G →₀ A) :
    translateFiniteSupport q D (x + q) = D x := by
  exact Finsupp.mapDomain_apply (fun _ _ h => add_right_cancel h) D x

@[simp]
theorem translateFiniteSupport_single
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (q x : G) (c : A) :
    translateFiniteSupport q (Finsupp.single x c) =
      Finsupp.single (x + q) c := by
  exact Finsupp.mapDomain_single

/-- The translations invisible to a finite orbit marker. -/
def finiteSupportTranslationStabilizer
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (D : G →₀ A) : AddSubgroup G where
  carrier := {q | translateFiniteSupport q D = D}
  zero_mem' := translateFiniteSupport_zero D
  add_mem' := by
    intro p q hp hq
    change translateFiniteSupport p D = D at hp
    change translateFiniteSupport q D = D at hq
    change translateFiniteSupport (p + q) D = D
    rw [translateFiniteSupport_add, hq, hp]
  neg_mem' := by
    intro q hq
    calc
      translateFiniteSupport (-q) D =
          translateFiniteSupport (-q) (translateFiniteSupport q D) := by rw [hq]
      _ = translateFiniteSupport ((-q) + q) D :=
        (translateFiniteSupport_add (-q) q D).symm
      _ = D := by simp

@[simp]
theorem mem_finiteSupportTranslationStabilizer
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (D : G →₀ A) (q : G) :
    q ∈ finiteSupportTranslationStabilizer D ↔
      translateFiniteSupport q D = D :=
  Iff.rfl

@[simp]
theorem finiteSupportTranslationStabilizer_zero_eq_top
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A] :
    finiteSupportTranslationStabilizer (0 : G →₀ A) = ⊤ := by
  ext q
  simp [finiteSupportTranslationStabilizer, translateFiniteSupport]

/-- A nonzero finite marker has only finitely many invisible translations. -/
theorem finite_finiteSupportTranslationStabilizer_of_ne_zero
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (D : G →₀ A) (hD : D ≠ 0) :
    Finite (finiteSupportTranslationStabilizer D) := by
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    simpa [Finsupp.ext_iff] using hD
  let emb : finiteSupportTranslationStabilizer D → D.support := fun q =>
    ⟨x + q.1, by
      rw [Finsupp.mem_support_iff]
      have hval := congrArg (fun E : G →₀ A => E (x + q.1)) q.2
      change translateFiniteSupport q.1 D (x + q.1) = D (x + q.1) at hval
      rw [translateFiniteSupport_apply_add] at hval
      exact fun hzero => hx (hval.trans hzero)⟩
  have hemb : Function.Injective emb := by
    intro p q hpq
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val hpq)
  exact Finite.of_injective emb hemb

/-- A nonzero atom is an aperiodic marker. -/
theorem finiteSupportTranslationStabilizer_single_eq_bot
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (x : G) {c : A} (hc : c ≠ 0) :
    finiteSupportTranslationStabilizer (Finsupp.single x c) = ⊥ := by
  ext q
  constructor
  · intro hq
    rw [AddSubgroup.mem_bot]
    have hs : Finsupp.single (x + q) c = Finsupp.single x c := by
      simpa using hq
    have hxq : x + q = x := (Finsupp.single_left_inj hc).mp hs
    exact add_left_cancel (show x + q = x + 0 by simpa using hxq)
  · intro hq
    rw [AddSubgroup.mem_bot] at hq
    subst q
    exact translateFiniteSupport_zero _

/-- Ambient translations invisible after a marker has been placed on `G/H`. -/
def ambientOrbitMarkerStabilizer
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) (D : (G ⧸ H) →₀ A) : AddSubgroup G :=
  (finiteSupportTranslationStabilizer D).comap (QuotientAddGroup.mk' H)

@[simp]
theorem mem_ambientOrbitMarkerStabilizer
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) (D : (G ⧸ H) →₀ A) (g : G) :
    g ∈ ambientOrbitMarkerStabilizer H D ↔
      (g : G ⧸ H) ∈ finiteSupportTranslationStabilizer D :=
  Iff.rfl

theorem periodSubgroup_le_ambientOrbitMarkerStabilizer
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) (D : (G ⧸ H) →₀ A) :
    H ≤ ambientOrbitMarkerStabilizer H D := by
  intro g hg
  change (g : G ⧸ H) ∈ finiteSupportTranslationStabilizer D
  rw [(QuotientAddGroup.eq_zero_iff g).2 hg]
  exact (finiteSupportTranslationStabilizer D).zero_mem

@[simp]
theorem ambientOrbitMarkerStabilizer_zero_eq_top
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) :
    ambientOrbitMarkerStabilizer H (0 : (G ⧸ H) →₀ A) = ⊤ := by
  simp [ambientOrbitMarkerStabilizer]

/-- The marker recovers its period subgroup exactly iff its residual quotient stabilizer is
trivial. -/
theorem ambientOrbitMarkerStabilizer_eq_iff
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) (D : (G ⧸ H) →₀ A) :
    ambientOrbitMarkerStabilizer H D = H ↔
      finiteSupportTranslationStabilizer D = ⊥ := by
  constructor
  · intro hamb
    ext q
    constructor
    · intro hq
      rw [AddSubgroup.mem_bot]
      obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective H q
      have hg : g ∈ ambientOrbitMarkerStabilizer H D := hq
      rw [hamb] at hg
      exact (QuotientAddGroup.eq_zero_iff g).2 hg
    · intro hq
      rw [AddSubgroup.mem_bot] at hq
      subst q
      exact (finiteSupportTranslationStabilizer D).zero_mem
  · intro hstab
    ext g
    change (g : G ⧸ H) ∈ finiteSupportTranslationStabilizer D ↔ g ∈ H
    rw [hstab, AddSubgroup.mem_bot]
    exact QuotientAddGroup.eq_zero_iff g

/-- A marked nonzero atom reconstructs the ambient period subgroup exactly. -/
theorem ambientOrbitMarkerStabilizer_single_eq
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H : AddSubgroup G) (x : G ⧸ H) {c : A} (hc : c ≠ 0) :
    ambientOrbitMarkerStabilizer H (Finsupp.single x c) = H := by
  rw [ambientOrbitMarkerStabilizer_eq_iff]
  exact finiteSupportTranslationStabilizer_single_eq_bot x hc

/-- Two typed aperiodic boundary markers recover the full labelled face incidence lattice. -/
theorem pairedOrbitMarkers_reconstruct_face_incidence
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H₀ H₁ : AddSubgroup G) (D₀ : (G ⧸ H₀) →₀ A) (D₁ : (G ⧸ H₁) →₀ A)
    (h₀ : finiteSupportTranslationStabilizer D₀ = ⊥)
    (h₁ : finiteSupportTranslationStabilizer D₁ = ⊥) :
    ambientOrbitMarkerStabilizer H₀ D₀ ⊓ ambientOrbitMarkerStabilizer H₁ D₁ = H₀ ⊓ H₁ ∧
    ambientOrbitMarkerStabilizer H₀ D₀ ⊔ ambientOrbitMarkerStabilizer H₁ D₁ = H₀ ⊔ H₁ := by
  rw [(ambientOrbitMarkerStabilizer_eq_iff H₀ D₀).2 h₀,
    (ambientOrbitMarkerStabilizer_eq_iff H₁ D₁).2 h₁]
  exact ⟨rfl, rfl⟩

/-- After the two face lattices are coarsened to their common quotient, even an aperiodic atom
recovers only the join.  The individual faces are retained only by the typed pair above. -/
theorem commonOrbitAtom_recovers_only_face_join
    {G A : Type*} [AddCommGroup G] [AddCommMonoid A]
    (H₀ H₁ : AddSubgroup G) (x : G ⧸ (H₀ ⊔ H₁)) {c : A} (hc : c ≠ 0) :
    ambientOrbitMarkerStabilizer (H₀ ⊔ H₁) (Finsupp.single x c) = H₀ ⊔ H₁ := by
  exact ambientOrbitMarkerStabilizer_single_eq (H₀ ⊔ H₁) x hc

/-- Two rank-two faces of an independent rank-three integer frame meet in their common line. -/
theorem rankThreeFaceSpans_inf_eq_commonSpan
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : Fin 3 → V) (hv : LinearIndependent ℚ v) :
    Submodule.span ℤ ({v 0, v 1} : Set V) ⊓
        Submodule.span ℤ ({v 0, v 2} : Set V) =
      Submodule.span ℤ ({v 0} : Set V) := by
  have hvz : LinearIndependent ℤ v := hv.restrict_scalars' ℤ
  ext z
  constructor
  · rintro ⟨hz01, hz02⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz01
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hz02
    have hrel : ∑ i, (![a - c, b, -d] : Fin 3 → ℤ) i • v i = 0 := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
      calc
        (a - c) • v 0 + b • v 1 + -d • v 2 =
            (a • v 0 + b • v 1) - (c • v 0 + d • v 2) := by module
        _ = z - z := by rw [hab, hcd]
        _ = 0 := sub_self z
    have hcoeff := Fintype.linearIndependent_iff.mp hvz _ hrel
    have hb : b = 0 := hcoeff 1
    rw [← hab, hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ a (Submodule.subset_span (by simp))
  · intro hz
    constructor
    · exact Submodule.span_mono (by simp) hz
    · exact Submodule.span_mono (by simp) hz

/-- An orbit subgroup is blind to the sign of its chosen primitive direction.  Thus stabilizer
reconstruction yields an unpolarized face; orientation is genuinely additional data. -/
theorem zmultiples_neg_eq_zmultiples
    {G : Type*} [AddCommGroup G] (q : G) :
    AddSubgroup.zmultiples (-q) = AddSubgroup.zmultiples q := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    simp
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    simp

end

end GaloisForLFunctions
