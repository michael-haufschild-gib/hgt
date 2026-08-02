import GaloisForLFunctions.RHTower.DeningerSchemeCharacterSpace
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Constructions

/-!
# The Frobenius colimit of the character space

The Frobenius maps of the character space of a scheme form a diagram indexed by the positive
integers ordered by divisibility.  Its colimit is the quotient of the disjoint union of one copy
of the character space per stage, where a point at stage `μ` and a point at stage `ν` are
identified as soon as some pair of Frobenius maps with matching stage cofactors makes them equal.

Because every Frobenius map fixes the underlying scheme point, the arithmetic projection descends
to the colimit, and the colimit carries the inductive-limit topology of its charts.  On the
colimit every Frobenius map becomes a homeomorphism: its inverse advances the stage instead of
raising the character to a power.

* `DeningerFrobeniusColimit`, `deningerColimitChart` : the colimit and its charts.
* `deningerColimit_topology` : the topology is the inductive limit of the chart topologies.
* `deningerColimitPr` : the arithmetic projection on the colimit.
* `deningerColimitCharacterOver_isOpen'` : the character space over an arithmetic open is open in
  the colimit.
* `deningerColimitFrobeniusHomeomorph` : every Frobenius map is a homeomorphism of the colimit.
-/

namespace RHTower

open AlgebraicGeometry Topology

universe u

namespace DeningerCharacterSpace

variable {X : Scheme.{u}}

/-- A point of the character space together with the Frobenius stage it sits at. -/
abbrev DeningerStagedCharacter (X : Scheme.{u}) : Type u :=
  Σ _ : ℕ+, DeningerCharacterSpace X

/-- Two staged points are identified when a pair of Frobenius maps with matching stage cofactors
makes them equal. -/
def deningerFrobeniusRel (a b : DeningerStagedCharacter X) : Prop :=
  ∃ k l : ℕ+, a.1 * k = b.1 * l ∧
    deningerCharacterFrobenius (k : ℕ) a.2 = deningerCharacterFrobenius (l : ℕ) b.2

theorem deningerFrobeniusRel_refl (a : DeningerStagedCharacter X) : deningerFrobeniusRel a a :=
  ⟨1, 1, rfl, rfl⟩

theorem deningerFrobeniusRel_symm {a b : DeningerStagedCharacter X}
    (h : deningerFrobeniusRel a b) : deningerFrobeniusRel b a := by
  obtain ⟨k, l, hkl, hF⟩ := h
  exact ⟨l, k, hkl.symm, hF.symm⟩

theorem deningerFrobeniusRel_trans {a b c : DeningerStagedCharacter X}
    (hab : deningerFrobeniusRel a b) (hbc : deningerFrobeniusRel b c) :
    deningerFrobeniusRel a c := by
  obtain ⟨k, l, hkl, hF⟩ := hab
  obtain ⟨s, t, hst, hG⟩ := hbc
  refine ⟨k * s, l * t, ?_, ?_⟩
  · refine PNat.coe_injective ?_
    have h1 : ((a.1 : ℕ)) * (k : ℕ) = ((b.1 : ℕ)) * (l : ℕ) := congrArg PNat.val hkl
    have h2 : ((b.1 : ℕ)) * (s : ℕ) = ((c.1 : ℕ)) * (t : ℕ) := congrArg PNat.val hst
    push_cast
    calc ((a.1 : ℕ)) * ((k : ℕ) * (s : ℕ))
        = (((a.1 : ℕ)) * (k : ℕ)) * (s : ℕ) := by ring
      _ = (((b.1 : ℕ)) * (l : ℕ)) * (s : ℕ) := by rw [h1]
      _ = (((b.1 : ℕ)) * (s : ℕ)) * (l : ℕ) := by ring
      _ = (((c.1 : ℕ)) * (t : ℕ)) * (l : ℕ) := by rw [h2]
      _ = ((c.1 : ℕ)) * ((l : ℕ) * (t : ℕ)) := by ring
  · have e1 : deningerCharacterFrobenius ((k * s : ℕ+) : ℕ) a.2
        = deningerCharacterFrobenius (s : ℕ) (deningerCharacterFrobenius (k : ℕ) a.2) := by
      rw [deningerCharacterFrobenius_comp]
      rfl
    have e2 : deningerCharacterFrobenius ((l * t : ℕ+) : ℕ) c.2
        = deningerCharacterFrobenius (l : ℕ) (deningerCharacterFrobenius (t : ℕ) c.2) := by
      rw [deningerCharacterFrobenius_comp]
      exact congrArg (fun n : ℕ => deningerCharacterFrobenius n c.2) (mul_comm _ _)
    rw [e1, e2, hF, ← hG, deningerCharacterFrobenius_comp, deningerCharacterFrobenius_comp]
    exact congrArg (fun n : ℕ => deningerCharacterFrobenius n b.2) (mul_comm _ _)

/-- The Frobenius identification. -/
def deningerFrobeniusSetoid (X : Scheme.{u}) : Setoid (DeningerStagedCharacter X) where
  r := deningerFrobeniusRel
  iseqv := ⟨deningerFrobeniusRel_refl, deningerFrobeniusRel_symm, deningerFrobeniusRel_trans⟩

/-- **The Frobenius colimit of the character space.** -/
abbrev DeningerFrobeniusColimit (X : Scheme.{u}) : Type u :=
  Quotient (deningerFrobeniusSetoid X)

/-- The chart of the colimit at a given Frobenius stage. -/
def deningerColimitChart (n : ℕ+) (p : DeningerCharacterSpace X) : DeningerFrobeniusColimit X :=
  Quotient.mk (deningerFrobeniusSetoid X) ⟨n, p⟩

theorem deningerColimitChart_surjective :
    Function.Surjective (fun a : DeningerStagedCharacter X => deningerColimitChart a.1 a.2) := by
  intro c
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  exact ⟨a, rfl⟩

theorem continuous_deningerColimitChart (n : ℕ+) :
    Continuous (deningerColimitChart (X := X) n) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

/-- **The colimit carries the inductive-limit topology of its charts.** -/
theorem deningerColimit_topology :
    (inferInstance : TopologicalSpace (DeningerFrobeniusColimit X))
      = ⨆ n : ℕ+, TopologicalSpace.coinduced (deningerColimitChart (X := X) n)
          inferInstance := by
  show TopologicalSpace.coinduced (Quotient.mk (deningerFrobeniusSetoid X)) _ = _
  show TopologicalSpace.coinduced (Quotient.mk (deningerFrobeniusSetoid X))
      (⨆ n : ℕ+, TopologicalSpace.coinduced (Sigma.mk n) inferInstance) = _
  rw [coinduced_iSup]
  exact iSup_congr fun n => coinduced_compose

/-- **The arithmetic projection on the colimit.**  It is well defined because every Frobenius map
fixes the underlying scheme point. -/
def deningerColimitPr (c : DeningerFrobeniusColimit X) : X :=
  Quotient.liftOn c (fun a => deningerCharacterPr a.2) (by
    rintro a b ⟨k, l, -, hF⟩
    have ha : deningerCharacterPr (deningerCharacterFrobenius (k : ℕ) a.2)
        = deningerCharacterPr a.2 := deningerCharacterFrobenius_pr _ _
    have hb : deningerCharacterPr (deningerCharacterFrobenius (l : ℕ) b.2)
        = deningerCharacterPr b.2 := deningerCharacterFrobenius_pr _ _
    rw [← ha, ← hb, hF])

@[simp]
theorem deningerColimitPr_chart (n : ℕ+) (p : DeningerCharacterSpace X) :
    deningerColimitPr (deningerColimitChart n p) = deningerCharacterPr p := rfl

/-- **The character space over an arithmetic open is open in the Frobenius colimit.** -/
theorem deningerColimitCharacterOver_isOpen' {U : Set X} (hU : IsOpen U) :
    IsOpen (deningerCharacterOver (deningerColimitPr (X := X)) U) :=
  RHTower.deningerColimitCharacterOver_isOpen (X := fun _ : ℕ+ => DeningerCharacterSpace X)
    (fun n => deningerColimitChart n) deningerColimitPr
    (fun _ => deningerCharacterPr) (fun _ _ => rfl)
    (fun _ => continuous_deningerCharacterPr) deningerColimit_topology hU

section FrobeniusHomeomorphism

variable (q : ℕ+)

/-- The Frobenius map of the colimit. -/
noncomputable def deningerColimitFrobenius (c : DeningerFrobeniusColimit X) :
    DeningerFrobeniusColimit X :=
  Quotient.liftOn c
    (fun a => deningerColimitChart a.1 (deningerCharacterFrobenius (q : ℕ) a.2)) (by
      rintro a b ⟨k, l, hkl, hF⟩
      refine Quotient.sound ⟨k, l, hkl, ?_⟩
      show deningerCharacterFrobenius (k : ℕ) (deningerCharacterFrobenius (q : ℕ) a.2)
        = deningerCharacterFrobenius (l : ℕ) (deningerCharacterFrobenius (q : ℕ) b.2)
      rw [deningerCharacterFrobenius_comp, deningerCharacterFrobenius_comp,
        mul_comm (q : ℕ) (k : ℕ), mul_comm (q : ℕ) (l : ℕ),
        ← deningerCharacterFrobenius_comp, ← deningerCharacterFrobenius_comp, hF])

@[simp]
theorem deningerColimitFrobenius_chart (n : ℕ+) (p : DeningerCharacterSpace X) :
    deningerColimitFrobenius q (deningerColimitChart n p)
      = deningerColimitChart n (deningerCharacterFrobenius (q : ℕ) p) := rfl

/-- The inverse of the Frobenius map of the colimit: it advances the stage. -/
def deningerColimitFrobeniusInv (c : DeningerFrobeniusColimit X) : DeningerFrobeniusColimit X :=
  Quotient.liftOn c (fun a => deningerColimitChart (a.1 * q) a.2) (by
    rintro a b ⟨k, l, hkl, hF⟩
    refine Quotient.sound ⟨k, l, ?_, hF⟩
    refine PNat.coe_injective ?_
    have h1 : ((a.1 : ℕ)) * (k : ℕ) = ((b.1 : ℕ)) * (l : ℕ) := congrArg PNat.val hkl
    push_cast
    calc ((a.1 : ℕ)) * (q : ℕ) * (k : ℕ) = (((a.1 : ℕ)) * (k : ℕ)) * (q : ℕ) := by ring
      _ = (((b.1 : ℕ)) * (l : ℕ)) * (q : ℕ) := by rw [h1]
      _ = ((b.1 : ℕ)) * (q : ℕ) * (l : ℕ) := by ring)

@[simp]
theorem deningerColimitFrobeniusInv_chart (n : ℕ+) (p : DeningerCharacterSpace X) :
    deningerColimitFrobeniusInv q (deningerColimitChart n p)
      = deningerColimitChart (n * q) p := rfl

theorem deningerColimitFrobenius_leftInverse :
    Function.LeftInverse (deningerColimitFrobeniusInv (X := X) q) (deningerColimitFrobenius q) := by
  intro c
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  show deningerColimitChart (a.1 * q) (deningerCharacterFrobenius (q : ℕ) a.2)
    = deningerColimitChart a.1 a.2
  refine Quotient.sound ⟨1, q, ?_, ?_⟩
  · rw [mul_one]
  · show deningerCharacterFrobenius 1 (deningerCharacterFrobenius (q : ℕ) a.2)
      = deningerCharacterFrobenius (q : ℕ) a.2
    exact deningerCharacterFrobenius_one _

theorem deningerColimitFrobenius_rightInverse :
    Function.RightInverse (deningerColimitFrobeniusInv (X := X) q)
      (deningerColimitFrobenius q) := by
  intro c
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  show deningerColimitChart (a.1 * q) (deningerCharacterFrobenius (q : ℕ) a.2)
    = deningerColimitChart a.1 a.2
  refine Quotient.sound ⟨1, q, ?_, ?_⟩
  · rw [mul_one]
  · show deningerCharacterFrobenius 1 (deningerCharacterFrobenius (q : ℕ) a.2)
      = deningerCharacterFrobenius (q : ℕ) a.2
    exact deningerCharacterFrobenius_one _

theorem continuous_deningerColimitFrobenius :
    Continuous (deningerColimitFrobenius (X := X) q) := by
  rw [(isQuotientMap_quotient_mk' (s := deningerFrobeniusSetoid X)).continuous_iff]
  exact continuous_sigma fun n =>
    (continuous_deningerColimitChart n).comp (continuous_deningerCharacterFrobenius (q : ℕ))

theorem continuous_deningerColimitFrobeniusInv :
    Continuous (deningerColimitFrobeniusInv (X := X) q) := by
  rw [(isQuotientMap_quotient_mk' (s := deningerFrobeniusSetoid X)).continuous_iff]
  exact continuous_sigma fun n => continuous_deningerColimitChart (n * q)

/-- **Every Frobenius map is a homeomorphism of the Frobenius colimit.**  Its inverse advances the
stage rather than raising the character to a power. -/
noncomputable def deningerColimitFrobeniusHomeomorph :
    DeningerFrobeniusColimit X ≃ₜ DeningerFrobeniusColimit X where
  toFun := deningerColimitFrobenius q
  invFun := deningerColimitFrobeniusInv q
  left_inv := deningerColimitFrobenius_leftInverse q
  right_inv := deningerColimitFrobenius_rightInverse q
  continuous_toFun := continuous_deningerColimitFrobenius q
  continuous_invFun := continuous_deningerColimitFrobeniusInv q

/-- **The Frobenius map of the colimit fixes the arithmetic projection.** -/
@[simp]
theorem deningerColimitFrobenius_pr (c : DeningerFrobeniusColimit X) :
    deningerColimitPr (deningerColimitFrobenius q c) = deningerColimitPr c := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  exact deningerCharacterFrobenius_pr _ _

/-- **The character space over an arithmetic open is Frobenius stable in the colimit.** -/
theorem deningerColimitFrobenius_characterOver_mem (U : Set X)
    {c : DeningerFrobeniusColimit X}
    (hc : c ∈ deningerCharacterOver (deningerColimitPr (X := X)) U) :
    deningerColimitFrobenius q c ∈ deningerCharacterOver (deningerColimitPr (X := X)) U :=
  deningerCharacterOver_map_mem (deningerColimitFrobenius q)
    (deningerColimitFrobenius_pr q) U hc

end FrobeniusHomeomorphism

section ColimitOpenEmbedding

variable {Y : Scheme.{u}}

/-- A subset of the colimit is open exactly when its preimage in every chart is open. -/
theorem deningerColimit_isOpen_iff {S : Set (DeningerFrobeniusColimit X)} :
    IsOpen S ↔ ∀ n : ℕ+, IsOpen (deningerColimitChart (X := X) n ⁻¹' S) := by
  rw [← (isQuotientMap_quotient_mk' (s := deningerFrobeniusSetoid X)).isOpen_preimage,
    isOpen_sigma_iff]
  rfl

/-- **The map of Frobenius colimits induced by a scheme morphism.** -/
noncomputable def deningerColimitMap (f : X ⟶ Y) :
    DeningerFrobeniusColimit X → DeningerFrobeniusColimit Y :=
  Quotient.lift (fun a => deningerColimitChart a.1 (deningerCharacterMap f a.2)) (by
    rintro a b ⟨k, l, hkl, hF⟩
    refine Quotient.sound ⟨k, l, hkl, ?_⟩
    show deningerCharacterFrobenius (k : ℕ) (deningerCharacterMap f a.2)
      = deningerCharacterFrobenius (l : ℕ) (deningerCharacterMap f b.2)
    rw [← deningerCharacterMap_frobenius, ← deningerCharacterMap_frobenius, hF])

@[simp]
theorem deningerColimitMap_chart (f : X ⟶ Y) (n : ℕ+) (p : DeningerCharacterSpace X) :
    deningerColimitMap f (deningerColimitChart n p)
      = deningerColimitChart n (deningerCharacterMap f p) := rfl

/-- The arithmetic projection is natural on the colimit. -/
theorem deningerColimitPr_map (f : X ⟶ Y) (c : DeningerFrobeniusColimit X) :
    deningerColimitPr (deningerColimitMap f c) = f (deningerColimitPr c) := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  rfl

theorem continuous_deningerColimitMap (f : X ⟶ Y) :
    Continuous (deningerColimitMap f) := by
  rw [(isQuotientMap_quotient_mk' (s := deningerFrobeniusSetoid X)).continuous_iff]
  exact continuous_sigma fun n =>
    (continuous_deningerColimitChart n).comp (continuous_deningerCharacterMap f)

variable (f : X ⟶ Y) [IsOpenImmersion f]

theorem deningerColimitMap_injective : Function.Injective (deningerColimitMap f) := by
  intro c d h
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) d
  obtain ⟨k, l, hkl, hF⟩ := Quotient.exact h
  refine Quotient.sound ⟨k, l, hkl, deningerCharacterMap_injective f ?_⟩
  rw [deningerCharacterMap_frobenius, deningerCharacterMap_frobenius]
  exact hF

/-- **The image of the colimit map is the character space over the image of the immersion.** -/
theorem deningerColimitMap_range :
    Set.range (deningerColimitMap f)
      = deningerCharacterOver (deningerColimitPr (X := Y)) (Set.range f.base) := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨deningerColimitPr d, (deningerColimitPr_map f d).symm⟩
  · intro hc
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid Y) c
    have ha : a.2 ∈ Set.range (deningerCharacterMap f) := by
      rw [deningerCharacterMap_range f]
      exact hc
    obtain ⟨p, hp⟩ := ha
    refine ⟨deningerColimitChart a.1 p, ?_⟩
    rw [deningerColimitMap_chart, hp]
    rfl

/-- **The colimit map is open.**  A point of a chart lies in the image of an open set exactly when
some Frobenius power of it is the image of a point of that open set at a matching stage, and each
of the resulting pieces is an open set. -/
theorem deningerColimitMap_isOpenMap : IsOpenMap (deningerColimitMap f) := by
  intro O hO
  rw [deningerColimit_isOpen_iff]
  intro n
  have key : deningerColimitChart (X := Y) n ⁻¹' (deningerColimitMap f '' O)
      = ⋃ l : ℕ+, (deningerCharacterFrobenius (X := Y) (l : ℕ)) ⁻¹'
          (deningerCharacterMap f '' (deningerColimitChart (X := X) (n * l) ⁻¹' O)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨c, hcO, hc⟩
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective (s := deningerFrobeniusSetoid X) c
      obtain ⟨k, l, hkl, hF⟩ := Quotient.exact hc
      refine ⟨l, deningerCharacterFrobenius (k : ℕ) a.2, ?_, ?_⟩
      · have hshift : deningerColimitChart (X := X) (n * l)
            (deningerCharacterFrobenius (k : ℕ) a.2) = deningerColimitChart a.1 a.2 := by
          refine Quotient.sound ⟨1, k, ?_, ?_⟩
          · rw [mul_one]
            exact hkl.symm
          · show deningerCharacterFrobenius 1 (deningerCharacterFrobenius (k : ℕ) a.2)
              = deningerCharacterFrobenius (k : ℕ) a.2
            exact deningerCharacterFrobenius_one _
        show deningerColimitChart (X := X) (n * l)
          (deningerCharacterFrobenius (k : ℕ) a.2) ∈ O
        rw [hshift]
        exact hcO
      · rw [deningerCharacterMap_frobenius]
        exact hF
    · rintro ⟨l, w, hw, hwz⟩
      refine ⟨deningerColimitChart (n * l) w, hw, ?_⟩
      show deningerColimitChart (X := Y) (n * l) (deningerCharacterMap f w)
        = deningerColimitChart n z
      refine Quotient.sound ⟨1, l, ?_, ?_⟩
      · rw [mul_one]
      · show deningerCharacterFrobenius 1 (deningerCharacterMap f w)
          = deningerCharacterFrobenius (l : ℕ) z
        rw [deningerCharacterFrobenius_one]
        exact hwz
  rw [key]
  refine isOpen_iUnion fun l => ?_
  refine (continuous_deningerCharacterFrobenius (l : ℕ)).isOpen_preimage _ ?_
  exact (deningerCharacterMap_isOpenEmbedding f).isOpenMap _
    ((continuous_deningerColimitChart (n * l)).isOpen_preimage _ hO)

/-- **Clause 2 at colimit level**: the Frobenius colimit of the character space of an open
subscheme is an open subspace of the Frobenius colimit, with image the character space over the
open. -/
theorem deningerColimitMap_isOpenEmbedding : IsOpenEmbedding (deningerColimitMap f) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_deningerColimitMap f)
    (deningerColimitMap_injective f) (deningerColimitMap_isOpenMap f)

end ColimitOpenEmbedding

section ArithmeticOpenColimit

variable (U : X.Opens)

/-- **Clause 2 for an arithmetic open.** -/
theorem deningerColimitMap_opens_range :
    Set.range (deningerColimitMap U.ι)
      = deningerCharacterOver (deningerColimitPr (X := X)) (U : Set X) := by
  rw [deningerColimitMap_range U.ι, U.range_ι]

theorem deningerColimitMap_opens_isOpenEmbedding :
    IsOpenEmbedding (deningerColimitMap U.ι) :=
  deningerColimitMap_isOpenEmbedding U.ι

end ArithmeticOpenColimit

end DeningerCharacterSpace

end RHTower


