import GaloisForLFunctions.RHTower.DeningerPolarizationAlmostProjection
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Radialization of the Kummer suspension and the ray augmentation resolution

The deck relation `(a, u) ∼ (q a, u/q)` on nonzero vectors times the positive reals is trivialized
by the radius: if the radius is homogeneous of weight one for the positive rational action, then
`u · r(a)` is deck invariant, and it identifies the deck quotient with rays times a single positive
half line.  The suspension flow becomes dilation of the second factor alone.

The ray-indexed direct sum has a canonical augmentation to a single summand, given by the finite
sum.  Placing an element in one summand is a section, so the augmentation is split surjective: its
kernel is complemented, the quotient is canonically the single summand, and the two-term complex
`ker → sum` has only degree-zero cohomology.  The augmentation commutes with any operator applied
componentwise — the Poisson operator or the dilation flow — so attaching it before the Poisson
differential produces one copy of the Poisson complex, not one per ray.

* `deningerRadialize`, `deningerRaySuspensionEquiv` : the radialization `(3)`--`(4)`.
* `deningerRaySuspensionEquiv_flow` : the flow `(5)`.
* `deningerRayAugmentation_section`, `_isCompl`, `_quotEquiv` : the resolution `(8)`--`(9)`.
* `deningerRayAugmentation_comm` : the operator compatibility `(10)`.
-/

namespace RHTower

section Radialization

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A point of the Kummer suspension cover: a nonzero vector and a positive height. -/
abbrev DeningerRayPoint (V : Type*) [AddCommGroup V] [Module ℚ V] : Type _ :=
  {p : V × ℝ // p.1 ≠ 0 ∧ 0 < p.2}

/-- Deninger's deck relation `(a, u) ∼ (q a, u / q)`. -/
def deningerDeckRel (p q : DeningerRayPoint V) : Prop :=
  ∃ c : ℚ, 0 < c ∧ (q : V × ℝ).1 = c • (p : V × ℝ).1 ∧ (q : V × ℝ).2 = (p : V × ℝ).2 / (c : ℝ)

theorem deningerDeckRel_refl (p : DeningerRayPoint V) : deningerDeckRel p p :=
  ⟨1, one_pos, by simp, by simp⟩

theorem deningerDeckRel_symm {p q : DeningerRayPoint V} (h : deningerDeckRel p q) :
    deningerDeckRel q p := by
  obtain ⟨c, hc, h1, h2⟩ := h
  refine ⟨c⁻¹, by positivity, ?_, ?_⟩
  · rw [h1, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  · rw [h2]
    have hc' : (c : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hc
    push_cast
    field_simp

theorem deningerDeckRel_trans {p q s : DeningerRayPoint V} (h1 : deningerDeckRel p q)
    (h2 : deningerDeckRel q s) : deningerDeckRel p s := by
  obtain ⟨c, hc, hc1, hc2⟩ := h1
  obtain ⟨d, hd, hd1, hd2⟩ := h2
  refine ⟨d * c, mul_pos hd hc, ?_, ?_⟩
  · rw [hd1, hc1, smul_smul]
  · rw [hd2, hc2]
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    push_cast
    field_simp

/-- The deck relation is an equivalence. -/
def deningerDeckSetoid (V : Type*) [AddCommGroup V] [Module ℚ V] :
    Setoid (DeningerRayPoint V) where
  r := deningerDeckRel
  iseqv := ⟨deningerDeckRel_refl, deningerDeckRel_symm, deningerDeckRel_trans⟩

/-- A nonzero vector of the Kummer space. -/
abbrev DeningerNonzero (V : Type*) [AddCommGroup V] [Module ℚ V] : Type _ := {a : V // a ≠ 0}

/-- The positive-rational ray relation. -/
def deningerRayRel (a b : DeningerNonzero V) : Prop :=
  ∃ c : ℚ, 0 < c ∧ (b : V) = c • (a : V)

theorem deningerRayRel_refl (a : DeningerNonzero V) : deningerRayRel a a :=
  ⟨1, one_pos, by simp⟩

theorem deningerRayRel_symm {a b : DeningerNonzero V} (h : deningerRayRel a b) :
    deningerRayRel b a := by
  obtain ⟨c, hc, hb⟩ := h
  refine ⟨c⁻¹, by positivity, ?_⟩
  rw [hb, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]

theorem deningerRayRel_trans {a b c : DeningerNonzero V} (h1 : deningerRayRel a b)
    (h2 : deningerRayRel b c) : deningerRayRel a c := by
  obtain ⟨d, hd, hb⟩ := h1
  obtain ⟨e, he, hc⟩ := h2
  exact ⟨e * d, mul_pos he hd, by rw [hc, hb, smul_smul]⟩

/-- The ray relation is an equivalence. -/
def deningerRaySetoid (V : Type*) [AddCommGroup V] [Module ℚ V] : Setoid (DeningerNonzero V) where
  r := deningerRayRel
  iseqv := ⟨deningerRayRel_refl, deningerRayRel_symm, deningerRayRel_trans⟩

variable (r : V → ℝ)

/-- A Kummer radius: positive off the origin and homogeneous of weight one for the positive
rational action. -/
structure DeningerRadius (r : V → ℝ) : Prop where
  pos : ∀ a : V, a ≠ 0 → 0 < r a
  smul : ∀ (c : ℚ), 0 < c → ∀ a : V, r (c • a) = (c : ℝ) * r a

variable {r}

theorem deningerRadius_ne_zero (hr : DeningerRadius r) {a : V} (ha : a ≠ 0) : r a ≠ 0 :=
  ne_of_gt (hr.pos a ha)

/-- **The deck-invariant height.**  The product of the suspension parameter and the radius is
invariant under the deck relation. -/
theorem deningerHeight_deckInvariant (hr : DeningerRadius r) {p q : DeningerRayPoint V}
    (h : deningerDeckRel p q) :
    (q : V × ℝ).2 * r (q : V × ℝ).1 = (p : V × ℝ).2 * r (p : V × ℝ).1 := by
  obtain ⟨c, hc, h1, h2⟩ := h
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  rw [h1, h2, hr.smul c hc]
  field_simp

/-- The radialization map `(3)`. -/
noncomputable def deningerRadialize (hr : DeningerRadius r) :
    Quotient (deningerDeckSetoid V) → Quotient (deningerRaySetoid V) × ℝ :=
  Quotient.lift
    (fun p : DeningerRayPoint V =>
      (Quotient.mk (deningerRaySetoid V) ⟨(p : V × ℝ).1, p.2.1⟩,
        (p : V × ℝ).2 * r (p : V × ℝ).1))
    (by
      intro p q h
      obtain ⟨c, hc, h1, h2⟩ := id h
      refine Prod.ext ?_ ?_
      · refine Quotient.sound ?_
        exact ⟨c, hc, h1⟩
      · exact (deningerHeight_deckInvariant hr h).symm)

@[simp]
theorem deningerRadialize_mk (hr : DeningerRadius r) (p : DeningerRayPoint V) :
    deningerRadialize hr (Quotient.mk (deningerDeckSetoid V) p)
      = (Quotient.mk (deningerRaySetoid V) ⟨(p : V × ℝ).1, p.2.1⟩,
        (p : V × ℝ).2 * r (p : V × ℝ).1) := rfl

/-- **The radialized height is positive.** -/
theorem deningerRadialize_pos (hr : DeningerRadius r) (p : DeningerRayPoint V) :
    0 < (deningerRadialize hr (Quotient.mk (deningerDeckSetoid V) p)).2 :=
  mul_pos p.2.2 (hr.pos _ p.2.1)

/-- **Injectivity of the radialization `(4)`.**  Two points with the same ray and the same height
are deck equivalent. -/
theorem deningerRadialize_injective (hr : DeningerRadius r) :
    Function.Injective (deningerRadialize hr) := by
  refine Quotient.ind fun p => Quotient.ind fun q => ?_
  intro h
  refine Quotient.sound ?_
  have hray : Quotient.mk (deningerRaySetoid V) (⟨(p : V × ℝ).1, p.2.1⟩ : DeningerNonzero V)
      = Quotient.mk (deningerRaySetoid V) ⟨(q : V × ℝ).1, q.2.1⟩ := congrArg Prod.fst h
  have hheight : (p : V × ℝ).2 * r (p : V × ℝ).1 = (q : V × ℝ).2 * r (q : V × ℝ).1 :=
    congrArg Prod.snd h
  obtain ⟨c, hc, hcq⟩ := Quotient.exact hray
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have hrq : r (q : V × ℝ).1 = (c : ℝ) * r (p : V × ℝ).1 := by
    rw [show (q : V × ℝ).1 = c • (p : V × ℝ).1 from hcq, hr.smul c hc]
  have hrp : r (p : V × ℝ).1 ≠ 0 := deningerRadius_ne_zero hr p.2.1
  refine ⟨c, hc, hcq, ?_⟩
  rw [hrq] at hheight
  field_simp at hheight ⊢
  nlinarith [hheight]

/-- **Surjectivity of the radialization `(4)`** onto rays times the positive half line. -/
theorem deningerRadialize_surjective (hr : DeningerRadius r) (y : Quotient (deningerRaySetoid V))
    {x : ℝ} (hx : 0 < x) :
    ∃ z : Quotient (deningerDeckSetoid V), deningerRadialize hr z = (y, x) := by
  refine Quotient.inductionOn y fun a => ?_
  have hra : 0 < r (a : V) := hr.pos _ a.2
  refine ⟨Quotient.mk (deningerDeckSetoid V) ⟨((a : V), x / r (a : V)), a.2, by positivity⟩, ?_⟩
  refine Prod.ext rfl ?_
  show x / r (a : V) * r (a : V) = x
  field_simp

/-- **The radialization bijection `(4)`.**  The deck quotient of the suspension cover is rays
times a single positive half line. -/
noncomputable def deningerRaySuspensionEquiv (hr : DeningerRadius r) :
    Quotient (deningerDeckSetoid V) ≃ Quotient (deningerRaySetoid V) × {x : ℝ // 0 < x} where
  toFun := Quotient.lift
    (fun p : DeningerRayPoint V =>
      (Quotient.mk (deningerRaySetoid V) (⟨(p : V × ℝ).1, p.2.1⟩ : DeningerNonzero V),
        (⟨(p : V × ℝ).2 * r (p : V × ℝ).1, mul_pos p.2.2 (hr.pos _ p.2.1)⟩ : {x : ℝ // 0 < x})))
    (by
      intro p q h
      refine Prod.ext ?_ ?_
      · obtain ⟨c, hc, h1, _⟩ := id h
        exact Quotient.sound ⟨c, hc, h1⟩
      · exact Subtype.ext (deningerHeight_deckInvariant hr h).symm)
  invFun := fun y =>
    Quotient.liftOn y.1
      (fun a : DeningerNonzero V =>
        Quotient.mk (deningerDeckSetoid V)
          (⟨((a : V), (y.2 : ℝ) / r (a : V)), a.2, div_pos y.2.2 (hr.pos _ a.2)⟩ :
            DeningerRayPoint V))
      (by
        intro a b hab
        obtain ⟨c, hc, hb⟩ := hab
        have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
        have hra : r (a : V) ≠ 0 := deningerRadius_ne_zero hr a.2
        refine Quotient.sound ⟨c, hc, hb, ?_⟩
        show (y.2 : ℝ) / r (b : V) = (y.2 : ℝ) / r (a : V) / (c : ℝ)
        rw [hb, hr.smul c hc]
        field_simp)
  left_inv := by
    refine Quotient.ind fun p => ?_
    have hra : r (p : V × ℝ).1 ≠ 0 := deningerRadius_ne_zero hr p.2.1
    refine Quotient.sound ⟨1, one_pos, ?_, ?_⟩
    · simp
    · show (p : V × ℝ).2 = (p : V × ℝ).2 * r (p : V × ℝ).1 / r (p : V × ℝ).1 / ((1 : ℚ) : ℝ)
      rw [mul_div_assoc, div_self hra, mul_one, Rat.cast_one, div_one]
  right_inv := by
    rintro ⟨y, x⟩
    refine Quotient.inductionOn y fun a => ?_
    have hra : r (a : V) ≠ 0 := deningerRadius_ne_zero hr a.2
    refine Prod.ext rfl (Subtype.ext ?_)
    show (x : ℝ) / r (a : V) * r (a : V) = (x : ℝ)
    field_simp

/-- **The suspension flow `(5)`.**  On the radialization the flow is dilation of the height. -/
noncomputable def deningerSuspensionFlow (t : ℝ) (p : DeningerRayPoint V) : DeningerRayPoint V :=
  ⟨((p : V × ℝ).1, Real.exp t * (p : V × ℝ).2), p.2.1, mul_pos (Real.exp_pos t) p.2.2⟩

theorem deningerRadialize_flow (hr : DeningerRadius r) (t : ℝ) (p : DeningerRayPoint V) :
    deningerRadialize hr (Quotient.mk (deningerDeckSetoid V) (deningerSuspensionFlow t p))
      = ((deningerRadialize hr (Quotient.mk (deningerDeckSetoid V) p)).1,
        Real.exp t * (deningerRadialize hr (Quotient.mk (deningerDeckSetoid V) p)).2) := by
  refine Prod.ext rfl ?_
  show Real.exp t * (p : V × ℝ).2 * r (p : V × ℝ).1
      = Real.exp t * ((p : V × ℝ).2 * r (p : V × ℝ).1)
  ring

/-- **The flow on the radialization `(5)`.**  Under the bijection the suspension flow is dilation
of the height alone; the ray is fixed. -/
theorem deningerRaySuspensionEquiv_flow (hr : DeningerRadius r) (t : ℝ) (p : DeningerRayPoint V) :
    deningerRaySuspensionEquiv hr
        (Quotient.mk (deningerDeckSetoid V) (deningerSuspensionFlow t p))
      = ((deningerRaySuspensionEquiv hr (Quotient.mk (deningerDeckSetoid V) p)).1,
        ⟨Real.exp t
            * ((deningerRaySuspensionEquiv hr (Quotient.mk (deningerDeckSetoid V) p)).2 : ℝ),
          by
            have hpos := (deningerRaySuspensionEquiv hr
              (Quotient.mk (deningerDeckSetoid V) p)).2.2
            positivity⟩) := by
  refine Prod.ext rfl (Subtype.ext ?_)
  show Real.exp t * (p : V × ℝ).2 * r (p : V × ℝ).1
      = Real.exp t * ((p : V × ℝ).2 * r (p : V × ℝ).1)
  ring

end Radialization

section RayAugmentation

open DirectSum

variable {R H : Type*} [Ring R] [AddCommGroup H] [Module R H]
variable {ι : Type*} [DecidableEq ι]

/-- The ray-indexed augmentation `(7)`: the finite sum of the ray components. -/
def deningerRayAugmentation : (⨁ _ : ι, H) →ₗ[R] H :=
  DirectSum.toModule R ι H fun _ => LinearMap.id

@[simp]
theorem deningerRayAugmentation_lof (i : ι) (h : H) :
    (deningerRayAugmentation (R := R) (ι := ι)) (DirectSum.lof R ι (fun _ => H) i h) = h := by
  rw [deningerRayAugmentation, DirectSum.toModule_lof]
  rfl

/-- **The augmentation is split.**  Placing an element in one summand is a linear section. -/
theorem deningerRayAugmentation_section (i : ι) :
    (deningerRayAugmentation (R := R) (ι := ι)).comp (DirectSum.lof R ι (fun _ => H) i)
      = LinearMap.id := by
  refine LinearMap.ext fun h => ?_
  rw [LinearMap.comp_apply, deningerRayAugmentation_lof, LinearMap.id_apply]

theorem deningerRayAugmentation_surjective (i : ι) :
    Function.Surjective (deningerRayAugmentation (R := R) (ι := ι) (H := H)) := by
  intro h
  exact ⟨DirectSum.lof R ι (fun _ => H) i h, deningerRayAugmentation_lof i h⟩

/-- **The kernel is complemented `(8)`.**  The section splits the augmentation, so the ray kernel
has the chosen summand as a complement; no ray enters the canonical quotient. -/
theorem deningerRayAugmentation_isCompl (i : ι) :
    IsCompl (LinearMap.ker (deningerLeg (DirectSum.lof R ι (fun _ => H) i)
        (deningerRayAugmentation (R := R) (ι := ι))))
      (LinearMap.range (DirectSum.lof R ι (fun _ => H) i)) :=
  deningerExactLeg_isCompl (deningerRayAugmentation_section i)

/-- **The quotient is canonically one radial copy `(9)`.**  The two-term complex `ker → sum` has
only degree-zero cohomology, canonically the single summand. -/
noncomputable def deningerRayAugmentation_quotEquiv (i : ι) :
    ((⨁ _ : ι, H) ⧸ LinearMap.ker (deningerRayAugmentation (R := R) (ι := ι) (H := H)))
      ≃ₗ[R] H :=
  LinearMap.quotKerEquivOfSurjective _ (deningerRayAugmentation_surjective i)

/-- **The augmentation commutes with componentwise operators `(10)`.**  Applying an operator in
every ray and then summing is applying it to the sum, so attaching the resolution before the
Poisson differential produces one copy of the Poisson complex. -/
theorem deningerRayAugmentation_comm (T : H →ₗ[R] H) :
    (deningerRayAugmentation (R := R) (ι := ι)).comp
        (DirectSum.toModule R ι (⨁ _ : ι, H) fun i =>
          (DirectSum.lof R ι (fun _ => H) i).comp T)
      = T.comp (deningerRayAugmentation (R := R) (ι := ι)) := by
  refine DirectSum.linearMap_ext R fun i => ?_
  refine LinearMap.ext fun h => ?_
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof, deningerRayAugmentation_lof]

/-- **Galois permutations preserve the augmentation.**  A permutation of the rays only permutes a
finite support, so the total sum is unchanged. -/
theorem deningerRayAugmentation_permute (σ : Equiv.Perm ι) :
    (deningerRayAugmentation (R := R) (ι := ι)).comp
        (DirectSum.toModule R ι (⨁ _ : ι, H) fun i =>
          DirectSum.lof R ι (fun _ => H) (σ i))
      = deningerRayAugmentation (R := R) (ι := ι) (H := H) := by
  refine DirectSum.linearMap_ext R fun i => ?_
  refine LinearMap.ext fun h => ?_
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof, deningerRayAugmentation_lof]

end RayAugmentation

end RHTower
