import GaloisForLFunctions.HTGeometry.BohrHullSeparation

/-!
# Comparison morphisms of phase carriers

If the translation distance of one bounded continuous function dominates that of another, the
identity of the line is uniformly continuous between the two Bohr lines and therefore extends to a
continuous homomorphism of the carriers.  The extension commutes with the canonical map of the line,
with every frequency character, and — when one function is a uniformly continuous image of the
other — with the carrier evaluation.

This is the projection of a joint carrier onto the carrier of a subfamily.  Its kernel is where all
the characters of the subfamily are trivial, which is the fibre a relative frequency law measures.
-/

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']

/-- The comparison morphism of carriers attached to a uniformly continuous comparison of translation
distances. -/
noncomputable def hullMap (f : ℝ →ᵇ E) (g : ℝ →ᵇ E') : BohrHull f → BohrHull g :=
  UniformSpace.Completion.map (fun t : BohrLine f => (BohrLine.of g t.val))

theorem continuous_hullMap (f : ℝ →ᵇ E) (g : ℝ →ᵇ E') : Continuous (hullMap f g) :=
  UniformSpace.Completion.continuous_map

theorem hullMap_bohrIota {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val))) (t : ℝ) :
    hullMap f g (bohrIota f t) = bohrIota g t :=
  UniformSpace.Completion.map_coe hcmp (BohrLine.of f t)

theorem hullMap_add {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val))) (x y : BohrHull f) :
    hullMap f g (x + y) = hullMap f g x + hullMap f g y := by
  have h1 : Continuous fun p : BohrHull f × BohrHull f => hullMap f g (p.1 + p.2) :=
    (continuous_hullMap f g).comp continuous_add
  have h2 : Continuous fun p : BohrHull f × BohrHull f =>
      hullMap f g p.1 + hullMap f g p.2 :=
    (((continuous_hullMap f g).comp continuous_fst).add
      ((continuous_hullMap f g).comp continuous_snd))
  have hdense : Dense (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    have := (denseRange_bohrIota f).prodMap (denseRange_bohrIota f)
    simpa [DenseRange, Prod.map] using this
  have heq : Set.EqOn (fun p : BohrHull f × BohrHull f => hullMap f g (p.1 + p.2))
      (fun p : BohrHull f × BohrHull f => hullMap f g p.1 + hullMap f g p.2)
      (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    rintro ⟨u, v⟩ ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
    simp only
    rw [← bohrIota_add, hullMap_bohrIota hcmp, hullMap_bohrIota hcmp, hullMap_bohrIota hcmp,
      bohrIota_add]
  exact congrFun (Continuous.ext_on hdense h1 h2 heq) (x, y)

@[simp] theorem hullMap_zero {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val))) :
    hullMap f g 0 = 0 := by
  have h := hullMap_bohrIota hcmp (0 : ℝ)
  rwa [bohrIota_zero, bohrIota_zero] at h

/-- **Characters are pulled back along the comparison morphism.** -/
theorem bohrHullChar_hullMap {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val)))
    {μ : ℝ} (hμ : IsBohrHullFrequency g μ) (x : BohrHull f) :
    bohrHullChar g μ (hullMap f g x) = bohrHullChar f μ x := by
  have hμf : IsBohrHullFrequency f μ :=
    isBohrHullFrequency_of_uniformContinuous_compare hcmp hμ
  have h1 : Continuous fun x : BohrHull f => bohrHullChar g μ (hullMap f g x) :=
    (continuous_bohrHullChar g μ).comp (continuous_hullMap f g)
  have h2 : Continuous (bohrHullChar f μ) := continuous_bohrHullChar f μ
  refine congrFun (Continuous.ext_on (denseRange_bohrIota f) h1 h2 ?_) x
  rintro y ⟨t, rfl⟩
  simp only
  rw [hullMap_bohrIota hcmp, bohrHullChar_bohrIota hμ, bohrHullChar_bohrIota hμf]

/-- **The carrier evaluation commutes with the comparison morphism.** -/
theorem bohrEval_hullMap [CompleteSpace E] [CompleteSpace E'] {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val)))
    {L : E → E'} (hL : Continuous L) (hLval : ∀ t : ℝ, g t = L (f t)) (x : BohrHull f) :
    bohrEval g (hullMap f g x) = L (bohrEval f x) := by
  have h1 : Continuous fun x : BohrHull f => bohrEval g (hullMap f g x) :=
    (continuous_bohrEval g).comp (continuous_hullMap f g)
  have h2 : Continuous fun x : BohrHull f => L (bohrEval f x) :=
    hL.comp (continuous_bohrEval f)
  refine congrFun (Continuous.ext_on (denseRange_bohrIota f) h1 h2 ?_) x
  rintro y ⟨t, rfl⟩
  simp only
  rw [hullMap_bohrIota hcmp, bohrEval_bohrIota, bohrEval_bohrIota, hLval t]

/-- **A carrier point killed by every character of the target is in the kernel of the comparison
morphism.** -/
theorem hullMap_eq_zero_of_char_eq_one {f : ℝ →ᵇ E} {g : ℝ →ᵇ E'}
    (hgu : UniformContinuous (fun x => g x)) (hgtb : HasTotallyBoundedOrbit (fun x => g x))
    [MeasurableSpace (BohrHull g)] [BorelSpace (BohrHull g)]
    (hcmp : UniformContinuous (fun t : BohrLine f => (BohrLine.of g t.val)))
    {x : BohrHull f}
    (hx : ∀ μ : ℝ, IsBohrHullFrequency g μ → bohrHullChar f μ x = 1) :
    hullMap f g x = 0 := by
  refine bohrHullChar_separates hgu hgtb fun μ hμ => ?_
  rw [bohrHullChar_hullMap hcmp hμ, hx μ hμ, bohrHullChar_zero hμ]

end GaloisForLFunctions
