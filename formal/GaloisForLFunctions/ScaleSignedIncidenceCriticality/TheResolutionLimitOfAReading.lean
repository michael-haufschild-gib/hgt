import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Readings, shadows, and the resolution limit

A *method* that bounds an invariant of a datum never touches the datum itself: it touches a
finite list of observables of it — coefficient magnitudes, translated moments, a positivity
certificate at one aperture, a node density. This module makes the passage from datum to
observables the primitive object and measures what it costs.

A **reading** of a class `D` of data is a map `r : D → O`. Its **shadow** at `d` is the set of
data with the same reading; a reading **resolves** a property when equal readings force equal
verdicts, and a map `κ : D → D` is **invisible** to `r` when it never moves the reading.

* *Collapse–resolution dichotomy* (`not_resolves_of_separating_collapse`): a reading either moves
  every collapse that separates the property, or it does not resolve the property. In the vacuous
  form (`forall_not_of_resolves_of_invisible`), a reading invisible to a uniformly fatal collapse
  resolves the property only when the property is nowhere true.
* *Resolution limit* (`resolutionLimit`): for a real invariant `I`, the supremum of `I` over the
  shadow. It is exactly the set of bounds the reading can certify
  (`certifies_iff_resolutionLimit_le`): a method reading `r` can prove `I d ≤ β` if and only if
  `β` is at least the limit, and every invisible collapse floors it
  (`iterate_le_resolutionLimit`).
* *Order on methods*: refinement shrinks shadows and lowers the limit
  (`resolutionLimit_le_of_refines`), joint readings intersect shadows
  (`shadow_joinReading`), and a reading faithful for one invariant certifies every invariant it
  dominates (`certifies_of_faithful_of_dominated`).

Nothing here is specific to ζ; the arithmetic instances name their collapse and their invariant.
-/

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Set

set_option autoImplicit false

variable {D O O' : Type*} {F : Type*}

/-! ### 1. Shadows -/

/-- The *shadow* of `d` under the reading `r`: the data a method reading only `r` cannot
distinguish from `d`. -/
def shadow (r : D → O) (d : D) : Set D := {e | r e = r d}

theorem mem_shadow_iff {r : D → O} {d e : D} : e ∈ shadow r d ↔ r e = r d := Iff.rfl

theorem mem_shadow_self (r : D → O) (d : D) : d ∈ shadow r d := rfl

/-- Being in the same shadow is symmetric. -/
theorem mem_shadow_comm {r : D → O} {d e : D} (h : e ∈ shadow r d) : d ∈ shadow r e := h.symm

/-- Shadows of indistinguishable data coincide. -/
theorem shadow_eq_of_mem {r : D → O} {d e : D} (h : e ∈ shadow r d) : shadow r e = shadow r d := by
  ext x
  simp only [mem_shadow_iff] at *
  rw [h]

/-! ### 2. Resolution and collapses -/

/-- A reading *resolves* a property when the reading decides it. -/
def Resolves (r : D → O) (P : D → Prop) : Prop := ∀ d e : D, e ∈ shadow r d → (P e ↔ P d)

/-- A map `κ` is *invisible* to `r` when it never moves the reading. -/
def Invisible (r : D → O) (κ : D → D) : Prop := ∀ d : D, r (κ d) = r d

theorem collapse_mem_shadow {r : D → O} {κ : D → D} (h : Invisible r κ) (d : D) :
    κ d ∈ shadow r d := h d

/-- Iterating an invisible collapse stays inside the shadow. -/
theorem iterate_collapse_mem_shadow {r : D → O} {κ : D → D} (h : Invisible r κ) (d : D) :
    ∀ n : ℕ, κ^[n] d ∈ shadow r d
  | 0 => mem_shadow_self r d
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (h _).trans (iterate_collapse_mem_shadow h d n)

/-- **Collapse–resolution dichotomy.** A collapse that is invisible to the reading and separates
the property forbids the reading from resolving it. -/
theorem not_resolves_of_separating_collapse {r : D → O} {P : D → Prop} {κ : D → D}
    (hinv : Invisible r κ) {d : D} (hd : P d) (hκ : ¬ P (κ d)) : ¬ Resolves r P :=
  fun hres => hκ ((hres d (κ d) (collapse_mem_shadow hinv d)).mpr hd)

/-- **Vacuity form.** A reading invisible to a uniformly fatal collapse resolves the property only
when the property fails everywhere. -/
theorem forall_not_of_resolves_of_invisible {r : D → O} {P : D → Prop} {κ : D → D}
    (hres : Resolves r P) (hinv : Invisible r κ) (hfail : ∀ d : D, ¬ P (κ d)) :
    ∀ d : D, ¬ P d :=
  fun d hd => hfail d ((hres d (κ d) (collapse_mem_shadow hinv d)).mpr hd)

/-! ### 3. The order on readings -/

/-- `r` *refines* `r'` when equality of `r` implies equality of `r'`: every method reading `r'`
is available to a method reading `r`. -/
def Refines (r : D → O) (r' : D → O') : Prop := ∀ d e : D, e ∈ shadow r d → e ∈ shadow r' d

/-- A reading factoring through another refines it. -/
theorem refines_of_comp (r : D → O) {r' : D → O'} {g : O → O'} (h : ∀ d : D, r' d = g (r d)) :
    Refines r r' := fun d e he => by
  simp only [mem_shadow_iff, h]
  rw [mem_shadow_iff.mp he]

theorem shadow_subset_of_refines {r : D → O} {r' : D → O'} (h : Refines r r') (d : D) :
    shadow r d ⊆ shadow r' d := fun _ he => h d _ he

/-- A finer reading resolves whatever a coarser one resolves. -/
theorem Resolves.of_refines {r : D → O} {r' : D → O'} {P : D → Prop} (h : Refines r r')
    (hres : Resolves r' P) : Resolves r P := fun d e he => hres d e (h d e he)

/-- The joint reading of two readings. -/
def joinReading (r : D → O) (r' : D → O') : D → O × O' := fun d => (r d, r' d)

/-- Combining data intersects shadows: this is the whole arithmetic of combining methods. -/
theorem shadow_joinReading (r : D → O) (r' : D → O') (d : D) :
    shadow (joinReading r r') d = shadow r d ∩ shadow r' d := by
  ext x
  simp [shadow, joinReading, Prod.ext_iff]

theorem refines_joinReading_left (r : D → O) (r' : D → O') : Refines (joinReading r r') r :=
  fun d _ he => ((shadow_joinReading r r' d).subset he).1

theorem refines_joinReading_right (r : D → O) (r' : D → O') : Refines (joinReading r r') r' :=
  fun d _ he => ((shadow_joinReading r r' d).subset he).2

/-! ### 4. The resolution limit of a real invariant -/

variable {I I' : D → ℝ}

/-- The *resolution limit* of the invariant `I` for the reading `r` at `d`: the supremum of `I`
over the shadow. -/
noncomputable def resolutionLimit (I : D → ℝ) (r : D → O) (d : D) : ℝ :=
  sSup (I '' shadow r d)

/-- A method reading `r` *certifies* the bound `β` at `d` when `I ≤ β` on the whole shadow: this is
what "the reading implies the bound" means, no more and no less. -/
def Certifies (I : D → ℝ) (r : D → O) (d : D) (β : ℝ) : Prop := ∀ e ∈ shadow r d, I e ≤ β

theorem shadow_image_nonempty (I : D → ℝ) (r : D → O) (d : D) : (I '' shadow r d).Nonempty :=
  ⟨I d, ⟨d, mem_shadow_self r d, rfl⟩⟩

theorem le_resolutionLimit {r : D → O} {d : D} (hbdd : BddAbove (I '' shadow r d)) :
    I d ≤ resolutionLimit I r d :=
  le_csSup hbdd ⟨d, mem_shadow_self r d, rfl⟩

/-- **The resolution limit is exactly the strength of the reading.** -/
theorem certifies_iff_resolutionLimit_le {r : D → O} {d : D} {β : ℝ}
    (hbdd : BddAbove (I '' shadow r d)) :
    Certifies I r d β ↔ resolutionLimit I r d ≤ β := by
  rw [resolutionLimit, csSup_le_iff hbdd (shadow_image_nonempty I r d)]
  exact ⟨fun h _ hx => by obtain ⟨e, he, rfl⟩ := hx; exact h e he,
    fun h e he => h _ ⟨e, he, rfl⟩⟩

/-- The limit is itself certified: the reading proves its own bound and nothing sharper. -/
theorem certifies_resolutionLimit {r : D → O} {d : D} (hbdd : BddAbove (I '' shadow r d)) :
    Certifies I r d (resolutionLimit I r d) :=
  (certifies_iff_resolutionLimit_le hbdd).mpr le_rfl

/-- **Collapse floor.** Every invisible collapse, and every iterate of it, floors what the reading
can certify. -/
theorem iterate_le_resolutionLimit {r : D → O} {κ : D → D} (hinv : Invisible r κ) {d : D}
    (hbdd : BddAbove (I '' shadow r d)) (n : ℕ) : I (κ^[n] d) ≤ resolutionLimit I r d :=
  le_csSup hbdd ⟨κ^[n] d, iterate_collapse_mem_shadow hinv d n, rfl⟩

theorem le_of_certifies_of_invisible {r : D → O} {κ : D → D} {d : D} {β : ℝ}
    (hinv : Invisible r κ) (h : Certifies I r d β) : I (κ d) ≤ β :=
  h _ (collapse_mem_shadow hinv d)

/-- Refinement lowers the limit: more data, smaller shadow, sharper bound. -/
theorem resolutionLimit_le_of_refines {r : D → O} {r' : D → O'} (h : Refines r r') {d : D}
    (hbdd : BddAbove (I '' shadow r' d)) : resolutionLimit I r d ≤ resolutionLimit I r' d :=
  csSup_le_csSup hbdd (shadow_image_nonempty I r d)
    (Set.image_mono (shadow_subset_of_refines h d))

/-- Combining two readings certifies at most the better of the two. -/
theorem resolutionLimit_joinReading_le (r : D → O) (r' : D → O') {d : D}
    (hbdd : BddAbove (I '' shadow r d)) (hbdd' : BddAbove (I '' shadow r' d)) :
    resolutionLimit I (joinReading r r') d ≤ min (resolutionLimit I r d) (resolutionLimit I r' d) :=
  le_min (resolutionLimit_le_of_refines (refines_joinReading_left r r') hbdd)
    (resolutionLimit_le_of_refines (refines_joinReading_right r r') hbdd')

/-! ### 5. Faithful readings and transfer -/

/-- A reading is *faithful* for `I` when its limit is `I`: the reading determines the invariant. -/
def Faithful (I : D → ℝ) (r : D → O) : Prop := ∀ d : D, resolutionLimit I r d = I d

/-- **Transfer.** A reading faithful for `I` certifies the sharp bound for every invariant `I`
dominates through a monotone comparison: one faithful unit pays for all units it controls. -/
theorem certifies_of_faithful_of_dominated {r : D → O} (hbdd : ∀ d : D, BddAbove (I '' shadow r d))
    (hf : Faithful I r) {Φ : ℝ → ℝ} (hΦ : Monotone Φ) (hdom : ∀ e : D, I' e ≤ Φ (I e)) (d : D) :
    Certifies I' r d (Φ (I d)) := fun e he =>
  (hdom e).trans (hΦ (((hf d).symm ▸ le_csSup (hbdd d) ⟨e, he, rfl⟩ : I e ≤ I d)))

/-- Faithfulness is invariance of the invariant along the shadow. -/
theorem faithful_iff {r : D → O} (hbdd : ∀ d : D, BddAbove (I '' shadow r d)) :
    Faithful I r ↔ ∀ d : D, ∀ e ∈ shadow r d, I e ≤ I d := by
  refine ⟨fun hf d e he => ?_, fun h d => le_antisymm ?_ (le_resolutionLimit (hbdd d))⟩
  · exact (hf d) ▸ le_csSup (hbdd d) ⟨e, he, rfl⟩
  · exact (certifies_iff_resolutionLimit_le (hbdd d)).mp (h d)

/-! ### 6. The dual limit for lower bounds -/

/-- The *resolution floor*: the best lower bound on `I` the reading can certify. -/
noncomputable def resolutionFloor (I : D → ℝ) (r : D → O) (d : D) : ℝ :=
  sInf (I '' shadow r d)

/-- A method reading `r` certifies the lower bound `β` when `β ≤ I` on the whole shadow. -/
def CertifiesLower (I : D → ℝ) (r : D → O) (d : D) (β : ℝ) : Prop := ∀ e ∈ shadow r d, β ≤ I e

theorem resolutionFloor_le {r : D → O} {d : D} (hbdd : BddBelow (I '' shadow r d)) :
    resolutionFloor I r d ≤ I d :=
  csInf_le hbdd ⟨d, mem_shadow_self r d, rfl⟩

theorem certifiesLower_iff_le_resolutionFloor {r : D → O} {d : D} {β : ℝ}
    (hbdd : BddBelow (I '' shadow r d)) :
    CertifiesLower I r d β ↔ β ≤ resolutionFloor I r d := by
  rw [resolutionFloor, le_csInf_iff hbdd (shadow_image_nonempty I r d)]
  exact ⟨fun h _ hx => by obtain ⟨e, he, rfl⟩ := hx; exact h e he,
    fun h e he => h _ ⟨e, he, rfl⟩⟩

/-- The floor is the limit of the negated invariant: upper and lower theories are one theory. -/
theorem resolutionFloor_eq_neg_resolutionLimit (I : D → ℝ) (r : D → O) (d : D) :
    resolutionFloor I r d = -resolutionLimit (fun e => -I e) r d := by
  have himg : (fun e => -I e) '' shadow r d = -(I '' shadow r d) := by
    ext x
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨e, he, hx⟩
      exact ⟨e, he, by rw [← hx]; ring⟩
    · rintro ⟨e, he, hx⟩
      exact ⟨e, he, by rw [hx]; ring⟩
  rw [resolutionFloor, resolutionLimit, himg, Real.sSup_neg, neg_neg]

/-- Every invisible collapse ceilings what a lower bound can claim. -/
theorem le_of_certifiesLower_of_invisible {r : D → O} {κ : D → D} {d : D} {β : ℝ}
    (hinv : Invisible r κ) (h : CertifiesLower I r d β) : β ≤ I (κ d) :=
  h _ (collapse_mem_shadow hinv d)

/-! ### 7. Resolution is factorization -/

/-- **Resolution is factorization.** A reading resolves a property exactly when the property is a
function of the reading. This identifies the barrier statements of the corpus — "there is no
functional `Φ` of the observables with `P ↔ Φ(observables)`" — with failure of resolution. -/
theorem resolves_iff_exists_factorization {r : D → O} {P : D → Prop} :
    Resolves r P ↔ ∃ Φ : O → Prop, ∀ d : D, P d ↔ Φ (r d) := by
  refine ⟨fun hres => ⟨fun o => ∃ d : D, r d = o ∧ P d, fun d => ⟨fun hd => ⟨d, rfl, hd⟩, ?_⟩⟩,
    fun ⟨Φ, hΦ⟩ d e he => by rw [hΦ, hΦ, mem_shadow_iff.mp he]⟩
  rintro ⟨e, he, hPe⟩
  exact (hres d e he).mp hPe

/-- **Witness-pair form of the dichotomy.** One pair with the same reading and opposite verdicts
destroys resolution; no global collapse map is needed. -/
theorem not_resolves_of_pair {r : D → O} {P : D → Prop} {d e : D} (h : r e = r d) (hd : P d)
    (he : ¬ P e) : ¬ Resolves r P := fun hres => he ((hres d e h).mpr hd)

/-- A witness pair floors the resolution limit at the invariant of the witness. -/
theorem le_resolutionLimit_of_reading_eq {r : D → O} {d e : D} (h : r e = r d)
    (hbdd : BddAbove (I '' shadow r d)) : I e ≤ resolutionLimit I r d :=
  le_csSup hbdd ⟨e, h, rfl⟩

/-! ### 8. The algebra of blindness -/

/-- Post-processing a blind reading stays blind: no amount of computation on blind observables
sees the collapse. -/
theorem Invisible.comp {r : D → O} {κ : D → D} (h : Invisible r κ) (g : O → O') :
    Invisible (g ∘ r) κ := fun d => by simp [Function.comp, h d]

/-- Joining two blind readings stays blind. -/
theorem Invisible.joinReading {r : D → O} {r' : D → O'} {κ : D → D} (h : Invisible r κ)
    (h' : Invisible r' κ) : Invisible (joinReading r r') κ := fun d => by
  have hd : (r (κ d), r' (κ d)) = (r d, r' d) := by rw [h d, h' d]
  exact hd

/-- The joint reading of a whole family of readings. -/
def familyReading {ι : Type*} {O : ι → Type*} (r : ∀ i, D → O i) : D → ∀ i, O i :=
  fun d i => r i d

theorem shadow_familyReading {ι : Type*} {O : ι → Type*} (r : ∀ i, D → O i) (d : D) :
    shadow (familyReading r) d = ⋂ i, shadow (r i) d := by
  ext x
  simp [shadow, familyReading, funext_iff]

/-- **Arbitrarily many blind observables stay blind.** A method may read a family of any
cardinality: if every member misses the collapse, the family misses it. -/
theorem Invisible.familyReading {ι : Type*} {O : ι → Type*} {r : ∀ i, D → O i} {κ : D → D}
    (h : ∀ i, Invisible (r i) κ) : Invisible (familyReading r) κ := fun d =>
  funext fun i => h i d

theorem refines_familyReading {ι : Type*} {O : ι → Type*} (r : ∀ i, D → O i) (i : ι) :
    Refines (familyReading r) (r i) := fun d x hx => by
  have := (shadow_familyReading r d).subset hx
  exact Set.mem_iInter.mp this i


/-! ### 9. The resolution interval -/

/-- The **resolution interval**: the exact set of values of `I` a method reading `r` leaves open
at `d`. -/
noncomputable def resolutionInterval (I : D → ℝ) (r : D → O) (d : D) : Set ℝ :=
  Icc (resolutionFloor I r d) (resolutionLimit I r d)

theorem mem_resolutionInterval {I : D → ℝ} {r : D → O} {d : D} (hb : BddBelow (I '' shadow r d))
    (ha : BddAbove (I '' shadow r d)) : I d ∈ resolutionInterval I r d :=
  ⟨resolutionFloor_le hb, le_resolutionLimit ha⟩

/-- Refinement shrinks the interval from both ends: more data, fewer open values. -/
theorem resolutionInterval_subset_of_refines {I : D → ℝ} {r : D → O} {r' : D → O'}
    (h : Refines r r') {d : D} (hb : BddBelow (I '' shadow r' d))
    (ha : BddAbove (I '' shadow r' d)) :
    resolutionInterval I r d ⊆ resolutionInterval I r' d :=
  Icc_subset_Icc
    (csInf_le_csInf hb (shadow_image_nonempty I r d) (Set.image_mono (shadow_subset_of_refines h d)))
    (resolutionLimit_le_of_refines h ha)

/-- **Degeneracy criterion.** The interval collapses to a point exactly when the reading pins the
invariant on its whole shadow. -/
theorem resolutionFloor_eq_resolutionLimit_iff {I : D → ℝ} {r : D → O} {d : D}
    (hb : BddBelow (I '' shadow r d)) (ha : BddAbove (I '' shadow r d)) :
    resolutionFloor I r d = resolutionLimit I r d ↔ ∀ e ∈ shadow r d, I e = I d := by
  refine ⟨fun h e he => ?_, fun h => ?_⟩
  · have h1 : resolutionFloor I r d ≤ I e := csInf_le hb ⟨e, he, rfl⟩
    have h2 : I e ≤ resolutionLimit I r d := le_csSup ha ⟨e, he, rfl⟩
    have h3 : resolutionFloor I r d ≤ I d := resolutionFloor_le hb
    have h4 : I d ≤ resolutionLimit I r d := le_resolutionLimit ha
    rw [h] at h1 h3
    linarith
  · have hfl : resolutionFloor I r d = I d :=
      le_antisymm (resolutionFloor_le hb)
        ((certifiesLower_iff_le_resolutionFloor hb).mp fun e he => (h e he).ge)
    have hli : resolutionLimit I r d = I d :=
      le_antisymm ((certifies_iff_resolutionLimit_le ha).mp fun e he => (h e he).le)
        (le_resolutionLimit ha)
    rw [hfl, hli]

/-! ### 10. The floor theorem: a maximal member in the shadow fixes the limit -/

/-- **The floor theorem.** If `I` has a global maximum `M` attained by some datum in the shadow,
the limit is exactly `M`: the reading certifies nothing beyond the a priori bound. -/
theorem resolutionLimit_eq_of_mem_shadow_of_max {I : D → ℝ} {r : D → O} {d e : D} {M : ℝ}
    (hub : ∀ x : D, I x ≤ M) (he : e ∈ shadow r d) (hval : I e = M) :
    resolutionLimit I r d = M := by
  have hbdd : BddAbove (I '' shadow r d) := ⟨M, by rintro x ⟨y, -, rfl⟩; exact hub y⟩
  refine le_antisymm (csSup_le (shadow_image_nonempty I r d) ?_) ?_
  · rintro x ⟨y, -, rfl⟩
    exact hub y
  · exact hval ▸ le_csSup hbdd ⟨e, he, rfl⟩

/-- A reading that factors through `f` is floored by any maximal member with the same `f`-value. -/
theorem resolutionLimit_eq_of_factors_of_max {I : D → ℝ} {f : D → F} {r : F → O} {d e : D}
    {M : ℝ} (hub : ∀ x : D, I x ≤ M) (he : f e = f d) (hval : I e = M) :
    resolutionLimit I (r ∘ f) d = M :=
  resolutionLimit_eq_of_mem_shadow_of_max hub (show r (f e) = r (f d) by rw [he]) hval

/-- A constant reading is floored at the maximum: it certifies only the a priori bound. -/
theorem resolutionLimit_eq_of_constant_reading {I : D → ℝ} {r : D → O}
    (hconst : ∀ x y : D, r x = r y) {M : ℝ} (hub : ∀ x : D, I x ≤ M) {e : D} (hval : I e = M)
    (d : D) : resolutionLimit I r d = M :=
  resolutionLimit_eq_of_mem_shadow_of_max hub (hconst e d) hval

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
