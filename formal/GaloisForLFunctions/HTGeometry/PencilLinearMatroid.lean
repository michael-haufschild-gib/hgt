import GaloisForLFunctions.HTGeometry.PencilSRRealization

/-!
# The Stanley–Reisner ring embeds into the pencil carriers modulo constants

The exact kernel theorem says a class has constant carrier only if it is zero.  Since the carrier
assignment is `ℂ`-linear, that is exactly injectivity of the induced map

```text
ℂ[x_v]/I_Δ  ⟶  {functions}/{constants},   q ↦ P(T)F  mod constants.
```

So the linear span of finitely many carriers has the same dimension as the span of their
Stanley–Reisner classes: the *linear* layer of the differential-matroid statement.

* `constFunctions` — the constants as a submodule;
* `seedCarrierQuot` — the carrier map modulo constants;
* `seedCarrierQuot_injective` — the embedding;
* `linearIndependent_seedCarrierQuot` — independent classes have independent carriers.

The differential layer — with coefficients in `ℂ[δ]` rather than `ℂ` — does **not** follow from this
source: `exp ∘ exp` satisfies `y y'' − y y' − y'² = 0`, so every carrier here is differentially
algebraic and the differential transcendence degree of any finite family of them is zero.  That
layer needs a source whose translation orbit is differentially independent, which is a genuinely
different construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [DecidableEq α] {facets : Finset (Finset α)}
  {E : Type*} [AddCommMonoid E]

/-- The constant functions, as a `ℂ`-submodule. -/
def constFunctions (E : Type*) : Submodule ℂ (E → ℂ) :=
  Submodule.span ℂ {(fun _ => 1 : E → ℂ)}

omit [AddCommMonoid E] in
theorem mem_constFunctions_iff {f : E → ℂ} :
    f ∈ constFunctions E ↔ ∃ c : ℂ, f = fun _ => c := by
  rw [constFunctions, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext z; simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by funext z; simp⟩

omit [AddCommMonoid E] in
theorem mem_constFunctions_of_forall {f : E → ℂ} (h : ∀ x y, f x = f y) [Nonempty E] :
    f ∈ constFunctions E := by
  obtain ⟨z₀⟩ := ‹Nonempty E›
  exact mem_constFunctions_iff.mpr ⟨f z₀, funext fun z => h z z₀⟩

namespace PencilSeparation

/-- The carrier map of a pencil separation, read modulo constants. -/
def seedCarrierQuot (S : PencilSeparation facets E) :
    stanleyReisnerRing ℂ facets →ₗ[ℂ] ((E → ℂ) ⧸ constFunctions E) :=
  (constFunctions E).mkQ.comp (seedCarrier S.ω facets S.seed S.seedAnnihilates)

@[simp] theorem seedCarrierQuot_mk (S : PencilSeparation facets E) (P : MvPolynomial α ℂ) :
    S.seedCarrierQuot (Ideal.Quotient.mk (stanleyReisnerIdeal ℂ facets) P)
      = Submodule.Quotient.mk (seedCarrierPoly S.ω S.seed P) := rfl

/-- **The Stanley–Reisner ring embeds into the carriers modulo constants.** -/
theorem seedCarrierQuot_ker_eq_bot (S : PencilSeparation facets E) [Nonempty E]
    (hanti : FacetAntichain (↑facets : Set (Finset α))) :
    LinearMap.ker S.seedCarrierQuot = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := stanleyReisnerIdeal ℂ facets) q
  by_contra hne
  have hPI : P ∉ stanleyReisnerIdeal ℂ facets := fun hP =>
    hne ((Submodule.Quotient.mk_eq_zero _).mpr hP)
  obtain ⟨x, y, hxy⟩ := S.exists_ne_seedCarrierPoly hanti P hPI
  have hmem : seedCarrierPoly S.ω S.seed P ∈ constFunctions E := by
    rw [seedCarrierQuot_mk] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  obtain ⟨c, hc⟩ := mem_constFunctions_iff.mp hmem
  exact hxy (by rw [hc])

theorem seedCarrierQuot_injective (S : PencilSeparation facets E) [Nonempty E]
    (hanti : FacetAntichain (↑facets : Set (Finset α))) :
    Function.Injective S.seedCarrierQuot :=
  LinearMap.ker_eq_bot.mp (S.seedCarrierQuot_ker_eq_bot hanti)

/-- **Independent classes have independent carriers modulo constants.**  This is the linear layer of
the differential-matroid statement: the span of finitely many carriers has the dimension of the span
of their Stanley–Reisner classes. -/
theorem linearIndependent_seedCarrierQuot (S : PencilSeparation facets E) [Nonempty E]
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {ι : Type*}
    {q : ι → stanleyReisnerRing ℂ facets} (hq : LinearIndependent ℂ q) :
    LinearIndependent ℂ fun i => S.seedCarrierQuot (q i) :=
  hq.map' S.seedCarrierQuot (S.seedCarrierQuot_ker_eq_bot hanti)

/-- **A class is determined by its carrier up to constants.** -/
theorem eq_of_seedCarrier_sub_const (S : PencilSeparation facets E) [Nonempty E]
    (hanti : FacetAntichain (↑facets : Set (Finset α)))
    {q q' : stanleyReisnerRing ℂ facets} {c : ℂ}
    (h : ∀ z, seedCarrier S.ω facets S.seed S.seedAnnihilates q z
      = seedCarrier S.ω facets S.seed S.seedAnnihilates q' z + c) : q = q' := by
  have hsub : S.seedCarrierQuot (q - q') = 0 := by
    rw [seedCarrierQuot, LinearMap.comp_apply, map_sub]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    refine mem_constFunctions_iff.mpr ⟨c, ?_⟩
    funext z
    show seedCarrier S.ω facets S.seed S.seedAnnihilates q z
      - seedCarrier S.ω facets S.seed S.seedAnnihilates q' z = c
    rw [h z]
    ring
  have hzero : S.seedCarrierQuot (q - q') = S.seedCarrierQuot 0 := by
    rw [hsub, map_zero]
  have hqq := S.seedCarrierQuot_injective hanti hzero
  exact sub_eq_zero.mp hqq

end PencilSeparation

end

end GaloisForLFunctions.HTGeometry
