import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation

/-!
# The general reduced simplicial cochain complex of an arbitrary finite complex

The Hochster source-coherence duality pairs the Koszul (Tor) side of a Stanley–Reisner ring with the
*reduced simplicial cohomology* of induced subcomplexes.  The corpus already carries the algebraic
side in full generality (`GeneralKoszulComplex`: the vertex Koszul differential `koszulD` at every
degree with `d² = 0`), but the topological side existed only in low degree and only for graphs
(`GraphCoboundary`, `ReducedH0Components`, `ReducedH1FirstBetti`).  This file supplies the missing
degree-uniform topological half: the **reduced simplicial cochain complex of an arbitrary finite
complex, in every degree**, with its `δ² = 0`.

The construction avoids any ordered-tuple (`Fin.succAbove`) bookkeeping.  A cochain is a function on
*all* finite vertex sets, and the coboundary is the signed face sum

```text
(δ f)(σ) = ∑_{v ∈ σ} (-1)^{#{u ∈ σ : u < v}} · f (σ \ {v}),
```

so the empty face is present and the complex is automatically the **reduced** one.  Because the
formula never mentions the cardinality of `σ`, one single statement `δ ∘ δ = 0` covers every degree
at once; the grading by `#σ` is recovered afterwards (`cardCochains`, `simplicialCoboundary_mem_cardCochains`).

The cancellation is the familiar `(u,v) ↔ (v,u)` involution over ordered distinct pairs of `σ`,
against the incidence-sign identity

`faceSign σ u · faceSign (σ \ {u}) v + faceSign σ v · faceSign (σ \ {v}) u = 0`,

which is proved from exactly two facts about the sign: erasing a *smaller* vertex flips it, erasing a
*larger* vertex preserves it.  The pair sum is discharged by the corpus involution lemma
`antisym_sigma_sum_zero`, the same device that runs the Koszul `d² = 0` proofs — so both halves of the
Hochster correspondence now rest on one cancellation principle.

Passing from the full simplex on `α` to a prescribed complex `Δ` (given by its facet family) is done
by a quotient rather than a guard: the cochains vanishing on every face of `Δ` form a `δ`-stable
submodule (faces are closed downwards), so the cochain complex of `Δ` is the quotient complex, with
`δ_Δ² = 0` inherited (`complexCoboundary_complexCoboundary`).  No decidability of `IsFaceOf` is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-! ### The incidence sign -/

/-- The incidence sign of a vertex in a finite vertex set: `(-1)` to the number of strictly smaller
members of the set.  This is the sign of the vertex's position in the increasing enumeration, which
is what the simplicial coboundary needs. -/
def faceSign (F : Type*) [CommRing F] (σ : Finset α) (v : α) : F :=
  (-1) ^ (σ.filter (· < v)).card

omit [DecidableEq α] in
@[simp]
theorem faceSign_empty (v : α) : faceSign F (∅ : Finset α) v = 1 := by
  simp [faceSign]

omit [DecidableEq α] in
/-- The incidence sign is its own inverse: it is `±1`. -/
@[simp]
theorem faceSign_mul_self (σ : Finset α) (v : α) :
    faceSign F σ v * faceSign F σ v = 1 := by
  show (-1 : F) ^ _ * (-1 : F) ^ _ = 1
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **Erasing a smaller vertex flips the incidence sign.** -/
theorem faceSign_erase_of_lt {σ : Finset α} {u v : α} (hu : u ∈ σ) (huv : u < v) :
    faceSign F (σ.erase u) v = - faceSign F σ v := by
  have h1 : (σ.erase u).filter (· < v) = (σ.filter (· < v)).erase u := Finset.filter_erase _ _ _
  have h2 : u ∈ σ.filter (· < v) := Finset.mem_filter.mpr ⟨hu, huv⟩
  have h3 : ((σ.filter (· < v)).erase u).card + 1 = (σ.filter (· < v)).card :=
    Finset.card_erase_add_one h2
  show (-1 : F) ^ ((σ.erase u).filter (· < v)).card = -(-1 : F) ^ (σ.filter (· < v)).card
  rw [h1, ← h3, pow_succ]
  ring

/-- **Erasing a larger vertex preserves the incidence sign.** -/
theorem faceSign_erase_of_gt {σ : Finset α} {u v : α} (hvu : v < u) :
    faceSign F (σ.erase u) v = faceSign F σ v := by
  have h1 : (σ.erase u).filter (· < v) = (σ.filter (· < v)).erase u := Finset.filter_erase _ _ _
  have h2 : u ∉ σ.filter (· < v) := by
    simp only [Finset.mem_filter, not_and, not_lt]
    exact fun _ => hvu.le
  show (-1 : F) ^ ((σ.erase u).filter (· < v)).card = (-1 : F) ^ (σ.filter (· < v)).card
  rw [h1, Finset.erase_eq_self.mpr h2]

/-- **The incidence-sign antisymmetry.**  For two distinct vertices of a finite set, the two ways of
deleting them one after the other carry opposite signs.  This is the whole content of `δ² = 0`. -/
theorem faceSign_mul_faceSign_erase_antisymm {σ : Finset α} {u v : α}
    (hu : u ∈ σ) (hv : v ∈ σ) (huv : u ≠ v) :
    faceSign F σ u * faceSign F (σ.erase u) v + faceSign F σ v * faceSign F (σ.erase v) u = 0 := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [faceSign_erase_of_lt hu h, faceSign_erase_of_gt h]; ring
  · rw [faceSign_erase_of_gt h, faceSign_erase_of_lt hv h]; ring

/-! ### The coboundary on all finite vertex sets -/

/-- The **reduced simplicial coboundary**: `(δ f)(σ) = ∑_{v ∈ σ} faceSign σ v · f (σ \ {v})`.  The
empty set is a legitimate argument, so this is the reduced (augmented) complex; and the formula is
uniform in the cardinality of `σ`, so it is the coboundary in every degree at once. -/
def simplicialCoboundary (F : Type*) [CommRing F] (f : Finset α → F) (σ : Finset α) : F :=
  ∑ v ∈ σ, faceSign F σ v * f (σ.erase v)

theorem simplicialCoboundary_apply (f : Finset α → F) (σ : Finset α) :
    simplicialCoboundary F f σ = ∑ v ∈ σ, faceSign F σ v * f (σ.erase v) := rfl

@[simp]
theorem simplicialCoboundary_empty (f : Finset α → F) :
    simplicialCoboundary F f ∅ = 0 := by
  simp [simplicialCoboundary]

/-- The reduced simplicial coboundary as an `F`-linear map on cochains. -/
def simplicialCoboundaryₗ (F : Type*) [CommRing F] :
    (Finset α → F) →ₗ[F] (Finset α → F) where
  toFun := simplicialCoboundary F
  map_add' f g := by
    funext σ
    simp only [simplicialCoboundary, Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' r f := by
    funext σ
    simp only [simplicialCoboundary, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)

@[simp]
theorem simplicialCoboundaryₗ_apply (f : Finset α → F) :
    simplicialCoboundaryₗ F f = simplicialCoboundary F f := rfl

/-- The guarded double-deletion term: the summand of `δ²` on the ordered distinct pairs of `σ`,
extended by `0` off those pairs so that it is antisymmetric as a function of two free vertices. -/
def cochainSwapTerm (F : Type*) [CommRing F] (f : Finset α → F) (σ : Finset α) (u v : α) : F :=
  if u ∈ σ ∧ v ∈ σ ∧ u ≠ v then
    faceSign F σ u * faceSign F (σ.erase u) v * f ((σ.erase u).erase v)
  else 0

theorem cochainSwapTerm_antisymm (f : Finset α → F) (σ : Finset α) (u v : α) :
    cochainSwapTerm F f σ u v + cochainSwapTerm F f σ v u = 0 := by
  by_cases h : u ∈ σ ∧ v ∈ σ ∧ u ≠ v
  · have h' : v ∈ σ ∧ u ∈ σ ∧ v ≠ u := ⟨h.2.1, h.1, Ne.symm h.2.2⟩
    show (if u ∈ σ ∧ v ∈ σ ∧ u ≠ v then _ else _)
        + (if v ∈ σ ∧ u ∈ σ ∧ v ≠ u then _ else _) = 0
    rw [if_pos h, if_pos h', Finset.erase_right_comm (a := v) (b := u) (s := σ)]
    have hs := faceSign_mul_faceSign_erase_antisymm (F := F) h.1 h.2.1 h.2.2
    linear_combination f ((σ.erase u).erase v) * hs
  · have h' : ¬ (v ∈ σ ∧ u ∈ σ ∧ v ≠ u) := fun hc => h ⟨hc.2.1, hc.1, Ne.symm hc.2.2⟩
    show (if u ∈ σ ∧ v ∈ σ ∧ u ≠ v then _ else _)
        + (if v ∈ σ ∧ u ∈ σ ∧ v ≠ u then _ else _) = 0
    rw [if_neg h, if_neg h', add_zero]

/-- **`δ² = 0` for the general reduced simplicial cochain complex.**  Unconditional, in every degree
at once, over any commutative ring, for any linearly ordered vertex type.  This is the topological
half of the Hochster correspondence, the mirror of `koszulD_koszulD_eq_zero`. -/
theorem simplicialCoboundary_simplicialCoboundary (f : Finset α → F) :
    simplicialCoboundary F (simplicialCoboundary F f) = 0 := by
  funext σ
  show (∑ v ∈ σ, faceSign F σ v * ∑ u ∈ σ.erase v, faceSign F (σ.erase v) u * f ((σ.erase v).erase u))
      = 0
  have step : ∀ v ∈ σ,
      faceSign F σ v * (∑ u ∈ σ.erase v, faceSign F (σ.erase v) u * f ((σ.erase v).erase u))
        = ∑ u ∈ σ.erase v, cochainSwapTerm F f σ v u := by
    intro v hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.mem_erase] at hu
    show _ = if v ∈ σ ∧ u ∈ σ ∧ v ≠ u then _ else _
    rw [if_pos ⟨hv, hu.2, Ne.symm hu.1⟩]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_sigma']
  exact antisym_sigma_sum_zero σ (cochainSwapTerm F f σ) (cochainSwapTerm_antisymm f σ)

/-- `δ ∘ δ = 0` in linear-map form: the cochains of the full simplex form a genuine complex. -/
theorem simplicialCoboundaryₗ_comp_self :
    (simplicialCoboundaryₗ (α := α) F) ∘ₗ (simplicialCoboundaryₗ (α := α) F) = 0 :=
  LinearMap.ext fun f => simplicialCoboundary_simplicialCoboundary f

/-! ### The cardinality grading -/

/-- The degree-`c` piece: cochains supported on vertex sets of cardinality `c`, i.e. on the
`(c-1)`-dimensional faces.  Degree `c = 0` is the augmentation slot of the reduced complex. -/
def cardCochains (F : Type*) [CommRing F] (c : ℕ) : Submodule F (Finset α → F) where
  carrier := {f | ∀ σ : Finset α, σ.card ≠ c → f σ = 0}
  add_mem' hf hg := fun σ hσ => by
    simp only [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun σ hσ => by
    show r * _ = 0
    rw [hf σ hσ, mul_zero]

omit [DecidableEq α] [LinearOrder α] in
theorem mem_cardCochains {c : ℕ} {f : Finset α → F} :
    f ∈ cardCochains F c ↔ ∀ σ : Finset α, σ.card ≠ c → f σ = 0 := Iff.rfl

/-- **The coboundary raises the cardinality degree by one.**  With `cardCochains` this exhibits the
reduced simplicial cochain complex as an honest graded complex `C⁰ → C¹ → C² → ⋯`, `Cᶜ` being the
cochains on the `(c-1)`-faces. -/
theorem simplicialCoboundary_mem_cardCochains {c : ℕ} {f : Finset α → F}
    (hf : f ∈ cardCochains F c) :
    simplicialCoboundary F f ∈ cardCochains F (c + 1) := by
  intro σ hσ
  show ∑ v ∈ σ, faceSign F σ v * f (σ.erase v) = 0
  refine Finset.sum_eq_zero (fun v hv => ?_)
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr ⟨v, hv⟩
  have hcard : (σ.erase v).card ≠ c := by
    rw [Finset.card_erase_of_mem hv]; omega
  rw [hf _ hcard, mul_zero]

/-! ### The cochain complex of a prescribed finite complex -/

/-- Cochains vanishing on every face of the complex: the kernel of restriction from the full simplex
on `α` to the complex `Δ` presented by `facets`. -/
def faceVanishingCochains (F : Type*) [CommRing F] (facets : Finset (Finset α)) :
    Submodule F (Finset α → F) where
  carrier := {f | ∀ σ : Finset α, IsFaceOf (↑facets : Set (Finset α)) σ → f σ = 0}
  add_mem' hf hg := fun σ hσ => by
    simp only [Pi.add_apply, hf σ hσ, hg σ hσ, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' r f hf := fun σ hσ => by
    show r * _ = 0
    rw [hf σ hσ, mul_zero]

omit [DecidableEq α] [LinearOrder α] in
theorem mem_faceVanishingCochains {facets : Finset (Finset α)} {f : Finset α → F} :
    f ∈ faceVanishingCochains F facets ↔
      ∀ σ : Finset α, IsFaceOf (↑facets : Set (Finset α)) σ → f σ = 0 := Iff.rfl

/-- **The restriction kernel is `δ`-stable.**  Faces are closed under deletion of a vertex, so a
cochain vanishing on all faces of `Δ` has coboundary vanishing on all faces of `Δ`. -/
theorem simplicialCoboundary_mem_faceVanishingCochains (facets : Finset (Finset α))
    {f : Finset α → F} (hf : f ∈ faceVanishingCochains F facets) :
    simplicialCoboundary F f ∈ faceVanishingCochains F facets := by
  intro σ hσ
  show ∑ v ∈ σ, faceSign F σ v * f (σ.erase v) = 0
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [hf _ (isFaceOf_mono (Finset.erase_subset v σ) hσ), mul_zero]

/-- The reduced simplicial cochains of the complex `Δ` presented by `facets`: cochains on the full
simplex modulo those vanishing on all faces of `Δ`, i.e. exactly the functions on the faces of `Δ`
(including the empty face, so the complex is reduced). -/
abbrev complexCochains (F : Type*) [CommRing F] (facets : Finset (Finset α)) : Type _ :=
  (Finset α → F) ⧸ faceVanishingCochains F facets

/-- The reduced simplicial coboundary of the complex `Δ`, induced on the quotient. -/
def complexCoboundaryₗ (F : Type*) [CommRing F] (facets : Finset (Finset α)) :
    complexCochains F facets →ₗ[F] complexCochains F facets :=
  Submodule.mapQ _ _ (simplicialCoboundaryₗ F)
    (fun _ hf => simplicialCoboundary_mem_faceVanishingCochains facets hf)

@[simp]
theorem complexCoboundaryₗ_mk (facets : Finset (Finset α)) (f : Finset α → F) :
    complexCoboundaryₗ F facets (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (simplicialCoboundary F f) :=
  rfl

/-- **`δ_Δ² = 0` for an arbitrary finite complex.**  The reduced simplicial cochain complex of any
finite complex is a genuine complex in every degree, unconditionally. -/
theorem complexCoboundary_complexCoboundary (facets : Finset (Finset α))
    (x : complexCochains F facets) :
    complexCoboundaryₗ F facets (complexCoboundaryₗ F facets x) = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [complexCoboundaryₗ_mk, complexCoboundaryₗ_mk, simplicialCoboundary_simplicialCoboundary,
    ← Submodule.Quotient.mk_zero]

theorem complexCoboundaryₗ_comp_self (facets : Finset (Finset α)) :
    (complexCoboundaryₗ F facets) ∘ₗ (complexCoboundaryₗ F facets) = 0 :=
  LinearMap.ext fun x => complexCoboundary_complexCoboundary facets x

end

end GaloisForLFunctions.HTGeometry
