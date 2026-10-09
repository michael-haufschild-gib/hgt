import GaloisForLFunctions.HTGeometry.FinsetCechHomotopy

/-!
# Alternating Čech complexes of a finite cover, abstractly

A *Čech datum* on a linearly ordered index type `T` is an abelian group `D s` for every finite
subset `s` (the sections over the intersection of the members indexed by `s`; the empty subset is
the covered set itself) together with restriction maps `D s → D t` for `s ⊆ t`, functorial in the
inclusions.  A cochain is a family `c s ∈ D s`; it has degree `p` when it is supported on the
subsets with `p + 1` elements.  The differential is the alternating sum

`(dc) s = ∑_{u ∈ s} ε(s, u) · c(s ∖ u)|_s`.

Every value of a differential computed below `s` can be transported into the single group `D s`;
there the complex becomes the constant-coefficient complex of `cechDModule`, so `d ∘ d = 0`
follows from the constant-coefficient identity.

The main structural result is the **snake chase**: for morphisms `F → G → Q` of Čech data that are
short exact on the subsets of the relevant cardinalities, exactness of `F` one degree up and of `G`
in a given degree gives exactness of `Q` in that degree — every cocycle of `Q` is the image of a
coboundary of `G`.  This is the one homological input of Leray's theorem and of Cartan's criterion.

* `HTGeometry.FinsetCechDatum` : the data.
* `HTGeometry.FinsetCechDatum.d_d` : `d ∘ d = 0`.
* `HTGeometry.FinsetCechDatum.ExactAt` : exactness of the augmented complex in a degree.
* `HTGeometry.FinsetCechDatum.chase_lift` : the snake chase.
-/

namespace HTGeometry

open GaloisForLFunctions.HTGeometry.BorelWeil

universe v

/-- A Čech datum: an abelian group for every finite subset of indices, and restriction maps along
inclusions of subsets. -/
structure FinsetCechDatum (T : Type*) where
  /-- The sections over the intersection indexed by a subset. -/
  obj : Finset T → Type v
  [grp : ∀ s, AddCommGroup (obj s)]
  /-- Restriction to a smaller intersection. -/
  res : ∀ {s t : Finset T}, s ⊆ t → obj s →+ obj t
  res_refl : ∀ (s : Finset T) (x : obj s), res (Finset.Subset.refl s) x = x
  res_res : ∀ {s t r : Finset T} (h₁ : s ⊆ t) (h₂ : t ⊆ r) (x : obj s),
    res h₂ (res h₁ x) = res (h₁.trans h₂) x

attribute [instance] FinsetCechDatum.grp

namespace FinsetCechDatum

variable {T : Type*} [DecidableEq T] [LinearOrder T] (D : FinsetCechDatum.{v} T)

/-- Čech cochains: a section over every intersection. -/
abbrev Cochain := ∀ s : Finset T, D.obj s

/-- **The Čech differential.** -/
def d (c : D.Cochain) : D.Cochain := fun s =>
  ∑ u ∈ s, (cechSign s u : ℤ) • D.res (Finset.erase_subset u s) (c (s.erase u))

/-- A cochain has degree `p` when it lives on the subsets with `p + 1` elements. -/
def IsDeg (c : D.Cochain) (p : ℕ) : Prop := ∀ s : Finset T, s.card ≠ p + 1 → c s = 0

/-- A cochain of degree `-1`: it lives on the empty subset. -/
def IsBot (c : D.Cochain) : Prop := ∀ s : Finset T, s.Nonempty → c s = 0

/-- **Exactness in degree `p`** of the augmented complex: every degree-`p` cocycle is the
differential of a cochain one degree lower (of degree `-1`, i.e. a section over the covered set,
when `p = 0`). -/
def ExactAt (p : ℕ) : Prop :=
  ∀ c : D.Cochain, D.IsDeg c p → D.d c = 0 →
    ∃ b : D.Cochain, (∀ s : Finset T, s.card ≠ p → b s = 0) ∧ D.d b = c

/-- **Exactness in degree `-1`**: a section over the covered set that restricts to zero on every
member of the cover is zero. -/
def ExactBot : Prop := ∀ c : D.Cochain, D.IsBot c → D.d c = 0 → c = 0

variable {D}

omit [DecidableEq T] [LinearOrder T] in
theorem res_congr {s s' t : Finset T} (h : s = s') (x : D.obj s) (hs : s ⊆ t) :
    D.res hs x = D.res (h ▸ hs) (h ▸ x) := by
  subst h
  rfl

omit [DecidableEq T] [LinearOrder T] in
/-- Restrictions of the values of a cochain at equal subsets agree. -/
theorem res_cochain_congr (c : D.Cochain) {s s' t : Finset T} (e : s = s') (h : s ⊆ t)
    (h' : s' ⊆ t) : D.res h (c s) = D.res h' (c s') := by
  subst e
  rfl

variable (D)

/-- Transport of a cochain into the sections over `s`, on the subsets of `s`. -/
def pull (c : D.Cochain) (s : Finset T) : Finset T → D.obj s := fun t =>
  if h : t ⊆ s then D.res h (c t) else 0

omit [LinearOrder T] in
theorem pull_of_subset (c : D.Cochain) {s t : Finset T} (h : t ⊆ s) :
    D.pull c s t = D.res h (c t) := dif_pos h

/-- **Restricting a differential is the constant-coefficient differential of the transported
cochain.** -/
theorem res_d (c : D.Cochain) {s t : Finset T} (h : t ⊆ s) :
    D.res h (D.d c t) = cechDModule ℤ (D.pull c s) t := by
  rw [d, map_sum, cechDModule]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_zsmul, D.res_res, D.pull_of_subset c ((Finset.erase_subset u t).trans h)]

theorem d_apply_eq (c : D.Cochain) (s : Finset T) :
    D.d c s = cechDModule ℤ (D.pull c s) s := by
  rw [← D.res_d c (Finset.Subset.refl s), D.res_refl]

/-- **`d ∘ d = 0`.** -/
theorem d_d (c : D.Cochain) : D.d (D.d c) = 0 := by
  funext s
  rw [d_apply_eq, Pi.zero_apply]
  have hpull : ∀ t ∈ s.powerset, D.pull (D.d c) s t = cechDModule ℤ (D.pull c s) t := by
    intro t ht
    rw [D.pull_of_subset _ (Finset.mem_powerset.mp ht), res_d]
  have key : cechDModule ℤ (D.pull (D.d c) s) s
      = cechDModule ℤ (cechDModule ℤ (D.pull c s)) s := by
    rw [cechDModule, cechDModule]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hpull _ (Finset.mem_powerset.mpr (Finset.erase_subset u s))]
  rw [key, cechDModule_cechDModule]
  rfl

theorem d_add (c c' : D.Cochain) : D.d (c + c') = D.d c + D.d c' := by
  funext s
  simp only [d, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

theorem d_sub (c c' : D.Cochain) : D.d (c - c') = D.d c - D.d c' := by
  funext s
  simp only [d, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem d_zero : D.d 0 = 0 := by
  funext s
  simp [d]

theorem d_isDeg {c : D.Cochain} {p : ℕ} (hc : D.IsDeg c p) : D.IsDeg (D.d c) (p + 1) := by
  intro s hs
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [hc (s.erase u) ?_, map_zero, smul_zero]
  rw [Finset.card_erase_of_mem hu]
  have : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  omega

/-- The differential of a cochain supported on the subsets with `p` elements is supported on the
subsets with `p + 1` elements. -/
theorem d_eq_zero_of_card {b : D.Cochain} {p : ℕ} (hb : ∀ t : Finset T, t.card ≠ p → b t = 0)
    (s : Finset T) (hs : s.card ≠ p + 1) : D.d b s = 0 := by
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [hb (s.erase u) ?_, map_zero, smul_zero]
  rw [Finset.card_erase_of_mem hu]
  have : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  omega

/-- The differential as an additive map. -/
def dHom : D.Cochain →+ D.Cochain where
  toFun := D.d
  map_zero' := D.d_zero
  map_add' := D.d_add

theorem d_isDeg_of_isBot {c : D.Cochain} (hc : D.IsBot c) : D.IsDeg (D.d c) 0 := by
  intro s hs
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [hc (s.erase u) ?_, map_zero, smul_zero]
  have : 0 < s.card := Finset.card_pos.mpr ⟨u, hu⟩
  rw [← Finset.card_pos, Finset.card_erase_of_mem hu]
  omega

/-! ## Morphisms of Čech data -/

/-- A morphism of Čech data: maps on sections commuting with restriction. -/
structure Hom (D E : FinsetCechDatum.{v} T) where
  /-- The map on sections over each intersection. -/
  app : ∀ s : Finset T, D.obj s →+ E.obj s
  comm : ∀ {s t : Finset T} (h : s ⊆ t) (x : D.obj s), E.res h (app s x) = app t (D.res h x)

variable {D} {E : FinsetCechDatum.{v} T}

/-- The induced map on cochains. -/
def Hom.onCochain (φ : Hom D E) (c : D.Cochain) : E.Cochain := fun s => φ.app s (c s)

theorem Hom.d_onCochain (φ : Hom D E) (c : D.Cochain) :
    E.d (φ.onCochain c) = φ.onCochain (D.d c) := by
  funext s
  simp only [d, Hom.onCochain, map_sum, map_zsmul, φ.comm]

omit [DecidableEq T] [LinearOrder T] in
theorem Hom.onCochain_sub (φ : Hom D E) (c c' : D.Cochain) :
    φ.onCochain (c - c') = φ.onCochain c - φ.onCochain c' := by
  funext s
  simp [Hom.onCochain]

omit [DecidableEq T] [LinearOrder T] in
theorem Hom.onCochain_isDeg (φ : Hom D E) {c : D.Cochain} {p : ℕ} (hc : D.IsDeg c p) :
    E.IsDeg (φ.onCochain c) p := by
  intro s hs
  simp [Hom.onCochain, hc s hs]

/-! ## The snake chase -/

section Chase

variable {F G Q : FinsetCechDatum.{v} T} (ι : Hom F G) (π : Hom G Q)

/-- **The snake chase, with a given lift.**  Let `F → G → Q` be exact on the intersections of
`p + 2` and `p + 3` members (only the parts of exactness used are assumed), and let `c` be a
degree-`p` cocycle of `Q` with a degree-`p` lift `g` to `G`.  If `F` is exact in degree `p + 1` and
`G` in degree `p`, then `c` is the differential of the image of a `G`-cochain one degree lower. -/
theorem chase_lift_of_lift (p : ℕ)
    (hπι : ∀ s : Finset T, s.card = p + 1 → ∀ x, π.app s (ι.app s x) = 0)
    (hexact : ∀ s : Finset T, s.card = p + 2 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = p + 3 → Function.Injective (ι.app s))
    (hF : F.ExactAt (p + 1)) (hG : G.ExactAt p)
    {c : Q.Cochain} (hdc : Q.d c = 0) (g : G.Cochain) (hg : G.IsDeg g p)
    (hπg : π.onCochain g = c) :
    ∃ t : G.Cochain, (∀ s : Finset T, s.card ≠ p → t s = 0) ∧ Q.d (π.onCochain t) = c := by
  classical
  -- the differential of the lift comes from `F`
  have hdg : G.IsDeg (G.d g) (p + 1) := G.d_isDeg hg
  have hπdg : ∀ s, π.app s (G.d g s) = 0 := by
    intro s
    have := congrFun (π.d_onCochain g) s
    rw [hπg, hdc] at this
    exact this.symm
  let f : F.Cochain := fun s =>
    if hs : s.card = p + 2 then Classical.choose (hexact s hs (G.d g s) (hπdg s)) else 0
  have hf : F.IsDeg f (p + 1) := fun s hs => dif_neg hs
  have hιf : ι.onCochain f = G.d g := by
    funext s
    by_cases hs : s.card = p + 2
    · change ι.app s (f s) = G.d g s
      simp only [f, dif_pos hs]
      exact Classical.choose_spec (hexact s hs (G.d g s) (hπdg s))
    · change ι.app s (f s) = G.d g s
      rw [hf s hs, hdg s hs, map_zero]
  -- it is a cocycle of `F`
  have hdf : F.d f = 0 := by
    funext s
    by_cases hs : s.card = p + 3
    · apply hinj s hs
      have := congrFun (ι.d_onCochain f) s
      rw [hιf, G.d_d] at this
      change ι.app s (F.d f s) = ι.app s 0
      rw [map_zero]
      exact this.symm
    · exact F.d_isDeg hf s hs
  obtain ⟨h, hh, hdh⟩ := hF f hf hdf
  -- correct the lift by the image of `h`
  have hh' : F.IsDeg h p := fun s hs => hh s hs
  have hcocycle : G.d (g - ι.onCochain h) = 0 := by
    rw [G.d_sub, ι.d_onCochain, hdh, hιf, sub_self]
  have hdeg : G.IsDeg (g - ι.onCochain h) p := by
    intro s hs
    change g s - ι.app s (h s) = 0
    rw [hg s hs, hh' s hs, map_zero, sub_zero]
  obtain ⟨t, ht, hdt⟩ := hG _ hdeg hcocycle
  refine ⟨t, ht, ?_⟩
  rw [π.d_onCochain, hdt, π.onCochain_sub, hπg]
  have hzero : π.onCochain (ι.onCochain h) = 0 := by
    funext s
    by_cases hs : s.card = p + 1
    · exact hπι s hs (h s)
    · change π.app s (ι.app s (h s)) = 0
      rw [hh' s hs, map_zero, map_zero]
  rw [hzero, sub_zero]

/-- **The snake chase.**  Let `F → G → Q` be short exact on the intersections of `p + 1`,
`p + 2` and `p + 3` members (only the parts of exactness used are assumed).  If `F` is exact in
degree `p + 1` and `G` in degree `p`, then every degree-`p` cocycle of `Q` is the image of a
coboundary of `G`: it is the differential of the image of a `G`-cochain one degree lower. -/
theorem chase_lift (p : ℕ)
    (hπι : ∀ s : Finset T, s.card = p + 1 → ∀ x, π.app s (ι.app s x) = 0)
    (hsurj : ∀ s : Finset T, s.card = p + 1 → Function.Surjective (π.app s))
    (hexact : ∀ s : Finset T, s.card = p + 2 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = p + 3 → Function.Injective (ι.app s))
    (hF : F.ExactAt (p + 1)) (hG : G.ExactAt p)
    {c : Q.Cochain} (hc : Q.IsDeg c p) (hdc : Q.d c = 0) :
    ∃ t : G.Cochain, (∀ s : Finset T, s.card ≠ p → t s = 0) ∧ Q.d (π.onCochain t) = c := by
  classical
  let g : G.Cochain := fun s =>
    if hs : s.card = p + 1 then Classical.choose (hsurj s hs (c s)) else 0
  have hg : G.IsDeg g p := fun s hs => dif_neg hs
  have hπg : π.onCochain g = c := by
    funext s
    by_cases hs : s.card = p + 1
    · change π.app s (g s) = c s
      simp only [g, dif_pos hs]
      exact Classical.choose_spec (hsurj s hs (c s))
    · change π.app s (g s) = c s
      rw [hg s hs, hc s hs, map_zero]
  exact chase_lift_of_lift ι π p hπι hexact hinj hF hG hdc g hg hπg

/-- **Exactness passes to the quotient.** -/
theorem exactAt_of_chase (p : ℕ)
    (hπι : ∀ s : Finset T, s.card = p + 1 → ∀ x, π.app s (ι.app s x) = 0)
    (hsurj : ∀ s : Finset T, s.card = p + 1 → Function.Surjective (π.app s))
    (hexact : ∀ s : Finset T, s.card = p + 2 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = p + 3 → Function.Injective (ι.app s))
    (hF : F.ExactAt (p + 1)) (hG : G.ExactAt p) : Q.ExactAt p := by
  intro c hc hdc
  obtain ⟨t, ht, hdt⟩ := chase_lift ι π p hπι hsurj hexact hinj hF hG hc hdc
  refine ⟨π.onCochain t, fun s hs => ?_, hdt⟩
  change π.app s (t s) = 0
  rw [ht s hs, map_zero]

/-- **A section over the covered set lifts as soon as its restrictions to the cover do.**  If the
quotient is separated over the cover and the chase applies in degree `0`, a section of `Q` over the
covered set whose restrictions to the members of the cover lift to `G` lifts to `G`. -/
theorem lift_bot_of_chase
    (hπι : ∀ s : Finset T, s.card = 1 → ∀ x, π.app s (ι.app s x) = 0)
    (hexact : ∀ s : Finset T, s.card = 2 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = 3 → Function.Injective (ι.app s))
    (hF : F.ExactAt 1) (hG : G.ExactAt 0) (hQ : Q.ExactBot) (q : Q.obj ∅)
    (g : G.Cochain) (hg : G.IsDeg g 0)
    (hπg : ∀ s : Finset T, s.card = 1 → π.app s (g s) = Q.res (Finset.empty_subset s) q) :
    ∃ t : G.obj ∅, π.app ∅ t = q := by
  classical
  let c : Q.Cochain := fun s => if hs : s = ∅ then hs ▸ q else 0
  have hcbot : Q.IsBot c := fun s hs => dif_neg hs.ne_empty
  have hc0 : c ∅ = q := dif_pos rfl
  have hdc : Q.d c = π.onCochain g := by
    funext s
    by_cases hs : s.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
      change _ = π.app {i} (g {i})
      rw [hπg {i} hs, d, Finset.sum_singleton,
        res_cochain_congr c (Finset.erase_singleton i) _ (Finset.empty_subset _), hc0]
      have hsign : (cechSign ({i} : Finset T) i : ℤ) = 1 := by
        simp [cechSign, belowCard, Finset.filter_singleton]
      rw [hsign, one_smul]
    · rw [Q.d_isDeg_of_isBot hcbot s hs]
      change 0 = π.app s (g s)
      rw [hg s hs, map_zero]
  obtain ⟨t, ht, hdt⟩ := chase_lift_of_lift ι π 0 hπι hexact hinj hF hG
    (Q.d_d c) g hg hdc.symm
  have hdiff : Q.d (π.onCochain t - c) = 0 := by rw [Q.d_sub, hdt, hdc, sub_self]
  have hbot : Q.IsBot (π.onCochain t - c) := by
    intro s hs
    change π.app s (t s) - c s = 0
    rw [ht s (Finset.card_ne_zero.mpr hs), hcbot s hs, map_zero, sub_zero]
  have := congrFun (hQ _ hbot hdiff) ∅
  refine ⟨t ∅, ?_⟩
  rw [← hc0]
  exact sub_eq_zero.mp this

/-- **Sections over the covered set lift.**  If the quotient is separated over the cover and the
chase applies in degree `0`, every section of `Q` over the covered set lifts to `G`. -/
theorem surjective_bot_of_chase
    (hπι : ∀ s : Finset T, s.card = 1 → ∀ x, π.app s (ι.app s x) = 0)
    (hsurj : ∀ s : Finset T, s.card = 1 → Function.Surjective (π.app s))
    (hexact : ∀ s : Finset T, s.card = 2 → ∀ y, π.app s y = 0 → ∃ x, ι.app s x = y)
    (hinj : ∀ s : Finset T, s.card = 3 → Function.Injective (ι.app s))
    (hF : F.ExactAt 1) (hG : G.ExactAt 0) (hQ : Q.ExactBot) :
    Function.Surjective (π.app ∅) := by
  classical
  intro q
  let g : G.Cochain := fun s =>
    if hs : s.card = 1 then Classical.choose (hsurj s hs (Q.res (Finset.empty_subset s) q))
    else 0
  refine lift_bot_of_chase ι π hπι hexact hinj hF hG hQ q g (fun s hs => dif_neg hs)
    fun s hs => ?_
  simp only [g, dif_pos hs]
  exact Classical.choose_spec (hsurj s hs _)

end Chase

end FinsetCechDatum

end HTGeometry
