import GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationPullback

/-!
# Relational composition of envelope correlations and the path join law

Envelope correlations compose as relations.  This module proves that relational composition is
associative, that composing a correlation carrying an extra ambiguity submodule with one further
edge correlation again produces a correlation with an explicitly enlarged ambiguity, and that the
direct correlation of a composite is contained in the composite of the two edge correlations.

Iterating the composition law along a tower gives the path law: the correlation of a path visiting
a prescribed set of intermediate vertices is the correlation of the total transport map with
ambiguity equal to the join of the boundary submodules of all visited vertices, transported to the
terminal vertex.

Main results:

* `relationalComp_assoc`: associativity of relational composition;
* `relationalComp_ambiguousCorrelation`: the exact one-step composition law;
* `envelopeCorrelation_comp_le_relationalComp`: a direct correlation is contained in any
  two-step factorisation of it;
* `pathCorrelation_eq`: the path correlation is the total correlation with the accumulated
  intermediate ambiguity;
* `pathJoin_eq` and `pathCorrelation_zero_mem_iff`: the ambiguity of a path is the transported
  boundary join over all visited vertices;
* `envelopeCorrelation_le_pathCorrelation`: path refinement only enlarges the correlation.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]

section RelationalComposition

variable {X Y Z T : Type v}
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup Z] [Module 𝕜 Z]
variable [AddCommGroup T] [Module 𝕜 T]

/-- Relational composition of two subdirect submodules. -/
def relationalComp (R : Submodule 𝕜 (X × Y)) (S : Submodule 𝕜 (Y × Z)) :
    Submodule 𝕜 (X × Z) where
  carrier := {p | ∃ y : Y, (p.1, y) ∈ R ∧ (y, p.2) ∈ S}
  add_mem' := by
    rintro p q ⟨y, hy₁, hy₂⟩ ⟨z, hz₁, hz₂⟩
    exact ⟨y + z, R.add_mem hy₁ hz₁, S.add_mem hy₂ hz₂⟩
  zero_mem' := ⟨0, R.zero_mem, S.zero_mem⟩
  smul_mem' := by
    rintro c p ⟨y, hy₁, hy₂⟩
    exact ⟨c • y, R.smul_mem c hy₁, S.smul_mem c hy₂⟩

theorem mem_relationalComp_iff (R : Submodule 𝕜 (X × Y)) (S : Submodule 𝕜 (Y × Z))
    (p : X × Z) :
    p ∈ relationalComp R S ↔ ∃ y : Y, (p.1, y) ∈ R ∧ (y, p.2) ∈ S :=
  Iff.rfl

theorem relationalComp_mono {R R' : Submodule 𝕜 (X × Y)} {S S' : Submodule 𝕜 (Y × Z)}
    (hR : R ≤ R') (hS : S ≤ S') : relationalComp R S ≤ relationalComp R' S' := by
  rintro p ⟨y, hy₁, hy₂⟩
  exact ⟨y, hR hy₁, hS hy₂⟩

theorem relationalComp_assoc (R : Submodule 𝕜 (X × Y)) (S : Submodule 𝕜 (Y × Z))
    (U : Submodule 𝕜 (Z × T)) :
    relationalComp (relationalComp R S) U = relationalComp R (relationalComp S U) := by
  ext p
  constructor
  · rintro ⟨z, ⟨y, hy₁, hy₂⟩, hz⟩
    exact ⟨y, hy₁, ⟨z, hy₂, hz⟩⟩
  · rintro ⟨y, hy, ⟨z, hz₁, hz₂⟩⟩
    exact ⟨z, ⟨y, hy, hz₁⟩, hz₂⟩

end RelationalComposition

section AmbiguousCorrelation

variable {V W : Type v}
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- Envelope correlation carrying an extra target ambiguity submodule. -/
def ambiguousCorrelation (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt N : Submodule 𝕜 W) :
    Submodule 𝕜 ((V ⧸ Js) × (W ⧸ Jt)) where
  carrier :=
    {p | ∃ a : V, ∃ n ∈ N,
      ((Submodule.Quotient.mk a : V ⧸ Js), (Submodule.Quotient.mk (f a + n) : W ⧸ Jt)) = p}
  add_mem' := by
    rintro p q ⟨a, n, hn, rfl⟩ ⟨b, m, hm, rfl⟩
    refine ⟨a + b, n + m, N.add_mem hn hm, ?_⟩
    rw [Prod.mk_add_mk, ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add]
    have hval : f (a + b) + (n + m) = (f a + n) + (f b + m) := by
      rw [map_add]; abel
    rw [hval]
  zero_mem' := ⟨0, 0, N.zero_mem, by simp⟩
  smul_mem' := by
    rintro c p ⟨a, n, hn, rfl⟩
    refine ⟨c • a, c • n, N.smul_mem c hn, ?_⟩
    rw [Prod.smul_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
    have hval : f (c • a) + c • n = c • (f a + n) := by
      rw [map_smul, smul_add]
    rw [hval]

theorem mem_ambiguousCorrelation_iff (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V)
    (Jt N : Submodule 𝕜 W) (p : (V ⧸ Js) × (W ⧸ Jt)) :
    p ∈ ambiguousCorrelation f Js Jt N ↔
      ∃ a : V, ∃ n ∈ N,
        ((Submodule.Quotient.mk a : V ⧸ Js),
          (Submodule.Quotient.mk (f a + n) : W ⧸ Jt)) = p :=
  Iff.rfl

theorem ambiguousCorrelation_bot (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W) :
    ambiguousCorrelation f Js Jt ⊥ = envelopeCorrelation f Js Jt := by
  ext p
  constructor
  · rintro ⟨a, n, hn, rfl⟩
    rw [Submodule.mem_bot] at hn
    subst hn
    exact ⟨a, by rw [correlationMap_apply, add_zero]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, 0, Submodule.zero_mem _, by rw [add_zero, correlationMap_apply]⟩

theorem ambiguousCorrelation_mono (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)
    {N N' : Submodule 𝕜 W} (h : N ≤ N') :
    ambiguousCorrelation f Js Jt N ≤ ambiguousCorrelation f Js Jt N' := by
  rintro p ⟨a, n, hn, rfl⟩
  exact ⟨a, n, h hn, rfl⟩

theorem envelopeCorrelation_le_ambiguousCorrelation (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V)
    (Jt N : Submodule 𝕜 W) :
    envelopeCorrelation f Js Jt ≤ ambiguousCorrelation f Js Jt N := by
  rw [← ambiguousCorrelation_bot f Js Jt]
  exact ambiguousCorrelation_mono f Js Jt bot_le

/-- Ambiguity law: the fibre of an ambiguous correlation over the zero source class is the join of
the edge join with the extra ambiguity. -/
theorem mem_ambiguousCorrelation_zero_iff (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V)
    (Jt N : Submodule 𝕜 W) (y : W ⧸ Jt) :
    ((0 : V ⧸ Js), y) ∈ ambiguousCorrelation f Js Jt N ↔
      y ∈ Submodule.map Jt.mkQ (edgeJoin f Js Jt ⊔ N) := by
  constructor
  · rintro ⟨a, n, hn, hp⟩
    have h1 : (Submodule.Quotient.mk a : V ⧸ Js) = 0 := congrArg Prod.fst hp
    have h2 : (Submodule.Quotient.mk (f a + n) : W ⧸ Jt) = y := congrArg Prod.snd hp
    refine ⟨f a + n, ?_, h2⟩
    refine Submodule.add_mem _ ?_ ?_
    · exact (le_sup_left : edgeJoin f Js Jt ≤ edgeJoin f Js Jt ⊔ N)
        (transported_le_edgeJoin f Js Jt
          (Submodule.mem_map_of_mem ((Submodule.Quotient.mk_eq_zero Js).mp h1)))
    · exact (le_sup_right : N ≤ edgeJoin f Js Jt ⊔ N) hn
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨e, he, n, hn, hsum⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, ht, u, hu, hesum⟩ := Submodule.mem_sup.mp he
    obtain ⟨s, hs, hfs⟩ := Submodule.mem_map.mp hu
    refine ⟨s, n, hn, ?_⟩
    refine Prod.ext ?_ ?_
    · exact (Submodule.Quotient.mk_eq_zero Js).mpr hs
    · show (Submodule.Quotient.mk (f s + n) : W ⧸ Jt) = Jt.mkQ w
      have hval : w - (f s + n) = t := by
        rw [← hsum, ← hesum, hfs]; abel
      refine (Submodule.Quotient.eq Jt).mpr ?_
      have : f s + n - w = -t := by rw [← hval]; abel
      rw [this]
      exact Jt.neg_mem ht

/-- An ambiguous correlation collapses to the plain envelope correlation exactly when its extra
ambiguity is already contained in the edge join. -/
theorem ambiguousCorrelation_eq_envelopeCorrelation_iff (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V)
    (Jt N : Submodule 𝕜 W) :
    ambiguousCorrelation f Js Jt N = envelopeCorrelation f Js Jt ↔ N ≤ edgeJoin f Js Jt := by
  constructor
  · intro h n hn
    have hmem : ((0 : V ⧸ Js), (Submodule.Quotient.mk n : W ⧸ Jt)) ∈
        ambiguousCorrelation f Js Jt N := by
      refine ⟨0, n, hn, ?_⟩
      refine Prod.ext ?_ ?_
      · exact (Submodule.Quotient.mk_eq_zero Js).mpr Js.zero_mem
      · show (Submodule.Quotient.mk (f 0 + n) : W ⧸ Jt) = Submodule.Quotient.mk n
        rw [map_zero, zero_add]
    rw [h] at hmem
    obtain ⟨b, hb⟩ := hmem
    have hb₁ : (Submodule.Quotient.mk b : V ⧸ Js) = 0 := congrArg Prod.fst hb
    have hb₂ : (Submodule.Quotient.mk (f b) : W ⧸ Jt) = Submodule.Quotient.mk n :=
      congrArg Prod.snd hb
    have hbJ : b ∈ Js := (Submodule.Quotient.mk_eq_zero Js).mp hb₁
    have hdiff : f b - n ∈ Jt := (Submodule.Quotient.eq Jt).mp hb₂
    have hval : n = f b - (f b - n) := by abel
    rw [hval]
    exact Submodule.sub_mem _
      ((le_sup_right : Js.map f ≤ Jt ⊔ Js.map f) (Submodule.mem_map_of_mem hbJ))
      ((le_sup_left : Jt ≤ Jt ⊔ Js.map f) hdiff)
  · intro h
    apply le_antisymm
    · rintro p ⟨a, n, hn, rfl⟩
      obtain ⟨t, ht, w, hw, hsum⟩ := Submodule.mem_sup.mp (h hn)
      obtain ⟨s, hs, hfs⟩ := Submodule.mem_map.mp hw
      refine ⟨a + s, ?_⟩
      refine Prod.ext ?_ ?_
      · show (Submodule.Quotient.mk (a + s) : V ⧸ Js) = Submodule.Quotient.mk a
        exact (Submodule.Quotient.eq Js).mpr (by simpa using hs)
      · show (Submodule.Quotient.mk (f (a + s)) : W ⧸ Jt) = Submodule.Quotient.mk (f a + n)
        refine (Submodule.Quotient.eq Jt).mpr ?_
        have hval : f (a + s) - (f a + n) = -t := by
          rw [map_add, hfs, ← hsum]; abel
        rw [hval]
        exact Jt.neg_mem ht
    · exact envelopeCorrelation_le_ambiguousCorrelation f Js Jt N

variable {U : Type v} [AddCommGroup U] [Module 𝕜 U]

/-- One-step composition law for ambiguous correlations. -/
theorem relationalComp_ambiguousCorrelation (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (Ju : Submodule 𝕜 U) (Jv N : Submodule 𝕜 V) (Jw : Submodule 𝕜 W) :
    relationalComp (ambiguousCorrelation f Ju Jv N) (envelopeCorrelation g Jv Jw) =
      ambiguousCorrelation (g ∘ₗ f) Ju Jw (N.map g ⊔ Jv.map g) := by
  ext p
  constructor
  · rintro ⟨y, ⟨a, n, hn, hay⟩, ⟨b, hbz⟩⟩
    have h1 : (Submodule.Quotient.mk a : U ⧸ Ju) = p.1 := congrArg Prod.fst hay
    have h2 : (Submodule.Quotient.mk (f a + n) : V ⧸ Jv) = y := congrArg Prod.snd hay
    have h3 : (Submodule.Quotient.mk b : V ⧸ Jv) = y := congrArg Prod.fst hbz
    have h4 : (Submodule.Quotient.mk (g b) : W ⧸ Jw) = p.2 := congrArg Prod.snd hbz
    have hdiff : b - (f a + n) ∈ Jv := (Submodule.Quotient.eq Jv).mp (h3.trans h2.symm)
    refine ⟨a, g n + g (b - (f a + n)), ?_, ?_⟩
    · exact Submodule.add_mem _
        ((le_sup_left : N.map g ≤ N.map g ⊔ Jv.map g) (Submodule.mem_map_of_mem hn))
        ((le_sup_right : Jv.map g ≤ N.map g ⊔ Jv.map g) (Submodule.mem_map_of_mem hdiff))
    · have hval : (g ∘ₗ f) a + (g n + g (b - (f a + n))) = g b := by
        show g (f a) + (g n + g (b - (f a + n))) = g b
        rw [map_sub, map_add]
        abel
      exact Prod.ext h1 (by rw [hval]; exact h4)
  · rintro ⟨a, w, hw, rfl⟩
    obtain ⟨w₁, hw₁, w₂, hw₂, hsum⟩ := Submodule.mem_sup.mp hw
    obtain ⟨n, hn, hgn⟩ := Submodule.mem_map.mp hw₁
    obtain ⟨v, hv, hgv⟩ := Submodule.mem_map.mp hw₂
    refine ⟨(Submodule.Quotient.mk (f a + n) : V ⧸ Jv), ⟨a, n, hn, rfl⟩, ?_⟩
    refine ⟨f a + n + v, ?_⟩
    refine Prod.ext ?_ ?_
    · show (Submodule.Quotient.mk (f a + n + v) : V ⧸ Jv) = Submodule.Quotient.mk (f a + n)
      refine (Submodule.Quotient.eq Jv).mpr ?_
      simpa using hv
    · show (Submodule.Quotient.mk (g (f a + n + v)) : W ⧸ Jw) =
        Submodule.Quotient.mk ((g ∘ₗ f) a + w)
      congr 1
      rw [map_add, map_add, hgn, hgv, ← hsum]
      show g (f a) + w₁ + w₂ = g (f a) + (w₁ + w₂)
      abel

/-- A direct correlation is contained in every two-step factorisation of it. -/
theorem envelopeCorrelation_comp_le_relationalComp (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (Ju : Submodule 𝕜 U) (Jv : Submodule 𝕜 V) (Jw : Submodule 𝕜 W) :
    envelopeCorrelation (g ∘ₗ f) Ju Jw ≤
      relationalComp (envelopeCorrelation f Ju Jv) (envelopeCorrelation g Jv Jw) := by
  rintro p ⟨a, rfl⟩
  exact ⟨Submodule.Quotient.mk (f a), ⟨a, rfl⟩, ⟨f a, rfl⟩⟩

/-- The exact composition excess: composing two edge correlations enlarges the ambiguity by the
transported middle boundary. -/
theorem relationalComp_envelopeCorrelation (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (Ju : Submodule 𝕜 U) (Jv : Submodule 𝕜 V) (Jw : Submodule 𝕜 W) :
    relationalComp (envelopeCorrelation f Ju Jv) (envelopeCorrelation g Jv Jw) =
      ambiguousCorrelation (g ∘ₗ f) Ju Jw (Jv.map g) := by
  rw [← ambiguousCorrelation_bot f Ju Jv, relationalComp_ambiguousCorrelation,
    Submodule.map_bot, bot_sup_eq]

/-- A two-step factorisation is exact exactly when the transported middle boundary is already
contained in the edge join of the composite; otherwise the composition is strictly larger. -/
theorem relationalComp_eq_envelopeCorrelation_iff (f : U →ₗ[𝕜] V) (g : V →ₗ[𝕜] W)
    (Ju : Submodule 𝕜 U) (Jv : Submodule 𝕜 V) (Jw : Submodule 𝕜 W) :
    relationalComp (envelopeCorrelation f Ju Jv) (envelopeCorrelation g Jv Jw) =
        envelopeCorrelation (g ∘ₗ f) Ju Jw ↔
      Jv.map g ≤ edgeJoin (g ∘ₗ f) Ju Jw := by
  rw [relationalComp_envelopeCorrelation, ambiguousCorrelation_eq_envelopeCorrelation_iff]

end AmbiguousCorrelation

section Tower

variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-- Composite bond from vertex `m + k` down to vertex `m`. -/
def towerMap (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) : (m k : ℕ) → (A (m + k) →ₗ[𝕜] A m)
  | _, 0 => LinearMap.id
  | m, (k + 1) => towerMap bond m k ∘ₗ bond (m + k)

@[simp] theorem towerMap_zero (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (m : ℕ) :
    towerMap A bond m 0 = LinearMap.id :=
  rfl

@[simp] theorem towerMap_succ (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (m k : ℕ) :
    towerMap A bond m (k + 1) = towerMap A bond m k ∘ₗ bond (m + k) :=
  rfl

/-- Source vertex of a path leaving the terminal vertex `m` with the prescribed gaps. -/
def pathSource : ℕ → List ℕ → ℕ
  | m, [] => m
  | m, (d :: rest) => pathSource (m + d) rest

@[simp] theorem pathSource_nil (m : ℕ) : pathSource m [] = m := rfl

@[simp] theorem pathSource_cons (m d : ℕ) (rest : List ℕ) :
    pathSource m (d :: rest) = pathSource (m + d) rest := rfl

/-- Total transport map of a path, from its source vertex to its terminal vertex. -/
def pathTotalMap (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) :
    (m : ℕ) → (gaps : List ℕ) → (A (pathSource m gaps) →ₗ[𝕜] A m)
  | _, [] => LinearMap.id
  | m, (d :: rest) => towerMap A bond m d ∘ₗ pathTotalMap bond (m + d) rest

@[simp] theorem pathTotalMap_nil (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (m : ℕ) :
    pathTotalMap A bond m [] = LinearMap.id :=
  rfl

@[simp] theorem pathTotalMap_cons (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (m d : ℕ)
    (rest : List ℕ) :
    pathTotalMap A bond m (d :: rest) =
      towerMap A bond m d ∘ₗ pathTotalMap A bond (m + d) rest :=
  rfl

/-- Ambiguity accumulated at the terminal vertex by the strictly intermediate vertices. -/
def pathAmbiguity (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (J : ∀ n, Submodule 𝕜 (A n)) :
    (m : ℕ) → List ℕ → Submodule 𝕜 (A m)
  | _, [] => ⊥
  | m, (d :: rest) =>
      Submodule.map (towerMap A bond m d) (pathAmbiguity bond J (m + d) rest ⊔ J (m + d))

@[simp] theorem pathAmbiguity_nil (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m : ℕ) :
    pathAmbiguity A bond J m [] = ⊥ :=
  rfl

@[simp] theorem pathAmbiguity_cons (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m d : ℕ) (rest : List ℕ) :
    pathAmbiguity A bond J m (d :: rest) =
      Submodule.map (towerMap A bond m d)
        (pathAmbiguity A bond J (m + d) rest ⊔ J (m + d)) :=
  rfl

/-- Transported boundary join over all vertices visited by a path. -/
def pathJoin (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (J : ∀ n, Submodule 𝕜 (A n)) :
    (m : ℕ) → List ℕ → Submodule 𝕜 (A m)
  | m, [] => J m
  | m, (d :: rest) =>
      J m ⊔ Submodule.map (towerMap A bond m d) (pathJoin bond J (m + d) rest)

@[simp] theorem pathJoin_nil (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m : ℕ) :
    pathJoin A bond J m [] = J m :=
  rfl

@[simp] theorem pathJoin_cons (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m d : ℕ) (rest : List ℕ) :
    pathJoin A bond J m (d :: rest) =
      J m ⊔ Submodule.map (towerMap A bond m d) (pathJoin A bond J (m + d) rest) :=
  rfl

/-- Correlation of a path, composed edge by edge through the visited vertices. -/
def pathCorrelation (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (J : ∀ n, Submodule 𝕜 (A n)) :
    (m : ℕ) → (gaps : List ℕ) →
      Submodule 𝕜 ((A (pathSource m gaps) ⧸ J (pathSource m gaps)) × (A m ⧸ J m))
  | m, [] => envelopeCorrelation LinearMap.id (J m) (J m)
  | m, (d :: rest) =>
      relationalComp (pathCorrelation bond J (m + d) rest)
        (envelopeCorrelation (towerMap A bond m d) (J (m + d)) (J m))

@[simp] theorem pathCorrelation_nil (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m : ℕ) :
    pathCorrelation A bond J m [] = envelopeCorrelation LinearMap.id (J m) (J m) :=
  rfl

@[simp] theorem pathCorrelation_cons (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m d : ℕ) (rest : List ℕ) :
    pathCorrelation A bond J m (d :: rest) =
      relationalComp (pathCorrelation A bond J (m + d) rest)
        (envelopeCorrelation (towerMap A bond m d) (J (m + d)) (J m)) :=
  rfl

/-- Path composition law: composing the edge correlations of a path gives the correlation of the
total transport map with the accumulated intermediate ambiguity. -/
theorem pathCorrelation_eq (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (J : ∀ n, Submodule 𝕜 (A n)) :
    ∀ (gaps : List ℕ) (m : ℕ),
      pathCorrelation A bond J m gaps =
        ambiguousCorrelation (pathTotalMap A bond m gaps) (J (pathSource m gaps)) (J m)
          (pathAmbiguity A bond J m gaps) := by
  intro gaps
  induction gaps with
  | nil =>
    intro m
    show envelopeCorrelation LinearMap.id (J m) (J m) =
      ambiguousCorrelation (LinearMap.id : A m →ₗ[𝕜] A m) (J m) (J m) ⊥
    rw [ambiguousCorrelation_bot]
  | cons d rest ih =>
    intro m
    show relationalComp (pathCorrelation A bond J (m + d) rest)
        (envelopeCorrelation (towerMap A bond m d) (J (m + d)) (J m)) =
      ambiguousCorrelation (towerMap A bond m d ∘ₗ pathTotalMap A bond (m + d) rest)
        (J (pathSource (m + d) rest)) (J m)
        (Submodule.map (towerMap A bond m d)
          (pathAmbiguity A bond J (m + d) rest ⊔ J (m + d)))
    rw [ih (m + d), relationalComp_ambiguousCorrelation, Submodule.map_sup]

/-- The accumulated ambiguity together with the transported source boundary is the boundary join
over all visited vertices. -/
theorem pathJoin_eq (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n) (J : ∀ n, Submodule 𝕜 (A n)) :
    ∀ (gaps : List ℕ) (m : ℕ),
      J m ⊔ Submodule.map (pathTotalMap A bond m gaps) (J (pathSource m gaps))
          ⊔ pathAmbiguity A bond J m gaps =
        pathJoin A bond J m gaps := by
  intro gaps
  induction gaps with
  | nil =>
    intro m
    show J m ⊔ Submodule.map (LinearMap.id : A m →ₗ[𝕜] A m) (J m) ⊔ ⊥ = J m
    rw [Submodule.map_id, sup_idem, sup_bot_eq]
  | cons d rest ih =>
    intro m
    show J m ⊔ Submodule.map (towerMap A bond m d ∘ₗ pathTotalMap A bond (m + d) rest)
          (J (pathSource (m + d) rest))
        ⊔ Submodule.map (towerMap A bond m d)
          (pathAmbiguity A bond J (m + d) rest ⊔ J (m + d)) =
      J m ⊔ Submodule.map (towerMap A bond m d) (pathJoin A bond J (m + d) rest)
    rw [← ih (m + d)]
    simp only [Submodule.map_comp, Submodule.map_sup]
    ac_rfl

/-- Path ambiguity law: the fibre of a path correlation over the zero source class is the
transported boundary join over all visited vertices. -/
theorem pathCorrelation_zero_mem_iff (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m : ℕ) (gaps : List ℕ) (y : A m ⧸ J m) :
    ((0 : A (pathSource m gaps) ⧸ J (pathSource m gaps)), y) ∈
        pathCorrelation A bond J m gaps ↔
      y ∈ Submodule.map (J m).mkQ (pathJoin A bond J m gaps) := by
  rw [pathCorrelation_eq, mem_ambiguousCorrelation_zero_iff, edgeJoin,
    ← pathJoin_eq A bond J gaps m]

/-- Path refinement only enlarges a correlation: the direct correlation of the total transport map
is contained in the composed path correlation. -/
theorem envelopeCorrelation_le_pathCorrelation (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (m : ℕ) (gaps : List ℕ) :
    envelopeCorrelation (pathTotalMap A bond m gaps) (J (pathSource m gaps)) (J m) ≤
      pathCorrelation A bond J m gaps := by
  rw [pathCorrelation_eq]
  exact envelopeCorrelation_le_ambiguousCorrelation _ _ _ _

end Tower

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
