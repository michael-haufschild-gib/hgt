import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Cartan–Dieudonné theorem

Let `K` be a field of characteristic `≠ 2`, let `V` be a finite-dimensional `K`-vector space and
let `B` be a nondegenerate symmetric bilinear form on `V`.  For an anisotropic vector `v`
(`B v v ≠ 0`) the *reflection* in the hyperplane `v^⊥` is

`reflect B v x = x - (2 * B x v / B v v) • v`.

The Cartan–Dieudonné theorem states that **every isometry of `(V, B)` is a composite of at most
`finrank K V` reflections**.  This file gives a complete, unconditional Lean proof.

## The argument

Write `disp f = f - 1` for the displacement of an endomorphism, `cdGam B f x = B (disp f x) x`
and `cdSig B f x y = - B (disp f x) (disp f y)`.  For an isometry `f` the polarization identity

`B (disp f x) y + B (disp f y) x = cdSig B f x y`                                (`cd_polar`)

holds, and `cdSig` is the polar form of the quadratic form `cdGam`.  In particular `cdGam B f x`
is `-1/2` times `B (disp f x) (disp f x)`, so "`range (disp f)` is totally isotropic" is exactly
"`cdGam B f` vanishes identically".

* `cd_crux` is the sharp descent step (Scherk's lemma).  If for every `v` with `cdGam B f v ≠ 0`
  the form `cdGam B f` vanishes on the hyperplane `{x | B (disp f x) v = 0}`, then
  `range (disp f)` is the single line `K ∙ disp f v₀`.  The proof is purely linear-algebraic: the
  `cdSig`-radical is shown to lie inside `ker (disp f)`, and then the hyperplane is shown to be
  contained in `ker (disp f)` as well.
* `cd_scherk` is Scherk's theorem: if `range (f - 1)` is *not* totally isotropic then `f` is a
  composite of at most `finrank K (range (f - 1))` reflections.  This is an induction on that
  rank; the descent multiplies `f` by the reflection in `disp f v`, which fixes `v` and drops the
  rank by exactly one, and `cd_crux` guarantees that the non-isotropy hypothesis survives the
  descent (or that the induction has already terminated).
* `cartan_dieudonne` handles the remaining, totally isotropic case.  There `range (f - 1)` is
  contained in `ker (f - 1)`, so its rank `r` satisfies `2 * r ≤ finrank K V`; moreover `r ≠ 1`,
  because a rank-one totally isotropic displacement forces `f = 1`.  Multiplying by one reflection
  in an anisotropic vector `w` produces an isometry with non-isotropic displacement range of rank
  at most `r + 1`, so `f` is a composite of at most `r + 2 ≤ finrank K V` reflections.

Note that no step of the argument passes to a subspace, so no nondegeneracy of restricted forms is
ever needed.

## Main results

* `reflect`, `reflect_isom`, `reflect_reflect` — reflections and their basic properties;
* `reflProd`, `IsReflProd` — composites of (at most `n`) reflections;
* `cd_crux` — the Scherk descent lemma;
* `cd_scherk` — Scherk's theorem;
* `cartan_dieudonne` — the Cartan–Dieudonné theorem;
* `cartan_dieudonne_list`, `isometry_iff_exists_reflProd`,
  `cartan_dieudonne_of_bilinForm` — restatements of the theorem.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.CartanDieudonne

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### Reflections -/

/-- The reflection of `V` in the hyperplane orthogonal to `v`. -/
noncomputable def reflect (B : V →ₗ[K] V →ₗ[K] K) (v : V) : V →ₗ[K] V :=
  LinearMap.id - (B.flip v).smulRight ((2 / B v v) • v)

lemma reflect_apply (B : V →ₗ[K] V →ₗ[K] K) (v x : V) :
    reflect B v x = x - (2 * B x v / B v v) • v := by
  simp only [reflect, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.flip_apply, smul_smul]
  have h : B x v * (2 / B v v) = 2 * B x v / B v v := by ring
  rw [h]

lemma reflect_isom (B : V →ₗ[K] V →ₗ[K] K) (hs : ∀ x y : V, B x y = B y x)
    {v : V} (hv : B v v ≠ 0) (x y : V) :
    B (reflect B v x) (reflect B v y) = B x y := by
  simp only [reflect_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hs v y, hs v v]
  field_simp
  ring

lemma reflect_reflect (B : V →ₗ[K] V →ₗ[K] K) {v : V} (hv : B v v ≠ 0) (x : V) :
    reflect B v (reflect B v x) = x := by
  simp only [reflect_apply, map_sub, map_smul]
  have h2 : (2 : K) * B v v / B v v = 2 := by field_simp
  rw [h2]
  module

/-- The composite of the reflections indexed by a list of vectors. -/
noncomputable def reflProd (B : V →ₗ[K] V →ₗ[K] K) : List V → (V →ₗ[K] V)
  | [] => LinearMap.id
  | v :: l => (reflect B v).comp (reflProd B l)

/-- `IsReflProd B n f` says that `f` is a composite of at most `n` reflections. -/
inductive IsReflProd (B : V →ₗ[K] V →ₗ[K] K) : ℕ → (V →ₗ[K] V) → Prop
  | id (n : ℕ) : IsReflProd B n LinearMap.id
  | cons {n : ℕ} {v : V} (hv : B v v ≠ 0) {g : V →ₗ[K] V} (hg : IsReflProd B n g) :
      IsReflProd B (n + 1) ((reflect B v).comp g)

lemma IsReflProd.mono {B : V →ₗ[K] V →ₗ[K] K} {n : ℕ} {f : V →ₗ[K] V}
    (h : IsReflProd B n f) : ∀ m : ℕ, n ≤ m → IsReflProd B m f := by
  induction h with
  | id n => intro m _; exact IsReflProd.id m
  | @cons n v hv g _ ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact IsReflProd.cons hv (ih m' (by omega))

lemma IsReflProd.exists_list {B : V →ₗ[K] V →ₗ[K] K} {n : ℕ} {f : V →ₗ[K] V}
    (h : IsReflProd B n f) :
    ∃ l : List V, l.length ≤ n ∧ (∀ v ∈ l, B v v ≠ 0) ∧ f = reflProd B l := by
  induction h with
  | id n => exact ⟨[], by simp, by simp, rfl⟩
  | @cons n v hv g _ ih =>
      obtain ⟨l, hl, hmem, rfl⟩ := ih
      refine ⟨v :: l, by simpa using hl, ?_, rfl⟩
      intro w hw
      rcases List.mem_cons.mp hw with h | h
      · exact h ▸ hv
      · exact hmem w h

/-! ### The displacement of an endomorphism -/

/-- The displacement `f - 1` of an endomorphism `f`. -/
def disp (f : V →ₗ[K] V) : V →ₗ[K] V := f - LinearMap.id

lemma disp_apply (f : V →ₗ[K] V) (x : V) : disp f x = f x - x := by
  simp [disp]

/-- `cdGam B f x = B (f x - x) x`. -/
def cdGam (B : V →ₗ[K] V →ₗ[K] K) (f : V →ₗ[K] V) (x : V) : K := B (disp f x) x

/-- `cdSig B f x y = - B (f x - x) (f y - y)`, the polarization of `cdGam`. -/
def cdSig (B : V →ₗ[K] V →ₗ[K] K) (f : V →ₗ[K] V) (x y : V) : K :=
  - B (disp f x) (disp f y)

variable {B : V →ₗ[K] V →ₗ[K] K} {f : V →ₗ[K] V}

lemma cdGam_eq (B : V →ₗ[K] V →ₗ[K] K) (f : V →ₗ[K] V) (x : V) :
    cdGam B f x = B (disp f x) x := rfl

lemma cdSig_symm (hs : ∀ x y : V, B x y = B y x) (x y : V) :
    cdSig B f x y = cdSig B f y x := by
  simp only [cdSig, hs (disp f x) (disp f y)]

lemma cdSig_add_right (x y z : V) :
    cdSig B f x (y + z) = cdSig B f x y + cdSig B f x z := by
  simp only [cdSig, map_add]; ring

lemma cdSig_smul_right (c : K) (x y : V) :
    cdSig B f x (c • y) = c * cdSig B f x y := by
  simp only [cdSig, map_smul, smul_eq_mul]; ring

lemma cdSig_sub_left (x y z : V) :
    cdSig B f (x - y) z = cdSig B f x z - cdSig B f y z := by
  simp only [cdSig, map_sub, LinearMap.sub_apply]; ring

lemma cdSig_smul_left (c : K) (x y : V) :
    cdSig B f (c • x) y = c * cdSig B f x y := by
  simp only [cdSig, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

lemma cdSig_neg_right (x y : V) : cdSig B f x (-y) = - cdSig B f x y := by
  simp only [cdSig, map_neg]

lemma cd_polar (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y) (x y : V) :
    B (disp f x) y + B (disp f y) x = cdSig B f x y := by
  simp only [cdSig, disp_apply, map_sub, LinearMap.sub_apply]
  linear_combination hf x y + hs (f y) x - hs y x

lemma cdSig_self (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y) (x : V) :
    cdSig B f x x = 2 * cdGam B f x := by
  have h := cd_polar hs hf x x
  simp only [cdGam]
  linear_combination -h

lemma cd_disp_sq (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y) (x : V) :
    B (disp f x) (disp f x) = -(2 * cdGam B f x) := by
  have h := cdSig_self hs hf x
  simp only [cdSig] at h
  linear_combination -h

lemma cdGam_add (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y) (x y : V) :
    cdGam B f (x + y) = cdGam B f x + cdGam B f y + cdSig B f x y := by
  have h := cd_polar hs hf x y
  simp only [cdGam, map_add, LinearMap.add_apply] at *
  linear_combination h

lemma cdGam_smul (c : K) (x : V) : cdGam B f (c • x) = c ^ (2 : ℕ) * cdGam B f x := by
  simp only [cdGam, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

lemma cdGam_neg (x : V) : cdGam B f (-x) = cdGam B f x := by
  simp only [cdGam, map_neg, LinearMap.neg_apply]; ring

lemma cdGam_sub (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y) (x y : V) :
    cdGam B f (x - y) = cdGam B f x + cdGam B f y - cdSig B f x y := by
  have h : x - y = x + (-y) := by abel
  rw [h, cdGam_add hs hf, cdGam_neg, cdSig_neg_right]
  ring


/-! ### The Scherk descent lemma -/

/-- If the `cdSig`-radical vector `z` is not orthogonal to some anisotropic `v`, the whole
form `cdGam` vanishes. -/
lemma cd_orth_of_rad (hs : ∀ x y : V, B x y = B y x) (h2 : (2 : K) ≠ 0)
    (hf : ∀ x y, B (f x) (f y) = B x y)
    (H : ∀ v : V, cdGam B f v ≠ 0 → ∀ x : V, B (disp f x) v = 0 → cdGam B f x = 0)
    {z : V} (hz : ∀ y : V, cdSig B f z y = 0) {v : V} (hv : cdGam B f v ≠ 0) :
    B (disp f z) v = 0 := by
  by_contra hne
  have hgz : cdGam B f z = 0 := by
    have h := cdSig_self hs hf z
    rw [hz z] at h
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' h2
    · exact h'
  have key : ∀ x : V, cdGam B f x = 0 := by
    intro x
    have hmem : B (disp f (x - (B (disp f x) v / B (disp f z) v) • z)) v = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hg : cdGam B f (x - (B (disp f x) v / B (disp f z) v) • z) = 0 := H v hv _ hmem
    have hsig : cdSig B f (x - (B (disp f x) v / B (disp f z) v) • z) z = 0 := by
      rw [cdSig_symm hs]; exact hz _
    have hsum : (x - (B (disp f x) v / B (disp f z) v) • z)
        + (B (disp f x) v / B (disp f z) v) • z = x := by abel
    have hx : cdGam B f x
        = cdGam B f ((x - (B (disp f x) v / B (disp f z) v) • z)
            + (B (disp f x) v / B (disp f z) v) • z) := by rw [hsum]
    rw [hx, cdGam_add hs hf, hg, cdGam_smul, hgz, cdSig_smul_right, hsig]
    ring
  exact hv (key v)

/-- A vector in the `cdSig`-radical has zero displacement. -/
lemma cd_disp_zero_of_rad (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0)
    (hf : ∀ x y, B (f x) (f y) = B x y)
    (H : ∀ v : V, cdGam B f v ≠ 0 → ∀ x : V, B (disp f x) v = 0 → cdGam B f x = 0)
    {v₀ : V} (hv₀ : cdGam B f v₀ ≠ 0)
    {z : V} (hz : ∀ y : V, cdSig B f z y = 0) :
    disp f z = 0 := by
  refine hnd _ ?_
  intro x
  by_cases hx : cdGam B f x = 0
  · by_cases hx1 : cdGam B f (x + v₀) = 0
    · have hx2 : cdGam B f (x - v₀) ≠ 0 := by
        intro hc
        apply hv₀
        have e1 := cdGam_add hs hf x v₀
        have e2 := cdGam_sub hs hf x v₀
        rw [hx1] at e1
        rw [hc] at e2
        rw [hx] at e1 e2
        have h4 : (2 : K) * cdGam B f v₀ = 0 := by linear_combination -e1 - e2
        rcases mul_eq_zero.mp h4 with h' | h'
        · exact absurd h' h2
        · exact h'
      have h1 := cd_orth_of_rad hs h2 hf H hz hx2
      have h3 := cd_orth_of_rad hs h2 hf H hz hv₀
      have hsplit : B (disp f z) x = B (disp f z) (x - v₀) + B (disp f z) v₀ := by
        rw [map_sub]; ring
      rw [hsplit, h1, h3]; ring
    · have h1 := cd_orth_of_rad hs h2 hf H hz hx1
      have h3 := cd_orth_of_rad hs h2 hf H hz hv₀
      have hsplit : B (disp f z) x = B (disp f z) (x + v₀) - B (disp f z) v₀ := by
        rw [map_add]; ring
      rw [hsplit, h1, h3]; ring
  · exact cd_orth_of_rad hs h2 hf H hz hx

/-- Two vectors orthogonal to `v₀` in the displacement pairing are `cdSig`-orthogonal. -/
lemma cd_sig_of_ker (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y)
    (H : ∀ v : V, cdGam B f v ≠ 0 → ∀ x : V, B (disp f x) v = 0 → cdGam B f x = 0)
    {v₀ : V} (hv₀ : cdGam B f v₀ ≠ 0) {a b : V}
    (ha : B (disp f a) v₀ = 0) (hb : B (disp f b) v₀ = 0) : cdSig B f a b = 0 := by
  have hab : B (disp f (a + b)) v₀ = 0 := by
    simp only [map_add, LinearMap.add_apply, ha, hb]
    ring
  have h1 : cdGam B f a = 0 := H v₀ hv₀ a ha
  have h2' : cdGam B f b = 0 := H v₀ hv₀ b hb
  have h3 : cdGam B f (a + b) = 0 := H v₀ hv₀ _ hab
  have h4 := cdGam_add hs hf a b
  rw [h1, h2', h3] at h4
  linear_combination -h4

/-- Step 3′ of the Scherk descent. -/
lemma cd_disp_zero_of_ker (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0)
    (hf : ∀ x y, B (f x) (f y) = B x y)
    (H : ∀ v : V, cdGam B f v ≠ 0 → ∀ x : V, B (disp f x) v = 0 → cdGam B f x = 0)
    {v₀ : V} (hv₀ : cdGam B f v₀ ≠ 0) {a : V}
    (ha : B (disp f a) v₀ = 0) (hsa : cdSig B f a v₀ = 0) : disp f a = 0 := by
  refine cd_disp_zero_of_rad hs hnd h2 hf H hv₀ ?_
  intro y
  have hc : B (disp f (y - (B (disp f y) v₀ / cdGam B f v₀) • v₀)) v₀ = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← cdGam_eq B f v₀]
    field_simp
    ring
  have key : cdSig B f a y
      = cdSig B f a (y - (B (disp f y) v₀ / cdGam B f v₀) • v₀)
        + (B (disp f y) v₀ / cdGam B f v₀) * cdSig B f a v₀ := by
    rw [← cdSig_smul_right, ← cdSig_add_right]
    congr 1
    abel
  rw [key, hsa, cd_sig_of_ker hs hf H hv₀ ha hc]
  ring

/-- **Scherk descent.**  If no anisotropic direction survives orthogonally, the displacement
range is a single line. -/
lemma cd_crux (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0)
    (hf : ∀ x y, B (f x) (f y) = B x y)
    (H : ∀ v : V, cdGam B f v ≠ 0 → ∀ x : V, B (disp f x) v = 0 → cdGam B f x = 0)
    {v₀ : V} (hv₀ : cdGam B f v₀ ≠ 0) :
    ∀ x : V, ∃ c : K, disp f x = c • disp f v₀ := by
  have main : ∀ a : V, B (disp f a) v₀ = 0 → disp f a = 0 := by
    intro a ha
    by_cases hsa : cdSig B f a v₀ = 0
    · exact cd_disp_zero_of_ker hs hnd h2 hf H hv₀ ha hsa
    · exfalso
      have hz : ∀ y : V, B (disp f a) y = 0 := by
        intro y
        set c : K := B (disp f y) v₀ / cdGam B f v₀ with hcdef
        have hw : B (disp f (y - c • v₀)) v₀ = 0 := by
          simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [← cdGam_eq B f v₀, hcdef]
          field_simp
          ring
        set d : K := cdSig B f (y - c • v₀) v₀ / cdSig B f a v₀ with hddef
        have hw' : B (disp f ((y - c • v₀) - d • a)) v₀ = 0 := by
          have hsp : disp f ((y - c • v₀) - d • a) = disp f (y - c • v₀) - d • disp f a := by
            rw [map_sub, map_smul]
          rw [hsp, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
            hw, ha]
          ring
        have hs' : cdSig B f ((y - c • v₀) - d • a) v₀ = 0 := by
          rw [cdSig_sub_left, cdSig_smul_left, hddef]
          field_simp
          ring
        have hd0 : disp f ((y - c • v₀) - d • a) = 0 :=
          cd_disp_zero_of_ker hs hnd h2 hf H hv₀ hw' hs'
        have e1 : B (disp f a) ((y - c • v₀) - d • a) = 0 := by
          have hp := cd_polar hs hf a ((y - c • v₀) - d • a)
          rw [hd0] at hp
          simp only [map_zero, LinearMap.zero_apply, add_zero] at hp
          rw [hp]
          exact cd_sig_of_ker hs hf H hv₀ ha hw'
        have e2 : B (disp f a) a = 0 := H v₀ hv₀ a ha
        have hsplit : y = ((y - c • v₀) - d • a) + d • a + c • v₀ := by abel
        calc B (disp f a) y
            = B (disp f a) (((y - c • v₀) - d • a) + d • a + c • v₀) := by rw [← hsplit]
          _ = 0 := by
              simp only [map_add, map_smul, smul_eq_mul, e1, e2, ha]
              ring
      exact hsa (by simp only [cdSig, hnd _ hz, map_zero, LinearMap.zero_apply, neg_zero])
  intro x
  refine ⟨B (disp f x) v₀ / cdGam B f v₀, ?_⟩
  have hw : B (disp f (x - (B (disp f x) v₀ / cdGam B f v₀) • v₀)) v₀ = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← cdGam_eq B f v₀]
    field_simp
    ring
  have h0 := main _ hw
  rw [map_sub, map_smul] at h0
  exact sub_eq_zero.mp h0


/-! ### Scherk's theorem and Cartan–Dieudonné -/

/-- The displacement of `reflect B (disp f v) ∘ f`. -/
lemma cd_disp_reflect (hs : ∀ x y : V, B x y = B y x) (hf : ∀ x y, B (f x) (f y) = B x y)
    (h2 : (2 : K) ≠ 0) {v : V} (hv : cdGam B f v ≠ 0) (y : V) :
    disp ((reflect B (disp f v)).comp f) y
      = disp f y - (B (disp f y) v / cdGam B f v) • disp f v := by
  have huu : B (disp f v) (disp f v) = -(2 * cdGam B f v) := cd_disp_sq hs hf v
  have hfy : B (f y) (disp f v) = - B (disp f y) v := by
    simp only [disp_apply, map_sub, LinearMap.sub_apply]
    linear_combination hf y v
  have hlhs : disp ((reflect B (disp f v)).comp f) y
      = f y - (2 * B (f y) (disp f v) / B (disp f v) (disp f v)) • disp f v - y := by
    rw [disp_apply ((reflect B (disp f v)).comp f) y, LinearMap.comp_apply, reflect_apply]
  have hcoef : 2 * (- B (disp f y) v) / (-(2 * cdGam B f v))
      = B (disp f y) v / cdGam B f v := by
    field_simp
  rw [hlhs, hfy, huu, hcoef, disp_apply f y]
  module

/-- **Scherk's theorem.**  An isometry whose displacement range is not totally isotropic is a
product of at most `finrank (range (f - 1))` reflections. -/
theorem cd_scherk [FiniteDimensional K V] (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0) :
    ∀ (r : ℕ) (g : V →ₗ[K] V), (∀ x y, B (g x) (g y) = B x y) →
      finrank K (LinearMap.range (disp g)) ≤ r →
      (∃ v : V, cdGam B g v ≠ 0) → IsReflProd B r g := by
  intro r
  induction r with
  | zero =>
      rintro g _ hrank ⟨v, hv⟩
      exfalso
      have hbot : LinearMap.range (disp g) = ⊥ :=
        Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
      have hz : disp g v = 0 := by
        have hmem : disp g v ∈ LinearMap.range (disp g) := ⟨v, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      exact hv (by simp only [cdGam, hz, map_zero, LinearMap.zero_apply])
  | succ r ih =>
      rintro g hg hrank ⟨v₀, hv₀⟩
      by_cases hcase : ∃ v : V, cdGam B g v ≠ 0 ∧ ∃ x : V, B (disp g x) v = 0 ∧ cdGam B g x ≠ 0
      · obtain ⟨v, hv, x, hx1, hx2⟩ := hcase
        have hu : B (disp g v) (disp g v) ≠ 0 := by
          rw [cd_disp_sq hs hg v]
          exact neg_ne_zero.mpr (mul_ne_zero h2 hv)
        have hg'isom : ∀ a b : V,
            B (((reflect B (disp g v)).comp g) a) (((reflect B (disp g v)).comp g) b) = B a b := by
          intro a b
          simp only [LinearMap.comp_apply]
          rw [reflect_isom B hs hu]
          exact hg a b
        have hdg' := cd_disp_reflect hs hg h2 hv
        have hx' : cdGam B ((reflect B (disp g v)).comp g) x ≠ 0 := by
          have hxx : disp ((reflect B (disp g v)).comp g) x = disp g x := by
            rw [hdg' x, hx1]
            simp
          simpa only [cdGam, hxx] using hx2
        have hker : ∀ y : V, B (disp g (y - (B (disp g y) v / cdGam B g v) • v)) v = 0 := by
          intro y
          simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [← cdGam_eq B g v]
          field_simp
          ring
        have hle : LinearMap.range (disp ((reflect B (disp g v)).comp g))
            ≤ Submodule.map (disp g) (LinearMap.ker ((B.flip v).comp (disp g))) := by
          rintro _ ⟨y, rfl⟩
          refine Submodule.mem_map.mpr ⟨y - (B (disp g y) v / cdGam B g v) • v, ?_, ?_⟩
          · simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.flip_apply]
            exact hker y
          · rw [map_sub, map_smul, ← hdg' y]
        have hWle : Submodule.map (disp g) (LinearMap.ker ((B.flip v).comp (disp g)))
            ≤ LinearMap.range (disp g) := by
          rintro _ hmem
          obtain ⟨z, _, rfl⟩ := Submodule.mem_map.mp hmem
          exact ⟨z, rfl⟩
        have hWne : Submodule.map (disp g) (LinearMap.ker ((B.flip v).comp (disp g)))
            ≠ LinearMap.range (disp g) := by
          intro hEq
          have hmem : disp g v ∈ Submodule.map (disp g) (LinearMap.ker ((B.flip v).comp (disp g))) := by
            rw [hEq]; exact ⟨v, rfl⟩
          obtain ⟨z, hz, hzz⟩ := Submodule.mem_map.mp hmem
          simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.flip_apply] at hz
          rw [hzz] at hz
          exact hv (by rw [cdGam_eq]; exact hz)
        have hrank' : finrank K (LinearMap.range (disp ((reflect B (disp g v)).comp g))) ≤ r := by
          have hh1 := Submodule.finrank_mono hle
          have hh2 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWle hWne)
          omega
        have hrec := ih _ hg'isom hrank' ⟨x, hx'⟩
        have hfinal : (reflect B (disp g v)).comp ((reflect B (disp g v)).comp g) = g := by
          ext y
          simp only [LinearMap.comp_apply]
          exact reflect_reflect B hu (g y)
        rw [← hfinal]
        exact IsReflProd.cons hu hrec
      · push Not at hcase
        have hu : B (disp g v₀) (disp g v₀) ≠ 0 := by
          rw [cd_disp_sq hs hg v₀]
          exact neg_ne_zero.mpr (mul_ne_zero h2 hv₀)
        have hcrux := cd_crux hs hnd h2 hg hcase hv₀
        have hdg' := cd_disp_reflect hs hg h2 hv₀
        have hzero : ∀ y : V, disp ((reflect B (disp g v₀)).comp g) y = 0 := by
          intro y
          obtain ⟨c, hc⟩ := hcrux y
          rw [hdg' y, hc]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          rw [← cdGam_eq B g v₀, mul_div_assoc, div_self hv₀, mul_one, sub_self]
        have hgid : (reflect B (disp g v₀)).comp g = LinearMap.id := by
          ext y
          have hy := hzero y
          rw [disp_apply] at hy
          simpa using sub_eq_zero.mp hy
        have hfinal : (reflect B (disp g v₀)).comp ((reflect B (disp g v₀)).comp g) = g := by
          ext y
          simp only [LinearMap.comp_apply]
          exact reflect_reflect B hu (g y)
        rw [← hfinal, hgid]
        exact IsReflProd.cons hu (IsReflProd.id r)


/-- **The Cartan–Dieudonné theorem.**  Over a field of characteristic `≠ 2`, every isometry of a
finite-dimensional nondegenerate symmetric bilinear space of dimension `n` is a composite of at
most `n` reflections. -/
theorem cartan_dieudonne [FiniteDimensional K V] (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0)
    (f : V →ₗ[K] V) (hf : ∀ x y, B (f x) (f y) = B x y) :
    IsReflProd B (finrank K V) f := by
  by_cases hex : ∃ v : V, cdGam B f v ≠ 0
  · exact cd_scherk hs hnd h2 _ f hf (Submodule.finrank_le _) hex
  push Not at hex
  have hiso : ∀ x y : V, B (disp f x) (disp f y) = 0 := by
    intro x y
    have h := cdGam_add hs hf x y
    rw [hex (x + y), hex x, hex y] at h
    simp only [cdSig] at h
    linear_combination h
  by_cases hfid : f = LinearMap.id
  · rw [hfid]; exact IsReflProd.id _
  have hwex : ∃ w : V, B w w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hfid
    have hB0 : ∀ x y : V, B x y = 0 := by
      intro x y
      have e := hcon (x + y)
      simp only [map_add, LinearMap.add_apply] at e
      rw [hcon x, hcon y, hs y x] at e
      have e2 : (2 : K) * B x y = 0 := by linear_combination e
      rcases mul_eq_zero.mp e2 with h' | h'
      · exact absurd h' h2
      · exact h'
    ext x
    have hx0 : x = 0 := hnd x (fun y => hB0 x y)
    simp [hx0]
  obtain ⟨w, hw⟩ := hwex
  have hw0 : w ≠ 0 := by
    intro hcon
    apply hw
    rw [hcon]
    simp
  have hgisom : ∀ a b : V,
      B (((reflect B w).comp f) a) (((reflect B w).comp f) b) = B a b := by
    intro a b
    simp only [LinearMap.comp_apply]
    rw [reflect_isom B hs hw]
    exact hf a b
  have hfw : B (f w) w = B w w := by
    have hgw := hex w
    simp only [cdGam, disp_apply, map_sub, LinearMap.sub_apply] at hgw
    linear_combination hgw
  have hdg : ∀ y : V, disp ((reflect B w).comp f) y
      = disp f y - (2 * B (f y) w / B w w) • w := by
    intro y
    rw [disp_apply ((reflect B w).comp f) y, LinearMap.comp_apply, reflect_apply, disp_apply f y]
    module
  have hdgw : disp ((reflect B w).comp f) w = disp f w - (2 : K) • w := by
    rw [hdg w, hfw]
    congr 2
    field_simp
  have hgamw : cdGam B ((reflect B w).comp f) w ≠ 0 := by
    rw [cdGam_eq, hdgw]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← cdGam_eq B f w, hex w]
    intro hcon
    apply hw
    have e2 : (2 : K) * B w w = 0 := by linear_combination -hcon
    rcases mul_eq_zero.mp e2 with h' | h'
    · exact absurd h' h2
    · exact h'
  have hrange : LinearMap.range (disp ((reflect B w).comp f))
      ≤ LinearMap.range (disp f) ⊔ (K ∙ w) := by
    rintro _ ⟨y, rfl⟩
    rw [hdg y]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩))
  have hsup : finrank K (LinearMap.range (disp f) ⊔ (K ∙ w) : Submodule K V)
      ≤ finrank K (LinearMap.range (disp f)) + 1 := by
    have hsplit := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (disp f)) (K ∙ w)
    have hspan : finrank K (K ∙ w : Submodule K V) = 1 := finrank_span_singleton hw0
    omega
  have hrank' : finrank K (LinearMap.range (disp ((reflect B w).comp f)))
      ≤ finrank K (LinearMap.range (disp f)) + 1 :=
    le_trans (Submodule.finrank_mono hrange) hsup
  have hfinal : (reflect B w).comp ((reflect B w).comp f) = f := by
    ext y
    simp only [LinearMap.comp_apply]
    exact reflect_reflect B hw (f y)
  -- The displacement range is totally isotropic, hence contained in the kernel of `f - 1`
  -- and of dimension at least `2`.
  have hsub : LinearMap.range (disp f) ≤ LinearMap.ker (disp f) := by
    rintro _ ⟨y, rfl⟩
    simp only [LinearMap.mem_ker]
    refine hnd _ ?_
    intro z
    have hp := cd_polar hs hf (disp f y) z
    rw [hiso z y] at hp
    simp only [cdSig] at hp
    rw [hiso (disp f y) z] at hp
    linear_combination hp
  have hkr : finrank K (LinearMap.range (disp f)) ≤ finrank K (LinearMap.ker (disp f)) :=
    Submodule.finrank_mono hsub
  have hrn := LinearMap.finrank_range_add_finrank_ker (disp f)
  have htwo : 2 ≤ finrank K (LinearMap.range (disp f)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, disp f v₁ ≠ 0 := by
      by_contra hcc
      push Not at hcc
      apply hfid
      ext y
      have hy := hcc y
      rw [disp_apply] at hy
      simpa using sub_eq_zero.mp hy
    have hle : (K ∙ disp f v₁) ≤ LinearMap.range (disp f) :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr ⟨v₁, rfl⟩
    have hsp : finrank K (K ∙ disp f v₁ : Submodule K V) = 1 := finrank_span_singleton hv₁
    have heq : (K ∙ disp f v₁) = LinearMap.range (disp f) :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    have hall : ∀ y : V, ∃ c : K, disp f y = c • disp f v₁ := by
      intro y
      have hmem : disp f y ∈ (K ∙ disp f v₁) := by
        rw [heq]; exact ⟨y, rfl⟩
      obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨c, hc'.symm⟩
    apply hv₁
    refine hnd _ ?_
    intro y
    obtain ⟨c, hc'⟩ := hall y
    have hp := cd_polar hs hf v₁ y
    have e1 : cdSig B f v₁ y = 0 := by
      simp only [cdSig, hiso v₁ y]
      ring
    have e2 : B (disp f y) v₁ = 0 := by
      rw [hc']
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← cdGam_eq B f v₁, hex v₁]
      ring
    rw [e1, e2] at hp
    linear_combination hp
  have hbound : finrank K (LinearMap.range (disp f)) + 2 ≤ finrank K V := by omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, finrank K (LinearMap.range (disp f)) = n := ⟨_, rfl⟩
  rw [hn] at hrank' hbound
  have hA := cd_scherk hs hnd h2 (n + 1) _ hgisom hrank' ⟨w, hgamw⟩
  have hstep : IsReflProd B (n + 2) f := by
    rw [← hfinal]
    exact IsReflProd.cons hw hA
  exact hstep.mono _ hbound

/-- **The Cartan–Dieudonné theorem**, list form: every isometry is the composite of a list of at
most `finrank K V` reflections in anisotropic vectors. -/
theorem cartan_dieudonne_list [FiniteDimensional K V] (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0)
    (f : V →ₗ[K] V) (hf : ∀ x y, B (f x) (f y) = B x y) :
    ∃ l : List V, l.length ≤ finrank K V ∧ (∀ v ∈ l, B v v ≠ 0) ∧ f = reflProd B l :=
  (cartan_dieudonne hs hnd h2 f hf).exists_list


/-- A composite of reflections in anisotropic vectors is an isometry. -/
lemma reflProd_isom (B : V →ₗ[K] V →ₗ[K] K) (hs : ∀ x y : V, B x y = B y x) (l : List V) :
    (∀ v ∈ l, B v v ≠ 0) → ∀ x y : V, B (reflProd B l x) (reflProd B l y) = B x y := by
  induction l with
  | nil => intro _ x y; rfl
  | cons v l ih =>
      intro hl x y
      simp only [reflProd, LinearMap.comp_apply]
      rw [reflect_isom B hs (hl v (by simp))]
      exact ih (fun w hw => hl w (by simp [hw])) x y

/-- **Cartan–Dieudonné, characterization form.**  An endomorphism of a finite-dimensional
nondegenerate symmetric bilinear space over a field of characteristic `≠ 2` is an isometry if and
only if it is the composite of at most `finrank K V` reflections in anisotropic vectors. -/
theorem isometry_iff_exists_reflProd [FiniteDimensional K V] (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0) (f : V →ₗ[K] V) :
    (∀ x y : V, B (f x) (f y) = B x y) ↔
      ∃ l : List V, l.length ≤ finrank K V ∧ (∀ v ∈ l, B v v ≠ 0) ∧ f = reflProd B l := by
  constructor
  · intro hf
    exact cartan_dieudonne_list hs hnd h2 f hf
  · rintro ⟨l, -, hl, rfl⟩ x y
    exact reflProd_isom B hs l hl x y

/-- **The Cartan–Dieudonné theorem** for a linear isometry equivalence. -/
theorem cartan_dieudonne_equiv [FiniteDimensional K V] (hs : ∀ x y : V, B x y = B y x)
    (hnd : ∀ x : V, (∀ y, B x y = 0) → x = 0) (h2 : (2 : K) ≠ 0) (f : V ≃ₗ[K] V)
    (hf : ∀ x y, B (f x) (f y) = B x y) :
    IsReflProd B (finrank K V) (f : V →ₗ[K] V) :=
  cartan_dieudonne hs hnd h2 _ hf

/-- **The Cartan–Dieudonné theorem**, stated with mathlib's bilinear-form predicates. -/
theorem cartan_dieudonne_of_bilinForm [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (h2 : (2 : K) ≠ 0)
    (f : V →ₗ[K] V) (hf : ∀ x y, B (f x) (f y) = B x y) :
    ∃ l : List V, l.length ≤ finrank K V ∧ (∀ v ∈ l, B v v ≠ 0) ∧ f = reflProd B l :=
  cartan_dieudonne_list hs.eq hnd.1 h2 f hf

end GaloisForLFunctions.HTGeometry.CartanDieudonne
