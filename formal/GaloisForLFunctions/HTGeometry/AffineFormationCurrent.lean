import GaloisForLFunctions.HTGeometry.SplitFormationCornerFlatness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# The affine formation current and the four-organ Bianchi law

A linear comparison that preserves the recovered base but not the chosen formation section has a
unique affine vertical normal form: a formation current `a : X → ker p` measuring how the source
is re-formed, together with a vertical transport `L`.  Composition couples them by the semidirect
law `(a', L') ⋆ (a, L) = (a' + L' a, L' L)`, triangle defects split into a current defect and a
transport defect, and associativity forces coupled four-organ Bianchi identities in which the
mixed term `Λ a` is load-bearing.
-/

namespace GaloisForLFunctions.HTGeometry

section Affine

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
  {Zi Zj Zk Zl : Type*}
  [AddCommGroup Zi] [Module K Zi] [AddCommGroup Zj] [Module K Zj]
  [AddCommGroup Zk] [Module K Zk] [AddCommGroup Zl] [Module K Zl]
  {fi : X →ₗ[K] Zi} {pi : Zi →ₗ[K] X} {fj : X →ₗ[K] Zj} {pj : Zj →ₗ[K] X}
  {fk : X →ₗ[K] Zk} {pk : Zk →ₗ[K] X} {fl : X →ₗ[K] Zl} {pl : Zl →ₗ[K] X}

/-- **`(AFC.4)`.**  A comparison preserving the recovered base. -/
def BasePreserving (pi : Zi →ₗ[K] X) (pj : Zj →ₗ[K] X) (Cji : Zi →ₗ[K] Zj) : Prop :=
  pj.comp Cji = pi

theorem BasePreserving.apply {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji) (z : Zi) :
    pj (Cji z) = pi z := congrArg (fun g : Zi →ₗ[K] X => g z) h

/-- **`(AFC.5)`.**  The affine formation current of a base-preserving comparison. -/
def formationCurrent (fi : X →ₗ[K] Zi) (fj : X →ₗ[K] Zj) {Cji : Zi →ₗ[K] Zj}
    (hi : pi.comp fi = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    (h : BasePreserving pi pj Cji) : X →ₗ[K] ↥(vertical pj) :=
  LinearMap.codRestrict (vertical pj) (Cji.comp fi - fj) (fun x => by
    show pj (Cji (fi x) - fj x) = 0
    rw [map_sub, h.apply, recover_form fi pi hi, recover_form fj pj hj, sub_self])

@[simp] theorem formationCurrent_coe (fi : X →ₗ[K] Zi) (fj : X →ₗ[K] Zj) {Cji : Zi →ₗ[K] Zj}
    (hi : pi.comp fi = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    (h : BasePreserving pi pj Cji) (x : X) :
    ((formationCurrent fi fj hi hj h x : ↥(vertical pj)) : Zj) = Cji (fi x) - fj x := rfl

/-- **`(AFC.5)`.**  The vertical transport of a base-preserving comparison. -/
def affineTransport {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji) :
    ↥(vertical pi) →ₗ[K] ↥(vertical pj) :=
  LinearMap.codRestrict (vertical pj) (Cji.comp (vertical pi).subtype) (fun v => by
    show pj (Cji (v : Zi)) = 0
    rw [h.apply]
    exact v.2)

@[simp] theorem affineTransport_coe {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji)
    (v : ↥(vertical pi)) : ((affineTransport h v : ↥(vertical pj)) : Zj) = Cji (v : Zi) := rfl

/-- **Theorem 2.1 `(AFC.6)`.**  Unique generation/transport decomposition. -/
theorem splitChart_basePreserving (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji)
    (x : X) (v : ↥(vertical pi)) :
    splitChart fj pj hj (Cji (splitAssemble fi pi (x, v)))
      = (x, formationCurrent fi fj hi hj h x + affineTransport h v) := by
  have h0 : pi (v : Zi) = 0 := v.2
  have hbase : pj (Cji (fi x + (v : Zi))) = x := by
    rw [h.apply, map_add, recover_form fi pi hi, h0, add_zero]
  refine Prod.ext hbase (Subtype.ext ?_)
  show Cji (fi x + (v : Zi)) - fj (pj (Cji (fi x + (v : Zi))))
    = (Cji (fi x) - fj x) + Cji (v : Zi)
  rw [hbase, map_add]
  abel

/-- **Theorem 2.1, uniqueness.** -/
theorem affine_normal_form_unique (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji)
    (a : X →ₗ[K] ↥(vertical pj)) (L : ↥(vertical pi) →ₗ[K] ↥(vertical pj))
    (hform : ∀ x v, splitChart fj pj hj (Cji (splitAssemble fi pi (x, v))) = (x, a x + L v)) :
    a = formationCurrent fi fj hi hj h ∧ L = affineTransport h := by
  constructor
  · refine LinearMap.ext fun x => ?_
    have h1 := hform x 0
    have h2 := splitChart_basePreserving hi hj h x 0
    rw [h1] at h2
    have := (Prod.ext_iff.mp h2).2
    simpa using this
  · refine LinearMap.ext fun v => ?_
    have h1 := hform 0 v
    have h2 := splitChart_basePreserving hi hj h 0 v
    rw [h1] at h2
    have := (Prod.ext_iff.mp h2).2
    simpa using this

/-- **`(AFC.7)`.**  The current vanishes exactly when the comparison preserves the section. -/
theorem formationCurrent_eq_zero_iff (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji) :
    formationCurrent fi fj hi hj h = 0 ↔ Cji.comp fi = fj := by
  constructor
  · intro hz
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun g : X →ₗ[K] ↥(vertical pj) => ((g x : ↥(vertical pj)) : Zj)) hz
    show Cji (fi x) = fj x
    have h0 : Cji (fi x) - fj x = 0 := this
    linear_combination (norm := abel) h0
  · intro hC
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hcx : Cji (fi x) = fj x := congrArg (fun g : X →ₗ[K] Zj => g x) hC
    show Cji (fi x) - fj x = 0
    rw [hcx, sub_self]

/-- **`(AFC.8)`.**  Both blocks vanish exactly for the canonical recover-then-form comparison. -/
theorem formationCurrent_and_transport_eq_zero_iff (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) {Cji : Zi →ₗ[K] Zj} (h : BasePreserving pi pj Cji) :
    (formationCurrent fi fj hi hj h = 0 ∧ affineTransport h = 0) ↔ Cji = fj.comp pi := by
  constructor
  · rintro ⟨ha, hL⟩
    refine LinearMap.ext fun z => ?_
    have hdecomp : z = fi (pi z) + (z - fi (pi z)) := by abel
    have hmem : z - fi (pi z) ∈ vertical pi := by
      show pi (z - fi (pi z)) = 0
      rw [map_sub, recover_form fi pi hi, sub_self]
    have hva : Cji (fi (pi z)) = fj (pi z) := by
      have := (formationCurrent_eq_zero_iff hi hj h).mp ha
      exact congrArg (fun g : X →ₗ[K] Zj => g (pi z)) this
    have hvL : Cji (z - fi (pi z)) = 0 := by
      have := congrArg (fun g : ↥(vertical pi) →ₗ[K] ↥(vertical pj) =>
        ((g ⟨z - fi (pi z), hmem⟩ : ↥(vertical pj)) : Zj)) hL
      exact this
    show Cji z = fj (pi z)
    conv_lhs => rw [hdecomp]
    rw [map_add, hva, hvL, add_zero]
  · intro hC
    constructor
    · refine LinearMap.ext fun x => Subtype.ext ?_
      show Cji (fi x) - fj x = 0
      rw [hC]
      show fj (pi (fi x)) - fj x = 0
      rw [recover_form fi pi hi, sub_self]
    · refine LinearMap.ext fun v => Subtype.ext ?_
      show Cji (v : Zi) = 0
      rw [hC]
      have h0 : pi (v : Zi) = 0 := v.2
      show fj (pi (v : Zi)) = 0
      rw [h0, map_zero]

/-! ## The semidirect composition law -/

theorem BasePreserving.comp {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj) :
    BasePreserving pi pk (Ckj.comp Cji) := by
  refine LinearMap.ext fun z => ?_
  show pk (Ckj (Cji z)) = pi z
  rw [hkj.apply, hji.apply]

/-- **Theorem 3.1 `(AFC.9)`, transport block.** -/
theorem affineTransport_comp {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj) :
    affineTransport (hji.comp hkj) = (affineTransport hkj).comp (affineTransport hji) :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- **Theorem 3.1 `(AFC.9)`, current block.**  The inner current is transported before it is
added. -/
theorem formationCurrent_comp (hi : pi.comp fi = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    (hk : pk.comp fk = LinearMap.id) {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj) :
    formationCurrent fi fk hi hk (hji.comp hkj)
      = formationCurrent fj fk hj hk hkj
        + (affineTransport hkj).comp (formationCurrent fi fj hi hj hji) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show Ckj (Cji (fi x)) - fk x = (Ckj (fj x) - fk x) + Ckj (Cji (fi x) - fj x)
  rw [map_sub]
  abel

/-! ## Joint triangle defect -/

/-- **`(AFC.11)`.**  The generated-current defect. -/
def currentDefect (hi : pi.comp fi = LinearMap.id) (hj : pj.comp fj = LinearMap.id)
    (hk : pk.comp fk = LinearMap.id) {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk}
    {Cki : Zi →ₗ[K] Zk} (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj)
    (hki : BasePreserving pi pk Cki) : X →ₗ[K] ↥(vertical pk) :=
  formationCurrent fj fk hj hk hkj
    + (affineTransport hkj).comp (formationCurrent fi fj hi hj hji)
    - formationCurrent fi fk hi hk hki

/-- **`(AFC.11)`.**  The transported defect. -/
def transportDefect {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj)
    (hki : BasePreserving pi pk Cki) : ↥(vertical pi) →ₗ[K] ↥(vertical pk) :=
  (affineTransport hkj).comp (affineTransport hji) - affineTransport hki

/-- **Theorem 4.1 `(AFC.13)`.**  The joint triangle defect is invisible to recovery. -/
theorem recover_comp_affineDefect {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj)
    (hki : BasePreserving pi pk Cki) :
    pk.comp (fusionDefect Cji Ckj Cki) = 0 := by
  refine LinearMap.ext fun z => ?_
  show pk (Ckj (Cji z) - Cki z) = 0
  rw [map_sub, hkj.apply, hji.apply, hki.apply, sub_self]

/-- **Theorem 4.1 `(AFC.12)`.**  The joint triangle defect has exact vertical block form. -/
theorem splitChart_affineDefect (hi : pi.comp fi = LinearMap.id)
    (hj : pj.comp fj = LinearMap.id) (hk : pk.comp fk = LinearMap.id)
    {Cji : Zi →ₗ[K] Zj} {Ckj : Zj →ₗ[K] Zk} {Cki : Zi →ₗ[K] Zk}
    (hji : BasePreserving pi pj Cji) (hkj : BasePreserving pj pk Ckj)
    (hki : BasePreserving pi pk Cki) (x : X) (v : ↥(vertical pi)) :
    splitChart fk pk hk (fusionDefect Cji Ckj Cki (splitAssemble fi pi (x, v)))
      = (0, currentDefect hi hj hk hji hkj hki x + transportDefect hji hkj hki v) := by
  have h0 : pi (v : Zi) = 0 := v.2
  have hb1 : pk (Ckj (Cji (fi x + (v : Zi)))) = x := by
    rw [hkj.apply, hji.apply, map_add, recover_form fi pi hi, h0, add_zero]
  have hb2 : pk (Cki (fi x + (v : Zi))) = x := by
    rw [hki.apply, map_add, recover_form fi pi hi, h0, add_zero]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show pk (Ckj (Cji (fi x + (v : Zi))) - Cki (fi x + (v : Zi))) = 0
    rw [map_sub, hb1, hb2, sub_self]
  · show (Ckj (Cji (fi x + (v : Zi))) - Cki (fi x + (v : Zi)))
      - fk (pk (Ckj (Cji (fi x + (v : Zi))) - Cki (fi x + (v : Zi))))
      = ((Ckj (fj x) - fk x) + Ckj (Cji (fi x) - fj x) - (Cki (fi x) - fk x))
        + (Ckj (Cji (v : Zi)) - Cki (v : Zi))
    rw [map_sub, hb1, hb2, sub_self, map_zero, sub_zero, map_add, map_add, map_add, map_sub]
    abel

/-! ## Four-organ Bianchi identities -/

/-- **Theorem 5.1 `(AFC.15)`.**  Transport-defect conservation, as a formal identity. -/
theorem bianchi_transport {Vi Vj Vk Vl : Type*}
    [AddCommGroup Vi] [Module K Vi] [AddCommGroup Vj] [Module K Vj]
    [AddCommGroup Vk] [Module K Vk] [AddCommGroup Vl] [Module K Vl]
    (Lji : Vi →ₗ[K] Vj) (Lkj : Vj →ₗ[K] Vk) (Lki : Vi →ₗ[K] Vk)
    (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) (Lli : Vi →ₗ[K] Vl) :
    Llk.comp (Lkj.comp Lji - Lki) + (Llk.comp Lki - Lli)
      = (Llk.comp Lkj - Llj).comp Lji + (Llj.comp Lji - Lli) := by
  refine LinearMap.ext fun v => ?_
  show Llk (Lkj (Lji v) - Lki v) + (Llk (Lki v) - Lli v)
    = (Llk (Lkj (Lji v)) - Llj (Lji v)) + (Llj (Lji v) - Lli v)
  rw [map_sub]
  abel

/-- **Theorem 5.1 `(AFC.16)`.**  Current-defect conservation, with the load-bearing mixed term
`Λ a`. -/
theorem bianchi_current {Vi Vj Vk Vl : Type*}
    [AddCommGroup Vi] [Module K Vi] [AddCommGroup Vj] [Module K Vj]
    [AddCommGroup Vk] [Module K Vk] [AddCommGroup Vl] [Module K Vl]
    (aji : X →ₗ[K] Vj) (akj : X →ₗ[K] Vk) (aki : X →ₗ[K] Vk)
    (alk : X →ₗ[K] Vl) (alj : X →ₗ[K] Vl) (ali : X →ₗ[K] Vl)
    (Lkj : Vj →ₗ[K] Vk) (Llk : Vk →ₗ[K] Vl) (Llj : Vj →ₗ[K] Vl) :
    Llk.comp (akj + Lkj.comp aji - aki) + (alk + Llk.comp aki - ali)
      = (alk + Llk.comp akj - alj) + (Llk.comp Lkj - Llj).comp aji
        + (alj + Llj.comp aji - ali) := by
  refine LinearMap.ext fun x => ?_
  show Llk (akj x + Lkj (aji x) - aki x) + (alk x + Llk (aki x) - ali x)
    = ((alk x + Llk (akj x) - alj x) + (Llk (Lkj (aji x)) - Llj (aji x)))
      + (alj x + Llj (aji x) - ali x)
  rw [map_sub, map_add]
  abel

end Affine

/-! ## The finite diagonal/reset realization -/

section FiniteRealization

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **`(AFC.17)`.**  First-marginal recovery. -/
def marginalRecovery : ((A × A) → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun z a := ∑ b, z (a, b)
  map_add' z w := by
    funext a
    show ∑ b, (z (a, b) + w (a, b)) = (∑ b, z (a, b)) + ∑ b, w (a, b)
    rw [Finset.sum_add_distrib]
  map_smul' c z := by
    funext a
    show ∑ b, c * z (a, b) = c * ∑ b, z (a, b)
    rw [Finset.mul_sum]

/-- **`(AFC.18)`.**  The diagonal section. -/
def diagSection : (A → ℝ) →ₗ[ℝ] ((A × A) → ℝ) where
  toFun x t := if t.1 = t.2 then x t.1 else 0
  map_add' x y := by
    funext t
    by_cases h : t.1 = t.2 <;> simp [h]
  map_smul' c x := by
    funext t
    by_cases h : t.1 = t.2 <;> simp [h]

/-- **`(AFC.18)`.**  The reset section attached to a weight vector. -/
def resetSection (q : A → ℝ) : (A → ℝ) →ₗ[ℝ] ((A × A) → ℝ) where
  toFun x t := x t.1 * q t.2
  map_add' x y := by
    funext t
    show (x t.1 + y t.1) * q t.2 = x t.1 * q t.2 + y t.1 * q t.2
    ring
  map_smul' c x := by
    funext t
    show (c * x t.1) * q t.2 = c * (x t.1 * q t.2)
    ring

theorem marginalRecovery_diagSection :
    marginalRecovery.comp (diagSection : (A → ℝ) →ₗ[ℝ] ((A × A) → ℝ)) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext a
  show (∑ b, if a = b then x a else 0) = x a
  rw [Finset.sum_ite_eq Finset.univ a (fun _ => x a)]
  simp

omit [DecidableEq A] in
theorem marginalRecovery_resetSection {q : A → ℝ} (hq : ∑ b, q b = 1) :
    marginalRecovery.comp (resetSection q) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext a
  show (∑ b, x a * q b) = x a
  rw [← Finset.mul_sum, hq, mul_one]

omit [DecidableEq A] in
/-- The ambient identity, read as a comparison from the diagonal chart to the reset chart. -/
theorem basePreserving_id :
    BasePreserving (marginalRecovery : ((A × A) → ℝ) →ₗ[ℝ] (A → ℝ)) marginalRecovery
      LinearMap.id :=
  LinearMap.comp_id _

omit [DecidableEq A] in
/-- **Theorem 6.1 `(AFC.19)`, transport block.**  The identity comparison transports verticals by
the identity. -/
theorem affineTransport_id_realization :
    affineTransport (basePreserving_id (A := A)) = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext rfl

/-- **Theorem 6.1 `(AFC.19)`, current block.**  The identity comparison has current
`f_Δ − f_R`. -/
theorem formationCurrent_id_realization {q : A → ℝ} (hq : ∑ b, q b = 1) (x : A → ℝ) :
    ((formationCurrent diagSection (resetSection q) marginalRecovery_diagSection
        (marginalRecovery_resetSection hq) basePreserving_id x : ↥(vertical marginalRecovery))
      : (A × A) → ℝ)
      = diagSection x - resetSection q x := rfl

/-- **Theorem 6.1 `(AFC.20)`.**  Evaluated at the formed weight vector, the current is the
diagonal minus the product state. -/
theorem formationCurrent_at_weight {q : A → ℝ} (hq : ∑ b, q b = 1) (t : A × A) :
    ((formationCurrent diagSection (resetSection q) marginalRecovery_diagSection
        (marginalRecovery_resetSection hq) basePreserving_id q : ↥(vertical marginalRecovery))
      : (A × A) → ℝ) t = (if t.1 = t.2 then q t.1 else 0) - q t.1 * q t.2 := rfl

/-- The reverse comparison has the opposite current and the same transport, so their semidirect
composite current vanishes exactly. -/
theorem formationCurrent_reverse_add {q : A → ℝ} (hq : ∑ b, q b = 1) :
    formationCurrent (resetSection q) diagSection (marginalRecovery_resetSection hq)
        marginalRecovery_diagSection basePreserving_id
      + formationCurrent diagSection (resetSection q) marginalRecovery_diagSection
        (marginalRecovery_resetSection hq) basePreserving_id = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  funext t
  show (resetSection q x t - diagSection x t) + (diagSection x t - resetSection q x t) = 0
  ring

/-- The Shannon entropy of a weight vector. -/
noncomputable def shannonEntropy (q : A → ℝ) : ℝ := -∑ a, q a * Real.log (q a)

/-- **`(AFC.21)`.**  The total-variation shadow of the affine current. -/
theorem totalVariation_current {q : A → ℝ} (hnn : ∀ a, 0 ≤ q a) (hq : ∑ b, q b = 1) :
    (2⁻¹ : ℝ) * ∑ t : A × A, |(if t.1 = t.2 then q t.1 else 0) - q t.1 * q t.2|
      = 1 - ∑ a, q a * q a := by
  have hle : ∀ a, q a ≤ 1 := by
    intro a
    rw [← hq]
    exact Finset.single_le_sum (fun b _ => hnn b) (Finset.mem_univ a)
  have hsum : ∑ t : A × A, |(if t.1 = t.2 then q t.1 else 0) - q t.1 * q t.2|
      = ∑ a, ∑ b, |(if a = b then q a else 0) - q a * q b| := Fintype.sum_prod_type _
  have hinner : ∀ a, ∑ b, |(if a = b then q a else 0) - q a * q b|
      = (q a - q a * q a) + (q a - q a * q a) := by
    intro a
    have hsplit : ∑ b, |(if a = b then q a else 0) - q a * q b|
        = |q a - q a * q a| + ∑ b ∈ Finset.univ.erase a, |q a * q b| := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
      congr 1
      · rw [if_pos rfl]
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [if_neg (Ne.symm (Finset.mem_erase.mp hb).1), zero_sub, abs_neg]
    have habs : |q a - q a * q a| = q a - q a * q a := by
      refine abs_of_nonneg ?_
      nlinarith [hnn a, hle a]
    have hoff : ∑ b ∈ Finset.univ.erase a, |q a * q b|
        = ∑ b ∈ Finset.univ.erase a, q a * q b := by
      refine Finset.sum_congr rfl fun b _ => abs_of_nonneg (mul_nonneg (hnn a) (hnn b))
    have htot : ∑ b ∈ Finset.univ.erase a, q a * q b = q a - q a * q a := by
      have h1 : ∑ b, q a * q b = q a * q a + ∑ b ∈ Finset.univ.erase a, q a * q b :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)).symm
      rw [← Finset.mul_sum, hq, mul_one] at h1
      linarith
    rw [hsplit, habs, hoff, htot]
  rw [hsum]
  have hfin : ∑ a, ∑ b, |(if a = b then q a else 0) - q a * q b|
      = ∑ a, ((q a - q a * q a) + (q a - q a * q a)) := Finset.sum_congr rfl fun a _ => hinner a
  rw [hfin]
  have hexp : ∑ a, ((q a - q a * q a) + (q a - q a * q a))
      = 2 * ((∑ a, q a) - ∑ a, q a * q a) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hexp, hq]
  ring

/-- **`(AFC.22)`.**  The relative-entropy shadow of the affine current is the Shannon entropy. -/
theorem relativeEntropy_current (q : A → ℝ) :
    ∑ t : A × A, (if t.1 = t.2 then q t.1 else 0)
        * Real.log ((if t.1 = t.2 then q t.1 else 0) / (q t.1 * q t.2))
      = shannonEntropy q := by
  have hsum : ∑ t : A × A, (if t.1 = t.2 then q t.1 else 0)
      * Real.log ((if t.1 = t.2 then q t.1 else 0) / (q t.1 * q t.2))
      = ∑ a, ∑ b, (if a = b then q a else 0)
        * Real.log ((if a = b then q a else 0) / (q a * q b)) := Fintype.sum_prod_type _
  have hinner : ∀ a, ∑ b, (if a = b then q a else 0)
      * Real.log ((if a = b then q a else 0) / (q a * q b)) = -(q a * Real.log (q a)) := by
    intro a
    have hsplit : ∑ b, (if a = b then q a else 0)
        * Real.log ((if a = b then q a else 0) / (q a * q b))
        = q a * Real.log (q a / (q a * q a)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a), if_pos rfl]
      have hzero : ∑ b ∈ Finset.univ.erase a, (if a = b then q a else 0)
          * Real.log ((if a = b then q a else 0) / (q a * q b)) = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        rw [if_neg (Ne.symm (Finset.mem_erase.mp hb).1), zero_mul]
      rw [hzero, add_zero]
    rw [hsplit]
    by_cases hqa : q a = 0
    · rw [hqa, zero_mul, zero_mul, neg_zero]
    · have hval : q a / (q a * q a) = (q a)⁻¹ := by
        field_simp
      rw [hval, Real.log_inv]
      ring
  rw [hsum, Finset.sum_congr rfl fun a _ => hinner a, shannonEntropy, ← Finset.sum_neg_distrib]

/-- The diagonal density state attached to a weight vector. -/
def diagonalState (q : A → ℝ) : Matrix A A ℝ := Matrix.diagonal q

/-- The weight entries are eigenvalues of the diagonal state. -/
theorem diagonalState_mulVec_single (q : A → ℝ) (a : A) :
    (diagonalState q).mulVec (Pi.single a (1 : ℝ)) = q a • Pi.single a (1 : ℝ) := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [diagonalState, Matrix.mulVec_diagonal]
  · simp [diagonalState, Matrix.mulVec_diagonal, hb]

/-- **`(AFC.23)`.**  The spectral (von Neumann) entropy of the diagonal density state is the
Shannon entropy of its weight vector. -/
theorem vonNeumannEntropy_diagonalState (q : A → ℝ) :
    -∑ a, diagonalState q a a * Real.log (diagonalState q a a) = shannonEntropy q := by
  rw [shannonEntropy]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show diagonalState q a a = q a from Matrix.diagonal_apply_eq q a]

end FiniteRealization

end GaloisForLFunctions.HTGeometry
