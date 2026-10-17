import GaloisForLFunctions.HTGeometry.SymbolicShiftSpace
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The Banach space of Hölder functions on a subshift

For `0 < ϑ`, `HolderSpace A ϑ` consists of the functions `f` on sequences that vanish off the
admissible sequences, are bounded, and satisfy `|f x − f y| ≤ K ϑⁿ` whenever the admissible
sequences `x, y` agree on `n` symbols.  It is realized as the closed subspace of
`ℓ^∞(sequences) × ℓ^∞(agreeing triples)` cut out by the identities
`f = 0` off the subshift and `q(x, y, n) = (f x − f y)/ϑⁿ`; it is therefore complete, and its norm
is the maximum of the supremum norm and the Hölder seminorm.

Main results:
* `norm_apply_le`, `norm_apply_sub_le` — the two halves of the norm;
* `norm_le_of_bounds` — the norm is at most any common bound of the two halves;
* `mk` — a function with both bounds is an element;
* `ofLinear` — a linear operation on functions that preserves the bounds is a bounded operator.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

noncomputable section

variable {k : ℕ} (A : Fin k → Fin k → Prop)

/-- Triples `(x, y, n)` of admissible sequences agreeing on `n` symbols. -/
def AgreeTriple : Type :=
  {p : (ℕ → Fin k) × (ℕ → Fin k) × ℕ // IsAdmissible A p.1 ∧ IsAdmissible A p.2.1 ∧
    Agree p.2.2 p.1 p.2.1}

/-- The ambient space `ℓ^∞(sequences) × ℓ^∞(agreeing triples)`. -/
abbrev HolderAmbient : Type :=
  lp (fun _ : ℕ → Fin k => ℂ) ⊤ × lp (fun _ : AgreeTriple A => ℂ) ⊤

/-- The subspace of pairs `(f, q)` with `f = 0` off the subshift and `q` the Hölder difference
quotient of `f`. -/
def holderSubmodule (ϑ : ℝ) : Submodule ℂ (HolderAmbient A) where
  carrier := {p | (∀ y, ¬ IsAdmissible A y → (p.1 : (ℕ → Fin k) → ℂ) y = 0) ∧
    ∀ q : AgreeTriple A, (p.2 : AgreeTriple A → ℂ) q =
      ((p.1 : (ℕ → Fin k) → ℂ) q.1.1 - (p.1 : (ℕ → Fin k) → ℂ) q.1.2.1) / (ϑ : ℂ) ^ q.1.2.2}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun y hy => ?_, fun q => ?_⟩
    · simp [ha1 y hy, hb1 y hy]
    · simp only [Prod.fst_add, Prod.snd_add, lp.coeFn_add, Pi.add_apply, ha2 q, hb2 q]
      ring
  zero_mem' := by
    refine ⟨fun y _ => ?_, fun q => ?_⟩ <;> simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    refine ⟨fun y hy => ?_, fun q => ?_⟩
    · simp [lp.coeFn_smul, ha1 y hy]
    · simp only [Prod.smul_fst, Prod.smul_snd, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ha2 q]
      ring

theorem isClosed_holderSubmodule (ϑ : ℝ) : IsClosed (holderSubmodule A ϑ : Set (HolderAmbient A)) := by
  have h1 : ∀ y, Continuous fun p : HolderAmbient A => (p.1 : (ℕ → Fin k) → ℂ) y := fun y =>
    (lp.evalCLM ℂ (fun _ : ℕ → Fin k => ℂ) ⊤ y).continuous.comp continuous_fst
  have h2 : ∀ q, Continuous fun p : HolderAmbient A => (p.2 : AgreeTriple A → ℂ) q := fun q =>
    (lp.evalCLM ℂ (fun _ : AgreeTriple A => ℂ) ⊤ q).continuous.comp continuous_snd
  have hset : (holderSubmodule A ϑ : Set (HolderAmbient A)) =
      (⋂ y : {y : ℕ → Fin k // ¬ IsAdmissible A y},
        {p : HolderAmbient A | (p.1 : (ℕ → Fin k) → ℂ) y.1 = 0}) ∩
      ⋂ q : AgreeTriple A, {p : HolderAmbient A | (p.2 : AgreeTriple A → ℂ) q =
        ((p.1 : (ℕ → Fin k) → ℂ) q.1.1 - (p.1 : (ℕ → Fin k) → ℂ) q.1.2.1) / (ϑ : ℂ) ^ q.1.2.2} := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
    rfl
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun y => isClosed_eq (h1 y.1) continuous_const)
    (isClosed_iInter fun q => isClosed_eq (h2 q) (((h1 _).sub (h1 _)).div_const _))

/-- **The Hölder space** `F_ϑ` of the subshift. -/
abbrev HolderSpace (ϑ : ℝ) : Type := ↥(holderSubmodule A ϑ)

instance (ϑ : ℝ) : CompleteSpace (HolderSpace A ϑ) := by
  haveI : IsClosed (holderSubmodule A ϑ : Set (HolderAmbient A)) := isClosed_holderSubmodule A ϑ
  exact IsClosed.completeSpace_coe

variable {A} {ϑ : ℝ}

/-- The underlying function on sequences. -/
def toFn (f : HolderSpace A ϑ) : (ℕ → Fin k) → ℂ := fun y => (f.1.1 : (ℕ → Fin k) → ℂ) y

instance : CoeFun (HolderSpace A ϑ) fun _ => (ℕ → Fin k) → ℂ := ⟨toFn⟩

theorem toFn_add (f g : HolderSpace A ϑ) : toFn (f + g) = toFn f + toFn g := rfl

theorem toFn_smul (c : ℂ) (f : HolderSpace A ϑ) : toFn (c • f) = c • toFn f := rfl

@[simp] theorem add_apply (f g : HolderSpace A ϑ) (y : ℕ → Fin k) : (f + g) y = f y + g y := rfl

@[simp] theorem sub_apply (f g : HolderSpace A ϑ) (y : ℕ → Fin k) : (f - g) y = f y - g y := rfl

@[simp] theorem smul_apply (c : ℂ) (f : HolderSpace A ϑ) (y : ℕ → Fin k) : (c • f) y = c * f y :=
  rfl

@[simp] theorem zero_apply (y : ℕ → Fin k) : (0 : HolderSpace A ϑ) y = 0 := rfl

@[simp] theorem neg_apply (f : HolderSpace A ϑ) (y : ℕ → Fin k) : (-f) y = -f y := rfl

theorem apply_of_not_adm (f : HolderSpace A ϑ) {y : ℕ → Fin k} (hy : ¬ IsAdmissible A y) :
    f y = 0 := f.2.1 y hy

theorem quot_apply (f : HolderSpace A ϑ) (q : AgreeTriple A) :
    (f.1.2 : AgreeTriple A → ℂ) q = (f q.1.1 - f q.1.2.1) / (ϑ : ℂ) ^ q.1.2.2 := f.2.2 q

theorem ext_iff' {f g : HolderSpace A ϑ} : f = g ↔ ∀ y, f y = g y := by
  constructor
  · rintro rfl y; rfl
  · intro h
    have h1 : f.1.1 = g.1.1 := lp.ext (funext h)
    have h2 : f.1.2 = g.1.2 := lp.ext (funext fun q => by rw [quot_apply, quot_apply, h, h])
    exact Subtype.ext (Prod.ext h1 h2)

@[ext] theorem ext {f g : HolderSpace A ϑ} (h : ∀ y, f y = g y) : f = g := ext_iff'.mpr h

/-- The supremum half of the norm. -/
theorem norm_apply_le (f : HolderSpace A ϑ) (y : ℕ → Fin k) : ‖f y‖ ≤ ‖f‖ := by
  calc ‖f y‖ ≤ ‖f.1.1‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ y
    _ ≤ ‖f.1‖ := norm_fst_le _
    _ = ‖f‖ := rfl

/-- The Hölder half of the norm. -/
theorem norm_apply_sub_le (hϑ : 0 < ϑ) (f : HolderSpace A ϑ) {x y : ℕ → Fin k} {n : ℕ}
    (hx : IsAdmissible A x) (hy : IsAdmissible A y) (hxy : Agree n x y) :
    ‖f x - f y‖ ≤ ‖f‖ * ϑ ^ n := by
  set q : AgreeTriple A := ⟨(x, y, n), hx, hy, hxy⟩
  have hq := quot_apply f q
  have hle : ‖(f.1.2 : AgreeTriple A → ℂ) q‖ ≤ ‖f‖ :=
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ q).trans (norm_snd_le _)
  rw [hq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hϑ,
    div_le_iff₀ (pow_pos hϑ n)] at hle
  exact hle

/-- **The norm is bounded by any common bound of the supremum and the Hölder quotients.** -/
theorem norm_le_of_bounds (hϑ : 0 < ϑ) (f : HolderSpace A ϑ) {K : ℝ} (hK : 0 ≤ K)
    (hsup : ∀ y, ‖f y‖ ≤ K)
    (hhol : ∀ x y n, IsAdmissible A x → IsAdmissible A y → Agree n x y → ‖f x - f y‖ ≤ K * ϑ ^ n) :
    ‖f‖ ≤ K := by
  show ‖f.1‖ ≤ K
  rw [Prod.norm_def]
  refine max_le (lp.norm_le_of_forall_le hK hsup) (lp.norm_le_of_forall_le hK fun q => ?_)
  rw [quot_apply, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hϑ,
    div_le_iff₀ (pow_pos hϑ _)]
  exact hhol _ _ _ q.2.1 q.2.2.1 q.2.2.2

/-- **A function with both bounds is an element of the Hölder space.** -/
def mk (hϑ : 0 < ϑ) (g : (ℕ → Fin k) → ℂ) (hsupp : ∀ y, ¬ IsAdmissible A y → g y = 0) (K : ℝ)
    (hsup : ∀ y, ‖g y‖ ≤ K)
    (hhol : ∀ x y n, IsAdmissible A x → IsAdmissible A y → Agree n x y → ‖g x - g y‖ ≤ K * ϑ ^ n) :
    HolderSpace A ϑ :=
  ⟨(⟨g, memℓp_infty ⟨K, by rintro _ ⟨y, rfl⟩; exact hsup y⟩⟩,
    ⟨fun q => (g q.1.1 - g q.1.2.1) / (ϑ : ℂ) ^ q.1.2.2, memℓp_infty ⟨K, by
      rintro _ ⟨q, rfl⟩
      show ‖(g q.1.1 - g q.1.2.1) / (ϑ : ℂ) ^ q.1.2.2‖ ≤ K
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hϑ,
        div_le_iff₀ (pow_pos hϑ _)]
      exact hhol _ _ _ q.2.1 q.2.2.1 q.2.2.2⟩⟩), hsupp, fun _ => rfl⟩

@[simp] theorem mk_apply (hϑ : 0 < ϑ) (g : (ℕ → Fin k) → ℂ) (hsupp) (K : ℝ) (hsup) (hhol)
    (y : ℕ → Fin k) : mk (A := A) hϑ g hsupp K hsup hhol y = g y := rfl

theorem norm_mk_le (hϑ : 0 < ϑ) (g : (ℕ → Fin k) → ℂ) (hsupp) {K : ℝ} (hK : 0 ≤ K) (hsup) (hhol) :
    ‖mk (A := A) hϑ g hsupp K hsup hhol‖ ≤ K :=
  norm_le_of_bounds hϑ _ hK hsup hhol

/-- The underlying function, as a linear map. -/
def toFunLinear : HolderSpace A ϑ →ₗ[ℂ] (ℕ → Fin k) → ℂ where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **A linear operation on functions that preserves the Hölder bounds is a bounded operator.** -/
def ofLinear (hϑ : 0 < ϑ) (L : ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hsupp : ∀ f : HolderSpace A ϑ, ∀ y, ¬ IsAdmissible A y → L f y = 0)
    (hsup : ∀ f : HolderSpace A ϑ, ∀ y, ‖L f y‖ ≤ K * ‖f‖)
    (hhol : ∀ f : HolderSpace A ϑ, ∀ x y n, IsAdmissible A x → IsAdmissible A y → Agree n x y →
      ‖L f x - L f y‖ ≤ K * ‖f‖ * ϑ ^ n) :
    HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ :=
  LinearMap.mkContinuous
    { toFun := fun f => mk hϑ (L f) (hsupp f) (K * ‖f‖) (hsup f) (hhol f)
      map_add' := fun f g => by
        ext y
        show L (toFn (f + g)) y = L (toFn f) y + L (toFn g) y
        rw [toFn_add, map_add]; rfl
      map_smul' := fun c f => by
        ext y
        show L (toFn (c • f)) y = c * L (toFn f) y
        rw [toFn_smul, map_smul]; rfl }
    K fun f => norm_mk_le hϑ (L f) (hsupp f) (mul_nonneg hK (norm_nonneg f)) (hsup f) (hhol f)

@[simp] theorem ofLinear_apply (hϑ : 0 < ϑ) (L : ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hsupp) (hsup) (hhol) (f : HolderSpace A ϑ) (y : ℕ → Fin k) :
    ofLinear hϑ L K hK hsupp hsup hhol f y = L f y := by
  rw [ofLinear, LinearMap.mkContinuous_apply]
  rfl

theorem norm_ofLinear_le (hϑ : 0 < ϑ) (L : ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hsupp) (hsup) (hhol) : ‖ofLinear (A := A) hϑ L K hK hsupp hsup hhol‖ ≤ K := by
  unfold ofLinear
  exact LinearMap.mkContinuous_norm_le _ hK _

end

end GaloisForLFunctions.HTGeometry.Symbolic
