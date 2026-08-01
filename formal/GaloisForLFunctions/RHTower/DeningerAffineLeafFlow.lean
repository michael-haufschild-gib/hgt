import GaloisForLFunctions.RHTower.DeningerKronecker
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The affine leaf distribution of the fine generic source

A point of the fine generic source is a unitary character, a nonzero Kummer vector, and a positive
suspension height.  Two one-parameter groups act on it: the modulus Euler flow, which rescales the
Kummer vector, and the Kummer–Kronecker phase flow, which twists the character by the unitary
character `κ_h^t(a) = exp (i t ⟪h, f a⟫)` determined by the Kummer vector.

Conjugating the phase flow by the modulus flow rescales its time parameter exponentially.  This is
the integrated form of the bracket relation `[A, K] = K`; the span of the two fields is therefore
involutive and the two flows generate an action of the affine group of the line, whose orbits are
the leaves.  The suspension height is constant on each leaf, so Deninger's flow — which changes
only the suspension height — is transverse to the foliation.

* `deningerKappa` : the unitary character determined by a Kummer vector and a time.
* `DeningerFinePoint` : a point of the fine generic source.
* `deningerModulusFlow`, `deningerPhaseFlow` : the two one-parameter flows.
* `deningerModulus_phase_conjugation` : the integrated bracket relation `[A, K] = K`.
* `deningerAffineFlow_comp` : the two flows generate an action of the affine group.
* `deningerAffineLeaf` : the leaf through a point, as the orbit of that action.
* `deningerSuspFlow_mem_leaf_iff` : Deninger's flow is transverse to the leaves.
-/

namespace RHTower

open scoped InnerProductSpace

section AffineLeaf

variable {V : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Kummer linear functional `ℓ_h(a) = ⟪h, f a⟫` attached to a Kummer vector. -/
def deningerKummerForm (f : V → H) (h : H) (a : V) : ℝ := ⟪h, f a⟫_ℝ

theorem deningerKummerForm_smul (f : V → H) (c : ℝ) (h : H) (a : V) :
    deningerKummerForm f (c • h) a = c * deningerKummerForm f h a := by
  rw [deningerKummerForm, deningerKummerForm, real_inner_smul_left]

/-- **The Kummer functional of a nonzero vector is not identically zero.**  This is the statement
that the Kummer–Kronecker phase field does not vanish. -/
theorem deningerKummerForm_ne_zero {f : V → H}
    (hdense : Dense ((Submodule.span ℝ (Set.range f) : Submodule ℝ H) : Set H)) {h : H}
    (hh : h ≠ 0) : ∃ a : V, deningerKummerForm f h a ≠ 0 := by
  obtain ⟨y, hy, hne⟩ := deningerKronecker_ne_zero hdense hh
  obtain ⟨a, rfl⟩ := hy
  exact ⟨a, hne⟩

/-- The unitary character determined by a Kummer vector and a time. -/
noncomputable def deningerKappa (f : V → H) (h : H) (t : ℝ) : V → Circle :=
  fun a => Circle.exp (t * deningerKummerForm f h a)

@[simp] theorem deningerKappa_zero (f : V → H) (h : H) : deningerKappa f h 0 = 1 := by
  funext a
  rw [deningerKappa, zero_mul, Circle.exp_zero]
  rfl

@[simp] theorem deningerKappa_zero_vec (f : V → H) (t : ℝ) :
    deningerKappa f (0 : H) t = 1 := by
  funext a
  rw [deningerKappa, deningerKummerForm, inner_zero_left, mul_zero, Circle.exp_zero]
  rfl

theorem deningerKappa_add (f : V → H) (h : H) (t₁ t₂ : ℝ) :
    deningerKappa f h (t₁ + t₂) = deningerKappa f h t₁ * deningerKappa f h t₂ := by
  funext a
  rw [deningerKappa, add_mul, Circle.exp_add]
  rfl

/-- **The scaling law of the phase character.**  Rescaling the Kummer vector rescales the time,
which is why the modulus flow conjugates the phase flow into a reparametrized phase flow. -/
theorem deningerKappa_smul (f : V → H) (c : ℝ) (h : H) (t : ℝ) :
    deningerKappa f (c • h) t = deningerKappa f h (c * t) := by
  funext a
  rw [deningerKappa, deningerKappa, deningerKummerForm_smul]
  ring_nf

theorem deningerKappa_pow (f : V → H) (h : H) (t : ℝ) (n : ℕ) :
    deningerKappa f h t ^ n = deningerKappa f ((n : ℝ) • h) t := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, deningerKappa_smul, deningerKappa_smul]
    push_cast
    rw [← deningerKappa_add]
    congr 1
    ring

/-- A point of the fine generic source: a unitary character, a nonzero Kummer vector, and a
positive suspension height. -/
structure DeningerFinePoint (V : Type*) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  /-- The unitary character. -/
  chi : V → Circle
  /-- The Kummer vector. -/
  vec : H
  /-- The Kummer vector is nonzero: the point is nonunitary. -/
  vec_ne_zero : vec ≠ 0
  /-- The suspension height. -/
  susp : ℝ
  /-- The suspension height is positive. -/
  susp_pos : 0 < susp

theorem DeningerFinePoint.ext' {p q : DeningerFinePoint V H} (hchi : p.chi = q.chi)
    (hvec : p.vec = q.vec) (hsusp : p.susp = q.susp) : p = q := by
  obtain ⟨c₁, v₁, hv₁, u₁, hu₁⟩ := p
  obtain ⟨c₂, v₂, hv₂, u₂, hu₂⟩ := q
  simp only at hchi hvec hsusp
  subst hchi
  subst hvec
  subst hsusp
  rfl

/-- **The modulus Euler flow.**  It rescales the Kummer vector and fixes everything else. -/
noncomputable def deningerModulusFlow (s : ℝ) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H where
  chi := p.chi
  vec := Real.exp s • p.vec
  vec_ne_zero := smul_ne_zero (Real.exp_ne_zero s) p.vec_ne_zero
  susp := p.susp
  susp_pos := p.susp_pos

@[simp] theorem deningerModulusFlow_chi (s : ℝ) (p : DeningerFinePoint V H) :
    (deningerModulusFlow s p).chi = p.chi := rfl

@[simp] theorem deningerModulusFlow_vec (s : ℝ) (p : DeningerFinePoint V H) :
    (deningerModulusFlow s p).vec = Real.exp s • p.vec := rfl

@[simp] theorem deningerModulusFlow_susp (s : ℝ) (p : DeningerFinePoint V H) :
    (deningerModulusFlow s p).susp = p.susp := rfl

/-- **The Kummer–Kronecker phase flow.**  It twists the character by the unitary character
attached to the Kummer vector and fixes everything else. -/
noncomputable def deningerPhaseFlow (f : V → H) (t : ℝ) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H where
  chi := p.chi * deningerKappa f p.vec t
  vec := p.vec
  vec_ne_zero := p.vec_ne_zero
  susp := p.susp
  susp_pos := p.susp_pos

@[simp] theorem deningerPhaseFlow_chi (f : V → H) (t : ℝ) (p : DeningerFinePoint V H) :
    (deningerPhaseFlow f t p).chi = p.chi * deningerKappa f p.vec t := rfl

@[simp] theorem deningerPhaseFlow_vec (f : V → H) (t : ℝ) (p : DeningerFinePoint V H) :
    (deningerPhaseFlow f t p).vec = p.vec := rfl

@[simp] theorem deningerPhaseFlow_susp (f : V → H) (t : ℝ) (p : DeningerFinePoint V H) :
    (deningerPhaseFlow f t p).susp = p.susp := rfl

theorem deningerModulusFlow_zero (p : DeningerFinePoint V H) :
    deningerModulusFlow 0 p = p := by
  refine DeningerFinePoint.ext' rfl ?_ rfl
  simp

theorem deningerModulusFlow_add (s₁ s₂ : ℝ) (p : DeningerFinePoint V H) :
    deningerModulusFlow s₁ (deningerModulusFlow s₂ p) = deningerModulusFlow (s₁ + s₂) p := by
  refine DeningerFinePoint.ext' rfl ?_ rfl
  simp [smul_smul, Real.exp_add]

theorem deningerPhaseFlow_zero (f : V → H) (p : DeningerFinePoint V H) :
    deningerPhaseFlow f 0 p = p := by
  refine DeningerFinePoint.ext' ?_ rfl rfl
  simp

theorem deningerPhaseFlow_add (f : V → H) (t₁ t₂ : ℝ) (p : DeningerFinePoint V H) :
    deningerPhaseFlow f t₁ (deningerPhaseFlow f t₂ p) = deningerPhaseFlow f (t₁ + t₂) p := by
  refine DeningerFinePoint.ext' ?_ rfl rfl
  show p.chi * deningerKappa f p.vec t₂ * deningerKappa f p.vec t₁
      = p.chi * deningerKappa f p.vec (t₁ + t₂)
  rw [deningerKappa_add, mul_assoc]
  congr 1
  exact mul_comm _ _

/-- **The integrated bracket relation `[A, K] = K`.**  Conjugating the phase flow by the modulus
flow rescales its time parameter by `exp (-s)`, because rescaling the Kummer vector rescales the
phase character's time.  Hence the span of the two fields is involutive. -/
theorem deningerModulus_phase_conjugation (f : V → H) (s t : ℝ) (p : DeningerFinePoint V H) :
    deningerModulusFlow s (deningerPhaseFlow f t (deningerModulusFlow (-s) p))
      = deningerPhaseFlow f (Real.exp (-s) * t) p := by
  refine DeningerFinePoint.ext' ?_ ?_ rfl
  · show p.chi * deningerKappa f (Real.exp (-s) • p.vec) t
      = p.chi * deningerKappa f p.vec (Real.exp (-s) * t)
    rw [deningerKappa_smul]
  · show Real.exp s • Real.exp (-s) • p.vec = p.vec
    rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- **The phase flow moves through the modulus flow with a rescaled time.**  This is the same
relation as `deningerModulus_phase_conjugation`, in the form used to compose affine flows. -/
theorem deningerPhase_modulus_comm (f : V → H) (t s : ℝ) (p : DeningerFinePoint V H) :
    deningerPhaseFlow f t (deningerModulusFlow s p)
      = deningerModulusFlow s (deningerPhaseFlow f (Real.exp s * t) p) := by
  refine DeningerFinePoint.ext' ?_ rfl rfl
  show p.chi * deningerKappa f (Real.exp s • p.vec) t
      = p.chi * deningerKappa f p.vec (Real.exp s * t)
  rw [deningerKappa_smul]

/-- The two flows composed: the action of the affine group of the line. -/
noncomputable def deningerAffineFlow (f : V → H) (s t : ℝ) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H :=
  deningerModulusFlow s (deningerPhaseFlow f t p)

@[simp] theorem deningerAffineFlow_susp (f : V → H) (s t : ℝ) (p : DeningerFinePoint V H) :
    (deningerAffineFlow f s t p).susp = p.susp := rfl

theorem deningerAffineFlow_zero (f : V → H) (p : DeningerFinePoint V H) :
    deningerAffineFlow f 0 0 p = p := by
  rw [deningerAffineFlow, deningerPhaseFlow_zero, deningerModulusFlow_zero]

/-- **The two flows generate an action of the affine group of the line.**  This is the integrated
form of involutivity: the composite of two affine flows is again an affine flow. -/
theorem deningerAffineFlow_comp (f : V → H) (s₁ t₁ s₂ t₂ : ℝ) (p : DeningerFinePoint V H) :
    deningerAffineFlow f s₁ t₁ (deningerAffineFlow f s₂ t₂ p)
      = deningerAffineFlow f (s₁ + s₂) (Real.exp s₂ * t₁ + t₂) p := by
  rw [deningerAffineFlow, deningerAffineFlow, deningerAffineFlow, deningerPhase_modulus_comm,
    deningerModulusFlow_add, deningerPhaseFlow_add]

/-- The leaf through a point: the orbit of the affine action. -/
noncomputable def deningerAffineLeaf (f : V → H) (p : DeningerFinePoint V H) :
    Set (DeningerFinePoint V H) :=
  Set.range fun c : ℝ × ℝ => deningerAffineFlow f c.1 c.2 p

theorem deningerMem_affineLeaf_self (f : V → H) (p : DeningerFinePoint V H) :
    p ∈ deningerAffineLeaf f p :=
  ⟨(0, 0), deningerAffineFlow_zero f p⟩

/-- **The leaves are the orbits.**  A point of a leaf has the same leaf. -/
theorem deningerAffineLeaf_of_mem (f : V → H) {p q : DeningerFinePoint V H}
    (hq : q ∈ deningerAffineLeaf f p) : deningerAffineLeaf f q = deningerAffineLeaf f p := by
  obtain ⟨⟨s, t⟩, rfl⟩ := hq
  apply Set.eq_of_subset_of_subset
  · rintro r ⟨⟨s', t'⟩, rfl⟩
    exact ⟨(s' + s, Real.exp s * t' + t), (deningerAffineFlow_comp f s' t' s t p).symm⟩
  · rintro r ⟨⟨s', t'⟩, rfl⟩
    refine ⟨(s' - s, Real.exp (-s) * (t' - t)), ?_⟩
    have hs : (s' - s) + s = s' := by ring
    have ht : Real.exp s * (Real.exp (-s) * (t' - t)) + t = t' := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      ring
    show deningerAffineFlow f (s' - s) (Real.exp (-s) * (t' - t))
        (deningerAffineFlow f s t p) = deningerAffineFlow f s' t' p
    rw [deningerAffineFlow_comp, hs, ht]

/-- **The suspension height is constant on a leaf.** -/
theorem deningerAffineLeaf_susp (f : V → H) {p q : DeningerFinePoint V H}
    (hq : q ∈ deningerAffineLeaf f p) : q.susp = p.susp := by
  obtain ⟨⟨s, t⟩, rfl⟩ := hq
  rfl

/-- **Deninger's flow**: it changes only the suspension height. -/
noncomputable def deningerSuspFlow (τ : ℝ) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H where
  chi := p.chi
  vec := p.vec
  vec_ne_zero := p.vec_ne_zero
  susp := Real.exp τ * p.susp
  susp_pos := mul_pos (Real.exp_pos τ) p.susp_pos

@[simp] theorem deningerSuspFlow_susp (τ : ℝ) (p : DeningerFinePoint V H) :
    (deningerSuspFlow τ p).susp = Real.exp τ * p.susp := rfl

theorem deningerSuspFlow_modulus_comm (s τ : ℝ) (p : DeningerFinePoint V H) :
    deningerSuspFlow τ (deningerModulusFlow s p) = deningerModulusFlow s (deningerSuspFlow τ p) :=
  DeningerFinePoint.ext' rfl rfl rfl

theorem deningerSuspFlow_phase_comm (f : V → H) (t τ : ℝ) (p : DeningerFinePoint V H) :
    deningerSuspFlow τ (deningerPhaseFlow f t p) = deningerPhaseFlow f t (deningerSuspFlow τ p) :=
  DeningerFinePoint.ext' rfl rfl rfl

/-- **Deninger's flow is transverse to the leaves.**  The suspension height is a leafwise
invariant, and the flow moves it, so no nontrivial flow time stays on the leaf. -/
theorem deningerSuspFlow_mem_leaf_iff (f : V → H) (τ : ℝ) (p : DeningerFinePoint V H) :
    deningerSuspFlow τ p ∈ deningerAffineLeaf f p ↔ τ = 0 := by
  constructor
  · intro hmem
    have h := deningerAffineLeaf_susp f hmem
    rw [deningerSuspFlow_susp] at h
    have hne : p.susp ≠ 0 := ne_of_gt p.susp_pos
    have h1 : Real.exp τ = 1 := by
      have hcancel : Real.exp τ * p.susp = 1 * p.susp := by rw [one_mul]; exact h
      exact mul_right_cancel₀ hne hcancel
    exact (Real.exp_eq_one_iff τ).mp h1
  · rintro rfl
    have : deningerSuspFlow 0 p = p := by
      refine DeningerFinePoint.ext' rfl rfl ?_
      rw [deningerSuspFlow_susp, Real.exp_zero, one_mul]
    rw [this]
    exact deningerMem_affineLeaf_self f p

end AffineLeaf

end RHTower
