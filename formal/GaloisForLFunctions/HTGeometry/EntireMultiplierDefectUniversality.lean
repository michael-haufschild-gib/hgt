import Mathlib
import GaloisForLFunctions.HTGeometry.EntireBezout

/-!
# Entire multiplier defects are divisor-universal

For a nonzero entire `F` the two-term multiplier complex `[A --F--> A]` on the ring `A` of entire
functions has the single cohomology `A / F·A`.  Its content is exactly the divisor of `F`:
an entire function lies in `F·A` precisely when its analytic order dominates that of `F` at every
point.  Multiplication by the nowhere-zero unit `exp(-i a z)` commutes with `F`, hence descends to
the defect module, and at a point `ρ` it differs from the scalar `exp(-i a ρ)` by a factor
vanishing at `ρ` — so on the local fibre the real translation acts by that character times a
unipotent operator.

None of this restricts the divisor: the real entire function `z² + 1` carries the same structure
with a nonreal zero pair.  What does restrict it is positivity.  An invariant Hermitian form on the
semisimple defect core can pair two local fibres only when their points are complex conjugates, so
its diagonal vanishes at every nonreal point; a faithful positive invariant form therefore exists
exactly when the divisor is real.
-/

namespace GaloisForLFunctions.HTGeometry.EntireDefect

open Complex Set

noncomputable section

theorem entire_analyticAt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) : AnalyticAt ℂ f z :=
  hf.differentiableOn.analyticAt Filter.univ_mem

/-- The real-translation multiplier `z ↦ exp(-i a z)` acting on entire functions. -/
noncomputable def translationMultiplier (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (a : ℂ) * z)

/-- The character by which a real translation acts on the local fibre at `ρ`. -/
noncomputable def defectCharacter (ρ : ℂ) (a : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (a : ℂ) * ρ)

@[simp]
theorem translationMultiplier_apply (a : ℝ) (ρ : ℂ) :
    translationMultiplier a ρ = defectCharacter ρ a := rfl

theorem differentiable_translationMultiplier (a : ℝ) :
    Differentiable ℂ (translationMultiplier a) := by
  unfold translationMultiplier
  exact (differentiable_id.const_mul _).cexp

theorem translationMultiplier_ne_zero (a : ℝ) (z : ℂ) : translationMultiplier a z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem translationMultiplier_zero (z : ℂ) : translationMultiplier 0 z = 1 := by
  simp [translationMultiplier]

theorem translationMultiplier_add (a b : ℝ) (z : ℂ) :
    translationMultiplier (a + b) z = translationMultiplier a z * translationMultiplier b z := by
  unfold translationMultiplier
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The modulus of the translation character. -/
theorem norm_defectCharacter (ρ : ℂ) (a : ℝ) :
    ‖defectCharacter ρ a‖ = Real.exp (a * ρ.im) := by
  unfold defectCharacter
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **The translation character is unitary exactly at a real point.** -/
theorem norm_defectCharacter_eq_one_iff (ρ : ℂ) :
    (∀ a : ℝ, ‖defectCharacter ρ a‖ = 1) ↔ ρ.im = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [norm_defectCharacter] at h1
    have h2 : (1 : ℝ) * ρ.im = 0 := (Real.exp_eq_one_iff _).mp h1
    simpa using h2
  · intro h a
    rw [norm_defectCharacter, h, mul_zero, Real.exp_zero]

/-- A single nonzero real translation already detects reality of the point. -/
theorem norm_defectCharacter_eq_one_iff_of_ne_zero {a : ℝ} (ha : a ≠ 0) (ρ : ℂ) :
    ‖defectCharacter ρ a‖ = 1 ↔ ρ.im = 0 := by
  rw [norm_defectCharacter]
  constructor
  · intro h
    have h2 : a * ρ.im = 0 := (Real.exp_eq_one_iff _).mp h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ha
    · exact h3
  · intro h
    rw [h, mul_zero, Real.exp_zero]

/-- **Divisor recovery.**  An entire function lies in the multiplier ideal of a nonzero entire `F`
exactly when its analytic order dominates that of `F` at every point.  The defect module
`A / F·A` therefore sees exactly the complete divisor of `F`, with multiplicity. -/
theorem mem_multiplierIdeal_iff {F g : ℂ → ℂ} (hF : Differentiable ℂ F) (hg : Differentiable ℂ g)
    (hF0 : ∃ z₀, F z₀ ≠ 0) :
    (∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = q z * F z)
      ↔ ∀ z, analyticOrderAt F z ≤ analyticOrderAt g z := by
  constructor
  · rintro ⟨q, hq, hqg⟩ z
    have hcongr : analyticOrderAt g z = analyticOrderAt (q * F) z :=
      analyticOrderAt_congr (Filter.Eventually.of_forall hqg)
    rw [hcongr, analyticOrderAt_mul (entire_analyticAt hq z) (entire_analyticAt hF z)]
    exact le_add_self
  · intro hord
    exact exists_entire_quotient hg hF hF0 hord

/-- Multiplying by the nowhere-zero translation multiplier changes no analytic order. -/
theorem analyticOrderAt_translationMultiplier_mul (a : ℝ) (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (z : ℂ) :
    analyticOrderAt (fun w => translationMultiplier a w * g w) z = analyticOrderAt g z := by
  have hmul : analyticOrderAt ((translationMultiplier a) * g) z
      = analyticOrderAt (translationMultiplier a) z + analyticOrderAt g z :=
    analyticOrderAt_mul (entire_analyticAt (differentiable_translationMultiplier a) z)
      (entire_analyticAt hg z)
  have hzero : analyticOrderAt (translationMultiplier a) z = 0 :=
    (entire_analyticAt (differentiable_translationMultiplier a) z).analyticOrderAt_eq_zero.mpr
      (translationMultiplier_ne_zero a z)
  calc analyticOrderAt (fun w => translationMultiplier a w * g w) z
      = analyticOrderAt ((translationMultiplier a) * g) z := rfl
    _ = analyticOrderAt (translationMultiplier a) z + analyticOrderAt g z := hmul
    _ = analyticOrderAt g z := by rw [hzero, zero_add]

/-- **The translation action preserves the multiplier ideal**, hence descends to the defect
module `A / F·A`. -/
theorem translation_mem_multiplierIdeal_iff {F g : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hg : Differentiable ℂ g) (hF0 : ∃ z₀, F z₀ ≠ 0) (a : ℝ) :
    (∃ q : ℂ → ℂ, Differentiable ℂ q ∧
        ∀ z, translationMultiplier a z * g z = q z * F z)
      ↔ (∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = q z * F z) := by
  have hmul : Differentiable ℂ (fun z => translationMultiplier a z * g z) :=
    (differentiable_translationMultiplier a).mul hg
  rw [mem_multiplierIdeal_iff hF hmul hF0, mem_multiplierIdeal_iff hF hg hF0]
  constructor
  · intro h z
    rw [← analyticOrderAt_translationMultiplier_mul a g hg z]
    exact h z
  · intro h z
    rw [analyticOrderAt_translationMultiplier_mul a g hg z]
    exact h z

theorem analyticOrderAt_sub_const_self (ρ : ℂ) :
    analyticOrderAt (fun w : ℂ => w - ρ) ρ = 1 := by
  have hf : AnalyticAt ℂ (fun w : ℂ => w - ρ) ρ := analyticAt_id.sub analyticAt_const
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, hf.analyticOrderAt_eq_natCast]
  refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall (fun z => ?_)⟩
  simp

/-- **The local character.**  At a point `ρ` the translation multiplier differs from its character
value by a factor vanishing at `ρ`, so on the local fibre the action is the character times a
unipotent operator. -/
theorem translationMultiplier_sub_character (a : ℝ) (ρ : ℂ) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧
      ∀ z, translationMultiplier a z - defectCharacter ρ a = u z * (z - ρ) := by
  have hf : Differentiable ℂ (fun z => translationMultiplier a z - defectCharacter ρ a) :=
    (differentiable_translationMultiplier a).sub_const _
  have hg : Differentiable ℂ (fun z : ℂ => z - ρ) := differentiable_id.sub_const _
  have hg0 : ∃ z₀ : ℂ, (fun z : ℂ => z - ρ) z₀ ≠ 0 := ⟨ρ + 1, by simp⟩
  refine exists_entire_quotient hf hg hg0 (fun z => ?_)
  rcases eq_or_ne z ρ with rfl | hz
  · rw [analyticOrderAt_sub_const_self]
    refine Order.one_le_iff_ne_zero.mpr ?_
    refine (entire_analyticAt hf _).analyticOrderAt_ne_zero.mpr ?_
    simp
  · have hne : (fun w : ℂ => w - ρ) z ≠ 0 := sub_ne_zero.mpr hz
    rw [(entire_analyticAt hg z).analyticOrderAt_eq_zero.mpr hne]
    exact bot_le

end

end GaloisForLFunctions.HTGeometry.EntireDefect

namespace GaloisForLFunctions.HTGeometry.EntireDefect

open Complex Matrix

noncomputable section

theorem conj_defectCharacter (ρ : ℂ) (a : ℝ) :
    (starRingEnd ℂ) (defectCharacter ρ a)
      = Complex.exp (Complex.I * (a : ℂ) * (starRingEnd ℂ) ρ) := by
  unfold defectCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

theorem conj_defectCharacter_mul (ρ σ : ℂ) (a : ℝ) :
    (starRingEnd ℂ) (defectCharacter ρ a) * defectCharacter σ a
      = Complex.exp (Complex.I * (a : ℂ) * ((starRingEnd ℂ) ρ - σ)) := by
  rw [conj_defectCharacter, defectCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- A nonzero displacement cannot give the trivial character for every real translation. -/
theorem not_forall_exp_eq_one {w : ℂ} (hw : w ≠ 0) :
    ¬ (∀ a : ℝ, Complex.exp (Complex.I * (a : ℂ) * w) = 1) := by
  intro h
  have hre : w.im = 0 := by
    have h1 : ‖Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * w)‖ = 1 := by rw [h 1]; simp
    rw [Complex.norm_exp] at h1
    have h2 : (Complex.I * ((1 : ℝ) : ℂ) * w).re = 0 := (Real.exp_eq_one_iff _).mp h1
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h2
    linarith [h2]
  obtain ⟨t, ht0, hwt⟩ : ∃ t : ℝ, t ≠ 0 ∧ w = (t : ℂ) := by
    refine ⟨w.re, ?_, ?_⟩
    · intro h0
      exact hw (Complex.ext (by simpa using h0) (by simpa using hre))
    · exact Complex.ext (by simp) (by simpa using hre)
  subst hwt
  have hkey := h (Real.pi / t)
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
  have hval : Complex.I * ((Real.pi / t : ℝ) : ℂ) * ((t : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hval, Complex.exp_pi_mul_I] at hkey
  norm_num at hkey

/-- Invariance of a Hermitian coefficient matrix under the real-translation character action on
the semisimple defect core. -/
def CharacterInvariant {ι : Type*} (Z : ι → ℂ) (H : Matrix ι ι ℂ) : Prop :=
  ∀ (a : ℝ) (i j : ι),
    (starRingEnd ℂ) (defectCharacter (Z i) a) * defectCharacter (Z j) a * H i j = H i j

/-- **Support law for invariant forms.**  An invariant coefficient between two local fibres can be
nonzero only when the two points are complex conjugates. -/
theorem characterInvariant_eq_zero_of_ne_conj {ι : Type*} (Z : ι → ℂ) (H : Matrix ι ι ℂ)
    (hinv : CharacterInvariant Z H) (i j : ι) (hij : (starRingEnd ℂ) (Z i) ≠ Z j) :
    H i j = 0 := by
  by_contra hne
  refine not_forall_exp_eq_one (sub_ne_zero.mpr hij) (fun a => ?_)
  have h := hinv a i j
  rw [conj_defectCharacter_mul] at h
  have := mul_right_cancel₀ hne (h.trans (one_mul (H i j)).symm)
  exact this

end

end GaloisForLFunctions.HTGeometry.EntireDefect

namespace GaloisForLFunctions.HTGeometry.EntireDefect

open Complex Matrix

noncomputable section

theorem conj_defectCharacter_mul_self_of_real {ρ : ℂ} (h : ρ.im = 0) (a : ℝ) :
    (starRingEnd ℂ) (defectCharacter ρ a) * defectCharacter ρ a = 1 := by
  rw [conj_defectCharacter_mul]
  have hz : (starRingEnd ℂ) ρ - ρ = 0 := by
    apply Complex.ext <;> simp [h]
  rw [hz, mul_zero, Complex.exp_zero]

/-- A faithful positive translation-invariant Hermitian form on the semisimple defect core. -/
structure PositiveInvariantForm {ι : Type*} [Fintype ι] (Z : ι → ℂ) where
  /-- The coefficient matrix of the form in the local-fibre basis. -/
  coeff : Matrix ι ι ℂ
  /-- Invariance under the real-translation character action. -/
  invariant : CharacterInvariant Z coeff
  /-- Hermitian symmetry. -/
  hermitian : coeff.IsHermitian
  /-- Faithful positivity. -/
  positive : ∀ x : ι → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (coeff *ᵥ x)).re

/-- The conjugate-pair block `[[0, c], [conj c, 0]]` is never faithfully positive: the first basis
vector is a null vector. -/
theorem conjPairBlock_not_positive (c : ℂ) :
    ¬ ∀ x : Fin 2 → ℂ, x ≠ 0 →
      0 < (star x ⬝ᵥ ((!![0, c; (starRingEnd ℂ) c, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x)).re := by
  intro h
  have hx : (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have := h _ hx
  simp [Matrix.mulVec, dotProduct] at this

/-- **Classification of faithful positive invariant semisimplifications.**  Such a form exists on
the semisimple defect core exactly when every point of the divisor is real. -/
theorem nonempty_positiveInvariantForm_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : ι → ℂ) :
    Nonempty (PositiveInvariantForm Z) ↔ ∀ i, (Z i).im = 0 := by
  constructor
  · rintro ⟨f⟩ i
    have hx : (Pi.single i 1 : ι → ℂ) ≠ 0 := by
      intro h0
      have := congrFun h0 i
      simp at this
    have hval := f.positive (Pi.single i 1 : ι → ℂ) hx
    have hcalc : star (Pi.single i 1 : ι → ℂ) ⬝ᵥ (f.coeff *ᵥ (Pi.single i 1 : ι → ℂ))
        = f.coeff i i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', mul_comm]
    rw [hcalc] at hval
    have hne : f.coeff i i ≠ 0 := by
      intro h0
      rw [h0] at hval
      simp at hval
    have hinv := f.invariant 1 i i
    have hnorm : ‖(starRingEnd ℂ) (defectCharacter (Z i) 1) * defectCharacter (Z i) 1‖ *
        ‖f.coeff i i‖ = ‖f.coeff i i‖ := by
      rw [← norm_mul, hinv]
    have hnn : ‖f.coeff i i‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have hone : ‖(starRingEnd ℂ) (defectCharacter (Z i) 1) * defectCharacter (Z i) 1‖ = 1 :=
      mul_right_cancel₀ hnn (hnorm.trans (one_mul (‖f.coeff i i‖)).symm)
    rw [norm_mul, RCLike.norm_conj] at hone
    have hchar : ‖defectCharacter (Z i) 1‖ = 1 := by
      nlinarith [norm_nonneg (defectCharacter (Z i) 1), hone]
    exact (norm_defectCharacter_eq_one_iff_of_ne_zero one_ne_zero (Z i)).mp hchar
  · intro hreal
    refine ⟨⟨1, ?_, Matrix.isHermitian_one, ?_⟩⟩
    · intro a i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_one, conj_defectCharacter_mul_self_of_real (hreal i)]
      · rw [Matrix.one_apply_ne hij, mul_zero]
    · intro x hx
      have hcalc : star x ⬝ᵥ ((1 : Matrix ι ι ℂ) *ᵥ x) = ∑ k, (starRingEnd ℂ) (x k) * x k := by
        simp [dotProduct]
      rw [hcalc]
      have hre : (∑ k, (starRingEnd ℂ) (x k) * x k).re = ∑ k, ‖x k‖ ^ (2 : ℕ) := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [mul_comm, Complex.mul_conj]
        simp [Complex.normSq_eq_norm_sq]
        norm_cast
      rw [hre]
      obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx (funext hcon)
      refine Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ k, ?_⟩
      have : 0 < ‖x k‖ := norm_pos_iff.mpr hk
      positivity

end

end GaloisForLFunctions.HTGeometry.EntireDefect

namespace GaloisForLFunctions.HTGeometry.EntireDefect

open Complex Matrix

noncomputable section

/-- **Universality witness.**  A real entire function with a nonreal zero.  Every structure built
above — the multiplier complex, the divisor recovery, the real-translation action and its
characters — applies verbatim to it, so none of those structures can force a real divisor. -/
theorem exists_realEntire_nonreal_zero :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z : ℂ, (starRingEnd ℂ) (F ((starRingEnd ℂ) z)) = F z) ∧
      (∃ z₀, F z₀ ≠ 0) ∧ (∃ ρ, F ρ = 0 ∧ ρ.im ≠ 0) := by
  refine ⟨fun z => z ^ (2 : ℕ) + 1, (differentiable_id.pow 2).add_const 1, ?_, ⟨0, by norm_num⟩,
    ⟨Complex.I, by simp [Complex.I_sq], by simp⟩⟩
  intro z
  simp [map_add, map_pow]

/-- The conjugate zero pair of the universality witness admits no faithful positive invariant
form: the divisor-universal structures are strictly weaker than reality of the divisor. -/
theorem not_nonempty_positiveInvariantForm_conjPair :
    ¬ Nonempty (PositiveInvariantForm ![Complex.I, -Complex.I]) := by
  intro h
  have := (nonempty_positiveInvariantForm_iff ![Complex.I, -Complex.I]).mp h 0
  simp at this

end

end GaloisForLFunctions.HTGeometry.EntireDefect
