import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Real.Basic

/-!
# Rank is the only invariant of a quadratic form over a quadratically closed field

Over a field in which every element is a square and two is invertible, a nondegenerate quadratic
form on a finite-dimensional space is isometric to the standard sum of squares of its rank.  Rank
is therefore a complete isometry invariant, orthogonal sum adds ranks, and the monoid of isometry
classes of nondegenerate forms is the additive monoid of natural numbers.

Group-completing that monoid gives the Grothendieck--Witt group: the rank map is the universal
additive map from isometry classes to an abelian group, so the Grothendieck--Witt group of a
quadratically closed field is the integers with rank as the isomorphism.

The nondegeneracy statements are all phrased through the polar form, which avoids the inverse of
two living in the endomorphism ring of the target.

* `deningerSeparatingLeft_iff_polar` : nondegeneracy through the polar form.
* `deningerWeightedSumSquares_separatingLeft` : a weighted sum of squares with nonzero weights is
  nondegenerate.
* `deningerEquivalent_standardForm` : every nondegenerate form is the standard form of its rank.
* `deningerEquivalent_iff_finrank_eq` : rank is a complete isometry invariant.
* `deningerStandardForm_sum` : orthogonal sum adds ranks.
* `deningerClassRank_bijective` : isometry classes are the natural numbers.
* `deningerGrothendieckWittRank_universal` : rank is the universal additive invariant, so the
  Grothendieck--Witt group is the integers.
* `deningerRealificationCongr`, `deningerTorsionQuotientCongr` : an isomorphism survives
  realification and the quotient by torsion.
-/

namespace RHTower

open QuadraticMap QuadraticForm

section PolarSeparating

variable {K : Type*} [Field K] [Invertible (2 : K)]

theorem deningerTwo_ne_zero : (2 : K) ≠ 0 := by
  intro hz
  have h1 : (⅟(2 : K)) * (2 : K) = 1 := invOf_mul_self 2
  have h2 : (⅟(2 : K)) * (0 : K) = 1 := by rw [← hz]; exact h1
  rw [mul_zero] at h2
  exact zero_ne_one h2

variable {M : Type*} [AddCommGroup M] [Module K M]

/-- Twice the associated bilinear form is the polar form. -/
theorem deningerTwo_nsmul_associated (Q : QuadraticForm K M) (x y : M) :
    (2 : ℕ) • (QuadraticMap.associated Q x y) = QuadraticMap.polar (⇑Q) x y := by
  have h := congrArg (fun B : LinearMap.BilinMap K M K => B x y)
    (QuadraticMap.two_nsmul_associated (S := K) (Q := Q))
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply] at h
  exact h

/-- **Nondegeneracy through the polar form.**  Two is invertible, so the associated bilinear form
and the polar form have the same left kernel. -/
theorem deningerSeparatingLeft_iff_polar (Q : QuadraticForm K M) :
    (QuadraticMap.associated Q).SeparatingLeft
      ↔ ∀ x : M, (∀ y, QuadraticMap.polar (⇑Q) x y = 0) → x = 0 := by
  have hcancel : ∀ a : K, (2 : ℕ) • a = 0 ↔ a = 0 := by
    intro a
    rw [nsmul_eq_mul, Nat.cast_ofNat, mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h deningerTwo_ne_zero
      · exact h
    · intro h
      exact Or.inr h
  constructor
  · intro hsep x hx
    refine hsep x fun y => ?_
    exact (hcancel _).mp (by rw [deningerTwo_nsmul_associated, hx y])
  · intro hpol x hx
    refine hpol x fun y => ?_
    rw [← deningerTwo_nsmul_associated, hx y, smul_zero]

omit [Invertible (2 : K)] in
theorem deningerPolar_comp {M' : Type*} [AddCommGroup M'] [Module K M']
    (Q : QuadraticForm K M) (f : M' →ₗ[K] M) (x y : M') :
    QuadraticMap.polar (⇑(Q.comp f)) x y = QuadraticMap.polar (⇑Q) (f x) (f y) := by
  show Q (f (x + y)) - Q (f x) - Q (f y) = Q (f x + f y) - Q (f x) - Q (f y)
  rw [map_add]

/-- **Nondegeneracy is an isometry invariant.** -/
theorem deningerSeparatingLeft_of_equivalent {M' : Type*} [AddCommGroup M'] [Module K M']
    {Q : QuadraticForm K M} {Q' : QuadraticForm K M'} (h : Q.Equivalent Q')
    (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    (QuadraticMap.associated Q').SeparatingLeft := by
  obtain ⟨e⟩ := h
  rw [deningerSeparatingLeft_iff_polar] at hQ ⊢
  intro x hx
  have hQeq : Q = Q'.comp (e.toLinearEquiv : M →ₗ[K] M') :=
    QuadraticMap.ext fun a => (e.map_app a).symm
  have hpolarQ : ∀ a b : M, QuadraticMap.polar (⇑Q) a b
      = QuadraticMap.polar (⇑Q') (e.toLinearEquiv a) (e.toLinearEquiv b) := by
    intro a b
    have h1 : QuadraticMap.polar (⇑Q) a b
        = QuadraticMap.polar (⇑(Q'.comp (e.toLinearEquiv : M →ₗ[K] M'))) a b := by
      rw [← hQeq]
    rw [h1, deningerPolar_comp]
    rfl
  have hkey : ∀ z : M, QuadraticMap.polar (⇑Q) (e.toLinearEquiv.symm x) z = 0 := by
    intro z
    rw [hpolarQ, LinearEquiv.apply_symm_apply]
    exact hx _
  have h0 := hQ _ hkey
  have hfin := congrArg (e.toLinearEquiv : M →ₗ[K] M') h0
  rw [map_zero] at hfin
  show x = 0
  rw [← hfin]
  exact (LinearEquiv.apply_symm_apply e.toLinearEquiv x).symm

end PolarSeparating

section WeightedSumSquares

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A weighted sum of squares with nonzero weights is nondegenerate.** -/
theorem deningerWeightedSumSquares_separatingLeft (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    (QuadraticMap.associated (weightedSumSquares K w)).SeparatingLeft := by
  rw [deningerSeparatingLeft_iff_polar]
  intro x hx
  funext i
  show x i = 0
  set e : ι → K := Pi.single i 1 with hedef
  have hei : e i = 1 := by rw [hedef]; exact Pi.single_eq_same i 1
  have hej : ∀ j, j ≠ i → e j = 0 := by
    intro j hj
    rw [hedef]
    exact Pi.single_eq_of_ne hj 1
  have h2 : weightedSumSquares K w (x + e) - weightedSumSquares K w x
      - weightedSumSquares K w e = 0 := hx e
  simp only [weightedSumSquares_apply, smul_eq_mul, Pi.add_apply] at h2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at h2
  have hterm : ∀ j : ι, w j * ((x j + e j) * (x j + e j))
      - w j * (x j * x j) - w j * (e j * e j) = 2 * w j * x j * e j := by
    intro j; ring
  simp only [hterm] at h2
  rw [Finset.sum_eq_single i] at h2
  · rw [hei, mul_one] at h2
    rcases mul_eq_zero.mp h2 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 deningerTwo_ne_zero
      · exact absurd h5 (hw i)
    · exact h4
  · intro j _ hj
    rw [hej j hj, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

end WeightedSumSquares

section QuadraticallyClosed

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

/-- The isometry between a weighted sum of squares over a field in which every element is a square
and the sum of squares with weights one or zero. -/
noncomputable def deningerIsometryEquivSumSquares [DecidableEq K]
    (hsq : ∀ x : K, ∃ y : K, x = y * y) (w : ι → K) :
    IsometryEquiv (weightedSumSquares K w)
      (weightedSumSquares K (fun i => if w i = 0 then 0 else 1 : ι → K)) := by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (hsq (w i)).choose (by
      rw [← mul_self_eq_zero.ne, ← (hsq (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_ifs with h <;>
    simp [h, pow_two, ← (hsq (w i)).choose_spec]

/-- The isometry between a weighted sum of squares with unit weights over a field in which every
element is a square and the standard sum of squares. -/
noncomputable def deningerIsometryEquivSumSquaresUnits [DecidableEq K]
    (hsq : ∀ x : K, ∃ y : K, x = y * y) (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K w) (weightedSumSquares K (1 : ι → K)) :=
  (deningerIsometryEquivSumSquares hsq (fun i ↦ (w i).val)).trans
    (weightedSumSquaresCongr (by ext; simp))

end QuadraticallyClosed

section StandardForm

variable (K : Type*) [Field K]

/-- The standard rank-`n` form, the sum of `n` squares. -/
noncomputable def deningerStandardForm (n : ℕ) : QuadraticForm K (Fin n → K) :=
  weightedSumSquares K (1 : Fin n → K)

variable {K}

theorem deningerStandardForm_apply (n : ℕ) (x : Fin n → K) :
    deningerStandardForm K n x = ∑ i, x i * x i := by
  rw [deningerStandardForm, weightedSumSquares_apply]
  exact Finset.sum_congr rfl fun i _ => one_smul _ _

variable [Invertible (2 : K)]

/-- **The standard form is nondegenerate.** -/
theorem deningerStandardForm_separatingLeft (n : ℕ) :
    (QuadraticMap.associated (deningerStandardForm K n)).SeparatingLeft :=
  deningerWeightedSumSquares_separatingLeft _ fun _ => one_ne_zero

omit [Invertible (2 : K)] in
theorem deningerFinrank_eq_of_equivalent {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁]
    [AddCommGroup M₂] [Module K M₂] {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (h : Q₁.Equivalent Q₂) : Module.finrank K M₁ = Module.finrank K M₂ := by
  obtain ⟨e⟩ := h
  exact e.toLinearEquiv.finrank_eq

/-- **Every nondegenerate form is the standard form of its rank.** -/
theorem deningerEquivalent_standardForm (hsq : ∀ x : K, ∃ y : K, x = y * y)
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) (hQ : (QuadraticMap.associated Q).SeparatingLeft) :
    Q.Equivalent (deningerStandardForm K (Module.finrank K M)) := by
  classical
  obtain ⟨w, ⟨hw⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  exact ⟨hw.trans (deningerIsometryEquivSumSquaresUnits hsq w)⟩

/-- **Rank is a complete isometry invariant** over a quadratically closed field. -/
theorem deningerEquivalent_iff_finrank_eq (hsq : ∀ x : K, ∃ y : K, x = y * y)
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module K M₁] [FiniteDimensional K M₁]
    [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (Q₁ : QuadraticForm K M₁) (Q₂ : QuadraticForm K M₂)
    (h₁ : (QuadraticMap.associated Q₁).SeparatingLeft)
    (h₂ : (QuadraticMap.associated Q₂).SeparatingLeft) :
    Q₁.Equivalent Q₂ ↔ Module.finrank K M₁ = Module.finrank K M₂ := by
  constructor
  · exact deningerFinrank_eq_of_equivalent
  · intro hrank
    refine (deningerEquivalent_standardForm hsq Q₁ h₁).trans ?_
    rw [hrank]
    exact (deningerEquivalent_standardForm hsq Q₂ h₂).symm

end StandardForm

section OrthogonalSum

variable (K : Type*) [Field K] (m n : ℕ)

/-- Splitting a coordinate vector into its first `m` and last `n` coordinates. -/
def deningerSplit : (Fin (m + n) → K) ≃ₗ[K] (Fin m → K) × (Fin n → K) :=
  (LinearEquiv.funCongrLeft K K finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) K K)

variable {K m n}

@[simp]
theorem deningerSplit_fst (x : Fin (m + n) → K) (i : Fin m) :
    (deningerSplit K m n x).1 i = x (Fin.castAdd n i) := by
  show x (finSumFinEquiv (Sum.inl i)) = x (Fin.castAdd n i)
  rw [finSumFinEquiv_apply_left]

@[simp]
theorem deningerSplit_snd (x : Fin (m + n) → K) (j : Fin n) :
    (deningerSplit K m n x).2 j = x (Fin.natAdd m j) := by
  show x (finSumFinEquiv (Sum.inr j)) = x (Fin.natAdd m j)
  rw [finSumFinEquiv_apply_right]

/-- The orthogonal sum of two forms in the standard coordinate model. -/
def deningerFormPlus {m n : ℕ} (Q₁ : QuadraticForm K (Fin m → K))
    (Q₂ : QuadraticForm K (Fin n → K)) : QuadraticForm K (Fin (m + n) → K) :=
  (Q₁.prod Q₂).comp (deningerSplit K m n).toLinearMap

theorem deningerFormPlus_apply {m n : ℕ} (Q₁ : QuadraticForm K (Fin m → K))
    (Q₂ : QuadraticForm K (Fin n → K)) (x : Fin (m + n) → K) :
    deningerFormPlus Q₁ Q₂ x = Q₁ (deningerSplit K m n x).1 + Q₂ (deningerSplit K m n x).2 :=
  QuadraticMap.prod_apply _ _ _

/-- The orthogonal sum is isometric to the product form. -/
def deningerFormPlus_isometry {m n : ℕ} (Q₁ : QuadraticForm K (Fin m → K))
    (Q₂ : QuadraticForm K (Fin n → K)) :
    IsometryEquiv (deningerFormPlus Q₁ Q₂) (Q₁.prod Q₂) where
  toLinearEquiv := deningerSplit K m n
  map_app' _ := rfl

/-- **Orthogonal sum adds ranks**: the sum of the standard forms of ranks `m` and `n` is the
standard form of rank `m + n`. -/
theorem deningerStandardForm_sum (m n : ℕ) :
    deningerFormPlus (deningerStandardForm K m) (deningerStandardForm K n)
      = deningerStandardForm K (m + n) := by
  refine QuadraticMap.ext fun x => ?_
  rw [deningerFormPlus_apply, deningerStandardForm_apply, deningerStandardForm_apply,
    deningerStandardForm_apply, Fin.sum_univ_add]
  congr 1

variable [Invertible (2 : K)]

/-- **The orthogonal sum of nondegenerate forms is nondegenerate.** -/
theorem deningerFormPlus_separatingLeft {m n : ℕ} {Q₁ : QuadraticForm K (Fin m → K)}
    {Q₂ : QuadraticForm K (Fin n → K)}
    (h₁ : (QuadraticMap.associated Q₁).SeparatingLeft)
    (h₂ : (QuadraticMap.associated Q₂).SeparatingLeft) :
    (QuadraticMap.associated (deningerFormPlus Q₁ Q₂)).SeparatingLeft := by
  rw [deningerSeparatingLeft_iff_polar] at h₁ h₂ ⊢
  intro x hx
  have hsplit : ∀ y : Fin (m + n) → K,
      QuadraticMap.polar (⇑(Q₁.prod Q₂)) (deningerSplit K m n x) (deningerSplit K m n y) = 0 := by
    intro y
    show QuadraticMap.polar (⇑(Q₁.prod Q₂))
      ((deningerSplit K m n).toLinearMap x) ((deningerSplit K m n).toLinearMap y) = 0
    rw [← deningerPolar_comp]
    exact hx y
  have hprod : ∀ p : (Fin m → K) × (Fin n → K),
      QuadraticMap.polar (⇑(Q₁.prod Q₂)) (deningerSplit K m n x) p = 0 := by
    intro p
    have := hsplit ((deningerSplit K m n).symm p)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hpolarprod : ∀ (a : (Fin m → K) × (Fin n → K)) (b : (Fin m → K) × (Fin n → K)),
      QuadraticMap.polar (⇑(Q₁.prod Q₂)) a b
        = QuadraticMap.polar (⇑Q₁) a.1 b.1 + QuadraticMap.polar (⇑Q₂) a.2 b.2 := by
    intro a b
    show (Q₁.prod Q₂) (a + b) - (Q₁.prod Q₂) a - (Q₁.prod Q₂) b
      = (Q₁ (a.1 + b.1) - Q₁ a.1 - Q₁ b.1) + (Q₂ (a.2 + b.2) - Q₂ a.2 - Q₂ b.2)
    rw [QuadraticMap.prod_apply, QuadraticMap.prod_apply, QuadraticMap.prod_apply]
    show Q₁ (a.1 + b.1) + Q₂ (a.2 + b.2) - (Q₁ a.1 + Q₂ a.2) - (Q₁ b.1 + Q₂ b.2)
      = (Q₁ (a.1 + b.1) - Q₁ a.1 - Q₁ b.1) + (Q₂ (a.2 + b.2) - Q₂ a.2 - Q₂ b.2)
    ring
  have hfst : (deningerSplit K m n x).1 = 0 := by
    refine h₁ _ fun c => ?_
    have h := hprod (c, 0)
    rw [hpolarprod] at h
    have hz : QuadraticMap.polar (⇑Q₂) (deningerSplit K m n x).2 (0 : Fin n → K) = 0 :=
      QuadraticMap.polar_zero_right Q₂ _
    rw [hz, add_zero] at h
    exact h
  have hsnd : (deningerSplit K m n x).2 = 0 := by
    refine h₂ _ fun d => ?_
    have h := hprod (0, d)
    rw [hpolarprod] at h
    have hz : QuadraticMap.polar (⇑Q₁) (deningerSplit K m n x).1 (0 : Fin m → K) = 0 :=
      QuadraticMap.polar_zero_right Q₁ _
    rw [hz, zero_add] at h
    exact h
  have hzero : deningerSplit K m n x = 0 := Prod.ext hfst hsnd
  have := congrArg (deningerSplit K m n).symm hzero
  rwa [LinearEquiv.symm_apply_apply, map_zero] at this

end OrthogonalSum

section WittClasses

variable (K : Type*) [Field K] [Invertible (2 : K)]

/-- A nondegenerate quadratic form in the standard coordinate model, together with its rank. -/
structure DeningerForm where
  /-- The rank of the form. -/
  rank : ℕ
  /-- The form itself, on the standard space of its rank. -/
  form : QuadraticForm K (Fin rank → K)
  /-- The form is nondegenerate. -/
  nondeg : (QuadraticMap.associated form).SeparatingLeft

variable {K}

/-- The orthogonal sum of two nondegenerate forms. -/
def DeningerForm.plus (F G : DeningerForm K) : DeningerForm K where
  rank := F.rank + G.rank
  form := deningerFormPlus F.form G.form
  nondeg := deningerFormPlus_separatingLeft F.nondeg G.nondeg

variable (K)

/-- Isometry of nondegenerate forms. -/
def deningerFormSetoid : Setoid (DeningerForm K) where
  r F G := F.form.Equivalent G.form
  iseqv :=
    ⟨fun F => QuadraticMap.Equivalent.refl F.form, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The monoid of isometry classes of nondegenerate quadratic forms. -/
def DeningerWittClass : Type _ := Quotient (deningerFormSetoid K)

variable {K}

/-- The class of a nondegenerate form. -/
def deningerClassOf (F : DeningerForm K) : DeningerWittClass K :=
  Quotient.mk (deningerFormSetoid K) F

theorem deningerClassOf_eq {F G : DeningerForm K} (h : F.form.Equivalent G.form) :
    deningerClassOf F = deningerClassOf G :=
  Quotient.sound h

theorem deningerClassOf_surjective : Function.Surjective (deningerClassOf (K := K)) :=
  Quotient.mk_surjective

/-- The rank of an isometry class. -/
def deningerClassRank : DeningerWittClass K → ℕ :=
  Quotient.lift (fun F : DeningerForm K => F.rank) (by
    intro F G h
    have hf := deningerFinrank_eq_of_equivalent h
    rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at hf)

@[simp]
theorem deningerClassRank_mk (F : DeningerForm K) :
    deningerClassRank (deningerClassOf F) = F.rank := rfl

/-- The standard nondegenerate form of a given rank. -/
noncomputable def deningerStandardFormData (n : ℕ) : DeningerForm K :=
  ⟨n, deningerStandardForm K n, deningerStandardForm_separatingLeft n⟩

/-- The class of the standard form of a given rank. -/
noncomputable def deningerStandardClass (n : ℕ) : DeningerWittClass K :=
  deningerClassOf (deningerStandardFormData n)

theorem deningerStandardClass_def (n : ℕ) :
    deningerStandardClass (K := K) n = deningerClassOf (deningerStandardFormData n) := rfl

@[simp]
theorem deningerClassRank_standard (n : ℕ) :
    deningerClassRank (deningerStandardClass (K := K) n) = n := rfl

/-- **Every class is the class of a standard form.** -/
theorem deningerClass_eq_standard (hsq : ∀ x : K, ∃ y : K, x = y * y) (F : DeningerForm K) :
    deningerClassOf F = deningerStandardClass F.rank := by
  refine deningerClassOf_eq ?_
  have h := deningerEquivalent_standardForm hsq F.form F.nondeg
  rwa [Module.finrank_fin_fun] at h

/-- **Isometry classes are the natural numbers**, with rank as the bijection. -/
theorem deningerClassRank_bijective (hsq : ∀ x : K, ∃ y : K, x = y * y) :
    Function.Bijective (deningerClassRank (K := K)) := by
  constructor
  · intro c d hcd
    obtain ⟨F, rfl⟩ := deningerClassOf_surjective c
    obtain ⟨G, rfl⟩ := deningerClassOf_surjective d
    rw [deningerClass_eq_standard hsq F, deningerClass_eq_standard hsq G]
    exact congrArg deningerStandardClass hcd
  · intro n
    exact ⟨deningerStandardClass n, rfl⟩

/-- **The rank of an orthogonal sum is the sum of the ranks.** -/
@[simp]
theorem deningerClassRank_plus (F G : DeningerForm K) :
    deningerClassRank (deningerClassOf (F.plus G)) = F.rank + G.rank := rfl

/-- **The standard classes add.** -/
theorem deningerStandardClass_plus (m n : ℕ) :
    deningerClassOf ((deningerStandardFormData (K := K) m).plus (deningerStandardFormData n))
      = deningerStandardClass (K := K) (m + n) := by
  refine deningerClassOf_eq ?_
  show (deningerFormPlus (deningerStandardForm K m) (deningerStandardForm K n)).Equivalent
    (deningerStandardForm K (m + n))
  rw [deningerStandardForm_sum]

end WittClasses

section Grothendieck

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- **The rank of a class as an integer.** -/
noncomputable def deningerClassRankInt (c : DeningerWittClass K) : ℤ := deningerClassRank c

/-- **The Grothendieck--Witt group of a quadratically closed field is the integers.**  An additive
invariant of nondegenerate quadratic forms factors uniquely through the rank, and the factorization
is a group homomorphism from the integers: rank is the universal additive invariant, so the group
completion of the monoid of isometry classes is `ℤ`. -/
theorem deningerGrothendieckWittRank_universal (hsq : ∀ x : K, ∃ y : K, x = y * y)
    {A : Type*} [AddCommGroup A] (f : DeningerWittClass K → A)
    (hadd : ∀ F G : DeningerForm K,
      f (deningerClassOf (F.plus G)) = f (deningerClassOf F) + f (deningerClassOf G)) :
    ∃! g : ℤ →+ A, ∀ c : DeningerWittClass K, f c = g (deningerClassRankInt c) := by
  classical
  set a : A := f (deningerStandardClass (K := K) 1) with hadef
  have hstd : ∀ n : ℕ, f (deningerStandardClass (K := K) n) = n • a := by
    intro n
    induction n with
    | zero =>
        have h0 : f (deningerStandardClass (K := K) 0)
            = f (deningerStandardClass (K := K) 0) + f (deningerStandardClass (K := K) 0) := by
          have hb := hadd (deningerStandardFormData (K := K) 0) (deningerStandardFormData 0)
          rwa [deningerStandardClass_plus 0 0, ← deningerStandardClass_def 0, Nat.add_zero] at hb
        have hcancel : f (deningerStandardClass (K := K) 0) + 0
            = f (deningerStandardClass (K := K) 0) + f (deningerStandardClass (K := K) 0) := by
          rw [add_zero]
          exact h0
        rw [zero_smul]
        exact (add_left_cancel hcancel).symm
    | succ n ih =>
        have h := hadd (deningerStandardFormData (K := K) n) (deningerStandardFormData 1)
        rw [deningerStandardClass_plus n 1, ← deningerStandardClass_def n,
          ← deningerStandardClass_def 1] at h
        rw [h, ih, ← hadef, succ_nsmul]
  refine ⟨zmultiplesHom A a, ?_, ?_⟩
  · intro c
    obtain ⟨F, rfl⟩ := deningerClassOf_surjective c
    rw [deningerClass_eq_standard hsq F, hstd F.rank]
    show F.rank • a = (deningerClassRankInt (deningerStandardClass (K := K) F.rank)) • a
    rw [deningerClassRankInt, deningerClassRank_standard]
    exact (natCast_zsmul a F.rank).symm
  · intro g hg
    refine AddMonoidHom.ext_int ?_
    have h := hg (deningerStandardClass (K := K) 1)
    rw [deningerClassRankInt, deningerClassRank_standard, Nat.cast_one] at h
    show g 1 = (zmultiplesHom A a) 1
    rw [← h, ← hadef]
    simp

end Grothendieck

section IsomorphismStability

open scoped TensorProduct

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **An isomorphism survives realification.** -/
noncomputable def deningerRealificationCongr (e : A ≃+ B) : (A ⊗[ℤ] ℝ) ≃ₗ[ℤ] (B ⊗[ℤ] ℝ) :=
  TensorProduct.congr e.toIntLinearEquiv (LinearEquiv.refl ℤ ℝ)

theorem deningerTorsion_map (e : A ≃+ B) :
    (Submodule.torsion ℤ A).map (e.toIntLinearEquiv : A →ₗ[ℤ] B) = Submodule.torsion ℤ B := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff a).mp ha
    refine (Submodule.mem_torsion_iff _).mpr ⟨n, ?_⟩
    have : ((n : ℤ)) • (e.toIntLinearEquiv a) = e.toIntLinearEquiv (((n : ℤ)) • a) :=
      (map_zsmul _ _ _).symm
    show ((n : ℤ)) • (e.toIntLinearEquiv a) = 0
    rw [this]
    have hna : ((n : ℤ)) • a = 0 := hn
    rw [hna, map_zero]
  · intro b hb
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff b).mp hb
    refine ⟨e.symm b, ?_, ?_⟩
    · refine (Submodule.mem_torsion_iff _).mpr ⟨n, ?_⟩
      show ((n : ℤ)) • (e.symm b) = 0
      have hnb : ((n : ℤ)) • b = 0 := hn
      have : ((n : ℤ)) • (e.symm b) = e.symm (((n : ℤ)) • b) := (map_zsmul _ _ _).symm
      rw [this, hnb, map_zero]
    · show e (e.symm b) = b
      exact e.apply_symm_apply b

/-- **An isomorphism survives the quotient by torsion.** -/
noncomputable def deningerTorsionQuotientCongr (e : A ≃+ B) :
    (A ⧸ Submodule.torsion ℤ A) ≃ₗ[ℤ] (B ⧸ Submodule.torsion ℤ B) :=
  Submodule.Quotient.equiv _ _ e.toIntLinearEquiv (deningerTorsion_map e)

end IsomorphismStability

end RHTower


