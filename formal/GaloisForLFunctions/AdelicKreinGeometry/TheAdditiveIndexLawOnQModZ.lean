import GaloisForLFunctions.AdelicKreinGeometry.TheAdditiveIndexLaw
import GaloisForLFunctions.AdelicKreinGeometry.ConformalSymmetryNeedsANegativeSquare

/-!
# The additive index law on `ℚ/ℤ`

A successor state of the integers is a `1`-periodic Hermitian function `ψ` on the translations of
`ℚ`, i.e. a kernel on `ℚ/ℤ`. Its characters are indexed by `ℤ̂`; at level `N` the subgroup
`(1/N)ℤ/ℤ ≅ ℤ/N` sees them through their reductions mod `N`.

* **Levels** (`gram_levelKernel`): the level-`N` kernel `k_N(x) = ψ(x/N)` on `ℤ/N` has the Gram
  matrices of `ψ` on the points `x/N`.
* **Every family lives at one level** (`negIndex_le_iSup_level`): a finite family of rationals is,
  modulo `ℤ`, a family in `(1/D)ℤ/ℤ` for a common denominator `D`.
* **The additive index law on `ℚ/ℤ`** (`negIndex_eq_iSup_card_negCoeffs`):
  `κ(ψ) = sup_N #{ξ ∈ ℤ/N : a^{(N)}_ξ < 0}`, the largest number of negative conductor coefficients
  at a finite level.

So a successor state of finite index has at most `κ` negative conductor coefficients at every level:
the negative part of its spectral measure on `ℤ̂` consists of at most `κ` points, and a successor
state of index zero is a positive measure on `ℤ̂`, as the Haar successor `1_ℤ` with Haar measure.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- `1`-periodicity on the translations of `ℚ`. -/
def IsIntPeriodic (ψ : Multiplicative ℚ → ℂ) : Prop :=
  ∀ b : ℚ, ψ (Multiplicative.ofAdd (b + 1)) = ψ (Multiplicative.ofAdd b)

theorem IsIntPeriodic.add_int {ψ : Multiplicative ℚ → ℂ} (h : IsIntPeriodic ψ) (b : ℚ) (m : ℤ) :
    ψ (Multiplicative.ofAdd (b + m)) = ψ (Multiplicative.ofAdd b) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih => rw [Int.cast_add, Int.cast_one, ← add_assoc, h, ih]
  | pred m ih =>
    have := h (b + ((-(m : ℤ) - 1 : ℤ) : ℚ))
    rw [show b + ((-(m : ℤ) - 1 : ℤ) : ℚ) + 1 = b + ((-(m : ℤ) : ℤ) : ℚ) by push_cast; ring] at this
    rw [← this, ih]

/-- The level-`N` kernel `k_N(x) = ψ(x/N)` on `ℤ/N`. -/
def levelKernel (ψ : Multiplicative ℚ → ℂ) (N : ℕ) (x : Multiplicative (ZMod N)) : ℂ :=
  ψ (Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℚ) / N))

/-- The level points `x ↦ x/N`. -/
def levelPoint (N : ℕ) (x : Multiplicative (ZMod N)) : Multiplicative ℚ :=
  Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℚ) / N)

/-- **Levels.** The level kernel has the Gram matrices of `ψ` at the level points. -/
theorem gram_levelKernel {ψ : Multiplicative ℚ → ℂ} (hψ : IsIntPeriodic ψ) (N : ℕ) [NeZero N]
    {n : ℕ} (x : Fin n → Multiplicative (ZMod N)) :
    gram (levelKernel ψ N) x = gram ψ fun a => levelPoint N (x a) := by
  ext a b
  simp only [gram, levelKernel, levelPoint, toAdd_mul, toAdd_inv]
  set y := Multiplicative.toAdd (x a)
  set z := Multiplicative.toAdd (x b)
  -- `(z − y).val ≡ z.val − y.val` modulo `N`
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (((-y + z).val : ℤ) : ℚ) = ((z.val : ℤ) - (y.val : ℤ) : ℤ) + N * m := by
    have h1 : ((-y + z : ZMod N).val : ℤ) = ((z.val : ℤ) - y.val) % N := by
      rw [← ZMod.val_intCast]; congr 1; push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]; ring_nf
    refine ⟨-(((z.val : ℤ) - y.val) / N), ?_⟩
    rw [h1]
    have := Int.emod_add_ediv_mul ((z.val : ℤ) - y.val) N
    have h' := congrArg (fun w : ℤ => (w : ℚ)) this
    push_cast at h' ⊢
    linarith
  rw [show (((-y + z).val : ℕ) : ℚ) / N = ((z.val : ℚ) / N - (y.val : ℚ) / N) + (m : ℚ) by
    rw [show (((-y + z).val : ℕ) : ℚ) = (((-y + z).val : ℤ) : ℚ) by push_cast; rfl, hm]
    push_cast; field_simp]
  rw [hψ.add_int]
  congr 1
  apply Multiplicative.toAdd.injective
  simp [toAdd_mul, toAdd_inv]
  ring

/-- The level kernels never have more negative squares than `ψ`. -/
theorem negIndex_levelKernel_le {ψ : Multiplicative ℚ → ℂ} (hψ : IsIntPeriodic ψ) (N : ℕ)
    [NeZero N] : negIndex (levelKernel ψ N) ≤ negIndex ψ :=
  negIndex_le_iff.mpr fun n x => by
    rw [gram_levelKernel hψ]
    exact hermNegIndex_gram_le_negIndex ψ _

/-- **Every family lives at one level.** -/
theorem negIndex_le_iSup_level {ψ : Multiplicative ℚ → ℂ} (hψ : IsIntPeriodic ψ) :
    negIndex ψ ≤ ⨆ N : ℕ, negIndex (levelKernel ψ (N + 1)) := by
  refine negIndex_le_iff.mpr fun n x => ?_
  obtain ⟨D, X, hD, hX⟩ := exists_int_scaling x
  obtain ⟨N, rfl⟩ : ∃ N, D = N + 1 := ⟨D - 1, by omega⟩
  set k : Fin n → Multiplicative (ZMod (N + 1)) :=
    fun a => Multiplicative.ofAdd ((Multiplicative.toAdd (X a) : ℤ) : ZMod (N + 1))
  -- the family agrees with the level points modulo `ℤ`
  have hgram : gram ψ x = gram ψ fun a => levelPoint (N + 1) (k a) := by
    ext a b
    simp only [gram, levelPoint, k, toAdd_ofAdd]
    have hq : ∀ c, ∃ m : ℤ, (((Multiplicative.toAdd (X c) : ℤ) : ZMod (N + 1)).val : ℚ) / (N + 1 : ℕ)
        = Multiplicative.toAdd (x c) + m := by
      intro c
      refine ⟨-((Multiplicative.toAdd (X c)) / ((N + 1 : ℕ) : ℤ)), ?_⟩
      have h1 := ZMod.val_intCast (n := N + 1) (Multiplicative.toAdd (X c))
      have h2 := Int.emod_add_ediv_mul (Multiplicative.toAdd (X c)) ((N + 1 : ℕ) : ℤ)
      have hD' : ((N + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hval : ((((Multiplicative.toAdd (X c) : ℤ) : ZMod (N + 1)).val : ℕ) : ℚ) =
          ((Multiplicative.toAdd (X c) : ℤ) : ℚ) -
            ((Multiplicative.toAdd (X c) / ((N + 1 : ℕ) : ℤ) : ℤ) : ℚ) * ((N + 1 : ℕ) : ℚ) := by
        have h3 : (((((Multiplicative.toAdd (X c) : ℤ) : ZMod (N + 1)).val : ℕ) : ℤ) : ℚ) =
            ((Multiplicative.toAdd (X c) % ((N + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by rw [h1]
        rw [show ((((Multiplicative.toAdd (X c) : ℤ) : ZMod (N + 1)).val : ℕ) : ℚ) =
          (((((Multiplicative.toAdd (X c) : ℤ) : ZMod (N + 1)).val : ℕ) : ℤ) : ℚ) by push_cast; rfl,
          h3]
        have h4 := congrArg (fun w : ℤ => (w : ℚ)) h2
        push_cast at h4 ⊢
        linarith
      rw [hval, hX c]
      field_simp
      push_cast
      ring
    obtain ⟨ma, hma⟩ := hq a
    obtain ⟨mb, hmb⟩ := hq b
    have e : (Multiplicative.ofAdd ((((Multiplicative.toAdd (X a) : ℤ) : ZMod (N + 1)).val : ℚ) /
        (N + 1 : ℕ)))⁻¹ * Multiplicative.ofAdd ((((Multiplicative.toAdd (X b) : ℤ) :
          ZMod (N + 1)).val : ℚ) / (N + 1 : ℕ)) =
        Multiplicative.ofAdd (Multiplicative.toAdd ((x a)⁻¹ * x b) + ((mb - ma : ℤ) : ℚ)) := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      rw [hma, hmb]; push_cast; ring
    rw [e, hψ.add_int, ofAdd_toAdd]
  rw [hgram, ← gram_levelKernel hψ]
  exact (hermNegIndex_gram_le_negIndex _ k).trans (le_iSup (fun N : ℕ =>
    negIndex (levelKernel ψ (N + 1))) N)

/-- The level kernels of a Hermitian periodic function are Hermitian. -/
theorem isHermKernel_levelKernel {ψ : Multiplicative ℚ → ℂ} (hk : IsHermKernel ψ)
    (hψ : IsIntPeriodic ψ) (N : ℕ) [NeZero N] : IsHermKernel (levelKernel ψ N) := fun x => by
  have h := congrFun (congrFun (gram_levelKernel hψ N ![1, x]) 0) 1
  have h' := congrFun (congrFun (gram_levelKernel hψ N ![1, x]) 1) 0
  simp only [gram, Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul, mul_one] at h h'
  rw [h', h, ← hk]
  congr 1
  simp [mul_comm]

/-- **The additive index law on `ℚ/ℤ`.** The index of a successor state is the supremum over levels
of its numbers of negative conductor coefficients. -/
theorem negIndex_eq_iSup_card_negCoeffs {ψ : Multiplicative ℚ → ℂ} (hk : IsHermKernel ψ)
    (hψ : IsIntPeriodic ψ) :
    negIndex ψ = ⨆ N : ℕ, ((negCoeffs (levelKernel ψ (N + 1))).card : ℕ∞) := by
  have hlevel : ∀ N : ℕ, negIndex (levelKernel ψ (N + 1)) =
      ((negCoeffs (levelKernel ψ (N + 1))).card : ℕ∞) := fun N =>
    negIndex_zmod_eq_card (isHermKernel_levelKernel hk hψ (N + 1))
  refine le_antisymm ?_ (iSup_le fun N => ?_)
  · exact (negIndex_le_iSup_level hψ).trans (iSup_mono fun N => (hlevel N).le)
  · rw [← hlevel N]
    exact negIndex_levelKernel_le hψ (N + 1)

end GaloisForLFunctions.AdelicKreinGeometry
