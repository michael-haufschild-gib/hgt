import GaloisForLFunctions.AdelicKreinGeometry.TheIndexOfAnInducedState
import Mathlib.Analysis.Fourier.ZMod

/-!
# The additive index law

The multiplicative side of the Weil kernel has an exact index formula: on the Hecke lattice the
index counts the zeros right of the line (HKT). This file gives the exact index law of the additive
side at every finite level: a successor state on the residues `ℤ/N`.

* **Fourier expansion** (`kernel_eq_sum_fourierCoeff`): `k(x) = Σ_ξ a_ξ e(xξ/N)` with
  `a_ξ = N⁻¹ Σ_x e(−xξ/N) k(x)`; for a Hermitian kernel the coefficients are real
  (`conj_fourierCoeff`).
* **The Gram form is a Fourier sum** (`gramForm_eq_sum_fourierCoeff`):
  `Σ_{a,b} c̄_a c_b k(y_b − y_a) = Σ_ξ a_ξ |Σ_b c_b e(y_b ξ/N)|²`.
* **The additive index law** (`negIndex_zmod_eq_card`): `κ(k) = #{ξ : a_ξ < 0}`. The negative
  coefficients pay for themselves with one square each; conversely the dual characters
  `x ↦ e(−xξ/N)`, `a_ξ < 0`, are orthogonal by character orthogonality and span a negative subspace
  of the full Gram matrix.
* **Conductor classes** (`fourierCoeff_unit_mul`): a kernel invariant under the units of `ℤ/N` has
  coefficients constant on each class `{ξ : gcd(ξ, N) = N/q}`, the Ramanujan conductor modes; its
  index is a sum of class sizes `φ(q)` (`negIndex_zmod_eq_sum_totient`).

So the additive side counts its negative squares exactly, one per negative conductor coefficient.
An additive integer invariant equal to a number of zeros would be a count of negative conductor
modes; at fixed overlap the complete Weil matrix has nonnegative conductor energies, index zero.
-/

open Complex Finset
open scoped ComplexConjugate ZMod
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {N : ℕ} [NeZero N]

local notation "e" => (ZMod.stdAddChar : AddChar (ZMod N) ℂ)

theorem stdAddChar_neg (y : ZMod N) : e (-y) = conj (e y) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- The Fourier coefficients of a kernel on `ℤ/N`. -/
def fourierCoeff (k : Multiplicative (ZMod N) → ℂ) (ξ : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, e (-(x * ξ)) * k (Multiplicative.ofAdd x)

/-- **Fourier expansion.** -/
theorem kernel_eq_sum_fourierCoeff (k : Multiplicative (ZMod N) → ℂ) (x : ZMod N) :
    k (Multiplicative.ofAdd x) = ∑ ξ, fourierCoeff k ξ * e (x * ξ) := by
  have h := congrFun (LinearEquiv.symm_apply_apply ZMod.dft
    (fun y : ZMod N => k (Multiplicative.ofAdd y))) x
  rw [ZMod.invDFT_apply] at h
  rw [← h, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [ZMod.dft_apply, fourierCoeff, smul_eq_mul]
  simp only [smul_eq_mul]
  ring_nf

/-- A Hermitian kernel has real Fourier coefficients. -/
theorem conj_fourierCoeff {k : Multiplicative (ZMod N) → ℂ} (hk : IsHermKernel k) (ξ : ZMod N) :
    conj (fourierCoeff k ξ) = fourierCoeff k ξ := by
  have h1 : ∀ x : ZMod N, conj (e (-(x * ξ)) * k (Multiplicative.ofAdd x)) =
      e (-((-x) * ξ)) * k (Multiplicative.ofAdd (-x)) := by
    intro x
    rw [map_mul, ← stdAddChar_neg, ← hk]
    congr 2
    · ring
  simp only [fourierCoeff, map_mul, map_inv₀, Complex.conj_natCast, map_sum, h1]
  congr 1
  exact Equiv.sum_comp (Equiv.neg (ZMod N)) (fun x => e (-(x * ξ)) * k (Multiplicative.ofAdd x))

/-- **The Gram form is a Fourier sum.** -/
theorem gramForm_eq_sum_fourierCoeff (k : Multiplicative (ZMod N) → ℂ) {n : ℕ}
    (z : Fin n → Multiplicative (ZMod N)) (c : Fin n → ℂ) :
    ∑ a, ∑ b, conj (c a) * k ((z a)⁻¹ * z b) * c b =
      ∑ ξ, fourierCoeff k ξ * (conj (∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)) *
        ∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)) := by
  have hz : ∀ a b, (z a)⁻¹ * z b =
      Multiplicative.ofAdd (Multiplicative.toAdd (z b) - Multiplicative.toAdd (z a)) := by
    intro a b; apply Multiplicative.toAdd.injective; simp; ring
  have hchar : ∀ a b ξ, e ((Multiplicative.toAdd (z b) - Multiplicative.toAdd (z a)) * ξ) =
      conj (e (Multiplicative.toAdd (z a) * ξ)) * e (Multiplicative.toAdd (z b) * ξ) := by
    intro a b ξ
    rw [← stdAddChar_neg, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have hk' : ∀ a b, k ((z a)⁻¹ * z b) = ∑ ξ, fourierCoeff k ξ *
      (conj (e (Multiplicative.toAdd (z a) * ξ)) * e (Multiplicative.toAdd (z b) * ξ)) := by
    intro a b
    rw [hz, kernel_eq_sum_fourierCoeff k]
    exact sum_congr rfl fun ξ _ => by rw [hchar]
  have hR : ∀ ξ, fourierCoeff k ξ * (conj (∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)) *
      ∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)) =
      ∑ a, ∑ b, conj (c a) * (fourierCoeff k ξ * (conj (e (Multiplicative.toAdd (z a) * ξ)) *
        e (Multiplicative.toAdd (z b) * ξ))) * c b := by
    intro ξ
    rw [map_sum, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  simp_rw [hR, hk', mul_sum, sum_mul]
  exact (sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

/-- The negative Fourier coefficients. -/
def negCoeffs (k : Multiplicative (ZMod N) → ℂ) : Finset (ZMod N) :=
  univ.filter fun ξ => (fourierCoeff k ξ).re < 0

/-- The real form of a Fourier sum with real coefficients. -/
theorem hermQuad_eq_sum_fourierCoeff {k : Multiplicative (ZMod N) → ℂ} (hk : IsHermKernel k)
    {n : ℕ} (z : Fin n → Multiplicative (ZMod N)) (c : Fin n → ℂ) :
    hermQuad (gram k z) c = ∑ ξ, (fourierCoeff k ξ).re *
      ‖∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)‖ ^ 2 := by
  rw [hermQuad_gram, gramForm_eq_sum_fourierCoeff, Complex.re_sum]
  refine sum_congr rfl fun ξ _ => ?_
  have hreal : fourierCoeff k ξ = ((fourierCoeff k ξ).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (conj_fourierCoeff hk ξ)).symm
  rw [Complex.conj_mul', hreal]
  norm_cast

/-- **The additive index law.** A Hermitian kernel on `ℤ/N` has exactly as many negative squares as
negative Fourier coefficients. -/
theorem negIndex_zmod_eq_card {k : Multiplicative (ZMod N) → ℂ} (hk : IsHermKernel k) :
    negIndex k = (negCoeffs k).card := by
  classical
  set S := negCoeffs k
  refine le_antisymm ?_ ?_
  · -- each negative coefficient is paid by one square
    set eS := S.equivFin
    refine negIndex_le_of_rank (m := S.card) (fun i g =>
      (Real.sqrt (-(fourierCoeff k (eS.symm i : ZMod N)).re) : ℂ) *
        e (Multiplicative.toAdd g * (eS.symm i : ZMod N))) fun n z c => ?_
    rw [hermQuad_eq_sum_fourierCoeff hk]
    have hsq : ∑ i, normSq (∑ a, c a * ((Real.sqrt (-(fourierCoeff k (eS.symm i : ZMod N)).re) : ℂ) *
        e (Multiplicative.toAdd (z a) * (eS.symm i : ZMod N)))) =
        ∑ ξ ∈ S, -(fourierCoeff k ξ).re * ‖∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)‖ ^ 2 := by
      rw [← S.sum_coe_sort, ← eS.symm.sum_comp]
      refine sum_congr rfl fun i _ => ?_
      have hneg : 0 ≤ -(fourierCoeff k (eS.symm i : ZMod N)).re := by
        have := (mem_filter.mp (eS.symm i).2).2
        linarith
      have e1 : ∑ a, c a * ((Real.sqrt (-(fourierCoeff k (eS.symm i : ZMod N)).re) : ℂ) *
          e (Multiplicative.toAdd (z a) * (eS.symm i : ZMod N))) =
          (Real.sqrt (-(fourierCoeff k (eS.symm i : ZMod N)).re) : ℂ) *
            ∑ a, c a * e (Multiplicative.toAdd (z a) * (eS.symm i : ZMod N)) := by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
      rw [e1, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hneg,
        Complex.normSq_eq_norm_sq]
    rw [hsq, ← Finset.sum_filter_add_sum_filter_not univ (fun ξ => (fourierCoeff k ξ).re < 0)]
    have hS : univ.filter (fun ξ : ZMod N => (fourierCoeff k ξ).re < 0) = S := rfl
    rw [hS]
    have : ∑ ξ ∈ S, (fourierCoeff k ξ).re * ‖∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)‖ ^ 2 +
        ∑ ξ ∈ S, -(fourierCoeff k ξ).re * ‖∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)‖ ^ 2 = 0 := by
      rw [← sum_add_distrib]; exact sum_eq_zero fun ξ _ => by ring
    have hnn : 0 ≤ ∑ ξ ∈ univ.filter (fun ξ : ZMod N => ¬ (fourierCoeff k ξ).re < 0),
        (fourierCoeff k ξ).re * ‖∑ b, c b * e (Multiplicative.toAdd (z b) * ξ)‖ ^ 2 :=
      sum_nonneg fun ξ hξ => mul_nonneg (not_lt.mp (mem_filter.mp hξ).2) (sq_nonneg _)
    linarith
  · -- the dual characters of the negative coefficients span a negative subspace
    set eN := Fintype.equivFin (ZMod N)
    set z : Fin (Fintype.card (ZMod N)) → Multiplicative (ZMod N) :=
      fun a => Multiplicative.ofAdd (eN.symm a)
    let L : (S → ℂ) →ₗ[ℂ] (Fin (Fintype.card (ZMod N)) → ℂ) :=
      { toFun := fun β a => ∑ ξ : S, β ξ * e (-(eN.symm a * (ξ : ZMod N)))
        map_add' := fun β β' => funext fun a => by simp [add_mul, sum_add_distrib]
        map_smul' := fun t β => funext fun a => by simp [mul_assoc, mul_sum] }
    have hP : ∀ (β : S → ℂ) (η : ZMod N),
        ∑ b, L β b * e (Multiplicative.toAdd (z b) * η) =
          (N : ℂ) * if h : η ∈ S then β ⟨η, h⟩ else 0 := by
      intro β η
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, z, toAdd_ofAdd, sum_mul]
      rw [Finset.sum_comm]
      have horth : ∀ ξ : S, ∑ b : Fin (Fintype.card (ZMod N)),
          β ξ * e (-(eN.symm b * (ξ : ZMod N))) * e (eN.symm b * η) =
            β ξ * if η - (ξ : ZMod N) = 0 then (N : ℂ) else 0 := by
        intro ξ
        have h := AddChar.sum_mulShift (η - (ξ : ZMod N)) (ZMod.isPrimitive_stdAddChar N)
        rw [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
        rw [← h, mul_sum, ← eN.symm.sum_comp]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_assoc, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      simp_rw [horth]
      split_ifs with hη
      · rw [Finset.sum_eq_single ⟨η, hη⟩]
        · simp [mul_comm]
        · intro ξ _ hξ
          rw [if_neg]; · simp
          intro h0
          exact hξ (Subtype.ext (sub_eq_zero.mp h0).symm)
        · exact fun h => absurd (mem_univ _) h
      · rw [mul_zero]
        refine sum_eq_zero fun ξ _ => ?_
        rw [if_neg]; · simp
        intro h0
        exact hη ((sub_eq_zero.mp h0) ▸ ξ.2)
    have hneg : ∀ β, β ≠ 0 → hermQuad (gram k z) (L β) < 0 := by
      intro β hβ
      rw [hermQuad_eq_sum_fourierCoeff hk]
      simp_rw [hP]
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun ξ => (fourierCoeff k ξ).re < 0)]
      have hzero : ∑ ξ ∈ univ.filter (fun ξ : ZMod N => ¬ (fourierCoeff k ξ).re < 0),
          (fourierCoeff k ξ).re * ‖(N : ℂ) * if h : ξ ∈ S then β ⟨ξ, h⟩ else 0‖ ^ 2 = 0 := by
        refine sum_eq_zero fun ξ hξ => ?_
        have hξS : ξ ∉ S := fun h => (mem_filter.mp hξ).2 (mem_filter.mp h).2
        rw [dif_neg hξS]; simp
      rw [hzero, add_zero]
      obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, β ξ ≠ 0 := by
        by_contra h; push Not at h; exact hβ (funext h)
      have hS' : univ.filter (fun ξ : ZMod N => (fourierCoeff k ξ).re < 0) = S := rfl
      rw [hS']
      refine Finset.sum_neg' (fun ξ hξ => ?_) ⟨ξ₀, ξ₀.2, ?_⟩
      · exact mul_nonpos_of_nonpos_of_nonneg (mem_filter.mp hξ).2.le (sq_nonneg _)
      · rw [dif_pos ξ₀.2]
        refine mul_neg_of_neg_of_pos (mem_filter.mp ξ₀.2).2 ?_
        have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
        exact pow_pos (norm_pos_iff.mpr (mul_ne_zero hN hξ₀)) 2
    have h := card_le_hermNegIndex_of_forall_neg (gram k z) L hneg
    rw [Fintype.card_coe] at h
    exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex k z)

/-- **Conductor classes.** A kernel invariant under the units of `ℤ/N` has Fourier coefficients
constant on unit orbits. -/
theorem fourierCoeff_unit_mul {k : Multiplicative (ZMod N) → ℂ}
    (hinv : ∀ (u : (ZMod N)ˣ) (x : ZMod N),
      k (Multiplicative.ofAdd ((u : ZMod N) * x)) = k (Multiplicative.ofAdd x))
    (u : (ZMod N)ˣ) (ξ : ZMod N) : fourierCoeff k ((u : ZMod N) * ξ) = fourierCoeff k ξ := by
  simp only [fourierCoeff]
  congr 1
  rw [← Equiv.sum_comp (Units.mulLeft u⁻¹)]
  refine sum_congr rfl fun y _ => ?_
  have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
  simp only [Units.mulLeft_apply]
  rw [hinv u⁻¹ y]
  congr 2
  linear_combination (-(y * ξ)) * hu

end GaloisForLFunctions.AdelicKreinGeometry
