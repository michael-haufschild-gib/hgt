import GaloisForLFunctions.HTGeometry.MvPolynomialLocalPoint
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Nullstellensatz

/-!
# Height of a complex point ideal

This module proves directly that the maximal ideal of a point of complex affine `n`-space has
height `n`.  The proof constructs the prime chain obtained by evaluating the coordinates one at a
time.  Keeping this fact in a small cached module avoids repeatedly unfolding the Krull-dimension
and multivariate-evaluation argument in local Jacobian calculations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinates not yet evaluated after the first `k` coordinates of `Fin n`. -/
abbrev pointTail (n k : ℕ) := {i : Fin n // k ≤ i.1}

instance pointTail_self_isEmpty (n : ℕ) : IsEmpty (pointTail n n) :=
  ⟨fun i ↦ by omega⟩

/-- Evaluate the first `k` coordinates at `x`, retaining the remaining coordinates as polynomial
variables. -/
def pointTailEvalHom {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    MvPolynomial (Fin n) ℂ →+* MvPolynomial (pointTail n k) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* MvPolynomial (pointTail n k) ℂ)
    (fun i ↦ if h : k ≤ i.1 then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (x i))

/-- Evaluate the next coordinate in a partially evaluated polynomial ring. -/
def pointTailStepHom {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    MvPolynomial (pointTail n k) ℂ →+* MvPolynomial (pointTail n (k + 1)) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* MvPolynomial (pointTail n (k + 1)) ℂ)
    (fun i ↦ if h : k + 1 ≤ i.1.1 then MvPolynomial.X ⟨i.1, h⟩
      else MvPolynomial.C (x i.1))

theorem pointTailStepHom_comp {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    (pointTailStepHom x k).comp (pointTailEvalHom x k) = pointTailEvalHom x (k + 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [pointTailStepHom, pointTailEvalHom]
  · intro i
    by_cases hk : k ≤ i.1
    · by_cases hks : k + 1 ≤ i.1
      · simp [pointTailStepHom, pointTailEvalHom, hk]
      · simp [pointTailStepHom, pointTailEvalHom, hk]
    · have hks : ¬ k + 1 ≤ i.1 := fun h ↦ hk (Nat.le_trans (Nat.le_add_right k 1) h)
      simp [pointTailStepHom, pointTailEvalHom, hk]
      intro h
      omega

/-- Kernel after evaluating the first `k` coordinates. -/
def pointTailIdeal {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (pointTailEvalHom x k)

instance pointTailIdeal_isPrime {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    (pointTailIdeal x k).IsPrime := RingHom.ker_isPrime _

theorem pointTailIdeal_mono {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    pointTailIdeal x k ≤ pointTailIdeal x (k + 1) := by
  intro p hp
  rw [pointTailIdeal, RingHom.mem_ker] at hp ⊢
  rw [← pointTailStepHom_comp x k, RingHom.comp_apply, hp, map_zero]

/-- Evaluating one additional coordinate strictly enlarges the kernel while a coordinate remains. -/
theorem pointTailIdeal_strictMono {n : ℕ} (x : Fin n → ℂ) {k : ℕ} (hk : k < n) :
    pointTailIdeal x k < pointTailIdeal x (k + 1) := by
  refine (pointTailIdeal_mono x k).lt_of_not_ge ?_
  intro hge
  let i : Fin n := ⟨k, hk⟩
  let w : MvPolynomial (Fin n) ℂ := MvPolynomial.X i - MvPolynomial.C (x i)
  have hwNext : w ∈ pointTailIdeal x (k + 1) := by
    rw [pointTailIdeal, RingHom.mem_ker]
    simp [w, i, pointTailEvalHom]
  have hwNow := hge hwNext
  rw [pointTailIdeal, RingHom.mem_ker] at hwNow
  have hkself : k ≤ i.1 := Nat.le_refl k
  simp only [w, pointTailEvalHom, map_sub, MvPolynomial.eval₂Hom_X',
    MvPolynomial.eval₂Hom_C] at hwNow
  have hcoeff := congrArg
    (fun p : MvPolynomial (pointTail n k) ℂ ↦
      p.coeff (Finsupp.single (⟨i, hkself⟩ : pointTail n k) 1)) hwNow
  have hsingle : Finsupp.single (⟨i, hkself⟩ : pointTail n k) 1 ≠ 0 := by
    exact Finsupp.single_ne_zero.mpr one_ne_zero
  have hsingle' : (0 : pointTail n k →₀ ℕ) ≠
      Finsupp.single (⟨i, hkself⟩ : pointTail n k) 1 := Ne.symm hsingle
  have hone : (1 : ℂ) = 0 := by
    simpa [i, hsingle, hsingle'] using hcoeff
  exact one_ne_zero hone

theorem natCast_le_pointTailIdeal_height {n : ℕ} (x : Fin n → ℂ) :
    ∀ k ≤ n, (k : ℕ∞) ≤ (pointTailIdeal x k).height := by
  intro k hk
  induction k with
  | zero => exact bot_le
  | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      calc
        ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by simp
        _ ≤ (pointTailIdeal x k).height + 1 := by
          gcongr
          exact ih (Nat.le_of_lt hkn)
        _ ≤ (pointTailIdeal x (k + 1)).height :=
          Ideal.height_add_one_le_of_lt_of_isPrime (pointTailIdeal_strictMono x hkn)

theorem pointTailIdeal_at_n_eq_vanishingIdeal {n : ℕ} (x : Fin n → ℂ) :
    pointTailIdeal x n = MvPolynomial.vanishingIdeal ℂ {x} := by
  ext p
  rw [pointTailIdeal, RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  change pointTailEvalHom x n p = 0 ↔ MvPolynomial.eval x p = 0
  have heval : (MvPolynomial.isEmptyRingEquiv ℂ (pointTail n n))
      (pointTailEvalHom x n p) = MvPolynomial.eval x p := by
    have hhom : (MvPolynomial.isEmptyRingEquiv ℂ (pointTail n n)).toRingHom.comp
          (pointTailEvalHom x n) =
        MvPolynomial.eval₂Hom (RingHom.id ℂ) x := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [pointTailEvalHom]
        change MvPolynomial.coeff 0 (MvPolynomial.C r) = r
        exact MvPolynomial.coeff_zero_C r
      · intro i
        have hi : ¬ n ≤ i.1 := Nat.not_le_of_gt i.isLt
        simp [pointTailEvalHom, hi]
        change MvPolynomial.coeff 0 (MvPolynomial.C (x i)) = x i
        exact MvPolynomial.coeff_zero_C (x i)
    exact DFunLike.congr_fun hhom p
  constructor
  · intro hp
    rw [← heval, hp, map_zero]
  · intro hp
    apply (MvPolynomial.isEmptyRingEquiv ℂ (pointTail n n)).injective
    simpa [heval] using hp

/-- The maximal ideal of a point of complex affine `n`-space has height exactly `n`. -/
theorem height_vanishingIdeal_singleton_fin {n : ℕ} (x : Fin n → ℂ) :
    (MvPolynomial.vanishingIdeal ℂ {x}).height = n := by
  apply le_antisymm
  · have hu := Ideal.height_le_ringKrullDim_of_isPrime (I :=
      MvPolynomial.vanishingIdeal ℂ {x})
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] at hu
    exact_mod_cast hu
  · rw [← pointTailIdeal_at_n_eq_vanishingIdeal x]
    exact natCast_le_pointTailIdeal_height x n (Nat.le_refl n)

end

end GaloisForLFunctions.HTGeometry
