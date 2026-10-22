import GaloisForLFunctions.RHTower.Deninger.DeningerEulerJets
import GaloisForLFunctions.RHTower.Deninger.DeningerTriangularShift

/-!
# Hermite interpolation for the Euler operator

At finitely many nonzero points, with prescribed jets of the Euler operator and prescribed zeros at
two further points, an interpolating polynomial exists.  The masked powers
`G_i · (X - w_i)^j`, where the mask carries the two prescribed zeros and the full multiplicities of
the other points, have a triangular Euler jet matrix with invertible diagonal, so the coefficients
are determined one at a time.

* `deningerEulerOp_iterate_finsetSum` : the Euler iterate is additive.
* `deningerJet_interpolation` : the interpolation theorem.
-/

namespace RHTower

open Polynomial

section Additivity

theorem deningerEulerOp_iterate_zero (δ : ℂ) (k : ℕ) :
    (deningerEulerOp δ)^[k] 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, deningerEulerOp]
    simp

theorem deningerEulerOp_iterate_finsetSum {ι : Type*} (δ : ℂ) (k : ℕ) (s : Finset ι)
    (f : ι → ℂ[X]) :
    (deningerEulerOp δ)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (deningerEulerOp δ)^[k] (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [deningerEulerOp_iterate_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, deningerEulerOp_iterate_add, ih, Finset.sum_insert hi]

end Additivity

section Interpolation

variable {K : ℕ}

/-- The mask of a node: the two prescribed zeros together with the full multiplicities of the other
nodes. -/
noncomputable def deningerJetMask (w : Fin K → ℂ) (m : Fin K → ℕ) (u₁ u₂ : ℂ) (i : Fin K) :
    ℂ[X] :=
  (X - C u₁) * (X - C u₂) * ∏ i' ∈ Finset.univ.erase i, (X - C (w i')) ^ (m i')

/-- The masked power attached to a node and an order. -/
noncomputable def deningerJetBasis (w : Fin K → ℂ) (m : Fin K → ℕ) (u₁ u₂ : ℂ)
    (i : Fin K) (j : ℕ) : ℂ[X] :=
  deningerJetMask w m u₁ u₂ i * (X - C (w i)) ^ j

theorem deningerJetMask_eval_ne_zero {w : Fin K → ℂ} {m : Fin K → ℕ} {u₁ u₂ : ℂ}
    (hwinj : Function.Injective w) (hwu₁ : ∀ i, w i ≠ u₁) (hwu₂ : ∀ i, w i ≠ u₂) (i : Fin K) :
    (deningerJetMask w m u₁ u₂ i).eval (w i) ≠ 0 := by
  rw [deningerJetMask]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_pow]
  refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hwu₁ i)) (sub_ne_zero.mpr (hwu₂ i))) ?_
  refine Finset.prod_ne_zero_iff.mpr fun i' hi' => ?_
  refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
  intro hcon
  exact (Finset.mem_erase.mp hi').1 (hwinj hcon.symm)

theorem deningerJetBasis_dvd_self (w : Fin K → ℂ) (m : Fin K → ℕ) (u₁ u₂ : ℂ)
    (i : Fin K) (j : ℕ) :
    (X - C (w i)) ^ j ∣ deningerJetBasis w m u₁ u₂ i j :=
  Dvd.intro_left _ rfl

theorem deningerJetBasis_dvd_other (w : Fin K → ℂ) (m : Fin K → ℕ) (u₁ u₂ : ℂ)
    {i i' : Fin K} (hne : i ≠ i') (j : ℕ) :
    (X - C (w i)) ^ (m i) ∣ deningerJetBasis w m u₁ u₂ i' j := by
  rw [deningerJetBasis, deningerJetMask]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)

theorem deningerJetBasis_eval_zero (w : Fin K → ℂ) (m : Fin K → ℕ) (u₁ u₂ : ℂ)
    (i : Fin K) (j : ℕ) :
    (deningerJetBasis w m u₁ u₂ i j).eval u₁ = 0 ∧
      (deningerJetBasis w m u₁ u₂ i j).eval u₂ = 0 := by
  constructor <;>
    · rw [deningerJetBasis, deningerJetMask]
      simp

/-- **Hermite interpolation for the Euler operator.**  With prescribed zeros at two points and
prescribed Euler jets at finitely many distinct nonzero points, an interpolating polynomial
exists. -/
theorem deningerJet_interpolation {δ : ℂ} (hδ : δ ≠ 0)
    (w : Fin K → ℂ) (hw0 : ∀ i, w i ≠ 0) (hwinj : Function.Injective w)
    (u₁ u₂ : ℂ) (hwu₁ : ∀ i, w i ≠ u₁) (hwu₂ : ∀ i, w i ≠ u₂)
    (m : Fin K → ℕ) (v : Fin K → ℕ → ℂ) :
    ∃ P : ℂ[X], P.eval u₁ = 0 ∧ P.eval u₂ = 0 ∧
      ∀ i : Fin K, ∀ k < m i, ((deningerEulerOp δ)^[k] P).eval (w i) = v i k := by
  classical
  set Q : Fin K → ℕ → ℂ[X] := fun i j => deningerJetBasis w m u₁ u₂ i j with hQ
  set M : Fin K → ℕ → ℕ → ℂ :=
    fun i k j => ((deningerEulerOp δ)^[k] (Q i j)).eval (w i) with hM
  have hzero : ∀ i k j, k < j → M i k j = 0 := by
    intro i k j hkj
    exact deningerEulerOp_iterate_eval_lt δ (deningerJetBasis_dvd_self w m u₁ u₂ i j) hkj
  have hdiag : ∀ i k, M i k k ≠ 0 := by
    intro i k
    have h := deningerEulerOp_iterate_eval_mul_pow δ (w i) k (deningerJetMask w m u₁ u₂ i)
    have hMk : M i k k = (-δ * w i) ^ k * (Nat.factorial k : ℂ)
        * (deningerJetMask w m u₁ u₂ i).eval (w i) := h
    rw [hMk]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ?_) ?_
    · exact mul_ne_zero (neg_ne_zero.mpr hδ) (hw0 i)
    · exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    · exact deningerJetMask_eval_ne_zero hwinj hwu₁ hwu₂ i
  have hsolve : ∀ i : Fin K, ∃ a : ℕ → ℂ, ∀ k < m i,
      ∑ j ∈ Finset.range (m i), a j * M i k j = v i k := by
    intro i
    exact deningerTriangular_solvable (M i) (hzero i) (hdiag i) (v i) (m i)
  choose a ha using hsolve
  refine ⟨∑ i : Fin K, ∑ j ∈ Finset.range (m i), C (a i j) * Q i j, ?_, ?_, ?_⟩
  · simp only [eval_finsetSum, eval_mul, eval_C]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [(deningerJetBasis_eval_zero w m u₁ u₂ i j).1, mul_zero]
  · simp only [eval_finsetSum, eval_mul, eval_C]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [(deningerJetBasis_eval_zero w m u₁ u₂ i j).2, mul_zero]
  · intro i k hk
    rw [deningerEulerOp_iterate_finsetSum]
    simp only [eval_finsetSum]
    have hother : ∀ i' ∈ (Finset.univ : Finset (Fin K)), i' ≠ i →
        ((deningerEulerOp δ)^[k] (∑ j ∈ Finset.range (m i'), C (a i' j) * Q i' j)).eval (w i)
          = 0 := by
      intro i' _ hne
      rw [deningerEulerOp_iterate_finsetSum]
      simp only [eval_finsetSum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hdvd : (X - C (w i)) ^ (m i) ∣ C (a i' j) * Q i' j :=
        Dvd.dvd.mul_left (deningerJetBasis_dvd_other w m u₁ u₂ (Ne.symm hne) j) _
      exact deningerEulerOp_iterate_eval_lt δ hdvd hk
    rw [Finset.sum_eq_single i _ (fun hcon => absurd (Finset.mem_univ i) hcon)]
    · rw [deningerEulerOp_iterate_finsetSum]
      simp only [eval_finsetSum]
      have hterm : ∀ j ∈ Finset.range (m i),
          ((deningerEulerOp δ)^[k] (C (a i j) * Q i j)).eval (w i) = a i j * M i k j := by
        intro j _
        have hsmul : ∀ (c : ℂ) (R : ℂ[X]) (n : ℕ),
            (deningerEulerOp δ)^[n] (C c * R) = C c * (deningerEulerOp δ)^[n] R := by
          intro c R n
          induction n generalizing R with
          | zero => simp
          | succ n ih =>
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
            have : deningerEulerOp δ (C c * R) = C c * deningerEulerOp δ R := by
              rw [deningerEulerOp, deningerEulerOp, derivative_mul, derivative_C]
              ring
            rw [this, ih]
        rw [hsmul, eval_mul, eval_C]
      rw [Finset.sum_congr rfl hterm]
      exact ha i k hk
    · exact hother

end Interpolation

end RHTower
