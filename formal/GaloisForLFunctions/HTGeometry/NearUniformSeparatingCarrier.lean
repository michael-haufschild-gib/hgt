/-
# A near-uniform carrier direction with separated energies

The base-three direction separates the classical energies but makes the edge couplings
exponentially smaller than the onsite ones, so on the unit sphere it violates the strong-bond
condition.  Perturbing the *uniform* carrier by an exponentially small base-three profile keeps
every coordinate between one and two -- hence of order `n^{-1/2}` after normalization -- and still
separates the energies: the unperturbed part of an energy difference is an even integer, so it is
either zero, in which case the base-three part alone gives `2ε`, or at least two, in which case the
base-three part is too small to cancel it.

Main results:
* `nearUniformCarrier` — the perturbed uniform carrier direction.
* `nearUniformCarrier_coord_mem` — every carrier coordinate lies in `[1,2]`.
* `separation_nearUniformCarrier` — **the energies are separated by `2ε`**.
-/
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection

open Matrix Finset
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The integer sign of a bit. -/
def signZ (b : Bool) : ℤ := if b then -1 else 1

theorem siteSign_eq_signZ {m : ℕ} (x : Fin m → Bool) (s : Fin m) :
    siteSign x s = ((signZ (x s) : ℤ) : ℝ) := by
  by_cases h : x s <;> simp [siteSign, signZ, h]

theorem even_signZ_sub (a b : Bool) : Even (signZ a - signZ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [signZ, ha, hb]

theorem even_signZ_mul_sub (a b c d : Bool) :
    Even (signZ a * signZ b - signZ c * signZ d) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp [signZ, ha, hb, hc, hd]

variable {n : ℕ}

/-- The uniform carrier direction perturbed by an `ε`-scaled base-three onsite profile. -/
def nearUniformCarrier (n : ℕ) (eps : ℝ) : PathShell n :=
  WithLp.toLp 2 fun l =>
    match l with
    | Sum.inl sq => if sq.2 = 2 then 1 + eps * 3 ^ (sq.1 : ℕ) else 0
    | Sum.inr eab => if eab.2 = (2, 2) then 1 else 0

theorem nearUniformCarrier_offDiag (eps : ℝ) (l : PathLabel n) (hl : ¬ IsDiagLabel l) :
    nearUniformCarrier n eps l = 0 := by
  cases l with
  | inl sq =>
      have : sq.2 ≠ 2 := by simpa [IsDiagLabel] using hl
      show (if sq.2 = 2 then 1 + eps * 3 ^ (sq.1 : ℕ) else 0) = 0
      rw [if_neg this]
  | inr eab =>
      have : eab.2 ≠ (2, 2) := by simpa [IsDiagLabel] using hl
      show (if eab.2 = (2, 2) then (1 : ℝ) else 0) = 0
      rw [if_neg this]

theorem nearUniformCarrier_onsite (eps : ℝ) (s : Fin (n + 2)) :
    nearUniformCarrier n eps (Sum.inl (s, 2)) = 1 + eps * 3 ^ (s : ℕ) := by
  show (if (2 : Fin 3) = 2 then 1 + eps * 3 ^ (s : ℕ) else 0) = _
  rw [if_pos rfl]

theorem nearUniformCarrier_edge (eps : ℝ) (e : Fin (n + 1)) :
    nearUniformCarrier n eps (Sum.inr (e, (2, 2))) = 1 := by
  show (if ((2 : Fin 3), (2 : Fin 3)) = (2, 2) then (1 : ℝ) else 0) = _
  rw [if_pos rfl]

/-- Every diagonal coordinate of the direction lies between one and two. -/
theorem nearUniformCarrier_coord_mem {eps : ℝ} (heps : 0 ≤ eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 1) (l : PathLabel n) (hl : IsDiagLabel l) :
    1 ≤ nearUniformCarrier n eps l ∧ nearUniformCarrier n eps l ≤ 2 := by
  cases l with
  | inl sq =>
      have hq : sq.2 = 2 := hl
      obtain ⟨s, q⟩ := sq
      simp only at hq
      subst hq
      rw [nearUniformCarrier_onsite]
      have hpow : (3 : ℝ) ^ (s : ℕ) ≤ 3 ^ (n + 2) :=
        pow_le_pow_right₀ (by norm_num) (le_of_lt s.isLt)
      constructor
      · nlinarith [heps, pow_pos (by norm_num : (0:ℝ) < 3) (s : ℕ)]
      · nlinarith [heps, hsmall, hpow]
  | inr eab =>
      have hab : eab.2 = (2, 2) := hl
      obtain ⟨e, ab⟩ := eab
      simp only at hab
      subst hab
      rw [nearUniformCarrier_edge]
      norm_num

theorem pathDiagEnergy_nearUniformCarrier (eps : ℝ)
    (x : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (nearUniformCarrier n eps) x
      = (∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign x s)
        + ∑ e : Fin (n + 1), siteSign x e.castSucc * siteSign x e.succ := by
  rw [pathDiagEnergy]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => by
      rw [nearUniformCarrier_onsite, zSetSign_singleton_eq]
  · exact Finset.sum_congr rfl fun e _ => by
      rw [nearUniformCarrier_edge, zSetSign_pair_eq, one_mul]

/-- The integer part of an energy difference. -/
def energyIntDiff (x y : FiniteQubitConfiguration (Fin (n + 2))) : ℤ :=
  (∑ s : Fin (n + 2), (signZ (x s) - signZ (y s)))
    + ∑ e : Fin (n + 1), (signZ (x e.castSucc) * signZ (x e.succ)
        - signZ (y e.castSucc) * signZ (y e.succ))

theorem even_energyIntDiff (x y : FiniteQubitConfiguration (Fin (n + 2))) :
    Even (energyIntDiff x y) := by
  refine Even.add (Finset.even_sum _ fun s _ => even_signZ_sub _ _)
    (Finset.even_sum _ fun e _ => even_signZ_mul_sub _ _ _ _)

theorem pathDiagEnergy_sub_eq (eps : ℝ) (x y : FiniteQubitConfiguration (Fin (n + 2))) :
    pathDiagEnergy (nearUniformCarrier n eps) x - pathDiagEnergy (nearUniformCarrier n eps) y
      = ((energyIntDiff x y : ℤ) : ℝ)
        + eps * ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := by
  rw [pathDiagEnergy_nearUniformCarrier, pathDiagEnergy_nearUniformCarrier, energyIntDiff]
  push_cast
  have h1 : (∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign x s)
        - ∑ s : Fin (n + 2), (1 + eps * 3 ^ (s : ℕ)) * siteSign y s
      = (∑ s : Fin (n + 2), ((signZ (x s) : ℝ) - (signZ (y s) : ℝ)))
        + eps * ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [siteSign_eq_signZ x s, siteSign_eq_signZ y s]
    ring
  have h2 : (∑ e : Fin (n + 1), siteSign x e.castSucc * siteSign x e.succ)
        - ∑ e : Fin (n + 1), siteSign y e.castSucc * siteSign y e.succ
      = ∑ e : Fin (n + 1), ((signZ (x e.castSucc) : ℝ) * (signZ (x e.succ) : ℝ)
          - (signZ (y e.castSucc) : ℝ) * (signZ (y e.succ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [siteSign_eq_signZ x e.castSucc, siteSign_eq_signZ x e.succ,
      siteSign_eq_signZ y e.castSucc, siteSign_eq_signZ y e.succ]
  linarith [h1, h2]

/-- **The near-uniform carrier separates the energies.**  The unperturbed part of an energy
difference is an even integer: if it vanishes the base-three part alone gives `2ε`, and otherwise it
is at least two while the base-three part is below `2/3`. -/
theorem separation_nearUniformCarrier {eps : ℝ} (heps : 0 < eps)
    (hsmall : eps * 3 ^ (n + 2) ≤ 2 / 3)
    {x y : FiniteQubitConfiguration (Fin (n + 2))} (hxy : x ≠ y) :
    2 * eps ≤ |pathDiagEnergy (nearUniformCarrier n eps) x
      - pathDiagEnergy (nearUniformCarrier n eps) y| := by
  classical
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
    K = ∑ s : Fin (n + 2), (3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s) := ⟨_, rfl⟩
  have hK2 : 2 ≤ |K| := by rw [hKdef]; exact two_le_abs_sum_signDiff hxy
  have hKle : |K| ≤ 3 ^ (n + 2) - 1 := by
    rw [hKdef]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ s ∈ (Finset.univ : Finset (Fin (n + 2))),
        |(3 : ℝ) ^ (s : ℕ) * (siteSign x s - siteSign y s)| ≤ 2 * 3 ^ (s : ℕ) := by
      intro s _
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ (s : ℕ))]
      have := abs_siteSign_sub_le x y s
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) (s : ℕ)]
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    have hval : ∑ s : Fin (n + 2), (2 : ℝ) * 3 ^ (s : ℕ)
        = ∑ j ∈ Finset.range (n + 2), (2 : ℝ) * 3 ^ j := by
      rw [Finset.sum_range fun j => (2 : ℝ) * 3 ^ j]
    rw [hval, sum_lt_three_pow]
  have hsplit := pathDiagEnergy_sub_eq (n := n) eps x y
  rw [← hKdef] at hsplit
  rcases eq_or_ne (energyIntDiff x y) 0 with hz | hz
  · rw [hsplit, hz]
    push_cast
    rw [zero_add, abs_mul, abs_of_pos heps]
    nlinarith [hK2, heps]
  · have heven := even_energyIntDiff x y
    have habs2 : (2 : ℤ) ≤ |energyIntDiff x y| := by
      obtain ⟨t, ht⟩ := heven
      have htne : t ≠ 0 := by
        intro h
        rw [h] at ht
        exact hz (by omega)
      have h1t : 1 ≤ |t| := by
        have := abs_pos.mpr htne
        omega
      have hgt : |energyIntDiff x y| = 2 * |t| := by
        rw [ht, show t + t = 2 * t by ring, abs_mul]
        norm_num
      omega
    have habs2R : (2 : ℝ) ≤ |((energyIntDiff x y : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast habs2
    have hepsK : |eps * K| ≤ 2 / 3 := by
      rw [abs_mul, abs_of_pos heps]
      have hpos : (0 : ℝ) < 3 ^ (n + 2) := by positivity
      nlinarith [hKle, heps.le, hsmall, abs_nonneg K]
    have hsmalleps : 2 * eps ≤ 2 / 3 := by
      have hone : (1 : ℝ) ≤ 3 ^ (n + 2) := one_le_pow₀ (by norm_num)
      nlinarith [hsmall, heps.le]
    rw [hsplit]
    have htri := abs_sub_abs_le_abs_sub (((energyIntDiff x y : ℤ) : ℝ)) (-(eps * K))
    rw [abs_neg, sub_neg_eq_add] at htri
    linarith [htri, habs2R, hepsK, hsmalleps]

end GaloisForLFunctions.HTGeometry

end
