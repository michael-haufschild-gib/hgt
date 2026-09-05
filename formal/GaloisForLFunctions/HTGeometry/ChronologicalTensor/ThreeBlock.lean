import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Foundations
import Mathlib.Data.Fintype.BigOperators

/-!
# Three-block factorization of genuine endpoint pairings

A bijection from two copies of Fin d to the endpoint set enumerates an
oriented perfect pairing. On three fixed endpoint-color classes, each
pairing is zero or a common monomial times an orientation sign. Incidence
counts force the exponents; they are proved from the bijection.

The resulting absolute-increment inequality applies to every coefficient
family. For chronological two-gap faces the colors are consecutive blocks;
connecting this algebraic statement to the gap capacity is a separate step.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def threeBlockPosition (u v : ℝ) : Fin 3 → ℝ := ![0,u,u+v]

def colorPresence (a z : Fin 3) : ℕ := if a = z then 1 else 0

def missingColor (a b z : Fin 3) : ℕ := if a ≠ z ∧ b ≠ z then 1 else 0

def threeBlockOrientation (a b : Fin 3) : ℝ :=
  if a.val < b.val then 1 else if b.val < a.val then -1 else 0

def endpointColorCount {d : ℕ} (colors : Fin (2*d) → Fin 3) (z : Fin 3) : ℕ :=
  ∑ i, colorPresence (colors i) z

def enumeratedPairingValue {d : ℕ} (e : (Fin d ⊕ Fin d) ≃ Fin (2*d))
    (x : Fin (2*d) → ℝ) : ℝ := ∏ i, (x (e (Sum.inr i))-x (e (Sum.inl i)))

def pairingOrientation {d : ℕ} (e : (Fin d ⊕ Fin d) ≃ Fin (2*d))
    (colors : Fin (2*d) → Fin 3) : ℝ :=
  ∏ i, threeBlockOrientation (colors (e (Sum.inl i))) (colors (e (Sum.inr i)))

def threeBlockMonomial {d : ℕ} (colors : Fin (2*d) → Fin 3) (u v : ℝ) : ℝ :=
  u^(d-endpointColorCount colors 2)*v^(d-endpointColorCount colors 0)*
    (u+v)^(d-endpointColorCount colors 1)

theorem endpointColorCount_pairing {d : ℕ} (e : (Fin d ⊕ Fin d) ≃ Fin (2*d))
    (colors : Fin (2*d) → Fin 3) (z : Fin 3) :
    endpointColorCount colors z = ∑ i : Fin d,
      (colorPresence (colors (e (Sum.inl i))) z+colorPresence (colors (e (Sum.inr i))) z) := by
  rw [endpointColorCount,← Equiv.sum_comp e,Fintype.sum_sum_type,Finset.sum_add_distrib]

theorem threeBlock_difference (a b : Fin 3) (u v : ℝ) :
    threeBlockPosition u v b-threeBlockPosition u v a =
      threeBlockOrientation a b*u^(missingColor a b 2)*v^(missingColor a b 0)*
        (u+v)^(missingColor a b 1) := by
  fin_cases a <;> fin_cases b <;>
    simp [threeBlockPosition,threeBlockOrientation,missingColor]

theorem enumeratedPairing_threeBlock_factor {d : ℕ}
    (e : (Fin d ⊕ Fin d) ≃ Fin (2*d)) (colors : Fin (2*d) → Fin 3) (u v : ℝ) :
    enumeratedPairingValue e (fun i => threeBlockPosition u v (colors i)) =
      pairingOrientation e colors*threeBlockMonomial colors u v := by
  classical
  by_cases hproper : ∀ i : Fin d, colors (e (Sum.inl i)) ≠ colors (e (Sum.inr i))
  · have hexponent (z : Fin 3) :
        (∑ i : Fin d, missingColor (colors (e (Sum.inl i))) (colors (e (Sum.inr i))) z) =
          d-endpointColorCount colors z := by
      have hi (i : Fin d) :
          missingColor (colors (e (Sum.inl i))) (colors (e (Sum.inr i))) z+
            (colorPresence (colors (e (Sum.inl i))) z+colorPresence (colors (e (Sum.inr i))) z) = 1 := by
        have hn := hproper i
        by_cases hl : colors (e (Sum.inl i)) = z
        · have hr : colors (e (Sum.inr i)) ≠ z := by intro hr; exact hn (hl.trans hr.symm)
          simp [missingColor,colorPresence,hl,hr]
        · by_cases hr : colors (e (Sum.inr i)) = z
          · simp [missingColor,colorPresence,hl,hr]
          · simp [missingColor,colorPresence,hl,hr]
      have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hi i)
      rw [Finset.sum_add_distrib,← endpointColorCount_pairing e colors z] at hh
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hh
      omega
    unfold enumeratedPairingValue
    simp only [threeBlock_difference,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
    rw [hexponent 2,hexponent 0,hexponent 1]
    unfold pairingOrientation threeBlockMonomial
    ring
  · push Not at hproper
    obtain ⟨i,hi⟩ := hproper
    have hv : enumeratedPairingValue e (fun i => threeBlockPosition u v (colors i)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      dsimp only
      rw [hi,sub_self]
    have ho : pairingOrientation e colors = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [threeBlockOrientation,hi]
    rw [hv,ho,zero_mul]

def enumeratedPairingFamilyValue {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (x : Fin (2*d) → ℝ) : ℝ := ∑ j, c j*enumeratedPairingValue (E j) x

def threeBlockAmplitude {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (colors : Fin (2*d) → Fin 3) : ℝ := ∑ j, c j*pairingOrientation (E j) colors

theorem enumeratedPairingFamily_threeBlock_factor {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (colors : Fin (2*d) → Fin 3) (u v : ℝ) :
    enumeratedPairingFamilyValue E c (fun i => threeBlockPosition u v (colors i)) =
      threeBlockAmplitude E c colors*threeBlockMonomial colors u v := by
  simp only [enumeratedPairingFamilyValue,enumeratedPairing_threeBlock_factor,← mul_assoc,
    ← Finset.sum_mul,threeBlockAmplitude]

theorem threeBlockMonomial_absolute (d : ℕ) (colors : Fin (2*d) → Fin 3) (u v : ℝ) :
    |threeBlockMonomial colors u v| ≤ |threeBlockMonomial colors (|u|) (|v|)| := by
  unfold threeBlockMonomial
  simp only [abs_mul,abs_pow,abs_abs,abs_of_nonneg (add_nonneg (abs_nonneg u) (abs_nonneg v))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le u v) _) (by positivity)

theorem enumeratedPairingFamily_threeBlock_absolute {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (colors : Fin (2*d) → Fin 3) (u v : ℝ) :
    |enumeratedPairingFamilyValue E c (fun i => threeBlockPosition u v (colors i))| ≤
      |enumeratedPairingFamilyValue E c (fun i => threeBlockPosition |u| |v| (colors i))| := by
  rw [enumeratedPairingFamily_threeBlock_factor,enumeratedPairingFamily_threeBlock_factor,
    abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_left (threeBlockMonomial_absolute d colors u v) (abs_nonneg _)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
