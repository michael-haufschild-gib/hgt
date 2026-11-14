import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Integral Lambert coefficients and exact multicover recovery

The arithmetic mechanism of Huq-Kuruvilla--Schultz, arXiv:2611.13126,
Theorem 4.5, is the divisor transform `b(n)=Σ_{d∣n} d^k N(d)`.
Möbius inversion recovers `n^k N(n)` exactly. An integer coefficient
sequence has integer multicover weights precisely when these recovered
integers are divisible by `n^k`; integrality of the original sequence alone
does not supply this divisibility.
-/

noncomputable section

namespace GaloisForLFunctions.EisensteinDegeneration

open scoped ArithmeticFunction.Moebius

/-- Coefficients of the weight-`k` Lambert series. -/
def multicover (k : ℕ) (w : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) ^ k * w d

/-- Möbius extraction of the primitive coefficient. -/
def primitiveCoefficient (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, μ (n / d) * b d

/-- The formal Lambert series has an integral coefficient at every degree. -/
def multicoverSeries (k : ℕ) (w : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (multicover k w)

@[simp] theorem coeff_multicoverSeries (k : ℕ) (w : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (multicoverSeries k w) = multicover k w n := by
  simp [multicoverSeries]

@[simp] theorem multicover_zero (k : ℕ) (w : ℕ → ℤ) : multicover k w 0 = 0 := by
  simp [multicover]

/-- Exact extraction at every positive degree, with no periodicity assumption. -/
theorem primitiveCoefficient_multicover (k : ℕ) (w : ℕ → ℤ) (n : ℕ) :
    primitiveCoefficient (multicover k w) (n + 1) = (n + 1 : ℤ) ^ k * w (n + 1) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (show ∀ m : ℕ, m > 0 → ∑ d ∈ m.divisors, (d : ℤ) ^ k * w d = multicover k w m
      from fun _ _ => rfl)) (n + 1) (Nat.succ_pos n)
  rwa [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℤ) * multicover k w b)] at h

/-- All positive weights are uniquely determined by the complete coefficient sequence. -/
theorem multicover_injective_positive (k : ℕ) (u v : ℕ → ℤ) :
    (∀ n : ℕ, multicover k u (n + 1) = multicover k v (n + 1)) ↔
      ∀ n : ℕ, u (n + 1) = v (n + 1) := by
  constructor
  · intro h n
    have hb : multicover k u = multicover k v := by
      funext m
      cases m with
      | zero => simp
      | succ m => exact h m
    have he := congrArg (fun b => primitiveCoefficient b (n + 1)) hb
    rw [primitiveCoefficient_multicover, primitiveCoefficient_multicover] at he
    exact mul_left_cancel₀ (pow_ne_zero _ (by omega : (n + 1 : ℤ) ≠ 0)) he
  · intro h n
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_of_mem_divisors hd).ne'
    rw [h e]

/-- Exact arithmetic criterion for integral multicover weights. -/
theorem exists_integral_multicover_iff (k : ℕ) (b : ℕ → ℤ) :
    (∃ w : ℕ → ℤ, ∀ n : ℕ, multicover k w (n + 1) = b (n + 1)) ↔
      ∀ n : ℕ, (n + 1 : ℤ) ^ k ∣ primitiveCoefficient b (n + 1) := by
  constructor
  · rintro ⟨w, hw⟩ n
    have he : primitiveCoefficient b (n + 1) =
        primitiveCoefficient (multicover k w) (n + 1) := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_of_mem_divisors hd).ne'
      rw [hw e]
    rw [he, primitiveCoefficient_multicover]
    exact dvd_mul_right _ _
  · intro h
    let w : ℕ → ℤ := fun n => primitiveCoefficient b n / (n : ℤ) ^ k
    refine ⟨w, ?_⟩
    have hinv : ∀ m : ℕ, m > 0 →
        ∑ x ∈ m.divisorsAntidiagonal, (μ x.1 : ℤ) * b x.2 = (m : ℤ) ^ k * w m := by
      intro m hm
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      rw [Nat.sum_divisorsAntidiagonal' (fun a d => (μ a : ℤ) * b d)]
      exact (Int.mul_ediv_cancel' (h n)).symm
    exact fun n => ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr hinv
      (n + 1) (Nat.succ_pos n)

/-- The period-three Eisenstein weights of the projective-plane example. -/
def planeEisensteinWeight (n : ℕ) : ℤ :=
  if n % 3 = 0 then 0 else if n % 3 = 1 then -9 else 9

/-- The period-two Eisenstein weights of the projective-three-space example. -/
def spaceEisensteinWeight (n : ℕ) : ℤ := if n % 2 = 0 then -40 else -80

theorem planeEisensteinWeight_periodic (n : ℕ) :
    planeEisensteinWeight (n + 3) = planeEisensteinWeight n := by
  simp only [planeEisensteinWeight, Nat.add_mod_right]

theorem spaceEisensteinWeight_periodic (n : ℕ) :
    spaceEisensteinWeight (n + 2) = spaceEisensteinWeight n := by
  simp only [spaceEisensteinWeight, Nat.add_mod_right]

/-- Möbius extraction recovers the cubic-family weights at every degree. -/
theorem planeEisenstein_primitive (n : ℕ) :
    primitiveCoefficient (multicover 2 planeEisensteinWeight) (n + 1) =
      (n + 1 : ℤ) ^ 2 * planeEisensteinWeight (n + 1) :=
  primitiveCoefficient_multicover _ _ _

/-- Möbius extraction recovers the quartic-family weights at every degree. -/
theorem spaceEisenstein_primitive (n : ℕ) :
    primitiveCoefficient (multicover 3 spaceEisensteinWeight) (n + 1) =
      (n + 1 : ℤ) ^ 3 * spaceEisensteinWeight (n + 1) :=
  primitiveCoefficient_multicover _ _ _

end GaloisForLFunctions.EisensteinDegeneration
