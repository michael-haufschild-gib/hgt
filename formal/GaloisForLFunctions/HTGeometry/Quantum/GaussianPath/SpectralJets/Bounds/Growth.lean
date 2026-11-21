import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Polynomial and exponential bounds in the Hilbert-space dimension -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A natural sequence bounded by a fixed power of the dimension 2^(k+3). -/
def PolynomialInDimension (s : ℕ → ℕ) : Prop := ∃ a : ℕ, ∀ k : ℕ, s k ≤ (2^(k+3))^a

/-- A real sequence whose magnitude is at most two raised to a polynomial
in the Hilbert-space dimension. -/
def LogPolynomialInDimension (f : ℕ → ℝ) : Prop :=
  ∃ s : ℕ → ℕ, PolynomialInDimension s ∧ ∀ k, |f k| ≤ (2:ℝ)^(s k)

namespace PolynomialInDimension
theorem dim : PolynomialInDimension (fun k => 2^(k+3)) := ⟨1,fun _ => by rw [pow_one]⟩

private theorem two_le_dim (k : ℕ) : 2 ≤ 2^(k+3) :=
  (by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ k+3))

theorem const (c : ℕ) : PolynomialInDimension (fun _ => c) :=
  ⟨c,fun k => (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left (two_le_dim k) c)⟩

theorem mono {s t : ℕ → ℕ} (h : PolynomialInDimension t) (hst : ∀ k, s k ≤ t k) :
    PolynomialInDimension s := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,fun k => (hst k).trans (ha k)⟩

theorem mul {s t : ℕ → ℕ} (hs : PolynomialInDimension s) (ht : PolynomialInDimension t) :
    PolynomialInDimension (fun k => s k*t k) := by
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := ht
  exact ⟨a+b,fun k => (Nat.mul_le_mul (ha k) (hb k)).trans_eq (pow_add _ _ _).symm⟩

theorem add {s t : ℕ → ℕ} (hs : PolynomialInDimension s) (ht : PolynomialInDimension t) :
    PolynomialInDimension (fun k => s k+t k) := by
  obtain ⟨a,ha⟩ := hs
  obtain ⟨b,hb⟩ := ht
  refine ⟨max a b+1,fun k => ?_⟩
  let D := 2^(k+3)
  have hD : 0 < D := by dsimp [D]; positivity
  have h₁ : s k ≤ D^max a b := (ha k).trans (Nat.pow_le_pow_right hD (le_max_left _ _))
  have h₂ : t k ≤ D^max a b := (hb k).trans (Nat.pow_le_pow_right hD (le_max_right _ _))
  calc s k+t k ≤ D^max a b+D^max a b := Nat.add_le_add h₁ h₂
       _ = D^max a b*2 := (mul_two _).symm
       _ ≤ D^max a b*D := Nat.mul_le_mul_left _ (two_le_dim k)
       _ = _ := (pow_succ D _).symm

theorem sites : PolynomialInDimension (fun k => k+3) := dim.mono fun k => (Nat.lt_two_pow_self (n := k+3)).le

theorem square {s : ℕ → ℕ} (hs : PolynomialInDimension s) :
    PolynomialInDimension (fun k => s k^2) := by simpa only [pow_two] using hs.mul hs

end PolynomialInDimension

namespace LogPolynomialInDimension
theorem natCast {s : ℕ → ℕ} (hs : PolynomialInDimension s) :
    LogPolynomialInDimension (fun k => (s k:ℝ)) := by
  refine ⟨s,hs,fun k => ?_⟩
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  change (s k : ℝ) ≤ (2:ℝ)^(s k)
  exact_mod_cast (Nat.lt_two_pow_self (n := s k)).le

theorem const (c : ℕ) : LogPolynomialInDimension (fun _ => (c:ℝ)) := natCast (PolynomialInDimension.const c)

theorem twoPow {s : ℕ → ℕ} (hs : PolynomialInDimension s) :
    LogPolynomialInDimension (fun k => (2:ℝ)^(s k)) := ⟨s,hs,fun k => (abs_of_nonneg (by positivity)).le⟩

theorem mono {f g : ℕ → ℝ} (hg : LogPolynomialInDimension g) (hf : ∀ k, 0 ≤ f k) (h : ∀ k, f k ≤ g k) :
    LogPolynomialInDimension f := by
  obtain ⟨s,hs,hg⟩ := hg
  exact ⟨s,hs,fun k => (abs_of_nonneg (hf k)).le.trans ((h k).trans ((le_abs_self _).trans (hg k)))⟩

theorem abs {f : ℕ → ℝ} (hf : LogPolynomialInDimension f) : LogPolynomialInDimension (fun k => |f k|) := by
  obtain ⟨s,hs,hf⟩ := hf
  exact ⟨s,hs,fun k => (abs_abs _).le.trans (hf k)⟩

theorem mul {f g : ℕ → ℝ} (hf : LogPolynomialInDimension f) (hg : LogPolynomialInDimension g) :
    LogPolynomialInDimension (fun k => f k*g k) := by
  obtain ⟨s,hs,hf⟩ := hf
  obtain ⟨t,ht,hg⟩ := hg
  refine ⟨_,hs.add ht,fun k => ?_⟩
  rw [abs_mul,pow_add]
  exact mul_le_mul (hf k) (hg k) (abs_nonneg _) (by positivity)

theorem add {f g : ℕ → ℝ} (hf : LogPolynomialInDimension f) (hg : LogPolynomialInDimension g) :
    LogPolynomialInDimension (fun k => f k+g k) := by
  obtain ⟨s,hs,hf⟩ := hf
  obtain ⟨t,ht,hg⟩ := hg
  refine ⟨_,(hs.add ht).add (PolynomialInDimension.const 1),fun k => ?_⟩
  have h₁ := (hf k).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (s k) (t k)))
  have h₂ := (hg k).trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_left (t k) (s k)))
  exact (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq ((mul_two _).symm.trans (pow_succ _ _).symm))

theorem pow {f : ℕ → ℝ} {s : ℕ → ℕ} (hf : LogPolynomialInDimension f) (hs : PolynomialInDimension s) :
    LogPolynomialInDimension (fun k => (f k)^(s k)) := by
  obtain ⟨t,ht,hf⟩ := hf
  refine ⟨_,ht.mul hs,fun k => ?_⟩
  rw [abs_pow,pow_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) (hf k) _

theorem factorial {s : ℕ → ℕ} (hs : PolynomialInDimension s) :
    LogPolynomialInDimension (fun k => ((s k).factorial:ℝ)) :=
  ((natCast hs).pow hs).mono (fun _ => Nat.cast_nonneg _) fun k => by exact_mod_cast Nat.factorial_le_pow (s k)

/-- One fixed dimension exponent works at all prefix lengths. -/
theorem bound {f : ℕ → ℝ} (hf : LogPolynomialInDimension f) :
    ∃ c : ℕ, ∀ k : ℕ, f k ≤ (2:ℝ)^((2^(k+3):ℕ)^c) := by
  obtain ⟨s,⟨c,hc⟩,hf⟩ := hf
  exact ⟨c,fun k => (le_abs_self _).trans ((hf k).trans (pow_le_pow_right₀ (by norm_num) (hc k)))⟩

end LogPolynomialInDimension
end
end GaloisForLFunctions.HTGeometry.SpectralJets
