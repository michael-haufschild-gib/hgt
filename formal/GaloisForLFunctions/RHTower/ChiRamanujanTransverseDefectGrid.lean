import GaloisForLFunctions.RHTower.ChiRamanujanCriticalGridSource
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Signed local transverse-defect source

The literal prime-square base reduces exactly to its p-divisible nodes.
Their product pushforward retains a negative centered zero atom together
with its surrounding signed mass. All four restricted base/tag placements
are evaluated for every complex test. The complete base/base physical
prime-frequency response is nonzero and negative. No global growing-profile
cancellation, full tagged CRT product, or RH consequence is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace
local instance (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩

def criticalDefectBase (p : Nat.Primes) (a : ZMod (p : ℕ)) : ℂ :=
  (if a=0 then 1 else 0)-(p : ℂ)⁻¹

def criticalDefectTag (p : Nat.Primes) : ℂ := (p : ℂ)⁻¹-(p : ℂ)⁻¹^2

def criticalDefectCenter (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) : ℂ :=
  Φ 0-(p : ℂ)⁻¹*∑ a, Φ a

private lemma sum_center (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    ∑ a, criticalDefectBase p a*Φ a = criticalDefectCenter p Φ := by
  simp [criticalDefectBase,criticalDefectCenter,sub_mul,Finset.sum_sub_distrib,
    ← Finset.mul_sum,ite_mul]

private lemma row (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) (a : ZMod (p : ℕ)) :
    (∑ b, Φ (a*b)) = (∑ b, Φ b)+
      (if a=0 then 1 else 0)*((p : ℂ)*Φ 0-∑ b, Φ b) := by
  by_cases h : a=0
  · simp [h]
  · rw [if_neg h,zero_mul,add_zero]
    exact Equiv.sum_comp (Equiv.mulLeft₀ a h) Φ

/-- Complete multiplicative pushforward, including its singular zero fibre. -/
theorem criticalDefect_unweighted (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, Φ (a*b)) = (p : ℂ)*Φ 0+((p : ℂ)-1)*∑ b, Φ b := by
  simp_rw [row]
  simp only [Finset.sum_add_distrib,← Finset.sum_mul,Finset.sum_const,
    Finset.card_univ,ZMod.card,nsmul_eq_mul]
  simp
  ring

/-- The two untagged source factors retain a negative centered defect law. -/
theorem criticalDefect_base_base (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectBase p a*criticalDefectBase p b*Φ (a*b)) =
      -(1-(p : ℂ)⁻¹)*criticalDefectCenter p Φ := by
  have hi (a : ZMod (p : ℕ)) :
      (∑ b, criticalDefectBase p b*Φ (a*b)) =
        Φ 0-(p : ℂ)⁻¹*∑ b, Φ (a*b) := by
    simpa only [criticalDefectCenter,mul_zero] using
      sum_center p (fun b => Φ (a*b))
  simp_rw [mul_assoc,← Finset.mul_sum,hi]
  rw [sum_center,criticalDefectCenter]
  simp only [zero_mul,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,criticalDefect_unweighted]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,criticalDefectCenter]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp
  ring

private lemma constant_base (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectBase p b*Φ (a*b)) =
      ((p : ℂ)-1)*criticalDefectCenter p Φ := by
  simp_rw [sum_center,criticalDefectCenter]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,criticalDefect_unweighted]
  simp only [mul_zero,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp
  ring

theorem criticalDefect_tag_base (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectTag p*criticalDefectBase p b*Φ (a*b)) =
      criticalDefectTag p*((p : ℂ)-1)*criticalDefectCenter p Φ := by
  simp_rw [mul_assoc,← Finset.mul_sum]
  rw [constant_base]

theorem criticalDefect_base_tag (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectBase p a*criticalDefectTag p*Φ (a*b)) =
      criticalDefectTag p*((p : ℂ)-1)*criticalDefectCenter p Φ := by
  rw [Finset.sum_comm]
  simpa only [mul_comm] using criticalDefect_tag_base p Φ

theorem criticalDefect_tag_tag (p : Nat.Primes) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectTag p*criticalDefectTag p*Φ (a*b)) =
      criticalDefectTag p^2*((p : ℂ)*Φ 0+((p : ℂ)-1)*∑ a, Φ a) := by
  simp_rw [← Finset.mul_sum]
  rw [criticalDefect_unweighted,pow_two]

def criticalDefectGridNode (p : Nat.Primes) (a : ZMod (p : ℕ)) : Fin ((p : ℕ)^2) :=
  ⟨(p : ℕ)*a.val, by have := a.val_lt; have := p.property.pos; nlinarith⟩

theorem criticalDefectGridNode_base (p : Nat.Primes) (a : ZMod (p : ℕ)) :
    (ramanujanGridBase p (criticalDefectGridNode p a) : ℂ)=criticalDefectBase p a := by
  have he : (p : ℕ)*a.val=0 ↔ a=0 := by simp [p.property.ne_zero,ZMod.val_eq_zero]
  simp only [ramanujanGridBase,criticalDefectGridNode,he,dvd_mul_right,if_true,mul_one]
  push_cast
  split_ifs <;> simp_all [criticalDefectBase]

theorem criticalDefectGridNode_tag (p : Nat.Primes) (a : ZMod (p : ℕ)) :
    (ramanujanGridTag p (criticalDefectGridNode p a) : ℂ)=criticalDefectTag p := by
  simp [ramanujanGridTag,criticalDefectGridNode,criticalDefectTag,inv_pow]

/-- Complete frequency law, with its zero mode and every nonzero mode. -/
theorem criticalDefect_base_base_fourier (p : Nat.Primes) (n : ZMod (p : ℕ)) :
    (∑ a, ∑ b, criticalDefectBase p a*criticalDefectBase p b*
      ZMod.stdAddChar ((a*b)*n)) =
      if n=0 then 0 else -(1-(p : ℂ)⁻¹) := by
  rw [criticalDefect_base_base p (fun x => ZMod.stdAddChar (x*n)),criticalDefectCenter,
    RHTower.Sieve.sum_stdAddChar_mul]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  by_cases hn : n=0 <;> simp [hn,hp]

/-- Exact physical prime frequency on the p-multiple prime-square nodes. -/
theorem criticalDefectGridNode_phase (p : Nat.Primes) (a b : ZMod (p : ℕ)) :
    ramanujanFourierPhase (p : ℕ)
      ((((criticalDefectGridNode p a).val : ℝ)/((p : ℕ)^2 : ℕ))*
       (((criticalDefectGridNode p b).val : ℝ)/((p : ℕ)^2 : ℕ))) =
      ZMod.stdAddChar (a*b) := by
  have he := ZMod.stdAddChar_coe (N := (p : ℕ)) ((a.val*b.val : ℕ) : ℤ)
  simp only [Nat.cast_mul,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val] at he
  rw [he,ramanujanFourierPhase]
  congr 1
  simp only [criticalDefectGridNode,Nat.cast_mul,Nat.cast_pow,Int.cast_natCast]
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp

/-- Literal local prime-square source response, without a zero-mode assumption. -/
theorem criticalDefectGridNode_bilinear (p : Nat.Primes) :
    (∑ a : ZMod (p : ℕ), ∑ b : ZMod (p : ℕ),
      (ramanujanGridBase p (criticalDefectGridNode p a) : ℂ)*
      (ramanujanGridBase p (criticalDefectGridNode p b) : ℂ)*
      ramanujanFourierPhase (p : ℕ)
        ((((criticalDefectGridNode p a).val : ℝ)/((p : ℕ)^2 : ℕ))*
         (((criticalDefectGridNode p b).val : ℝ)/((p : ℕ)^2 : ℕ)))) =
      -(1-(p : ℂ)⁻¹) := by
  simp only [criticalDefectGridNode_base,criticalDefectGridNode_phase]
  simpa using criticalDefect_base_base_fourier p 1

/-- These coordinates exhaust exactly the p-multiple support of the literal base. -/
theorem criticalDefectGridNode_range (p : Nat.Primes) (k : Fin ((p : ℕ)^2)) :
    (∃ a, criticalDefectGridNode p a=k) ↔ (p : ℕ) ∣ k.val := by
  constructor
  · rintro ⟨a,rfl⟩
    exact dvd_mul_right _ _
  · intro hk
    have hlt : k.val/(p : ℕ) < (p : ℕ) := by
      apply (Nat.div_lt_iff_lt_mul p.property.pos).mpr
      simpa only [pow_two] using k.isLt
    refine ⟨(k.val/(p : ℕ) : ℕ),?_⟩
    apply Fin.ext
    change (p : ℕ)*((k.val/(p : ℕ) : ℕ) : ZMod (p : ℕ)).val=k.val
    rw [ZMod.val_cast_of_lt hlt,Nat.mul_div_cancel' hk]

private lemma node_injective (p : Nat.Primes) : Function.Injective (criticalDefectGridNode p) := by
  intro a b h
  apply ZMod.val_injective (p : ℕ)
  have he := congrArg Fin.val h
  change (p : ℕ)*a.val=(p : ℕ)*b.val at he
  exact Nat.eq_of_mul_eq_mul_left p.property.pos he

/-- Exact reduction of the entire prime-square base, for every test. -/
theorem criticalDefectGridBase_sum (p : Nat.Primes) (F : Fin ((p : ℕ)^2) → ℂ) :
    (∑ k, (ramanujanGridBase p k : ℂ)*F k) =
      ∑ a, criticalDefectBase p a*F (criticalDefectGridNode p a) := by
  symm
  apply Fintype.sum_of_injective (criticalDefectGridNode p) (node_injective p)
  · intro k hk
    have hn : ¬ (p : ℕ) ∣ k.val := fun h => hk ((criticalDefectGridNode_range p k).mpr h)
    have hz : k.val ≠ 0 := fun h => hn (h ▸ dvd_zero _)
    simp [ramanujanGridBase,hn,hz]
  · intro a
    rw [criticalDefectGridNode_base]

/-- Complete prime-square bilinear source, including every zero and nonprimitive node. -/
theorem criticalGridBase_bilinear_prime (p : Nat.Primes) :
    (∑ k : Fin ((p : ℕ)^2), ∑ l : Fin ((p : ℕ)^2),
      (ramanujanGridBase p k : ℂ)*(ramanujanGridBase p l : ℂ)*
        ramanujanFourierPhase (p : ℕ)
          (((k.val : ℝ)/((p : ℕ)^2 : ℕ))*((l.val : ℝ)/((p : ℕ)^2 : ℕ)))) =
      -(1-(p : ℂ)⁻¹) := by
  simp_rw [mul_assoc,← Finset.mul_sum,criticalDefectGridBase_sum]
  simp_rw [Finset.mul_sum,← mul_assoc]
  simpa only [criticalDefectGridNode_base] using criticalDefectGridNode_bilinear p

end RHTower.BAGTrace
