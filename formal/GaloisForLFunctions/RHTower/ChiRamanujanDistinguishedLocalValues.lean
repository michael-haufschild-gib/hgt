import GaloisForLFunctions.RHTower.ChiRamanujanWeightedDistinguishedCubic
import GaloisForLFunctions.RHTower.ChiRamanujanTransverseDefectGrid

/-!
# Explicit local values of the distinguished critical source

* With `h = z/(1-z)` and the local coefficient `c_z`, the finite valuation diagonals are
  `D_{-1} = -h(x⁻¹+y⁻¹)`, `D_0 = 1-h(y/x+x/y)`, `D_1 = x+y-h(y²/x+x²/y)`, and
  `c_z(t-1) = c_z(t) + h·1_{t=-1} - (1+h)·1_{t=0}` for every integer `t`.
* In the primitive prime-square stratum (`p ∤ k`) the local grid base vanishes and the local
  grid tag equals `-1/p²`.
* The multiplicative pushforward of the product of two centred bases on `𝔽_p` is
  `-(1-1/p)` times the centred base: mass `-(p-1)²/p²` at `0` and `(p-1)/p²` at every nonzero
  point.  The grid-node map `a ↦ p·a` into `ℤ/p²` is injective.
-/

noncomputable section
open Complex
namespace RHTower.BAGTrace

private theorem complexCoefficient_below (z : ℂ) {i : ℤ} (hi : i < -1) :
    complexCoefficient z i = 0 := by
  simp [complexCoefficient, show i ≠ -1 by omega, show ¬ 0 ≤ i by omega]

/-- `D_{-1} = -h(x⁻¹+y⁻¹)`. -/
theorem weightedValuationDiagonal_neg_one_hasSum (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y (-1)) (-(z/(1-z))*(x⁻¹+y⁻¹)) := by
  have hs : Finset.Icc (-1 : ℤ) 0 = {-1,0} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y (-1)
  norm_num only [neg_add_cancel,hs,Finset.sum_insert,Finset.sum_singleton,
    Finset.mem_singleton,neg_ne_zero,one_ne_zero,not_false_eq_true,zero_sub,
    sub_self,zpow_zero,zpow_neg_one,complexCoefficient] at h
  convert h using 1
  simp
  ring

/-- `D_0 = 1-h(y/x+x/y)`. -/
theorem weightedValuationDiagonal_zero_hasSum (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y 0) (1-(z/(1-z))*(y/x+x/y)) := by
  have hs : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y 0
  simp only [zero_add,hs] at h
  norm_num [complexCoefficient] at h
  convert h using 1
  simp only [div_eq_mul_inv]
  ring

/-- `D_1 = x+y-h(y²/x+x²/y)`. -/
theorem weightedValuationDiagonal_one_hasSum (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y 1) (x+y-(z/(1-z))*(y^2/x+x^2/y)) := by
  have hs : Finset.Icc (-1 : ℤ) 2 = {-1,0,1,2} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y 1
  norm_num [hs,complexCoefficient] at h
  simp only [zpow_ofNat] at h
  convert h using 1
  simp only [div_eq_mul_inv]
  ring

/-- The coefficient predecessor identity, valid for every `z` (including `z = 1`). -/
theorem complexCoefficient_pred (z : ℂ) (t : ℤ) :
    complexCoefficient z (t-1) = complexCoefficient z t +
      z/(1-z)*complexAtom (-1) t - (1+z/(1-z))*complexAtom 0 t := by
  by_cases ht : t < -1
  · simp [complexCoefficient_below z ht, complexCoefficient_below z (show t-1 < -1 by omega),
      complexAtom, show t ≠ -1 by omega, show t ≠ 0 by omega]
  by_cases ht1 : t = -1
  · subst t
    norm_num [complexCoefficient,complexAtom]
    ring
  by_cases ht0 : t = 0
  · subst t
    norm_num [complexCoefficient,complexAtom]
    ring
  simp [complexCoefficient,complexAtom,ht1,ht0,show 0 ≤ t by omega,
    show t-1 ≠ -1 by omega,show 1 ≤ t by omega]

/-- In the primitive stratum the local grid base vanishes. -/
theorem ramanujanGridBase_primitive {p : ℕ} {k : Fin (p^2)} (hk : ¬ p ∣ k.val) :
    ramanujanGridBase p k = 0 := by
  have hk0 : k.val ≠ 0 := fun h => hk (h ▸ dvd_zero p)
  simp [ramanujanGridBase, hk0, hk]

/-- In the primitive stratum the local grid tag equals `-1/p²`. -/
theorem ramanujanGridTag_primitive {p : ℕ} {k : Fin (p^2)} (hk : ¬ p ∣ k.val) :
    ramanujanGridTag p k = -((p^2 : ℕ) : ℝ)⁻¹ := by
  simp [ramanujanGridTag, hk]

/-- The multiplicative pushforward of two centred bases is `-(1-1/p)` times the centred base. -/
theorem criticalDefect_pushforward (p : Nat.Primes) (c : ZMod (p : ℕ)) :
    (∑ a, ∑ b, if a*b = c then criticalDefectBase p a*criticalDefectBase p b else 0) =
      -(1-(p : ℂ)⁻¹)*criticalDefectBase p c := by
  have h := criticalDefect_base_base p (fun u => if u = c then (1 : ℂ) else 0)
  have hc : criticalDefectCenter p (fun u => if u = c then (1 : ℂ) else 0) =
      criticalDefectBase p c := by
    simp only [criticalDefectCenter, criticalDefectBase, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_one]
    by_cases h0 : c = 0
    · simp [h0]
    · simp [h0, Ne.symm h0]
  rw [hc] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- Explicit pushforward masses: `-(p-1)²/p²` at zero and `(p-1)/p²` at every nonzero point. -/
theorem criticalDefect_pushforward_mass (p : Nat.Primes) (c : ZMod (p : ℕ)) :
    (∑ a, ∑ b, if a*b = c then criticalDefectBase p a*criticalDefectBase p b else 0) =
      if c = 0 then -(((p : ℂ)-1)^2/(p : ℂ)^2) else ((p : ℂ)-1)/(p : ℂ)^2 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  rw [criticalDefect_pushforward]
  by_cases h0 : c = 0
  · simp only [criticalDefectBase, h0, if_true]
    field_simp
  · simp only [criticalDefectBase, h0, if_false]
    field_simp
    ring

/-- The grid-node map `a ↦ p·val(a)` into `ℤ/p²` is injective. -/
theorem criticalDefectGridNode_injective (p : Nat.Primes) :
    Function.Injective (criticalDefectGridNode p) := by
  intro a b h
  have hv : (p : ℕ)*a.val = (p : ℕ)*b.val := by
    simpa [criticalDefectGridNode] using congrArg Fin.val h
  exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left p.property.pos hv)

end RHTower.BAGTrace
