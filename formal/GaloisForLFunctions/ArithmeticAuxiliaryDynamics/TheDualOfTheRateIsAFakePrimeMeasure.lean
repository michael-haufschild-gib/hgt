import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMoebiusPartOfAProducer

/-!
# The dual of the rate is a fake prime measure

The slope of a stencil depends on its multiplicity through the pronic weights `u₀(r) = 1/(r (r + 1))`.
What makes these weights work is one family of moment identities: `Σ_r u₀(r) (r mod k) = log k`. Any
nonnegative measure with the same moments on an alphabet computes the same slope. It behaves like the
density `(ψ(n/r) − ψ(n/(r+1)))/n` of a prime system consistent with the Chebyshev identity up to
level `K`.

So the best rate is a linear program whose dual variables are **fake prime measures**:
`A(K) ≥ (mass of u on the window)/(1 − 1/B)` for every consistent `u`. Every floor is a dual measure:
the forced jump at a rough `p` is the move of mass from `p` to `p − 1` and `1`, which preserves the
moments because `ρ(p) = ρ(p − 1) + ρ(1)` on the alphabet.

The dual constraints are arithmetic sawteeth, not potentials, so the rate is not a capacity: the
capacity-type ceiling `e^{-0.87 n}` of integer polynomials on `[0, 1]` is already passed by stencils.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- A measure on `r = j + 1`, nonnegative, with the Chebyshev moments up to level `K`. -/
structure IsFakePrimeMeasure (K : ℕ) (u : ℕ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ u j
  moment : ∀ k ∈ Icc 1 K, HasSum (fun j => u j * (((j + 1) % k : ℕ) : ℝ)) (Real.log k)

/-- **The pronic measure is consistent at every level.** -/
theorem isFakePrimeMeasure_pronic (K : ℕ) :
    IsFakePrimeMeasure K fun j => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  refine ⟨fun j => by positivity, fun k hk => ?_⟩
  have hk1 := (mem_Icc.mp hk).1
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := (hasSum_mod_div_pronic hk1).mul_left (k : ℝ)
  have hval : (k : ℝ) * (Real.log k / k) = Real.log k := by field_simp
  rw [hval] at h
  have hfun : (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * (((j + 1) % k : ℕ) : ℝ)) =
      fun j : ℕ => (k : ℝ) * (((j + 1) % k : ℕ) / (k : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    funext j
    field_simp
  rw [hfun]
  exact h

/-- **Weak duality: a fake prime measure computes the slope.** -/
theorem IsFakePrimeMeasure.hasSum_slope {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    HasSum (fun j => u j * (stepWeight c (j + 1) : ℝ)) (stencilSlope c) := by
  have hsub := hP.support_subset_Icc hK
  have hfun : (fun j => u j * (stepWeight c (j + 1) : ℝ)) = fun j =>
      ∑ k ∈ c.support, (-(c k : ℝ) / k) * (u j * (((j + 1) % k : ℕ) : ℝ)) := by
    funext j
    rw [stepWeight_eq_sum_mod hP.zero hP.balanced, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, stencilSlope]
  refine hasSum_sum fun k hk => ?_
  have h := (hu.moment k (hsub hk)).mul_left (-(c k : ℝ) / k)
  have hval : -(c k : ℝ) / k * Real.log k = -(c k : ℝ) * Real.log k / k := by ring
  rwa [hval] at h

/-- **The dual bound.** A fake prime measure bounds the slope below by its mass on the window. -/
theorem IsFakePrimeMeasure.mul_mass_le {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    (m : ℝ) * ∑ j ∈ range (B - 1), u j ≤ stencilSlope c := by
  have hterm : ∀ j, 0 ≤ u j * (stepWeight c (j + 1) : ℝ) := fun j =>
    mul_nonneg (hu.nonneg j) (by exact_mod_cast hP.nonneg (j + 1))
  refine le_trans ?_ (sum_le_hasSum (range (B - 1)) (fun j _ => hterm j) (hu.hasSum_slope hP hK))
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  have hjB := mem_range.mp hj
  have hw : (m : ℝ) ≤ stepWeight c (j + 1) := by
    exact_mod_cast hP.window (j + 1) (mem_Ico.mpr ⟨by omega, by omega⟩)
  calc (m : ℝ) * u j = u j * m := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (hu.nonneg j)

/-- **The dual form of the floor of the rate.** The normalized slope is at least the window mass of
every fake prime measure, over `1 − 1/B`. -/
theorem IsFakePrimeMeasure.le_normSlope {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    (∑ j ∈ range (B - 1), u j) / (1 - 1 / (B : ℝ)) ≤ normSlope c m B := by
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  have hbound := hu.mul_mass_le hP hK
  rw [normSlope, le_div_iff₀ (mul_pos hm h1), div_mul_eq_mul_div, div_le_iff₀ h1]
  calc (∑ j ∈ range (B - 1), u j) * ((m : ℝ) * (1 - 1 / (B : ℝ)))
      = (m : ℝ) * (∑ j ∈ range (B - 1), u j) * (1 - 1 / (B : ℝ)) := by ring
    _ ≤ stencilSlope c * (1 - 1 / (B : ℝ)) := mul_le_mul_of_nonneg_right hbound h1.le

/-- The move of mass at a prime beyond the alphabet preserves every moment on the alphabet:
`p mod k = (p − 1) mod k + 1 mod k` for `k ≤ K < p`. -/
theorem mod_prime_eq {K p k : ℕ} (hp : p.Prime) (hK : K < p) (hk : k ∈ Icc 1 K) :
    ((p % k : ℕ) : ℝ) = (((p - 1) % k : ℕ) : ℝ) + ((1 % k : ℕ) : ℝ) := by
  obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
  by_cases h1 : k = 1
  · subst h1
    simp [Nat.mod_one]
  · have hk2 : 2 ≤ k := by omega
    have hnd : ¬ k ∣ p := fun hd => by
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
    have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hp1 : p = (p - 1) + 1 := by have := hp.pos; omega
    have hpne : p % k ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hdiv := Nat.div_add_mod p k
    have hlt := Nat.mod_lt p (by omega : 0 < k)
    have hrew : p - 1 = (p % k - 1) + k * (p / k) := by omega
    have hsmall : p % k - 1 < k := by omega
    have hmod : (p - 1) % k = p % k - 1 := by
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]
    rw [hmod, hmod1]
    have hpos : 1 ≤ p % k := by omega
    exact_mod_cast (by omega : p % k = p % k - 1 + 1)

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
