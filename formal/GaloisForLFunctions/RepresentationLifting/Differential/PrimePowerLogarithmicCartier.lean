import GaloisForLFunctions.RepresentationLifting.Differential.LogarithmicCartier

/-!
# Horizontal thickening of logarithmic coefficients

Over `ZMod (p^(r+1))`, the generalized zero space of the logarithmic Euler
operator consists exactly of lists supported in degrees divisible by `p`.
Its powers stabilize at exponent `r+1`, and the degree-`p` monomial proves
this bound sharp. Thus prime-power thickening adds nilpotent depth precisely
to the residue-zero sector of the prime-characteristic Cartier splitting.

This is a coefficient-level application of the indexed local models in
Fersi, *Lifting the local logarithmic Cartier transform modulo p^n*, §4.4.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
/-- The logarithmic operator over a residue ring of arbitrary thickness. -/
def modularEuler (m : ℕ) : Module.End (ZMod m) (ℕ →₀ ZMod m) where
  toFun f := Finsupp.onFinset f.support (fun n => n * f n) (fun n hn =>
    Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, mul_zero])))
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' c f := by ext n; exact mul_left_comm _ _ _

@[simp] theorem modularEuler_apply (m : ℕ) (f : ℕ →₀ ZMod m) (n : ℕ) :
    modularEuler m f n = n * f n := rfl

theorem modularEuler_pow_apply (m k : ℕ) (f : ℕ →₀ ZMod m) (n : ℕ) :
    (modularEuler m ^ k) f n = (n : ZMod m) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, modularEuler_apply, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

variable (p : ℕ)

/-- Projection onto exponents divisible by the residue characteristic. -/
def cartierPrimary (r : ℕ) : Module.End (ZMod (p ^ (r + 1))) (ℕ →₀ ZMod (p ^ (r + 1))) where
  toFun f := Finsupp.filter (fun n => p ∣ n) f
  map_add' f g := by
    ext n
    by_cases h : p ∣ n <;> simp [h]
  map_smul' c f := by
    ext n
    by_cases h : p ∣ n <;> simp [h]

@[simp] theorem cartierPrimary_apply (r : ℕ) (f : ℕ →₀ ZMod (p ^ (r + 1))) (n : ℕ) :
    cartierPrimary p r f n = if p ∣ n then f n else 0 := by
  exact Finsupp.filter_apply _ _ _

/-- Thickening to p^(r+1) makes the zero-residue sector nilpotent of bounded order. -/
theorem logarithmicEuler_primary_nilpotent (r : ℕ) :
    modularEuler (p ^ (r + 1)) ^ (r + 1) * cartierPrimary p r = 0 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change (modularEuler (p ^ (r + 1)) ^ (r + 1)) (cartierPrimary p r f) n = 0
  rw [modularEuler_pow_apply, cartierPrimary_apply]
  by_cases h : p ∣ n
  · rw [if_pos h]
    obtain ⟨a, rfl⟩ := h
    rw [Nat.cast_mul, mul_pow, ← Nat.cast_pow, CharP.cast_eq_zero, zero_mul, zero_mul]
  · rw [if_neg h, mul_zero]

variable [Fact p.Prime]

private theorem degree_isUnit (r n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : ZMod (p ^ (r + 1))) := by
  apply (ZMod.isUnit_iff_coprime n (p ^ (r + 1))).mpr
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn).symm.pow_right _

/-- Every generalized zero vector lies in the residue-zero sector. -/
theorem logarithmicEuler_nilpotent_vector_iff (r : ℕ) (f : ℕ →₀ ZMod (p ^ (r + 1))) :
    (∃ k : ℕ, (modularEuler (p ^ (r + 1)) ^ k) f = 0) ↔
      cartierPrimary p r f = f := by
  constructor
  · rintro ⟨k, hk⟩
    ext n
    rw [cartierPrimary_apply]
    by_cases hn : p ∣ n
    · rw [if_pos hn]
    · rw [if_neg hn]
      have h := congrArg (fun g : ℕ →₀ ZMod (p ^ (r + 1)) => g n) hk
      rw [modularEuler_pow_apply] at h
      obtain ⟨u, hu⟩ := (degree_isUnit p r n hn).pow k
      rw [← hu] at h
      have hh := congrArg (fun z : ZMod (p ^ (r + 1)) => ↑(u⁻¹) * z) h
      simpa only [Finsupp.zero_apply, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] using hh.symm
  · intro hf
    refine ⟨r + 1, ?_⟩
    have h := congrArg (fun T : Module.End (ZMod (p ^ (r + 1))) (ℕ →₀ ZMod (p ^ (r + 1))) => T f)
      (logarithmicEuler_primary_nilpotent p r)
    change (modularEuler (p ^ (r + 1)) ^ (r + 1)) (cartierPrimary p r f) = 0 at h
    rwa [hf] at h

/-- The generalized zero space stabilizes at the thickness, independently of degree support. -/
theorem logarithmicEuler_primary_kernel (r k : ℕ) (f : ℕ →₀ ZMod (p ^ (r + 1))) :
    (modularEuler (p ^ (r + 1)) ^ (r + 1 + k)) f = 0 ↔
      cartierPrimary p r f = f := by
  constructor
  · intro h
    exact (logarithmicEuler_nilpotent_vector_iff p r f).mp ⟨r + 1 + k, h⟩
  · intro h
    have hz := congrArg (fun T : Module.End (ZMod (p ^ (r + 1))) (ℕ →₀ ZMod (p ^ (r + 1))) => T f)
      (logarithmicEuler_primary_nilpotent p r)
    change (modularEuler (p ^ (r + 1)) ^ (r + 1)) (cartierPrimary p r f) = 0 at hz
    rw [h] at hz
    rw [Nat.add_comm (r + 1) k, pow_add (modularEuler (p ^ (r + 1))) k (r + 1), Module.End.mul_apply, hz, map_zero]


/-- The thickness bound is sharp: the degree-p monomial survives r iterations. -/
theorem logarithmicEuler_primary_sharp (r : ℕ) :
    (modularEuler (p ^ (r + 1)) ^ r) (Finsupp.single p 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ℕ →₀ ZMod (p ^ (r + 1)) => f p) h
  rw [modularEuler_pow_apply, Finsupp.single_eq_same, mul_one, Finsupp.zero_apply,
    ← Nat.cast_pow, ZMod.natCast_eq_zero_iff] at hc
  exact Nat.not_dvd_of_pos_of_lt (pow_pos (Fact.out : p.Prime).pos r)
    (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self r)) hc

#print axioms logarithmicEuler_primary_sharp
#print axioms logarithmicEuler_primary_nilpotent
#print axioms logarithmicEuler_nilpotent_vector_iff
#print axioms logarithmicEuler_primary_kernel
/-- At thickness one this recovers the prime-characteristic Euler operator. -/
theorem modularEuler_prime : modularEuler p = logarithmicEuler p := by
  apply LinearMap.ext
  intro f
  exact Finsupp.ext (fun _ => rfl)

end GaloisForLFunctions.RepresentationLifting.DividedPower
