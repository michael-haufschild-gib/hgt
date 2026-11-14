import GaloisForLFunctions.HTGeometry.ValuationSubringInertiaDictionary

/-!
# Valuation units and inertia characters

Matched powers of a radical and a base parameter have valuation one.
If inertia acts on such a unit through a constant eigenvalue, that
eigenvalue is one: otherwise its displacement is itself a valuation
unit, contradicting trivial action on the residue field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {K L : Type*} [Field K] [Field L]

/-- A residue-trivial action on a unit has trivial constant eigenvalue. -/
theorem valuation_unit_eigenvalue_eq_one (v : Valuation L (WithZero (Multiplicative ℤ)))
    (f : K →+* L) (hc : ∀ a : K, a ≠ 0 → v (f a) = 1)
    {x y : L} {a : K} (hx : v x = 1) (hres : v (y - x) < 1) (heig : y = f a * x) :
    a = 1 := by
  by_contra ha
  have he : y - x = f (a - 1) * x := by
    rw [heig, map_sub, map_one]
    ring
  rw [he, map_mul, hc (a - 1) (sub_ne_zero.mpr ha), hx, one_mul] at hres
  exact (lt_irrefl (1 : WithZero (Multiplicative ℤ))) hres


/-- Dividing matched powers of a radical and a base parameter gives a valuation unit. -/
theorem valuation_balanced_radical (v : Valuation L (WithZero (Multiplicative ℤ)))
    {z t : L} {N m g : ℕ} (hg : 0 < g) (hN : g ∣ N) (hm : g ∣ m)
    (ht : v t ≠ 0) (hval : v z ^ N = v t ^ m) :
    v (z ^ (N / g) / t ^ (m / g)) = 1 := by
  have hp : v (z ^ (N / g) / t ^ (m / g)) ^ g = 1 := by
    rw [map_div₀, map_pow, map_pow, div_pow, ← pow_mul, ← pow_mul,
      Nat.div_mul_cancel hN, Nat.div_mul_cancel hm, hval, div_self (pow_ne_zero _ ht)]
  have hu0 : v (z ^ (N / g) / t ^ (m / g)) ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hg)] at hp
    exact zero_ne_one hp
  have hl := congrArg WithZero.log hp
  rw [WithZero.log_pow, nsmul_eq_mul, WithZero.log_one] at hl
  have hlog : (v (z ^ (N / g) / t ^ (m / g))).log = 0 :=
    (mul_eq_zero.mp hl).resolve_left (by exact_mod_cast Nat.ne_of_gt hg)
  rw [← WithZero.exp_log hu0, hlog, WithZero.exp_zero]


/-- Inertia acts trivially on the constant character of a valuation unit. -/
theorem inertia_unit_character_eq_one {F : Type*} [Field F] [Algebra F L]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (f : K →+* L) (hc : ∀ a : K, a ≠ 0 → v (f a) = 1)
    (g : v.valuationSubring.inertiaSubgroup F) {x : L} {a : K}
    (hx : v x = 1)
    (heig : (((g : v.valuationSubring.decompositionSubgroup F) : L ≃ₐ[F] L)) x = f a * x) :
    a = 1 := by
  let u : v.valuationSubring := ⟨x, show v x ≤ 1 from hx.le⟩
  have hres := GaloisForLFunctions.HTGeometry.ValuationInertia.smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup
    v.valuationSubring g.property u
  have hv := (v.mem_maximalIdeal_iff).mp hres
  exact valuation_unit_eigenvalue_eq_one v f hc hx hv heig

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
