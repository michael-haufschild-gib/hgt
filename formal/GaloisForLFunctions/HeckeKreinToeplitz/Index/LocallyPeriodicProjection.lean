import GaloisForLFunctions.HeckeKreinToeplitz.Index.NilpotentSubspaces
import Mathlib.Algebra.Ring.GeomSum

/-!
# Algebraic projections for locally periodic operators

Over a characteristic-zero field, an operator with finite periodic orbits splits its module
into fixed vectors and the range of its difference from identity. The fixed projection equals
every complete finite orbit average and commutes with every operator in the commutant.
-/

open Module Finset
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

section PeriodicVectors
variable {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]

theorem pow_mul_apply_of_period {T : End R W} {m : ℕ} {x : W}
    (hx : (T ^ m) x = x) (n : ℕ) : (T ^ (m * n)) x = x := by
  rw [pow_mul]
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hx, ih]

/-- Vectors with finite periodic orbits form a submodule. -/
def periodicVectorSubmodule (T : End R W) : Submodule R W where
  carrier := {x | ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x}
  zero_mem' := ⟨1, one_ne_zero, by rw [map_zero]⟩
  add_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [map_add, pow_mul_apply_of_period hx n,
      Nat.mul_comm m n, pow_mul_apply_of_period hy m]
  smul_mem' := by
    rintro c x ⟨m, hm, hx⟩
    exact ⟨m, hm, by rw [map_smul, hx]⟩

end PeriodicVectors

variable {K V : Type*} [Field K] [CharZero K] [AddCommMonoid V] [Module K V]

/-- The normalized average of the first `m` iterates of an algebraic operator. -/
def periodicOrbitAverage (T : End K V) (m : ℕ) : End K V :=
  (m : K)⁻¹ • ∑ j ∈ range m, T ^ j

omit [CharZero K] in
theorem periodicOrbitAverage_fixed (T : End K V) {m : ℕ} {x : V}
    (hp : (T ^ m) x = x) : T (periodicOrbitAverage T m x) = periodicOrbitAverage T m x := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  apply sub_eq_zero.mp
  change (T - 1) (periodicOrbitAverage T m x) = 0
  rw [periodicOrbitAverage, LinearMap.smul_apply, map_smul]
  change (m : K)⁻¹ • (((T - 1) * ∑ j ∈ range m, T ^ j) x) = 0
  rw [mul_geom_sum, LinearMap.sub_apply, Module.End.one_apply, hp, sub_self, smul_zero]

/-- Averaging changes a vector only by an operator difference. -/
theorem sub_periodicOrbitAverage_mem_range (T : End K V) {m : ℕ} (hm : m ≠ 0) (x : V) :
    x + (-1 : K) • periodicOrbitAverage T m x ∈ LinearMap.range (T + (-1 : K) • 1) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  change x - periodicOrbitAverage T m x ∈ LinearMap.range (T - 1)
  have hj (j : ℕ) : (T ^ j) x - x ∈ LinearMap.range (T - 1) := by
    refine ⟨(∑ l ∈ range j, T ^ l) x, ?_⟩
    change (((T - 1) * ∑ l ∈ range j, T ^ l) x) = (T ^ j) x - x
    rw [mul_geom_sum, LinearMap.sub_apply, Module.End.one_apply]
  have he : periodicOrbitAverage T m x - x =
      (m : K)⁻¹ • ∑ j ∈ range m, ((T ^ j) x - x) := by
    rw [sum_sub_distrib, sum_const, card_range,
      ← Nat.cast_smul_eq_nsmul K m x, smul_sub, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul]
    rw [periodicOrbitAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  have ha : periodicOrbitAverage T m x - x ∈ LinearMap.range (T - 1) := by
    rw [he]
    exact (LinearMap.range (T - 1)).smul_mem _
      ((LinearMap.range (T - 1)).sum_mem (fun j _ => hj j))
  simpa only [neg_sub] using (LinearMap.range (T - 1)).neg_mem ha

/-- For a locally periodic operator, fixed vectors and moving vectors are complementary. -/
theorem locallyPeriodic_isCompl (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) :
    IsCompl (LinearMap.ker (T + (-1 : K) • 1))
      (LinearMap.range (T + (-1 : K) • 1)) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  change IsCompl (LinearMap.ker (T - 1)) (LinearMap.range (T - 1))
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hxr
    obtain ⟨y, hy⟩ := hxr
    obtain ⟨m, hm, hperiod⟩ := hp y
    have hnil : ((T + (-1 : K) • (1 : End K V)) ^ (2 : ℕ)) y = 0 := by
      change ((T - (1 : End K V)) ^ (2 : ℕ)) y = 0
      rw [pow_two, Module.End.mul_apply, hy]
      exact hx
    have hfix := fixed_of_periodic_unipotent T y hm hperiod hnil
    rw [← hy, LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]
  · apply codisjoint_iff.mpr
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨m, hm, hperiod⟩ := hp x
    apply Submodule.mem_sup.mpr
    refine ⟨periodicOrbitAverage T m x, ?_, x - periodicOrbitAverage T m x,
      sub_periodicOrbitAverage_mem_range T hm x, ?_⟩
    · change (T - 1) (periodicOrbitAverage T m x) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, periodicOrbitAverage_fixed T hperiod,
        sub_self]
    · abel

/-- The fixed-space projection for a locally periodic operator, with moving kernel. -/
def locallyPeriodicProjection (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) : End K V := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  exact (LinearMap.ker (T + (-1 : K) • 1)).projection
    (LinearMap.range (T + (-1 : K) • 1)) (locallyPeriodic_isCompl T hp)

theorem locallyPeriodicProjection_fixed (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (x : V) :
    T (locallyPeriodicProjection T hp x) = locallyPeriodicProjection T hp x := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  have h := Submodule.projection_apply_mem (locallyPeriodic_isCompl T hp) x
  change (T - 1) (locallyPeriodicProjection T hp x) = 0 at h
  simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h

theorem locallyPeriodicProjection_apply_of_fixed (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) {x : V} (hx : T x = x) :
    locallyPeriodicProjection T hp x = x := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  apply Submodule.projection_apply_of_mem_left (locallyPeriodic_isCompl T hp)
  change (T - 1) x = 0
  rw [LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]

theorem locallyPeriodicProjection_apply_eq_zero_iff (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (x : V) :
    locallyPeriodicProjection T hp x = 0 ↔ x ∈ LinearMap.range (T + (-1 : K) • 1) := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  exact Submodule.projection_apply_eq_zero_iff (locallyPeriodic_isCompl T hp)

/-- The canonical projection equals every nonempty complete orbit average of the vector. -/
theorem locallyPeriodicProjection_eq_average (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) {m : ℕ} (hm : m ≠ 0)
    {x : V} (hperiod : (T ^ m) x = x) :
    locallyPeriodicProjection T hp x = periodicOrbitAverage T m x := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  have hz := (locallyPeriodicProjection_apply_eq_zero_iff T hp _).mpr
    (sub_periodicOrbitAverage_mem_range T hm x)
  change locallyPeriodicProjection T hp (x - periodicOrbitAverage T m x) = 0 at hz
  rw [map_sub, locallyPeriodicProjection_apply_of_fixed T hp
    (periodicOrbitAverage_fixed T hperiod)] at hz
  exact sub_eq_zero.mp hz

/-- The complementary component lies in the moving subspace. -/
theorem add_neg_locallyPeriodicProjection_mem_range (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (x : V) :
    x + (-1 : K) • locallyPeriodicProjection T hp x ∈
      LinearMap.range (T + (-1 : K) • 1) := by
  obtain ⟨m, hm, hperiod⟩ := hp x
  rw [locallyPeriodicProjection_eq_average T hp hm hperiod]
  exact sub_periodicOrbitAverage_mem_range T hm x

#print axioms locallyPeriodic_isCompl
#print axioms locallyPeriodicProjection_eq_average
#print axioms add_neg_locallyPeriodicProjection_mem_range

/-- The fixed-space projection commutes with every operator commuting with the original action. -/
theorem locallyPeriodicProjection_commute (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x)
    (S : End K V) (hS : Commute T S) : Commute (locallyPeriodicProjection T hp) S := by
  change locallyPeriodicProjection T hp * S = S * locallyPeriodicProjection T hp
  apply LinearMap.ext
  intro x
  obtain ⟨m, hm, hperiod⟩ := hp x
  have hpow (j : ℕ) : (T ^ j) (S x) = S ((T ^ j) x) :=
    LinearMap.congr_fun (hS.pow_left j).eq x
  have hperiodS : (T ^ m) (S x) = S x := by rw [hpow, hperiod]
  change locallyPeriodicProjection T hp (S x) = S (locallyPeriodicProjection T hp x)
  rw [locallyPeriodicProjection_eq_average T hp hm hperiodS,
    locallyPeriodicProjection_eq_average T hp hm hperiod]
  simp only [periodicOrbitAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, hpow]

#print axioms locallyPeriodicProjection_commute

/-- The fixed projection is unchanged along every orbit iterate. -/
theorem locallyPeriodicProjection_pow_apply (T : End K V)
    (hp : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (n : ℕ) (x : V) :
    locallyPeriodicProjection T hp ((T ^ n) x) = locallyPeriodicProjection T hp x := by
  have hc := locallyPeriodicProjection_commute T hp T (Commute.refl T)
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have he := LinearMap.congr_fun hc.eq ((T ^ n) x)
    rw [Module.End.mul_apply, Module.End.mul_apply] at he
    rw [he, ih, locallyPeriodicProjection_fixed T hp]

#print axioms locallyPeriodicProjection_pow_apply
end GaloisForLFunctions.HeckeKreinToeplitz
