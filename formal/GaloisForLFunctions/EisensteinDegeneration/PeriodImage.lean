import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Period changes and regular specialization

A map between two free period lines has coordinate `X^m u`, with `u` a unit.
Its image shifts vanishing orders by `m`; its first surviving coefficient is
the original specialization times `u(0)`. Multiplication by `u` detects
regularity of Laurent series and divisibility by every power of `X`.

These are the algebraic period-comparison mechanisms in Polo–Rivero,
*Irregular weight-one Eisenstein series and Euler systems*, Proposition 6.6,
Remark 6.7 and the regularity argument of Corollary 6.10.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open PowerSeries

noncomputable section

section Ring

variable {R : Type*} [CommRing R]

/-- Coordinates of the image under a period map with boundary order `m`. -/
def periodImage (m : ℕ) (u : (PowerSeries R)ˣ) (f : PowerSeries R) : PowerSeries R :=
  X ^ m * ((u : PowerSeries R) * f)

/-- A unit cannot create or remove divisibility by any given element. -/
theorem dvd_period_unit_iff (a f : PowerSeries R) (u : (PowerSeries R)ˣ) :
    a ∣ (u : PowerSeries R) * f ↔ a ∣ f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(↑u⁻¹ : PowerSeries R) * g, ?_⟩
    calc
      f = (↑u⁻¹ : PowerSeries R) * (u * f) := by simp
      _ = (↑u⁻¹ : PowerSeries R) * (a * g) := by rw [hg]
      _ = a * ((↑u⁻¹ : PowerSeries R) * g) := by ac_rfl
  · rintro ⟨g, rfl⟩
    exact ⟨(u : PowerSeries R) * g, by ac_rfl⟩

/-- The coefficient at the boundary order reads precisely the original special fibre. -/
theorem periodImage_coeff_boundary (m : ℕ) (u : (PowerSeries R)ˣ)
    (f : PowerSeries R) :
    coeff m (periodImage m u f) = constantCoeff (u : PowerSeries R) * constantCoeff f := by
  simp only [periodImage, coeff_X_pow_mul', le_refl, if_true, Nat.sub_self,
    coeff_zero_eq_constantCoeff, map_mul]

/-- Consecutive changes of period line add their boundary orders and multiply their units. -/
theorem periodImage_comp (m n : ℕ) (u v : (PowerSeries R)ˣ) (f : PowerSeries R) :
    periodImage m u (periodImage n v f) = periodImage (m + n) (u * v) f := by
  simp only [periodImage, pow_add, Units.val_mul]
  ac_rfl

/-- Changing a period basis and its scalar coordinate by inverse units preserves the image. -/
theorem periodImage_change_basis (m : ℕ) (u v : (PowerSeries R)ˣ)
    (f : PowerSeries R) :
    periodImage m (u * v) ((↑v⁻¹ : PowerSeries R) * f) = periodImage m u f := by
  simp [periodImage, mul_assoc]

/-- A Laurent series is regular when it comes from an actual power series. -/
def Regular (f : LaurentSeries R) : Prop :=
  ∃ g : PowerSeries R, (g : LaurentSeries R) = f

/-- A regular unit is an exact detector of poles, including for a zero input. -/
theorem regular_mul_unit_iff (f : LaurentSeries R) (u : (PowerSeries R)ˣ) :
    Regular (f * ((u : PowerSeries R) : LaurentSeries R)) ↔ Regular f := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g * (↑u⁻¹ : PowerSeries R), ?_⟩
    rw [PowerSeries.coe_mul, hg, mul_assoc, ← PowerSeries.coe_mul]
    simp
  · rintro ⟨g, rfl⟩
    exact ⟨g * (u : PowerSeries R), PowerSeries.coe_mul _ _⟩

/-- Dividing a regular family by `X^m` is regular precisely when its first `m`
coefficients vanish. This detects a pole before choosing a scalar moment. -/
theorem regular_shift_iff (m : ℕ) (f : PowerSeries R) :
    Regular (HahnSeries.single (-(m : ℤ)) (1 : R) * (f : LaurentSeries R)) ↔
      X ^ m ∣ f := by
  have hcancel : (HahnSeries.single (m : ℤ) (1 : R) : LaurentSeries R) *
      HahnSeries.single (-(m : ℤ)) 1 = 1 := by
    simp [HahnSeries.single_mul_single, ← HahnSeries.C_apply]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_⟩
    rw [map_mul, HahnSeries.ofPowerSeries_X_pow]
    change (f : LaurentSeries R) = HahnSeries.single (m : ℤ) 1 * (g : LaurentSeries R)
    rw [hg, ← mul_assoc, hcancel, one_mul]
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    rw [PowerSeries.coe_mul, HahnSeries.ofPowerSeries_X_pow, ← mul_assoc,
      HahnSeries.single_mul_single, neg_add_cancel, one_mul]
    simp [← HahnSeries.C_apply]

end Ring

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The exact vanishing order, with infinity retained when the input is zero. -/
theorem periodImage_order (m : ℕ) (u : (PowerSeries R)ˣ) (f : PowerSeries R) :
    (periodImage m u f).order = m + f.order := by
  rw [periodImage, order_mul, order_X_pow, order_mul,
    order_zero_of_unit u.isUnit, zero_add]

/-- A period map is injective even when its special-fibre map vanishes. -/
theorem periodImage_injective (m : ℕ) (u : (PowerSeries R)ˣ) :
    Function.Injective (periodImage m u) := by
  intro f g h
  have h' := PowerSeries.X_pow_mul_cancel h
  exact (mul_left_cancel₀ u.ne_zero) h'

/-- Vanishing in the image at every order is exactly the corresponding shifted condition. -/
theorem periodImage_X_pow_dvd_iff (m n : ℕ) (u : (PowerSeries R)ˣ)
    (f : PowerSeries R) :
    X ^ (m + n) ∣ periodImage m u f ↔ X ^ n ∣ f := by
  rw [periodImage, pow_add, mul_dvd_mul_iff_left (pow_ne_zero m X_ne_zero)]
  exact dvd_period_unit_iff _ _ _

/-- A nonzero period basis vector admits exactly `m` divisions by the parameter. -/
theorem regular_shift_period_iff (m n : ℕ) (u : (PowerSeries R)ˣ) :
    Regular (HahnSeries.single (-(n : ℤ)) (1 : R) *
      ((periodImage m u 1 : PowerSeries R) : LaurentSeries R)) ↔ n ≤ m := by
  rw [regular_shift_iff, PowerSeries.X_pow_dvd_iff]
  have hord : (periodImage m u 1).order = m := by
    rw [periodImage_order, order_one, add_zero]
  constructor
  · intro h
    have hn := PowerSeries.nat_le_order (periodImage m u 1) n h
    simpa only [hord, ENat.coe_le_coe] using hn
  · intro h i hi
    apply PowerSeries.coeff_of_lt_order
    rw [hord]
    exact_mod_cast hi.trans_le h

end Domain

section Cokernel

variable {K : Type*} [Field K]

/-- The map of period lines, viewed over the residue field. -/
def periodMap (m : ℕ) (u : (PowerSeries K)ˣ) : PowerSeries K →ₗ[K] PowerSeries K :=
  LinearMap.mulLeft K (X ^ m * (u : PowerSeries K))

theorem periodMap_apply (m : ℕ) (u : (PowerSeries K)ˣ) (f : PowerSeries K) :
    periodMap m u f = periodImage m u f :=
  mul_assoc (X ^ m) (u : PowerSeries K) f

/-- The finite jet retained in the boundary quotient. -/
def boundaryJet (m : ℕ) : PowerSeries K →ₗ[K] (Fin m → K) where
  toFun f i := coeff i.val f
  map_add' f g := by ext i; exact map_add (coeff i.val) f g
  map_smul' c f := by ext i; exact PowerSeries.coeff_smul i.val f c

theorem boundaryJet_surjective (m : ℕ) : Function.Surjective (boundaryJet (K := K) m) := by
  intro v
  refine ⟨PowerSeries.mk (fun n => if h : n < m then v ⟨n, h⟩ else 0), ?_⟩
  ext i
  simp [boundaryJet, i.isLt]

/-- The image is exactly the families whose boundary jet vanishes; it does not depend on
the unit used to choose the two bases. -/
theorem periodMap_range (m : ℕ) (u : (PowerSeries K)ˣ) :
    (periodMap m u).range = (boundaryJet (K := K) m).ker := by
  ext f
  have hjet : f ∈ (boundaryJet (K := K) m).ker ↔ X ^ m ∣ f := by
    rw [LinearMap.mem_ker, PowerSeries.X_pow_dvd_iff]
    constructor
    · intro h n hn
      exact congrFun h ⟨n, hn⟩
    · intro h
      exact funext fun i => h i.val i.isLt
  rw [hjet, LinearMap.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(u : PowerSeries K) * g, (periodMap_apply m u g)⟩
  · rintro ⟨g, rfl⟩
    refine ⟨(↑u⁻¹ : PowerSeries K) * g, ?_⟩
    simp [periodMap_apply, periodImage]

/-- A period map of order `m` has precisely the first `m` Taylor coefficients as cokernel. -/
def periodCokernelEquiv (m : ℕ) (u : (PowerSeries K)ˣ) :
    (PowerSeries K ⧸ (periodMap m u).range) ≃ₗ[K] (Fin m → K) := by
  have e : (PowerSeries K ⧸ (boundaryJet (K := K) m).ker) ≃ₗ[K] (Fin m → K) :=
    (boundaryJet (K := K) m).quotKerEquivRange.trans
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr (boundaryJet_surjective m)))
  exact (periodMap_range m u).symm ▸ e

/-- The boundary dimension is the vanishing order of the period map. -/
theorem periodCokernel_finrank (m : ℕ) (u : (PowerSeries K)ˣ) :
    Module.finrank K (PowerSeries K ⧸ (periodMap m u).range) = m := by
  rw [(periodCokernelEquiv m u).finrank_eq]
  simp

/-- The image ideal of the period line is the `m`-th power of the maximal ideal. -/
theorem periodIdeal_eq (m : ℕ) (u : (PowerSeries K)ˣ) :
    Ideal.span {X ^ m * (u : PowerSeries K)} =
      IsLocalRing.maximalIdeal (PowerSeries K) ^ m := by
  rw [Ideal.span_singleton_mul_right_unit u.isUnit,
    PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]

/-- The intrinsic module length of the boundary quotient equals the period-map order.
This length is over the weight ring, not just its residue field. -/
theorem periodQuotient_length (m : ℕ) (u : (PowerSeries K)ˣ) :
    Module.length (PowerSeries K)
      (PowerSeries K ⧸ Ideal.span {X ^ m * (u : PowerSeries K)}) = m := by
  rw [periodIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (PowerSeries K) m

end Cokernel

end

end GaloisForLFunctions.EisensteinDegeneration
