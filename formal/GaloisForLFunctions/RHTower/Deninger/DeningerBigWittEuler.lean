import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittSource
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Integral Euler coordinates for the literal big-Witt carrier

Every series in `1 + T A⟦T⟧` has a unique factorization

`∏ m ≥ 1, (1 - a_m T^m)`.

The construction below is triangular.  In particular it uses no division and is valid over every
commutative ring, including rings with torsion and nilpotents.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Raw power series underlying an element of the literal big-Witt additive group. -/
def deningerBigWittSeries (w : DeningerBigWittAdditive A) : PowerSeries A :=
  ((w.1 : (PowerSeries A)ˣ) : PowerSeries A)

@[simp] theorem deningerBigWittSeries_constantCoeff
    (w : DeningerBigWittAdditive A) :
    PowerSeries.constantCoeff (deningerBigWittSeries w) = 1 := by
  have hw := congrArg Units.val w.2
  simpa [deningerBigWittSeries, deningerBigWittUnitEvaluationZero] using hw

/-- Turn a constant-one power series into an element of the literal big-Witt additive group. -/
def deningerBigWittOfSeries (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) : DeningerBigWittAdditive A := by
  have hu : IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  change PowerSeries.constantCoeff f = 1
  exact hf

@[simp] theorem deningerBigWittSeries_ofSeries (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittSeries (deningerBigWittOfSeries f hf) = f := by
  rfl

theorem deningerBigWittOfSeries_series (w : DeningerBigWittAdditive A) :
    deningerBigWittOfSeries (deningerBigWittSeries w)
      (deningerBigWittSeries_constantCoeff w) = w := by
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Euler factor `1 - aT^m`.  Big-Witt coordinates use only positive `m`. -/
def deningerBigWittFactor (a : A) (m : ℕ) : PowerSeries A :=
  1 - PowerSeries.C a * PowerSeries.X ^ m

@[simp] theorem deningerBigWittFactor_zero (m : ℕ) :
    deningerBigWittFactor (0 : A) m = 1 := by
  simp [deningerBigWittFactor]

@[simp] theorem deningerBigWittFactor_constantCoeff (a : A) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.constantCoeff (deningerBigWittFactor a m) = 1 := by
  simp [deningerBigWittFactor, hm]

/-- Product of the first `N` positive-degree Euler factors. -/
def deningerBigWittEulerPartial (x : ℕ → A) (N : ℕ) : PowerSeries A :=
  ∏ i ∈ Finset.range N, deningerBigWittFactor (x i) (i + 1)

@[simp] theorem deningerBigWittEulerPartial_zero (x : ℕ → A) :
    deningerBigWittEulerPartial x 0 = 1 := by
  simp [deningerBigWittEulerPartial]

theorem deningerBigWittEulerPartial_succ (x : ℕ → A) (N : ℕ) :
    deningerBigWittEulerPartial x (N + 1) =
      deningerBigWittEulerPartial x N * deningerBigWittFactor (x N) (N + 1) := by
  simp [deningerBigWittEulerPartial, Finset.prod_range_succ]

@[simp] theorem deningerBigWittEulerPartial_constantCoeff (x : ℕ → A) (N : ℕ) :
    PowerSeries.constantCoeff (deningerBigWittEulerPartial x N) = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [deningerBigWittEulerPartial_succ, map_mul, ih]
      simp [deningerBigWittFactor_constantCoeff]

theorem coeff_mul_deningerBigWittFactor_of_lt
    (f : PowerSeries A) (a : A) {k m : ℕ} (hkm : k < m) :
    PowerSeries.coeff k (f * deningerBigWittFactor a m) = PowerSeries.coeff k f := by
  rw [deningerBigWittFactor, mul_sub, mul_one, map_sub]
  have hnot : ¬m ≤ k := Nat.not_le.mpr hkm
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow', if_neg hnot]
  simp

theorem coeff_mul_deningerBigWittFactor_self
    (f : PowerSeries A) (a : A) (m : ℕ) :
    PowerSeries.coeff m (f * deningerBigWittFactor a m) =
      PowerSeries.coeff m f - PowerSeries.constantCoeff f * a := by
  rw [deningerBigWittFactor, mul_sub, mul_one, map_sub, ← mul_assoc,
    PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_eq_constantCoeff]

theorem deningerBigWittEulerPartial_coeff_stable_step
    (x : ℕ → A) {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k (deningerBigWittEulerPartial x (N + 1)) =
      PowerSeries.coeff k (deningerBigWittEulerPartial x N) := by
  rw [deningerBigWittEulerPartial_succ]
  exact coeff_mul_deningerBigWittFactor_of_lt _ _ (Nat.lt_succ_of_le hk)

theorem deningerBigWittEulerPartial_coeff_stable
    (x : ℕ → A) {k N M : ℕ} (hk : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k (deningerBigWittEulerPartial x M) =
      PowerSeries.coeff k (deningerBigWittEulerPartial x N) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      rw [deningerBigWittEulerPartial_coeff_stable_step x (hk.trans hNM), ih]

/-- Power series represented by an Euler-coordinate sequence.  Each coefficient is a finite
product, so this definition has no convergence or topology hypothesis. -/
def deningerBigWittEulerSeries (x : ℕ → A) : PowerSeries A :=
  PowerSeries.mk fun n => PowerSeries.coeff n (deningerBigWittEulerPartial x n)

@[simp] theorem deningerBigWittEulerSeries_coeff (x : ℕ → A) (n : ℕ) :
    PowerSeries.coeff n (deningerBigWittEulerSeries x) =
      PowerSeries.coeff n (deningerBigWittEulerPartial x n) := by
  simp [deningerBigWittEulerSeries]

@[simp] theorem deningerBigWittEulerSeries_constantCoeff (x : ℕ → A) :
    PowerSeries.constantCoeff (deningerBigWittEulerSeries x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- Triangular partial reconstruction of a constant-one power series. -/
def deningerBigWittEulerApprox (f : PowerSeries A) : ℕ → PowerSeries A
  | 0 => 1
  | N + 1 =>
      deningerBigWittEulerApprox f N *
        deningerBigWittFactor
          (PowerSeries.coeff (N + 1) (deningerBigWittEulerApprox f N) -
            PowerSeries.coeff (N + 1) f)
          (N + 1)

@[simp] theorem deningerBigWittEulerApprox_zero (f : PowerSeries A) :
    deningerBigWittEulerApprox f 0 = 1 := by
  rfl

theorem deningerBigWittEulerApprox_succ (f : PowerSeries A) (N : ℕ) :
    deningerBigWittEulerApprox f (N + 1) =
      deningerBigWittEulerApprox f N *
        deningerBigWittFactor
          (PowerSeries.coeff (N + 1) (deningerBigWittEulerApprox f N) -
            PowerSeries.coeff (N + 1) f)
          (N + 1) := by
  rfl

@[simp] theorem deningerBigWittEulerApprox_constantCoeff
    (f : PowerSeries A) (N : ℕ) :
    PowerSeries.constantCoeff (deningerBigWittEulerApprox f N) = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [deningerBigWittEulerApprox_succ, map_mul, ih]
      simp [deningerBigWittFactor_constantCoeff]

theorem deningerBigWittEulerApprox_coeff_succ (f : PowerSeries A) (N : ℕ) :
    PowerSeries.coeff (N + 1) (deningerBigWittEulerApprox f (N + 1)) =
      PowerSeries.coeff (N + 1) f := by
  rw [deningerBigWittEulerApprox_succ, coeff_mul_deningerBigWittFactor_self,
    deningerBigWittEulerApprox_constantCoeff, one_mul, sub_sub_cancel]

theorem deningerBigWittEulerApprox_coeff_stable_step
    (f : PowerSeries A) {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k (deningerBigWittEulerApprox f (N + 1)) =
      PowerSeries.coeff k (deningerBigWittEulerApprox f N) := by
  rw [deningerBigWittEulerApprox_succ]
  exact coeff_mul_deningerBigWittFactor_of_lt _ _ (Nat.lt_succ_of_le hk)

theorem deningerBigWittEulerApprox_coeff
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1)
    {k N : ℕ} (hk : k ≤ N) :
    PowerSeries.coeff k (deningerBigWittEulerApprox f N) = PowerSeries.coeff k f := by
  induction N with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp [PowerSeries.coeff_zero_eq_constantCoeff, hf]
  | succ N ih =>
      rcases lt_or_eq_of_le hk with hklt | rfl
      · rw [deningerBigWittEulerApprox_coeff_stable_step f (Nat.le_of_lt_succ hklt)]
        exact ih (Nat.le_of_lt_succ hklt)
      · exact deningerBigWittEulerApprox_coeff_succ f N

/-- Integral Euler coordinate in degree `n+1`. -/
def deningerBigWittEulerCoord (f : PowerSeries A) (n : ℕ) : A :=
  PowerSeries.coeff (n + 1) (deningerBigWittEulerApprox f n) -
    PowerSeries.coeff (n + 1) f

theorem deningerBigWittEulerPartial_coord (f : PowerSeries A) (N : ℕ) :
    deningerBigWittEulerPartial (deningerBigWittEulerCoord f) N =
      deningerBigWittEulerApprox f N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [deningerBigWittEulerPartial_succ, deningerBigWittEulerApprox_succ, ih]
      rfl

theorem deningerBigWittEulerSeries_coord
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittEulerSeries (deningerBigWittEulerCoord f) = f := by
  apply PowerSeries.ext
  intro n
  rw [deningerBigWittEulerSeries_coeff, deningerBigWittEulerPartial_coord]
  exact deningerBigWittEulerApprox_coeff f hf le_rfl

theorem deningerBigWittEulerSeries_injective :
    Function.Injective (deningerBigWittEulerSeries (A := A)) := by
  intro x y hxy
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hprev : deningerBigWittEulerPartial x n = deningerBigWittEulerPartial y n := by
        apply Finset.prod_congr rfl
        intro i hi
        have hin : i < n := Finset.mem_range.mp hi
        rw [ih i hin]
      have hc := congrArg (PowerSeries.coeff (n + 1)) hxy
      simp only [deningerBigWittEulerSeries_coeff] at hc
      rw [deningerBigWittEulerPartial_succ, deningerBigWittEulerPartial_succ,
        coeff_mul_deningerBigWittFactor_self,
        coeff_mul_deningerBigWittFactor_self,
        deningerBigWittEulerPartial_constantCoeff,
        deningerBigWittEulerPartial_constantCoeff, one_mul, one_mul, hprev] at hc
      exact sub_right_inj.mp hc

@[simp] theorem deningerBigWittEulerCoord_series (x : ℕ → A) :
    deningerBigWittEulerCoord (deningerBigWittEulerSeries x) = x := by
  apply deningerBigWittEulerSeries_injective
  rw [deningerBigWittEulerSeries_coord]
  exact deningerBigWittEulerSeries_constantCoeff x

/-- Euler coordinates as an equivalence with the literal power-series-unit carrier. -/
def deningerBigWittEulerEquiv (A : Type*) [CommRing A] :
    (ℕ → A) ≃ DeningerBigWittAdditive A where
  toFun x := deningerBigWittOfSeries (deningerBigWittEulerSeries x)
    (deningerBigWittEulerSeries_constantCoeff x)
  invFun w := deningerBigWittEulerCoord (deningerBigWittSeries w)
  left_inv x := by simp
  right_inv w := by
    apply Subtype.ext
    apply Units.ext
    change deningerBigWittEulerSeries
        (deningerBigWittEulerCoord (deningerBigWittSeries w)) = deningerBigWittSeries w
    exact deningerBigWittEulerSeries_coord _ (deningerBigWittSeries_constantCoeff w)

@[simp] theorem deningerBigWittSeries_eulerEquiv (x : ℕ → A) :
    deningerBigWittSeries (deningerBigWittEulerEquiv A x) =
      deningerBigWittEulerSeries x := by
  rfl

@[simp] theorem deningerBigWittEulerEquiv_symm_apply
    (w : DeningerBigWittAdditive A) :
    (deningerBigWittEulerEquiv A).symm w =
      deningerBigWittEulerCoord (deningerBigWittSeries w) := by
  rfl

/-- Coefficientwise functoriality of the literal big-Witt additive carrier. -/
def deningerBigWittMap (f : A →+* B) :
    DeningerBigWittAdditive A →* DeningerBigWittAdditive B where
  toFun w :=
    ⟨Units.map (PowerSeries.map f) w.1, by
      apply Units.ext
      change PowerSeries.constantCoeff
          (PowerSeries.map f (deningerBigWittSeries w)) = 1
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        deningerBigWittSeries_constantCoeff, map_one]⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem deningerBigWittSeries_map (f : A →+* B)
    (w : DeningerBigWittAdditive A) :
    deningerBigWittSeries (deningerBigWittMap f w) =
      PowerSeries.map f (deningerBigWittSeries w) := by
  rfl

@[simp] theorem deningerBigWittFactor_map (f : A →+* B) (a : A) (m : ℕ) :
    PowerSeries.map f (deningerBigWittFactor a m) =
      deningerBigWittFactor (f a) m := by
  simp [deningerBigWittFactor]

@[simp] theorem deningerBigWittEulerPartial_map
    (f : A →+* B) (x : ℕ → A) (N : ℕ) :
    PowerSeries.map f (deningerBigWittEulerPartial x N) =
      deningerBigWittEulerPartial (f ∘ x) N := by
  simp [deningerBigWittEulerPartial]

@[simp] theorem deningerBigWittEulerSeries_map
    (f : A →+* B) (x : ℕ → A) :
    PowerSeries.map f (deningerBigWittEulerSeries x) =
      deningerBigWittEulerSeries (f ∘ x) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, deningerBigWittEulerSeries_coeff,
    deningerBigWittEulerSeries_coeff]
  exact congrArg (PowerSeries.coeff n) (deningerBigWittEulerPartial_map f x n)

@[simp] theorem deningerBigWittEulerApprox_map
    (f : A →+* B) (g : PowerSeries A) (N : ℕ) :
    PowerSeries.map f (deningerBigWittEulerApprox g N) =
      deningerBigWittEulerApprox (PowerSeries.map f g) N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [deningerBigWittEulerApprox_succ, map_mul, ih,
        deningerBigWittEulerApprox_succ]
      congr 1
      rw [deningerBigWittFactor_map]
      congr 1
      rw [map_sub]
      congr 1
      simpa only [PowerSeries.coeff_map] using
        congrArg (PowerSeries.coeff (N + 1)) ih

@[simp] theorem deningerBigWittEulerCoord_map
    (f : A →+* B) (g : PowerSeries A) :
    deningerBigWittEulerCoord (PowerSeries.map f g) =
      f ∘ deningerBigWittEulerCoord g := by
  funext n
  simp only [deningerBigWittEulerCoord, Function.comp_apply, map_sub,
    PowerSeries.coeff_map]
  congr 1
  simpa only [PowerSeries.coeff_map] using
    congrArg (PowerSeries.coeff (n + 1))
      (deningerBigWittEulerApprox_map f g n).symm

@[simp] theorem deningerBigWittEulerEquiv_natural
    (f : A →+* B) (x : ℕ → A) :
    deningerBigWittMap f (deningerBigWittEulerEquiv A x) =
      deningerBigWittEulerEquiv B (f ∘ x) := by
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map f (deningerBigWittEulerSeries x) =
    deningerBigWittEulerSeries (f ∘ x)
  simp

@[simp] theorem deningerBigWittMap_id (w : DeningerBigWittAdditive A) :
    deningerBigWittMap (RingHom.id A) w = w := by
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n
      (PowerSeries.map (RingHom.id A) (deningerBigWittSeries w)) =
    PowerSeries.coeff n (deningerBigWittSeries w)
  rw [PowerSeries.coeff_map]
  rfl

@[simp] theorem deningerBigWittMap_comp
    {C : Type*} [CommRing C] (g : B →+* C) (f : A →+* B)
    (w : DeningerBigWittAdditive A) :
    deningerBigWittMap (g.comp f) w =
      deningerBigWittMap g (deningerBigWittMap f w) := by
  apply Subtype.ext
  apply Units.ext
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n
      (PowerSeries.map (g.comp f) (deningerBigWittSeries w)) =
    PowerSeries.coeff n
      (PowerSeries.map g (PowerSeries.map f (deningerBigWittSeries w)))
  simp only [PowerSeries.coeff_map]
  rfl

end

end RHTower
