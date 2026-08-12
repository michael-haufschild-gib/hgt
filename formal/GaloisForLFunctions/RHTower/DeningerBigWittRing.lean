import GaloisForLFunctions.RHTower.DeningerBigWittGhost
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Canonical big-Witt ring over an arbitrary commutative ring

This module supplies the ring laws omitted by a ghost-coordinate-only construction.  First they
are proved over additively torsion-free rings, where the integral logarithmic ghost is injective.
For an arbitrary target ring, all participating Euler coordinates are lifted simultaneously to
the polynomial ring `ℤ[X_(i,n)]`; the torsion-free identity is then evaluated back into the target.
This is the universal-polynomial descent used by Lenstra and Cuntz--Deninger, and remains valid in
the presence of nilpotents.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A : Type*} [CommRing A]

/-- Euler coordinates of the multiplicative identity of the big-Witt ring. -/
def deningerBigWittOneCoord (A : Type*) [CommRing A] : ℕ → A :=
  fun n => if n = 0 then 1 else 0

/-- Multiplicative identity `[1] = 1-T` of the big-Witt ring. -/
def deningerBigWittOne (A : Type*) [CommRing A] : DeningerBigWittAdditive A :=
  deningerBigWittEulerEquiv A (deningerBigWittOneCoord A)

@[simp] theorem deningerBigWittOne_natural
    {B : Type*} [CommRing B] (f : A →+* B) :
    deningerBigWittMap f (deningerBigWittOne A) = deningerBigWittOne B := by
  rw [deningerBigWittOne, deningerBigWittEulerEquiv_natural]
  congr 1
  funext n
  simp [deningerBigWittOneCoord]

@[simp] theorem deningerBigWittGhostCoeff_one {k : ℕ} (hk : 0 < k) :
    deningerBigWittGhostCoeff (deningerBigWittOne A) k = 1 := by
  rw [deningerBigWittOne, deningerBigWittGhostCoeff_euler _ hk]
  unfold deningerBigWittEulerGhost
  rw [Finset.sum_eq_single 0]
  · simp [deningerBigWittOneCoord]
  · intro i hi hi0
    simp only [deningerBigWittOneCoord, hi0, if_false]
    by_cases hik : i + 1 ∣ k
    · rw [if_pos hik]
      have hq : 0 < k / (i + 1) :=
        Nat.div_pos (Nat.le_of_dvd hk hik) (Nat.succ_pos i)
      rw [zero_pow hq.ne']
      simp
    · rw [if_neg hik]
  · simp [hk]

/-- Euler coordinates of the Teichmüller representative `[a]=1-aT`. -/
def deningerBigWittTeichCoord (a : A) : ℕ → A :=
  fun n => if n = 0 then a else 0

/-- Teichmüller representative on the literal power-series carrier. -/
def deningerBigWittTeichCarrier (a : A) : DeningerBigWittAdditive A :=
  deningerBigWittEulerEquiv A (deningerBigWittTeichCoord a)

@[simp] theorem deningerBigWittTeichCarrier_natural
    {B : Type*} [CommRing B] (f : A →+* B) (a : A) :
    deningerBigWittMap f (deningerBigWittTeichCarrier a) =
      deningerBigWittTeichCarrier (f a) := by
  rw [deningerBigWittTeichCarrier, deningerBigWittEulerEquiv_natural]
  congr 1
  funext n
  by_cases hn : n = 0 <;> simp [deningerBigWittTeichCoord, hn]

/-- Literal series represented by a Teichmüller carrier. -/
@[simp] theorem deningerBigWittSeries_teichCarrier (a : A) :
    deningerBigWittSeries (deningerBigWittTeichCarrier a) =
      deningerBigWittFactor a 1 := by
  change deningerBigWittEulerSeries (deningerBigWittTeichCoord a) = _
  apply PowerSeries.ext
  intro n
  rw [deningerBigWittEulerSeries_coeff]
  by_cases hn : n = 0
  · subst n
    simp [deningerBigWittEulerPartial, deningerBigWittFactor]
  · unfold deningerBigWittEulerPartial
    rw [Finset.prod_eq_single 0]
    · simp [deningerBigWittTeichCoord]
    · intro i hi hi0
      simp [deningerBigWittTeichCoord, hi0, deningerBigWittFactor]
    · simp [Nat.pos_of_ne_zero hn]

@[simp] theorem deningerBigWittTeichCarrier_zero :
    deningerBigWittTeichCarrier (0 : A) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change deningerBigWittSeries (deningerBigWittTeichCarrier (0 : A)) =
    (1 : PowerSeries A)
  rw [deningerBigWittSeries_teichCarrier]
  simp [deningerBigWittFactor]

@[simp] theorem deningerBigWittTeichCarrier_one :
    deningerBigWittTeichCarrier (1 : A) = deningerBigWittOne A := by
  rw [deningerBigWittTeichCarrier, deningerBigWittOne]
  congr 1

@[simp] theorem deningerBigWittGhostCoeff_teich
    (a : A) {k : ℕ} (hk : 0 < k) :
    deningerBigWittGhostCoeff (deningerBigWittTeichCarrier a) k = a ^ k := by
  rw [deningerBigWittTeichCarrier, deningerBigWittGhostCoeff_euler _ hk]
  unfold deningerBigWittEulerGhost
  rw [Finset.sum_eq_single 0]
  · simp [deningerBigWittTeichCoord]
  · intro i hi hi0
    simp only [deningerBigWittTeichCoord, hi0, if_false]
    by_cases hik : i + 1 ∣ k
    · rw [if_pos hik]
      have hq : 0 < k / (i + 1) :=
        Nat.div_pos (Nat.le_of_dvd hk hik) (Nat.succ_pos i)
      rw [zero_pow hq.ne']
      simp
    · rw [if_neg hik]
  · simp [hk]

theorem deningerBigWittMul_teich_of_torsionFree
    [IsAddTorsionFree A] (a b : A) :
    deningerBigWittMul (deningerBigWittTeichCarrier a)
        (deningerBigWittTeichCarrier b) =
      deningerBigWittTeichCarrier (a * b) := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      change deningerBigWittGhostCoeff
          (deningerBigWittMul (deningerBigWittTeichCarrier a)
            (deningerBigWittTeichCarrier b)) (Nat.succ k) =
        deningerBigWittGhostCoeff (deningerBigWittTeichCarrier (a * b)) (Nat.succ k)
      rw [deningerBigWittGhostCoeff_mul _ _ (Nat.succ_pos k),
        deningerBigWittGhostCoeff_teich _ (Nat.succ_pos k),
        deningerBigWittGhostCoeff_teich _ (Nat.succ_pos k),
        deningerBigWittGhostCoeff_teich _ (Nat.succ_pos k), mul_pow]

@[simp] theorem deningerBigWittGhostCoeff_add
    (u v : DeningerBigWittAdditive A) (k : ℕ) :
    deningerBigWittGhostCoeff (u * v) k =
      deningerBigWittGhostCoeff u k + deningerBigWittGhostCoeff v k := by
  exact congrArg (PowerSeries.coeff k) (deningerBigWittGhostSeries_mul u v)

theorem deningerBigWittMul_assoc_of_torsionFree
    [IsAddTorsionFree A] (u v w : DeningerBigWittAdditive A) :
    deningerBigWittMul (deningerBigWittMul u v) w =
      deningerBigWittMul u (deningerBigWittMul v w) := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      change deningerBigWittGhostCoeff
          (deningerBigWittMul (deningerBigWittMul u v) w) (Nat.succ k) =
        deningerBigWittGhostCoeff
          (deningerBigWittMul u (deningerBigWittMul v w)) (Nat.succ k)
      simp only [deningerBigWittGhostCoeff_mul _ _ (Nat.succ_pos k)]
      rw [mul_assoc]

theorem deningerBigWittOne_mul_of_torsionFree
    [IsAddTorsionFree A] (u : DeningerBigWittAdditive A) :
    deningerBigWittMul (deningerBigWittOne A) u = u := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      change deningerBigWittGhostCoeff
          (deningerBigWittMul (deningerBigWittOne A) u) (Nat.succ k) =
        deningerBigWittGhostCoeff u (Nat.succ k)
      rw [deningerBigWittGhostCoeff_mul _ _ (Nat.succ_pos k),
        deningerBigWittGhostCoeff_one (Nat.succ_pos k), one_mul]

theorem deningerBigWittZero_mul_of_torsionFree
    [IsAddTorsionFree A] (u : DeningerBigWittAdditive A) :
    deningerBigWittMul (1 : DeningerBigWittAdditive A) u = 1 := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      change deningerBigWittGhostCoeff
          (deningerBigWittMul (1 : DeningerBigWittAdditive A) u) (Nat.succ k) =
        deningerBigWittGhostCoeff (1 : DeningerBigWittAdditive A) (Nat.succ k)
      rw [deningerBigWittGhostCoeff_mul _ _ (Nat.succ_pos k)]
      simp [deningerBigWittGhostCoeff]

theorem deningerBigWittMul_add_of_torsionFree
    [IsAddTorsionFree A] (u v w : DeningerBigWittAdditive A) :
    deningerBigWittMul u (v * w) =
      deningerBigWittMul u v * deningerBigWittMul u w := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      change deningerBigWittGhostCoeff
          (deningerBigWittMul u (v * w)) (Nat.succ k) =
        deningerBigWittGhostCoeff
          (deningerBigWittMul u v * deningerBigWittMul u w) (Nat.succ k)
      simp only [deningerBigWittGhostCoeff_mul _ _ (Nat.succ_pos k),
        deningerBigWittGhostCoeff_add]
      rw [mul_add]

/-- Universal torsion-free coefficient ring for `d` simultaneous big-Witt vectors. -/
abbrev DeningerBigWittUniversalRing (d : ℕ) := MvPolynomial (Fin d × ℕ) ℤ

/-- Universal vector whose Euler coordinates are independent integer variables. -/
def deningerBigWittUniversalVector (d : ℕ) (i : Fin d) :
    DeningerBigWittAdditive (DeningerBigWittUniversalRing d) :=
  deningerBigWittEulerEquiv _ (fun n => MvPolynomial.X (i, n))

/-- Evaluation carrying all universal Euler coordinates to prescribed vectors at once. -/
def deningerBigWittUniversalEval (d : ℕ)
    (x : Fin d → DeningerBigWittAdditive A) :
    DeningerBigWittUniversalRing d →+* A :=
  MvPolynomial.eval₂Hom (Int.castRingHom A)
    (fun p => (deningerBigWittEulerEquiv A).symm (x p.1) p.2)

@[simp] theorem deningerBigWittUniversalEval_vector
    (d : ℕ) (x : Fin d → DeningerBigWittAdditive A) (i : Fin d) :
    deningerBigWittMap (deningerBigWittUniversalEval d x)
        (deningerBigWittUniversalVector d i) = x i := by
  rw [deningerBigWittUniversalVector, deningerBigWittEulerEquiv_natural]
  calc
    (deningerBigWittEulerEquiv A)
        ((deningerBigWittUniversalEval d x) ∘
          fun n => MvPolynomial.X (i, n)) =
        (deningerBigWittEulerEquiv A).symm.symm
          ((deningerBigWittEulerEquiv A).symm (x i)) := by
            congr 1
            funext n
            simp [deningerBigWittUniversalEval]
    _ = x i := (deningerBigWittEulerEquiv A).apply_symm_apply (x i)

/-- Full Teichmüller multiplication law over an arbitrary ring, including nilpotent elements. -/
theorem deningerBigWittMul_teich (a b : A) :
    deningerBigWittMul (deningerBigWittTeichCarrier a)
        (deningerBigWittTeichCarrier b) =
      deningerBigWittTeichCarrier (a * b) := by
  let x : Fin 2 → A := ![a, b]
  let ev : MvPolynomial (Fin 2) ℤ →+* A :=
    MvPolynomial.eval₂Hom (Int.castRingHom A) x
  have h := deningerBigWittMul_teich_of_torsionFree
    (A := MvPolynomial (Fin 2) ℤ)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))
  have hm := congrArg (deningerBigWittMap ev) h
  simpa [ev, x] using hm

/-- Associativity over an arbitrary ring, descended from the universal integer polynomial ring. -/
theorem deningerBigWittMul_assoc
    (u v w : DeningerBigWittAdditive A) :
    deningerBigWittMul (deningerBigWittMul u v) w =
      deningerBigWittMul u (deningerBigWittMul v w) := by
  let x : Fin 3 → DeningerBigWittAdditive A :=
    ![u, v, w]
  have h := deningerBigWittMul_assoc_of_torsionFree
    (deningerBigWittUniversalVector 3 (0 : Fin 3))
    (deningerBigWittUniversalVector 3 (1 : Fin 3))
    (deningerBigWittUniversalVector 3 (2 : Fin 3))
  have hm := congrArg (deningerBigWittMap (deningerBigWittUniversalEval 3 x)) h
  simpa [x] using hm

/-- Left identity over an arbitrary ring; no injectivity assumption on target ghosts. -/
theorem deningerBigWittOne_mul (u : DeningerBigWittAdditive A) :
    deningerBigWittMul (deningerBigWittOne A) u = u := by
  let x : Fin 1 → DeningerBigWittAdditive A := fun _ => u
  have h := deningerBigWittOne_mul_of_torsionFree
    (deningerBigWittUniversalVector 1 (0 : Fin 1))
  have hm := congrArg (deningerBigWittMap (deningerBigWittUniversalEval 1 x)) h
  simpa only [deningerBigWittMul_natural, deningerBigWittOne_natural,
    deningerBigWittUniversalEval_vector, x] using hm

theorem deningerBigWittMul_one (u : DeningerBigWittAdditive A) :
    deningerBigWittMul u (deningerBigWittOne A) = u := by
  rw [deningerBigWittMul_comm, deningerBigWittOne_mul]

/-- Absorption by Witt zero (`1` as an ordinary power-series unit), valid with nilpotents. -/
theorem deningerBigWittZero_mul (u : DeningerBigWittAdditive A) :
    deningerBigWittMul (1 : DeningerBigWittAdditive A) u = 1 := by
  let x : Fin 1 → DeningerBigWittAdditive A := fun _ => u
  have h := deningerBigWittZero_mul_of_torsionFree
    (deningerBigWittUniversalVector 1 (0 : Fin 1))
  have hm := congrArg (deningerBigWittMap (deningerBigWittUniversalEval 1 x)) h
  simpa only [deningerBigWittMul_natural, map_one,
    deningerBigWittUniversalEval_vector, x] using hm

theorem deningerBigWittMul_zero (u : DeningerBigWittAdditive A) :
    deningerBigWittMul u (1 : DeningerBigWittAdditive A) = 1 := by
  rw [deningerBigWittMul_comm, deningerBigWittZero_mul]

/-- Left distributivity, universally descended and hence unconditional in the target ring. -/
theorem deningerBigWittMul_add
    (u v w : DeningerBigWittAdditive A) :
    deningerBigWittMul u (v * w) =
      deningerBigWittMul u v * deningerBigWittMul u w := by
  let x : Fin 3 → DeningerBigWittAdditive A :=
    ![u, v, w]
  have h := deningerBigWittMul_add_of_torsionFree
    (deningerBigWittUniversalVector 3 (0 : Fin 3))
    (deningerBigWittUniversalVector 3 (1 : Fin 3))
    (deningerBigWittUniversalVector 3 (2 : Fin 3))
  have hm := congrArg (deningerBigWittMap (deningerBigWittUniversalEval 3 x)) h
  simpa [x] using hm

theorem deningerBigWittAdd_mul
    (u v w : DeningerBigWittAdditive A) :
    deningerBigWittMul (u * v) w =
      deningerBigWittMul u w * deningerBigWittMul v w := by
  rw [deningerBigWittMul_comm (u * v) w, deningerBigWittMul_add]
  rw [deningerBigWittMul_comm w u, deningerBigWittMul_comm w v]

/-- Literal big-Witt carrier, wrapped so Lean notation can distinguish Witt addition (ordinary
power-series multiplication) from Witt multiplication. -/
@[ext] structure DeningerBigWittRing (A : Type*) [CommRing A] where
  additiveVal : Additive (DeningerBigWittAdditive A)

/-- Carrier equivalence used only to transport the already literal additive group. -/
def deningerBigWittRingAddEquiv (A : Type*) [CommRing A] :
    DeningerBigWittRing A ≃ Additive (DeningerBigWittAdditive A) where
  toFun := DeningerBigWittRing.additiveVal
  invFun := DeningerBigWittRing.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

noncomputable instance deningerBigWittRingAddCommGroup
    (A : Type*) [CommRing A] : AddCommGroup (DeningerBigWittRing A) :=
  (deningerBigWittRingAddEquiv A).addCommGroup

/-- Ring structure whose addition is literal series multiplication and whose multiplication is the
integral gcd--lcm Euler product. -/
noncomputable instance deningerBigWittRingRing
    (A : Type*) [CommRing A] : Ring (DeningerBigWittRing A) where
  mul x y := ⟨Additive.ofMul (deningerBigWittMul
    (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal))⟩
  one := ⟨Additive.ofMul (deningerBigWittOne A)⟩
  mul_assoc x y z := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul
      (deningerBigWittMul (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal))
      (Additive.toMul z.additiveVal)) = Additive.ofMul (deningerBigWittMul
        (Additive.toMul x.additiveVal)
        (deningerBigWittMul (Additive.toMul y.additiveVal) (Additive.toMul z.additiveVal)))
    exact congrArg Additive.ofMul (deningerBigWittMul_assoc
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal)
      (Additive.toMul z.additiveVal))
  one_mul x := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul (deningerBigWittOne A)
      (Additive.toMul x.additiveVal)) = x.additiveVal
    exact congrArg Additive.ofMul
      (deningerBigWittOne_mul (Additive.toMul x.additiveVal))
  mul_one x := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul (Additive.toMul x.additiveVal)
      (deningerBigWittOne A)) = x.additiveVal
    exact congrArg Additive.ofMul
      (deningerBigWittMul_one (Additive.toMul x.additiveVal))
  zero_mul x := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul 1
      (Additive.toMul x.additiveVal)) = Additive.ofMul 1
    exact congrArg Additive.ofMul
      (deningerBigWittZero_mul (Additive.toMul x.additiveVal))
  mul_zero x := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul (Additive.toMul x.additiveVal) 1) =
      Additive.ofMul 1
    exact congrArg Additive.ofMul
      (deningerBigWittMul_zero (Additive.toMul x.additiveVal))
  left_distrib x y z := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul (Additive.toMul x.additiveVal)
      (Additive.toMul y.additiveVal * Additive.toMul z.additiveVal)) =
      Additive.ofMul (deningerBigWittMul (Additive.toMul x.additiveVal)
        (Additive.toMul y.additiveVal) * deningerBigWittMul
          (Additive.toMul x.additiveVal) (Additive.toMul z.additiveVal))
    exact congrArg Additive.ofMul (deningerBigWittMul_add
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal)
      (Additive.toMul z.additiveVal))
  right_distrib x y z := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul
      (Additive.toMul x.additiveVal * Additive.toMul y.additiveVal)
      (Additive.toMul z.additiveVal)) = Additive.ofMul
        (deningerBigWittMul (Additive.toMul x.additiveVal) (Additive.toMul z.additiveVal) *
          deningerBigWittMul (Additive.toMul y.additiveVal) (Additive.toMul z.additiveVal))
    exact congrArg Additive.ofMul (deningerBigWittAdd_mul
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal)
      (Additive.toMul z.additiveVal))

/-- Canonical commutative big-Witt ring over every commutative base ring. -/
noncomputable instance deningerBigWittRingCommRing
    (A : Type*) [CommRing A] : CommRing (DeningerBigWittRing A) :=
  CommRing.mk (fun x y => by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMul (Additive.toMul x.additiveVal)
      (Additive.toMul y.additiveVal)) = Additive.ofMul
        (deningerBigWittMul (Additive.toMul y.additiveVal) (Additive.toMul x.additiveVal))
    exact congrArg Additive.ofMul (deningerBigWittMul_comm
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal)))

/-- Witt addition is literally multiplication in `1+TA[[T]]`. -/
@[simp] theorem deningerBigWittRing_additiveVal_add
    (x y : DeningerBigWittRing A) :
    (x + y).additiveVal = x.additiveVal + y.additiveVal := rfl

/-- Witt multiplication is literally the completed gcd--lcm Euler product. -/
@[simp] theorem deningerBigWittRing_additiveVal_mul
    (x y : DeningerBigWittRing A) :
    (x * y).additiveVal = Additive.ofMul (deningerBigWittMul
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal)) := rfl

@[simp] theorem deningerBigWittRing_additiveVal_zero :
    (0 : DeningerBigWittRing A).additiveVal = Additive.ofMul 1 := rfl

@[simp] theorem deningerBigWittRing_additiveVal_one :
    (1 : DeningerBigWittRing A).additiveVal =
      Additive.ofMul (deningerBigWittOne A) := rfl

/-- Functorial map of canonical big-Witt rings. -/
noncomputable def deningerBigWittRingMap
    {B : Type*} [CommRing B] (f : A →+* B) :
    DeningerBigWittRing A →+* DeningerBigWittRing B where
  toFun x := ⟨Additive.ofMul
    (deningerBigWittMap f (Additive.toMul x.additiveVal))⟩
  map_zero' := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMap f 1) = Additive.ofMul 1
    rw [map_one]
  map_add' x y := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMap f
      (Additive.toMul x.additiveVal * Additive.toMul y.additiveVal)) =
      Additive.ofMul (deningerBigWittMap f (Additive.toMul x.additiveVal) *
        deningerBigWittMap f (Additive.toMul y.additiveVal))
    rw [map_mul]
  map_one' := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMap f (deningerBigWittOne A)) =
      Additive.ofMul (deningerBigWittOne B)
    rw [deningerBigWittOne_natural]
  map_mul' x y := by
    apply DeningerBigWittRing.ext
    change Additive.ofMul (deningerBigWittMap f (deningerBigWittMul
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal))) =
      Additive.ofMul (deningerBigWittMul
        (deningerBigWittMap f (Additive.toMul x.additiveVal))
        (deningerBigWittMap f (Additive.toMul y.additiveVal)))
    rw [deningerBigWittMul_natural]

@[simp] theorem deningerBigWittRingMap_additiveVal
    {B : Type*} [CommRing B] (f : A →+* B) (x : DeningerBigWittRing A) :
    (deningerBigWittRingMap f x).additiveVal =
      Additive.ofMul (deningerBigWittMap f (Additive.toMul x.additiveVal)) := rfl

@[simp] theorem deningerBigWittRingMap_id (x : DeningerBigWittRing A) :
    deningerBigWittRingMap (RingHom.id A) x = x := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittMap (RingHom.id A)
    (Additive.toMul x.additiveVal)) = x.additiveVal
  rw [deningerBigWittMap_id]
  rfl

@[simp] theorem deningerBigWittRingMap_comp
    {B C : Type*} [CommRing B] [CommRing C]
    (g : B →+* C) (f : A →+* B) (x : DeningerBigWittRing A) :
    deningerBigWittRingMap (g.comp f) x =
      deningerBigWittRingMap g (deningerBigWittRingMap f x) := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittMap (g.comp f)
    (Additive.toMul x.additiveVal)) = Additive.ofMul
      (deningerBigWittMap g (deningerBigWittMap f
        (Additive.toMul x.additiveVal)))
  rw [deningerBigWittMap_comp]

/-- Teichmüller map into the canonical big-Witt ring. -/
def deningerBigWittRingTeichmuller (a : A) : DeningerBigWittRing A :=
  ⟨Additive.ofMul (deningerBigWittTeichCarrier a)⟩

@[simp] theorem deningerBigWittRingTeichmuller_zero :
    deningerBigWittRingTeichmuller (0 : A) = 0 := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittTeichCarrier (0 : A)) = Additive.ofMul 1
  rw [deningerBigWittTeichCarrier_zero]

@[simp] theorem deningerBigWittRingTeichmuller_one :
    deningerBigWittRingTeichmuller (1 : A) = 1 := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittTeichCarrier (1 : A)) =
    Additive.ofMul (deningerBigWittOne A)
  rw [deningerBigWittTeichCarrier_one]

@[simp] theorem deningerBigWittRingTeichmuller_mul (a b : A) :
    deningerBigWittRingTeichmuller a * deningerBigWittRingTeichmuller b =
      deningerBigWittRingTeichmuller (a * b) := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittMul (deningerBigWittTeichCarrier a)
    (deningerBigWittTeichCarrier b)) = Additive.ofMul
      (deningerBigWittTeichCarrier (a * b))
  exact congrArg Additive.ofMul (deningerBigWittMul_teich a b)

@[simp] theorem deningerBigWittRingMap_teichmuller
    {B : Type*} [CommRing B] (f : A →+* B) (a : A) :
    deningerBigWittRingMap f (deningerBigWittRingTeichmuller a) =
      deningerBigWittRingTeichmuller (f a) := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul (deningerBigWittMap f (deningerBigWittTeichCarrier a)) =
    Additive.ofMul (deningerBigWittTeichCarrier (f a))
  rw [deningerBigWittTeichCarrier_natural]

/-- Positive ghost component as an unconditional ring homomorphism. -/
noncomputable def deningerBigWittGhostComponent (k : ℕ) (hk : 0 < k) :
    DeningerBigWittRing A →+* A where
  toFun x := deningerBigWittGhostCoeff (Additive.toMul x.additiveVal) k
  map_zero' := by
    simp [deningerBigWittGhostCoeff]
  map_add' x y := by
    exact deningerBigWittGhostCoeff_add
      (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal) k
  map_one' := deningerBigWittGhostCoeff_one hk
  map_mul' x y := deningerBigWittGhostCoeff_mul
    (Additive.toMul x.additiveVal) (Additive.toMul y.additiveVal) hk

@[simp] theorem deningerBigWittGhostComponent_teichmuller
    (k : ℕ) (hk : 0 < k) (a : A) :
    deningerBigWittGhostComponent k hk (deningerBigWittRingTeichmuller a) =
      a ^ k := by
  exact deningerBigWittGhostCoeff_teich a hk

end

end RHTower
