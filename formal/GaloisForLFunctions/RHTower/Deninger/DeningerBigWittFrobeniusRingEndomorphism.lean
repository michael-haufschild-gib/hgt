import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusPrimeSeamTransgression

/-!
# Canonical Frobenius two on the arbitrary-ring big-Witt ring

The division-free norm series `f(T) f(-T)` constructed in the prime-seam
transgression is promoted here to the canonical big-Witt Frobenius ring
endomorphism over every commutative ring, including rings with additive
torsion and nilpotents.

The proof first works over an additively torsion-free ring. Involution
invariance then forces the odd coefficients of `f(T) f(-T)` to vanish, so its
coefficient contraction expands back to the literal norm. Formal logarithmic
differentiation gives the full ghost shift

`ghost_k (F₂ w) = ghost_(2k) w`.

Additivity and multiplicativity follow by ghost injectivity only in the
torsion-free universal polynomial ring. Universal Euler-coordinate evaluation
then descends both ring laws and the full ghost shift to arbitrary targets;
no target reducedness, torsion-freeness, or ghost injectivity is assumed.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A : Type*} [CommRing A]

theorem deningerPowerSeriesDerivative_rescale (a : A) (f : PowerSeries A) :
    PowerSeries.derivative A (PowerSeries.rescale a f) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.derivative A f) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
    PowerSeries.coeff_C_mul]
  rw [pow_succ']
  ring

theorem deningerPowerSeriesDerivative_expand (p : ℕ) (hp : p ≠ 0) (f : PowerSeries A) :
    PowerSeries.derivative A (PowerSeries.expand p hp f) =
      PowerSeries.expand p hp (PowerSeries.derivative A f) *
        ((p : PowerSeries A) * PowerSeries.X ^ (p - 1)) := by
  rw [PowerSeries.expand_apply,
    PowerSeries.derivative_subst A (PowerSeries.HasSubst.X_pow hp),
    PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one,
    ← PowerSeries.expand_apply]

theorem deningerBigWittLogGhost_rescale
    (a : A) (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittLogGhost (PowerSeries.rescale a f) (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale, pow_zero, one_mul,
        PowerSeries.coeff_zero_eq_constantCoeff, hf]) =
      PowerSeries.rescale a (deningerBigWittLogGhost f hf) := by
  have hu : IsUnit (PowerSeries.rescale a f) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale, pow_zero, one_mul,
        PowerSeries.coeff_zero_eq_constantCoeff, hf]
      exact isUnit_one)
  apply hu.mul_right_cancel
  rw [deningerBigWittLogGhost_mul_self]
  symm
  calc
    PowerSeries.rescale a (deningerBigWittLogGhost f hf) *
          PowerSeries.rescale a f =
        PowerSeries.rescale a (deningerBigWittLogGhost f hf * f) := by
          rw [map_mul]
    _ = PowerSeries.rescale a
          (-(PowerSeries.X * PowerSeries.derivative A f)) := by
          rw [deningerBigWittLogGhost_mul_self]
    _ = -(PowerSeries.X * PowerSeries.derivative A
          (PowerSeries.rescale a f)) := by
          rw [map_neg, map_mul, PowerSeries.rescale_X,
            deningerPowerSeriesDerivative_rescale]
          ring

theorem deningerBigWittLogGhost_expand
    (p : ℕ) (hp : p ≠ 0) (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittLogGhost (PowerSeries.expand p hp f) (by
      rw [PowerSeries.constantCoeff_expand, hf]) =
      PowerSeries.C (p : A) *
        PowerSeries.expand p hp (deningerBigWittLogGhost f hf) := by
  have hu : IsUnit (PowerSeries.expand p hp f) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by
      rw [PowerSeries.constantCoeff_expand, hf]
      exact isUnit_one)
  apply hu.mul_right_cancel
  rw [deningerBigWittLogGhost_mul_self]
  symm
  calc
    (PowerSeries.C (p : A) *
          PowerSeries.expand p hp (deningerBigWittLogGhost f hf)) *
          PowerSeries.expand p hp f =
        PowerSeries.C (p : A) * PowerSeries.expand p hp
          (deningerBigWittLogGhost f hf * f) := by
          rw [map_mul]
          ring
    _ = PowerSeries.C (p : A) * PowerSeries.expand p hp
          (-(PowerSeries.X * PowerSeries.derivative A f)) := by
          rw [deningerBigWittLogGhost_mul_self]
    _ = -(PowerSeries.X * PowerSeries.derivative A
          (PowerSeries.expand p hp f)) := by
          rw [map_neg, map_mul, PowerSeries.expand_X,
            deningerPowerSeriesDerivative_expand]
          have hXp : (PowerSeries.X : PowerSeries A) *
              PowerSeries.X ^ (p - 1) = PowerSeries.X ^ p := by
            rw [← pow_succ' PowerSeries.X,
              Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)]
          rw [← hXp]
          have hpC : (p : PowerSeries A) = PowerSeries.C (p : A) := by simp
          rw [hpC]
          ring

theorem deningerBigWittFrobeniusTwoNorm_invariant (f : PowerSeries A) :
    PowerSeries.rescale (-1 : A)
        (f * PowerSeries.rescale (-1 : A) f) =
      f * PowerSeries.rescale (-1 : A) f := by
  rw [map_mul, PowerSeries.rescale_rescale]
  have hneg : (-1 : A) * -1 = 1 := by ring
  rw [hneg, show PowerSeries.rescale (1 : A) f = f by simp]
  ring

theorem deningerBigWittFrobeniusTwoNormSeries_expand_of_torsionFree
    [IsAddTorsionFree A] (w : DeningerBigWittRing A) :
    PowerSeries.expand 2 (by decide)
        (deningerBigWittFrobeniusTwoNormSeries w) =
      deningerBigWittRingSeries w *
        PowerSeries.rescale (-1 : A) (deningerBigWittRingSeries w) := by
  let f := deningerBigWittRingSeries w
  apply PowerSeries.ext
  intro n
  by_cases hn : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_expand_mul]
    simp [deningerBigWittFrobeniusTwoNormSeries]
  · rw [PowerSeries.coeff_expand_of_not_dvd 2 (by decide) _ hn]
    have hinv := congrArg (PowerSeries.coeff n)
      (deningerBigWittFrobeniusTwoNorm_invariant f)
    simp only [PowerSeries.coeff_rescale] at hinv
    have hodd : Odd n := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hn)
    rw [hodd.neg_one_pow, neg_one_mul] at hinv
    have hadd : PowerSeries.coeff n
          (f * PowerSeries.rescale (-1 : A) f) +
        PowerSeries.coeff n
          (f * PowerSeries.rescale (-1 : A) f) = 0 :=
      neg_eq_iff_add_eq_zero.mp hinv
    symm
    apply (nsmul_right_injective (M := A) (by decide : (2 : ℕ) ≠ 0))
    simpa [two_mul, f] using hadd

theorem deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree
    [IsAddTorsionFree A] (w : DeningerBigWittRing A)
    (k : ℕ) (hk : 0 < k) :
    deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo w) =
      deningerBigWittGhostComponent (2 * k) (Nat.mul_pos (by decide) hk) w := by
  let f := deningerBigWittRingSeries w
  let g := deningerBigWittFrobeniusTwoNormSeries w
  have hf : PowerSeries.constantCoeff f = 1 := deningerBigWittSeries_constantCoeff _
  have hg : PowerSeries.constantCoeff g = 1 :=
    deningerBigWittFrobeniusTwoNormSeries_constantCoeff w
  have hnorm : PowerSeries.expand 2 (by decide) g =
      f * PowerSeries.rescale (-1 : A) f := by
    exact deningerBigWittFrobeniusTwoNormSeries_expand_of_torsionFree w
  have hlog := deningerBigWittLogGhost_congr
    (by rw [PowerSeries.constantCoeff_expand, hg])
    (by
      rw [map_mul, hf, one_mul,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale, pow_zero, one_mul,
        PowerSeries.coeff_zero_eq_constantCoeff, hf]) hnorm
  rw [deningerBigWittLogGhost_expand 2 (by decide) g hg,
    deningerBigWittLogGhost_mul f (PowerSeries.rescale (-1 : A) f) hf (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_rescale, pow_zero, one_mul,
        PowerSeries.coeff_zero_eq_constantCoeff, hf]),
    deningerBigWittLogGhost_rescale (-1 : A) f hf] at hlog
  have hc := congrArg (PowerSeries.coeff (2 * k)) hlog
  have heven : Even (2 * k) := even_two.mul_right k
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_expand_mul,
    map_add, PowerSeries.coeff_rescale,
    heven.neg_one_pow, one_mul] at hc
  have hFw : PowerSeries.constantCoeff
      (deningerBigWittRingSeries (deningerBigWittFrobeniusTwo w)) = 1 :=
    deningerBigWittSeries_constantCoeff _
  have hw : PowerSeries.constantCoeff (deningerBigWittRingSeries w) = 1 :=
    deningerBigWittSeries_constantCoeff _
  change PowerSeries.coeff k
      (deningerBigWittLogGhost
        (deningerBigWittRingSeries (deningerBigWittFrobeniusTwo w)) hFw) =
    PowerSeries.coeff (2 * k)
      (deningerBigWittLogGhost (deningerBigWittRingSeries w) hw)
  have hFg : deningerBigWittLogGhost
        (deningerBigWittRingSeries (deningerBigWittFrobeniusTwo w)) hFw =
      deningerBigWittLogGhost g hg :=
    deningerBigWittLogGhost_congr hFw hg
      (deningerBigWittRingSeries_frobeniusTwo w)
  rw [hFg]
  apply (nsmul_right_injective (M := A) (by decide : (2 : ℕ) ≠ 0))
  simpa [two_nsmul, two_mul, f, g, deningerBigWittGhostSeries,
    deningerBigWittRingSeries] using hc

theorem deningerBigWittRing_ext_ghost [IsAddTorsionFree A]
    {x y : DeningerBigWittRing A}
    (h : ∀ (k : ℕ) (hk : 0 < k),
      deningerBigWittGhostComponent k hk x =
        deningerBigWittGhostComponent k hk y) :
    x = y := by
  apply DeningerBigWittRing.ext
  apply congrArg Additive.ofMul
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      exact h (k + 1) (Nat.zero_lt_succ k)

theorem deningerBigWittFrobeniusTwo_zero_of_torsionFree [IsAddTorsionFree A] :
    deningerBigWittFrobeniusTwo (0 : DeningerBigWittRing A) = 0 := by
  apply deningerBigWittRing_ext_ghost
  intro k hk
  rw [deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree]
  simp

theorem deningerBigWittFrobeniusTwo_one_of_torsionFree [IsAddTorsionFree A] :
    deningerBigWittFrobeniusTwo (1 : DeningerBigWittRing A) = 1 := by
  apply deningerBigWittRing_ext_ghost
  intro k hk
  rw [deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree]
  simp

theorem deningerBigWittFrobeniusTwo_add_of_torsionFree [IsAddTorsionFree A]
    (x y : DeningerBigWittRing A) :
    deningerBigWittFrobeniusTwo (x + y) =
      deningerBigWittFrobeniusTwo x + deningerBigWittFrobeniusTwo y := by
  apply deningerBigWittRing_ext_ghost
  intro k hk
  let h2k : 0 < 2 * k := Nat.mul_pos (by decide) hk
  calc
    deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo (x + y)) =
      deningerBigWittGhostComponent (2 * k) h2k (x + y) :=
        deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree (x + y) k hk
    _ = deningerBigWittGhostComponent (2 * k) h2k x +
        deningerBigWittGhostComponent (2 * k) h2k y := map_add _ _ _
    _ = deningerBigWittGhostComponent k hk
          (deningerBigWittFrobeniusTwo x) +
        deningerBigWittGhostComponent k hk
          (deningerBigWittFrobeniusTwo y) := by
          rw [deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree,
            deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree]
    _ = deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo x +
          deningerBigWittFrobeniusTwo y) := (map_add _ _ _).symm

theorem deningerBigWittFrobeniusTwo_mul_of_torsionFree [IsAddTorsionFree A]
    (x y : DeningerBigWittRing A) :
    deningerBigWittFrobeniusTwo (x * y) =
      deningerBigWittFrobeniusTwo x * deningerBigWittFrobeniusTwo y := by
  apply deningerBigWittRing_ext_ghost
  intro k hk
  let h2k : 0 < 2 * k := Nat.mul_pos (by decide) hk
  calc
    deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo (x * y)) =
      deningerBigWittGhostComponent (2 * k) h2k (x * y) :=
        deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree (x * y) k hk
    _ = deningerBigWittGhostComponent (2 * k) h2k x *
        deningerBigWittGhostComponent (2 * k) h2k y := map_mul _ _ _
    _ = deningerBigWittGhostComponent k hk
          (deningerBigWittFrobeniusTwo x) *
        deningerBigWittGhostComponent k hk
          (deningerBigWittFrobeniusTwo y) := by
          rw [deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree,
            deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree]
    _ = deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo x *
          deningerBigWittFrobeniusTwo y) := (map_mul _ _ _).symm

theorem deningerBigWittFrobeniusTwo_zero :
    deningerBigWittFrobeniusTwo (0 : DeningerBigWittRing A) = 0 := by
  apply deningerBigWittRingSeries_injective
  apply PowerSeries.ext
  intro n
  simp [deningerBigWittFrobeniusTwoNormSeries]

theorem deningerBigWittFrobeniusTwo_one :
    deningerBigWittFrobeniusTwo (1 : DeningerBigWittRing A) = 1 := by
  simpa using deningerBigWittFrobeniusTwo_teichmuller (A := A) 1

theorem deningerBigWittUniversalRingEval_vector
    (d : ℕ) (v : Fin d → DeningerBigWittRing A) (i : Fin d) :
    deningerBigWittRingMap
        (deningerBigWittUniversalEval d
          (fun j => Additive.toMul (v j).additiveVal))
        ⟨Additive.ofMul (deningerBigWittUniversalVector d i)⟩ =
      v i := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul
      (deningerBigWittMap
        (deningerBigWittUniversalEval d
          (fun j => Additive.toMul (v j).additiveVal))
        (deningerBigWittUniversalVector d i)) =
    (v i).additiveVal
  exact congrArg Additive.ofMul
    (deningerBigWittUniversalEval_vector d
      (fun j => Additive.toMul (v j).additiveVal) i)

theorem deningerBigWittEulerGhost_natural
    {B : Type*} [CommRing B] (f : A →+* B)
    (x : ℕ → A) (k : ℕ) :
    f (deningerBigWittEulerGhost x k) =
      deningerBigWittEulerGhost (f ∘ x) k := by
  simp only [deningerBigWittEulerGhost, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : i + 1 ∣ k <;> simp [hd]

theorem deningerBigWittGhostComponent_natural
    {B : Type*} [CommRing B] (f : A →+* B)
    (k : ℕ) (hk : 0 < k) (w : DeningerBigWittRing A) :
    f (deningerBigWittGhostComponent k hk w) =
      deningerBigWittGhostComponent k hk (deningerBigWittRingMap f w) := by
  let x := (deningerBigWittEulerEquiv A).symm
    (Additive.toMul w.additiveVal)
  have hw : Additive.toMul w.additiveVal = deningerBigWittEulerEquiv A x :=
    (deningerBigWittEulerEquiv A).apply_symm_apply _ |>.symm
  change f (deningerBigWittGhostCoeff
      (Additive.toMul w.additiveVal) k) =
    deningerBigWittGhostCoeff
      (deningerBigWittMap f (Additive.toMul w.additiveVal)) k
  rw [hw, deningerBigWittGhostCoeff_euler x hk,
    deningerBigWittEulerEquiv_natural,
    deningerBigWittGhostCoeff_euler (f ∘ x) hk,
    deningerBigWittEulerGhost_natural]

theorem deningerBigWittFrobeniusTwo_add (x y : DeningerBigWittRing A) :
    deningerBigWittFrobeniusTwo (x + y) =
      deningerBigWittFrobeniusTwo x + deningerBigWittFrobeniusTwo y := by
  let v : Fin 2 → DeningerBigWittRing A := ![x, y]
  let ev := deningerBigWittUniversalEval 2
    (fun i => Additive.toMul (v i).additiveVal)
  let U : DeningerBigWittRing (DeningerBigWittUniversalRing 2) :=
    ⟨Additive.ofMul (deningerBigWittUniversalVector 2 (0 : Fin 2))⟩
  let V : DeningerBigWittRing (DeningerBigWittUniversalRing 2) :=
    ⟨Additive.ofMul (deningerBigWittUniversalVector 2 (1 : Fin 2))⟩
  have hU : deningerBigWittRingMap ev U = x := by
    simpa [U, ev, v] using
      (deningerBigWittUniversalRingEval_vector (A := A) 2 v (0 : Fin 2))
  have hV : deningerBigWittRingMap ev V = y := by
    simpa [V, ev, v] using
      (deningerBigWittUniversalRingEval_vector (A := A) 2 v (1 : Fin 2))
  have h := deningerBigWittFrobeniusTwo_add_of_torsionFree U V
  have hm := congrArg (deningerBigWittRingMap ev) h
  simp only [map_add, deningerBigWittFrobeniusTwo_natural] at hm
  rw [hU, hV] at hm
  exact hm

theorem deningerBigWittFrobeniusTwo_mul (x y : DeningerBigWittRing A) :
    deningerBigWittFrobeniusTwo (x * y) =
      deningerBigWittFrobeniusTwo x * deningerBigWittFrobeniusTwo y := by
  let v : Fin 2 → DeningerBigWittRing A := ![x, y]
  let ev := deningerBigWittUniversalEval 2
    (fun i => Additive.toMul (v i).additiveVal)
  let U : DeningerBigWittRing (DeningerBigWittUniversalRing 2) :=
    ⟨Additive.ofMul (deningerBigWittUniversalVector 2 (0 : Fin 2))⟩
  let V : DeningerBigWittRing (DeningerBigWittUniversalRing 2) :=
    ⟨Additive.ofMul (deningerBigWittUniversalVector 2 (1 : Fin 2))⟩
  have hU : deningerBigWittRingMap ev U = x := by
    simpa [U, ev, v] using
      (deningerBigWittUniversalRingEval_vector (A := A) 2 v (0 : Fin 2))
  have hV : deningerBigWittRingMap ev V = y := by
    simpa [V, ev, v] using
      (deningerBigWittUniversalRingEval_vector (A := A) 2 v (1 : Fin 2))
  have h := deningerBigWittFrobeniusTwo_mul_of_torsionFree U V
  have hm := congrArg (deningerBigWittRingMap ev) h
  simp only [map_mul, deningerBigWittFrobeniusTwo_natural] at hm
  rw [hU, hV] at hm
  exact hm

theorem deningerBigWittFrobeniusTwo_ghost_shift
    (w : DeningerBigWittRing A) (k : ℕ) (hk : 0 < k) :
    deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwo w) =
      deningerBigWittGhostComponent (2 * k)
        (Nat.mul_pos (by decide) hk) w := by
  let v : Fin 1 → DeningerBigWittRing A := fun _ => w
  let ev := deningerBigWittUniversalEval 1
    (fun i => Additive.toMul (v i).additiveVal)
  let U : DeningerBigWittRing (DeningerBigWittUniversalRing 1) :=
    ⟨Additive.ofMul (deningerBigWittUniversalVector 1 (0 : Fin 1))⟩
  have hU : deningerBigWittRingMap ev U = w := by
    simpa [U, ev, v] using
      (deningerBigWittUniversalRingEval_vector (A := A) 1 v (0 : Fin 1))
  have h := deningerBigWittFrobeniusTwo_ghost_shift_of_torsionFree U k hk
  have hm := congrArg ev h
  rw [deningerBigWittGhostComponent_natural,
    deningerBigWittGhostComponent_natural,
    deningerBigWittFrobeniusTwo_natural, hU] at hm
  exact hm

/-- Canonical Frobenius-two ring endomorphism on the big-Witt ring over an
arbitrary commutative ring. The target may contain additive torsion and
nilpotents. -/
noncomputable def deningerBigWittFrobeniusTwoRingHom :
    DeningerBigWittRing A →+* DeningerBigWittRing A where
  toFun := deningerBigWittFrobeniusTwo
  map_zero' := deningerBigWittFrobeniusTwo_zero
  map_add' := deningerBigWittFrobeniusTwo_add
  map_one' := deningerBigWittFrobeniusTwo_one
  map_mul' := deningerBigWittFrobeniusTwo_mul

/-- The bundled endomorphism retains the literal division-free norm
construction as its underlying function. -/
@[simp] theorem deningerBigWittFrobeniusTwoRingHom_apply
    (w : DeningerBigWittRing A) :
    deningerBigWittFrobeniusTwoRingHom w =
      deningerBigWittFrobeniusTwo w := rfl

/-- Full canonical ghost law over every commutative base ring. No ghost
injectivity hypothesis is present in the statement. -/
theorem deningerBigWittFrobeniusTwoRingHom_ghost
    (w : DeningerBigWittRing A) (k : ℕ) (hk : 0 < k) :
    deningerBigWittGhostComponent k hk
        (deningerBigWittFrobeniusTwoRingHom w) =
      deningerBigWittGhostComponent (2 * k)
        (Nat.mul_pos (by decide) hk) w :=
  deningerBigWittFrobeniusTwo_ghost_shift w k hk

/-- Frobenius two is a natural ring endomorphism of the arbitrary-ring
big-Witt functor. -/
theorem deningerBigWittFrobeniusTwoRingHom_natural
    {B : Type*} [CommRing B] (f : A →+* B) :
    (deningerBigWittRingMap f).comp deningerBigWittFrobeniusTwoRingHom =
      deningerBigWittFrobeniusTwoRingHom.comp (deningerBigWittRingMap f) := by
  apply RingHom.ext
  intro w
  exact deningerBigWittFrobeniusTwo_natural f w

/-- Bundled Frobenius squares every Teichmüller representative. -/
@[simp] theorem deningerBigWittFrobeniusTwoRingHom_teichmuller (a : A) :
    deningerBigWittFrobeniusTwoRingHom
        (deningerBigWittRingTeichmuller a) =
      deningerBigWittRingTeichmuller (a ^ 2) :=
  deningerBigWittFrobeniusTwo_teichmuller a

/-- Exact nilpotent survival law: a Frobenius-transgressed Teichmüller power
vanishes precisely when the corresponding even power vanishes in the base
ring. Thus arbitrary-ring descent does not silently reduce the target. -/
@[simp] theorem deningerBigWittFrobeniusTwo_teichmuller_pow_eq_zero_iff
    (a : A) (n : ℕ) :
    (deningerBigWittFrobeniusTwoRingHom
        (deningerBigWittRingTeichmuller a)) ^ n = 0 ↔
      a ^ (2 * n) = 0 := by
  rw [deningerBigWittFrobeniusTwoRingHom_teichmuller,
    deningerBigWittRingTeichmuller_pow_eq_zero_iff, ← pow_mul]

end

end RHTower
