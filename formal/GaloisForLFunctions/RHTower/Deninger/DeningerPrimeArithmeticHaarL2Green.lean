import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeArithmeticHaarL2Comparison

/-!
# Full Green form on literal arithmetic Haar-L² prime fibres

The local packet Haar-`L²` comparison extends coordinatewise to the all-prime Hilbert direct sum.
This identifies the existing packet Green form with a Green form whose `p`-coordinate is literally
normalized Haar-`L²` on

`Aut((AlgebraicClosure (ZMod p))ˣ) / closure(〈Frob_p〉)`.

Thus the full-block target no longer depends on treating the cyclotomic packet as a candidate
arithmetic fibre.  Local and global Green forms are preserved exactly, including every mean-zero
mode.
-/

namespace RHTower

open Filter Topology
open scoped ENNReal BigOperators

noncomputable section

/-- All-prime Hilbert sum of literal arithmetic quotient Haar-`L²` fibres. -/
abbrev DeningerPrimeArithmeticHaarHilbertSum : Type :=
  DeningerHilbertSum DeningerPrimeArithmeticHaarL2

private theorem deningerPrimePacketArithmeticHaarHilbertSumForward_memℓp
    (x : DeningerPrimePacketHaarHilbertSum) :
    Memℓp
      (fun p =>
        deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p (x p))
      2 := by
  apply Memℓp.of_norm
  have hx := (lp.memℓp x).norm
  simpa only [LinearIsometryEquiv.norm_map] using hx

/-- Coordinatewise packet-to-arithmetic Haar-`L²` comparison on the all-prime Hilbert sum. -/
def deningerPrimePacketArithmeticHaarHilbertSumForward :
    DeningerPrimePacketHaarHilbertSum →ₗᵢ[ℝ]
      DeningerPrimeArithmeticHaarHilbertSum where
  toLinearMap :=
    { toFun := fun x =>
        ⟨fun p =>
          deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p (x p),
          deningerPrimePacketArithmeticHaarHilbertSumForward_memℓp x⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext p
        simp
      map_smul' := by
        intro c x
        apply lp.ext
        funext p
        simp }
  norm_map' := by
    intro x
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 2
    funext p
    change
      ‖deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p (x p)‖ ^
          ENNReal.toReal 2 =
        ‖x p‖ ^ ENNReal.toReal 2
    rw [LinearIsometryEquiv.norm_map]

private theorem deningerPrimePacketArithmeticHaarHilbertSumBackward_memℓp
    (x : DeningerPrimeArithmeticHaarHilbertSum) :
    Memℓp
      (fun p =>
        (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p).symm (x p))
      2 := by
  apply Memℓp.of_norm
  have hx := (lp.memℓp x).norm
  simpa only [LinearIsometryEquiv.norm_map] using hx

theorem deningerPrimePacketArithmeticHaarHilbertSumForward_surjective :
    Function.Surjective deningerPrimePacketArithmeticHaarHilbertSumForward := by
  intro x
  refine ⟨⟨fun p =>
    (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p).symm (x p),
    deningerPrimePacketArithmeticHaarHilbertSumBackward_memℓp x⟩, ?_⟩
  apply lp.ext
  funext p
  exact LinearIsometryEquiv.apply_symm_apply
    (deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p) (x p)

/-- **All-prime arithmetic Haar-L² comparison.**  The packet and literal arithmetic Hilbert sums
are canonically linearly isometric, coordinate by coordinate. -/
noncomputable def
    deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv :
    DeningerPrimePacketHaarHilbertSum ≃ₗᵢ[ℝ]
      DeningerPrimeArithmeticHaarHilbertSum :=
  LinearIsometryEquiv.ofSurjective
    deningerPrimePacketArithmeticHaarHilbertSumForward
    deningerPrimePacketArithmeticHaarHilbertSumForward_surjective

@[simp] theorem
    deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv_apply
    (x : DeningerPrimePacketHaarHilbertSum) (p : Nat.Primes) :
    deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x p =
      deningerPrimePacketArithmeticHaarL2LinearIsometryEquiv p (x p) := rfl

/-- Local Green form on the literal arithmetic Haar-`L²` fibre at `p`. -/
def deningerPrimeArithmeticHaarLocalGreenForm (p : Nat.Primes) :
    DeningerPrimeArithmeticHaarHilbertSum →L[ℝ]
      DeningerPrimeArithmeticHaarHilbertSum →L[ℝ] ℝ :=
  deningerPrimeBlockGreenForm (Kp := DeningerPrimeArithmeticHaarL2) p

@[simp] theorem deningerPrimeArithmeticHaarLocalGreenForm_apply_apply
    (p : Nat.Primes)
    (x y : DeningerPrimeArithmeticHaarHilbertSum) :
    deningerPrimeArithmeticHaarLocalGreenForm p x y =
      deningerPrimeGraphGreenCoefficient p * inner ℝ (x p) (y p) := by
  exact deningerBlockCoordinateGreenForm_apply_apply _ _ _ _ _

/-- Literal arithmetic local Green forms sum unconditionally in operator norm. -/
theorem summable_deningerPrimeArithmeticHaarLocalGreenForm :
    Summable deningerPrimeArithmeticHaarLocalGreenForm :=
  summable_deningerPrimeBlockGreenForm
    (Kp := DeningerPrimeArithmeticHaarL2)

/-- Global Green form on the all-prime literal arithmetic Haar-`L²` sum. -/
def deningerPrimeArithmeticHaarSummedGreenForm :
    DeningerPrimeArithmeticHaarHilbertSum →L[ℝ]
      DeningerPrimeArithmeticHaarHilbertSum →L[ℝ] ℝ :=
  ∑' p, deningerPrimeArithmeticHaarLocalGreenForm p

theorem deningerPrimeArithmeticHaarSummedGreenForm_self
    (x : DeningerPrimeArithmeticHaarHilbertSum) :
    deningerPrimeArithmeticHaarSummedGreenForm x x =
      ∑' p : Nat.Primes,
        deningerPrimeGraphGreenCoefficient p * ‖x p‖ ^ 2 :=
  deningerPrimeBlockSummedGreenForm_self
    (Kp := DeningerPrimeArithmeticHaarL2) x

theorem deningerPrimeArithmeticHaarSummedGreenForm_nonneg
    (x : DeningerPrimeArithmeticHaarHilbertSum) :
    0 ≤ deningerPrimeArithmeticHaarSummedGreenForm x x :=
  deningerPrimeBlockSummedGreenForm_nonneg
    (Kp := DeningerPrimeArithmeticHaarL2) x

/-- No nonzero literal arithmetic Haar-`L²` mode lies in the global Green radical. -/
theorem deningerPrimeArithmeticHaarSummedGreenForm_self_eq_zero_iff
    (x : DeningerPrimeArithmeticHaarHilbertSum) :
    deningerPrimeArithmeticHaarSummedGreenForm x x = 0 ↔ x = 0 :=
  deningerPrimeBlockSummedGreenForm_self_eq_zero_iff
    (Kp := DeningerPrimeArithmeticHaarL2) x

/-- The all-prime Hilbert comparison preserves each local Green form exactly. -/
theorem deningerPrimePacketArithmeticHaarLocalGreenForm_transport
    (p : Nat.Primes)
    (x y : DeningerPrimePacketHaarHilbertSum) :
    deningerPrimeArithmeticHaarLocalGreenForm p
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x)
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv y) =
      deningerPrimePacketHaarLocalGreenForm p x y := by
  rw [deningerPrimeArithmeticHaarLocalGreenForm_apply_apply,
    deningerPrimePacketHaarLocalGreenForm_apply_apply,
    deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv_apply,
    deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv_apply,
    LinearIsometryEquiv.inner_map_map]

/-- **Green target identification.**  The full packet Green form equals the full literal
arithmetic Green form under the canonical all-prime Haar-`L²` isometry. -/
theorem deningerPrimePacketArithmeticHaarSummedGreenForm_transport
    (x y : DeningerPrimePacketHaarHilbertSum) :
    deningerPrimeArithmeticHaarSummedGreenForm
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x)
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv y) =
      deningerPrimePacketHaarSummedGreenForm x y := by
  have hArithmetic :=
    summable_deningerPrimeArithmeticHaarLocalGreenForm.hasSum
  have hArithmeticX := hArithmetic.mapL
    ((ContinuousLinearMap.apply ℝ
      (DeningerPrimeArithmeticHaarHilbertSum →L[ℝ] ℝ))
      (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x))
  have hArithmeticXY := hArithmeticX.mapL
    ((ContinuousLinearMap.apply ℝ ℝ)
      (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv y))
  have hPacket :=
    summable_deningerPrimePacketHaarLocalGreenForm.hasSum
  have hPacketX := hPacket.mapL
    ((ContinuousLinearMap.apply ℝ
      (DeningerPrimePacketHaarHilbertSum →L[ℝ] ℝ)) x)
  have hPacketXY := hPacketX.mapL
    ((ContinuousLinearMap.apply ℝ ℝ) y)
  calc
    deningerPrimeArithmeticHaarSummedGreenForm
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x)
        (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv y) =
        ∑' p, deningerPrimeArithmeticHaarLocalGreenForm p
          (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv x)
          (deningerPrimePacketArithmeticHaarHilbertSumLinearIsometryEquiv y) := by
      exact hArithmeticXY.tsum_eq.symm
    _ = ∑' p, deningerPrimePacketHaarLocalGreenForm p x y := by
      apply tsum_congr
      intro p
      exact deningerPrimePacketArithmeticHaarLocalGreenForm_transport p x y
    _ = deningerPrimePacketHaarSummedGreenForm x y :=
      hPacketXY.tsum_eq

end

end RHTower
