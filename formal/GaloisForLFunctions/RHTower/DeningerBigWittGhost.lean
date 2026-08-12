import GaloisForLFunctions.RHTower.DeningerBigWittMultiplication
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Logarithmic ghost map for the literal big-Witt carrier

The ghost series is `-T f'(T)/f(T)`.  Division here is only by the power-series unit `f`, never by
an integer.  Thus additivity is valid over arbitrary rings.  Injectivity is used only over the
universal torsion-free source ring before descent to arbitrary targets.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A : Type*} [CommRing A]

/-- Logarithmic ghost series of a constant-one formal power series. -/
def deningerBigWittLogGhost (f : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1) : PowerSeries A :=
  -(PowerSeries.X * PowerSeries.derivative A f * PowerSeries.invOfUnit f 1)

@[simp] theorem deningerBigWittLogGhost_constantCoeff
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.constantCoeff (deningerBigWittLogGhost f hf) = 0 := by
  simp [deningerBigWittLogGhost]

theorem deningerBigWittLogGhost_mul_self
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    deningerBigWittLogGhost f hf * f =
      -(PowerSeries.X * PowerSeries.derivative A f) := by
  rw [deningerBigWittLogGhost, neg_mul, mul_assoc,
    PowerSeries.invOfUnit_mul f 1 hf]
  simp

/-- The logarithmic ghost transforms ordinary multiplication into addition over every
commutative ring. -/
theorem deningerBigWittLogGhost_mul
    (f g : PowerSeries A)
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    deningerBigWittLogGhost (f * g) (by simp [hf, hg]) =
      deningerBigWittLogGhost f hf + deningerBigWittLogGhost g hg := by
  have hfg : IsUnit (f * g) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hf, hg])
  apply hfg.mul_right_cancel
  rw [deningerBigWittLogGhost_mul_self]
  rw [add_mul]
  rw [← mul_assoc (deningerBigWittLogGhost f hf) f g,
    deningerBigWittLogGhost_mul_self f hf]
  have hgterm : deningerBigWittLogGhost g hg * (f * g) =
      f * (-(PowerSeries.X * PowerSeries.derivative A g)) := by
    calc
      deningerBigWittLogGhost g hg * (f * g) =
          f * (deningerBigWittLogGhost g hg * g) := by ring
      _ = f * (-(PowerSeries.X * PowerSeries.derivative A g)) := by
          rw [deningerBigWittLogGhost_mul_self g hg]
  rw [hgterm]
  change -(PowerSeries.X * PowerSeries.derivativeFun (f * g)) = _
  rw [PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  change -(PowerSeries.X * (f * PowerSeries.derivative A g +
    g * PowerSeries.derivative A f)) = _
  ring

/-- Ghost series on the literal big-Witt carrier. -/
def deningerBigWittGhostSeries (w : DeningerBigWittAdditive A) : PowerSeries A :=
  deningerBigWittLogGhost (deningerBigWittSeries w)
    (deningerBigWittSeries_constantCoeff w)

@[simp] theorem deningerBigWittGhostSeries_one :
    deningerBigWittGhostSeries (1 : DeningerBigWittAdditive A) = 0 := by
  simp [deningerBigWittGhostSeries, deningerBigWittLogGhost, deningerBigWittSeries]

@[simp] theorem deningerBigWittGhostSeries_mul
    (u v : DeningerBigWittAdditive A) :
    deningerBigWittGhostSeries (u * v) =
      deningerBigWittGhostSeries u + deningerBigWittGhostSeries v := by
  exact deningerBigWittLogGhost_mul _ _ _ _

theorem deningerBigWittLogGhost_eq_iff
    [IsAddTorsionFree A]
    {f g : PowerSeries A}
    (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    deningerBigWittLogGhost f hf = deningerBigWittLogGhost g hg ↔ f = g := by
  constructor
  · intro h
    let fi : PowerSeries A := PowerSeries.invOfUnit f 1
    let gi : PowerSeries A := PowerSeries.invOfUnit g 1
    have hfi : f * fi = 1 := PowerSeries.mul_invOfUnit f 1 hf
    have hif : fi * f = 1 := PowerSeries.invOfUnit_mul f 1 hf
    have hgi : g * gi = 1 := PowerSeries.mul_invOfUnit g 1 hg
    have hlog : PowerSeries.derivative A f * fi =
        PowerSeries.derivative A g * gi := by
      have hx : -(PowerSeries.X * (PowerSeries.derivative A f * fi)) =
          -(PowerSeries.X * (PowerSeries.derivative A g * gi)) := by
        simpa only [deningerBigWittLogGhost, fi, gi, mul_assoc] using h
      have hx' : PowerSeries.X * (PowerSeries.derivative A f * fi) =
          PowerSeries.X * (PowerSeries.derivative A g * gi) := neg_injective hx
      exact PowerSeries.X_pow_mul_injective (k := 1) (by simpa using hx')
    have hD : PowerSeries.derivative A (f * gi) = 0 := by
      change PowerSeries.derivativeFun (f * gi) = 0
      rw [PowerSeries.derivativeFun_mul]
      simp only [smul_eq_mul]
      have hginv : PowerSeries.derivative A gi =
          -(gi ^ 2) * PowerSeries.derivative A g := by
        have hu : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.mpr (hg ▸ isUnit_one)
        have hunit : hu.unit = (⟨g, gi, PowerSeries.mul_invOfUnit g 1 hg,
            PowerSeries.invOfUnit_mul g 1 hg⟩ : (PowerSeries A)ˣ) := by
          apply Units.ext
          rfl
        have hd := PowerSeries.derivative_inv hu.unit
        rw [hunit] at hd
        exact hd
      change f * PowerSeries.derivative A gi + gi * PowerSeries.derivative A f = 0
      rw [hginv]
      have hlog' : PowerSeries.derivative A f =
          PowerSeries.derivative A g * gi * f := by
        calc
          PowerSeries.derivative A f =
              (PowerSeries.derivative A f * fi) * f := by rw [mul_assoc, hif, mul_one]
          _ = PowerSeries.derivative A g * gi * f := by rw [hlog]
      rw [hlog']
      rw [pow_two]
      ring
    have hc : PowerSeries.constantCoeff (f * gi) =
        PowerSeries.constantCoeff (1 : PowerSeries A) := by
      simp [fi, gi, hf, hg]
    have hD' : PowerSeries.derivative A (f * gi) =
        PowerSeries.derivative A (1 : PowerSeries A) := by simpa using hD
    have hquot : f * gi = 1 := PowerSeries.derivative.ext hD' hc
    calc
      f = (f * gi) * g := by rw [mul_assoc, PowerSeries.invOfUnit_mul g 1 hg, mul_one]
      _ = g := by rw [hquot, one_mul]
  · exact fun h => h ▸ rfl

/-- Ghost injectivity over additively torsion-free rings. -/
theorem deningerBigWittGhostSeries_injective [IsAddTorsionFree A] :
    Function.Injective (deningerBigWittGhostSeries (A := A)) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact (deningerBigWittLogGhost_eq_iff
    (deningerBigWittSeries_constantCoeff u)
    (deningerBigWittSeries_constantCoeff v)).mp huv

end

end RHTower
