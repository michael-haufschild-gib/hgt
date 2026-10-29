import GaloisForLFunctions.HeckeKreinToeplitz.TheHeckeOrbitKernelOfAZeroConfiguration
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit

/-!
# The finite-index stratum of `ζ` is Lindelöf-deep

The Weil kernel of `ζ` on the Hecke lattice: the Hecke orbit kernel `K_ζ(u) = W(B, B(· − log u))` of
the cubic spline `B`, whose transform `(sin z/z)⁴` vanishes only on the real axis, so that `B` sees
every zero off the line (`zetaKernel`).

* **Index = right zeros** (`negIndex_zetaKernel`): `κ(K_ζ) = #{ρ : Re ρ > ½}`, already on the
  sublattice of any two primes (`negIndex_zetaKernel_twoPrime`).
* **RH** (`riemannHypothesis_tfae_zetaKernel`): RH ⇔ `K_ζ` is positive definite ⇔ `κ(K_ζ) = 0` ⇔
  `κ(K_ζ) ≤ 1` ⇔ the restriction to `⟨p, q⟩` is positive definite. The index is even: right zeros
  come in conjugate pairs.
* **The finite stratum** (`zetaKernel_finiteIndex_tfae`): `κ(K_ζ) < ∞` ⇔ finite index on two prime
  towers ⇔ finitely many off-line zeros ⇔ bounded heat counts `N(t)` ⇔ all zeros above some height on
  the line. This is the Krein–Langer class of the Weil kernel, seen from four sides.
* **Lindelöf law** (`lindelof_of_negIndex_zetaKernel_lt_top`): a Weil kernel of finite index forces
  the zeros to approach the line, hence the Lindelöf hypothesis and a zero-free half-plane
  `Re s > ½ + α`, `α < ½`. Every finite-index theorem for `ζ` proves LH; an argument that bounds the
  index without Lindelöf-strength input cannot be correct.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros sectorZeros
  zeta_rightZeros_encard_eq_two_mul_sectorZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros_cubicSpline
  riemannHypothesis_iff_no_rightZero index_exit_first_rung_tfae rightZeros_zeta_finite_iff_finiteOffLine)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- The Weil kernel of `ζ` on `ℚ_{>0}`: the Hecke orbit kernel of the cubic spline. -/
def zetaKernel : HeckeLattice → ℂ := orbitKernel zetaZeroConfig cubicSpline

theorem cubicSpline_mem_realTests : cubicSpline ∈ ArithmeticCastelnuovoSeveri.realTests :=
  ⟨contDiff_cubicSpline, hasCompactSupport_cubicSpline⟩

theorem isHermKernel_zetaKernel : IsHermKernel zetaKernel :=
  isHermKernel_orbitKernel _ _

/-- **The index of the Weil kernel of `ζ` is the number of zeros right of the line.** -/
theorem negIndex_zetaKernel : negIndex zetaKernel = (rightZeros zetaZeroConfig).encard := by
  rw [zetaKernel, negIndex_orbitKernel _ temperedConfig_zetaZeroConfig cubicSpline_mem_realTests,
    seenRightZeros_cubicSpline]
  rfl

/-- **Two primes carry the whole index of `ζ`.** -/
theorem negIndex_zetaKernel_twoPrime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    negIndex (zetaKernel ∘ (twoPrimeLattice hp hq).subtype) = (rightZeros zetaZeroConfig).encard := by
  rw [zetaKernel, negIndex_orbitKernel_twoPrime _ temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests hp hq hpq, seenRightZeros_cubicSpline]
  rfl

/-- The index of the Weil kernel of `ζ` is even: right zeros come in conjugate pairs. -/
theorem negIndex_zetaKernel_eq_two_mul :
    negIndex zetaKernel = 2 * (sectorZeros zetaZeroConfig 1).encard := by
  rw [negIndex_zetaKernel, zeta_rightZeros_encard_eq_two_mul_sectorZeros 1]

theorem riemannHypothesis_iff_negIndex_zetaKernel_eq_zero :
    RiemannHypothesis ↔ negIndex zetaKernel = 0 := by
  rw [riemannHypothesis_iff_no_rightZero, negIndex_zetaKernel, Set.encard_eq_zero]
  rfl

/-- **One negative square is never enough**: the index of `K_ζ` is `0` or at least `2`. -/
theorem negIndex_zetaKernel_le_one_iff : negIndex zetaKernel ≤ 1 ↔ negIndex zetaKernel = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ zero_le_one⟩
  rw [negIndex_zetaKernel_eq_two_mul] at h ⊢
  by_contra hne
  have hk : (sectorZeros zetaZeroConfig 1).encard ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  have h1 : (1 : ℕ∞) ≤ (sectorZeros zetaZeroConfig 1).encard := Order.one_le_iff_ne_zero.mpr hk
  have : (2 : ℕ∞) ≤ 1 := (by calc (2 : ℕ∞) = 2 * 1 := by norm_num
    _ ≤ 2 * (sectorZeros zetaZeroConfig 1).encard := by gcongr
    _ ≤ 1 := h)
  exact absurd this (by norm_num)

/-- **RH as positivity of one kernel.** -/
theorem riemannHypothesis_tfae_zetaKernel {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    [RiemannHypothesis,
      IsPosDefKernel zetaKernel,
      negIndex zetaKernel = 0,
      negIndex zetaKernel ≤ 1,
      IsPosDefKernel (zetaKernel ∘ (twoPrimeLattice hp hq).subtype)].TFAE := by
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_negIndex_zetaKernel_eq_zero
  tfae_have 2 ↔ 3 := isPosDefKernel_iff isHermKernel_zetaKernel
  tfae_have 3 ↔ 4 := negIndex_zetaKernel_le_one_iff.symm
  tfae_have 5 ↔ 3 := by
    rw [isPosDefKernel_iff (isHermKernel_zetaKernel.comp _), negIndex_zetaKernel_twoPrime hp hq hpq,
      negIndex_zetaKernel]
  tfae_finish

/-- **The finite-index stratum of `ζ`.** Finite index of the Weil kernel, on `ℚ_{>0}` or on two
prime towers, is finitely many off-line zeros, bounded heat counts, and the critical line above
some height. -/
theorem zetaKernel_finiteIndex_tfae {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    [negIndex zetaKernel < ⊤,
      negIndex (zetaKernel ∘ (twoPrimeLattice hp hq).subtype) < ⊤,
      FiniteOffLine,
      ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M,
      ∃ T₀ : ℝ, ∀ ρ ∈ zetaZeroConfig.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2].TFAE := by
  have hex := index_exit_first_rung_tfae
  tfae_have 1 ↔ 3 := by
    rw [negIndex_zetaKernel, Set.encard_lt_top_iff]; exact rightZeros_zeta_finite_iff_finiteOffLine
  tfae_have 2 ↔ 1 := by rw [negIndex_zetaKernel_twoPrime hp hq hpq, negIndex_zetaKernel]
  tfae_have 3 ↔ 4 := hex.out 1 2
  tfae_have 3 ↔ 5 := hex.out 1 4
  tfae_finish

/-- **The Lindelöf law.** A Weil kernel of finite index forces the Lindelöf hypothesis. -/
theorem lindelof_of_negIndex_zetaKernel_lt_top (h : negIndex zetaKernel < ⊤) :
    LindelofCriticalLine := by
  have hF : FiniteOffLine := by
    rw [negIndex_zetaKernel, Set.encard_lt_top_iff] at h
    exact rightZeros_zeta_finite_iff_finiteOffLine.mp h
  exact lindelofCriticalLine_of_zerosApproachLine (zerosApproachLine_of_finiteOffLine hF)

/-- A Weil kernel of finite index forces a zero-free half-plane `Re s > ½ + α`, `α < ½`. -/
theorem quasiRH_of_negIndex_zetaKernel_lt_top (h : negIndex zetaKernel < ⊤) :
    ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α := by
  have hF : FiniteOffLine := by
    rw [negIndex_zetaKernel, Set.encard_lt_top_iff] at h
    exact rightZeros_zeta_finite_iff_finiteOffLine.mp h
  exact quasiRH_of_zerosApproachLine (zerosApproachLine_of_finiteOffLine hF)

end GaloisForLFunctions.HeckeKreinToeplitz
