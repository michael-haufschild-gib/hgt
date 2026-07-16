import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayAnisotropicPhase
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPairCurrent
import Mathlib.Data.PNat.Prime

/-!
# Exact arithmetic partition into complete primitive theta rays

Every positive square-index pair has a unique decomposition into a coprime positive direction and
a positive common scale.  This file packages that decomposition as an actual equivalence and
therefore obtains an unconditional `tsum` reindexing theorem.  It is the arithmetic half of the
global primitive-ray disintegration; no sign, summability, change of variables, or RH-bearing
current estimate is assumed.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- A positive coprime direction in the square-index lattice. -/
def ThetaCuspPrimitiveDirection :=
  {p : ℕ+ × ℕ+ // PNat.Coprime p.1 p.2}

/-- A coprime positive direction together with its positive common scale. -/
abbrev ThetaCuspPrimitiveRayIndex := ThetaCuspPrimitiveDirection × ℕ+

/-- Reassemble a primitive direction and common scale into its positive lattice pair. -/
def thetaCuspPrimitiveRayIndexToPositivePair
    (q : ThetaCuspPrimitiveRayIndex) : ℕ+ × ℕ+ :=
  (q.1.1.1 * q.2, q.1.1.2 * q.2)

private theorem thetaCuspPNat_divExact_gcd_coprime (m n : ℕ+) :
    PNat.Coprime (PNat.divExact m (PNat.gcd m n))
      (PNat.divExact n (PNat.gcd m n)) := by
  let g : ℕ+ := PNat.gcd m n
  let a : ℕ+ := PNat.divExact m g
  let b : ℕ+ := PNat.divExact n g
  have hga : g * a = m := by
    exact PNat.mul_div_exact (PNat.gcd_dvd_left m n)
  have hgb : g * b = n := by
    exact PNat.mul_div_exact (PNat.gcd_dvd_right m n)
  have hnat : Nat.gcd (a : ℕ) (b : ℕ) = 1 := by
    apply Nat.mul_left_cancel g.pos
    calc
      (g : ℕ) * Nat.gcd (a : ℕ) (b : ℕ) =
          Nat.gcd ((g : ℕ) * (a : ℕ)) ((g : ℕ) * (b : ℕ)) := by
            rw [Nat.gcd_mul_left]
      _ = Nat.gcd (m : ℕ) (n : ℕ) := by
        rw [show (g : ℕ) * (a : ℕ) = (m : ℕ) by exact_mod_cast hga,
          show (g : ℕ) * (b : ℕ) = (n : ℕ) by exact_mod_cast hgb]
      _ = (g : ℕ) := rfl
      _ = (g : ℕ) * 1 := by ring
  exact PNat.coprime_coe.mp hnat

/-- Extract the gcd scale and the two coprime quotients from a positive lattice pair. -/
def thetaCuspPositivePairToPrimitiveRayIndex
    (p : ℕ+ × ℕ+) : ThetaCuspPrimitiveRayIndex :=
  let g := PNat.gcd p.1 p.2
  let a := PNat.divExact p.1 g
  let b := PNat.divExact p.2 g
  (⟨(a, b), thetaCuspPNat_divExact_gcd_coprime p.1 p.2⟩, g)

private theorem thetaCuspPNat_gcd_mul_of_coprime
    {a b g : ℕ+} (hab : PNat.Coprime a b) :
    PNat.gcd (a * g) (b * g) = g := by
  apply PNat.eq
  rw [PNat.gcd_coe]
  push_cast
  rw [Nat.gcd_mul_right]
  have hnat : Nat.Coprime (a : ℕ) (b : ℕ) := PNat.coprime_coe.mpr hab
  rw [hnat.gcd_eq_one, one_mul]

private theorem thetaCuspPNat_divExact_mul_right
    (a g : ℕ+) : PNat.divExact (a * g) g = a := by
  apply mul_left_cancel (a := g)
  rw [PNat.mul_div_exact]
  · exact mul_comm a g
  · exact dvd_mul_left g a

theorem thetaCuspPrimitiveRayIndexToPositivePair_leftInverse :
    Function.LeftInverse thetaCuspPositivePairToPrimitiveRayIndex
      thetaCuspPrimitiveRayIndexToPositivePair := by
  rintro ⟨⟨⟨a, b⟩, hab⟩, g⟩
  dsimp only [thetaCuspPositivePairToPrimitiveRayIndex,
    thetaCuspPrimitiveRayIndexToPositivePair]
  have hgcd : PNat.gcd (a * g) (b * g) = g :=
    thetaCuspPNat_gcd_mul_of_coprime hab
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · change PNat.divExact (a * g) (PNat.gcd (a * g) (b * g)) = a
      rw [hgcd]
      exact thetaCuspPNat_divExact_mul_right a g
    · change PNat.divExact (b * g) (PNat.gcd (a * g) (b * g)) = b
      rw [hgcd]
      exact thetaCuspPNat_divExact_mul_right b g
  · exact hgcd

theorem thetaCuspPrimitiveRayIndexToPositivePair_rightInverse :
    Function.RightInverse thetaCuspPositivePairToPrimitiveRayIndex
      thetaCuspPrimitiveRayIndexToPositivePair := by
  rintro ⟨m, n⟩
  apply Prod.ext
  · exact (mul_comm _ _).trans
      (PNat.mul_div_exact (PNat.gcd_dvd_left m n))
  · exact (mul_comm _ _).trans
      (PNat.mul_div_exact (PNat.gcd_dvd_right m n))

/-- **Unique complete-ray partition of the positive lattice.** -/
def thetaCuspPrimitiveRayIndexEquivPositivePair :
    ThetaCuspPrimitiveRayIndex ≃ (ℕ+ × ℕ+) where
  toFun := thetaCuspPrimitiveRayIndexToPositivePair
  invFun := thetaCuspPositivePairToPrimitiveRayIndex
  left_inv := thetaCuspPrimitiveRayIndexToPositivePair_leftInverse
  right_inv := thetaCuspPrimitiveRayIndexToPositivePair_rightInverse

/-- **Unconditional primitive-ray regrouping.**  Any topological additive infinite sum over
positive square-index pairs can be reindexed exactly by coprime direction and common scale.  The
statement uses only the arithmetic equivalence, so it does not smuggle in convergence or a sign. -/
theorem tsum_thetaCuspPositivePair_eq_primitiveRay
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : ℕ+ × ℕ+ → E) :
    (∑' p : ℕ+ × ℕ+, f p) =
      ∑' q : ThetaCuspPrimitiveRayIndex,
        f (thetaCuspPrimitiveRayIndexToPositivePair q) := by
  symm
  exact Equiv.tsum_eq thetaCuspPrimitiveRayIndexEquivPositivePair f

/-- **The full canonical density product partitioned into complete arithmetic rays.**  This is the
actual square-index density, not an abstract summand family: pointwise, its ordered atom-pair sum
is exactly the sum over coprime direction and positive common scale. -/
theorem thetaCuspTailSecondDensity_mul_eq_tsum_primitiveRay
    (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y =
      ∑' q : ThetaCuspPrimitiveRayIndex,
        thetaCuspTailSecondDensityAtom
            (thetaCuspPrimitiveRayIndexToPositivePair q).1 x *
          thetaCuspTailSecondDensityAtom
            (thetaCuspPrimitiveRayIndexToPositivePair q).2 y := by
  rw [thetaCuspTailSecondDensity_mul_eq_tsum_atomPair]
  let e : (ℕ+ × ℕ+) ≃ (ℕ × ℕ) :=
    Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat
  let f : ℕ × ℕ → ℝ := fun q =>
    thetaCuspTailSecondDensityAtom (q.1 + 1) x *
      thetaCuspTailSecondDensityAtom (q.2 + 1) y
  have hreindex :
      (∑' q : ℕ × ℕ, f q) =
        ∑' p : ℕ+ × ℕ+,
          thetaCuspTailSecondDensityAtom p.1 x *
            thetaCuspTailSecondDensityAtom p.2 y := by
    symm
    calc
      (∑' p : ℕ+ × ℕ+,
          thetaCuspTailSecondDensityAtom p.1 x *
            thetaCuspTailSecondDensityAtom p.2 y) =
          ∑' p : ℕ+ × ℕ+, f (e p) := by
            apply tsum_congr
            intro p
            change thetaCuspTailSecondDensityAtom (p.1 : ℕ) x *
                thetaCuspTailSecondDensityAtom (p.2 : ℕ) y =
              thetaCuspTailSecondDensityAtom (PNat.natPred p.1 + 1) x *
                thetaCuspTailSecondDensityAtom (PNat.natPred p.2 + 1) y
            rw [PNat.natPred_add_one, PNat.natPred_add_one]
      _ = ∑' q : ℕ × ℕ, f q := Equiv.tsum_eq e f
  change (∑' q : ℕ × ℕ, f q) = _
  rw [hreindex]
  exact tsum_thetaCuspPositivePair_eq_primitiveRay
    (fun p : ℕ+ × ℕ+ =>
      thetaCuspTailSecondDensityAtom p.1 x *
        thetaCuspTailSecondDensityAtom p.2 y)

end

end RHTower
