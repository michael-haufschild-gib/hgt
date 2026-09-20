import GaloisForLFunctions.RHTower.DeningerCriticalFloquetVonMangoldtWall
import GaloisForLFunctions.RHTower.PhotonicParabolicReturn

/-!
# Prime monodromy first jet as the PTR parabolic transfer

## PTR proof-chain position

The PTR receiver already proves that a specified parabolic transfer has the
zeta return response.  The missing source step is to derive that transfer from
a physical Maxwell/time-crystal system.  This module isolates an unconditional
arithmetic source invariant which any such realization can target: the
source-normal first jet of the literal Deninger relative prime monodromy.

For a prime `p`, the monodromy `u ↦ p⁻ᵘ` has value one and first derivative
`-log p` at the source normal `u = 0`.  Scaling by that nonzero derivative and
swapping the two jet channels is exactly `photonicParabolic`.  Thus this is not
an assumed transfer matrix and not a Maxwell derivation; it reduces the
remaining physical task to realizing a literal, normalized arithmetic jet and
then proving the separate defect-confinement law.
-/

open Complex Matrix
open scoped Matrix

namespace RHTower

/-- Value/first-derivative jet of the literal relative prime monodromy at its source normal. -/
noncomputable def deningerFloquetRelativeMonodromyFirstJet (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![iteratedDeriv 0 (deningerFloquetRelativeMonodromyComplex p) 0, 0;
    iteratedDeriv 1 (deningerFloquetRelativeMonodromyComplex p) 0,
      iteratedDeriv 0 (deningerFloquetRelativeMonodromyComplex p) 0]

/-- Canonical diagonal normalization by the nonzero prime-log first jet. -/
noncomputable def deningerFloquetJetNormalization (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -(Real.log ((p : ℕ) : ℝ) : ℂ)]

/-- Explicit inverse channel scaling for `deningerFloquetJetNormalization`. -/
noncomputable def deningerFloquetJetNormalizationInv (p : Nat.Primes) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -((Real.log ((p : ℕ) : ℝ) : ℂ)⁻¹)]

/-- Exchange of value and normalized derivative jet channels. -/
def deningerFloquetJetSwap : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The literal relative prime monodromy has the expected source-normal first jet. -/
theorem deningerFloquetRelativeMonodromyFirstJet_eq (p : Nat.Primes) :
    deningerFloquetRelativeMonodromyFirstJet p =
      !![1, 0; -(Real.log ((p : ℕ) : ℝ) : ℂ), 1] := by
  rw [deningerFloquetRelativeMonodromyFirstJet,
    iteratedDeriv_deningerFloquetRelativeMonodromyComplex_zero p 0,
    iteratedDeriv_deningerFloquetRelativeMonodromyComplex_zero p 1]
  simp

/--
The canonical normalized source-normal first jet is exactly the PTR parabolic
transfer.  This supplies an arithmetic target for a future physical
Maxwell/time-crystal realization, without claiming that realization here.
-/
theorem deningerFloquetRelativeMonodromyFirstJet_normalized_eq_photonicParabolic
    (p : Nat.Primes) :
    deningerFloquetJetSwap * deningerFloquetJetNormalizationInv p *
        deningerFloquetRelativeMonodromyFirstJet p *
          deningerFloquetJetNormalization p * deningerFloquetJetSwap =
      photonicParabolic := by
  rw [deningerFloquetRelativeMonodromyFirstJet_eq]
  have hlog : (Real.log ((p : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.log_pos p.property).ne'
  simp only [deningerFloquetJetSwap, deningerFloquetJetNormalizationInv,
    deningerFloquetJetNormalization, photonicParabolic, photonicUpper,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> field_simp [hlog] <;> ring

/-- The source-normal first jet retains the prime label exactly. -/
theorem deningerFloquetRelativeMonodromyFirstJet_injective :
    Function.Injective deningerFloquetRelativeMonodromyFirstJet := by
  intro p q hpq
  rw [deningerFloquetRelativeMonodromyFirstJet_eq p,
    deningerFloquetRelativeMonodromyFirstJet_eq q] at hpq
  have hentry := congrFun (congrFun hpq (1 : Fin 2)) (0 : Fin 2)
  change -(Real.log ((p : ℕ) : ℝ) : ℂ) =
    -(Real.log ((q : ℕ) : ℝ) : ℂ) at hentry
  have hlogC : (Real.log ((p : ℕ) : ℝ) : ℂ) =
      (Real.log ((q : ℕ) : ℝ) : ℂ) := neg_inj.mp hentry
  have hlogR : Real.log ((p : ℕ) : ℝ) = Real.log ((q : ℕ) : ℝ) := by
    exact_mod_cast hlogC
  apply Subtype.ext
  have hpPos : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
  have hqPos : 0 < ((q : ℕ) : ℝ) := by exact_mod_cast q.property.pos
  have hpqR : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by
    rw [← Real.exp_log hpPos, hlogR, Real.exp_log hqPos]
  exact_mod_cast hpqR

/--
Distinct prime jets cannot share one invertible right frame and one parabolic
transfer. Thus an all-prime PTR source must retain prime-dependent frame or
coupling data; a uniform-frame source class is closed.
-/
theorem not_exists_deningerFloquetRelativeMonodromyFirstJet_common_parabolic_frame
    {p q : Nat.Primes} (hpq : p ≠ q) :
    ¬ ∃ C B : Matrix (Fin 2) (Fin 2) ℂ,
      C * B = 1 ∧
      deningerFloquetRelativeMonodromyFirstJet p * C = C * photonicParabolic ∧
      deningerFloquetRelativeMonodromyFirstJet q * C = C * photonicParabolic := by
  rintro ⟨C, B, hCB, hp, hq⟩
  apply hpq
  apply deningerFloquetRelativeMonodromyFirstJet_injective
  calc
    deningerFloquetRelativeMonodromyFirstJet p =
        deningerFloquetRelativeMonodromyFirstJet p * (C * B) := by rw [hCB, mul_one]
    _ = (deningerFloquetRelativeMonodromyFirstJet p * C) * B := by rw [Matrix.mul_assoc]
    _ = (C * photonicParabolic) * B := by rw [hp]
    _ = (deningerFloquetRelativeMonodromyFirstJet q * C) * B := by rw [hq]
    _ = deningerFloquetRelativeMonodromyFirstJet q * (C * B) := by rw [Matrix.mul_assoc]
    _ = deningerFloquetRelativeMonodromyFirstJet q := by rw [hCB, mul_one]

end RHTower
