import GaloisForLFunctions.RHTower.MobiusDivisorLateBlockBooleanTransport
import GaloisForLFunctions.RHTower.MobiusDivisorOrientedPrimeDilationRenormalization

/-!
# All-order background--copy decomposition at a prime dilation

At a fresh prime dilation, each oriented residual coordinate after processing
the dilation prime is the large-cutoff `p`-free background minus a
square-root-amplified old coordinate.  This file promotes that pointwise law
to every finite weighted residual detector and every Boolean jet of its
processed-core response.

Thus a moving-core transition has exactly three contributions at every finite
grade: the new background jet, `p` times the inherited jet, and one signed
background--copy cross jet.  The cross jet is the only term which can repay
or amplify inherited covariance.  No sign or quantitative bound for it is
assumed here.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- A finite weighted square detector for oriented residual source fibres. -/
def mobiusDivisorOrientedResidualDetector
    (M : ℕ) (P : Finset ℕ) (T : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) : ℝ :=
  ∑ R ∈ T, w R * (mobiusDivisorOrientedFibre M P R)^(2 : ℕ)

/-- The signed background--copy pairing seen by one finite residual detector. -/
def mobiusDivisorOrientedResidualCrossDetector
    (M N : ℕ) (P : Finset ℕ) (T : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) : ℝ :=
  ∑ R ∈ T, w R * mobiusDivisorOrientedFibre M P R *
    mobiusDivisorOrientedFibre N P R

/-- **Exact detector renormalization.** After a fresh prime dilation, every
finite oriented detector is background energy plus amplified inherited energy
minus twice the square-root-scale background--copy covariance. -/
theorem mobiusDivisorOrientedResidualDetector_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P : Finset ℕ) (T : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) (hpP : p ∉ P)
    (hpT : ∀ R ∈ T, p ∉ R) :
    mobiusDivisorOrientedResidualDetector (p * N) (insert p P) T w =
      mobiusDivisorOrientedResidualDetector (p * N) P T w +
        (p : ℝ) * mobiusDivisorOrientedResidualDetector N P T w -
          2 * Real.sqrt p *
            mobiusDivisorOrientedResidualCrossDetector (p * N) N P T w := by
  unfold mobiusDivisorOrientedResidualDetector
    mobiusDivisorOrientedResidualCrossDetector
  calc
    (∑ R ∈ T, w R * (mobiusDivisorOrientedFibre (p * N) (insert p P) R)^(2 : ℕ)) =
        ∑ R ∈ T,
          (w R * (mobiusDivisorOrientedFibre (p * N) P R)^(2 : ℕ) +
            (p : ℝ) * (w R * (mobiusDivisorOrientedFibre N P R)^(2 : ℕ)) -
              (2 * Real.sqrt p) *
                (w R * mobiusDivisorOrientedFibre (p * N) P R *
                  mobiusDivisorOrientedFibre N P R)) := by
          apply sum_congr rfl
          intro R hR
          rw [mobiusDivisorOrientedFibre_insert_mul_prime_square_renormalization
            hp hNp P R hpP (hpT R hR)]
          ring
    _ = _ := by
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]

/-- **All-order detector renormalization.** A prime-dilation transition has
the same exact background/copy/cross decomposition on every finite Boolean
jet.  Hence controlling diagonal detector energy at either scale cannot
replace control of the displayed cross jet. -/
theorem mobiusDivisorOrientedResidualDetector_booleanAlternating_insert_mul_prime
    {N p : ℕ} (hp : p.Prime) (hNp : N < p)
    (P A : Finset ℕ) (T : Finset (Finset ℕ)) (w : Finset ℕ → ℝ) (hpP : p ∉ P)
    (hpA : p ∉ A) (hpT : ∀ R ∈ T, p ∉ R) :
    mobiusDivisorBooleanAlternating (insert p P) A
        (fun Q => mobiusDivisorOrientedResidualDetector (p * N) Q T w) =
      mobiusDivisorBooleanAlternating P A
          (fun Q => mobiusDivisorOrientedResidualDetector (p * N) Q T w) +
        (p : ℝ) * mobiusDivisorBooleanAlternating P A
          (fun Q => mobiusDivisorOrientedResidualDetector N Q T w) -
          2 * Real.sqrt p * mobiusDivisorBooleanAlternating P A
            (fun Q => mobiusDivisorOrientedResidualCrossDetector (p * N) N Q T w) := by
  have hterm (B : Finset ℕ) (hB : B ∈ A.powerset) :
      mobiusDivisorOrientedResidualDetector (p * N) ((insert p P) ∪ B) T w =
        mobiusDivisorOrientedResidualDetector (p * N) (P ∪ B) T w +
          (p : ℝ) * mobiusDivisorOrientedResidualDetector N (P ∪ B) T w -
            2 * Real.sqrt p *
              mobiusDivisorOrientedResidualCrossDetector (p * N) N (P ∪ B) T w := by
    have hpB : p ∉ B := fun hpB => hpA (mem_powerset.mp hB hpB)
    have hpPB : p ∉ P ∪ B := by simp [hpP, hpB]
    have hunion : (insert p P) ∪ B = insert p (P ∪ B) := by
      ext q
      simp only [mem_union, mem_insert]
      tauto
    rw [hunion, mobiusDivisorOrientedResidualDetector_insert_mul_prime
      hp hNp (P ∪ B) T w hpPB hpT]
  have hrewrite :
      mobiusDivisorBooleanAlternating (insert p P) A
          (fun Q => mobiusDivisorOrientedResidualDetector (p * N) Q T w) =
        mobiusDivisorBooleanAlternating P A
          (fun Q =>
            mobiusDivisorOrientedResidualDetector (p * N) Q T w +
              (p : ℝ) * mobiusDivisorOrientedResidualDetector N Q T w -
                2 * Real.sqrt p *
                  mobiusDivisorOrientedResidualCrossDetector (p * N) N Q T w) := by
    unfold mobiusDivisorBooleanAlternating
    apply sum_congr rfl
    intro B hB
    exact congrArg (fun x : ℝ => (-1 : ℝ)^B.card * x) (hterm B hB)
  rw [hrewrite]
  have hnormal :
      (fun Q =>
        mobiusDivisorOrientedResidualDetector (p * N) Q T w +
          (p : ℝ) * mobiusDivisorOrientedResidualDetector N Q T w -
            2 * Real.sqrt p *
              mobiusDivisorOrientedResidualCrossDetector (p * N) N Q T w) =
        fun Q =>
          mobiusDivisorOrientedResidualDetector (p * N) Q T w +
            (p : ℝ) * mobiusDivisorOrientedResidualDetector N Q T w +
              (-2 * Real.sqrt p) *
                mobiusDivisorOrientedResidualCrossDetector (p * N) N Q T w := by
    funext Q
    ring
  rw [hnormal]
  have hcross := mobiusDivisorBooleanAlternating_affine P A
    (fun Q =>
      mobiusDivisorOrientedResidualDetector (p * N) Q T w +
        (p : ℝ) * mobiusDivisorOrientedResidualDetector N Q T w)
    (fun Q => mobiusDivisorOrientedResidualCrossDetector (p * N) N Q T w)
    (-2 * Real.sqrt p) 0
  simp only [zero_mul, add_zero] at hcross
  rw [hcross]
  have hbackground := mobiusDivisorBooleanAlternating_affine P A
    (fun Q => mobiusDivisorOrientedResidualDetector (p * N) Q T w)
    (fun Q => mobiusDivisorOrientedResidualDetector N Q T w) (p : ℝ) 0
  simp only [zero_mul, add_zero] at hbackground
  rw [hbackground]
  ring

end RHTower
