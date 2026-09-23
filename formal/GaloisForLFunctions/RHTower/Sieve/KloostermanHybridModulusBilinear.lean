import GaloisForLFunctions.RHTower.Sieve.KloostermanModulusBilinear
import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridLargeSieve

/-!
# Signed modulus-average Kloosterman hybrid form

This is the physical-height specialization of `kloostermanModulusBilinear`: both residue vectors
are additive twists of ordinary Dirichlet coefficient sequences.  The finite modulus sum remains
inside the complex amplitude, so later Kuznetsov or Deshouillers--Iwaniec cancellation is not
destroyed by premature absolute values.
-/

open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Signed Kloosterman hybrid amplitude across a finite family of moduli. -/
def kloostermanHybridModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ q ∈ Q, w q *
    ∑ n : ZMod (q + 1),
      additiveHybridDirichletPoly q M (b q) n t *
        kloostermanHybridTransform q N (a q) n t

/-- The hybrid amplitude is the generic signed modulus bilinear form evaluated on the two
additive Dirichlet vectors. -/
theorem kloostermanHybridModulusBilinear_eq
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℕ → ℂ) (t : ℝ) :
    kloostermanHybridModulusBilinear Q w N M a b t =
      kloostermanModulusBilinear Q w
        (fun q d => additiveHybridDirichletPoly q N (a q) d t)
        (fun q n => additiveHybridDirichletPoly q M (b q) n t) := by
  unfold kloostermanHybridModulusBilinear kloostermanModulusBilinear
    kloostermanBilinear kloostermanHybridTransform
  rfl

/-- Every finite signed hybrid modulus amplitude is continuous in physical height. -/
theorem continuous_kloostermanHybridModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℕ → ℂ) :
    Continuous (kloostermanHybridModulusBilinear Q w N M a b) := by
  unfold kloostermanHybridModulusBilinear
  apply continuous_finsetSum
  intro q _hq
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro n _hn
  exact (continuous_additiveHybridDirichletPoly q M (b q) n).mul
    (continuous_kloostermanHybridTransform q N (a q) n)

/-- Pointwise fixed-modulus baseline for the signed hybrid amplitude. -/
theorem norm_kloostermanHybridModulusBilinear_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℕ → ℂ) (t : ℝ) :
    ‖kloostermanHybridModulusBilinear Q w N M a b t‖ ≤
      ∑ q ∈ Q, ‖w q‖ * ((q + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ d : ZMod (q + 1),
          ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ (2 : ℕ)) *
        Real.sqrt (∑ n : ZMod (q + 1),
          ‖additiveHybridDirichletPoly q M (b q) n t‖ ^ (2 : ℕ)) := by
  rw [kloostermanHybridModulusBilinear_eq]
  exact norm_kloostermanModulusBilinear_le_baseline Q w
    (fun q d => additiveHybridDirichletPoly q N (a q) d t)
    (fun q n => additiveHybridDirichletPoly q M (b q) n t)

/-- Pointwise direct-sum square baseline, before any spectral saving in the modulus variable. -/
theorem norm_kloostermanHybridModulusBilinear_sq_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℕ → ℂ) (t : ℝ) :
    ‖kloostermanHybridModulusBilinear Q w N M a b t‖ ^ (2 : ℕ) ≤
      (∑ q ∈ Q,
        (‖w q‖ * ((q + 1 : ℕ) : ℝ) *
          Real.sqrt (∑ d : ZMod (q + 1),
            ‖additiveHybridDirichletPoly q N (a q) d t‖ ^ (2 : ℕ))) ^ (2 : ℕ)) *
      ∑ q ∈ Q,
        (Real.sqrt (∑ n : ZMod (q + 1),
          ‖additiveHybridDirichletPoly q M (b q) n t‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
  rw [kloostermanHybridModulusBilinear_eq]
  exact norm_kloostermanModulusBilinear_sq_le_baseline Q w
    (fun q d => additiveHybridDirichletPoly q N (a q) d t)
    (fun q n => additiveHybridDirichletPoly q M (b q) n t)

end

end RHTower.Sieve
