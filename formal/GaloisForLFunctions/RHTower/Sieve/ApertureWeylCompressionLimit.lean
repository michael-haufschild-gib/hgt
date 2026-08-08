import GaloisForLFunctions.RHTower.ProjectiveTensorAperture
import GaloisForLFunctions.RHTower.Sieve.PrimeLeakageProductLimit

/-!
# The Weyl compression coefficient of the prime aperture

Over the aperture of all primes `p ≤ N`, the local projective clocks assemble into one tensor
product, the local Weyl inversions into one reflection, and the local point/complement projections
into one compression.  Applying the reflection to the aperture natural-cone state and compressing it
back to the producer polarizations produces a coefficient whose Hilbert norm is exactly the product
of the local Hellinger weights `√(1 - L_p)`.

Combining this with the prime-profile limit of that product identifies the limit of the aperture
compression coefficient with the squarefree Hellinger–Fock kernel.
-/

namespace RHTower.Sieve

open RHTower Filter
open scoped TensorProduct Topology

noncomputable section

/-- The aperture index: the primes up to `N`. -/
abbrev primeAperture (N : ℕ) : Type := {p : ℕ // p ∈ Nat.primesLE N}

instance factPrime_primeAperture {N : ℕ} (i : primeAperture N) : Fact (i : ℕ).Prime :=
  ⟨(Nat.mem_primesLE.1 i.2).2⟩

/-- The Euler producer marking of the aperture: the point at infinity in every local clock. -/
def apertureInfinity (N : ℕ) : ∀ i : primeAperture N, Option (ZMod (i : ℕ)) := fun _ => none

/-- The Weyl reflection of the aperture: the residue inversion `x ↦ -1/x` in every local clock. -/
def apertureWeyl (N : ℕ) : ∀ i : primeAperture N, Equiv.Perm (Option (ZMod (i : ℕ))) :=
  fun i => weylInversion (i : ℕ)

/-- **Equation (15).**  The Hilbert norm of the compressed reflected aperture state is the product
of the local Hellinger weights. -/
theorem apertureNorm_weylCompression (N : ℕ) (z : primeAperture N → ℝ) :
    apertureNorm (apertureCompress (apertureInfinity N)
        (aperturePermute (apertureWeyl N) (apertureNatural (apertureInfinity N) z)))
      = ∏ i : primeAperture N, Real.sqrt (1 - primeLeakage (i : ℕ) (z i)) := by
  have h2 : ∀ i : primeAperture N, 2 ≤ Fintype.card (Option (ZMod (i : ℕ))) :=
    fun i => two_le_card_optionZMod (i : ℕ)
  have hσ : ∀ i : primeAperture N,
      apertureInfinity N i ≠ apertureWeyl N i (apertureInfinity N i) := by
    intro i
    rw [apertureInfinity, apertureWeyl, weylInversion_infinity]
    simp
  rw [apertureNorm_compress_permute_natural h2 (apertureInfinity N) hσ z]
  exact Finset.prod_congr rfl fun i _ => by
    rw [primeLeakage_eq_projLeakageValue (i : ℕ) (z i)]

/-- **Equation (14), in operator form.**  The Hilbert norm of the compressed reflected aperture
state converges to the squarefree Hellinger–Fock kernel `𝓚(f, 0)`. -/
theorem tendsto_apertureNorm_weylCompression {f : ℝ → ℝ} {F Lf : ℝ}
    (hf : Continuous f) (hf0 : f 0 = 0) (hfb : ∀ t, |f t| ≤ F)
    (hflip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) :
    Tendsto (fun N : ℕ => apertureNorm (apertureCompress (apertureInfinity N)
        (aperturePermute (apertureWeyl N)
          (apertureNatural (apertureInfinity N)
            (fun i => f (Real.log (i : ℕ) / Real.log N))))))
      atTop
      (𝓝 (Real.exp (-((∫ t in (0 : ℝ)..1, expProfile f t / t) / 2)))) := by
  refine (tendsto_prod_sqrt_one_sub_primeLeakage hf hf0 hfb hflip).congr ?_
  intro N
  rw [apertureNorm_weylCompression]
  exact (Finset.prod_coe_sort (Nat.primesLE N)
    (fun p => Real.sqrt (1 - primeLeakage p (f (Real.log p / Real.log N))))).symm

end

end RHTower.Sieve
