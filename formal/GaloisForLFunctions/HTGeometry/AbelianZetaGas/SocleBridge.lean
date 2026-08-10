import GaloisForLFunctions.HTGeometry.PartitionQPochhammerBridge
import GaloisForLFunctions.HTGeometry.EulerQGammaGlobalLaw

/-!
# The socle bridge: the Euler weights are the shadow of geometric prime-power modes

At the prime `p` the abelian zeta gas has one geometric mode for every depth `j`, with occupation
ratio `p^{−(j+1)σ}`, that is `q^{j+1}` for the nome `q = p^{−σ}`.  The mass of a local
configuration is therefore `(q;q)_∞ · q^{size}`, and summing over the configurations with exactly
`n` cyclic factors gives the Euler weight of the random-integer law of `ULF-EQG-1` at `pⁿ`.

This is (GAS.5): the corpus's local Euler weights are not primitive, they are the socle-observer
shadow of independent geometric prime-power modes, and Euler's partition identity is the change of
observer.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

noncomputable section

/-- The depth-`j` occupation ratio at the prime `p` is the `(j+1)`-st power of the nome. -/
theorem eqgNome_pow_succ (σ : EulerSigma) (p : Nat.Primes) (j : ℕ) :
    ((eqgNome σ p).val) ^ (j + 1) = ((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val)) := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eqgNome_val, eqgQ, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ.val)) (j + 1),
    ← Real.rpow_mul hp]
  congr 1
  push_cast
  ring

/-- **(GAS.5).**  The local socle marginal of the abelian zeta gas at the prime `p` is the Euler
weight of the random-integer law at `pⁿ`. -/
theorem gas_socleMarginal_eq_eulerWeight (σ : EulerSigma) (p : Nat.Primes) (n : ℕ) :
    (∑' g : {g : PartConfig // partCount g = n},
        ENNReal.ofReal (∏' j : ℕ,
          ((((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val))) ^ (g.1 j)
            * (1 - ((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val)))))).toReal
      = realQFactorialInf (eqgNome σ p) * eqgWeight σ ((p : ℕ) ^ n) := by
  have hratio : ∀ j : ℕ,
      ((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val)) = ((eqgNome σ p).val) ^ (j + 1) :=
    fun j => (eqgNome_pow_succ σ p j).symm
  have hcongr : (fun g : {g : PartConfig // partCount g = n} =>
        ENNReal.ofReal (∏' j : ℕ,
          ((((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val))) ^ (g.1 j)
            * (1 - ((p : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * σ.val))))))
      = fun g : {g : PartConfig // partCount g = n} =>
        ENNReal.ofReal (∏' j : ℕ,
          ((((eqgNome σ p).val) ^ (j + 1)) ^ (g.1 j)
            * (1 - ((eqgNome σ p).val) ^ (j + 1)))) := by
    funext g
    congr 1
    exact tprod_congr fun j => by rw [hratio j]
  rw [hcongr, tsum_localModeMass_toReal (eqgNome σ p) n, eqgWeight_prime_pow σ p n]

end

end GaloisForLFunctions.HTGeometry
