/-
# The weld commutator: the abstract rate is a concrete derivative eigenvalue

`WeldClassTable` records the weld as an abstract group cocycle with class `θ = log(base) ∈ H²`, and
`SeamSpectrumDensity` records that the rate group `⟨log p⟩` — the spectrum of `ad(∂_s)` — is dense.
Both are stated on the *abstract* rate `log p`.  This file realizes that rate **concretely**, as the
eigenvalue of the actual archimedean derivation acting on the actual prime-shift operator, so the
abstract weld and its spectrum are grounded in genuine analysis, not just posited.

The prime shift is multiplication by the Euler exponential `M_a f = fun z ↦ a^{−z}·f z` (`a = p`
gives the `p`-factor `p^{−s}`).  The archimedean generator is `∂ = d/ds`.  Their commutator is an
**operator identity**:

  `[∂, M_a] f = ∂(M_a f) − M_a(∂ f) = −(log a)·M_a f`,

so every prime-shift operator is an eigenvector of `ad(∂)` with eigenvalue the rate `−log a`.  For a
prime the eigenvalue is the real number `−log p`, an element of `primeLogLattice` — the very spectrum
whose gaplessness `SeamSpectrumDensity` establishes.  The `[∂, M_a] = −(log a)M_a` bracket is the
`ax + b`/affine Lie relation underlying the abstract `H²` cocycle: this is where `log a` *comes from*.

Nothing here detects a zero; it is the infinitesimal structure of the weld, read off calculus.
-/
import GaloisForLFunctions.RHTower.SeamSpectrumDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

open Complex

namespace GaloisForLFunctions
namespace RHTower

/-- **The weld commutator, general base.**  For `a ≠ 0` and `f` differentiable at `s`, the archimedean
derivation and the shift-operator `M_a : f ↦ (a^{−·})·f` satisfy `[∂, M_a] f (s) = −(log a)·(M_a f)(s)`:
`M_a` is an eigenvector of `ad(∂)` with eigenvalue `−log a`.  Pure product rule with
`d/dz (a^{−z}) = −(log a) a^{−z}`. -/
theorem weld_commutator (a : ℂ) (ha : a ≠ 0) (f : ℂ → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) :
    deriv (fun z => a ^ (-z) * f z) s - a ^ (-s) * deriv f s
      = -(Complex.log a) * (a ^ (-s) * f s) := by
  have hM : HasDerivAt (fun z : ℂ => a ^ (-z)) (a ^ (-s) * Complex.log a * (-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl ha)
  have hprod : HasDerivAt (fun z => a ^ (-z) * f z)
      (a ^ (-s) * Complex.log a * (-1) * f s + a ^ (-s) * deriv f s) s :=
    hM.mul hf.hasDerivAt
  rw [hprod.deriv]; ring

/-- **The weld commutator, prime base.**  For a prime `p` the eigenvalue is the *real* rate
`−log p`: `[∂, M_p] f (s) = (−log p)·(M_p f)(s)`.  This is the concrete realization of the abstract
weld cocycle `θ = log p` as the derivative eigenvalue of the `p`-Euler-factor operator. -/
theorem weld_commutator_prime (p : ℕ) (hp : 0 < p) (f : ℂ → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) :
    deriv (fun z => (p:ℂ) ^ (-z) * f z) s - (p:ℂ) ^ (-s) * deriv f s
      = (-(Real.log p) : ℝ) • ((p:ℂ) ^ (-s) * f s) := by
  have ha : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hM : HasDerivAt (fun z : ℂ => (p:ℂ) ^ (-z)) ((p:ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl ha)
  have hprod : HasDerivAt (fun z => (p:ℂ) ^ (-z) * f z)
      ((p:ℂ) ^ (-s) * Complex.log p * (-1) * f s + (p:ℂ) ^ (-s) * deriv f s) s :=
    hM.mul hf.hasDerivAt
  rw [hprod.deriv]
  have hlog : Complex.log (p:ℂ) = (Real.log p : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  rw [hlog, Complex.real_smul]; push_cast; ring

/-- **The eigenvalue is a point of the weld spectrum.**  The commutator eigenvalue `−log p` of the
`p`-shift operator lies in `primeLogLattice = ⟨log p⟩` — the `ad(∂_s)`-spectrum whose density is
`primeLogLattice_dense`.  So the concrete derivative eigenvalues *are* the abstract rate lattice, and
the gapless-spectrum invariant is a statement about these genuine operator eigenvalues. -/
theorem weld_eigenvalue_mem_primeLogLattice {p : ℕ} (hp : p.Prime) :
    -(Real.log p) ∈ primeLogLattice :=
  primeLogLattice.neg_mem (primeLog_mem_primeLogLattice hp)

end RHTower
end GaloisForLFunctions
