import Mathlib.NumberTheory.PrimeCounting
import GaloisForLFunctions.RHTower.ArchimedeanCorank
import GaloisForLFunctions.HTGeometry.KroneckerFlow

/-!
# Finite-aperture prime-torus carrier law

The cutoff Euler product
`Z_{N,σ}(t) = ∏_{p ≤ N} (1 - p^{-σ-it})^{-1}`
is a continuous translation-equivariant observable of the aperture-`N` prime torus `T^{π(N)}`, whose
coordinate characters are indexed by the primes `p ≤ N`.  Any compact abelian phase carrier that
produces this observable must transport at least `π(N)` independent phase dimensions.

The load-bearing arithmetic is unique factorization.  The coordinate log-frequencies
`{log p : p ≤ N}` are `ℚ`-linearly independent, so the aperture-`N` character lattice — realized
here as the frequency module `span_ℚ {log p : p ≤ N}` — has rank exactly `π(N) = Nat.primeCounting N`.
A carrier producing the observable factors continuously onto the aperture hull; dualizing, its
rational character space receives an injection of this rank-`π(N)` module, so its covering dimension
(equal to rational character rank for a finite-dimensional compact abelian group) is at least `π(N)`.
The dimension is unbounded: `π(N) → ∞`, so no fixed finite-dimensional carrier serves all apertures.

The Kronecker–Weyl density of the diagonal orbit and the compact-group covering-dimension = character
rank identity are the classical topological envelope of this algebraic core.  The injection of
character lattices is the interface standing for the dual of the carrier's factor map; each
coordinate character contributes the concrete diagonal-flow frequency `log p` of the module.
-/

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The primes at most `N`, packaged as a `Finset Nat.Primes`.  This is the coordinate index of the
aperture-`N` prime torus `T^{π(N)}` whose observable is the cutoff Euler product. -/
def primesLE (N : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow (N + 1)).attach.map
    ⟨fun x : {n // n ∈ Nat.primesBelow (N + 1)} =>
        (⟨x.1, Nat.prime_of_mem_primesBelow x.2⟩ : Nat.Primes),
     fun _ _ h => Subtype.ext (congrArg (fun q : Nat.Primes => q.val) h)⟩

/-- The aperture count is the prime-counting function `π(N)`. -/
@[simp]
theorem primesLE_card (N : ℕ) : (primesLE N).card = Nat.primeCounting N := by
  unfold primesLE
  rw [Finset.card_map, Finset.card_attach, Nat.primesBelow_card_eq_primeCounting']
  rfl

/-- Membership in `primesLE N` is exactly being a prime with value at most `N`. -/
@[simp]
theorem mem_primesLE (N : ℕ) (p : Nat.Primes) : p ∈ primesLE N ↔ (p : ℕ) ≤ N := by
  unfold primesLE
  simp only [Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk,
    Subtype.exists]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hn).1
  · intro hp
    exact ⟨(p : ℕ), Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hp, p.2⟩, rfl⟩

/-- The aperture-`N` prime frequency module: the `ℚ`-span of the coordinate log-frequencies
`{log p : p ≤ N}`.  Pontryagin-dually this is the character lattice of the aperture-`N` prime torus,
rationalized. -/
def primeApertureCharacterModule (N : ℕ) : Submodule ℚ ℝ :=
  primeLogSpan (primesLE N)

/-- Unique factorization gives `ℚ`-linear independence of the aperture-`N` coordinate
log-frequencies.  This is the rational-independence input that forces a nontrivial torus. -/
theorem primeAperture_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun p : primesLE N => Real.log ((p : Nat.Primes) : ℕ)) :=
  primeLogFiniteSlice_linearIndependent (primesLE N)

/-- The aperture-`N` character lattice has rational rank exactly `π(N)`. -/
@[simp]
theorem primeApertureCharacterModule_finrank (N : ℕ) :
    Module.finrank ℚ (primeApertureCharacterModule N) = Nat.primeCounting N := by
  unfold primeApertureCharacterModule
  rw [primeLogFiniteSlice_finrank, primesLE_card]

/-- Each coordinate character contributes the concrete diagonal-flow frequency `log p`, which lies in
the aperture module.  This grounds the abstract lattice in the actual Kronecker-flow spectrum. -/
theorem primeLogFrequency_single_mem_aperture (N : ℕ) {p : Nat.Primes} (hp : p ∈ primesLE N) :
    primeLogFrequency (Finsupp.single p 1) ∈ primeApertureCharacterModule N := by
  rw [primeLogFrequency_single]
  have hlog : Real.log ((p : Nat.Primes) : ℕ) ∈ primeApertureCharacterModule N := by
    unfold primeApertureCharacterModule primeLogSpan
    exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
  simpa using hlog

/-- **Carrier covering-dimension lower bound.**  Let `A` be the rational character space of a compact
abelian phase carrier producing the aperture-`N` cutoff Euler product as a continuous
translation-equivariant observable.  The carrier factors continuously onto the aperture hull, so its
dual receives an injection `j` from the aperture-`N` character lattice.  Then the covering dimension
of the carrier — the rational rank `Module.finrank ℚ A` — is at least `π(N)`. -/
theorem primeAperture_carrier_covering_dim_ge {A : Type*} [AddCommGroup A] [Module ℚ A]
    [Module.Finite ℚ A] (N : ℕ)
    (j : primeApertureCharacterModule N →ₗ[ℚ] A) (hj : Function.Injective j) :
    Nat.primeCounting N ≤ Module.finrank ℚ A := by
  have h := LinearMap.finrank_le_finrank_of_injective (f := j) hj
  rwa [primeApertureCharacterModule_finrank] at h

/-- **Dimension divergence.**  For every bound `M` there is an aperture `N` whose forced carrier
covering dimension exceeds `M`.  Thus no fixed finite-dimensional carrier produces the cutoff Euler
product for all apertures; the phase dimension diverges with `N`. -/
theorem primeAperture_dim_unbounded (M : ℕ) : ∃ N, M ≤ Nat.primeCounting N := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq Nat.Primes M
  refine ⟨S.sup (fun p => (p : ℕ)), ?_⟩
  rw [← primesLE_card, ← hS]
  apply Finset.card_le_card
  intro p hp
  rw [mem_primesLE]
  exact Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp

end

end GaloisForLFunctions
