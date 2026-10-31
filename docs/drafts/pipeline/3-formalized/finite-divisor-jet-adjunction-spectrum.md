# The finite divisor graph has the exact adjunction spectrum

- **ID:** SSH-FINITE-DIVISOR-JET-ADJUNCTION-SPECTRUM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1/O1, finite conductor Hamiltonian behind the divisor-jet square completion.

## Statement

For `M≥1`, use the divisor energy

`E_M(f)=Σ_(m|M)Σ_(k|m)Λ(m/k)φ(k)(f(m)−f(k))²`

and scalar product `⟨f,g⟩_M=(1/M)Σ_(k|M)φ(k)f(k)g(k)`.
The orthonormal eigenbasis is

`v_d(k)=c_d(M/k)/√φ(d)`, for `d|M`,

with eigenvalue `λ_d=log d+tameDifferent(d)`. Thus, with
`A_d=⟨f,v_d⟩_M`, the diagonalization is

`E_M(f)=M Σ_(d|M)λ_d A_d²`.

Equivalently, for `F(n)=Σ_(k|M)f(k)c_k(n)`, the exact formula is

`E_M(f)=(1/M)Σ_(d|M)φ(d)λ_d F(M/d)²`.

Totient-weighted Ramanujan reciprocity identifies the two expressions.
Grouping the integer period by gcd classes also gives
`E_M(f)=(1/M)Σ_(n<M)λ_(M/gcd(M,n)) F(n)²`.
All identities are formalized.

## Lean

Namespace `GaloisForLFunctions.SuccessorShellArithmetic`, in `Conductor/`:

- `DivisorJetReciprocity.lean`: `divisor_lag_quotient_eq`,
  `divisor_ramanujan_reciprocity`, `divisor_jet_reciprocity`,
  `sum_divisors_totient_ramanujan_mul`, `sum_divisors_ramanujan_reciprocal`,
  `divisor_profile_ramanujan_expansion`.
- `DivisorJetSpectrum.lean`: `divisorJetGenerator_ramanujan`,
  `divisorJetEnergy_eq_generator`, `divisorJetEnergy_eq_adjunction_spectrum`,
  `divisorJetEnergy_eq_period_symbol`.

Both direct `lake --old env lean` audits passed without diagnostics.
Transitive axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`.
Both modules are imported by the programme umbrella.

## Paper proof

For `m≥1`, set `q=m/gcd(m,n)`. The finite real-power quotient identity gives

`J_m(n)=c_m(n)(λ_m−λ_q)`.

For `d,k|M`, multiplying `gcd(d,M/k)` by `k` and `gcd(k,M/d)` by `d`
gives the same `gcd(dk,M)`. Hence the reduced lag quotients coincide.
The ordinary Möbius/totient quotient and the jet-gap identity give

`φ(k)c_d(M/k)=φ(d)c_k(M/d)`,

`φ(k)J_d(M/k)−φ(d)J_k(M/d)`
`=(λ_d−λ_k)φ(k)c_d(M/k)`.

Use the weighted generator

`L_M f(k)=Σ_(a|k)Λ(k/a)φ(a)[f(k)−f(a)]`
`          +φ(k)Σ_(r|M/k)Λ(r)[f(k)−f(kr)]`.

The exact downward prime convolution and the conductor expansion of `J`
identify its two rows. Jet reciprocity then gives
`L_M[c_d(M/·)](k)=φ(k)λ_d c_d(M/k)`.
Reindexing divisor chains gives `E_M(f)=Σ_(k|M)f(k)L_M f(k)`.

Each gcd class has cardinality `φ(M/g)`. Complete-period orthogonality
therefore gives
`Σ_(k|M)φ(k)c_d(M/k)c_e(M/k)=Mφ(d)·1_(d=e)`.
Reciprocity turns this into the inversion formula
`f(k)=(1/M)Σ_(d|M)F(M/d)c_d(M/k)`.
Substitute into the generator and apply reciprocity once more; its
quadratic form becomes the stated diagonal sum.

## Corpus boundary

The corpus already identifies the infinite finite-prime sieve's
adjunction eigenbasis. This theorem concerns the exact finite divisor
lattice and its top valuation boundary. The missing comparison with
the actual finite-horizon complete Weil form remains separate.

- [x] Existing sieve adjunction basis and finite divisor-square mechanisms identified.
- [x] Finite reciprocity, basis inversion and generator calculation on paper.
- [x] Complete basis and exact energy identity formalized.
- [x] Lean formalization and dependency audit.
