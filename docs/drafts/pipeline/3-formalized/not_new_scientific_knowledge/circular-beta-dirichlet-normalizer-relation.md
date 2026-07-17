# Circular beta-ensemble and Dirichlet normalizers differ by a rational gauge

- **ID:** `circular-beta-dirichlet-normalizer-relation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** T. Jiang and S. Matsumoto, *Moments of Traces for Circular Beta-Ensembles*, arXiv:1102.4123, equations (1.3) and (2.10); R. Chhaibi and J. Najnudel, *On the circle, Gaussian Multiplicative Chaos and Beta Ensembles match exactly*, arXiv:1904.00578; P. Saad, S. H. Shenker, and D. Stanford, *JT gravity as a matrix integral*, arXiv:1903.11115; D. Stanford and E. Witten, *JT Gravity and the Ensembles of Random Matrix Theory*, arXiv:1907.03363
- **Statement:** For every positive eigenangle count `K`, the circular beta-ensemble partition normalizer `Gamma(Kz+1)/Gamma(z+1)^K` is exactly the symmetric Dirichlet normalizer `Gamma(Kz)/Gamma(z)^K` times the rational gauge `Kz/z^K`; both are DA exactly at `K=1` and HT exactly at `K>1`.

## Goal

Turn the exact Selberg integral of the circular beta ensemble into a cross-domain value theorem
linking random-matrix quantum statistics to the symmetric Dirichlet normalizer used in AI and
genomics.  The theorem must classify the coupling observable and its exact cancellation, not infer
temporal dynamics from a parameterized partition function.

## Gates

- [x] 0 → 1 in-progress: exact primary-source circular beta-ensemble normalization located
- [x] 1 → 2 fully-proven: scaled Gamma recurrence and rational quotient identity proved
- [x] 2 → 3 formalized: exact targeted module build, direct file check, and axiom audit pass
- [ ] 3 → 4 publication-ready: application note not yet written

## Source relation

Jiang--Matsumoto give the circular beta density and the normalized Selberg integral

`(2*pi)^(-K) integral prod_{p<q}|exp(i theta_p)-exp(i theta_q)|^beta d theta
  = Gamma(K*beta/2+1)/Gamma(beta/2+1)^K`.

Writing `z=beta/2`, its Gamma partition normalizer is

`C_K(z)=Gamma(Kz+1)/Gamma(z+1)^K`.

The same source recalls Dyson's introduction of the circular ensembles for nuclear scattering and
the `beta=1,2,4` time-reversal symmetry classes.  Separate primary sources identify matrix
ensembles with JT gravity variants and circular beta ensembles with circular Gaussian
multiplicative chaos.  Those facts motivate consumers of the formal theorem; Lean proves the
normalizer identity itself, not a JT-gravity or GMC equivalence.

## Exact positive statement

The newly formalized scaled recurrence gives

`Gamma(Kz+1)=(Kz) Gamma(Kz)`

and the unit-scale recurrence gives

`Gamma(z+1)=z Gamma(z)`.

Therefore

`C_K(z) = (Kz/z^K) * [Gamma(Kz)/Gamma(z)^K]`.

The bracket is the symmetric Dirichlet normalizer.  The quotient of the random-matrix and
AI/genomic observables is thus exactly rational and hence DA, even though each observable is HT
for every `K>1`.  For `K=1`, both are exactly one.  This yields the complete boundary

`DA(C_K) iff K=1`, and `HT(C_K) iff 1<K`.

The Gamma factor multiplying the circular-ensemble density is exactly `C_K(z)^(-1)`.  The generic
inversion theorem added to `ExponentialObservationHypertranscendence` has no nonzero hypothesis,
so the density Gamma normalizer is HT exactly for `K>1` as well.  Partition and density
normalizers multiply to one identically in the meromorphic field.

The finite-circuit corollary is the nontrivial positive source statement: any scalar-aware finite
differential circuit realizing the interacting `K>1` partition normalizer must contain an HT
non-scalar atom.

## Corpus value

The result adds a reusable parameter recurrence for every positive natural scale,
`Gamma(nz+a+1)=(nz+a)Gamma(nz+a)`, to `MeromorphicGammaNatScale`.  The application module then
connects two previously separate theorem surfaces by an exact DA quotient, transports the complete
Dirichlet category-count classification to a quantum-statistical partition function, and adds
source extraction for random-matrix normalization circuits.

It also adds the general corpus lemmas `hypertranscendentalOver_inv_iff` and
`hypertranscendentalOver_div_differentialAlgebraic_iff`, eliminating repeated nonzero side
conditions when moving between a partition normalizer, its density prefactor, and DA-gauged
quotients.

## Lean certificate

Modules:

- `GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale`
- `GaloisForLFunctions.HTGeometry.CircularBetaEnsembleNormalizerBoundary`

Capstones:

- `gammaNatScaleMero_add_one`
- `circularBetaEnsemblePartitionNormalizerMero_eq_dirichlet`
- `circularBetaEnsemblePartition_mul_densityGammaNormalizer`
- `circularBetaEnsemble_div_symmetricDirichlet_eq_gauge`
- `differentialAlgebraicOver_circularBetaEnsemble_div_symmetricDirichlet`
- `differentialAlgebraicOver_circularBetaEnsemblePartitionNormalizerMero_iff_one`
- `hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero_iff_many`
- `hypertranscendentalOver_circularBetaEnsembleDensityGammaNormalizerMero_iff_many`
- `exists_hypertranscendental_atom_of_circularBetaEnsembleNormalizerCircuit`

All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Limits

The formal theorem concerns the circular beta Selberg normalizer as a meromorphic function of the
complexified coupling `z`.  It does not prove that every random-matrix observable, a time-evolved
quantum system, JT gravity, or Gaussian multiplicative chaos is HT.  The JT/GMC links are
literature context and possible downstream interfaces, not Lean-proved transports.

## RH pressure test

The exact DA quotient is directly useful for RH proof search as a normalization-cancellation
diagnostic: two HT archimedean observables can differ by no non-DA information at all.  Therefore
HT status alone is not a source producer; orbit charge after quotienting is the invariant to track.
The result does not close a current `RHTower` prime-source, positivity, sign, zero-free, or
off-critical-zero hypothesis.

## Log

- 2026-07-17 — circular beta Selberg normalizer extracted; scaled recurrence, exact Dirichlet
  quotient, full `K=1`/`K>1` boundary, and circuit source extraction formalized and verified.
- 2026-07-17 — density-prefactor inversion relation and its full HT boundary added; generic
  inversion/division transport promoted to the shared HTGeometry API and axiom-audited.
