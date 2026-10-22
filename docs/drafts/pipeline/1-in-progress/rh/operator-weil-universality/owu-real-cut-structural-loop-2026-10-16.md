# OWU structural loop after automatic slit continuation

Status: unresolved investigation; no new theorem or frontier advance claimed.
Objective: one further structural contribution to OWU,
with no extra unproved producer premise, bound-only conclusion, or RH receiver.

## Plan

1. Read current Lean sources and search across the corpus for the actual frontier.
2. Attack competing conjectures about the real spectral branch and odd null tests.
3. Complete an exact paper proof before formalization.
4. Audit individual leaves, axioms, imports and lint; clean owned scratch files.

## Starting facts checked in Lean source

- `OddWeilPickContinuation.exists_weilFunction_slit_continuation` produces
  holomorphy on `Re s > 1/2` off the real segment `(1/2,1]` from the defining
  odd-positivity predicate alone.
- `EvenSectorPoleWeightUniqueness.source_unique_of_weilPositiveEvenAt`
  now identifies every source in any finite even pole cone. Its signed
  detuned-packet construction solves a convergence obstruction, while
  cosine covariance excludes the double-pole branch.
- Odd spectral division by `z²` reverses sign on the imaginary segment.
  Neither even source uniqueness nor full-cone null certificates transfer
  automatically.

## Competing conjectures

1. Arithmetic discreteness removes the real cut in the automatic odd
   continuation. Open core: identify a structural restriction on its
   positive squared-variable spectral measure which excludes that branch.
2. An Xi-divisible odd covariance can be made prime-blind by imposing
   higher-order arithmetic zeros on the existing Gamma covariance.
   Open core: maintain positivity and Xi divisibility simultaneously.

Only current Lean source and corpus-search evidence are used. No external
search, old research-note reading, numerical experiment, or novelty audit.

## Conjecture attacks and exact gaps

- **Transfer the even uniqueness proof.** Fails at spectral division by
  `z²`: on `z = iy`, this reverses sign. The new even-cone theorem does
  not supply the missing even positivity of an odd-positive source.
- **Use saturation of the pole-weight ceiling.** The far-bump lower
  identity and logarithmic-density ceiling address the leading residue
  at `s = 1`. They do not establish removability of a cut, including a
  nonatomic cut approaching that endpoint. No removal theorem follows
  from residue cancellation alone.
- **Project the Gamma null family to odd tests.** The original diagonal
  covariance is prime-blind. Odd projection introduces a cross-reflection
  covariance; its arithmetic values are not cancelled by the existing
  identity. It cannot be silently discarded.
- **Add a zero at the strip edge by a hyperbolic dilation filter.**
  `ModularArcDyadicInversionDuality` identifies the defect exactly:
  the backward dilation retains only sublattice blindness. Forward
  recentering restores all-integer blindness but moves the inversion
  center and the center of spectral positivity. This does not produce
  the simultaneous identities needed for an odd Weil null covariance.
- **Use the boundary member of the twist family.** In
  `TwistedArcFamilyN1Reduction`, the parameter `a = 1/4` gives the
  spectral factor `τ²(1/4 + τ²)`. It has the desired central zero,
  but supplies only one strip-edge factor; the Xi-divisible transfer
  needs the squared factor. The family annihilating measure is also an
  input in that file. Neither obligation was proved here.
- **Repair mass with the two-arc witness.**
  `ModularTwoArcWitnessMass.exists_twoArcWitness_mass` is an
  unconditional positive-mass construction. A positive multiple
  repairs mass but adds positive central spectral value, destroying
  the central zero. Earlier reasoning that this positive-mass witness
  was itself missing was incorrect and was discarded after reading
  the actual declaration.
- **Use odd exposing-ray sources.**
  `WeilWorkExposingRayCriticalOddSource` supplies an exact complementary
  covariance with a shorter residual. It explicitly does not supply
  positivity or smallness of the residual. Those are still necessary;
  the identity alone does not yield a null test.

## Remaining concrete conjecture

Construct a nonzero prime-blind positive covariance of actual odd tests
whose spectral factors are Xi-divisible, with the necessary strip decay
and pole control proved. A formal receiver assuming this covariance would
not meet the requested contribution.

A more specific, unformalized lead is a shifted Legendre running-mean
kernel for the family operator `L(L-a)`, `a > 0`, where
`L f = ((1-c²) f')'`. Let `p` solve `L p = a p`, `p(0)=1`, `p'(0)=0`,
and put `P(c)=∫₀ᶜ p`. The proposed clamped kernel solves
`(L-a) k = 1/P(b) - 1_[0,c]/P(c)` on `[0,b]`, with `b=1/2`.
The weighted Wronskian suggests `k ≥ 0` and the identity
`∫ L(L-a)f · k = G(b)/P(b) - G(c)/P(c)`, `G=(1-c²)f'`.
This may extend the existing stream minimum-principle argument to the
twist family. Existence, boundary identities, and transfer to the exact
arc moments still require proof. Even a completed family minimum
principle would not by itself resolve the missing second strip-edge
factor identified above.

## Verification and ownership

No Lean source was added or changed in this investigation. No Lean build,
axiom audit, or umbrella build was run, and no compilation result is
claimed. Search hits were inspected in current source; source inspection
was not treated as a fresh compiler audit. Owned search-result scratch
files were removed. Other ongoing work in the shared tree was preserved.
