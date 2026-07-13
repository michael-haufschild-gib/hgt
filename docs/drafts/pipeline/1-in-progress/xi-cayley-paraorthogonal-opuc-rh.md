# Xi Cayley--paraorthogonal OPUC coherence and RH

- **ID:** `xi-cayley-paraorthogonal-opuc-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [UNITARY CIRCLE MODEL]`
- **Lean inputs:** `formal/GaloisForLFunctions/HTGeometry/FiniteOPUCRootLocation.lean`,
  `formal/GaloisForLFunctions/HTGeometry/FiniteOPUCReversal.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ParaorthogonalBlaschkeRoot.lean`,
  `formal/GaloisForLFunctions/HTGeometry/BernsteinSzegoReconstruction.lean`,
  `formal/GaloisForLFunctions/HTGeometry/BernsteinSzegoDensity.lean`,
  `formal/GaloisForLFunctions/HTGeometry/BernsteinSzegoMomentForm.lean`,
  `formal/GaloisForLFunctions/HTGeometry/CayleyMomentFrame.lean`, and
  `formal/GaloisForLFunctions/HTGeometry/CayleyUnitCircleReality.lean`
- **Consumer:** the classical Pólya--Jensen characterization of the Laguerre--Pólya class and the
  existing `XiLaguerrePolya.lean` RH interface

## Claim

Every Xi Jensen polynomial has a source-coherent paraorthogonal-polynomial-on-the-unit-circle
realization after Cayley homogenization.  The realizing Toeplitz moments are constructed from the
completed prime--Gamma source before the Jensen roots are inspected.  Paraorthogonal OPUC root
location puts the Cayley-transformed roots on the unit circle; the exact Cayley reality bridge puts
the original roots on the real line.  Hyperbolicity of every Xi Jensen polynomial implies that Xi
is Laguerre--Pólya and proves RH.

## Closed two-ended chain

Let `J_(d,n)(x)` be the degree-`d` Jensen polynomial of the normalized even Xi Taylor sequence.
Define its Cayley homogenization

```text
P_(d,n)(w)=(1-w)^d J_(d,n)(i(1+w)/(1-w)).                (1)
```

The proposed chain is

```text
continued prime--Gamma source at Jensen shift n
  -> Hermitian circle moment sequence c_n : Z -> C
       [OPEN CORE A: source construction and root-blind positivity]
  -> every finite Toeplitz section positive definite
  -> finite OPUC polynomial Phi_(d,n) and reversal Phi*_(d,n)
  -> paraorthogonal terminal polynomial
       Psi_(d,n)(w)=w Phi_(d,n)(w)-tau_n Phi*_(d,n)(w), |tau_n|=1
  -> exact coefficient identity Psi_(d,n)=constant*P_(d,n)
       [OPEN CORE C: source recurrence matches the Xi Jensen coefficients]
  -> every root of P_(d,n) lies on |w|=1
  -> every root of J_(d,n) is real by Cayley transport
  -> every Xi Jensen polynomial is hyperbolic
  -> Xi belongs to the Laguerre--Pólya class
  -> every centered Xi zero is real
  -> RH.
```

The final transport is already formalized:

```text
|(z-i)/(z+i)|=1  <->  Im(z)=0.
```

The corpus proves that finite OPUC roots lie strictly inside the disk and that their reversed
polynomials have no zeros on the closed disk.  It now also proves the exact conjugate-reversal root
product, the generic paraorthogonal polynomial theorem, and the concrete finite-OPUC corollary:
for every positive-definite Toeplitz section and every unimodular terminal parameter, every root of
`w Phi-tau Phi*` lies on the unit circle.  Thus the entire finite OPUC/reversal/root-location
interface is closed; the remaining load is the source-coherent arithmetic coefficient identity.

## Why paraorthogonal, not ordinary OPUC

Ordinary OPUC zeros lie strictly inside the unit disk.  Under inverse Cayley transform they lie in
one open half-plane, not on the real line.  The terminal unimodular boundary condition is therefore
load-bearing: the paraorthogonal combination moves the spectrum from a contraction to a unitary
finite CMV truncation and puts its roots on the circle.

This is the positive statement extracted from the ordinary-OPUC no-go.  The strict disk theorem is
not a failed approximation to RH; it identifies the exact missing boundary operation.

## Source producer candidates

1. **Prime--Gamma contour moments.**  Pull the finite Hermite contour functional through the
   Cayley map and read its reciprocal moments at `-i`.  `CayleyMomentFrame.lean` proves the exact
   triangular equivalence between reciprocal-moment and circle-moment prefixes.
2. **Theta density pushforward.**  Push the positive theta-cusp density through a source-prescribed
   real coordinate and Cayley map.  This gives positive Toeplitz sections automatically; the hard
   comparison is then `(1)`.
3. **Bernstein--Szego finite reconstruction.**  Construct a source outer polynomial first, use its
   reciprocal-square circle density, and prove that the associated terminal POPUC polynomial is
   `(1)`.  The corpus already contains exact finite Bernstein--Szego orthogonality and prefix
   reconstruction.
4. **CMV/prime incidence.**  Treat the Verblunsky coefficients as local reflection amplitudes of
   a prime--Gamma scattering chain.  The source theorem must prove `|alpha_k|<1`; the final
   unimodular parameter is supplied by functional-equation reflection.

## Hard no-go tests and positive statements

1. **Independent finite fitting is circular.**  Every finite unit-circle root set can be packaged
   as a paraorthogonal polynomial after the roots are known.
   **Positive statement:** the circle moments and Verblunsky coefficients must be computed from one
   source recursion before root localization, and prefixes must agree under aperture growth.
2. **Self-inversive is insufficient.**  A self-inversive polynomial can have reciprocal pairs off
   the unit circle.
   **Positive statement:** Toeplitz positive definiteness plus strict Schur parameters and one
   unimodular terminal parameter are the maximal finite hypotheses that force the circle theorem.
3. **Ordinary OPUC is on the wrong locus.**  Its roots are strictly inside the disk.
   **Positive statement:** use the paraorthogonal terminal combination, not the orthogonal
   polynomial itself.
4. **Target-defined Herglotz measure is a mirror.**  The atomic measure on Cayley images of Xi zeros
   already contains RH-strength divisor data.
   **Positive statement:** use a theta/prime--Gamma pushforward or contour moment sequence whose
   definition contains no Xi zero.
5. **Toeplitz positivity alone is RH-blind.**  Any positive circle measure supplies it.
   **Positive statement:** the exact coefficient identity with every Cayley-homogenized Xi Jensen
   polynomial is the arithmetic load-bearing theorem.
6. **One fixed finite degree is insufficient.**  Eventual fixed-degree Jensen hyperbolicity is
   already known and does not imply RH.
   **Positive statement:** require a coherent two-parameter family for every degree and every
   Taylor shift, or an equivalent cofinal theorem that covers the finite exceptional region.

## Complete-selector detour and source-producer audit

The complete Cayley/OPUC selector is already closed in Lean.  For probability measures on the real
line, equality of all Cayley moments determines the measure; equality of the complete Toeplitz Gram
tower or of every canonical inverse-Cholesky frame therefore determines the same measure.  Finite
Cayley prefixes are exactly finite regular Cauchy jets at `-i`.  Consequently the indeterminate
Hamburger-moment fiber is not an obstruction once a candidate carrier is given in all-order
Cauchy/Cayley coordinates.

This closes a selector, not a producer.  Four source constructions have different failures:

1. A positive theta-density pushforward gives strict Toeplitz positivity without locating any Xi
   root.  The missing coefficient identity with the Cayley-homogenized Jensen polynomials remains
   the entire arithmetic load.
2. The normalized Xi logarithmic-derivative germ supplies the correct Schur coefficients, but
   positivity of all finite Pick/Toeplitz sections is already equivalent to RH.  Its singular
   atomic carrier and Bernstein--Szego condensation are positive consequences of that positivity,
   not independent inputs.
3. The positive Sonin residual energies give genuine source-defined Hankel moment sequences.  A
   cofinal aperture family whose moments converge to the prime--Gamma moment germ already proves RH
   through `riemannHypothesis_of_soninPrimeArchSingleMomentCoupling`.  Passing those measures through
   Cayley compactifies the family and selects subsequential carriers, but compactness alone does not
   identify a cluster carrier with the prime--Gamma germ.  The positive residue is that OPUC can
   make a proved Sonin moment weld canonical; it cannot prove the weld.
4. A representing measure for all normalized prime--archimedean power moments immediately yields
   RH through `riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation`.  Its Cayley
   pushforward also yields every finite paraorthogonal unitary truncation.  This gives a coherent
   OPUC realization after the measure is constructed, but does not weaken the measure-existence
   theorem.

Thus the strongest surviving use of this detour is

```text
source-defined positive cofinal carrier family
  -> independently prove its all-order Cauchy or power-moment weld to the prime--Gamma germ
  -> complete Cayley/frame selector makes the limiting carrier canonical
  -> finite paraorthogonal unitary truncations at every level
  -> prime--archimedean moment positivity
  -> RH.
```

The load-bearing open theorem is the source weld in the second arrow.  Neither OPUC root location,
weak compactness, nor complete-frame determinacy supplies it.  This is the positive statement of
the no-go: any successful OPUC proof must enter through a source theorem that identifies a positive
carrier before the Xi divisor is read; after that theorem, the corpus already closes selection,
finite unitary geometry, and the RH consumer.

## Exact open cores

- `[CLOSED SELECTOR]` Complete Cayley moments, regular Cauchy jets, Toeplitz Gram towers, and canonical
  inverse-Cholesky frame towers select the underlying probability measure uniquely.
- `[OPEN CORE A]` Construct a source-positive carrier for every Jensen shift and prove, independently
  of the Xi divisor, that its all-order Cauchy/Cayley data are the required source moments.
- `[CLOSED FINITE BRIDGE]` `finiteOPUCPolynomial`, its conjugate reversal, and its paraorthogonal
  terminal polynomial are connected to the unit-circle root theorem in Lean.
- `[OPEN CORE C]` Prove the source CMV/Verblunsky recurrence gives the coefficients in `(1)` at every
  degree and shift.
- `[OPEN CORE D]` Formalize the Jensen-polynomial/Laguerre--Pólya consumer and compose it with the
  existing Xi/RH endpoint.

## Kill conditions

Retire the chain if the moment sequence is reconstructed from Xi roots; if source Toeplitz
positivity is merely assumed; if the coefficient comparison holds only after degree-dependent
moment refitting; if the terminal parameter is not unimodular; or if only eventual fixed-degree
hyperbolicity is obtained.  Preserve any source-built coherent Schur prefix, explicit Verblunsky
bound, or maximal degree range as the positive statement.

## Gates

- [x] unit-circle/reality Cayley endpoint formalized
- [x] ordinary OPUC strict-disk and reversed zero-free inputs present in Lean
- [x] finite Bernstein--Szego reconstruction inputs present in Lean
- [x] both-end POPUC-to-RH chain specified
- [x] factorized paraorthogonal Blaschke unit-circle theorem formalized
- [x] finite OPUC polynomial/reversal connected to the paraorthogonal root theorem
- [x] complete Cayley/Cauchy/frame selector and measure uniqueness formalized
- [x] theta, Xi-Schur, singular-carrier, and Sonin producer variants attacked
- [ ] source moment/Verblunsky family constructed
- [ ] all-degree coefficient comparison proved
- [ ] Jensen/Laguerre--Pólya/RH capstone composed in Lean
