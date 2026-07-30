# Riemann bifiltered source-ancestry purity

- **ID:** `riemann-bifiltered-source-ancestry-purity`
- **Stage:** 5-failed
- **Type:** RETIRED SYNTHESIS / DUPLICATE HYPER-TOR DETECTOR / NOT A PRODUCER
- **Scientific status:** `[CORPUS COLLISION] [NO-GO RETAINED] [ROUTE RETIRED] [NOT RH]`
- **No positivity premise:** Native coefficient positivity, positive forms, orientation signs, and
  positive generalized-prime models are falsifiers, not inputs.
- **Concrete parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/source-face-observation-cohomology-transmutation.md`;
  - `../3-formalized/normal-crossing-derived-critical-base-change-defect.md`;
  - `polarized-critical-rees-corona-transgression-rh.md`;
  - `../4-publication-ready/source-horizon-riemann-divisor/main.tex`;
  - `../3-formalized/squarefree-fixed-current-right-half-ward-localization.md`;
  - `../3-formalized/hedenmalm-divisor-metric-dense-radical-no-go.md`;
  - `singular-euler-source-divisor-incidence-law.md`;
  - `formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean`;
  - `formal/GaloisForLFunctions/RHTower/XiWoldPoissonBivariateConormal.lean`.

## 1. Correction forced by the corpus

The missing Xi class cannot be created by an exact completion of the prime-winning source
contraction.  Let `C_obs=[M -> N]` be a source observation complex and let `B` be a source face.
Derived specialization is exact, so

```text
homotopyFiber(f) tensor^L B
  = homotopyFiber(f tensor^L B).                         (1)
```

Therefore every proposed “derived rigidification--specialization commutator” is zero.  If the
source complex is contractible and the completion preserves its contraction strictly, its derived
specialization remains contractible.  It cannot simultaneously acquire a nonzero Xi conormal.

The source-face theorem supplies the only compatible birth mechanism:

```text
0 -> H^(-1)(C_obs) tensor B
  -> H^(-1)(C_obs tensor^L B)
  -> Tor_1(H^0(C_obs),B) -> 0.                           (2)
```

Thus a new boundary kernel class is not created from nothing.  It is an ancestral generic
attainment defect in `H^0` which changes observed degree under ordinary cohomology/truncation.
The hyper-Tor filtration remembers that ancestry.

`[PROVED CORPUS CONSEQUENCE]`

> Any RH route demanding both strict preservation of the source Čech contraction and creation of a
> nonzero Xi conormal in the same exact realization is impossible.  A surviving Xi class must be
> the edge image of a pre-existing attainment defect under a non-exact boundary-value,
> domain, topology, or truncation functor.

This also explains the Hedenmalm dense-radical theorem.  Ordinary `L²` completion sees the
theta-null radical as dense and gives the zero quotient seminorm.  A nonzero divisor class can
survive only in a boundary functor singular to ordinary `L²`; closable Hilbert completion is the
wrong category.

## 2. The two clocks and the missing ancestry datum

For a nontrivial Xi zero `rho`, put

```text
nu_rho=2 Re(rho)-1.
```

The source-horizon theorem gives an all-jet Poisson mode with exact mass growth

```text
exp(nu_rho tau).                                         (3)
```

The ordinary-prime Wold shell theorem gives the opposite normalized likelihood rate

```text
|H_n(rho)|^2/h_n
  =C_rho exp(-nu_rho n log 2)(1+o(1)),                  (4)
```

where `C_rho>0`.  Their product is conservative on the characteristic diagonal
`tau=n log 2`, even when `rho` is off line.  Hence every one-clock or diagonal completion is
provably blind.

The two rates are not two unrelated estimates.  They are the two filtration weights of one
candidate ancestral class:

```text
Poisson/source-time weight = +nu_rho,
Wold/source-depth weight    = -nu_rho.                   (5)
```

Endpoint divisor order, reflection parity, and seam multiplicity forget `(5)`.  This is why they
cannot distinguish a genuine critical-line zero from a deposited pair-collision residue.  The
hyper-Tor filtration can: it records the source degree from which the endpoint class arrived.

## 3. Universal interpretation

> **Spectral location is ancestry weight.**  In a singular analytic continuation, a divisor point
> is not merely an endpoint zero.  It is a filtered boundary class descended from a specific
> source attainment defect.  Its displacement from the self-dual line is the imbalance between
> two independent source-filtration weights.  Functional equation exchanges the filtrations;
> arithmetic purity means that the same ancestral class, not a second reflected class, is fixed by
> that exchange.

This reinterprets the corpus shadows:

```text
finite Čech contraction
  = exact source resolution before boundary truncation;

source-face Tor
  = degree transmutation retaining ancestry;

source-horizon Lyapunov rate
  = first filtration weight;

Wold shell escape rate
  = opposite filtration weight;

duality-versus-adjunction fracture
  = failure to identify filtration exchange with the dagger on one class;

continuous-spectrum loss
  = forgetting the Tor edge class in an exact ambient completion;

Hedenmalm dense radical
  = collapse of ancestry under ordinary L² closure;

off-line generalized-prime systems
  = systems where reflection supplies two complementary boundary classes rather than one pure
    ancestral class.
```

Positivity is absent.  The selector is whether reflection acts internally on one source-ancestral
class or externally pairs two independently born classes.

## 4. Riemann source-ancestry purity conjecture

`[BOLD CONJECTURE] [XI_BIFILTERED_ANCESTRY_PURITY]`

There is a source-defined two-term or perfect observation complex `C_Xi` over the independent
ordinary-prime Wold-depth and Poisson-time parameter ring, constructed before choosing a zero,
with the following properties.

1. **Generic source identification.**  `H^0(C_Xi)` is the completed Euler--Gamma/co-Poisson
   attainment module represented off divisor by
   `xiWoldPoissonBivariateConormalResponse`.
2. **Boundary transmutation.**  At Xi Cartier specialization, every top principal-conormal jet is
   the nonzero edge image of one class in

   ```text
   Tor_1(H^0(C_Xi),B_Xi).                               (6)
   ```

   No conormal is postulated in the generic kernel.
3. **Bifiltration faithfulness.**  The hyper-Tor spectral-sequence filtration survives the
   singular Gamma/co-Poisson boundary functor and retains the two independent weights `(5)`.
4. **Internal reflection.**  Riemann reflection exchanges the two filtrations on the same
   ancestral Tor class and agrees there with the source dagger.  It does not create an independent
   anti-source class.
5. **Purity.**  The Tor edge class is fixed under that filtered exchange.  Equivalently, its two
   filtration weights agree.

By `(5)`, clauses 4--5 give

```text
nu_rho=-nu_rho,
```

so `nu_rho=0` and `Re(rho)=1/2` for every nontrivial Xi zero.  This proves RH.

The conjecture is not the statement that a chosen zero is bounded in two norms.  It constructs one
pre-divisor observation complex, identifies the generic ancestor, and requires filtered
reflection on the resulting Tor edge class.

## 5. Concrete construction target

`[OPEN CORE] [XI_WOLD_POISSON_HYPERTOR_EDGE_IDENTIFICATION]`

Construct `C_Xi` from the existing literal data:

```text
prime-winning augmented Čech resolution
  + Wold maximum-exponent shell augmentation
  + Euler--Gamma logarithmic source
  + co-Poisson/Sonin boundary comparison
  + squarefree overlap multiplication graph.             (7)
```

Then prove:

1. its generic `H^0` contains the exact bivariate response already formalized;
2. the squarefree-overlap range defect is the same `H^0` class, not a scalar quotient introduced
   after continuation;
3. its Xi-face hyper-Tor edge map equals the principal conormal residue, with all jets;
4. Poisson time and Wold depth act on the filtered complex before specialization;
5. Gamma reflection exchanges those actions at chain level;
6. the edge class is one internally reflected class rather than a direct sum of two orbit classes.

Clause 6 is the load-bearing arithmetic theorem.  The earlier reflection-Tate left inverse and
“internal reflection rank noncreation” are terminal consequences of it, not substitutes for its
construction.

## 6. Kill tests

1. **Exactness kill.**  If `C_Xi` is replaced by a contractible complex and exact base change, the
   boundary class is zero.  Reject the construction.
2. **Endpoint kill.**  If the proposed invariant depends only on divisor order, parity,
   functional equation, or endpoint seam data, the explicit pair-deposit model refutes it.
3. **Diagonal kill.**  If the topology identifies `tau` with `n log 2`, equation `(4)` makes every
   off-line mode conservative.  Reject it.
4. **Two-class kill.**  If reflection sends the Tor class to an independent complementary class,
   weights `+nu` and `-nu` coexist without contradiction.  No RH consequence remains.
5. **Positivity kill.**  Native positive finite sources converge at divisor-retaining inverse
   depth to the mixed-sign Möbius boundary.  No coefficientwise positive or positive-form descent
   may be assumed.
6. **Target-fed kill.**  Defining the complex, filtration, norm, or edge map after enumerating Xi
   zeros is circular.
7. **Generalized-prime kill.**  If an explicit off-line generalized-prime Euler system satisfies
   all six construction clauses with the literal ordinary-prime source replaced verbatim, the
   conjecture is false.
8. **Literature collision kill.**  General hyper-Tor, excess intersection, Hodge purity, and
   filtered duality are parent mathematics.  Candidate novelty is only the concrete
   ordinary-prime Euler--Gamma/co-Poisson identification `(7)` and its internal-reflection edge
   theorem.

## 7. Current status

The following pieces are already unconditional:

- source-face kernel/attainment/Tor transmutation;
- rank-two filtration and scalarization no-go;
- source-horizon all-jet growth;
- Wold--Poisson two-clock reciprocity;
- off-divisor bivariate arithmetic response and residue transport;
- squarefree overlap/fixed-current quotient identity;
- Xi source normal-cone divisor and affine-current conservation;
- Hedenmalm ordinary-`L²` dense-radical/nonclosability obstruction.

No current corpus theorem constructs the complex `(7)`, identifies its Xi hyper-Tor edge, or
proves internal filtered reflection of that edge.  RH remains open at precisely those clauses.

## 8. Hostile corpus verdict

This route is retired as an independent RH mechanism.

1. The boundary-birth statement is the existing source-face observation transmutation law.
2. Relative purity of its attainment `Tor_1` is already
   `SOURCE_EFFECTIVE_PURE_REVERSE_LAW` /
   `XI_DAGGER_COMPARISON_REDUCED_TOR_INDEPENDENCE`.
3. Requiring reflection to act on one ancestral class rather than two is already
   `XI_INTERNAL_REFLECTION_RANK_NONCREATION`.
4. The newly formalized least-atom shell law proves a nonzero two-clock traveling-wave profile
   for every `Re rho > 0`, including off-line points.  The abstract full-quadrant boundedness
   criterion is equivalent to vanishing transverse rate, but the arithmetic source does not
   provide that boundedness.
5. Putting the known rates `+nu_rho` and `-nu_rho` on a conjectural hyper-Tor filtration does not
   produce purity.  Declaring the same edge class fixed under filtered exchange is the missing
   RH assertion in renamed form.

The only positive survivor is the representation correction in Section 1: exact derived base
change cannot both preserve a source contraction and create a nonzero Xi conormal.  Any viable
construction must use an ordinary-cohomology, domain, topology, or boundary-value non-exactness,
and must prove its source-specific control rather than call that control ancestry purity.

No separate open core remains on this card.  The literal source-side problem stays where the
corpus already placed it: construct the Gamma/co-Poisson/Sonin boundary comparison and prove a
non-circular cofinal control theorem on its independently retained Wold--Poisson quadrant.
