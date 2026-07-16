# The DA-relative multiple-Gamma characteristic boundary has a periodic logarithmic pair arrangement

- **ID:** `multiple-elliptic-gamma-relative-log-characteristic-arrangement`
- **Stage:** 2-fully-proven / Lean core formalized
- **Type:** THEOREM / RELATIVE CHARACTERISTIC GEOMETRY / UNIFIED-OBSTRUCTION SOURCE OBJECT
- **Scientific status:** `[PAPER PROOF COMPLETE] [LEAN CORE FORMALIZED]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:**
  - `multiple-elliptic-gamma-transverse-constraint-depth.md`
  - `multiple-gamma-effective-fracture-descent-orthogonality.md`
  - `../../3-formalized/gamma-periodic-constraint-corona.md`
  - `../../1-in-progress/hypertranscendental-critical-closure-defect-principle.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/RelativeLogCharacteristicArrangement.lean`

## Statement

For the generic order-`r` multiple elliptic Gamma logarithmic derivative, the exact
DA-relative translation module is

```text
M_r = R_tau / I_r,
I_r = < product_(j in J)(t_j-1) : |J|=r >,
R_tau=C[t_0^(+-1),...,t_r^(+-1)].                         (1)
```

Let

```text
Exp : C^(r+1) -> (C^x)^(r+1),
Exp(lambda)_j=exp(lambda_j),                              (2)
```

and pull the support of `M_r` back through `Exp`.  Its logarithmic characteristic boundary is

```text
LogChar_DA(Psi_r)
 ={lambda : product_(j != i)(exp(lambda_j)-1)=0
              for every i}
 = union_(a != b)
    {lambda : exp(lambda_a)=exp(lambda_b)=1}.             (3)
```

Thus the DA-relative characteristic boundary is a countable periodic arrangement of
codimension-two sheets.  For each coordinate pair `(a,b)`, its sheets are indexed by the two deck
charges in the fibres of the exponential map.  Reflection sends every sheet charge to its
negative, while coordinatewise deck translation preserves the entire arrangement.

For the order-one Gamma shift, the formal cofactor

```text
U_hat(D)=(exp(D)-1)/D                                     (4)
```

is a unit at every finite clock horizon.  Restoring the removable value of its global symbol,

```text
U(0)=1,
U(lambda)=(exp(lambda)-1)/lambda  for lambda != 0,        (5)
```

makes its action on every finite periodic Fourier packet exact:

```text
U(D) sum_(m>=0) a_m exp(2 pi i m z) = a_0.               (6)
```

Hence the source cofactor is not merely a nonunit.  It is the canonical gauge-reduction map:
its image is the constant calibration line and its kernel is precisely the nonconstant periodic
gauge.

## Proof of the arrangement theorem

Put

```text
x_j=exp(lambda_j)-1.                                     (7)
```

The generators of `I_r` are the `r`-fold products obtained by omitting one of the `r+1`
coordinates.  Suppose all these coface products vanish.  Omit any coordinate `i`.  Since the
remaining product is zero over `C`, one factor `x_a` with `a != i` is zero.  Now omit `a`.
The resulting product is again zero, so a second factor `x_b`, necessarily with `b != a`, is
zero.  Conversely, if two distinct factors vanish, every coface product contains at least one of
them.  This proves `(3)`.

If `d` is any coordinatewise deck displacement with `exp(d_j)=1`, then

```text
exp(lambda_j+d_j)=exp(lambda_j),                          (8)
```

so the arrangement is deck invariant.  Also

```text
exp(-lambda_j)=1 iff exp(lambda_j)=1,                     (9)
```

which proves reflection invariance.

Equation `(6)` follows from `(5)`: the zero Fourier mode has frequency zero and multiplier one;
every positive periodic frequency has exponential character one but nonzero frequency, hence
multiplier zero.  `QED`

## What this changes

The exact annihilator theorem produced an algebraic Stanley--Reisner support.  The logarithmic
lift identifies the missing global object:

```text
thin algebraic boundary in translation-character space
    <- infinite deck-labelled clock arrangement
    <- source polarization/orientation on its logarithmic lift.               (10)
```

This gives a precise meaning to

```text
hypertranscendence is infinite algebraic clock capacity
concentrated on a thin constraint boundary.              (11)
```

The boundary is thin because every irreducible sheet has codimension two.  The capacity is
infinite because each algebraic sheet has infinitely many logarithmic deck lifts.  The source
constraint fixes the arrangement; it does not propagate a flow.

The theorem also explains the earlier orientation no-go.  Formal completion at the central clock
uses

```text
exp(lambda_j)-1=lambda_j U_j(lambda_j),
U_j(0)=1.                                                 (12)
```

Each `U_j` is a formal unit, so formal and derived local geometry recovers the same squarefree
Stanley--Reisner scheme on the `lambda_j`.  It cannot retain the global deck label.  Therefore any
invariant which factors only through the algebraic translation character, including its full
derived local topology, is necessarily blind to opposite deck orientations.

The nontrivial positive successor is exact: the missing datum is not another local cohomology
class but the logarithmic lift itself, equivalently the integer deck charge on each resonant
coordinate.  Pointing selects the central sheet; polarization must orient the remaining deck
charges.  This is the smallest enrichment capable of distinguishing a sheet from its reflected
partner.

## Unified-obstruction interpretation `[CONJECTURE]`

> **[CONJECTURE — DA-RELATIVE LOGARITHMIC CHARACTERISTIC PRINCIPLE.]**  For every source-minimal
> constrained hypertranscendental system `F`, its canonical unified obstruction object is the
> polarized logarithmic lift of the support of its translation module modulo DA functions:
>
> ```text
> LogChar_DA(F)=LogLift Supp(R_source / Ann_DA(F)).        (13)
> ```
>
> Spectral incompleteness is nonclosed realization of this lifted support; continuation failure
> is failure to invert its characteristic section; positivity failure is failure to orient its
> self-dual real form; monodromy is its deck action; and noncanonical boundary conditions are the
> residual fibre of logarithmic lifts after pointing.

The conjecture is falsifiable.  It fails if two natural obstruction representations of one
source cannot be functorially recovered from the same relative support, or if an orientation
obstruction survives after the deck-labelled polarized lift is fixed.

For an RH application, no zeta zero is inserted into `(13)`.  A valid application must first
construct `Ann_DA` from the Euler--Gamma--theta source and then show that the existing positivity,
spectral, continuation, and boundary chains are conservative realizations of its logarithmic
support.  The conjecture is not an RH equivalence and supplies no RH conclusion by itself.

## Novelty and anti-theatre gate

### Parent mathematics

- Schwartz--Ehrenpreis mean-periodic theory already relates convolution annihilators, entire
  symbols, and exponential-polynomial spectra.
- Support varieties of modules over Laurent group rings and logarithmic/exponential covers of
  algebraic tori are standard.
- The zero locus of a squarefree Veronese ideal is the union of its coordinate minimal-prime
  components.

Those facts are `[SEARCH]`, not new knowledge.

Primary parent anchors include:

- Berenstein--Taylor, *Mean-periodic functions*,
  `https://doi.org/10.1155/S0161171280000154`;
- Adamczewski--Dreyfus--Hardouin, *Hypertranscendence and linear difference equations*,
  `https://arxiv.org/abs/1910.01874`;
- Dreyfus, *Hypertranscendence and linear difference equations, the exponential case*,
  `https://arxiv.org/abs/2212.00388`.

### Candidate-new residue

The new input is the previously computed special-function theorem

```text
Ann_DA(Psi_r)=I_r,                                       (14)
```

where annihilation means landing in the nonlinear differential-algebraic coefficient sector,
not vanishing in an ordinary linear convolution module.  Combining `(14)` with the logarithmic
clock covering gives the explicit DA-relative arrangement `(3)` and identifies its lost deck
orientation as the exact information absent from the formal/derived fracture object.

Targeted searches found difference-Galois hypertranscendence, mean-periodic spectral synthesis,
Laurent-module support loci, and multiple-elliptic-Gamma hierarchy identities.  No located source
constructs a DA-relative characteristic variety for the multiple elliptic Gamma translation
module, computes its logarithmic pair arrangement, or uses the deck-labelled lift to separate
formal HT freedom from global orientation.  This is preliminary negative evidence, not priority
certification.

### Significance verdict

- The pair-arrangement calculation alone is a direct geometric corollary of `(14)` and is not a
  standalone paper.
- Together with the annihilator theorem it supplies the first source-canonical geometric object
  which simultaneously contains thinness, infinite clock capacity, monodromy, reflection, and
  the local/global unit defect.
- Fields-scale significance remains conditional on proving `(13)` for a natural class and
  transferring a genuinely new theorem between two conservative realizations.

## Lean formalization

`RelativeLogCharacteristicArrangement.lean` proves unconditionally:

1. `cofaceProductsVanish_iff_exists_pair_zero`;
2. `multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair`;
3. reflection invariance;
4. coordinatewise deck invariance;
5. exact blindness of the algebraic clock character to deck translation.

`GammaPeriodicConstraintCorona.lean` additionally proves:

1. the removable-origin completion of the Gamma shift cofactor;
2. its values on all nonnegative periodic Fourier frequencies;
3. exact projection to the constant gauge mode;
4. the exact kernel and surjectivity of this gauge reduction.

The special-function identification `(14)` remains the analytic input of the parent paper theorem;
it is not introduced as a Lean axiom.

## Gates

- [x] relative translation characteristic variety identified
- [x] logarithmic pullback computed exactly
- [x] codimension-two pair-sheet structure proved
- [x] deck invariance proved
- [x] reflection invariance proved
- [x] removable-origin cofactor corrected
- [x] Gamma cofactor gauge reduction proved
- [x] classical mean-periodic parent separated from the DA-relative residue
- [x] external novelty search completed provisionally
- [x] unconditional combinatorial and Gamma gauge cores formalized in Lean
- [ ] independent audit of the parent multiple-Gamma annihilator theorem
- [ ] source-minimal reconstruction theorem for a natural HT class
- [ ] conservative comparison with two independent analytic realizations
