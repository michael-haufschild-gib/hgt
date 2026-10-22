# The CCM--Sonin source has a forced three-grade principal--relative carrier

- **ID:** `ccm-sonin-three-grade-relative-carrier-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CORPUS SYNTHESIS, `[BRIDGE]`
- **Scientific status:** `[PROVED FROM FORMALIZED COMPONENTS] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`
- **Parent results:** the Sonin Calkin shell laws, Sonin relative-Gram factorization, all-prime
  residual assembly, semilocal relative trace, and the signed-Gamma orbit-charge dichotomy
- **Statement:** In the canonical Sonin principal/residual decomposition, the source data occupy
  three different operator-ideal grades: a noncompact principal Calkin symbol, a Hilbert--Schmidt
  linear relative cross, and a positive trace-class quadratic residual. The prime-character
  quotient lives in the principal grade, while the unsquared logarithmic Euler coefficient lives
  in the relative grade. Consequently a successful CCM construction is forced to use a closed
  principal--relative extension coupling all three grades; no one grade can carry the exact source.

## One-place decomposition

Fix a Sonin aperture `a>0` and a scale `r>1`. Let `P_(a,r)` be the formal principal lower corner
and let

```text
R_(a,r)=L_(a,r)-P_(a,r)                                   (1)
```

be the exact principal-subtracted Sonin residual. For a logarithmic Euler coefficient `c`, put

```text
D_(a,r,c)=P_(a,r)+c R_(a,r).                              (2)
```

The formalized relative-Gram identity is

```text
D^*D-P^*P
 =c P^*R+conjugate(c) R^*P+|c|^2 R^*R.                   (3)
```

The three grades in `(3)` have different exact types.

### Grade zero: principal Calkin symbol

The unsmoothed lower corner has a nonzero Calkin image. Its Gram entries are partial isometries
whose initial and final projections are explicit two-polarization shells. For distinct finite
prime families, every nonzero matrix combination of the quadratic corners remains noncompact.
Thus the principal grade carries a faithful finite prime matrix algebra modulo compacts.

At cutoff `N`, this grade contains the operator copy of

```text
A_N=V_N/(V_N intersection D),
V_N=span_Q{log p:p<=N},                                   (4)
```

from `ccm-compressed-prime-shift-arithmetic-complement-law.md`. The signed-Gamma completion cannot
replace this quotient.

### Grade one: relative Hilbert--Schmidt cross

The linear term

```text
X_(a,r,c)=c P^*R+conjugate(c)R^*P                         (5)
```

is self-adjoint and Hilbert--Schmidt. Crucially, it depends linearly on `c`. At every prime power,
the formalized specialization exposes the exact unsquared logarithmic Euler coefficient in `(5)`;
coefficient squaring occurs only in the next grade.

This is the only grade in the canonical decomposition with the correct linear arithmetic
dependence for the logarithmic derivative and the semilocal explicit formula.

### Grade two: positive trace-class energy

The quadratic term

```text
Y_(a,r,c)=|c|^2 R^*R                                     (6)
```

is positive and trace class. After deleting the exponent-one principal shell, the prime-power
coefficients are square-summable. The formal all-prime residual operator is Hilbert--Schmidt and
its energy `K_a^*K_a` is a positive trace-class operator. Its polynomial probe functional is
unconditionally nonnegative.

## All-prime separation theorem

The three grades cannot be collapsed into one ordinary ideal.

1. The exponent-one principal energy is the divergent prime-harmonic series

   ```text
   sum_p 1/p=infinity.                                    (7)
   ```

   Formalized Calkin lower bounds show that canonical finite positive-Euler sums become unbounded
   modulo compacts. Therefore grade zero cannot be assembled as a compact, Hilbert--Schmidt, or
   trace-class all-prime correction.

2. The exponent-at-least-two residual tail is square-summable and gives the positive all-prime
   grade-two operator. But residual block orthogonalization deletes the principal mode and mixed
   prime words, while `R^*R` squares the Euler coefficient. Therefore the positive residual Gram
   is not the completed logarithmic source.

3. Grade one restores the unsquared coefficient, including the exponent-one shell, but a general
   Hilbert--Schmidt operator has no canonical operator trace. Pairing the cross with the exact
   Hilbert--Schmidt Sonin projection correction produces a legitimate trace-class scalar, but the
   corpus proves that its geometric response is uniformly bounded and therefore cannot equal the
   required unbounded orbital length `log(p^m)`.

These are theorems, not implementation preferences. Hence the exact source must remain a relative
object retaining all three grades simultaneously.

## Positive carrier law

Within the canonical Sonin/CCM architecture, every successful source construction must carry

```text
principal Calkin shell and A_N
  + a degree-one relative functional with the exact log(p^m) response
    (polarized leakage cross plus any nonzero trace-defect cocycle)
  + positive trace-class residual energy
  + the finite signed-Gamma alien-charge channel.          (8)
```

The principal arithmetic term must remain channel-resolved through the positive factorization.
`ccm-coherent-euler-logarithm-square-exclusion-law.md` proves that coherently summing the Euler
logarithm and then completing one square creates exponentially large prime--prime boundary energy
even on a packet whose actual prime commutator form is zero. Hence the completed carrier must either
separate the prime directions before squaring or retain an exact operator-valued covariance which
cancels those off-diagonal terms.

Nor can singular finite-state dynamics absorb the channel count for free. If an autonomous
implicit ADE carrier retains all rates through cutoff `N`, then

```text
kappa(P_N)>=ceil(pi(N)/2),                                (8a)
```

by `singular-autonomous-ade-kolchin-frequency-law.md`. Thus the positive alternatives are a
cofinally growing jet variety or an explicitly infinite-dimensional/nonautonomous carrier such as
the principal--relative Sonin extension itself.

Equivalently, it must construct a closed extension or graph carrier `E_a` with

```text
S_2 subset E_a -> principal Calkin symbol algebra,         (9)
```

together with a source-defined relative trace/cocycle on its degree-one cross. The notation `(9)`
records the ideal filtration, not a claim that every compact operator lies in `S_2` or that the
extension is already constructed.

The existing Connes semilocal trace formula supplies the correct orbital logarithmic functional.
The existing Sonin formalization supplies the principal symbol and the residual ideal. The live
construction is their compatibility on one closed carrier, not another scalar normalization of
the bounded projection-correction pairing.

`critical-euler-position-commutator-carrier-law.md` supplies the degree-one generator before Sonin
compression. If `X_A` is logarithmic position and `T_(A,h)` the compressed weighted shift, then

```text
[X_A,T_(A,h)]=h T_(A,h),
Z_A=sum_(n<e^A) Lambda(n)/(n log n)(T_(A,log n)-T_(A,log n)^*),
[X_A,Z_A]=sum_(n<e^A)Lambda(n)/n(T_(A,log n)+T_(A,log n)^*). (9a)
```

Thus the unsquared coefficient and the orbital length already coexist in an exact operator. The
remaining degree-one construction is specifically the closed transport of `(9a)` through the
Sonin principal--relative extension, together with the Burnol archimedean conductor.

The ambient logarithmic transport is already exact. Conjugating by multiplication with
`e^(-x/2)` sends the weighted shift to `e^(h/2)` times ordinary translation. Hence the `p^k` term
of the skew Euler logarithm has coefficient `1/(k p^(k/2))`, exactly the coefficient used by the
formalized semilocal Sonin logarithmic metric. The unresolved transport is therefore only the
passage through the true two-constraint Sonin projection and its Hilbert--Schmidt correction.

The projection algebra itself is also closed. For the exact Sonin projection `Q`, define

```text
L_X=(1-Q)XQ,
L_Z=(1-Q)ZQ.                                              (9b)
```

Then

```text
Q[X,Z]Q=[QXQ,QZQ]+L_X^*L_Z+L_Z^*L_X.                    (9c)
```

For an ordinary trace on a trace-class internal corner, cyclicity kills the internal commutator and
leaves precisely the polarized position/Euler leakage cross. For a renormalized trace this is an
extra analytic statement. In general the degree-one term splits as

```text
Def_tau(QXQ,QZQ)+tau(L_X^*L_Z+L_Z^*L_X).                    (9d)
```

The remaining construction is analytic rather than algebraic: a common closed graph, the correct
semilocal relative trace on the pair in `(9d)`, and a positive square or contraction after the
Gamma conductor is included.

## CCM contraction interface

Let `F_(+,a)` and `F_(-,a)` be feature maps on the completed carrier `(8)` such that the true
finite-aperture completed form satisfies

```text
QW_a(f,f)=||F_(+,a)f||^2-||F_(-,a)f||^2.                 (10)
```

The positive theorem forced by the corpus is the construction of contractions `C_a` with

```text
F_(-,a)=C_a F_(+,a),
||C_a||<=1,                                               (11)
```

subject to all of the following source conditions:

1. the induced principal-symbol map is injective on every quotient `A_N` with `log N<a`;
2. the degree-one component is the genuine semilocal logarithmic trace, including any nonzero
   internal trace-defect cocycle, not the disproved bounded scalarization;
3. the degree-two component agrees with the formalized positive all-prime residual energy;
4. the family is compatible with aperture compression and transports inertia to Suzuki's compact
   screw operator `G_a`;
5. the construction is cofinal and closed in the relevant form topology.

If `(10)`--`(11)` are constructed unconditionally for every aperture, then the negative CCM Morse
charge is zero at every aperture and RH follows. Equations `(8)`--`(11)` do not assume RH; they name
the exact source carrier and the remaining theorem.

## What the corpus already supplies

The following components are unconditional and formalized in Lean:

- exact aperture correlation cutoff:
  `intervalShiftCorrelation_eq_zero`,
  `logApertureDilationCorrelation_eq_zero`;
- principal Calkin shell partial isometries and finite matrix faithfulness:
  `evenCentralSoninQuadraticCorner_isCalkinPartialIsometry`,
  `finitePrimeEvenDilationGram_isCompactOperator_iff`,
  `finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero`;
- all-prime Calkin growth and the weighted `l2(1/p)` necessity:
  `finiteEulerCoefficientL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact`,
  `summable_primeEulerCoefficientEnergy_of_uniform_sub_compact_bound`;
- the relative ideal tower:
  `centralSoninRelativeGramDefect_eq_linearCross_add_energy`,
  `centralSoninRelativeGramLinearCross_isHilbertSchmidt`,
  `centralSoninWeightedRelativeGramDefect_eq`;
- the positive all-prime residual:
  `soninAllPrimeResidualOperator_isHilbertSchmidt`,
  `soninAllPrimeResidualEnergyOperator_isTraceClass`,
  `soninCanonicalAllPrimeResidualEnergyOperator_re_inner_nonneg`;
- exact unsquared semilocal coefficient exposure:
  `centralSoninSemilocalRelativeGramLinearCross_eq_coefficient_smul`;
- abstract Krein/index readers:
  `kreinNonneg_iff_no_negDef`, `exact_neg_inertia`.

Thus the remaining mathematical work is not basic Hilbert--Schmidt assembly, prime faithfulness,
finite index algebra, or aperture cutoff. It is the source-defined degree-one relative functional,
the closed contraction `(11)`, and its index-preserving CCM transport.

## Scientific classification

The three-grade synthesis follows directly from already formalized operator identities and ideal
membership theorems. It is a bridge, not new scientific knowledge. Its significance is route
selection: it replaces the collection of negative results by the precise positive carrier a proof
is forced to construct.

## Lean decision

Every substantive component listed above is already in Lean. Adding a record that bundles them
would be wrapper work and would not formalize `(11)`. No new Lean file is added until the genuine
relative carrier or contraction is constructed.

## Gates

- [x] principal Calkin grade and prime faithfulness identified
- [x] linear Hilbert--Schmidt relative grade identified
- [x] positive trace-class residual grade identified
- [x] all-prime separation of the three grades proved from the corpus
- [x] signed-Gamma arithmetic complement attached
- [x] exact existing Lean endpoints inventoried
- [x] finite-aperture degree-one position commutator constructed
- [x] ambient weighted-shift/semilocal-log transport proved
- [x] exact projection-compressed degree-one Gram identity proved
- [x] trace-defect/leakage alternative isolated
- [x] coherent-square exclusion and singular jet-capacity floor attached
- [ ] construct the closed principal--relative carrier `E_a`
- [ ] construct the genuine degree-one semilocal relative functional and trace-defect cocycle on `E_a`
- [ ] construct the cofinal contractions `C_a`
- [ ] prove index-preserving transport to `G_a`
- [ ] invoke aperture Morse-charge conservation to prove RH

## Connes finite-part normalization of the degree-one class

The companion theorem
`connes-semilocal-finite-part-orbital-source-class.md` sharpens the remaining degree-one task.
Connes's proved semilocal cutoff formula already defines a canonical finite-part functional

```text
FP_S(f)=lim_(Lambda->infinity)
  (Tr(vartheta_a(f)R_Lambda)-2f(1)log Lambda)
       =sum_(v in S)W_v(f),
```

whose `p^m` response is exactly `log(p^m)` after the Euler-logarithm coefficient is factored out.
The quantized-differential product identity makes this source class additive and independent of the
Gauss factorization modulo conjugation coboundaries.  Thus the open task is not to invent or
normalize an abstract relative trace.  It is to descend this already fixed cyclic finite-part class
to the closed Sonin three-grade extension, identify its image with the internal trace-defect plus
Burnol-conductor/Euler leakage cross, and prove the completed contraction.  The formal bounded-
response obstruction proves that this descent cannot land entirely in the fixed Hilbert--Schmidt
projection-correction pairing.

Connes--Consani define the finite semilocal Sonin carrier as the kernel of the lower Hardy block of
the finite completed quasi-inner multiplier.  Connes--Consani--Moscovici subsequently prove the
stronger aperture-by-aperture Hilbertian isomorphism with the classical Sonin space and its common
de Branges realization.  Thus no carrier-identification problem remains.  The open grade problem
is to transport the cyclic finite part and its index through the explicit place connection and the
Sonin cutoff/resolvent.

## Exact degree-one source representative

`semilocal-dual-pair-euler-connection-source-law.md` closes the finite-place degree-one
representative before cutoff.  The Connes--Consani--Moscovici place isomorphism satisfies

```text
theta_S^(-1)D_S theta_S-D_infinity
  =M_(-sum_(p in S_f)L_p'/L_p),                           (C1)
```

and the multiplier on the right has the exact von Mangoldt coefficients.  Together with the
Connes finite-part theorem, the principal degree-one grade is therefore fixed simultaneously as a
cutoff finite part, a quantized-differential orbital class, and a semilocal Euler connection.  The
remaining three-grade theorem must transport this explicit connection through the Sonin
cutoff/resolvent and combine it with the Burnol conductor and positive trace-class residual.  It no
longer asks for an abstract semilocal carrier or an arbitrary relative trace.

## Lean status — 2026-08-16

`[FORMALIZED]` — the card's substantive components were already in Lean (all endpoints listed under
"What the corpus already supplies" were verified present in `formal/GaloisForLFunctions/RHTower/`:
`SoninRelativeGramDefect`, `SoninSemilocalTraceObstruction`, `SoninAllPrimeResidualKernel`,
`SoninSemilocalRelativeTrace`, `SoninEulerCalkinPartialIsometry`, `SeamSpectralFlow`,
`MeasuredIndexBlindness`).  The one algebraic gate that had no Lean carrier — the exact
projection-compressed degree-one Gram identity `(9b)`–`(9d)` — is now proved:

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMSoninCompressedCommutator.lean`
(6 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]` — two use
`[propext]` only — wired into `formal/GaloisForLFunctions/RHTower.lean`).

- `one_sub_mul_one_sub`, `compress_split` — **equation (9b)**: inserting the resolution of the
  identity splits a compressed product `Q X Z Q` into the internal term `(QXQ)(QZQ)` and the
  leakage term `(QX(1−Q))((1−Q)ZQ)`.
- `star_leakage_selfAdjoint`, `star_leakage_skewAdjoint` — the adjoints of the two leakages
  `L_X = (1−Q)XQ` and `L_Z = (1−Q)ZQ`, using the symmetry of `Q`, `X` and the skew-symmetry of `Z`.
- **`compressed_commutator_split`** — **equation (9c)**:
  `Q[X,Z]Q = [QXQ, QZQ] + L_X^* L_Z + L_Z^* L_X`, exactly as stated on the card, for a projection
  `Q`, self-adjoint `X` and skew-adjoint `Z`.
- **`degree_one_trace_split`** — **equation (9d)**: applying any additive trace splits the
  degree-one term into the internal trace defect and the leakage pairing.

The statement is proved in an arbitrary `*`-ring, so it applies verbatim to bounded operators on the
Sonin carrier.

Still deliberately absent (the card's own open gates, not statements of this card): the closed
principal–relative carrier `E_a`, the genuine degree-one semilocal relative functional, the cofinal
contractions `(11)`, the index-preserving transport, and RH.
