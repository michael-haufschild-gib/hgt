# Nodal charge boundary intervals and polarized shift transmutation

- **ID:** `nodal-charge-boundary-interval-transmutation`
- **Stage:** 1-in-progress
- **Type:** TYPED LOCALIZATION CORRECTION / POLARIZED CHARGE INTERVAL
- **Scientific status:** `[CONJECTURE UNDER ATTACK] [LOCAL INTERVAL LAWS LEAN-FORMALIZED]`
  `[TWO-SIDED DESCENT NO-GO + POLARIZED TAIL TOWER LEAN-FORMALIZED]`
  `[PARENT EQUIVARIANT DEVISSAGE / TOEPLITZ INDEX] [GLOBAL HT COMPARISON OPEN]`
  `[NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/tate-theta-koszul-barnes-localization-transmutation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/nodal-charge-character-fan-realization.md`
  - `../3-formalized/tate-clock-unilateral-boundary-defect.md`
- **Live successor:**
  `hypertranscendental-source-face-vanishing-cycle-conservation.md`

## Discriminator: charge two

The current endpoint proposal says that the localization boundary of `[x^m]` should land in the
`m`-th source-character line.  This cannot preserve the additive localization boundary when
`m>1`.  Already

```text
partial_K([x^2])=2[A/(x)],                                      (Q1)
```

whereas one endpoint character line has rank one.  Matching `[x^2]` with the charge-two line loses
the multiplicity and the intermediate charge crossing.

```text
[NO-GO]
The equivariant or source-character localization boundary of `[x^m]` is not the endpoint
character fibre `L_m`.
```

The positive replacement is an oriented charge interval.

## `[CONJECTURE -- CHARGE-INTERVAL LOCALIZATION]`

Let `L_k` be the charge-`k` line on one selected source face.  For `m>0`, define an oriented
interval representation `B(m)` with vertices `0,...,m-1`, stalk `L_k` at vertex `k`, and the
charge-raising structure map between consecutive stalks.  Its associated graded object is

```text
gr B(m)=directSum_(0<=k<m) L_k.                                (Q2)
```

For negative charge use the oppositely oriented interval and opposite lines.  Then the correctly
typed equivariant boundary should be

```text
partial_char([x^m])=[B(m)],                                     (Q3)
```

whose nonequivariant rank is `m`.  The endpoint `L_m` is the state reached after applying `x^m`;
it is not the boundary crossed on the way there.  Replacing `B(m)` by its split associated graded
retains its K-class but forgets the successor maps and hence the order of the crossings.

The interval obeys the cocycle law

```text
B(m+n)=B(m) concatenate shift_m(B(n)),                           (Q4)
```

which is the character-refined additivity of the `K_1` boundary.

## Polarized unilateral realization

On the unpolarized Laurent charge module `directSum_(k in Z)L_k`, multiplication by `x` is a
bilateral shift and is invertible.  It has no boundary defect and cannot choose an orientation.

Choose the positive chamber

```text
H_+=directSum_(k>=0)L_k
```

and let `S` raise charge by one.  Its backward partial inverse `B` satisfies

```text
B S=1,
S B=1-P_0.                                                     (Q5)
```

For every `m>=0`, the expected power law is

```text
B^m S^m=1,
S^m B^m=1-P_[0,m),
coker(S^m)=B(m), with gr B(m)=directSum_(0<=k<m)L_k.           (Q6)
```

The negative chamber reverses kernel and cokernel and hence reverses the oriented index.  Thus
the positive chamber missing from the unpolarized character fan is exactly what converts an
invertible bilateral charge translation into a nonzero localization boundary.

## Analytic opposite-charge realization

For the nodal modes

```text
ell_k(z)=exp(2 pi i k z/omega),
```

opposite charges pair to one.  Therefore the interval pairing is

```text
sum_(0<=k<m) ell_(-k)(z) ell_k(z)=m.                           (Q7)
```

Equation `(Q7)` is the analytic realization of the nonequivariant boundary multiplicity in
`(Q1)`.  It retains the full sector decomposition before forgetting the source characters, while
the shift action retains the interval arrows that the numerical pairing cannot see.

The algebraic power defect, exact prefix-plus-tail decomposition, pairing law, and interval cocycle
are Lean-formalized as

```text
tateClockIndBackwardN_forwardN
tateClockInd_boundaryInterval_add_forwardN_backwardN
tateClockPairing_boundaryInterval_add_shift
tateClockIndBoundaryInterval_add.                               (Q6L)
```

The analytic multiplicity and sharp endpoint no-go are Lean-formalized as

```text
nodalChargeBoundaryIntervalPairing_eq
nodalChargeBoundaryIntervalPairing_eq_endpoint_iff.             (Q7L)
```

## Typed covariant module

The nodal coordinate and the Barnes source operators should act on one graded module without being
identified.  On the Laurent model with coordinate `u`, put

```text
M_u(u^k)=u^(k+1),
delta(u^k)=lambda_k u^k,
T_j(u^k)=u^k,
T_r(u^k)=exp(lambda_k omega_r)u^k.                            (Q8)
```

Then

```text
[delta,M_u]=lambda_1 M_u,
T_r M_u=exp(lambda_1 omega_r) M_u T_r,
(T_j-1)M_u^k(1)=0.                                           (Q9)
```

Thus `x` is a charge-raising operator, `T_j-1` is its selected annihilator, and the vacuum `1`
provides the calibration sending `x^k` to `ell_k`.  This resolves the vector/operator symbol
collision without collapsing them into one ring element.

## Anti-theatre and novelty gate

The power defect of a unilateral shift, the Toeplitz index, the filtration of `A/(x^m)` by the
powers of `x`, and the equivariant identity

```text
[A/(x^m)]=1+q+...+q^(m-1)
```

are parent mathematics.  Equations `(Q1)`--`(Q9)` alone are therefore a bridge, not new science.

The candidate-new content is the global HT theorem that the oriented interval objects `(Q2)` glue
over the source-face resonance fan, that their covariant modules carry the same localization
sequence as the coherent Barnes `Tor` class, and that the independently defined analytic,
integral, positive, and spectral realizations are conservative on this interval field.  This is a
strict strengthening of endpoint matching and is falsified by any face for which the localization
boundary has a different character filtration.

Persistence modules already identify finite equioriented `A_m`-quiver representations with graded
modules over a polynomial ring, and coherent devissage already reconstructs additive invariants
from filtered subquotients.  Fujikawa's unilateral phase operator already supplies the unit index
and rank-one anomaly.  Therefore neither the local interval module, its cocycle, nor its index is
new.  The preliminary exact-search gate found no construction tying such interval modules to
hypertranscendence, source-face localization, and jointly conservative transverse reporters.

## Raw interval-capacity no-go

For a source-minimal germ equipped with a transverse reporter, the source-face boundary field is
not merely a constructible sheaf of obstruction groups.  It is a self-dual representation of the
**oriented exit-path category** of the resonance fan.  Every normal path carries an interval module
`B(m)`; path concatenation is `(Q4)`; and orientation reversal sends `B(m)` to the dual oppositely
oriented interval.

Raw interval capacity, however, does **not** characterize hypertranscendence.  The
differential-algebraic function `f(z)=exp(z)` satisfies `f(z+1)=e f(z)`.  For every `N`,

```text
p_N(z)=1+(exp(2 pi i z)-1)^(N+1)
```

is a nontrivial period-one differential-algebraic gauge whose difference from `1` vanishes through
order `N` at zero.  Both `f` and `p_N f` are differential-algebraic, satisfy the same source, and
have the same `N`-jet.  The existing Lean theorem
`existsUnique_gammaPeriodicFourierPolynomial_jet` proves the stronger arbitrary-finite-jet
freedom of the period-one analytic fixed field.

```text
[NO-GO]
Unbounded finite-jet invisibility is an invariant of the enlarged analytic difference-constant
field, not an invariant of hypertranscendence.                                             (Q10)
```

This explains why the bare-source theorem and local interval law cannot by themselves detect HT.
They must be compared only after descent to the declared joint constant field of the minimal
parameterized source-Galois problem.

## Two-sided descent no-go and polarized successor `[PROVED + LEAN]`

The proposed descended **subrepresentation** does not exist nontrivially if it is required to
respect both clock directions.  Let `V=directSum_(n>=0) K e_n`, let `S(e_n)=e_(n+1)`, and let
`B(e_0)=0`, `B(e_(n+1))=e_n`.  Lean proves

```text
D <= V, S(D) <= D, B(D) <= D  ==>  D=0 or D=V.                         (Q11)
```

Indeed, backward-shifting the highest nonzero coordinate of any nonzero finite-support vector
produces a nonzero multiple of `e_0`; the field action and forward shifts then produce every
`e_n`.  This is the algebraic finite-support form of the classical irreducibility of the
multiplicity-one unilateral shift under the shift and its adjoint.

The positive successor is the canonical tail tower

```text
T_m={a : a_0=...=a_(m-1)=0}=S^m(V).                                  (Q12)
```

Every `T_(m+1)` is nonzero and proper, `S(T_m)<=T_m`, and
`B(T_(m+1))<=T_m`, but `B` does not preserve `T_(m+1)`.  Thus every nontrivial clock descent is
necessarily **polarized**: it is a one-sided filtration or a morphism between two filtered clocks,
not a two-sided invariant subclock.  More sharply,

```text
T_m=range(S^m)=kernel(P_[0,m)),
V/T_m=B(m).                                                           (Q12+)
```

The last quotient identity is represented by the already proved prefix-plus-tail decomposition;
the following declarations formalize the image, kernel, and polarization laws:

```text
tateClockIndTailSubmodule_nontrivial_proper
tateClockIndTailSubmodule_forward_mem
tateClockIndTailSubmodule_backward_mem
tateClockIndTailSubmodule_not_backward_invariant
tateClockIndBoundaryInterval_eq_zero_iff_mem_tailSubmodule
mem_tateClockIndTailSubmodule_iff_exists_forwardN
tateClockInd_bishiftInvariantSubmodule_eq_bot_or_top.
```

There is a second scalar no-go.  The complete Kolchin dimension polynomial depends on the chosen
differential generators; only its differential type and leading typical dimension are
differential-birational invariants.  Moreover interval length forgets the extension arrows already
shown essential by the charge-two discriminator.  Therefore an equality between a
presentation-independent scalar interval length and the full Kolchin polynomial cannot be the
universal comparison theorem.

## Standalone cotangent--Tate cone no-go and positive derived chart

Let `H_(S,R)=K^S intersect intersection_r ker(R_r)` be the source-fixed gauge invisible to a
reporter family.  The Gamma collision shows that the base of the theory is the stack of
source-effectively normalized germs with stabilizer `H_(S,R)`, restricted to the stratum `H=0`
when reconstruction is required.  Over that stack one may still form:

1. the one-sided algebraic cotangent tower of differential prolongations, whose `n`th graded
   generic rank is the new differential freedom at order `n`;
2. the independently constructed polarized analytic tail/exit-path tower; and
3. a source-natural comparison morphism `Phi_(S,R)` between their Ind--Pro completions.

but the cone

```text
C_HT(S,R)=Cone(P_alg(S,R) --Phi_(S,R)--> P_an(S,R)),                    (Q13)
```

is not a primary invariant.  The labelled free-field universality theorem makes `P_alg` identical
for equally indexed HT palettes.  If `Phi` is intrinsic to that carrier, `(Q13)` is source-blind;
if it factors through the bare source, the common-kernel no-go persists; and if it uses a genuinely
transverse reporter, `(Q13)` is only one chart of the source--reporter object.  Moreover an ordinary
cone forgets approximate zero modes, nonclosed range, source-labelled orientation, critical
rescaling, the boundary self-symbol, and integral effectivity.

The positive survivor is exact: the oriented interval tower is the exit-path realization of the
strict derived source--reporter observation complex

```text
Cone(RGamma(S,G_HT) -> H_R),                              (Q13+)
```

inside the normalized anomaly-fracture stack.  Its low cohomology contains the normalized common
kernel, reporter nonattainment, and first source cohomology in one long exact sequence; its interval
arrows retain the ordered boundary crossings.  The full stack must additionally retain the
completed reporter graph/Gram field, complete anomaly colligation, critical product bornology,
polarization/anomaly line, integral realization, and distinguished effective section.

The candidate-new claim is no longer existence of `(Q13)`, which is parent mapping-cone
mathematics.  It is presentation-invariant construction of the full normalized stack and proof
that two independently constructed analytic receivers preserve the same interval/seam class.

## Gates

- [x] isolate the charge-two endpoint contradiction
- [x] prove the all-power unilateral boundary identities, prefix decomposition, and cocycle `(Q6)`
- [x] prove the analytic interval pairing and sharp endpoint no-go `(Q7)`
- [ ] prove the covariant commutation laws `(Q9)`
- [x] run the preliminary parent and exact-search gate on the interval formulation
- [x] replace endpoint language in the Tate--Barnes bridge and character-fan target
- [x] kill raw interval capacity as an HT criterion by differential-algebraic periodic gauges `(Q10)`
- [x] kill two-sided descended subrepresentations and formalize the polarized tail successor
      with its exact image--kernel interval law `(Q11)`--`(Q12+)`
- [x] kill the full Kolchin polynomial as a presentation-independent scalar invariant
- [x] retire the standalone cotangent--Tate cone `(Q13)` using free-field universality and the
      strict/oriented/critical reporter no-gos
- [ ] realize the interval tower as the exit-path chart `(Q13+)` of the normalized anomaly-fracture
      stack
- [ ] construct the source-face resonance gluing of boundary intervals
- [ ] construct the global map of localization sequences
