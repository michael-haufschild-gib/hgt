# Source-curved prime-torus conormal temperedness

- **ID:** `source-curved-prime-torus-conormal-temperedness`
- **Stage:** 1-in-progress
- **Type:** FROZEN BOLD CONJECTURE / PRIME-SCHWARTZ THIRD-COMPLETION PROGRAM
- **Scientific status:** `[TRUTH-HUNCH FROZEN] [SOURCE-NATIVE] [EXACTLY RH-EQUIVALENT]`
  `[NOT YET FRONTIER PROGRESS]`
  `[PLAIN C*-MODULE ROUTE RETIRED] [GENERIC WOLD-EXACTNESS RETIRED] [PROOF UNKNOWN]`
- **Source:** the forced reciprocal occupation metric, the Wold--Gamma determinant law, the
  first-trace/BV residue match, the source-conormal strict-topology theorem, the infinite
  prime-torus carrier theorem, and the critical radial-\(L^2\) dense-range no-go
- **Statement:** The full rational-dilation orbit of the source-defined BV/co-Poisson Xi principal
  conormal extends from the algebraic rational group ring to the finite-prime Schwartz
  Ind-completion, continuously and with every multiplicity jet nonzero.  Equivalently, every
  distinguished Xi conormal character is a tempered distribution on every finite-rank
  prime-valuation lattice.  A centered power character is tempered there exactly when it is
  unitary, so RH follows.

## Goal

Construct the missing third completion:

```text
finite source clocks:
  conormal fibres survive, but prime covariance leaks;

scalar adelic L2:
  prime covariance is unitary, but reduced conormal cohomology is zero;

relative source completion:
  prime translation is unitary on the Hilbert middle;
  unitary point characters survive as distributions in the dual;
  the complete source-defined Xi conormal orbit extends continuously into that dual.
```

The conjecture is stated because the complete corpus makes it plausible, not because a proof is
currently visible.  Proof search and falsification begin only after the statement is fixed.
Provability, a proposed construction, and a decomposition into lemmas are not part of the
conjecture.

## Frozen conjecture: prime-Schwartz Xi conormal temperedness

Let

```text
G=Q_(>0)^x=direct-sum_(p prime) Z,
G_P=<P> ~= Z^P                                           (T1)
```

for each finite prime set `P`.  Give `G_P` its valuation coordinates and let `S(G_P)` be the
ordinary Schwartz space on `Z^P`.  Extension by zero along `P subset P'` defines the source-natural
finite-prime Ind-space

```text
S_pr(G)=colim_(P finite) S(G_P).                          (T2)
```

It has the rigged regular representation

```text
S_pr(G) subset ell2(G) subset S_pr(G)'.                   (T3)
```

Rational prime translation is continuous on both outer terms and unitary on the Hilbert middle.
Unlike scalar `ell2(G)`, the dual retains every unitary point character as a generalized
eigenvector.

Let `U` be the shifted nontrivial Xi strip, let `A=O(U)` with compact-open topology, let
`Lambda` be the completed co-Poisson multiplier, and put

```text
N_Xi=A/(Lambda).                                         (T4)
```

The quotient retains the full principal divisor scheme, including multiplicity jets.  For a
compact-BV window `W`, write `F_W` for its canonical meromorphic prime-polar continuation and

```text
J_W(g)=[Lambda F_(g.W)] in N_Xi,                         (T5)
```

where `g.W` is argument dilation or expansion according to the rational `g`.  Pole cancellation
makes `(T5)` analytic before any zero is chosen.  Use either the proved two-window jointly
noncensoring family or the proved single inverse-tilted source, so every nontrivial principal
conormal jet is detected.

> **[FROZEN CONJECTURE -- PRIME-SCHWARTZ XI CONORMAL TEMPEREDNESS.]**
> The algebraic orbit map
>
> ```text
> J_Xi^alg : C[G] tensor W_sep -> N_Xi
> ```
>
> extends continuously from `S_pr(G) tensor W_sep` to `N_Xi`, compatibly over finite prime sets,
> and its specialization to the top nonzero jet at every nontrivial Xi divisor point is nonzero.
> The extension is presentation-independent under the six source channels forced by the HT
> minimality theorems.

This is the statement that now seems true after the corpus audit.  No construction of the
extension is known.  Neither Wold homological perturbation, a Hilbert-module realization, nor any
candidate proof is part of the conjecture.

The conjecture makes temperedness literal.  At a divisor point `rho`, the top nonzero conormal jet
of `(T5)` has rational-dilation character

```text
chi_rho(g)=g^(rho-1/2).                                  (T6)
```

On any one-prime axis `g=p^k`, a character on `Z` is a tempered distribution exactly when its
values have polynomial growth in `|k|`.  The sequence

```text
k |-> p^(k(rho-1/2))                                    (T7)
```

has polynomial growth in both directions exactly when `Re(rho)=1/2`.  Multiplicity derivatives
only add polynomial factors in `k` and do not change this criterion.  Therefore continuous
nonzero specialization of the conjectured extension forces every nontrivial Xi zero onto the
critical line.

### Logical audit: exact RH equivalence in the natural analytic quotient

The natural quotient topology does not make the frozen conjecture stronger than RH.  On the open
strip `U`, the principal ideal quotient

```text
O(U)/(Lambda)
```

is the holomorphic function space of the discrete divisor scheme: a product of the finite
multiplicity-jet spaces at the zeros of `Lambda`.  This is the one-dimensional
Cartan/Mittag--Leffler restriction theorem plus the open mapping theorem for Fréchet spaces.
Consequently a map into `(T4)` is continuous exactly when each divisor-jet coordinate is
continuous.

For a zero `rho` of multiplicity `m`, every coordinate of the dilation orbit is a finite linear
combination of

```text
polynomial(log g) * g^(rho-1/2),                          (T8)
```

of degree below `m`.  On the one-prime subgroup `g=p^k`, `(T8)` is tempered exactly when
`Re(rho)=1/2`.  A jointly noncensoring source family makes at least one top coordinate nonzero at
every zero.  Therefore

```text
PRIME-SCHWARTZ XI CONORMAL TEMPEREDNESS
  iff every nontrivial Xi zero has real part 1/2
  iff RH.                                                 (T9)
```

This is a precise topological reformulation and identifies the correct point-fibre carrier, but
`(T9)` is not new mathematical progress toward RH.  A frontier theorem must force the extension
from independently constructed source effectivity, critical bornology, or anomaly integration;
assuming continuity in `(T4)` is assuming the missing horizontal rigidity.

Why believe the conjecture, independently of provability:

1. finite coefficient clocks retain the conormal but lose covariance only through exact Wold
   boundary layers;
2. the reciprocal occupation metric already centers rational dilation as an isometry;
3. functional-equation reflection supplies the opposite valuation direction;
4. the source-conormal theorem forces a topology strictly finer than the raw product clock;
5. the HT minimality theorems force the full finite-prime product bornology rather than one
   cofinal ray;
6. Gamma `det_2` and BV first trace are the regular and singular readings of the same Wold
   boundary;
7. scalar `ell2(G)` loses point fibres, while the canonical Schwartz rigging retains precisely
   tempered generalized characters.

## Exact centering correction

Let

```text
H0=ell2(N_{>0}),
Q e_n=n^(-1)e_n,
S_q e_n=e_(qn),
E_q=I-S_q S_q^*,
V_q=sqrt(q) S_q.
```

The proved covariance

```text
S_q^* Q S_q=q^(-1)Q                                      (1)
```

is equivalent to

```text
V_q^* Q V_q=Q.                                           (2)
```

Thus the RH-centered dilation is already isometric, but only after the arithmetic source metric
`Q` is inserted before taking the adjoint.  This is the exact mathematical content extracted from
the “source determines geometry” principle in the Einstein equation.

On the algebraic occupation core, write `dagger_Q` for this adjoint. Directly,

```text
V_q^dagger_Q=(1/sqrt(q))S_q^*,
V_q^dagger_Q V_q=I,
V_q V_q^dagger_Q=S_qS_q^*,
I-V_q V_q^dagger_Q=E_q.                                 (2a)
```

Equivalently, complete the algebraic core in the `Q`-metric and use
`f_n=sqrt(n)e_n` as its orthonormal basis. Then `V_q f_n=f_(qn)`: `V_q` is the ordinary
unilateral multiplicative shift in that Hilbert realization. This is the representation whose
Toeplitz boundary is used below.

It also corrects an ambiguity in the first Wold--Gamma anomaly proposal.  In the standard
`ell2` metric:

```text
S_q^* has Dirichlet eigencharacter q^(-rho),
sqrt(q) S_q has dual eigencharacter q^(1/2-rho),
V_q^*V_q-I=(q-1)I.
```

Therefore the centered RH character is not obtained by declaring the ordinary Wold projection
`E_q` to be `U_q^*U_q-I`. The isometry-side defect is zero; `E_q` is exactly the opposite
range defect in `(2a)`. The Wold projection also enters through the source-metric decomposition

```text
Q=E_q Q+S_q S_q^*Q,                                     (3)
```

whose regular determinant is the proved Gamma cocycle and whose missing first trace has the same
coefficient `1-q^(-1)` as the BV off-multiple conormal residue.  Any successful chain identity
must be formulated relative to `Q`, not relative to the background `ell2` metric.

## Why a scalar Hilbert completion is the wrong category

Completing the critical Poisson complex in scalar radial \(L^2\) makes multiplication by zeta have
dense range, so reduced Hilbert cohomology vanishes.  The bilateral regular representation
likewise restores unitary prime covariance but turns divisor characters into continuous spectrum.

The source-conormal topology theorem proves the complementary fact: a nonzero HT conormal forces a
strict refinement of the product clock topology.  The finite prime-torus theorem proves that the
required phase dimension is unbounded.  These two facts point to a module over the complete prime
phase algebra, not another scalar norm.

Put

```text
G=Q_{>0}^x = directSum_(p prime) Z,
Ghat=Hom(G,T)=T^P,
A=C*(G)=C(Ghat).                                         (4)
```

Unlike scalar \(L^2(\widehat G)\), an \(A\)-module retains point fibres by the Hausdorff quotient
`E tensor_A C_chi`.  The canonical group elements `u_q in A` are central unitaries.  The nuclear
test/dual rigging is required because Xi conormals are distributional boundary classes rather than
ordinary vectors of the scalar Hilbert shadow.

## Concrete coefficient algebra: descalarized Wold--Toeplitz extension

The coefficient part is more specific than an arbitrary Hilbert \(A\)-module.  Let

```text
T_Gamma=C*(Q,{S_p : p prime}) subset B(H0)
J_Gamma=the closed ideal generated by {E_p : p prime} and Q.
```

The relations are

```text
S_p S_q=S_q S_p,
S_p^* S_q=S_q S_p^*                 for p!=q,
Q S_q=q^(-1)S_q Q,
S_q^* Q S_q=q^(-1)Q.                               (4a)
```

After every `E_p` is killed, the `S_p` become commuting unitaries.  The covariance then forces the
image of `Q` to vanish.  In fact the source coefficient extension is exactly

```text
0 -> J_Gamma -> T_Gamma -> C*(G)=C(Ghat) -> 0.             (4b)
```

### Exact boundary-quotient theorem `[PROVED HERE]`

The quotient in `(4b)` is not a proper quotient of `C*(G)`.

Enumerate the primes as `p_1,p_2,...`.  Fix
`chi=(chi_p)_p in Ghat`.  For `k>=1`, let

```text
B_k={0,...,k}^{ {p_1,...,p_k} }
```

and define the unit vector

```text
xi_(k,chi)
 =|B_k|^(-1/2)
   sum_(a in B_k)
     product_(j<=k) chi_(p_j)^(-a_j)
     e_(product_(j<=k) p_j^(a_j)).                       (4c)
```

For every fixed prime `p_j`, once `k>=j`, direct comparison of the two endpoint faces of the
`p_j`-exponent box gives

```text
‖(S_(p_j)-chi_(p_j))xi_(k,chi)‖^2=2/(k+1),
‖E_(p_j)xi_(k,chi)‖^2=1/(k+1).                          (4d)
```

The adjoint error also tends to zero.  Moreover

```text
‖Q xi_(k,chi)‖^2
 =1/(k+1)^k product_(j<=k) sum_(a=0)^k p_j^(-2a)
 <=zeta(2)/(k+1)^k ->0.                                (4e)
```

Hence every noncommutative star polynomial in `Q,{S_p}` acts on `xi_(k,chi)` asymptotically by
the scalar obtained from

```text
Q |->0,       S_p |->chi_p,       S_p^* |->conjugate(chi_p).
```

Any weak-star limit of the corresponding vector states is therefore the character
`omega_chi` of `T_Gamma` with these generator values.  Equations `(4d)`--`(4e)` show that
`omega_chi` annihilates `J_Gamma`.

The quotient is generated by the commuting unitaries `[S_p]`, so there is a surjection

```text
C*(G)=C(Ghat) -> T_Gamma/J_Gamma.
```

Every point evaluation on `C(Ghat)` factors through this map by `omega_chi`.  Its kernel therefore
vanishes at every point of `Ghat` and is zero.  This proves `(4b)`.

This coefficient theorem is parent semigroup-boundary mathematics, not the conjectural RH step.
For an Ore semigroup the general boundary quotient/C-star-envelope theorem already identifies the
boundary with the group C-star algebra; see Kakariadis--Katsoulis--Laca--Li,
https://arxiv.org/abs/2105.00422.  The direct argument above checks that adjoining the singular
source operator `Q` does not shrink that boundary.

The semigroup Toeplitz algebra and its group boundary quotient are parent operator algebra.  The
source-specific content is the extra critical operator `Q` and its two simultaneous boundary
readings:

```text
regular reading:   det_2 of E_q Q = Gamma phase cocycle;
singular reading:  renormalized Tr(E_q Q) = BV residue density.
```

This extension explains the two bad scalar limits.  The `J_Gamma` side retains unilateral Wold
leakage but has no unitary character boundary.  Haar scalarization of the quotient gives the
regular representation

```text
L2(Ghat,Haar) ~= ell2(G),
```

which restores unitary covariance but makes every point ideal dense.  Keeping the quotient as the
Hilbert module `A_A`, rather than applying Haar scalarization, gives the nonzero Hausdorff fibre

```text
A tensor_A C_chi ~= C_chi
```

at every unitary prime character.  The third completion must be a rigged relative complex over
`(4b)`: boundary-sensitive enough to retain `J_Gamma`'s Gamma/first-trace anomaly and
module-valued enough to retain `A`'s point fibres.

### Plain boundary-module no-go `[PROVED HERE]`

A Hilbert module over `A=C*(G)` alone cannot be the third completion. Every representation
factoring through the quotient in `(4b)` sends

```text
Q |->0,       E_q |->0,       E_q Q |->0.
```

Therefore it sends both source anomaly readings to zero:

```text
det_2(I-tE_qQ)/det_2(I+tE_qQ) |->1,
finite-part Tr(E_qQ) |->0.
```

But the actual source values are the nontrivial Gamma cocycle `Phi(t)/Phi(t/q)` and the nonzero
first-trace density `1-q^(-1)`. Adding those values back as unrelated scalar decorations would
discard the chain map whose existence is the entire open problem.

Thus the third completion is not an `A`-module. It must be a **relative object for the extension
`(4b)`**: a mapping-cone, relative cyclic, or equivalent rigged complex which retains the ideal
transgression while its boundary cohomology is an `A`-module. Relative cyclic cocycles and
renormalized trace/eta pairs for algebra extensions are parent mathematics; the source-specific
claim is that the Wold--Gamma and BV readings form one such relative Xi class.

The source metric also identifies the group boundary without a guessed centering.  With
`f_n=sqrt(n)e_n`, the vectors `f_n` are orthonormal for the `Q`-metric and

```text
V_q f_n=f_(qn).
```

The minimal unitary dilation of this multiplicative semigroup is the regular action on
`ell2(G)`.  Thus the already constructed Deninger Gamma-rank regular representation is the Haar
scalar shadow of the proposed module boundary, not the final completion itself.

## Canonical Wold contraction and the second redressing no-go

Let `H_Q` be the reciprocal-metric completion from `(1)` and let

```text
W_q : 0 -> H_Q --U_q--> H_Q --E_q--> E_q H_Q -> 0.        (4h)
```

Here the second arrow is the Wold projection with codomain restricted to its range.  Since

```text
E_q U_q=0,
ker(E_q)=range(U_q),
U_q^dagger U_q=I,
U_q U_q^dagger+E_q=I,
```

`(4h)` is split exact.  Its canonical contraction is

```text
h_q|_(H_Q)=U_q^dagger,
h_q|_(E_q H_Q)=i_q,                                      (4i)
```

where `i_q:E_qH_Q -> H_Q` is inclusion.  Directly,

```text
partial_q h_q+h_q partial_q=I.                            (4j)
```

This proves a stronger no-go than abstract `sqrt(D_q)` redressing: the actual coefficient Wold
defect is already contractible by source-independent arithmetic maps.  Merely asking that `E_q`
be exact, even with the correct reciprocal metric, adds no Xi information.

### Typed BV/co-Poisson Wold renewal `[PROVED PAPER BRIDGE; NOVELTY NOT CLAIMED]`

The missing type comparison between coefficient Wold maps and the conormal quotient is not an
unspecified differential.  Let `q=r^2`, let `W_j(x)=W(r^j x)`, let `p_j` be its prime-polar
coefficient, and let

```text
D_q p_j=p_(j+2),
c_j=E_q p_j=p_j-S_q p_(j+2).                            (4j1)
```

For the pole-cancelled continuation define, before choosing a zero,

```text
J(a)=[Lambda F_a] in A/(Lambda).                         (4j2)
```

The proved normal-class dilation and the elementary Dirichlet inflation law give

```text
J(p_(j+2))=q^(s-1) J(p_j),
J(S_q a)=q^(-s)J(a),
J(c_j)=(1-q^(-1))J(p_j).                                (4j3)
```

The ordinary finite Wold identity is

```text
p_j=S_q^n p_(j+2n)+
    sum_(0<=k<n) S_q^k c_(j+2k).                         (4j4)
```

Applying `J` cancels the spectral parameter exactly:

```text
J(S_q^n p_(j+2n))=q^(-n)J(p_j),
J(S_q^k c_(j+2k))=(1-q^(-1))q^(-k)J(p_j).               (4j5)
```

Hence the conormal is the infinite Wold-boundary renewal

```text
J(p_j)=sum_(k>=0)(1-q^(-1))q^(-k)J(p_j).                (4j6)
```

The weights are the exact Haar probabilities of the `q`-adic valuation layers.  The same layer
projections `S_q^k E_q D_q^k` split the regular determinant into the telescoping factors

```text
Phi(t/q^k)/Phi(t/q^(k+1)).                               (4j7)
```

Thus Gamma regularization, BV first trace, and the principal conormal are now typed on one
coefficient-layer tower.  This is a direct consequence of existing identities, not frontier
mathematics.  It changes the live question: the missing theorem is not a map between unrelated
modules but bilateral tempered continuity of the complete conormal orbit.  Equations `(4j5)`--
`(4j6)` alone cannot select the critical line because their weights are independent of `s`.

Now let `C_Xi^alg` be the source complex generated before zero specialization by:

1. the integral multiplicative coefficient core and its centered maps `V_q`;
2. the completed co-Poisson/Xi constraint and its principal conormal;
3. independent prime-labelled Wold boundary terms `E_q Q`;
4. the polarized determinant line
   `det_2(I-tQ)/det_2(I+tQ)`;
5. the renormalized first-trace boundary with density `1-q^(-1)`;
6. the critical Gevrey product bornology, source reflection, and distinguished effective section.

These are exactly the independent channels forced by the HT minimality theorems.  No zero,
zero enumeration, Weil sign, or RH-equivalent norm is used in the definition.

Let `N_Xi^src` denote the algebraic principal-conormal cohomology of this source complex, including
multiplicity jets, with the centered rational-dilation action.  It is defined before choosing or
enumerating a zero; specialization only reads its support.

The former conjecture that `N_Xi^src` merely has a radical-free unitary completion is retired as a
frontier claim. It collides with
`../5-failed/prime-translation-theta-unitary-defect-conjecture.md`: faithful positive
semisimplification of the analytic Xi defect is RH-equivalent. Replacing Hilbert space by a plain
Hilbert `A`-module changes vocabulary but not that logical content.

Write `dagger` for the adjoint in the forced reciprocal occupation metric. Centered prime
dilation is already an isometry,

```text
U_q^dagger U_q=I,
```

and its Wold range defect is `D_q=I-U_q U_q^dagger=E_q`.

Suppose a relative source totalization has square-zero differential

```text
mathcalD_(Xi,q)=partial_q+delta_Xi
```

on the algebraic Wold--source core.  Define the mixed contraction anomaly by the typed identity

```text
I+mathcalA_q
 =mathcalD_(Xi,q) h_q+h_q mathcalD_(Xi,q),
mathcalA_q=delta_Xi h_q+h_q delta_Xi.                    (4k)
```

Because `mathcalD_(Xi,q)^2=0`, `I+mathcalA_q` commutes with `mathcalD_(Xi,q)`.  Wherever it has a
continuous inverse, the explicit homotopy

```text
h_q (I+mathcalA_q)^(-1)                                  (4l)
```

contracts the total complex.  Therefore source cohomology can survive only where `(4l)` fails:
noninvertibility, nonclosability, or loss of domain under critical completion.  This is the
homological-perturbation support mechanism.  The algebraic identity is parent mathematics; the
arithmetic completion and its support are not supplied by it.

> **[POST-CONJECTURE PROOF HYPOTHESIS -- WOLD--SOURCE PERTURBATION SUPPORT.]**
> One possible attack would assemble the six fixed source channels into a polarized rigged
> relative totalization of `(4b)` in which the cofinal family `mathcalA_q` has a
> presentation-independent closed graph class `mathcalA_Xi`.  Its regular relative determinant
> would be the proved cocycle `Phi(t)/Phi(t/q)`, its singular trace would be `(1-q^(-1))` times the
> proved BV principal conormal, and strict failure of `I+mathcalA_Xi` would recover the
> prime-Schwartz conormal extension.

This paragraph is not part of the frozen conjecture.  It is a later proof hypothesis motivated by
the regular/singular Wold fingerprints and may be discarded without weakening or changing the
truth-hunch.  Neither `mathcalD_(Xi,q)`, its domain, nor its completion may be manufactured from a
zero, a target Gram factorization, or the desired failure locus.

### Abstract Hodge redressing is automatic `[PROVED NO-GO]`

For any positive operator `D`, put `d=sqrt(D)` in a two-term Hilbert complex and `K=d/2`. On its
degree-zero term,

```text
d^dagger K+K^dagger d=D.
```

Thus existential Hodge exactness on an unspecified complex carries no information.  Equations
`(4h)`--`(4j)` show that even the actual Wold coefficient sequence is already split exact.  The
post-conjecture proof hypothesis concerns failure of its fixed contraction to survive the
independently fixed Euler--Gamma--co-Poisson source totalization and critical completion. Adding a
contractible `sqrt(D_q)` cone is prohibited redressing.

The following six clauses are a **candidate realization package**, not additional conjuncts hidden
inside the conjecture. One possible realization would construct extension `(4b)` in the
source-critical category and a source-functorial rigged relative extension complex
>
> ```text
> Phi_Xi subset E_Xi subset Phi_Xi'
> ```
>
> and a comparison from `C_Xi^alg` satisfying:
>
> 1. **Metric-first covariance.** On the occupation core its metric restricts to `(1)`--`(3)`;
>    centered rational dilation is an isometry there, and `(4h)`--`(4j)` are the actual Wold
>    resolution and contraction transported into the relative totalization.
> 2. **Gamma determinant compatibility.**  The relative determinant of the `q`-Wold boundary is
>    exactly the proved polarized Gamma cocycle
>    `Phi(t)/Phi(t/q)`.
> 3. **First-trace compatibility.**  Its singular boundary transgression is the BV/co-Poisson
>    conormal class with coefficient `1-q^(-1)`, not a freely chosen counterterm.
> 4. **Strict Hausdorff cohomology.**  Constraint cohomology is formed in the source Mackey/critical
>    bornology before Hilbert reduction and is Hausdorff after the prime-torus module realization.
> 5. **Fibrewise conormal faithfulness.**  For every nontrivial Xi divisor point `rho`, including
>    multiplicity jets, the distinguished algebraic conormal fibre maps nontrivially into the
>    corresponding completed module fibre.
> 6. **Presentation covariance.**  Equivalent Euler--Gamma/co-Poisson presentations induce the
>    same completed object; prime exhaustion, finite clock coordinates, and local counterterm
>    choices do not change it.

Clause 5 is a source comparison theorem, not an extra zero-defined vector.  Its domain is the
conormal of the distinguished Xi section already produced by the completed source.

## RH consequence of either the frozen extension or the stronger proof hypothesis

At an Xi zero `rho`, the algebraic centred adjoint prime character is

```text
lambda_rho(q)=q^(rho-1/2).                                 (5)
```

The frozen conjecture says that its nonzero principal conormal multiplicity jet defines a
continuous distribution on each prime-axis Schwartz space.  Equivalently, under the stronger
Wold proof hypothesis it is a strict failure point supported on the unitary boundary.  Either
formulation gives
`|lambda_rho(q)|=1` for every `q`.  Hence

```text
|q^(rho-1/2)|=1,
Re(rho)=1/2.
```

At the boundary endpoint this has the equivalent coefficient-algebra reading: for any complex
character `lambda` of the group algebra `C[G]`, the scalar base change

```text
A tensor_(C[G]) C_lambda                                  (6)
```

is zero unless `lambda` is unitary: if `|lambda(q)|!=1`, then `u_q-lambda(q)` is invertible in
`A=C(Ghat)` while `(6)` forces it to act as zero. The relative source comparison says the mixed
failure class reaches this boundary without becoming zero. Thus the strict-support and
\(C^*\)-boundary readings give the same RH conclusion. The plain boundary module is the endpoint
of the relative construction, not the third completion itself.

This consumer is elementary.  All difficulty lies in constructing `mathcalA_Xi` and proving its
exact divisor and unitary-support clauses.

## Why this is a genuine jump rather than a renamed old route

1. It changes the completion category from scalar Hilbert space or a plain boundary module to a
   source-relative complex for the Wold--Toeplitz extension.
2. It puts the arithmetic metric before adjunction; the standard-metric Wold defect and centered
   dilation are not conflated.
3. It uses the exact regular/singular unity of the Gamma determinant and BV first trace.
4. It retains the distinguished section and integral source lattice required by the six-channel
   HT lower bound.
5. It does not infer a groupoid lift from scalar pair-face data, which is forbidden by the
   existing equivariant-section no-go.
6. It does not ask an AF norm limit to nucleate divisor charge; the conormal is already a
   distinguished singular source section before completion.

## Relation to the “LLMs cannot jump” paper

Only the paper's methodological pattern is imported.

- **General covariance:** clause 6 requires presentation/exhaustion independence.
- **Equivalence principle:** every finite Euler connection is locally pure gauge; obstruction is
  the unattainable cofinal first-trace boundary.
- **Einstein equation:** `(1)`--`(3)` show that source covariance fixes the metric in which the
  centered dynamics is isometric.
- **Gravity gravitates:** Gamma determinant and first-trace anomaly are part of the completion
  geometry, not scalar reporters appended after the metric is fixed.
- **Newtonian limit:** the safe Euler/finite-occupation chamber must recover `Q e_n=e_n/n`.

No Lorentz or Einstein formula is asserted to prove RH.  Their value is the category correction
confirmed here by the exact arithmetic covariance equation `(1)`.

## Hostile falsifiers

Retire or revise the conjecture if any of the following occurs.

1. The map `(T5)` is not well-defined on algebraic source relations before choosing a divisor
   point.
2. Its restriction to one finite prime lattice fails to extend to `S(Z^P)` in the natural analytic
   quotient topology.
3. A proved jointly noncensoring source jet becomes zero after the proposed extension.
4. Compatibility fails under enlargement of finite prime sets, source reflection, or a
   source-equivalent window presentation.
5. The only continuous extension factors through scalar `ell2(G)` and therefore loses the
   principal conormal fibres.
6. An explicit off-line generalized-prime Euler system carries the same algebraic normal map and
   the same compatible finite-prime Schwartz continuity.  This would directly refute the hunch,
   not merely one proof route.

The separate Wold--source proof hypothesis fails if Gamma has only a scalar determinant reading,
if its mixed graph cannot be defined source-first, if it adds a contractible redressing cone, or
if `I+mathcalA_Xi` has the wrong strict failure support.  Such a failure does not by itself refute
the frozen temperedness conjecture.

## Research program after conjecture generation

1. Prove the abstract finite-prime theorem: a centered power character and all its finite jets are
   tempered on `Z^P` exactly on the unitary screen.
2. Finish the algebraic orbit-map audit and the Wold renewal bridge `(4j1)`--`(4j7)` without
   inserting a zero.
3. Prove the analytic conormal quotient is Hausdorff, retains multiplicity jets, and is compatible
   with the finite-prime Schwartz Ind-system.
4. Attack continuity of `J_Xi^alg` directly from the six source channels.  Treat Wold
   homological perturbation only as one possible attack, not as the conjecture.
5. Prove compatibility is independent of prime order and source presentation.
6. Attack fibrewise faithfulness; if it fails, classify the radical rather than adding a
   zero-dependent repair.
7. Run a specialist literature audit for co-Poisson Schwartz spaces, scaling-site spectral
   realizations, Tate/Ind-Pro categories, and arithmetic temperedness.
8. Formalize only dependency-closed unconditional theorems.

## Literature boundary

The categorical and analytic containers are parent mathematics:

- Braunling--Groechenig--Wolfson,
  [*Tate Objects in Exact Categories*](https://arxiv.org/abs/1402.4969), develops admissible
  Ind--Pro/Tate objects and their lattices;
- Hennion,
  [*Tate objects in stable infinity categories*](https://arxiv.org/abs/1606.05527), supplies the
  derived stable setting;
- Connes--Consani,
  [*Hochschild homology, trace map and zeta-cycles*](https://arxiv.org/abs/2207.10419), already
  places a zeta multiplier quotient of a Schwartz space on the Scaling Site and spectrally
  realizes the critical zeros;
- Connes--Consani--Moscovici,
  [*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423), develops the
  semilocal scaling/Sonin framework over increasing finite place sets;
- Burnol's co-Poisson and Sonine work supplies the source quotient and point-evaluation side used
  elsewhere in the corpus.

Therefore Schwartz rigging, Tate categories, scaling actions, and quotienting by a zeta multiplier
are not discoveries here.  The exact frontier claim is narrower: the source-defined
BV/co-Poisson **principal conormal orbit for the complete divisor**, with its integer-decimation
Wold renewal and multiplicity jets, extends compatibly to every finite-prime Schwartz lattice.
Connes--Consani's critical-zero realization does not assert that the all-zero conormal orbit has
this tempered extension; proving that assertion would exclude the off-line part rather than
discard it by selecting the critical spectrum.  Targeted searches found no paper proving this
extension.  This is provisional placement, not a priority claim.

## Gates

- [x] 0 → 1: truth-hunch frozen independently of proof visibility
- [x] prime-Schwartz third completion and exact RH consumer stated
- [x] exact coefficient extension `(4b)` proved, including the adjoined source operator `Q`
- [x] algebraic BV/co-Poisson normal orbit and one-prime Wold renewal typed on paper
- [x] one-prime Wold renewal lifted to the coherent continuous
      unit-exponential Wold--Calderón first-cell cocycle
- [ ] finite-prime Schwartz Ind-space and tempered-character criterion formalized
- [ ] analytic conormal quotient topology and multiplicity-jet continuity proved
- [ ] `J_Xi^alg` extended continuously on every finite-prime Schwartz chart
- [ ] chart extensions proved compatible and presentation-independent
- [x] plain Hilbert-`A` module ruled out because it kills both anomaly layers
- [ ] source-effective relative mapping-cone complex constructed
- [x] generic and coefficient-level Wold exactness retired as split-exact redressing
- [ ] cofinal mixed anomaly `mathcalA_Xi` constructed with Gamma/BV relative character
- [ ] failure locus identified with Xi principal conormal divisor
- [ ] failure locus proved unitary
- [ ] strict cohomology proved Hausdorff
- [ ] fibrewise conormal faithfulness proved
- [ ] specialist novelty audit complete
- [ ] dependency-closed paper proof
- [ ] unconditional Lean formalization
- [ ] RH

## Log

- 2026-07-28 — Formulated after combining the source-determined-metric lesson of the LLM-jump
  paper with the exact reciprocal occupation covariance, the Wold--Gamma/BV anomaly match,
  prime-torus dimension divergence, strict source-conormal topology, and scalar-\(L^2\) erasure
  theorem.  Separated conjecture quality from current proof availability.
- 2026-07-28 — Replaced the original six-clause existence package by one atomic conjecture:
  radical-free unitarizability of the source-effective Xi conormal representation.  The six
  clauses are now only a candidate realization.  Rejected Fourier--Bohr almost periodicity as the
  conjecture: the corpus already proves the analogous Suzuki criterion equivalent to RH and
  records the prime-side Bohr-mean derivation as circular.
- 2026-07-28 — Proved the exact coefficient extension `(4b)` by prime-valuation Følner boxes.
  Every prime-torus character is an asymptotic joint eigenstate killing all Wold defects and `Q`,
  so adjoining `Q` does not turn the standard semigroup boundary quotient into a proper quotient.
- 2026-07-28 — Hostile audit retired radical-free unitarizability as a frontier conjecture: it is
  the failed Route A faithfulness core in Hilbert-module language. Proved a plain boundary-module
  no-go and replaced it by relative Wold anomaly inflow. Corrected the anomaly from the vacuous
  isometry side `U_q^dagger U_q-I` to the Wold range side `I-U_q U_q^dagger`.
- 2026-07-28 — Sharpened conjecture quality independently of proof visibility.  Proved the actual
  Wold sequence is canonically split exact with contraction `(U_q^dagger,i_q)`, so range-defect
  Hodge exactness is not frontier mathematics. Replaced it by the mixed Wold--source perturbation
  support conjecture: Gamma/BV are the two readings of the strict failure of the canonical
  contraction after the fixed Xi source differential and critical completion; that failure locus
  is conjectured to equal the Xi conormal divisor and to be unitary.
- 2026-07-28 — Applied the truth-hunch criterion literally.  Froze PRIME-SCHWARTZ XI CONORMAL
  TEMPEREDNESS before proof design: the full source conormal dilation orbit should extend
  continuously from the rational group ring to the finite-prime Schwartz Ind-space, with every Xi
  multiplicity jet nonzero.  Demoted Wold homological perturbation from the conjecture to one
  optional post-conjecture proof hypothesis.
- 2026-07-28 — Typed the coefficient/conormal bridge.  Repeated Wold decomposition gives exact
  boundary weights `(1-q^(-1))q^(-k)` and tail `q^(-n)` in the pole-cancelled conormal quotient;
  the same valuation layers telescope the Gamma determinant.  This closes the module mismatch but
  cannot select the critical line because the weights are spectral-parameter independent.
- 2026-07-28 — Literature audit found the closest collision in Connes--Consani's Scaling-Site
  Schwartz quotient and semilocal Sonin realizations.  Those works realize critical zeros; they do
  not prove tempered finite-prime extension of the complete BV/co-Poisson conormal divisor.  Tate,
  Schwartz, and scaling containers are parent theory, not novelty.
- 2026-07-28 — Hostile logical audit proved on paper that the frozen conjecture in the natural
  compact-open conormal quotient is exactly equivalent to RH: the quotient is a product of
  divisor-jet spaces, and each jet is a polynomial times `g^(rho-1/2)`, tempered on a prime axis
  exactly on the critical line.  Reclassified it as a clean hunch/third-completion specification,
  not frontier progress.  Independent source-forced continuity remains the actual research task.
- 2026-07-28 — `unit-exponential-wold-calderon-suspension.md` supplies the missing continuous
  comparison at the coefficient layer.  The unit exponential aperture cells have exactly the
  Wold/Haar masses `(1-q^(-1))q^(-k)`, compose under rational multiplication, and have first-cell
  symbol `(1-q^(-(1+w)))/(1+w)`.  This is Lean-formalized.  It does not prove the all-prime
  source-effective product or conormal conservativity; the bounded unit metric is norm-equivalent
  to scalar `L2` and therefore cannot be the third completion.
