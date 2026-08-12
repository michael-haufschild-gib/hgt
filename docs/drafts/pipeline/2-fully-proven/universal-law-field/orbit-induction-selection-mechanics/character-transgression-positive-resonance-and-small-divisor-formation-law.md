# Character transgression, positive resonance, and small-divisor formation law

- **ID:** ULF-OISM-4
- **Stage:** 2-fully-proven
- **Type:** PHASE-TRANSGRESSION / POSITIVE-FORMATION / GLOBAL-PROPERNESS THEOREM
- **Parents:** ULF-OISM-1, ULF-OISM-2, ULF-OISM-3, and the common-recovery
  functional-equation packet lift
- **Statement:** Shift transgression has a bounded primitive on every nontrivial phase character
  and no bounded primitive on the neutral character.  Positive Gram formation pairs each character
  with its conjugate and therefore sends every self-pair to the neutral obstruction.  A finite
  phase packet splits canonically into its resonant commutant survivor and an exact oscillatory
  coboundary.  For a countable pure-point packet, the transgression range is closed exactly when
  only finitely many distinct phase classes occur.  Infinite phase diversity therefore forces
  both unbounded recovery conditioning and rank growth of the positive survivor.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [THREE-ORGAN FUSION] [EXACT CONSERVATION IDENTITY] [GLOBAL PROPERNESS THEOREM]
  [FUNCTIONAL-EQUATION NEUTRAL] [LEAN-PENDING] [NOT RH]

## 1. Why this is a field mechanism

Orbit induction by itself explains why a local defect can become essential.  It does not explain
which orbit modes admit a source primitive, why positivity repeatedly destroys phase information,
or why phase-rich cofinal systems develop nonclosed ranges.

The missing operation is the interaction of three formations:

```text
character formation       chi
shift transgression        delta = 1 - shift
positive formation         chi* chi.
```

The first two distinguish neutral from oscillatory modes.  The third sends every self-pair to the
neutral mode.  This noncommutation is the mechanism proved below.

## 2. Exact bounded-primitive classification

Let `H,K` be complex Hilbert spaces, let `D:H->K` be bounded and nonzero, and write

```text
HH = ell2(N;H),   KK = ell2(N;K).
```

Let `S_H,S_K` be the unilateral right shifts.  Thus

```text
(S_H x)_0 = 0,       (S_H x)_(n+1)=x_n,
```

and similarly on `KK`.  For a bounded scalar sequence `a=(a_n)`, define the diagonal formed
operator

```text
A_a = diag(a_n D) : HH -> KK.
```

For `B:HH->KK`, define its shift transgression

```text
delta(B) = B - S_K B S_H*.
```

Put

```text
s_n = sum_(k=0)^n a_k.
```

### Theorem 2.1 -- bounded primitive if and only if partial sums are bounded

The equation

```text
delta(B)=A_a
```

has a bounded solution if and only if

```text
sup_n |s_n| < infinity.
```

More sharply,

\[
 \boxed{
 \inf_{\delta(B)=A_a}\|B\|
   = \|D\|\sup_{n\geq0}\left|\sum_{k=0}^{n}a_k\right|.}
\tag{CTR.1}
\]

#### Proof

Let `I_n:H->HH` insert a vector in coordinate `n`, and let `P_n:KK->K` read coordinate `n`.
Write

```text
B_nn = P_n B I_n.
```

Taking the `(0,0)` block of `delta(B)=A_a` gives

```text
B_00=a_0 D.
```

For `n>=1`, the shift relations give

```text
P_n S_K B S_H* I_n = P_(n-1) B I_(n-1)=B_(n-1,n-1).
```

Hence

```text
B_nn-B_(n-1,n-1)=a_nD,
```

and induction yields

```text
B_nn=s_nD.
```

Every diagonal compression has norm at most `||B||`, so

```text
||B|| >= sup_n ||B_nn|| = ||D|| sup_n |s_n|.
```

Conversely, if the partial sums are bounded, the diagonal operator

```text
B_s=diag(s_nD)
```

is bounded, has norm `||D|| sup_n|s_n|`, and direct substitution gives
`delta(B_s)=A_a`.  This proves existence and the exact minimum. QED.

### Corollary 2.2 -- positive accumulation and open history

If `a_n>=0`, then a bounded primitive exists exactly when `sum_n a_n<infinity`.  For the
homogeneous law `a_n=1`, every primitive has diagonal history

```text
B_nn=(n+1)D,
```

so no bounded primitive exists.  The finite-horizon primitive cost is exactly `(N+1)||D||`.

This is an operator-valued strengthening of the scalar constant-ramp no-go already present in the
corpus: it classifies every bounded amplitude sequence and computes the optimal primitive norm.

## 3. Character law and functional-equation neutrality

Let `z` lie on the unit circle and take

```text
a_n=z^n.
```

Then

\[
 s_n(z)=
 \begin{cases}
   (1-z^{n+1})/(1-z),&z\ne1,\\
   n+1,&z=1.
 \end{cases}
\tag{CTR.2}
\]

### Theorem 3.1 -- neutral-character singularity

1. If `z!=1`, then `A_z` has a bounded shift primitive and
   \[
   \inf_{\delta(B)=A_z}\|B\|
      =\|D\|\sup_n\left|\frac{1-z^{n+1}}{1-z}\right|
      \le \frac{2\|D\|}{|1-z|}.
   \tag{CTR.3}
   \]
2. If `z=1`, no bounded primitive exists.
3. Reflection `z -> z^(-1)=conj(z)` preserves the exact minimum primitive norm.

#### Proof

The first two claims follow from `(CTR.1)` and `(CTR.2)`.  For reflection,

```text
s_n(z^(-1))=z^(-n)s_n(z),
```

so the absolute values agree. QED.

Thus functional-equation reflection is information-neutral at the transgression level: it changes
the phase gauge, not bounded exactifiability or its optimal cost.

### Theorem 3.2 -- global character properness

Let `(z_j)` be any family of nontrivial unit-circle characters.  The family admits primitives with
one uniform norm bound exactly when

```text
inf_j |1-z_j| > 0.
```

In particular, if some subsequence tends to `1`, every member is individually exact but the family
has no uniformly bounded primitive.

#### Proof

A positive lower bound on `|1-z_j|` gives the uniform upper bound in `(CTR.3)`.  Conversely, suppose
`z_j->1`.  For every fixed `N`, continuity gives

```text
s_N(z_j)->N+1.
```

Hence the optimal norms are eventually at least `(N+1)||D||/2`.  Since `N` is arbitrary, no
uniform bound exists.  Compactness of the unit circle shows that failure of a positive gap produces
a subsequence tending to `1`. QED.

This is the first global formation/properness law: local exactness does not survive cofinal phase
formation unless the neutral character is uniformly separated.

## 4. Finite phase packets and the resonance projection

Let `E=C^m` with orthonormal basis `(e_j)`, choose unit phases `z_1,...,z_m`, and set

```text
U e_j = z_j e_j.
```

On `End(E)` define

```text
alpha(X)=U* X U,       delta_U(X)=X-alpha(X).
```

Let `E_jk` be the matrix unit taking `e_k` to `e_j`.  Then

\[
 \alpha(E_{jk})=\bar z_jz_kE_{jk},\qquad
 \delta_U(E_{jk})=(1-\bar z_jz_k)E_{jk}.
\tag{CTR.4}
\]

Define the resonance projection

\[
 \Pi_U(X)_{jk}=
 \begin{cases}
 X_{jk},&z_j=z_k,\\
 0,&z_j\ne z_k.
 \end{cases}
\tag{CTR.5}
\]

Equivalently, if `P_lambda` are the spectral projections of `U`,

```text
Pi_U(X)=sum_lambda P_lambda X P_lambda.
```

### Theorem 4.1 -- exact resonant/exact splitting

There is an orthogonal direct sum for the Hilbert--Schmidt inner product

\[
 \boxed{
 \operatorname{End}(E)
   =\operatorname{ran}\Pi_U\ \oplus\ \operatorname{ran}\delta_U.}
\tag{CTR.6}
\]

More precisely,

```text
ker(delta_U)=ran(Pi_U),
ran(delta_U)=ker(Pi_U).
```

Every `X` has the canonical formation decomposition

\[
 \boxed{X=\Pi_UX+\delta_U G_U(X),}
\tag{CTR.7}
\]

where

\[
 G_U(X)_{jk}=
 \begin{cases}
 (1-\bar z_jz_k)^{-1}X_{jk},&z_j\ne z_k,\\
 0,&z_j=z_k.
 \end{cases}
\tag{CTR.8}
\]

If

```text
g(U)=min_{z_j!=z_k}|1-conj(z_j)z_k|,
```

then on the oscillatory sector

\[
 \boxed{\|G_U\|_{S_2\to S_2}=g(U)^{-1}.}
\tag{CTR.9}
\]

#### Proof

The matrix units form an orthonormal Hilbert--Schmidt basis.  Formula `(CTR.4)` says that
`delta_U` kills exactly the resonant units and multiplies every other unit by a nonzero scalar.
This proves the kernel, range, and orthogonal splitting.  Dividing each nonresonant coefficient by
its multiplier proves `(CTR.7)`--`(CTR.8)`.  The norm of a diagonal multiplier on an orthonormal
basis is the supremum of its coefficient magnitudes, proving `(CTR.9)`. QED.

### Corollary 4.2 -- Cesaro formation

For every `X`,

\[
 \boxed{
 \frac1N\sum_{n=0}^{N-1}\alpha^n(X)\longrightarrow\Pi_U(X).}
\tag{CTR.10}
\]

Indeed, a resonant matrix unit is fixed, while a nonresonant unit is multiplied by a geometric
average tending to zero.

Thus `Pi_U` is not a chosen quotient.  It is the asymptotic packet formed by the phase orbit.

## 5. Positivity creates the resonant survivor

### Theorem 5.1 -- no nonzero positive coboundary

If `X>=0` and `X!=0`, then

```text
Pi_U(X)>=0,     tr(Pi_U(X))=tr(X)>0.
```

Consequently `Pi_U(X)!=0` and `X` is not in `ran(delta_U)`.

#### Proof

Each compression `P_lambda X P_lambda` is positive, so their orthogonal sum is positive.  Block
compression preserves diagonal entries, hence the trace.  A nonzero positive finite-dimensional
operator has positive trace.  The range characterization in Theorem 4.1 now excludes `X` from
`ran(delta_U)`. QED.

### Theorem 5.2 -- phase quotient and transgression do not commute

Let `A_z=diag(z^nD)` as in Section 3.  For `z!=1`, `A_z` has a bounded primitive, but

\[
 \boxed{A_z^*A_z=\operatorname{diag}(D^*D)}
\tag{CTR.11}
\]

has no bounded shift primitive.

More generally,

\[
 \boxed{A_z^*A_w
   =\operatorname{diag}((\bar zw)^nD^*D)}
\tag{CTR.12}
\]

has a bounded primitive exactly when `z!=w`.

#### Proof

Formula `(CTR.11)` follows from `|z|=1`.  Since `D!=0`, also `D*D!=0`; the homogeneous case of
Corollary 2.2 forbids a bounded primitive.  Formula `(CTR.12)` is blockwise multiplication, and
Theorem 3.1 applies to the ratio character `conj(z)w`. QED.

This is the central fusion law:

```text
nontrivial character  --shift transgression--> exact
nontrivial character  --positive self-pair---> neutral nonexact survivor.
```

Positive formation is therefore not merely phase-blind.  It moves data from the exact oscillatory
sector into the obstructed neutral sector.

### Theorem 5.3 -- rank transmutation under phase formation

For `v in E`, put `X_v=vv*`.  Decompose

```text
v=sum_lambda v_lambda,       v_lambda=P_lambda v.
```

Then

\[
 \boxed{\Pi_U(vv^*)=\sum_\lambda v_\lambda v_\lambda^*.}
\tag{CTR.13}
\]

The summands have orthogonal ranges, so

\[
 \boxed{
 \operatorname{rank}\Pi_U(vv^*)
   =\#\{\lambda:v_\lambda\ne0\}.}
\tag{CTR.14}
\]

Moreover

\[
 \boxed{
 \|vv^*\|_{S_2}^2
   =\|\Pi_U(vv^*)\|_{S_2}^2
    +\|(1-\Pi_U)(vv^*)\|_{S_2}^2,}
\tag{CTR.15}
\]

with

\[
 \|\Pi_U(vv^*)\|_{S_2}^2=\sum_\lambda\|v_\lambda\|^4.
\tag{CTR.16}
\]

Thus a rank-one source packet becomes a positive survivor whose rank is the number of phase classes
actually occupied.  Equation `(CTR.15)` is the exact conservation identity: formation does not
destroy Hilbert--Schmidt energy; it separates neutral population from oscillatory coherence.

## 6. Countable packet and closed-range classification

Let `J` be countable, let `E=ell2(J)`, and let

```text
U e_j=z_j e_j,      |z_j|=1.
```

On the Hilbert space `S_2(E)` of Hilbert--Schmidt operators, keep

```text
alpha(X)=U*XU,      delta_U=1-alpha.
```

The matrix units remain an orthonormal basis and `(CTR.4)` remains valid.

### Theorem 6.1 -- global formation/properness

Let `Sigma={z_j:j in J}` be the set of distinct phase values.  Then:

1. `closure(ran(delta_U))=ker(Pi_U)`;
2. `ran(delta_U)` is closed exactly when
   \[
   \inf_{z,w\in\Sigma,\ z\ne w}|1-\bar zw|>0;
   \tag{CTR.17}
   \]
3. because the unit circle is compact, `(CTR.17)` holds exactly when `Sigma` is finite;
4. if `Sigma` is infinite, every finite phase aperture has an exact oscillatory inverse, but the
   cofinal inverse norms diverge and the limiting transgression range is nonclosed.

#### Proof

On the basis `E_jk`, `delta_U` is the scalar multiplier

```text
d_jk=1-conj(z_j)z_k.
```

Finite-support nonresonant matrices lie in the range and are dense in `ker(Pi_U)`, proving item 1.
A diagonal multiplier on `ell2(JxJ)` has closed range exactly when its nonzero coefficients are
bounded away from zero, proving item 2.  An infinite subset of the compact unit circle has distinct
pairs arbitrarily close, so the infimum in `(CTR.17)` is zero.  A finite set has a positive minimum.
This proves item 3.  Formula `(CTR.9)` on finite apertures proves item 4. QED.

### Corollary 6.2 -- cofinal rank/topology prediction

Let `E_N` exhaust a countable phase packet and suppose each new aperture contains a new distinct
phase.  Choose `v` with nonzero component in every phase class.  Then simultaneously:

```text
rank(Pi_(U_N)(v_N v_N*)) -> infinity,
||G_(U_N)||_(S2->S2)     -> infinity,
ran(delta_U)             is nonclosed.
```

This predicts a topological theorem from a reconstruction theorem: unbounded observed phase rank
forces loss of closed-range transgression in the cofinal packet.

No hypertranscendence premise is used.  If a separate source theorem realizes infinitely many
distinct differential characters in this packet, the topology conclusion then follows without
additional analysis.

## 7. Information and common-recovery fusion

For a vector `x in H`, the character-tagged response has constant positive density

\[
 \|z^nDx\|^2=\|Dx\|^2.
\tag{CTR.18}
\]

Hence its finite-horizon positive work is

\[
 \boxed{
 \sum_{n=0}^{N}\|z^nDx\|^2=(N+1)\|Dx\|^2,}
\tag{CTR.19}
\]

even when the signed character packet has a uniformly bounded primitive.  This is the Hilbert
counterpart of the conditional-information conservation law in ULF-OISM-3.

For probability packets, let `(P,Q)` be repeated or conditionally regenerated with positive local
Jeffreys innovation.  The chain rule gives the same cumulative positive law.  Passing both packet
laws through a common recovery kernel with an exact left inverse preserves both directed KL
divergences and therefore preserves the accumulated Jeffreys work.  Functional-equation reflection
only sends each phase ratio to its conjugate; Sections 3--6 show that it preserves:

1. exactifiability;
2. optimal primitive cost;
3. resonance partition;
4. positive survivor rank;
5. small-divisor gap;
6. closed-range status;
7. recovered information separation.

Thus the functional equation is neutral for this entire mechanism.  It is a symmetry of the field
law, not a source of cancellation.

## 8. The new set of laws

ULF-OISM-4 adds six laws to Orbit-Induction Selection Mechanics.

1. **Character exactness.** Every nontrivial phase character is a bounded shift coboundary.
2. **Neutral singularity.** The trivial character has no bounded primitive.
3. **Positive resonance.** Self-pairing sends every character to the trivial character.
4. **Resonant conservation.** Every finite packet splits uniquely into a commutant survivor and an
   exact oscillatory part.
5. **Small-divisor properness.** Infinite phase diversity destroys closed range by crowding the
   neutral character.
6. **Rank/topology transmutation.** The number of occupied phase classes is simultaneously the rank
   of the positive survivor and the source of cofinal inverse blow-up.

These are mechanisms, not route labels.

## 9. Sharp boundaries and hostile audit

1. **This is not a proof of RH.** A literal source still must identify its physical parameter with a
   phase packet and prove which global admission is required.
2. **Nonexact need not mean physical.** The theorem identifies the neutral survivor; it does not
   decree that physical laws must select it.
3. **Positivity is not always a phase quotient.** The theorem concerns Gram/self-pair formation or
   the spectral pinching it generates.  A faithful positive identity map loses nothing.
4. **Finite phase diversity has closed range.** Large finite rank alone does not create a topology
   wall; the wall is cofinal phase crowding.
5. **Continuous spectrum needs a spectral-measure version.** The countable theorem is pure-point.
6. **The inverse is topology-dependent.** `(CTR.9)` is Hilbert--Schmidt.  Operator-norm Schur
   multiplier bounds require separate hypotheses.
7. **Oscillatory cancellation is signed.** Absolute values, squared norms, KL divergence, and Gram
   formation remove it and recover the neutral positive accumulation.
8. **Classical parents are acknowledged.** Geometric sums, the mean ergodic projection, spectral
   pinching, and diagonal-multiplier closed-range criteria are classical.  Field content is their
   coupled interpretation as one formation/transgression/properness mechanism.

The closest direct operator parent found in the hostile search is
[Badea--Devys, *Rochberg's abstract coboundary theorem revisited*](https://arxiv.org/abs/2209.15124),
which studies solvability of `(1-T)y=x` for isometries through partial-sum growth.  It supports the
coboundary side of Theorem 2.1 but does not couple it to positive Gram resonance, commutant rank,
or countable phase-packet range closure.  Current categorical work on generalized inverses of
quantum channels, such as
[Cockett--Pacaud Lemay--Srinivasan (2026)](https://arxiv.org/abs/2603.13946),
likewise treats recovery maps, not the character-to-positive-resonance transmutation.  No isolated
novelty claim is made; the exact coupled mechanism is the programme contribution.

## 10. Lean status

Paper proof is dependency-closed.  No Lean file is written under the active read-only formal audit.
Read-only audit found the exact reusable infrastructure:

1. `HTGeometry.HilbertSchmidtMatrix` supplies the `ell2` kernel/operator bridge, canonical Hilbert
   basis, matrix recovery, and Hilbert--Schmidt norm identities;
2. `HTGeometry.HilbertClosedRange` supplies closed range if and only if a transverse lower bound;
3. `RHTower.PhysicalCutoffConnectedCoareaSuccessor` already formalizes constant-step primitive
   growth and the scalar no-bounded-primitive theorem;
4. `HTGeometry.ConstitutiveFunctionalEquationPacketLift` supplies the existing
   functional-equation common-recovery lift and information isometry.

Missing reusable layer:

1. a bounded unilateral shift on vector-valued `ell2` with coordinate compression lemmas;
2. `delta_U=1-Ad_U` on the Hilbert--Schmidt kernel model;
3. finite and countable resonance projections;
4. the diagonal-multiplier range-closure specialization of `HilbertClosedRange`.

No Lean process was started and no formal file was modified under the active read-only formal
audit.  Status remains `[LEAN-PENDING]`.
