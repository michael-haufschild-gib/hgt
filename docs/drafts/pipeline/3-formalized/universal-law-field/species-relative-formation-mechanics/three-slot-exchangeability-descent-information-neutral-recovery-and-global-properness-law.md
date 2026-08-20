# Three-slot exchangeability descent, information-neutral recovery, and global properness law

**ID:** ULF-SRFM-6  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [THREE-ORGAN FUSION]`
`[FUNCTIONAL-EQUATION NEUTRALITY SURVIVES] [GLOBAL FORMATION PROPERNESS]`
`[LEAN CLOSED] [SOURCE-LANDING OPEN] [NOT RH]`

## 1. Purpose

The source-natural functional-equation history alternates two reflected formation laws.  One clock
shift exchanges its two phases for every parameter, so shift covariance, two-step recurrence,
endpoint recovery, and entropy conservation cannot select the reflection fixed point.

This card isolates a stronger formation law which those operations do not test:

> repeated formation slots of one declared species must descend from ordered slots to
> indistinguishable slots.

For an alternating reflected formation, three slots are the first place where this descent can be
tested after functional-equation orbit symmetrization.  The resulting permutation defect is an
exact square.  Before symmetrization its information cost is exactly Jeffreys divergence.  Common
recovery preserves the cost, and independent formation depth makes it additive.  Consequently a
uniform global work bound forces equality of the reflected laws.

The theorem is a mechanism and an acceptance gate, not an RH proof.  The remaining arithmetic task
is to prove that the literal pre-zero HGT formation really has the required indistinguishable-slot
descent.  Declaring exchangeability after seeing the critical line would be circular.

## 2. Finite formation laws

Let (A) be a finite nonempty alphabet.  Let (p,q:A\to(0,1)) be strictly positive probability
weights:

\[
 \sum_{a\in A}p_a=\sum_{a\in A}q_a=1.
 \tag{EFD.1}
\]

They model two functional-equation phases.  Define the two ordered three-slot laws

\[
 \alpha(i,j,k)=p_iq_jp_k,
 \qquad
 \beta(i,j,k)=p_ip_jq_k.
 \tag{EFD.2}
\]

Thus (eta) is obtained from (alpha) by the adjacent transposition of slots (2,3).  Write

\[
 D(r\Vert s)=\sum_x r_x\log\frac{r_x}{s_x},
 \qquad
 J(p,q)=D(p\Vert q)+D(q\Vert p).
 \tag{EFD.3}
\]

### Theorem 2.1 -- permutation information identity

\[
 \boxed{D(\alpha\Vert\beta)=J(p,q).}
 \tag{EFD.4}
\]

The same identity holds after functional-equation reflection (p\leftrightarrow q).

#### Proof

Using positivity and `(EFD.1)`,

\[
\begin{aligned}
D(\alpha\Vert\beta)
 &=\sum_{i,j,k}p_iq_jp_k
   \log\frac{p_iq_jp_k}{p_ip_jq_k}\\
 &=\sum_{i,j,k}p_iq_jp_k
   \left(\log\frac{q_j}{p_j}+\log\frac{p_k}{q_k}\right)\\
 &=D(q\Vert p)+D(p\Vert q).
\end{aligned}
\]

Swapping (p,q) interchanges the two summands and leaves their sum fixed. ∎

### Corollary 2.2 -- strict zero locus

\[
 D(\alpha\Vert\beta)=0\quad\Longleftrightarrow\quad p=q.
 \tag{EFD.5}
\]

This is Gibbs' equality case applied to the two terms in `(EFD.4)`.

## 3. Functional-equation orbit symmetrization does not erase the defect

Let

\[
 \alpha^\theta=q\otimes p\otimes q,
 \qquad
 \overline\alpha=\frac12(\alpha+\alpha^\theta).
 \tag{EFD.6}
\]

The two-slot analogue

\[
 \frac12(p\otimes q+q\otimes p)
 \tag{EFD.7}
\]

is automatically invariant under its only transposition.  Thus two slots cannot distinguish an
off-centre reflected pair after orbit symmetrization.

Fix a subset (E\subseteq A), and put

\[
 u=p(E),\qquad v=q(E).
 \tag{EFD.8}
\]

Under (overline\alpha), the cylinder probabilities are

\[
\begin{aligned}
 \overline\alpha(E,E,E^c)
   &=\frac12\bigl(uv(1-u)+vu(1-v)\bigr),\\
 \overline\alpha(E,E^c,E)
   &=\frac12\bigl(u^2(1-v)+v^2(1-u)\bigr).
\end{aligned}
\tag{EFD.9}
\]

### Theorem 3.1 -- minimal symmetrized exchangeability defect

The transposition of slots (2,3) has exact cylinder defect

\[
 \boxed{
 \overline\alpha(E,E^c,E)-\overline\alpha(E,E,E^c)
 =\frac12\bigl(p(E)-q(E)\bigr)^2.}
 \tag{EFD.10}
\]

Hence (overline\alpha) is invariant under that transposition if and only if (p=q).  Therefore
three slots are minimal for detecting the reflected phase after orbit symmetrization.

#### Proof

Expanding `(EFD.9)` gives

\[
 \frac12\left(u^2+v^2-2uv\right)=\frac12(u-v)^2.
\]

If the transposition preserves (overline\alpha), `(EFD.10)` vanishes for every (E\), so
(p(E)=q(E)) for every subset and (p=q).  The converse is immediate.  Two-slot minimality is
`(EFD.7)`. ∎

The key point is that functional-equation averaging removes the phase label but not the three-slot
formation schedule.  Shift recurrence and exchangeability are different laws.

### Theorem 3.2 -- thinning/spreadability is already sufficient

Full permutation exchangeability is stronger than needed.  Consider the orbit-symmetrized
alternating history and one event (E), with (u=p(E)), (v=q(E)).  Two adjacent retained slots
have coincidence probability

\[
 C_{12}(E)=\frac12(uv+vu)=uv,
 \tag{EFD.10a}
\]

whereas deleting the middle slot and retaining positions (1,3) gives

\[
 C_{13}(E)=\frac12(u^2+v^2).
 \tag{EFD.10b}
\]

Therefore

\[
 \boxed{C_{13}(E)-C_{12}(E)=\frac12(p(E)-q(E))^2.}
 \tag{EFD.10c}
\]

Consequently the phase-averaged alternating process is spreadable under this single deletion test
if and only if (p=q).  Stationarity under shifts is automatic for every reflected pair, but
formation-thinning consistency forces neutrality.

#### Proof

The two phase choices give (p\otimes q,q\otimes p) on adjacent slots and
(p\otimes p,q\otimes q) on equal-parity slots.  Subtracting their coincidence probabilities gives

\[
 \frac12(u^2+v^2)-uv=\frac12(u-v)^2.
\]

Vanishing for every (E) is equivalent to (p=q). ∎

This is the sharper source gate.  It replaces the broad request for exchangeability by a concrete
commutation law between two source operations: functional-equation phase averaging and deletion of
an unobserved formation slot.

### Theorem 3.3 -- coordinate-free formation-interchange factorization

The scalar square is the evaluation of one tensor law.  Let (V) be a module over a commutative
ring in which the two reflected formed states are (p,q\in V).  Define the skipped and adjacent
orbit packets without normalization by

\[
 S(p,q)=p\otimes p+q\otimes q,
 \qquad
 A(p,q)=p\otimes q+q\otimes p.
 \tag{EFD.10d}
\]

Then

\[
 \boxed{S(p,q)-A(p,q)=(p-q)\otimes(p-q).}
 \tag{EFD.10e}
\]

#### Proof

Bilinearity gives

\[
 (p-q)\otimes(p-q)
 =p\otimes p-p\otimes q-q\otimes p+q\otimes q.
\]

Rearranging proves `(EFD.10e)`. ∎

This is the genuine fusion law.  Functional-equation reflection exchanges (p,q), hence negates
the unsquared difference but fixes its tensor square.  Tensor formation turns the invisible
reflection-odd direction into a positive rank-one reporter after applying any real linear probe
(arphi\):

\[
 (\varphi\otimes\varphi)(S-A)=(\varphi(p)-\varphi(q))^2.
 \tag{EFD.10f}
\]

Every common linear recovery map transports `(EFD.10e)` naturally.  A jointly separating recovery
family reconstructs (p=q) from vanishing of all such squares.  Thus phase quotient, positive
response, thinning defect, and joint reconstruction are four shadows of one factorization, not four
independent axioms.

### Corollary 3.4 -- fourth-organ positive reporter prediction

For every real linear reporter (arphi:V\to\mathbb R), define

\[
 \mathcal G_\varphi(p,q)
 =\varphi(p)^2+\varphi(q)^2-2\varphi(p)\varphi(q).
 \tag{EFD.10g}
\]

Then

\[
 \boxed{
 \mathcal G_\varphi(p,q)=(\varphi(p)-\varphi(q))^2\ge0,}
 \qquad
 \mathcal G_\varphi(p,q)=0\Longleftrightarrow\varphi(p)=\varphi(q).
 \tag{EFD.10h}
\]

This is the theorem predicted in the positive/Gram organ by the formation-interchange identity.  It
was not used to define the tensor law.  A separating reporter family converts simultaneous Gram
vanishing into (p=q); one reporter only identifies its own quotient.

## 4. Common recovery is information-neutral

Let (K(a,dh)) be any common Markov recovery kernel.  Form every slot by retaining its visible
letter and adjoining an independent conditional recovery coordinate with law (K).  Denote the
formed triple laws by (widehat\alpha,widehat\beta).

### Theorem 4.1 -- recovery neutrality

\[
 \boxed{D(\widehat\alpha\Vert\widehat\beta)
       =D(\alpha\Vert\beta)=J(p,q).}
 \tag{EFD.11}
\]

#### Proof

Conditioned on the visible triple, both formed laws use the same product recovery kernel
(K^{\otimes3}).  The KL chain rule therefore has zero conditional term.  Projection to the visible
triple gives the reverse data-processing inequality, so equality is exact. ∎

Thus the functional-equation action can lift through the common recovery kernel without changing
information.  Recovery neither creates nor cancels the exchangeability defect.

## 5. Global formation properness

For (m\ge0), form (m) independent copies of the ordered three-slot experiment:

\[
 \alpha_m=\alpha^{\otimes m},
 \qquad
 \beta_m=\beta^{\otimes m}.
 \tag{EFD.12}
\]

Define the complete exchangeability work

\[
 \mathcal W_m(p,q)=D(\alpha_m\Vert\beta_m).
 \tag{EFD.13}
\]

### Theorem 5.1 -- exact conservation and properness

For all (m,n\in\mathbb N),

\[
 \boxed{
 \mathcal W_m=mJ(p,q),
 \qquad
 \mathcal W_{m+n}=\mathcal W_m+\mathcal W_n.}
 \tag{EFD.14}
\]

Consequently

\[
 \boxed{
 \left(\exists C<\infty\;\forall m,\ \mathcal W_m\le C\right)
 \Longleftrightarrow p=q.}
 \tag{EFD.15}
\]

The same statements hold after common recovery formation.

#### Proof

Relative entropy tensorizes over independent products.  Apply Theorem 2.1 to every block to obtain
`(EFD.14)`.  If (p=q), every work is zero.  If (p\ne q), strict Gibbs inequality gives
(J(p,q)>0), so (mJ(p,q)\to\infty).  The recovery statement follows blockwise from Theorem 4.1.
∎

This is the required global formation/properness theorem: bounded work across unbounded formation
depth is possible exactly on the exchangeable locus.

## 6. Reflection-family selection and fourth-organ prediction

Let (x\mapsto p_x) be a family with involution (x\mapsto-x), and assume it is
**reflection-separating**:

\[
 p_x=p_{-x}\quad\Longleftrightarrow\quad x=0.
 \tag{EFD.16}
\]

Set (p=p_x, q=p_{-x}).  The preceding results give

\[
 \boxed{
 \text{three-slot exchangeability}
 \Longleftrightarrow
 \sup_m\mathcal W_m<\infty
 \Longleftrightarrow
 x=0.}
 \tag{EFD.17}
\]

This predicts a theorem in the history organ which endpoint, entropy, and recurrence analyses miss:

> An off-centre source-natural alternating history can be exactly two-periodic under the
> functional-equation phase shift while its three-coordinate orbit law fails finite-permutation
> exchangeability.  A single cylinder reporter measures the failure as
> (rac12(p_x(E)-p_{-x}(E))^2).

For example, on a binary alphabet with

\[
 p_x(1)=\frac{e^x}{1+e^x},
 \qquad
 p_x(0)=\frac1{1+e^x},
 \tag{EFD.18}
\]

one has (p_x=p_{-x}) exactly at (x=0).

## 7. Mechanism grammar

The theorem fuses four previously separate organs:

| organ | law |
|---|---|
| functional equation | swaps (p,q); orbit average removes phase label |
| formation species | indistinguishable slots demand permutation descent |
| information/recovery | schedule cost is (J(p,q)) and survives common recovery exactly |
| history/properness | each new independent block adds the same work; bounded global work forces neutrality |

The conservation identity is not another scalar fitted to one route.  It is generated by the
composition law for independent formation and the symmetric-group action on slots.

## 8. Hostile boundaries

1. **Exchangeability is not automatic.**  Chronological slots are distinguishable.  The theorem
   selects only after a source theorem proves that the relevant formation slots belong to one
   indistinguishable species.
2. **Arbitrary exchangeable mixtures do not select.**  The de Finetti mixture
   (rac12p^{\otimes\infty}+\frac12q^{\otimes\infty}) is exchangeable for (p\ne q).  The
   load-bearing object is the source-generated alternating formation, not an arbitrary law with the
   same one-slot marginals.
3. **Two slots are blind after orbit averaging.**  Equation `(EFD.7)` explains why a binary symmetry
   test regresses to functional-equation neutrality.  Three slots are minimal.
4. **Common recovery is not a selector.**  It preserves the defect.  Selection comes from formation
   descent plus global bounded work.
5. **Reflection separation is necessary.**  A family with (p_x=p_{-x}) off the fixed locus cannot
   be selected by this mechanism.
6. **No RH claim.**  The theorem does not yet prove that the rational-adelic, theta, Euler-shell, or
   divisor source supplies exchangeable alternating slots before zero specialization.

## 9. Exact open source gate

To convert `(EFD.17)` into an RH selection law, construct a pre-zero formation functor

\[
 \mathfrak F:\text{HGT source histories}\longrightarrow
 \text{species-labelled probability histories}
 \tag{EFD.19}
\]

with all four properties proved independently of any Xi zero:

1. functional equation acts by the alternating phase swap (p_x\leftrightarrow p_{-x});
2. common recovery is the already formalized information-neutral packet lift;
3. formation commutes with deletion/thinning of an unobserved slot, equivalently the adjacent and
   one-deletion two-slot laws agree; full indistinguishable-slot exchangeability is a stronger
   sufficient form;
4. cofinal source formation supplies unbounded independent block depth while total admitted work is
   uniformly bounded or conserved.

Theorems 3.1 and 5.1 then force (p_x=p_{-x}).  A coefficient-faithful reflection-separating landing
would force (x=0), hence the critical line.  Properties 3 and 4 are the literal formation and
properness gates; they cannot be inserted as observer axioms.

## 10. Lean certificate

The unconditional algebraic core is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection`:

- exact three-slot orbit-cylinder square;
- exact adjacent-versus-skipped thinning square;
- coordinate-free rank-one tensor factorization;
- positive linear-reporter square and exact zero locus;
- equality iff reflected event masses agree;
- reflection invariance;
- additive depth work;
- bounded-depth properness iff equality.

Scratch elaboration, direct leaf elaboration, and one targeted leaf build pass.  No umbrella, area,
or project build was run.  A scratch `#print axioms` audit of all capstones reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The module is wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField` without building that umbrella.  Repository lint
reports six unrelated pre-existing umbrella-ownership failures and no defect in this module.

The measure-level results `(EFD.4)`, `(EFD.5)`, `(EFD.11)`, `(EFD.14)`, `(EFD.15)`, `(EFD.17)` and
`(EFD.18)` are closed in
`GaloisForLFunctions.HTGeometry.ThreeSlotExchangeabilityInformation`, on top of the new
`klDiv_prod` / `klDiv_pi` product-additivity lemmas.  See the companion `...-formalized.md`.

## Log

- 2026-08-18 — Derived after the frozen alternating-history selector was falsified by exact shift
  transport.  Corpus search found common-recovery information neutrality, alternating recurrence,
  and generic Jeffreys properness, but no three-slot exchangeability descent theorem.  Two-slot
  phase averaging was proved blind; three-slot orbit-cylinder defect and global work law proved.
- 2026-08-18 — Lean formalization completed.  Scratch, direct leaf, targeted leaf, and axiom audits
  pass; umbrella import wired without an umbrella build.
