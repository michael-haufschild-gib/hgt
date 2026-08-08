# Framed provenance curvature and universal scalar no-go

- **ID:** `framed-provenance-curvature-scalar-no-go`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NO-GO / POSITIVE SURVIVOR / CONSTRAINT RELATIVITY
- **Scientific status:** `[PAPER-PROVED] [NO LEAN WRITTEN OR BUILT] [NOT RH]`
- **Novelty status:** finite-lattice proof is elementary. Its field-level consequence is
  candidate-new: completion curvature must be source-framed, oriented, and provenance-valued;
  scalar energy or complexity is a chosen observer pairing and cannot be primitive.
- **Parent:**
  `../../1-in-progress/constraint-relativity/constraint-relativity-and-relation-completion-spacetime.md`.

## 1. Purpose

This card attacks the strongest tempting scalar formulation of Constraint Relativity.

Suppose completion transport has a comparison defect. Can one assign it a canonical finite scalar
which is faithful, presentation-invariant, exactly additive under composition, and decreases under
all admissible processing?

No. Two independent countertheorems hold already for finite chains.

1. The completed nucleus alone forgets whether raw transport was flat.
2. Even when the comparison interval is retained, no finite faithful scalar is both chain-additive
   and data-processing for all bottom-preserving finite-join maps.

The strongest positive survivor is a universal oriented provenance class. Every additive scalar
factors through it after an observer chooses a potential/valuation.

## 2. Completion compositors

Let `L,M,K` be finite lattices with closure operators `c_L,c_M,c_K`. For a closed `x in L` and
monotone transports

\[
 T:L\to M,
 \qquad
 V:M\to K,
 \tag{2.1}
\]

put

\[
 \bar T(x)=c_MT(x).
\]

The completion compositor is the ordered comparison

\[
 \omega_{V,T,x}:
 \underbrace{c_KVT(x)}_{\alpha}
 \le
 \underbrace{c_KV c_MT(x)}_{\beta}.
 \tag{2.2}
\]

It is flat at `x` exactly when `alpha=beta`.

### Lemma 2.1 — every finite interval is a completion defect

Let `a<=b` in a finite lattice `K`. There are finite chains, closures, and bottom-preserving join
maps for which `(2.2)` is exactly `a<=b`.

#### Proof

Take `C_2={0<1}` and `C_3={0<p<q}`. On `C_3`, define

\[
 c(0)=0,
 \qquad c(p)=q,
 \qquad c(q)=q.
\]

Let `T:C_2->C_3` send `1` to `p`, and let `V:C_3->K` send `0` to `0`, `p` to `a`, and `q` to
`b`. At `x=1`, raw then completed transport gives `a`, while intermediate completion then
transport gives `b`. QED.

Thus a universal scalar on completion defects induces a scalar on every comparable pair in every
finite lattice.

## 3. Nucleus-only invariance erases flatness

### Theorem 3.1 — Morita-collapse countermodel

BC-flatness is not invariant under any equivalence retaining only the fixed-point nucleus and
induced maps between completed objects.

#### Proof

Use `C_3` and closure `c` from Lemma 2.1. Its nucleus is

\[
 N(c)=\{0,q\}\cong C_2.
\]

Let the target be `C_2` and choose

\[
 V(0)=0,
 \qquad V(p)=0,
 \qquad V(q)=1.
\]

At source point `1`, the original raw/completed comparison is

\[
 VT(1)=0<1=VcT(1),
\]

so the compositor is nonflat. Replace the intermediate presentation by its nucleus with identity
closure. The induced completed legs send `1` to `q` to `1`; raw and completed composites now agree.
The nucleus and induced completed map are unchanged, but flatness changed. QED.

### Positive conclusion

A flatness invariant must retain at least

\[
 (P,c,\eta:P\to N(c))
 \tag{3.1}
\]

together with raw transport and its comparison cell. The closure unit `eta` is not expendable
presentation syntax. It records which raw relation event produced the completed object. Call an
equivalence preserving this data **source-framed equivalence**.

## 4. Additive scalars are potentials

Let a scalar endpoint divergence assign

\[
 D_L(x,y)\in\mathbb R_{\ge0}
 \qquad(x\le y)
 \tag{4.1}
\]

and suppose

\[
 D_L(x,z)=D_L(x,y)+D_L(y,z)
 \qquad(x\le y\le z).
 \tag{4.2}
\]

### Theorem 4.1 — potential classification

Every chain-additive divergence has the form

\[
 \boxed{D_L(x,y)=v_L(y)-v_L(x)}
 \tag{4.3}
\]

for `v_L(x)=D_L(0,x)`. It is faithful, `D_L(x,y)=0 iff x=y`, exactly when `v_L` is strictly
order-preserving.

#### Proof

Additivity on `0<=x<=y` gives

\[
 D_L(0,y)=D_L(0,x)+D_L(x,y),
\]

which is `(4.3)`. Faithfulness is equivalent to strict increase along every strict comparable
pair. The converse is immediate. QED.

Therefore a scalar cost is precisely an observer-chosen potential. Relation completion does not
fix its scale or declare which processing maps are nonexpansive.

## 5. Universal scalar data-processing is impossible

Suppose additionally that every bottom-preserving finite-join map `f:L->M` obeys

\[
 D_M(fx,fy)\le D_L(x,y).
 \tag{5.1}
\]

### Theorem 5.1 — sharp scalar no-go

No family on all finite lattices can be simultaneously finite, faithful, chain-additive, and
data-processing under all bottom-preserving finite-join maps. Failure occurs on `C_2` and `C_3`.

#### Proof

Let

\[
 C_2=\{0<1\},
 \qquad
 C_3=\{0<a<1\},
 \qquad
 \delta=D_{C_2}(0,1)>0.
\]

There are join maps embedding `C_2` as the interval `0<1` of `C_3` and retracting `C_3` back by
sending `a` to `0`. Data processing in both directions forces

\[
 D_{C_3}(0,1)=\delta.
 \tag{5.2}
\]

There are also join maps embedding `C_2` as `0<a` and retracting by sending both `a` and `1` to
`1`. Data processing in both directions forces

\[
 D_{C_3}(0,a)=\delta.
 \tag{5.3}
\]

Additivity along `0<a<1` now gives

\[
 \delta
 =D_{C_3}(0,1)
 =D_{C_3}(0,a)+D_{C_3}(a,1)
 =\delta+D_{C_3}(a,1).
\]

Therefore `D_C3(a,1)=0`, contradicting faithfulness. QED.

Allowing infinity evades subtraction only by permitting the useless invariant which assigns
infinite cost to every nonflat defect.

## 6. Universal positive survivor

For a finite lattice `L`, define the free abelian provenance group

\[
 \mathcal U(L)=\mathbb Z^{L\setminus\{0\}},
 \tag{6.1}
\]

with generators `e_x` and `e_0=0`. For `x<=y`, put

\[
 \boxed{J_L(x,y)=e_y-e_x.}
 \tag{6.2}
\]

### Theorem 6.1 — oriented universal provenance class

The class `J` satisfies:

\[
 J_L(x,y)=0\Longleftrightarrow x=y,
 \tag{6.3}
\]

\[
 J_L(x,z)=J_L(x,y)+J_L(y,z),
 \tag{6.4}
\]

and every bottom-preserving map `f:L->M` induces `U(f)e_x=e_f(x)` with

\[
 \mathcal U(f)J_L(x,y)=J_M(fx,fy).
 \tag{6.5}
\]

Every real-valued additive divergence factors through `J`.

#### Proof

Equations `(6.3)`--`(6.5)` follow from the free basis. For an additive divergence, Theorem 4.1
gives a potential `v_L`. Define `lambda_L:U(L)->R` by `lambda_L(e_x)=v_L(x)`. Then

\[
 D_L(x,y)=\lambda_L(J_L(x,y)).
 \tag{6.6}
\]

Uniqueness holds after the normalization `v_L(0)=0`. QED.

Thus canonical datum is oriented defect `J`, not its magnitude. A metric, energy, entropy, or
complexity is an observer state `lambda` paired with it.

For the sought field, the free group must be replaced by a provenance module generated by raw
relation creation/loss events, quotiented by completion squares and higher composition laws. The
finite theorem fixes the architecture but not that higher object.

## 7. Required extra structure

Four additions are logically independent.

1. **Flatness:** retain raw closure units and comparison provenance; nucleus-only equivalence is
   too coarse.
2. **Scalar cost:** choose a positive observer state `lambda` on the provenance object.
3. **Data processing:** restrict processing maps to those nonexpansive for `lambda`; all join maps
   cannot qualify.
4. **Time arrow:** add a probability law, directed dynamics, or irreversible structure. Order and
   completion alone supply no statistical second law.

This explains why Brown--Susskind complexity legitimately depends on a gate set, penalties,
initial state, Hamiltonian path, and typicality. It should not be invariant under arbitrary
relation-language changes.

## 8. Corpus interpretation

The current RH corpus has one oriented horizontal source-isogeny class and several positive or
scalar shadows. Theorem 5.1 forbids treating any canonical positive scalar as the primitive class.
The correct order is

\[
 \boxed{
 \text{source-framed oriented provenance}
 \xrightarrow{\text{observer state}}
 \text{metric/energy/complexity shadow}.}
 \tag{8.1}
\]

The one-port Stokes square can be a pairing of the horizontal class only after a
coefficient-faithful source framing proves that factorization. Equating them from their common
zero set is circular.

For RH, mathematical target remains annihilation of the oriented horizontal class or admission
of its source primitive, not minimization of its norm.

For hypertranscendence, finite jets are observer pairings of a pro-provenance tail. Agreement of
every finite scalar pairing need not identify the completed tail. This is a programmatic
interpretation, not yet a classification theorem.

## 9. Framed provenance curvature conjecture

There exists a source-framed higher category of heterogeneous relation completions carrying a
universal oriented class

\[
 \mathfrak K(\omega)\in K_{\mathrm{prov}}
 \tag{9.1}
\]

such that:

1. `K(omega)=0` exactly for framed BC-flat transport;
2. it is invariant under source-preserving framed equivalence;
3. triple composition gives an exact nonabelian cocycle or pentagon law;
4. every operational divergence factors as
   \[
   D_\lambda(\omega)=\lambda(\mathfrak K(\omega));
   \tag{9.2}
   \]
5. no positive state `lambda` is canonical across all frames;
6. the RH one-port energy is a one-dimensional polarized shadow of an arithmetic provenance
   class;
7. Brown--Susskind growth appears only after choosing local cost and proving a large-deviation
   drift theorem compatible with recurrence.

### Fatal tests

Retire this conjecture if:

1. source-framed localization still erases `K`;
2. `K` reduces to endpoint rank difference;
3. no scalar pairing gives independent operational lower bounds;
4. the horizontal one-port energy does not factor through a coefficient-faithful oriented source
   class;
5. higher composition supplies no invariant beyond an ordinary free difference group.

## 10. Lean handoff notes

No Lean code was written or built. A later formalization can begin with finite chains, closure
operators, and the potential classification. The higher provenance object `(9.1)` is conjectural
and must not be encoded as an axiom.
