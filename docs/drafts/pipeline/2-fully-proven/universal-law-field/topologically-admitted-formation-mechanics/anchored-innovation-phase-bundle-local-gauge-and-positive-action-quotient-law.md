# Anchored innovation phase bundle, local gauge, and positive-action quotient law

- **ID:** ULF-TAFM-18
- **Stage:** 2-fully-proven
- **Type:** universal reconstruction and obstruction theorem
- **Parents:** ULF-TAFM-15 through ULF-TAFM-17
- **Status:** dependency-closed paper proof; Lean formalisation complete

## 1. Mechanism

The completed formation action does not forget only one global functional-equation sign.  It
forgets one independent sign at every scale.  The correct field object is therefore an anchored
affine history bundle over the full innovation-current space, with the pointwise sign group acting
on its fibres.

For an anchor `a in R` and a current `r : N -> R`, put

\[
 P_{a,r}(N)=a+\sum_{k=2}^{N-1}\frac{r_k}{k+2}
 \tag{IPB.1}
\]

and let `H_{a,r}` be the unique anchored history reconstructed from this potential by

\[
 H_{a,r}(2)=P_{a,r}(2),\qquad
 H_{a,r}(n)=(n+1)P_{a,r}(n)-nP_{a,r}(n-1)\quad(n\ge3).
 \tag{IPB.2}
\]

This construction is not an endpoint receiver.  It is the coordinate-free recovery kernel between
the three presentations of one formation field: anchor plus current, potential, and open history.

## 2. Joint reconstruction

### Theorem 2.1 -- anchor-current/history equivalence

For every `N>=2`,

\[
 \overline H_{a,r}(N)=P_{a,r}(N),\qquad
 \mathcal I_N(H_{a,r})=r_N,
 \tag{IPB.3}
\]

where `overline H` is the anchored Cesaro potential and `mathcal I_N` its weighted high-pass.
Conversely every history `h` satisfies

\[
 h_n=H_{h_2,\mathcal I(h)}(n)\qquad(n\ge2).
 \tag{IPB.4}
\]

Thus anchor plus all innovations jointly reconstruct the history, and the only kernel of the
current projection is the constant-history gauge.

#### Proof

The finite-sum primitive obeys

\[
 P_{a,r}(N+1)-P_{a,r}(N)=\frac{r_N}{N+2}.
\]

The ULF-TAFM-17 potential/history recovery theorem gives the first identity in `(IPB.3)`; its
weighted-potential-increment theorem gives the second.  For an arbitrary history, harmonic
holonomy reconstructs its potential from `h_2` and the currents `mathcal I_N(h)`.  The uniqueness
part of ULF-TAFM-17 then gives `(IPB.4)`.  QED.

## 3. Positive action and its exact phase quotient

Define

\[
 \mathcal A_N(r)=\sum_{k=2}^{N-1}\frac{k+1}{k+2}r_k^2.
 \tag{IPB.5}
\]

### Theorem 3.1 -- action is quadratic variation of the recovered history

For every `N>=2`,

\[
 \operatorname{Var}_N(H_{a,r})=\mathcal A_N(r),
 \qquad
 \mathcal A_{N+1}(r)-\mathcal A_N(r)
   =\frac{N+1}{N+2}r_N^2.
 \tag{IPB.6}
\]

#### Proof

Both sides vanish at `N=2`.  The online variance law for the reconstructed history and `(IPB.3)`
show that both sides acquire the same successor term.  Induction proves the first identity; the
second is the last summand of the finite sum.  QED.

Let a local phase gauge be any `epsilon : N -> R` satisfying `epsilon_N^2=1`, acting by

\[
 (\epsilon\cdot r)_N=\epsilon_Nr_N.
 \tag{IPB.7}
\]

### Theorem 3.2 -- exact local-gauge invariance

For every such `epsilon`,

\[
 \mathcal A_N(\epsilon\cdot r)=\mathcal A_N(r)
 \quad\text{for every }N,
 \tag{IPB.8}
\]

while recovery remains equivariant:

\[
 \mathcal I_N(H_{a,\epsilon\cdot r})=\epsilon_Nr_N.
 \tag{IPB.9}
\]

The constant gauge `epsilon=-1` is the global functional-equation reflection.  But `(IPB.8)` is
strictly stronger: positive action is invariant under independent scale-by-scale reflections.

If `r_m != 0`, the gauge which is `-1` only at `m` produces a different recovered history with the
same action at every depth.  Hence no family of diagonal production energies can reconstruct
source orientation, even when the recovery kernel is exact and information-neutral.

#### Proof

Equation `(IPB.9)` is Theorem 2.1 applied to `epsilon*r`.  In `(IPB.5)`, each transformed summand
contains `(epsilon_k r_k)^2=epsilon_k^2 r_k^2=r_k^2`, proving `(IPB.8)`.  A one-site flip changes the
`m`th recovered innovation from `r_m` to `-r_m`; equality of the two histories would make those
currents equal and force `r_m=0`, contradiction.  QED.

## 4. Orientation connection

For a sign gauge define adjacent holonomy

\[
 \omega_N=\epsilon_{N+1}\epsilon_N.
 \tag{IPB.10}
\]

One anchored sign and all adjacent holonomies reconstruct every later sign recursively by
`epsilon_{N+1}=omega_N epsilon_N`.  Positive action records none of this connection.  Global FE
reflection changes the anchored sign but leaves every `omega_N` fixed.  Thus:

- positivity is the quotient by the full local phase gauge;
- FE is only its constant subgroup;
- source orientation is a connection/parallel-transport law between successive innovations;
- a phase no-go is failure to construct that source connection, not lack of another square.

This is the precise higher-law meaning of the corpus-wide observation that diagonal positivity,
unitary reflection, and exact recovery can coexist with unresolved orientation.

## 5. Literal Suzuki consequence

Put

\[
 r_N=S_{N+1},
\]

where `S_{N+1}` is the literal completed Suzuki Abel source from ULF-TAFM-15--17, and anchor at the
completed Suzuki potential at scale two.  The resulting recovered history is the canonical Suzuki
history.  For every local sign gauge `epsilon`, the gauge-recovered history has innovation
`epsilon_N S_{N+1}` but exactly the same:

1. local formation-energy production;
2. accumulated variance action;
3. conditioned aligned-Gamma energy wherever the outgoing charge is nonzero.

Therefore Gamma/Cartan/positive-action receivers see the orbit of the literal source under the
entire local sign gauge, not merely its FE pair.  A source theorem that uses only those positive
readouts cannot prove signed order.  It must either construct adjacent innovation holonomy from
prime--polar--Gamma formation, or control the already-oriented literal current before phase
quotient.

This does **not** replace the remaining magnitude theorem.  In the RG/CCM-FU fusion the literal
source already fixes the signs; RH still requires a uniform bound on their magnitudes.  The theorem
prevents a false pivot back to FE or positive phase reconstruction and cleanly separates the two
source obligations:

\[
 \text{orientation connection}\quad\text{versus}\quad
 \text{innovation-magnitude properness}.
 \tag{IPB.11}
\]

## 6. Hostile audit

1. **Not generic phase retrieval renamed.**  The theorem identifies the exact phase group acting
   on the canonical scale-current/potential/history recovery kernel and on literal completed
   Suzuki production.
2. **No RH premise.**  All identities are finite algebraic consequences of the existing recovery
   and variance laws.
3. **No source claim.**  Gauge-transformed histories need not be arithmetic histories; they are
   indistinguishable positive receiver states.  That is the obstruction proved.
4. **No global-sign understatement.**  A different sign may be chosen at every scale.  FE controls
   only the constant reflection.
5. **No magnitude/order conflation.**  Fixing all signs does not bound the current.  Literal
   Suzuki orientation and source properness remain separate gates.

## Gates

- [x] anchor-current/potential/history joint reconstruction
- [x] exact quadratic-variation action
- [x] local phase-gauge equivariance and action invariance
- [x] strict one-site nonfaithfulness witness
- [x] functional-equation reflection identified as constant subgroup
- [x] literal Suzuki/Gamma receiver prediction
- [x] Lean formalisation
- [ ] source-generated adjacent orientation connection
- [ ] source-generated innovation-magnitude properness
