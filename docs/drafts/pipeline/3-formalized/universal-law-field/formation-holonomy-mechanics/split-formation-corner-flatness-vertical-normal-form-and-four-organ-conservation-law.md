# Split-formation corner flatness, vertical normal form, and four-organ conservation law

- **ID:** ULF-FHM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Formation Holonomy Mechanics
- **Statement:** Split formations over a common recovered object form a flat pair groupoid in the Karoubi corner; every base-compatible linear comparison is uniquely a vertical transport, every three-organ composition defect is purely vertical, and four-organ defects obey an exact associativity conservation law.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [UNIVERSAL FINITE MECHANISM] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [NOT RH]

## 1. Arbitrary-category split formations

Let \(\mathcal C\) be a category. Fix an object \(X\). For every index \(i\), let

\[
 X\xrightarrow{f_i}Z_i\xrightarrow{p_i}X,
 \qquad p_if_i=1_X.
 \tag{SFH.1}
\]

Put

\[
 e_i=f_ip_i:Z_i\to Z_i,
 \qquad
 T_{ji}=f_jp_i:Z_i\to Z_j.
 \tag{SFH.2}
\]

### Theorem 1.1 -- common-recovery corner flatness

For all indices \(i,j,k\):

\[
 \boxed{e_i^2=e_i,}
 \tag{SFH.3}
\]

\[
 \boxed{T_{kj}T_{ji}=T_{ki},}
 \tag{SFH.4}
\]

and

\[
 \boxed{T_{ij}T_{ji}=e_i.}
 \tag{SFH.5}
\]

Moreover,

\[
 e_jT_{ji}=T_{ji}=T_{ji}e_i.
 \tag{SFH.6}
\]

Hence \(T_{ji}\) is an isomorphism from \((Z_i,e_i)\) to \((Z_j,e_j)\) in the Karoubi envelope,
with inverse \(T_{ij}\). Every canonical loop is the local corner identity \(e_i\).

#### Proof

Using only \(p_if_i=1_X\),

\[
 e_i^2=f_ip_if_ip_i=f_i(p_if_i)p_i=f_ip_i=e_i.
\]

Similarly,

\[
 T_{kj}T_{ji}=f_kp_jf_jp_i=f_k(p_jf_j)p_i=f_kp_i=T_{ki},
\]

and the case \(k=i\) gives (SFH.5). Finally,

\[
 e_jT_{ji}=f_jp_jf_jp_i=f_jp_i,
 \qquad
 T_{ji}e_i=f_jp_if_ip_i=f_jp_i.
\]

These are exactly the Karoubi-morphism and relative-inverse identities. ∎

### Corollary 1.2 -- common recovery cannot generate holonomy

Any comparison system built only from “recover to \(X\), then form the target” has zero triangle
defect and trivial corner holonomy. This conclusion is independent of topology, probability,
positivity, dimension, or presentation.

## 2. Linear split chart

Now let \(\mathcal C=\mathrm{Vect}_K\) for a field \(K\). Put

\[
 V_i=\ker p_i.
 \tag{SFH.7}
\]

Define

\[
 \Phi_i:X\oplus V_i\longrightarrow Z_i,
 \qquad
 \Phi_i(x,v)=f_i(x)+v,
 \tag{SFH.8}
\]

and

\[
 \Psi_i:Z_i\longrightarrow X\oplus V_i,
 \qquad
 \Psi_i(z)=\bigl(p_i(z),z-f_ip_i(z)\bigr).
 \tag{SFH.9}
\]

### Lemma 2.1 -- canonical vertical decomposition

The second component of \(\Psi_i(z)\) lies in \(V_i\), and \(\Phi_i,\Psi_i\) are inverse linear
isomorphisms. In these coordinates,

\[
 e_i=1_X\oplus0_{V_i},
 \qquad
 T_{ji}=1_X\oplus0_{V_i,V_j}.
 \tag{SFH.10}
\]

#### Proof

Since \(p_if_i=1_X\),

\[
 p_i(z-f_ip_i z)=p_i z-(p_if_i)p_i z=0.
\]

Also

\[
 \Phi_i\Psi_i(z)=f_ip_i z+z-f_ip_i z=z,
\]

while for \(v\in\ker p_i\),

\[
 \Psi_i\Phi_i(x,v)
 =\bigl(x,f_ix+v-f_ix\bigr)=(x,v).
\]

Equations (SFH.10) follow by substitution. ∎

## 3. Base-compatible comparisons

Let \(C_{ji}:Z_i\to Z_j\) be linear and satisfy

\[
 p_jC_{ji}=p_i,
 \qquad
 C_{ji}f_i=f_j.
 \tag{SFH.11}
\]

The first identity says recovery is preserved. The second says already formed source data are
preserved.

### Theorem 3.1 -- unique vertical normal form

There is a unique linear map

\[
 L_{ji}:V_i\to V_j
 \tag{SFH.12}
\]

such that

\[
 \boxed{
 \Psi_jC_{ji}\Phi_i=1_X\oplus L_{ji}.}
 \tag{SFH.13}
\]

It is the restriction \(L_{ji}=C_{ji}|_{V_i}\).

#### Proof

If \(v\in V_i\), then

\[
 p_j(C_{ji}v)=p_i(v)=0,
\]

so \(C_{ji}v\in V_j\); the restriction is well-defined. For \(x\in X,v\in V_i\),

\[
 C_{ji}(f_ix+v)=f_jx+L_{ji}v.
\]

Applying \(\Psi_j\) gives \((x,L_{ji}v)\), proving (SFH.13). Any map satisfying (SFH.13) must agree
with \(C_{ji}\) on \(V_i\), so uniqueness follows. ∎

### Corollary 3.2 -- factor-through-recovery criterion

The following are equivalent:

1. \(C_{ji}=T_{ji}=f_jp_i\);
2. \(L_{ji}=0\);
3. \(C_{ji}\) annihilates \(V_i\).

Thus a comparison contains information beyond common recovery exactly when its vertical transport is
nonzero.

## 4. Three-organ fusion defect

For compatible comparisons \(C_{ji},C_{kj},C_{ki}\), define

\[
 \Omega_{kji}=C_{kj}C_{ji}-C_{ki}:Z_i\to Z_k.
 \tag{SFH.14}
\]

### Theorem 4.1 -- exact vertical defect formula

In the split coordinates,

\[
 \boxed{
 \Psi_k\Omega_{kji}\Phi_i
 =0_X\oplus\bigl(L_{kj}L_{ji}-L_{ki}\bigr).}
 \tag{SFH.15}
\]

Consequently

\[
 \boxed{p_k\Omega_{kji}=0,\qquad \Omega_{kji}f_i=0.}
 \tag{SFH.16}
\]

Every linear reporter \(r:Z_k\to W\) factoring through recovery, \(r=\bar r p_k\), annihilates
\(\Omega_{kji}\).

#### Proof

Theorem 3.1 gives

\[
 \Psi_kC_{kj}C_{ji}\Phi_i
 =(1_X\oplus L_{kj})(1_X\oplus L_{ji})
 =1_X\oplus L_{kj}L_{ji}.
\]

Subtract \(\Psi_kC_{ki}\Phi_i=1_X\oplus L_{ki}\) to obtain (SFH.15). The base component is zero,
which proves (SFH.16). If \(r=\bar r p_k\), then

\[
 r\Omega_{kji}=\bar r(p_k\Omega_{kji})=0.
\]

∎

### Corollary 4.2 -- loop normal form

For a loop of base-compatible comparisons

\[
 Z_{i_0}\xrightarrow{C_{i_1i_0}}Z_{i_1}\to\cdots\to
 Z_{i_m}=Z_{i_0},
\]

the composite has the form

\[
 \boxed{
 1_X\oplus
  (L_{i_0i_{m-1}}\cdots L_{i_2i_1}L_{i_1i_0}).}
 \tag{SFH.17}
\]

Thus the recovered base always returns exactly. Full conservative return requires the displayed
vertical product to be \(1_{V_{i_0}}\); canonical regenerate-after-recovery return instead has
vertical product \(0\) and equals \(e_{i_0}\). These are different closure doctrines.

## 5. Four-organ conservation

For four indices \(i,j,k,\ell\), define every triangle defect as in (SFH.14).

### Theorem 5.1 -- associativity/Bianchi identity

The defects obey

\[
 \boxed{
 C_{\ell k}\Omega_{kji}+\Omega_{\ell ki}
 =\Omega_{\ell kj}C_{ji}+\Omega_{\ell ji}.}
 \tag{SFH.18}
\]

Equivalently, on vertical fibres,

\[
 \boxed{
 L_{\ell k}(L_{kj}L_{ji}-L_{ki})
 +(L_{\ell k}L_{ki}-L_{\ell i})
 =(L_{\ell k}L_{kj}-L_{\ell j})L_{ji}
 +(L_{\ell j}L_{ji}-L_{\ell i}).}
 \tag{SFH.19}
\]

#### Proof

Expanding the left side gives

\[
 C_{\ell k}(C_{kj}C_{ji}-C_{ki})
 +(C_{\ell k}C_{ki}-C_{\ell i})
 =C_{\ell k}C_{kj}C_{ji}-C_{\ell i}.
\]

Expanding the right side gives

\[
 (C_{\ell k}C_{kj}-C_{\ell j})C_{ji}
 +(C_{\ell j}C_{ji}-C_{\ell i})
 =C_{\ell k}C_{kj}C_{ji}-C_{\ell i}.
\]

The expressions agree by associativity. Applying the vertical normal form gives (SFH.19). ∎

This identity is a genuine four-organ prediction: once three triangle defects and the edge
transports are fixed, the fourth defect is constrained. It is not an independent fitted scalar.

## 6. Packet-formation specialization and correction

In the Markov category of standard Borel spaces and Markov kernels, packet formation is a section
\(f\), observer projection is a recovery \(p\), and \(pf=1\). The arbitrary-category Theorem 1.1
therefore applies without linearization:

- recover--act--regenerate is a corner action;
- an involution squares to the formation idempotent on raw packets and to the identity only on
  already formed laws;
- any family of packet charts compared only through the recovered observer is flat.

The linear vertical-normal-form theorem is not asserted for arbitrary Markov kernels. Conditional
history is its probabilistic analogue and requires disintegration/standard-Borel hypotheses.

For the functional-equation history, the source-natural execution alternates the reflected recovery
laws. One history shift transports the phase-\(x\) alternating product law to the phase-\(-x\) law
for every \(x\). Hence the frozen stationary-history entropy obstruction is not a source-natural
functional-equation obstruction. Its entropy difference is an orbit coboundary. The surviving
source-natural work is symmetric conditional-change work, which needs an independent boundedness,
passivity, or conservation producer before it can select.

## 7. Hostile loops

### Loop A -- common recovery creates curvature

- **Conjecture:** three different formed receivers over one sufficient observer can have nontrivial
  canonical loop holonomy.
- **Failure:** Theorem 1.1 gives exact pair-groupoid composition.
- **Positive survivor:** any nontrivial fusion must be a vertical transport not factoring through
  recovery.

### Loop B -- a split idempotent is already the missing field

- **Conjecture:** Karoubi completion itself supplies new dynamics.
- **Failure:** it makes every canonical comparison invertible relative to the idempotents and stores
  all split objects timelessly.
- **Positive survivor:** sequentially source-generated vertical transports and their positive work
  remain additional data.

### Loop C -- base reporters can detect fusion defect

- **Conjecture:** a sufficiently rich family of reporters factoring through the common observer can
  reconstruct \(\Omega\).
- **Failure:** Theorem 4.1 gives \(p_k\Omega=0\) identically.
- **Positive survivor:** reporters must separate vertical fibres or admit a transgression from them.

### Loop D -- three pairwise defects are independent

- **Conjecture:** every triangle can be fitted independently.
- **Failure:** adding a fourth organ imposes (SFH.18).
- **Positive survivor:** four-organ coherence is an exact falsifier of proposed fusion data.

### Loop E -- vertical holonomy by itself selects RH

- **Conjecture:** any nonzero vertical loop forces the critical line.
- **Failure:** arbitrary \(L_{ji}\) realize arbitrary loop products.
- **Positive survivor:** selection needs source genesis plus a positive/proper work law and a strict
  zero-locus theorem.

## 8. Corpus leverage and exact next test

The theorem changes the search target. It rules out, at once, every proposal whose inter-organ maps
all have the form

\[
 \text{target formation}\circ\text{common recovery}.
\]

The next non-theatrical corpus test is therefore:

1. choose three structurally different organs with literal split formation maps;
2. construct at least one source-derived comparison whose restriction to the recovery kernel is
   nonzero;
3. compute its triangle defect;
4. predict and verify the fourth comparison using (SFH.18);
5. only then seek positive/proper selection.

Failure at step 2 proves that the chosen organs are merely common-base shadows and cannot unlock the
field.

## 9. Literature boundary

The categorical part is standard split-idempotent/Karoubi algebra; the linear part is elementary
split-exact-sequence algebra. Related occupied frameworks include:

- Gaiotto--Johnson-Freyd, *Condensations in higher categories*,
  <https://arxiv.org/abs/1905.09566>;
- Miller, *Idempotent Completion of Persistence Categories*,
  <https://arxiv.org/abs/2503.20603>;
- Mohammed, *Partializations of Markov categories*,
  <https://arxiv.org/abs/2509.05094>.

No novelty claim is made for those ingredients. The theorem is promoted because its exact
cross-organ consequence, vertical normal form, and four-organ conservation identity are
dependency-closed and materially sharpen the universal-law-field acceptance gate.

## Gates

- [x] arbitrary-category flatness proved
- [x] linear vertical normal form proved
- [x] three-organ defect formula proved
- [x] four-organ conservation identity proved
- [x] common-recovery and frozen-history overclaims explicitly killed
- [x] Lean formalization (`GaloisForLFunctions.HTGeometry.SplitFormationCornerFlatness`)
- [ ] three literal heterogeneous corpus realizations
- [ ] source-generated positive vertical-work theorem

## Log

- 2026-08-11 -- theorem extracted from hostile failure of frozen formed-history selection. Paper
  proof closed; exact next corpus test isolated. No Lean files edited or built.
