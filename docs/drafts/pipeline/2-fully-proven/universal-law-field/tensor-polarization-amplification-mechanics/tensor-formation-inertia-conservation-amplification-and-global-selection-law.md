# Tensor-formation inertia conservation, amplification, and global selection law

- **ID:** ULF-TPAM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / UNIVERSAL FORMATION-SELECTION LAW
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [ROUTE-INDEPENDENT]`
  `[FORMATION + POLARIZATION + CONSERVATION + PROPERNESS] [CONDITIONAL RH INTERFACE]`
- **Statement:** Tensor formation obeys an exact two-channel fusion law.  A mixed positive/negative
  packet generates unbounded negative index under repeated formation, whereas a uniform family
  index budget is equivalent to positivity of the initial active packet.

## 1. Higher-level mechanism

Many corpus arguments try to eliminate one negative direction by inspecting one finite observer.
That is the wrong scale.  The load-bearing operation is not another observer but **independent
formation**: combine packets by tensor product, then require a conservation law to remain valid on
the entire formed family.

The mechanism is

> **mixed polarity is multiplicatively unstable under formation; a uniform global index budget
> selects the positive chamber.**

This fuses four previously separate organs:

1. **formation:** tensor product creates composite packets;
2. **polarization:** each active channel carries positive or negative sign;
3. **conservation:** active rank and signature multiply exactly;
4. **properness/selection:** negative-index sublevels occupy only finite formation depth.

It also predicts a fourth, combinatorial/species shadow: the number of negative formed words is
the odd-parity count of negative letters, determined by the same rank/signature conservation law.
No route-specific datum enters the theorem.

## 2. Binary tensor fusion

Let `H` and `K` be finite-dimensional Hermitian forms.  Write

\[
 (p_H,q_H,r_H),\qquad (p_K,q_K,r_K)
\tag{TPA.1}
\]

for positive, negative, and null indices.  On active quotients by radicals, the tensor eigenvalues
are the products `mu_i nu_j`.  Hence signs agree exactly when both factors have equal sign and
differ exactly when they have opposite sign.

### Theorem 2.1 -- tensor-polarization fusion

\[
\boxed{
\begin{aligned}
 p_{H\otimes K}&=p_Hp_K+q_Hq_K,\\
 q_{H\otimes K}&=p_Hq_K+q_Hp_K.
\end{aligned}}
\tag{TPA.2}
\]

In particular,

\[
 (p+q)_{H\otimes K}=(p+q)_H(p+q)_K,
 \qquad
 (p-q)_{H\otimes K}=(p-q)_H(p-q)_K.
\tag{TPA.3}
\]

#### Proof

Choose unitary diagonalizations

\[
 H=U\operatorname{diag}(\mu_i)U^*,
 \qquad
 K=V\operatorname{diag}(\nu_j)V^*.
\]

Then `U tensor V` diagonalizes `H tensor K` with eigenvalues `mu_i nu_j`.  A product is negative
iff one factor is positive and the other negative; it is positive iff both are positive or both
negative.  Counting the corresponding Cartesian products gives `(TPA.2)`.  Adding and subtracting
the identities gives `(TPA.3)`.  QED.

The Lean proof does not assume diagonal input.  It performs spectral diagonalization and transports
indices through invertible Kronecker congruence.

## 3. Repeated formation and exact conservation

Fix a nondegenerate active packet with `p` positive and `q` negative channels.  Let `P_d,N_d` be
the positive and negative indices after `d` independent tensor formations, with the empty packet
at depth zero:

\[
 P_0=1,\qquad N_0=0.
\tag{TPA.4}
\]

The binary fusion theorem gives

\[
\boxed{
\begin{aligned}
 P_{d+1}&=pP_d+qN_d,\\
 N_{d+1}&=qP_d+pN_d.
\end{aligned}}
\tag{TPA.5}
\]

### Theorem 3.1 -- rank/signature conservation

For every `d>=0`,

\[
\boxed{P_d+N_d=(p+q)^d,\qquad P_d-N_d=(p-q)^d.}
\tag{TPA.6}
\]

Consequently

\[
\boxed{2N_d=(p+q)^d-(p-q)^d.}
\tag{TPA.7}
\]

#### Proof

Add and subtract the two recurrences in `(TPA.5)`.  The sum is multiplied by `p+q`; the difference
is multiplied by `p-q`.  Initial values are `1` for the sum and difference.  Induction gives
`(TPA.6)`, and subtraction gives `(TPA.7)`.  QED.

This is the exact conservation identity requested from a common formation grammar.  Rank and
signature are not competing summaries; together they reconstruct both polarity counts.

## 4. Amplification and global properness

Assume `p>0` and `q>0`.  From `(TPA.5)` and `(TPA.6)`,

\[
 N_{d+1}=qP_d+pN_d\ge P_d+N_d=(p+q)^d\ge2^d>d.
\tag{TPA.8}
\]

### Theorem 4.1 -- formation-depth properness

For every budget `K`,

\[
 N_{d+1}\le K\quad\Longrightarrow\quad d<K.
\tag{TPA.9}
\]

Thus every negative-index sublevel has finite formation depth.  Equivalently, for every `K` there
is a formation degree `d` with `N_d>K`.

#### Proof

Equation `(TPA.8)` gives `d<N_{d+1}`.  Compose with `N_{d+1}<=K`.  QED.

This is a genuine global formation/properness theorem.  It does not infer selection from one
packet; it tests compatibility of an entire generated family with a fixed conservation budget.

### Theorem 4.2 -- global tensor-formation selection

Assume `p>0`.  Then

\[
\boxed{
 \left(\exists K\ \forall d,\ N_d\le K\right)
 \quad\Longleftrightarrow\quad q=0.}
\tag{TPA.10}
\]

#### Proof

If `q=0`, recurrence `(TPA.5)` gives `N_d=0` for every `d`.  Conversely, if `q>0`, Theorem 4.1
produces, for every proposed `K`, a depth with `N_d>K`.  QED.

This is the first selection law in the universal-law-field programme whose conclusion is positivity
and whose premise is a global formation constraint rather than a local positivity assumption.

## 5. Fourth-organ prediction: formed-sign parity

Regard the `p+q` active channels as an alphabet with `p` positive and `q` negative letters.  A word
of length `d` is negative iff it contains an odd number of negative letters.  Splitting a word by
its last letter gives exactly recurrence `(TPA.5)`.  Therefore the odd-parity word count is

\[
 \#\{\text{negative words of length }d\}=N_d,
\tag{TPA.11}
\]

and is reconstructed from total word count and signed character by `(TPA.7)`.

Thus the same theorem predicts a species/probability law not used in its Hermitian derivation:
the parity distribution of independently formed signs is fixed by multiplicativity of the two
characters `p+q` and `p-q`.  This is the fourth-organ shadow of the fusion law.

## 6. Conditional RH interface

The corpus already contains finite Hermitian/Krein carriers in which negative index counts
off-critical-line divisor pairs.  Applying Theorem 4.2 would require two new source theorems:

1. a **literal source-native independent-formation functor** whose polarization is the relevant
   Xi/Weil carrier polarization;
2. a **uniform source-derived negative-index budget** valid at every formation degree.

If both are constructed and the carrier has at least one positive channel, `(TPA.10)` forces its
negative index to vanish.  Under the existing carrier identification this is the RH selection
consequence.

The change of target is substantial.  One no longer tries to prove base positivity directly.
One proves a family law: independent formation is legal, while the conserved source budget cannot
grow.  Tensor amplification then performs the selection automatically.

This card does **not** construct those two source theorems and therefore does not prove RH.

## 7. Sharp boundaries

1. **Formation must be literal.** Adding formal tensor powers after specialization does not produce
   a source law.
2. **Budget must be uniform.** A degree-dependent budget growing like `(p+q)^d` selects nothing.
3. **At least one positive channel is load-bearing.** A purely negative one-dimensional form has
   alternating tensor sign and bounded negative index.
4. **Radicals require separate bookkeeping.** The theorem applies directly to the active quotient;
   zero channels generate additional null terms but do not alter opposite-sign fusion.
5. **Tensor formation is specific.** Symmetric, exterior, free, and interacting formation laws have
   different multiplicities and require their own fusion polynomials.
6. **No local route repair is claimed.** The theorem changes the global selection architecture.

## 8. Lean certificate

Formal module:

`formal/GaloisForLFunctions/HTGeometry/TensorPolarizationAmplification.lean`

Core declarations:

- `negIndex_kronecker`
- `posIndex_kronecker`
- `tensorPolar_total`
- `tensorPolar_signature`
- `tensorPolar_twice_negative`
- `tensorPolar_negative_sublevel_window`
- `tensorPolar_uniform_negative_budget_iff`
- `tensorPolarizationAmplification_closed`
- `tensorPolarizationSelection_closed`

The two capstones are closed propositions with no mathematical premises.  No `sorry`, `admit`,
new axiom, `opaque`, or `unsafe` declaration is used.

