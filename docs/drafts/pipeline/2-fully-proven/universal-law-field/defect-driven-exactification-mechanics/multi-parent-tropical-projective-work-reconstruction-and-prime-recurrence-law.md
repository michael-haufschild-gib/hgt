# Multi-parent tropical-projective work, observer reconstruction, and prime-recurrence law

- **ID:** ULF-DDEM-TPW-1
- **Stage:** 2-fully-proven
- **Type:** FIELD LAW / THREE-ORGAN FUSION / EXACT CONSERVATION / FOURTH-ORGAN PREDICTION
- **Source:** full-frontier intervention grammar; multi-parent revealed-work open core; finite
  prime Boolean--Mass--Hankel packet
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM, NOT ROUTE]
  [MULTI-PARENT OPEN CORE CLOSED] [BOOLEAN FORMATION] [MASS CLOCK]
  [HANKEL RECONSTRUCTION] [RECURRENCE PREDICTION] [LEAN-CERTIFIED]
  [RH SELECTION REDUCED, NOT PROVED]

## 1. Field mechanism

Let (P) be a nonempty finite family of legal parent laws and let (X) be a source-state space.
Each parent has a scalar action

\[
 A_p:X\longrightarrow\mathbb R,
 \qquad
 \delta_p(x,y)=A_p(y)-A_p(x).
 \tag{TPW.1}
\]

Formation does not choose one parent.  It imposes all of them and charges the mandatory work

\[
 M_A(x,y)=\max_{p\in P}\delta_p(x,y).
 \tag{TPW.2}
\]

The primitive invariant is not (M_A) alone.  It is the projective action profile

\[
 [A(x)]\in \mathbb R^P/\mathbb R\mathbf 1
 \tag{TPW.3}
\]

and its reversible work

\[
 H_A(x,y)=M_A(x,y)+M_A(y,x).
 \tag{TPW.4}
\]

This is a mechanism: legal parent actions generate one relative geometry by maximum formation.
No curvature object, connection, or route-specific receiver is postulated.

## 2. Tropical-projective fusion theorem

### Theorem 2.1

For every nonempty finite parent family:

1. **Exact width law**
   \[
   \boxed{
   H_A(x,y)=\max_p\delta_p(x,y)-\min_p\delta_p(x,y)
   =\max_{p,q}\bigl(\delta_p(x,y)-\delta_q(x,y)\bigr).}
   \tag{TPW.5}
   \]
   Thus (H_A) is Hilbert's tropical projective distance between (A(x)) and (A(y)).

2. **Common-gauge law.**  Replacing every parent by (A_p+C) changes (M_A) by the exact
   increment (C(y)-C(x)) and leaves (H_A) unchanged.

3. **Zero law**
   \[
   \boxed{H_A(x,y)=0\iff
      \delta_p(x,y)=\delta_q(x,y)\quad\text{for all }p,q.}
   \tag{TPW.6}
   \]

4. **Reference conservation.**  For any parent (p_0), define
   \[
   R_{p_0}(x,y)=M_A(x,y)-\delta_{p_0}(x,y)\ge0.
   \tag{TPW.7}
   \]
   Then every finite history (gamma=(x_0,\ldots,x_n)) obeys
   \[
   \boxed{
   \sum_{i<n}M_A(x_i,x_{i+1})
   =A_{p_0}(x_n)-A_{p_0}(x_0)
    +\sum_{i<n}R_{p_0}(x_i,x_{i+1}).}
   \tag{TPW.8}
   \]
   In particular, every closed history has nonnegative mandatory work.

5. **Reverse-history conservation**
   \[
   \boxed{
   W_A(\gamma)+W_A(\gamma^{\rm rev})
   =\sum_{i<n}H_A(x_i,x_{i+1}).}
   \tag{TPW.9}
   \]

6. **Scalar integrability rigidity.**  On the complete reversible transition system,
   (M_A(x,y)=V(y)-V(x)) for one scalar (V) exactly when every relative potential
   (A_p-A_q) is constant.  Multi-parent work scalarizes only on the common-gauge stratum.

### Proof

Put (d_p=\delta_p(x,y)).  Since

\[
 M_A(y,x)=\max_p(-d_p)=-\min_p d_p,
\]

`(TPW.5)` follows.  It is nonnegative, and equality holds exactly when the maximum and minimum
coincide, which proves `(TPW.6)`.  Adding a common increment (dC) translates every (d_p) by the
same number; maxima translate and width does not.

Equation `(TPW.7)` is nonnegative because (d_{p_0}) is one candidate in the maximum.  The local
identity (M_A=dA_{p_0}+R_{p_0}), summed along the history, gives `(TPW.8)` by telescoping.  Applying
`(TPW.5)` edgewise gives `(TPW.9)`.  If (M_A=dV), every two-cycle has zero work; `(TPW.6)` makes
every relative potential constant.  Conversely, constant relative potentials make all increments
equal, so (M_A=dA_{p_0}).  QED.

## 3. Exact observer-memory theorem

Choose a reference parent (p_0) and use the affine chart

\[
 \rho_{p_0}(x)=\bigl(A_p(x)-A_{p_0}(x)\bigr)_{p\in P}.
 \tag{TPW.10}
\]

### Theorem 3.1

For any observer (q:X\to Q), the following are equivalent:

1. (ho_{p_0}) factors through the attained range of (q);
2. whenever (q(x)=q(y)), one has (H_A(x,y)=0);
3. every relative potential (A_p-A_r) factors through the attained range of (q).

If these fail, there are observer-indistinguishable (x,y) with (H_A(x,y)>0).

### Proof

Factorization through the attained observer range is equivalent to constancy on every observer
kernel pair.  Equality of the relative profiles is equivalent to equality of all parent
increments.  Apply `(TPW.6)`.  Nonnegativity upgrades nonzero width to positive width.  QED.

This proves minimal memory in a precise sense: the projective profile, not one scalar obstruction,
is the universal finite multi-parent memory.

### Sharp scalar-loss countermodel

The increment packets

\[
 (0,1,2),\qquad (0,0,2)
 \tag{TPW.11}
\]

have the same width (2) but different projective profiles.  Therefore width detects failure of
descent but cannot reconstruct a three-parent law.  The full projective packet is load-bearing.

## 4. Genuine fusion across three route organs

Let (F) be a finite marked set of at least two primes.  The literal ramification-diagonal source
already supplies three structurally different organs.

### 4.1 Boolean formation organ

The shell identity

\[
 \widetilde a_m(k^m)=\mu(k)^2
 \tag{TPW.12}
\]

constructs the finite Boolean mode family (F) and its hard-core configuration space.  This fixes
which parent laws exist; it is not inferred from later moments.

### 4.2 Mass-current organ

The source logarithmic derivative supplies

\[
 \lambda_p=\log p,
 \qquad
 j_p=\sqrt{w_p}\lambda_p.
 \tag{TPW.13}
\]

Use the clocks as parent actions

\[
 A_p(t)=t\lambda_p.
 \tag{TPW.14}
\]

### 4.3 Positive Hankel organ and joint reconstruction

The same packet supplies moments

\[
 \mu_n=\sum_{p\in F}w_p\lambda_p^n.
 \tag{TPW.15}
\]

For (r=|F|), the first (2r) moments reconstruct the spectral polynomial and hence the unordered
clock packet.  Once the marked prime clocks are fixed, the first (r) moments reconstruct all
weights.  Therefore Boolean labels plus the finite Hankel packet jointly reconstruct

\[
 (\lambda_p,w_p)_p,quad j,quad [A(t)],\quad H_A(s,t).
 \tag{TPW.16}
\]

This is a genuine fusion law.  Formation chooses the modes, Mass supplies their generators, and
Hankel data reconstructs the full generated projective geometry.  None of the three outputs alone
contains the other two.

For (p_-\) and (p_+) the smallest and largest primes in (F), Theorem 2.1 gives the exact
conservation value

\[
 \boxed{
 H_A(s,t)=|t-s|\bigl(\log p_+-\log p_-\bigr)
 =|t-s|\log{p_+\over p_-}.}
 \tag{TPW.17}
\]

## 5. Predicted theorem in the recurrence organ

The compact observer is

\[
 U(t)=\operatorname{diag}(e^{-it\log p})_{p\in F}.
 \tag{TPW.18}
\]

Prime-log rational independence implies arbitrarily late returns: for every (T>0) and
(\varepsilon>0), there is (t\ge T) with

\[
 \|U(t)-I\|<\varepsilon.
 \tag{TPW.19}
\]

### Theorem 5.1 — recurrent observer with forced open projective work

The same return time obeys

\[
 \boxed{
 H_A(0,t)=t\log{p_+\over p_-}
 \ge T\log{p_+\over p_-}.}
 \tag{TPW.20}
\]

Hence observed history closes arbitrarily accurately while the reconstructed projective source
work escapes linearly.  This is stronger than the previous statement that some chosen universal
cover lift is open: `(TPW.20)` is determined by the jointly reconstructed Mass--Hankel clock packet,
is common-gauge invariant, and is independent of lift coordinates.

### Proof

Use the existing finite-prime Kronecker return theorem for `(TPW.19)` and apply `(TPW.17)` with
(s=0).  Since (t\ge T) and the clock span is positive, `(TPW.20)` follows.  QED.

The one-prime case is sharp: its projective width is identically zero although its phase still
recurs.

## 6. RH selection consequence—only after fusion

Put

\[
 a_\rho=\Re\rho-\tfrac12,
 \qquad
 A_{\rho,p}(u)=u\log p.
 \tag{TPW.21}
\]

For any aperture containing two primes,

\[
 \boxed{
 H_A(0,a_\rho)=|a_\rho|\log{p_+\over p_-},
 \qquad
 H_A(0,a_\rho)=0\iff\Re\rho=\tfrac12.}
 \tag{TPW.22}
\]

This identifies the exact selection theorem the field would need:

> construct a source-normal observer through which the full prime projective action profile
> descends at every nontrivial Xi zero, and prove that this observer identifies the physical
> zero-state (a_\rho) with the centered reference state (0).

The observer-memory theorem would then force the specific collapsed width
(H_A(0,a_\rho)) to vanish, and `(TPW.22)` would give RH.  The present theorem manufactures neither
the descent nor the source-normal state identification.  It converts the vague missing
"source-native selector" into a precise mechanism-level obligation: joint descent of a
reconstructed projective profile across a source-proved kernel pair.  Scalar residues,
determinants, and one-prime Bocksteins cannot satisfy it because they do not retain the profile.

## 7. Why this is not regression

1. The theorem solves the general multi-parent generation problem before using primes.
2. Route-specific formulas enter only as realizations of one law.
3. Conservation and observer-memory theorems are valid in every finite parent family.
4. The recurrence statement is predicted from fusion and was not used to define family work.
5. RH selection is attempted only after the first four gates close.

## 8. Formal certificate

Lean module:

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveTropicalProjectiveWork.lean`

Certified declarations include:

- `constitutiveFamilyWidth_eq_zero_iff`;
- `constitutiveFamilyWork_add_common_potential`;
- `constitutiveFamilyPathWork_conservation`;
- `constitutiveFamilyPathWork_nonneg_of_closed`;
- `relativeProfile_factorsThroughRange_iff_collapsedWidth_zero`;
- `affineClock_familyWidth_eq_abs_mul_span`;
- `affineClock_centeredWidth_eq_zero_iff`;
- `PrimeTropical.exists_large_return_with_tropical_width`.

No new axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computational certificate is used.
