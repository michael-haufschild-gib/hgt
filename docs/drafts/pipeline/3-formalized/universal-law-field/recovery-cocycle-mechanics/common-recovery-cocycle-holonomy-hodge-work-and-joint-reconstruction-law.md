# Common-recovery cocycle holonomy, Hodge work, and joint reconstruction law

- **ID:** ULF-RCM-1
- **Stage:** 3-formalized
- **Type:** THEOREM / INFORMATION--HISTORY FUSION
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL FINITE THEOREM]
  [BRIDGE: FINITE LIVSIC + HODGE + SUFFICIENCY] [NEW-TO-CORPUS FUSION]
  [LEAN CLOSED: FULL THEOREM/COROLLARY SURFACE] [AXIOM-AUDITED] [NOT RH]

## 1. Setup

Let `S` be a finite nonempty set and let `T:S->S` be a permutation.  Let `L` be a
finite-dimensional real inner-product space.  A persistent ledger rule is a map

\[
 c:S\longrightarrow L.
 \tag{RCH.1}
\]

Its deterministic skew lift is

\[
 \widetilde T_c(s,\ell)=(Ts,\ell+c(s)).
 \tag{RCH.2}
\]

A state-dependent change of ledger origin is a map `h:S->L` acting by

\[
 \Phi_h(s,\ell)=(s,\ell+h(s)).
 \tag{RCH.3}
\]

Conjugation gives

\[
 \Phi_h\widetilde T_c\Phi_h^{-1}=\widetilde T_{c^h},
 \qquad
 c^h(s)=c(s)+h(Ts)-h(s).
 \tag{RCH.4}
\]

Thus ledger rules differing by `h o T-h` are gauge equivalent.

Let the cycles of `T` be denoted by `C`.  Their holonomies are

\[
 H_C(c)=\sum_{s\in C}c(s)\in L.
 \tag{RCH.5}
\]

Finally, let `H` be an arbitrary measurable local-history space and let

\[
 K:S\rightsquigarrow H
 \tag{RCH.6}
\]

be one Markov recovery kernel, independent of every source law.  For a probability law `mu` on
`S`, form the initial packet with zero persistent ledger

\[
 \mathsf P_\mu(ds,dh,d\ell)
 =\mu(ds)K(s,dh)\delta_0(d\ell).
 \tag{RCH.7}
\]

The recovery--cocycle lift is the Markov kernel

\[
 \mathcal L_{K,c}((s,h,\ell),ds'\,dh'\,d\ell')
 =\delta_{Ts}(ds')K(Ts,dh')\delta_{\ell+c(s)}(d\ell').
 \tag{RCH.8}
\]

It refreshes disposable local history and retains persistent additive history.

## 2. Exact packet execution and information neutrality

For `n>=0`, define

\[
 C_n(s)=\sum_{j=0}^{n-1}c(T^js),
 \qquad C_0(s)=0.
 \tag{RCH.9}
\]

### Theorem 2.1 -- common-recovery ledger isometry

After `n` executions of (RCH.8), a packet begun at observer `s` has observer `T^n s`, freshly
recovered local history with law `K(T^n s,-)`, and persistent ledger `C_n(s)`.  For any two
probability laws `mu,nu` on `S`, extended relative entropy satisfies

\[
 \boxed{
 D((\mathcal L_{K,c}^{,n})_*\mathsf P_\mu
   \Vert
   (\mathcal L_{K,c}^{,n})_*\mathsf P_\nu)
 =D(\mathsf P_\mu\Vert\mathsf P_\nu)
 =D(\mu\Vert\nu).}
 \tag{RCH.10}
\]

This holds for every ledger cocycle `c`, including cocycles with nonzero cycle holonomy.

#### Proof

Induction on `n` gives the stated conditional law: each step sends `T^j s` to `T^(j+1)s`, refreshes
local history from `K(T^(j+1)s,-)`, and adds `c(T^j s)` to the ledger.

Common-kernel formation in (RCH.7) preserves relative entropy, so

\[
 D(\mathsf P_\mu\Vert\mathsf P_\nu)=D(\mu\Vert\nu).
\]

Data processing through `n` lifted steps gives

\[
 D((\mathcal L_{K,c}^{,n})_*\mathsf P_\mu
   \Vert
   (\mathcal L_{K,c}^{,n})_*\mathsf P_\nu)
 \le D(\mu\Vert\nu).
\]

Projecting the output to its observer coordinate gives `T^n_* mu` and `T^n_* nu`.  A second data
processing inequality therefore gives

\[
 D(T^n_*\mu\Vert T^n_*\nu)
 \le
 D((\mathcal L_{K,c}^{,n})_*\mathsf P_\mu
   \Vert
   (\mathcal L_{K,c}^{,n})_*\mathsf P_\nu).
\]

Since `T^n` is a measurable bijection of a finite discrete space,
`D(T^n_*mu||T^n_*nu)=D(mu||nu)`.  The two inequalities coincide, proving (RCH.10), including the
value `+infinity`. `square`

## 3. Periodic holonomy classification

### Theorem 3.1 -- finite ledger Livsic theorem

For two ledger rules `c,d:S->L`, the following are equivalent:

1. `d=c^h` for some gauge `h:S->L`;
2. `H_C(d)=H_C(c)` for every cycle `C` of `T`.

Consequently `c` is gauge equivalent to zero exactly when every cycle holonomy vanishes.

#### Proof

If `d=c^h`, summing (RCH.4) around a cycle telescopes, so the holonomies agree.

Conversely, put `delta=d-c`.  Its sum on every cycle is zero.  On each cycle choose a base point
`s_0`, set `h(s_0)=0`, and define recursively

\[
 h(Ts)=h(s)+\delta(s).
\]

The zero cycle sum makes this definition consistent when the cycle returns to `s_0`.  Then
`delta(s)=h(Ts)-h(s)` at every state, so `d=c^h`. `square`

## 4. Hodge representative and exact minimum work

Let `Q:L->L` be positive definite and self-adjoint, and write

\[
 \|x\|_Q^2=\langle Qx,x\rangle,
 \qquad
 \mathcal E_Q(c)=\sum_{s\in S}\|c(s)\|_Q^2.
 \tag{RCH.11}
\]

For `s` in a cycle `C`, define the harmonic representative

\[
 \bar c(s)=\frac{H_C(c)}{|C|}.
 \tag{RCH.12}
\]

### Theorem 4.1 -- cycle Hodge--work identity

The cocycle `bar c` is gauge equivalent to `c`.  For every gauge-equivalent rule `d` and every
cycle `C`, one has the exact orthogonal decomposition

\[
 \boxed{
 \sum_{s\in C}\|d(s)\|_Q^2
 =\frac{\|H_C(c)\|_Q^2}{|C|}
 +\sum_{s\in C}
   \left\|d(s)-\frac{H_C(c)}{|C|}\right\|_Q^2.}
 \tag{RCH.13}
\]

Hence

\[
 \boxed{
 \inf_h\mathcal E_Q(c^h)
 =\sum_C\frac{\|H_C(c)\|_Q^2}{|C|},}
 \tag{RCH.14}
\]

and the infimum is attained exactly when the increment is constant on each cycle.  The minimizing
cocycle is unique, while its gauge potential is unique only up to a constant on each cycle.

#### Proof

The rules `c` and `bar c` have the same cycle sums, so Theorem 3.1 makes them gauge equivalent.
For a fixed cycle write `m=H_C(c)/|C|`.  Every gauge-equivalent `d` has sum `|C|m`.  Expanding

\[
 \sum_{s\in C}\|d(s)\|_Q^2
 =\sum_{s\in C}\|m+(d(s)-m)\|_Q^2
\]

gives `|C| ||m||_Q^2`, the final squared-deviation sum, and a cross term

\[
 2\left\langle Qm,\sum_{s\in C}(d(s)-m)\right\rangle=0.
\]

This proves (RCH.13).  Summing over cycles proves (RCH.14), and equality holds exactly when every
deviation vanishes. `square`

## 5. Recurrent observer and proper open lift

### Theorem 5.1 -- bounded-history classification

For `s` on a cycle `C` of length `P`, the persistent ledger after `kP` steps is

\[
 \boxed{C_{kP}(s)=kH_C(c).}
 \tag{RCH.15}
\]

The following are equivalent:

1. every lifted observer history is bounded;
2. every cycle holonomy is zero;
3. `c` is a coboundary;
4. the minimum gauge energy (RCH.14) is zero.

If `H_C(c)!=0`, then along returns of the observer state

\[
 \|C_{kP}(s)\|_Q^2=k^2\|H_C(c)\|_Q^2.
 \tag{RCH.16}
\]

#### Proof

Partitioning the first `kP` terms of (RCH.9) into `k` complete cycles proves (RCH.15) and
(RCH.16).  If all holonomies vanish, every partial sum is periodic and hence bounded.  If one is
nonzero, (RCH.16) is unbounded.  The remaining equivalences are Theorems 3.1 and 4.1. `square`

## 6. Ledger reconstruction and statistical independence

### Theorem 6.1 -- holonomy reconstructs the sector that information misses

Fix `S,T,K,L`.  Then:

1. every ledger rule `c` induces the same relative-entropy geometry on formed source laws through
   (RCH.10);
2. two recovery--cocycle lifts are conjugate by a state-dependent ledger translation exactly when
   their cycle-holonomy packets `(H_C)_C` agree;
3. the holonomy packet determines the exact minimum positive work by (RCH.14);
4. information geometry alone cannot determine ledger gauge class, and ledger holonomy alone
   cannot determine relative entropy between source laws.

Thus the pair

\[
 \boxed{
 \bigl(D(\mu\Vert\nu),\ (H_C(c))_C\bigr)}
 \tag{RCH.17}
\]

records exactly the declared relative-entropy value and the complete ledger gauge class of a fixed
finite common-recovery lift.

#### Proof

Items 1--3 are Theorems 2.1, 3.1, and 4.1.  For item 4, changing `c` changes its holonomy packet
without changing (RCH.10).  Conversely, with `c` fixed, changing the source pair `mu,nu` changes
their relative entropy without changing any `H_C(c)`. `square`

Only the holonomy packet is a complete classification invariant.  A relative-entropy scalar does
not reconstruct `mu` or `nu`; no classification of the recovery kernel, observer action, or source
laws is claimed.

## 7. Predicted sandpile local-work theorem

Consider the dissipative sandpile setup of ULF-EARM-1.  Fix a source `a>=0` and an eventual stable
addition cycle

\[
 z_{j+1}=\operatorname{stab}(z_j+a),
 \qquad z_P=z_0.
\]

Let `c_j` be the one-step odometer, so

\[
 z_j+a=z_{j+1}+\Delta c_j.
 \tag{RCH.18}
\]

Summing over one cycle gives

\[
 \sum_{j=0}^{P-1}c_j=P\Delta^{-1}a.
 \tag{RCH.19}
\]

### Corollary 7.1 -- local/cumulative Green-work decomposition

With `G=Delta^{-1}`,

\[
 \boxed{
 \sum_{j=0}^{P-1}c_j^T\Delta c_j
 =P\,a^TGa
 +\sum_{j=0}^{P-1}(c_j-Ga)^T\Delta(c_j-Ga).}
 \tag{RCH.20}
\]

Therefore

\[
 \boxed{
 \sum_{j=0}^{P-1}c_j^T\Delta c_j
 \ge P\,a^TGa
 =\frac1P q_P^T\Delta q_P,}
 \tag{RCH.21}
\]

where `q_P=sum_j c_j=P G a` is the cumulative cycle odometer.  Equality holds exactly when every
one-step odometer equals `G a`.

#### Proof

Apply Theorem 4.1 to the addition cycle, ledger increments `c_j`, and positive metric `Q=Delta`.
Its harmonic increment is the mean `(1/P)sum_j c_j=G a`, which gives (RCH.20).  Dropping the
nonnegative fluctuation term gives (RCH.21). `square`

This is a genuine prediction of the recovery--cocycle fusion in a fourth organ: the earlier
sandpile theorem established the cumulative work but did not contain the one-step Hodge variance
decomposition.

## 8. Functional-equation two-cycle consequence

Let `T=R` be an involution.  On every two-point orbit `{s,Rs}`, the persistent holonomy is

\[
 H(s)=c(s)+c(Rs),
 \tag{RCH.22}
\]

and its minimum two-step local work is

\[
 \frac12\|H(s)\|_Q^2.
 \tag{RCH.23}
\]

The common-recovery functional-equation packet action remains KL-isometric for every value of
`H(s)`.  Hence information neutrality cannot imply closed lifted history.  A selection mechanism
must constrain the source-produced reflection holonomy, not merely preserve packet information.

## 9. Hostile audit and exact scope

1. **Known parent machinery.**  Theorem 3.1 is the finite additive Livsic theorem; Theorem 4.1 is
   cyclewise Hodge least squares; Theorem 2.1 is equality under common sufficient recovery.  No
   novelty claim is made for any isolated ingredient.
2. **Why this is more than vocabulary.**  The fusion produces the exact sandpile identity
   (RCH.20), proves a joint reconstruction theorem, and separates local latent refresh from
   persistent history in the packet mechanism.
3. **Invertibility is load-bearing.**  Projection to `T^n s` recovers the initial observer only
   because `T` is a permutation.  A noninvertible action can lose KL information and requires a
   relative-fibre defect.
4. **Finite base is load-bearing.**  Periodic data are complete here because every orbit is a
   cycle.  Infinite hyperbolic Livsic theory needs regularity and closing hypotheses; general
   recurrence does not suffice.
5. **Abelian ledger is load-bearing.**  Nonabelian increments compose in order; their harmonic
   minimization and gauge classification are different problems.
6. **Positive metric is extra constitutive data.**  Holonomy exists without `Q`.  A physical
   application must derive `Q` from its source rather than choose it after seeing the holonomy.
7. **No RH theorem.**  No source-canonical arithmetic ledger with a proper reflection holonomy is
   constructed here.
8. **No curvature claim.**  Cycle holonomy is the invariant; calling it curvature would add no
   content.

## 10. Literature boundary

- B. Kalinin, *Livsic theorem for matrix cocycles*,
  [arXiv:0808.0350](https://arxiv.org/abs/0808.0350), proves periodic-data rigidity in a far more
  general hyperbolic setting.
- Common-kernel KL equality and sufficient recovery are standard information geometry and are
  formalized in `ConstitutiveFunctionalEquationPacketLift.lean`.
- Graph/cochain Hodge decomposition, skew products, and gauge cohomology are established parent
  mathematics.
- Bond--Levine's abelian-network least action and the finite sandpile critical-group literature
  are parents of Corollary 7.1's realization, not of the packet-information theorem.

The exact new-to-corpus result is the combined recovery--ledger theorem and its local/cumulative
Green-work consequence.  External priority of this exact synthesis is not asserted.

## 11. Lean boundary

Formalization is closed in
`GaloisForLFunctions.HTGeometry.ConstitutiveRecoveryCocycleHolonomy` and wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField`.  It includes:

1. exact finite ledger sums, gauge telescoping, same-cycle holonomy invariance, and both the
   global-order and literal periodic-data forms of finite Livsic classification;
2. canonical harmonic representatives, exact global and per-periodic-orbit Hodge identities,
   sharp lower bounds, and equality/uniqueness criteria for every positive self-adjoint metric;
3. exact primitive-period repetition `C_(kP)=k C_P`, quadratic return work, bounded-history iff
   zero holonomy, and skew-lift conjugacy iff holonomy agreement;
4. generic finite Hodge infrastructure, the local/cumulative sandpile work identity and equality
   criterion, and the exact involutive two-cycle decomposition;
5. the joint `(KL, holonomy)` reconstruction signature;
6. the explicit endpoint/history/ledger packet, exact recovery of the initial observer through
   the inverse endpoint permutation, and extended-KL isometry for every execution depth and
   ledger.

Direct elaboration and the targeted leaf build pass.  Axiom prints for all capstones report only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, project axiom, opaque escape,
unsafe declaration, computation certificate, or numerical proof is used.  The finite global-order
traversal is a faithful redundant encoding of primitive-cycle holonomy; the module separately
exposes periodic-data and per-orbit statements so no primitive-cycle theorem is weakened.

## Log

- 2026-08-12 -- theorem frozen after information-neutrality was shown unable to control persistent
  history.
- 2026-08-12 -- cycle classification, Hodge work, joint reconstruction, and sandpile prediction
  proved; hostile audit classified the ingredients as known and the exact fusion as a bridge.
- 2026-08-14 -- full theorem/corollary surface formalized unconditionally in
  `HTGeometry.ConstitutiveRecoveryCocycleHolonomy`; leaf, umbrella, lint-scope, and axiom audits
  completed.
- 2026-08-14 — full unconditional Lean closure in HTGeometry.ConstitutiveRecoveryCocycleHolonomy; direct/targeted/umbrella checks and capstone axiom audit pass
