# Source-conjugate reflection orbit tightness, recurrence, and lifted-action selection law

- **ID:** ULF-OGRPM-1
- **Stage:** 2-fully-proven
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]
  [SOURCE-GENERATED POLYREFLECTION] [EXACT GLOBAL PROPERNESS]
  [RECURRENT OBSERVER / OPEN ACTION] [LEAN-PROVED FINITE CYCLIC CORE]
  [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:**
  `../../../1-in-progress/universal-law-field/orbit-generated-reflection-properness-mechanics/field-programme.md`
- **Claim:** One reflection conjugated by source evolution produces a joint-reversal reporter whose
  Gramian is exactly the orbit fusion-frame operator.  A wandering source sector gives sharp bound
  four.  In the finite cyclic model the reporter is periodic while accumulated lifted work grows
  by `4||x||^2` per cycle, so bounded lifted work selects the neutral state.

## 1. Setup

Let `H` be a real or complex Hilbert space, let `U:H->H` be unitary, and let `P:H->H` be an
orthogonal projection.  For every integer `k` define

\[
 P_k=U^kPU^{-k},\qquad J_k=2P_k-I,\qquad D_k=I+J_k.
 \tag{ORT.1}
\]

Write `E=ran(P)` and

\[
 \mathcal E=\overline{\operatorname{span}}\{U^kE:k\in\mathbb Z\}.
 \tag{ORT.2}
\]

No family of reversals is supplied independently: `(J_k)` is generated from `(J_0,U)`.

## 2. Generated-reversal and orbit-analysis theorem

### Theorem 2.1

For every integer `k`:

1. `P_k` is an orthogonal projection;
2. `J_k` is a self-adjoint unitary involution;
3. `J_(k+1)=U J_k U^{-1}`;
4. `D_k=2P_k`;
5. for every finite `F subset Z` and every `x in H`,

   \[
   \sum_{k\in F}\|D_kx\|^2
   =4\sum_{k\in F}\|PU^{-k}x\|^2;
   \tag{ORT.3}
   \]

6. the common odd sector is

   \[
   \bigcap_{k\in\mathbb Z}\ker D_k=\mathcal E^\perp.
   \tag{ORT.4}
   \]

Consequently the generated reversals select zero exactly when `E` is cyclic for `U`, and they are
stably selecting exactly when the orbit subspaces form a fusion frame:

\[
 A\|x\|^2\le\sum_{k\in\mathbb Z}\|P_kx\|^2\le B\|x\|^2
 \quad(0<A\le B<\infty).
 \tag{ORT.5}


### Proof

Unitary conjugation preserves adjoints, products, and identities, so

\[
 P_k^*=P_k,qquad P_k^2=P_k.
\]

Hence

\[
 J_k^*=J_k,qquad
 J_k^2=(2P_k-I)^2=4P_k^2-4P_k+I=I.
\]

This proves (1)--(2).  Equation (3) follows directly from

\[
 U(U^kPU^{-k})U^{-1}=U^{k+1}PU^{-(k+1)}.
\]

Equation (4) is `I+(2P_k-I)=2P_k`.  Since `P_k=U^kPU^{-k}` and `U^k` is an isometry,

\[
 \|P_kx\|=\|PU^{-k}x\|.
\]

Squaring and summing gives `(ORT.3)`.

Finally,

\[
 x\in\ker D_k
 \Longleftrightarrow P_kx=0
 \Longleftrightarrow x\perp U^kE.
\]

Intersecting over `k` gives `(ORT.4)`.  Vanishing of this intersection is equivalent to
`mathcal E=H`.  The two-sided estimate `(ORT.5)` is by definition the fusion-frame estimate, and
`(ORT.3)` multiplies both bounds by four for the reversal defects.  QED.

## 3. Wandering-sector global properness

### Theorem 3.1

Assume the orbit subspaces are pairwise orthogonal and complete:

\[
 H=\bigoplus_{k\in I}U^kE
 \tag{ORT.6}


for `I=Z` or a finite cyclic index set.  Then for every `x in H`,

\[
 \boxed{\sum_{k\in I}\|(I+J_k)x\|^2=4\|x\|^2.}
 \tag{ORT.7}


Thus the generated joint-reversal Gramian is exactly `4I`; its properness constant neither decays
with aperture nor depends on the dimension.

### Proof

The orthogonal decomposition theorem gives Parseval's identity

\[
 \sum_{k\in I}\|P_kx\|^2=\|x\|^2.
\]

Apply `(ORT.3)` to finite partial sums and pass monotonically to the complete sum.  QED.

## 4. Exact finite cyclic model

Fix `N>=1` and put `H_N=K^N`, with standard coordinate basis `(e_0,...,e_(N-1))`.  Let

\[
 Ue_j=e_{j+1\pmod N},\qquad P_0x=\langle x,e_0\rangle e_0.
 \tag{ORT.8}


Then `P_k` is coordinate projection onto `K e_k`, so

\[
 (J_kx)_j=
 \begin{cases}
 x_j,&j=k,\\
 -x_j,&j\ne k,
 \end{cases}
 \qquad
 (D_kx)_j=
 \begin{cases}
 2x_j,&j=k,\\
 0,&j\ne k.
 \end{cases}
 \tag{ORT.9}


Theorem 3.1 becomes the coordinate identity

\[
 \boxed{\sum_{k=0}^{N-1}\sum_{j=0}^{N-1}|x_j+(J_kx)_j|^2
 =4\sum_{j=0}^{N-1}|x_j|^2.}
 \tag{ORT.10}


### Corollary 4.1 — joint selection

If `J_kx=-x` for every `k`, then `x=0`.  Quantitatively, `(ORT.10)` gives the exact lower bound
four for the complete joint-odd reporter.

### Proof

The hypothesis is `D_kx=0` for every `k`.  The left side of `(ORT.10)` is zero, so
`4||x||^2=0`.  QED.

## 5. Recurrent observer and open lifted work

The reversal observer is periodic:

\[
 J_{m+N}=J_m.
 \tag{ORT.11}


Retain, however, the marked execution index `m in N`.  Define work through `q` completed cycles by

\[
 \mathcal A_q(x)=\sum_{m=0}^{qN-1}\|(I+J_{m\bmod N})x\|^2.
 \tag{ORT.12}


### Theorem 5.1 — lifted-action properness

For every natural number `q`,

\[
 \boxed{\mathcal A_q(x)=4q\|x\|^2.}
 \tag{ORT.13}


Consequently

\[
 \sup_q\mathcal A_q(x)<\infty\quad\Longleftrightarrow\quad x=0.
 \tag{ORT.14}


The reporter orbit closes after every `N` steps, while the marked history and action remain open.

### Proof

Partition `{0,...,qN-1}` into the `q` consecutive blocks of length `N`.  Periodicity makes each
block sum equal to `(ORT.10)`, namely `4||x||^2`.  Summing the `q` identical blocks proves
`(ORT.13)`.  If `x=0`, every action is zero.  If `x!=0`, then `4||x||^2>0` and the right side of
`(ORT.13)` tends to infinity with `q`, proving `(ORT.14)`.  QED.

## 6. Common-recovery neutrality

Let `L:H->K` be an isometry and suppose there are operators `tilde U, tilde P` on `K` such that

\[
 LU=\widetilde UL,\qquad LP=\widetilde PL.
 \tag{ORT.15}


Define `tilde J_k=2 tilde U^k tilde P tilde U^{-k}-I`.  Then

\[
 L D_k=\widetilde D_kL,qquad
 \|\widetilde D_kLx\|=\|D_kx\|.
 \tag{ORT.16}


Thus every identity and lower bound above is unchanged by common isometric recovery.  For split
Markov formation, the separately proved packet theorem gives the analogous exact KL/Jeffreys
isometry.  Neither recovery doctrine creates the orbit bound; both transport it without loss.

### Proof

Intertwining is stable under products, inverses of unitary restrictions, sums, and scalar
multiplication.  Therefore `LJ_k=tilde J_kL`, hence `LD_k=tilde D_kL`.  Isometry of `L` gives the
norm identity.  QED.

## 7. Sharp infinite-dimensional boundary

Completeness is not properness.  Let `H=ell^2(Z)`, let `U` be the bilateral shift, and let
`phi=e_0-e_1`.  Put `E=C phi`.  Under the Fourier transform, `phi` is the multiplier `1-z`, which is
nonzero almost everywhere on the circle.  Therefore the closed span of `(U^k phi)` is all of `H`:
the common odd sector is zero.

But

\[
 \sum_{k\in\mathbb Z}\|P_{U^kE}x\|^2
 =\frac1{\|\phi\|^2}\sum_k|\langle x,U^k\phi\rangle|^2
 =\frac1{2}\int_{S^1}|\widehat x(z)|^2|1-z|^2\,dz.
 \tag{ORT.17}


Choose unit Fourier functions supported on arcs shrinking to `z=1`.  The right side tends to zero.
Hence the orbit is complete but has no positive lower frame bound.  This is the exact cofinal wall:
joint reversals may be injective while adaptive almost-odd histories destroy stable selection.

## 8. What the theorem changes

The earlier joint-reversal theorem required several source-marked reversals.  This theorem proves a
strictly more generative route:

\[
 \boxed{\text{one reversal}+\text{one legal source evolution}
 \longrightarrow\text{a complete generated reversal atlas}.}
 \tag{ORT.18}


It couples five structurally different organs without identifying them:

1. functional reflection supplies `J_0`;
2. legal source evolution supplies conjugation by `U`;
3. positive observation is the orbit-defect Gramian;
4. recurrence is periodicity of the observed reversal;
5. global properness is boundedness of the lifted accumulated action.

The exact fourth-organ prediction is `(ORT.13)`: a closed finite observer cycle can carry linearly
divergent source action, with slope fixed by the joint reversal frame constant.

## 9. Hostile scope and significance audit

1. **Not new frame theory.**  Orbit frames, fusion frames, dynamical sampling, observability
   Gramians, and wandering subspaces are established mathematics.
2. **Not automatic.**  If `UP=PU`, every generated reversal is `J_0`; no odd direction is removed.
3. **Not finite-to-infinite by fiat.**  Section 7 proves exact injective/nonproper failure.
4. **Not information selection.**  Common recovery and reversible functional action preserve
   information and the orbit energy.
5. **Not yet arithmetic.**  The theorem does not construct `U` and `P` from the literal pre-zero
   RH source.  That is the next source-realization gate.
6. **Not RH.**  No zero, divisor specialization, or RH-equivalent boundedness is assumed or proved.

External parents:

- Calderbank--Casazza--Heinecke--Kutyniok--Pezeshki,
  *Fusion Frames: Existence and Construction*, <https://arxiv.org/abs/0906.5606>.
- Iverson, *Frames generated by compact group actions*, <https://arxiv.org/abs/1509.06802>.
- Christensen--Hasannasab, *A survey on frame representations via dynamical sampling*,
  <https://arxiv.org/abs/2201.00038>.

The generic machinery is `[REDISCOVERED/BRIDGE]`.  The exact unconditional corpus leverage is the
replacement of “several independent reversals” by a generated conjugacy orbit, together with the
closed-observer/open-action identity `(ORT.13)` and the sharp completeness/properness separation.

## 10. Lean gate

Formalize exactly:

1. coordinate reversals on finite families;
2. involutivity and defect support;
3. tight cycle identity `(ORT.10)`;
4. common-odd selection;
5. repeated-cycle identity `(ORT.13)` and bounded-work selection.

The abstract Hilbert/fusion-frame theorem and bilateral-shift countermodel may reuse later analysis
infrastructure; until formalized they remain paper-proved only.

## Log

- 2026-08-14 — complete paper proof closed after orbit-frame and fusion-frame collision audit.
- 2026-08-14 — source-realization gate kept open; no RH or novelty claim.
