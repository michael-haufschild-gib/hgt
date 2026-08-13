# Split-recovery formation-capital monotonicity and functional-equation neutrality law

- **ID:** ULF-SGOGM-2
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / CROSS-MECHANISM FUSION LAW
- **Source programme:**
  `../../../1-in-progress/universal-law-field/source-generated-orbit-gramian-mechanics/field-programme.md`
- **Orbit-capital parent:**
  `cyclic-heat-orbit-gramian-lyapunov-properness-and-corona-selection-law.md`
- **Packet-lift parent:**
  `../packet-formation-mechanics/functional-equation-split-formation-lift-information-isometry-and-work-no-go.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[FORMATION/RECOVERY/FE FUSION] [EXACT NEUTRALITY CLASSIFICATION]`
  `[LEAN PENDING] [NOT RH]`

## 1. Purpose

Two prior mechanisms were exact but disconnected.

1. A source orbit `W` generates an endogenous inverse-Gramian cost equal to least formation
   capital.
2. A common recovery kernel lifts functional-equation transport without changing relative
   entropy.

The missing question was whether common recovery or functional-equation transport can improve the
formation capital required by an RH-bearing defect. This card answers exactly:

\[
 \boxed{
 \text{post-recovery capital never increases;}
 \quad
 \text{split recovery and invertible functional equations preserve it exactly.}}
 \tag{RCN.1}
\]

Strict decrease is possible only by identifying a nonzero defect direction with zero through the
recovery kernel. It is information loss, not new financing.

## 2. Abstract formation capital

Let `K,H,U,H'` be complex Hilbert spaces. Let

\[
 W:K\to H,
 \qquad X:U\to H
 \tag{RCN.2}
\]

be bounded and Hilbert--Schmidt respectively. Define the extended formation capital

\[
 \mathfrak c_W(X)
 :=\inf\left\{\|B\|_{\mathrm{HS}}^2:
 B:U\to K\text{ Hilbert--Schmidt},\ WB=X\right\},
 \tag{RCN.3}
\]

with value `+infinity` when the factorization set is empty. If nonempty, the infimum is attained by
the unique factor orthogonal to

\[
 \ker(W_*),
 \qquad
 W_*:\mathcal S_2(U,K)\to\mathcal S_2(U,H),
 \quad W_*(B)=WB.
 \tag{RCN.4}
\]

Indeed, the solution set is a closed affine subspace of the Hilbert space `S_2(U,K)`.

## 3. Main theorem

### Theorem 3.1 — recovery monotonicity and exact kernel formula

Let `R:H->H'` be bounded. Then

\[
 \boxed{
 \mathfrak c_{RW}(RX)
 =\inf\left\{\|B\|_{\mathrm{HS}}^2:
 WB-X\in\ker R\right\}
 \le \mathfrak c_W(X).}
 \tag{RCN.5}
\]

The following consequences are exact.

#### I. Injective recovery is capital-neutral

If `R` is injective, then

\[
 \boxed{\mathfrak c_{RW}(RX)=\mathfrak c_W(X).}
 \tag{RCN.6}
\]

The factorization sets themselves are identical.

#### II. Split recovery is capital-neutral

If `R` has a bounded left inverse `Q:H'->H`, so that

\[
 QR=1_H,
 \tag{RCN.7}
\]

then `(RCN.6)` holds. Thus extending a packet by a common split recovery kernel cannot make its
source formation cheaper or more expensive.

#### III. Strict gain is kernel erasure

If

\[
 \mathfrak c_{RW}(RX)<\mathfrak c_W(X),
 \tag{RCN.8}
\]

then `R` is noninjective and the cheaper factor satisfies

\[
 WB-X\in\ker R\setminus\{0\}.
 \tag{RCN.9}
\]

Hence every strict capital improvement is obtained by erasing a nonzero formation residual.

#### IV. Serial recovery obeys a data-processing chain

For bounded `R_1:H->H_1` and `R_2:H_1->H_2`,

\[
 \boxed{
 \mathfrak c_{R_2R_1W}(R_2R_1X)
 \le
 \mathfrak c_{R_1W}(R_1X)
 \le
 \mathfrak c_W(X).}
 \tag{RCN.10}
\]

Equality holds throughout when both recovery maps are injective.

### Proof

For a Hilbert--Schmidt `B`,

\[
 (RW)B=RX
 \iff R(WB-X)=0
 \iff WB-X\in\ker R.
 \tag{RCN.11}
\]

Taking the infimum of the same Hilbert--Schmidt norm proves the equality in `(RCN.5)`. Every exact
factorization `WB=X` is admissible after applying `R`, proving the inequality. If `R` is injective,
`(RCN.11)` reduces to `WB=X`, proving `(RCN.6)`. A left inverse forces injectivity, proving II. If
strict inequality held with zero residual, the cheaper factor would already be admissible before
recovery, a contradiction; this proves III. Applying `(RCN.5)` twice proves IV. QED.

## 4. Functional-equation capital isometry

Let `A:H->H_A` be a bounded linear isomorphism, representing a functional-equation change of
sheet. Transport source formation and defect together:

\[
 W_A=AW,
 \qquad X_A=AX.
 \tag{RCN.12}
\]

Since `A` is injective, Theorem 3.1 gives

\[
 \boxed{
 \mathfrak c_{W_A}(X_A)=\mathfrak c_W(X).}
 \tag{RCN.13}
\]

No unitarity is needed. If `A` is involutive or unitary, that additional structure affects
coordinates or metric realization, not the factorization capital.

Now let `E:H_A->\widehat H_A` be a split recovery embedding with `QE=1`. The recovered
functional-equation packet has

\[
 \widehat W_A=EAW,
 \qquad \widehat X_A=EAX.
 \tag{RCN.14}
\]

Applying `(RCN.6)` twice gives the fusion identity

\[
 \boxed{
 \mathfrak c_{\widehat W_A}(\widehat X_A)
 =\mathfrak c_{W_A}(X_A)
 =\mathfrak c_W(X).}
 \tag{RCN.15}
\]

Thus the functional equation lifts through every common split recovery kernel as a formation-
capital isometry.

## 5. Orbit-Gramian specialization

Let `W:L^2(0,infinity)->H` be the heat-orbit reachability operator from `ULF-SGOGM-1`, with
`WW*=G`. Its formation-reconstruction theorem states

\[
 \mathfrak c_W(X)
 =\mathcal E_G(XX^*)
 =\|G^{-1/2}X\|_{\mathrm{HS}}^2.
 \tag{RCN.16}
\]

For an injective recovery `R`, let

\[
 H_R=\overline{R(H)}\subset H'
 \tag{RCN.17}
\]

be the recovered carrier, and set

\[
 W_R=RW,
 \qquad G_R=W_RW_R^*=RGR^*.
 \tag{RCN.18}
\]

Viewed on `H_R`, the operator `G_R` is injective: if
`<y,G_Ry>=<R*y,GR*y>=0`, then injectivity of `G` gives `R*y=0`, while
`y in closure(Ran R)` forces `y=0`. The least-control form of `G_R` and Theorem 3.1 therefore give

\[
 \boxed{
 \mathcal E_{G_R}(RXX^*R^*)
 =\mathcal E_G(XX^*).}
 \tag{RCN.19}
\]

Equation `(RCN.19)` is the properness counterpart of KL information neutrality. A common split
recovery preserves both the statistical separation of packet laws and the exact source work needed
to form their defect.

## 6. Common Markov recovery

Let `mu,nu` be probability measures on a standard Borel observer space `X`, and let `K(x,dh)` be a
parameter-independent Markov kernel. The split packet laws are

\[
 \widehat\mu(dx,dh)=\mu(dx)K(x,dh),
 \qquad
 \widehat\nu(dx,dh)=\nu(dx)K(x,dh).
 \tag{RCN.20}
\]

Marginalization is a left inverse to packet extension. Moreover

\[
 D(\widehat\mu\Vert\widehat\nu)=D(\mu\Vert\nu).
 \tag{RCN.21}
\]

The first statement is immediate by integrating `K(x,dh)=1`. For the second, the
Radon--Nikodym derivative is

\[
 {d\widehat\mu\over d\widehat\nu}(x,h)
 ={d\mu\over d\nu}(x)
 \tag{RCN.22}
\]

on the common conditional support, and integration over `h` gives `(RCN.21)`; the singular case is
preserved as well by marginalization.

On `L^2` score spaces, packet extension is the isometry

\[
 E_{\mu,K}f(x,h)=f(x),
 \qquad
 \|E_{\mu,K}f\|_{L^2(\widehat\mu)}=\|f\|_{L^2(\mu)}.
 \tag{RCN.23}
\]

Therefore the packet theorem's information-neutral functional-equation lift and `(RCN.15)` are
two exact faces of the same split-recovery law:

\[
 \boxed{
 \text{common conditional formation preserves divergence and least source capital.}}
 \tag{RCN.24}
\]

## 7. Sharp countermodels and scope

### 7.1 Noninjective recovery can erase all capital

Take `H=K=C^2`, `U=C`, `W=1`, and `X(1)=e_2`. Let

\[
 R(z_1,z_2)=z_1.
 \tag{RCN.25}
\]

Then

\[
 \mathfrak c_W(X)=1,
 \qquad RX=0,
 \qquad \mathfrak c_{RW}(RX)=0.
 \tag{RCN.26}
\]

The apparent gain is exactly loss of the `e_2` direction.

### 7.2 Recovery neutrality does not imply selection

If an off-center defect has finite or infinite capital before common recovery, `(RCN.15)` gives the
same status afterward. Functional-equation symmetry plus common recovery cannot manufacture the
bounded-capital premise of the corona-selection theorem.

### 7.3 Parameter-dependent kernels are outside the theorem

If two packets use different recovery kernels, `(RCN.20)` can become a strict data-processing
inequality, and their linear recovery embeddings need not share one left inverse. Such a change is
a new constitutive operation, not common recovery.

### 7.4 Changing the source formation is outside neutrality

Replacing `W` by an unrelated `W'` can change capital arbitrarily. The theorem applies when the
same source formation is transported, not when a new cost is fitted after observing the defect.

## 8. Selection consequence and new field gate

Let `(T_n)` be positive defects with `T_n=X_nX_n*` satisfying the source-commutator condition of
`ULF-SGOGM-1`. If `R` is a common split recovery and `A` is a functional-equation isomorphism, then

\[
 \sup_n\mathcal E_G(T_n)<\infty
 \iff
 \sup_n\mathcal E_{EAG A^*E^*}(EAX_nX_n^*A^*E^*)<\infty.
 \tag{RCN.26}
\]

Therefore neither operation can supply the missing bounded-capital premise by transport alone.
The missing selection mechanism must do at least one of the following:

1. create a source factorization that did not previously exist;
2. bound its least capital by an independently generated source work law;
3. change the source formation operator itself;
4. use a noninjective quotient and explicitly account for the information it erases.

This is the exact pivot. Search should target a **capital-generating intervention**, not another
functional-equation lift or common recovery completion.

## 9. Parent boundary and hostile verdict

The Hilbert-space proof is elementary quotient-norm/least-squares geometry. KL invariance under a
common conditional kernel is standard statistical sufficiency. No external novelty claim is made.

The corpus delta is their exact fusion with source-generated inverse-Gramian properness:

- recovery data processing now has a least-capital counterpart;
- strict capital gain is classified as recovery-kernel erasure;
- functional-equation transport and common recovery are proved incapable of supplying the missing
  properness premise;
- the next load-bearing operation is isolated as source-capital generation.

- [x] abstract recovery theorem dependency-closed;
- [x] exact kernel classification;
- [x] serial composition law;
- [x] functional-equation capital isometry;
- [x] orbit-Gramian specialization;
- [x] common-Markov information fusion;
- [x] sharp noninjective countermodel;
- [ ] Lean formalization in a later formalization pass;
- [ ] literal source-capital producer;
- [ ] RH selection consequence.

No Lean was written or built during this research pass.
