# Beta-threshold complete-incidence law

- **ID:** `beta-threshold-complete-incidence-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SHARP BOUNDED REPLICA REDUCTION
- **Parents:** `bures-incidence-minimax-coarea-law.md`,
  `gapped-eigenstate-uniform-shortcut-floor.md`,
  `quenched-krylov-circuit-incidence-front-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [FRONTIER CORRECTION] [EXTERNAL PRIORITY OPEN]`
- **Formalized companion:** `./beta-threshold-complete-incidence-law-formalized.md`
- **Statement:** A bounded binomial replica projector is, exactly, a beta-normalized average of the
  complete approximate-tube incidence mass.  With fixed error slack it sandwiches the desired
  shortcut probability up to `exp(-Theta(r))`, while paying every rare return or fibre sheet only
  at its actual probability and never multiplying it by the monomial factor `a^(-r)`.

## Public sentence

Growing replicas should test whether an overlap crosses the observational threshold, not raise the
overlap to a power and then divide by that threshold.  The former is a bounded quantum test and an
exact coarea average; the latter can magnify an exponentially rare return tube into a useless
exponential error.

This theorem replaces the overly strong Bures-monomial finite-onset target.  It does not itself
prove local-Hamiltonian anti-concentration.

## Setup

Let `(Omega,mu)` be a probability space, `V` a finite-dimensional complex Hilbert space, and
`psi:Omega->V` a measurable unit-vector field.  Let `Z` be a finite nonempty set of unit target
vectors.  Define the complete occupied-target fidelity

\[
 X_z(\omega)=|\langle z,\psi(\omega)\rangle|^2,
 \qquad
 Y_Z(\omega)=\max_{z\in Z}X_z(\omega).                           \tag{1}
\]

Repeated labels do not change `Y_Z`.  Every source point is integrated before any quotient, so
distinct source fibre sheets retain their full measure.

Fix

\[
 0<b<a<1,\qquad \delta=a-b,\qquad
 q={a+b\over2}.                                                   \tag{2}
\]

For replica order `r>=1`, put `k=ceil(rq)` and define the binomial-tail polynomial

\[
 \mathcal B_{r,k}(x)
 =\sum_{j=k}^r{r\choose j}x^j(1-x)^{r-j},
 \qquad 0\le x\le1.                                              \tag{3}
\]

It is increasing and takes values in `[0,1]`.  Define the bounded complete-incidence action

\[
 \mathfrak I_{r;a,b}(\psi,Z)
 =\int_\Omega \mathcal B_{r,k}(Y_Z(\omega))\,d\mu(\omega).       \tag{4}
\]

## Theorem A -- sharp threshold sandwich

Let

\[
 \eta_r=\exp\left(-{r\delta^2\over2}\right).                    \tag{5}
\]

Then

\[
 \boxed{
 (1-\eta_r)\,\mu\{Y_Z\ge a\}
 \le \mathfrak I_{r;a,b}(\psi,Z)
 \le \mu\{Y_Z\ge b\}+\eta_r.}                                \tag{6}
\]

In particular, when `r>=2 log(2)/delta^2`,

\[
 \boxed{
 \mu\{Y_Z\ge a\}
 \le2\mathfrak I_{r;a,b}(\psi,Z).}                              \tag{7}
\]

Thus decay of `(4)` is equivalent, up to fixed observational slack and an
`exp(-Theta(r))` remainder, to decay of the complete approximate shortcut tube itself.

### Proof

For `S_x` binomial with parameters `(r,x)`, equation `(3)` is

\[
 \mathcal B_{r,k}(x)=\Pr\{S_x\ge k\}.                            \tag{8}
\]

If `x>=a`, then `(k-1)/r<q<=x-delta/2`.  Hoeffding's lower-tail inequality gives

\[
 \mathcal B_{r,k}(x)
 \ge1-\exp(-r\delta^2/2)=1-\eta_r.                              \tag{9}
\]

If `x<=b`, then `k/r>=q>=x+delta/2`, and the upper-tail inequality gives

\[
 \mathcal B_{r,k}(x)\le\eta_r.                                 \tag{10}
\]

Apply `(9)--(10)` pointwise to `x=Y_Z(omega)` and integrate.  This proves `(6)`.
When `eta_r<=1/2`, its first inequality gives `(7)`.

## Theorem B -- exact beta-coarea identity

For `1<=k<=r`,

\[
 {d\over dx}\mathcal B_{r,k}(x)
 =r{r-1\choose k-1}x^{k-1}(1-x)^{r-k}.                           \tag{11}
\]

The right side is the probability density of a `Beta(k,r-k+1)` random variable; in particular it
integrates to one.  Consequently

\[
 \boxed{
 \mathfrak I_{r;a,b}(\psi,Z)
 =\int_0^1
   r{r-1\choose k-1}u^{k-1}(1-u)^{r-k}
   \mu\{Y_Z\ge u\}\,du.}                                      \tag{12}
\]

Equation `(12)` is an exact incidence-normalized coarea law.  The tube union is formed first at
each physical threshold `u`; only then is it averaged against one unit-mass beta kernel.  Circuit
duplicates, target parametrizations, and source-sheet relabellings cannot change it.

### Proof

Differentiate `(3)`.  Using

\[
 j{r\choose j}=r{r-1\choose j-1},\qquad
 (r-j){r\choose j}=r{r-1\choose j},                              \tag{13}
\]

the two sums telescope, leaving `(11)`.  Since `B_(r,k)(0)=0`,

\[
 \mathcal B_{r,k}(x)=\int_0^x \mathcal B_{r,k}'(u)\,du.          \tag{14}
\]

Insert `x=Y_Z(omega)`, apply Tonelli to the nonnegative integrand, and obtain `(12)`.

## Theorem B' -- exact return excision before incidence formation

Let `R subseteq Omega` be measurable and define the return-excised statistic

\[
 \mathfrak I^R_{r;a,b}(\psi,Z)
 =\int_{\Omega\setminus R}\mathcal B_{r,k}(Y_Z(\omega))\,d\mu(\omega). \tag{15}
\]

Then

\[
 \boxed{
 (1-\eta_r)\,\mu(\{Y_Z\ge a\}\setminus R)
 \le \mathfrak I^R_{r;a,b}(\psi,Z)
 \le \mu(\{Y_Z\ge b\}\setminus R)
       +\eta_r\mu(\Omega\setminus R).}                         \tag{16}
\]

Moreover, return removal commutes exactly with the beta-threshold decomposition:

\[
 \boxed{
 \mathfrak I^R_{r;a,b}(\psi,Z)
 =\int_0^1
   r{r-1\choose k-1}u^{k-1}(1-u)^{r-k}
   \mu\bigl((\Omega\setminus R)\cap\{Y_Z\ge u\}\bigr)\,du.} \tag{17}
\]

Consequently

\[
 \boxed{
 \mu\{Y_Z\ge a\}
 \le \mu(R)+{\mathfrak I^R_{r;a,b}(\psi,Z)\over1-\eta_r}.}     \tag{18}
\]

When `eta_r<=1/2`, the last term is at most
`2 I^R_(r;a,b)`.  Thus a
target-independent return or easy-carrier set is paid once, with coefficient one.  No
`R times R^c` mixed pair is ever formed.  Integration still occurs on the original source space,
so distinct fibre sheets outside `R` retain their full multiplicity even when they share an
endpoint or a circuit label.

### Proof

Multiply the pointwise bounds `(9)--(10)` by `1_(Omega setminus R)` and integrate to obtain `(16)`.
Apply the Tonelli argument for `(12)` to the restricted measure
`mu.restrict (Omega setminus R)` to obtain `(17)`.  Finally split
`{Y_Z>=a}` into its intersections with `R` and `Omega setminus R`, bound the first part by `mu(R)`,
and apply the left inequality of `(16)` to the second.

## Theorem C -- literal bounded replica projector

For a unit target `z`, write `P_z=|z><z|`.  On `V^(tensor r)`, define

\[
 Q_{z;r,k}
 =\sum_{\substack{S\subseteq\{1,\ldots,r\}\\|S|\ge k}}
   \bigotimes_{i=1}^r
   \begin{cases}
     P_z,&i\in S,\\
     I-P_z,&i\notin S.
   \end{cases}                                                   \tag{19}
\]

The summands are mutually orthogonal projections.  Hence

\[
 \boxed{Q_{z;r,k}^2=Q_{z;r,k}=Q_{z;r,k}^*,\qquad0\le Q_{z;r,k}\le I.} \tag{20}
\]

For every unit `v`,

\[
 \boxed{
 \langle v^{\otimes r},Q_{z;r,k}v^{\otimes r}\rangle
 =\mathcal B_{r,k}(|\langle z,v\rangle|^2).}                    \tag{21}
\]

Therefore `(4)` is the ensemble expectation of the best occupied-target bounded replica test:

\[
 \boxed{
 \mathfrak I_{r;a,b}(\psi,Z)
 =\int_\Omega\max_{z\in Z}
 \langle\psi(\omega)^{\otimes r},
 Q_{z;r,k}\psi(\omega)^{\otimes r}\rangle\,d\mu(\omega).}     \tag{22}
\]

### Proof

At each replica position, `P_z` and `I-P_z` are complementary orthogonal projections.  Distinct
outcome strings in `(19)` are orthogonal, proving `(20)`.  Product factorization gives probability
`x^j(1-x)^(r-j)` for every string with `j` successes, where
`x=|<z,v>|^2`.  Summing the `binom(r,j)` strings proves `(21)`.  Monotonicity of
`B_(r,k)` makes maximum over `z` commute with it, proving `(22)`.

## Corollary -- operational circuit tubes

Let `Z_s` be the distinct states prepared by circuits of depth at most `s`.  For pure-state trace
distance, choose

\[
 a=1-\epsilon_-^2,qquad b=1-\epsilon_+^2,qquad
 0<\epsilon_-<\epsilon_+<1.                                    \tag{23}
\]

Then `delta=epsilon_+^2-epsilon_-^2`, and `(6)` becomes

\[
 \boxed{
 (1-\eta_r)\Pr\{C_{\epsilon_-}(\psi)\le s\}
 \le\mathfrak I_{r;a,b}(\psi,Z_s)
 \le\Pr\{C_{\epsilon_+}(\psi)\le s\}+\eta_r.}                \tag{24}
\]

No circuit-word union factor appears in `(20)`: the actual occupied endpoint image is maximized
before integration.  Any later upper bound may exploit its geometry, but cannot replace it by a
label count without explicitly paying that loss.

## Strict separation from the monomial/Bures reporter

Let one target have squared overlap `X=1` on a source set of probability `p` and `X=0` elsewhere.
For every `1<=k<=r`,

\[
 \mathfrak I_{r;a,b}=p.                                         \tag{25}
\]

The monomial Markov reporter instead gives

\[
 a^{-r}\mathbb E X^r=a^{-r}p.                                   \tag{26}
\]

Thus its overestimate relative to the bounded test is exactly `a^(-r)`.  If, for example,
`p=exp(-sqrt(r))`, the physical exceptional tube vanishes while `(26)` grows exponentially.  This
is precisely the pathology exposed by gapped easy-eigenline boxes and near-return sheets.

The Bures minimax law remains an exact optimum **within its positive ellipsoidal monomial
reporters**.  Theorem C changes the statistical experiment: it uses a bounded hypothesis test with
both success and failure outcomes.  Hence it is not contradicted by Bures optimality and can be
exponentially sharper for approximate-tube probabilities.

## Conjecturing and falsification ledger

### C0 -- improve the Bures nuclear-norm estimate using Casimir Hall expansion

**Failed.**  Bi-tight Casimir scaling gives exact rank and Hilbert--Schmidt energy expansion, but an
upper bound on nuclear norm still costs the square root of occupied rank.  No singular-value decay
follows from Hall expansion; one-local Pauli words already span the full operator algebra.

### C1 -- optimize the monomial threshold constant

**Failed structurally.**  Every bound `1_{X>=a}<=a^(-r)X^r` multiplies a genuine high-overlap tube
by `a^(-r)`.  Better collision constants cannot remove this amplification.

### C2 -- cap the monomial after integration

**Failed.**  `min(1,a^(-r)E X^r)` has already forgotten source sheets.  One rare sheet can dominate
the expectation before the cap and cannot be paid once.

### C3 -- perform a bounded repeated threshold experiment before source integration

**Proved.**  Theorems A--C give the exact binomial projector and beta-coarea law.  Every source sheet
contributes a number in `[0,1]`; complete occupied-target maximization precedes integration; fixed
radius slack costs only `exp(-Theta(r))`.

### Positive survivor

The finite-onset frontier is no longer the exponentially stronger monomial Bures contraction
`a^(-r)B_r=o(1)`.  It is enough, and up to observational slack necessary, to prove

\[
 \boxed{
 \mathfrak I_{r;a,b}
 =\mathbb E_H\max_{z\in Z_s}
   \langle\psi_H(t)^{\otimes r},Q_{z;r,k}\psi_H(t)^{\otimes r}\rangle
 =o_n(1)}                                                       \tag{27}
\]

for `r` scale-matched to time and circuit budget.  Equation `(12)` says this is exactly a quenched
beta-window average of complete approximate-tube coarea mass, not a pseudodeterminant, minimum gap,
raw targetwise moment, or ellipsoidal covariance surrogate.

More generally, for any physically specified, target-independent return/easy-carrier set `R_n`,
Theorem B' reduces the same frontier to

\[
 \boxed{
 \Pr(R_n)+\mathfrak I^{R_n}_{r;a,b}(\psi_H(t),Z_s)=o_n(1).}      \tag{28}
\]

Unlike the former pair-action reduction, `(28)` forms no mixed return/nonreturn covariance and
requires no occupied-rank prefactor.  Return mass and every surviving fibre sheet are charged at
their actual source probability.

## Hostile audit

1. **Reduction, not anti-concentration.**  Equations `(27)--(28)` are still unproved for ordinary static
   local Hamiltonians.  No Brown growth claim follows yet.
2. **The max remains hard.**  The exact occupied circuit image is retained.  Replacing it by a sum
   reintroduces circuit entropy; replacing it by a span can be arbitrarily loose.
3. **Standard probability ingredients.**  Hoeffding, binomial projectors, and beta densities are
   classical.  Candidate new knowledge is their exact complete-incidence composition and the
   identification that monomial/Bures amplification is the wrong approximate-tube invariant.
4. **Bures theorem is not false.**  It remains optimal for its reporter class.  It is insufficient
   for rare-sheet finite onset because that reporter class answers a stronger moment question.
5. **No external priority conclusion.**  Threshold amplification and quantum hypothesis testing
   are broad literatures.  The claimed frontier correction needs targeted expert review.
6. **Lean closure.**  Theorems A, B, B', C, the trace-distance corollary `(24)` and the
   monomial separation `(25)`--`(26)` are formalized unconditionally in
   `HTGeometry/BinomialTailBetaThreshold`, `HTGeometry/BetaThresholdIncidenceLaw` and
   `HTGeometry/BoundedReplicaThresholdProjector`.  The unproved part is `(27)`--`(28)`, the
   dynamical anti-concentration statement, which is a parent-card research target.

## Exact next move

Work at the beta level `(17)`, not at exact-overlap maxima.  For thresholds `u` in the
`O(r^(-1/2))` beta window around `q=(a+b)/2`, prove a quenched coarea bound on the union of actual
depth-`s` endpoint tubes after one target-independent return/easy-carrier excision.  The bound may
be only `o_n(1)`; it need not be `exp(-Theta(r))`.  It must retain source fibre multiplicity and
perform the occupied endpoint union before threshold averaging.

## Lean realization

All six layers are built; see the formalized companion for the declaration-by-declaration map.

1. finite binomial-tail polynomial, monotonicity, and Hoeffding sandwich --
   `binomialTail`, `binomialTail_monotoneOn`, `binomialTail_replicaThreshold_le`,
   `one_sub_le_binomialTail_replicaThreshold`;
2. derivative telescoping and beta-density normalization --
   `hasDerivAt_binomialTail`, `intervalIntegral_betaKernel_eq_one`;
3. restricted-source beta identity and return-paid-once inequality `(16)--(18)` --
   `restrictedIncidenceAction_eq_betaCoarea`,
   `measure_le_return_add_restrictedIncidenceAction`;
4. finite tensor outcome projections and expectation identity `(21)` --
   `boundedReplicaProjector_mul_self`, `quadForm_boundedReplicaProjector`;
5. finite target maximum and trace-distance circuit-tube sandwich `(24)` --
   `sup'_replicaTest`, `incidenceAction_traceDistance_sandwich`;
6. strict monomial-separation example `(25)--(26)` --
   `monomial_reporter_eq_pow_mul_incidenceAction`.

## Log

- 2026-08-09 -- Casimir/nuclear route falsified; bounded binomial replica test and exact
  beta-threshold complete-incidence coarea law proved on paper.
- 2026-08-09 -- formalized: all six Lean layers built and closed unconditionally; promoted to
  stage 3.
