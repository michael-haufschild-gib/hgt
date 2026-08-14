# Prime-torsion recurrence-polygon complexity law

- **ID:** `prime-torsion-recurrence-polygon-complexity-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / quantum-recurrence anatomy / static-complexity advance
- **Parents:** `universal-static-choi-complexity-plateau.md`,
  `local-circuit-heap-capacity-law.md`,
  `arithmetic-static-local-hardness-recurrence-window-law.md`,
  `autonomous-return-complexity-reflection-law.md`
- **Status:** `[PAPER-PROVED] [PROVED HERE] [NOVELTY UNVERIFIED] [LEAN CORE PROVED]`
- **Date:** 2026-08-13

## Public sentence

A maximal-projective-rank autonomous quantum system has arbitrarily late recurrence cycles whose
equally spaced interior snapshots are all hard to prepare.  At Hilbert dimension `D`, one can force
linearly large circuit complexity at exponentially many rational slices of the same eventual
return, while an ordinary local Hamiltonian remains distinguishable from Haar randomness
throughout the cycle.

The theorem is existential in recurrence time.  It does not bound the first such cycle or prove
linear growth from laboratory time zero.

## 1. Uniform spectral phase torus

Let `D>=2`, let `f_1,...,f_D` be orthonormal vectors in a complex Hilbert space, and define

\[
 \Phi(z)={1\over\sqrt D}\sum_{a=1}^D z_a f_a,
 \qquad z\in\mathbb T^D.
 \tag{1}
\]

Only the projective phase class matters.  For an integer `k>=2`, let `mu_k` be the group of `k`th
roots of unity and put

\[
 \mathcal Q_{D,k}=\mu_k^D/\mu_k^{\rm diag}.
 \tag{2}
\]

Thus

\[
 |\mathcal Q_{D,k}|=k^{D-1}.
 \tag{3}
\]

Every `q in Q_(D,k)` is a projective `k`-torsion phase and `Phi(q)` is well-defined as a ray.

Use pure-state trace distance

\[
 d_{\rm tr}([u],[v])=\sqrt{1-|\langle u,v\rangle|^2}.
 \tag{4}
\]

Fix `0<delta<1/2` and define

\[
 \gamma_\delta={1-4\delta^2\over4}>0.
 \tag{5}
\]

Let `Y` be any finite dictionary of `N` normalized target rays and let

\[
 \mathcal E_{Y,\delta}^{(k)}
 =\{q\in\mathcal Q_{D,k}:\exists y\in Y,
   \ d_{\rm tr}(\Phi(q),y)\le\delta\}
 \tag{6}
\]

be the easy `k`-torsion phases.

## 2. A dimension-exponential torsion-cap bound

### Lemma A -- every target captures an exponentially small torsion fraction

For every `k>=2`,

\[
 \boxed{
 |\mathcal E_{Y,\delta}^{(k)}|
 \le 4N e^{-\gamma_\delta D}k^{D-1}.}
 \tag{7}
\]

The estimate is independent of `k`, the basis `(f_a)`, and the locations of the targets.

### Proof

It is enough to treat one target `y`.  If its `delta`-ball contains no torsion phase, the claim is
trivial.  Otherwise fix one captured class `q_0`.  Every other captured class `q` satisfies, by the
triangle inequality,

\[
 d_{\rm tr}(\Phi(q_0),\Phi(q))\le2\delta.
 \tag{8}
\]

Choose representatives and put `X_a=q_a overline(q_(0,a)) in mu_k`.  Equations `(1)` and `(4)` give

\[
 \left|{1\over D}\sum_{a=1}^D X_a\right|
 \ge\sqrt{1-4\delta^2}=:c_\delta.
 \tag{9}
\]

Count relative phases before dividing by their common diagonal action.  Under the uniform law on
`mu_k^D`, the coordinates `X_a` are independent uniform `k`th roots.  Their real and imaginary
parts have mean zero and lie in `[-1,1]`.  If the modulus in `(9)` is at least `c_delta`, then either

\[
 \left|{1\over D}\sum_a\operatorname{Re}X_a\right|
 \ge {c_\delta\over\sqrt2}
 \quad\text{or}\quad
 \left|{1\over D}\sum_a\operatorname{Im}X_a\right|
 \ge {c_\delta\over\sqrt2}.
 \tag{10}
\]

The two-sided Hoeffding inequality for `D` variables in `[-1,1]`, followed by a union bound over the
two coordinates, gives

\[
 \Pr\left\{
  \left|D^{-1}\sum_aX_a\right|\ge c_\delta
 \right\}
 \le4\exp\left(-{Dc_\delta^2\over4}\right)
 =4e^{-\gamma_\delta D}.
 \tag{11}
\]

Every projective class has exactly `k` representatives, so the same fraction bound holds in
`Q_(D,k)`.  Multiply by `k^(D-1)` and then by `N` targets to prove `(7)`. `square`

The constant is not optimized.  For `k=2`, a binary Hamming-ball calculation gives the sharper
fraction `exp[-D(log 2-h(alpha_delta))]`, where

\[
 \alpha_\delta={1-\sqrt{1-4\delta^2}\over2}
 \tag{12}
\]

and `h` is binary entropy.  The uniform bound `(7)` is used because it works simultaneously for
every torsion order.

## 3. A hard cyclic orbit inside the torsion group

### Theorem A -- prime-torsion hard polygon

Let `k` be prime.  If

\[
 \boxed{
 4(k-1)N e^{-\gamma_\delta D}<1,}
 \tag{13}
\]

then there exists `q_* in Q_(D,k)` such that

\[
 \boxed{
 d_{\rm tr}(\Phi(q_*^j),y)>\delta
 \quad
 (y\in Y,\ 1\le j\le k-1).}
 \tag{14}
\]

Thus every nonidentity vertex of one cyclic order-`k` torsion polygon avoids the complete target
dictionary.  Quantitatively, the number of points generating such a polygon is at least

\[
 \boxed{
 \left(1-4(k-1)Ne^{-\gamma_\delta D}\right)k^{D-1}.}
 \tag{14a}
\]

If the reference ray belongs to `Y`, these points split into complete generator orbits of size
`k-1`.  Hence the number of distinct hard cyclic order-`k` subgroups is at least the floor of

\[
 \boxed{
 {\left(1-4(k-1)Ne^{-\gamma_\delta D}\right)k^{D-1}\over k-1}.}
 \tag{14b}
\]

### Proof

Because `k` is prime, for every `1<=j<=k-1` the power map

\[
 P_j:\mathcal Q_{D,k}\longrightarrow\mathcal Q_{D,k},
 \qquad P_j(q)=q^j
 \tag{15}
\]

is a bijection.  Hence `P_j^(-1)(E)` has the same cardinality as `E`, where
`E=E_(Y,delta)^(k)`.  By Lemma A,

\[
 \left|\bigcup_{j=1}^{k-1}P_j^{-1}(E)\right|
 \le(k-1)|E|
 \le4(k-1)Ne^{-\gamma_\delta D}|\mathcal Q_{D,k}|.
 \tag{16}
\]

Condition `(13)` makes this union a proper subset.  Any point in its complement satisfies `(14)`.
Subtracting the right side of `(16)` from `|Q_(D,k)|` gives `(14a)`.
If the reference ray `Phi(1)` belongs to `Y`, this point is not the identity.  Since `k` is prime,
it then has exact order `k`.  Moreover the good set is invariant under every nonzero power map:
replacing `q` by `q^a` only permutes the powers `q^j`, `1<=j<=k-1`.  Its points therefore partition
into the `k-1` generators of distinct order-`k` cyclic subgroups, proving `(14b)`.  In the circuit
specialization the empty word guarantees the reference-target condition. `square`

The primality restriction is structural, not cosmetic.  At composite order, a nonunit power can
collapse a large part of `Q_(D,k)` into a lower-order torsion subgroup, so the equal-cardinality
argument in `(16)` is false.

## 4. Recurrence polygons in autonomous time

Let `E_1,...,E_D` be real energies of maximal projective rational rank: after choosing an anchor,
the `D-1` gaps are linearly independent over the rationals.  Define the autonomous trajectory

\[
 \Phi_E(t)={1\over\sqrt D}\sum_{a=1}^D e^{-itE_a}f_a.
 \tag{17}
\]

Kronecker's theorem makes its projective phase flow dense and minimal in `T^(D-1)`.

### Theorem B -- every hard torsion polygon is shadowed by arbitrarily late recurrences

Under `(13)`, for every return tolerance `rho>0` there are arbitrarily large `tau>0` such that

\[
 \boxed{
 d_{\rm tr}(\Phi_E(k\tau),\Phi_E(0))<\rho}
 \tag{18}
\]

and simultaneously

\[
 \boxed{
 d_{\rm tr}(\Phi_E(j\tau),y)>\delta
 \quad
 (y\in Y,\ 1\le j\le k-1).}
 \tag{19}
\]

Equivalently, with recurrence time `R=k tau`, every rational slice

\[
 {jR\over k},\qquad1\le j\le k-1,
 \tag{20}
\]

is target-hard, while the endpoint is an arbitrarily accurate return.

### Proof

Let `q_*` be supplied by Theorem A.  Minimality of the projective phase flow gives an unbounded
sequence `tau_m` whose phase classes converge to `q_*`.  For every fixed `j`, continuity of the
power map gives

\[
 [e^{-ij\tau_mE_a}]_a\longrightarrow q_*^j.
 \tag{21}
\]

The target dictionary and the set of powers `1<=j<=k-1` are finite.  Equation `(14)` therefore has
a strictly positive common distance margin above `delta`; for all sufficiently large `m`, `(21)`
preserves every strict inequality in `(19)`.  At the endpoint,

\[
 [e^{-ik\tau_mE_a}]_a\longrightarrow q_*^k=1,
 \tag{22}
\]

so `(18)` holds for all sufficiently large `m`.  The sequence is unbounded, proving arbitrary
lateness. `square`

Theorems A and B are the recurrence-polygon law.  Ordinary recurrence says only that the endpoint
can return.  The new constraint specifies the computational anatomy of an entire finite rational
frame inside the same recurrence cycle.

## 5. Circuit-complexity specialization

Let a finite local gate dictionary `Sigma` act on the state space.  Quotient only swaps of
support-disjoint gates, obtaining the trace monoid with alphabet size `M` and dependence degree
`Delta`.  Let `H_s` be the number of traces of length at most `s`.  The proved heap-capacity law gives

\[
 H_s\le(s+1){M+s-1\choose s}2^{\Delta s}.
 \tag{23}
\]

Take `Y` to be all circuit endpoints of traces of length at most `s`, so `N<=H_s`.  If

\[
 \boxed{
 4(k-1)(s+1){M+s-1\choose s}2^{\Delta s}
 e^{-\gamma_\delta D}<1,}
 \tag{24}
\]

then Theorem B yields arbitrarily late recurrence times `R` satisfying

\[
 \boxed{
 C_\delta\!\left(\Phi_E\!\left({jR\over k}\right)\right)>s
 \quad(1\le j\le k-1),
 \qquad
 d_{\rm tr}(\Phi_E(R),\Phi_E(0))<\rho.}
 \tag{25}
\]

No circuit target is selected after the torsion point; `(24)` pays the complete robust circuit
dictionary before the recurrence time is chosen.

### Corollary B.1 -- Hilbert-scale complexity at exponentially many recurrence slices

Suppose

\[
 D=2^n,qquad M=O(n),qquad\Delta=O(1).
 \tag{26}
\]

Choose `c>0` with

\[
 c\Delta\log2<\gamma_\delta
 \tag{27}
\]

when `Delta>0`, and any fixed `c>0` when `Delta=0`.  Put `s=floor(cD)`.  Then

\[
 \log\left((s+1){M+s-1\choose s}2^{\Delta s}\right)
 =c\Delta D\log2+o(D).
 \tag{28}
\]

For every fixed prime `k`, condition `(24)` holds for all sufficiently large `n`.  More strongly,
for every

\[
 0<\eta<\gamma_\delta-c\Delta\log2,
 \tag{29}
\]

there are primes `k_D=exp(eta D+o(D))` for which `(24)` holds.  Hence one recurrence cycle has

\[
 \boxed{k_D-1=\exp(\eta D+o(D))}
 \tag{30}
\]

equally spaced interior slices of robust circuit complexity greater than `cD`.

### Proof

For `M=O(log D)` and `s=Theta(D)`,

\[
 \log {M+s-1\choose s}=O(M\log(1+s/M))=O(n^2)=o(D),
 \tag{31}
\]

which proves `(28)`.  Fixed `k` follows from `(24)` and `(27)`.  Given `(29)`, Bertrand's postulate
supplies a prime between `ceil(exp(eta D))` and twice that integer.  Its logarithm is
`eta D+o(D)`.  Insert this and `(28)` into `(24)`; the logarithmic exponent is

\[
 (\eta+c\Delta\log2-\gamma_\delta)D+o(D)<0.
\]

This proves `(30)`. `square`

The depth `Theta(D)` is the intrinsic dimension scale of the equal-amplitude spectral phase torus.
No claim of generic `Theta(D^2)` state complexity in the ambient doubled Hilbert space is made.

## 6. Ordinary static-local Hamiltonians and permanent non-Haar locality

For an `n`-qubit time-independent Hamiltonian `H` with eigenpairs `(E_a,e_a)`, its normalized Choi
trajectory is

\[
 |\Phi_H(t)\rangle
 ={1\over\sqrt D}\sum_{a=1}^D e^{-itE_a}
 |e_a\rangle|\overline{e_a}\rangle.
 \tag{32}
\]

Thus it has exactly the uniform phase form `(17)`, independently of eigenbasis.  The formalized
path-local spectral theorem supplies maximal projective rational rank on a dense residual
full-measure subset of the ordinary trace-zero onsite-plus-edge Hamiltonian coefficient space.  In
the qubit specialization, the formalized same-Hamiltonian locality theorem supplies, under its
explicit finite-size inequality, one fixed two-query Pauli experiment whose signal remains
strictly above the Haar benchmark at every real time.

Combining those corpus theorems with `(25)--(30)` gives the following paper-level consequence:

> For a dense residual full-measure set of ordinary time-independent trace-zero onsite-plus-edge
> qubit Hamiltonians satisfying the separator's explicit finite-size inequality, there are
> arbitrarily late Choi recurrence cycles containing exponentially many equally spaced
> Hilbert-scale-hard interior states, while one fixed local experiment distinguishes every one of
> those propagators—and the entire intervening evolution—from Haar randomness.

This is coexistence on the same Hamiltonian and same times, not a comparison between two ensembles.
The exact finite-grid cap moment law, translated target union, prime power-orbit avoidance, and their
replica-budget composition are now formalized.  Arbitrary-ray reduction, recurrence shadowing
composition, and asymptotic circuit specialization remain outside this card's Lean gate.

## 7. Conjecture--failure--survivor loop

### C0 -- any hard phase produces a hard midpoint recurrence

Verdict: `[FALSIFIED]`.  If `q` is hard but `q^2` is not the identity, approaching `q` says nothing
about recurrence at doubled time.

### C1 -- find a hard two-torsion phase

Verdict: `[PAPER-PROVED]`.  Lemma A with `k=2` leaves a hard sign phase whenever the circuit
capacity is below the torsion-cap exponent.  Dense evolution approaches that sign phase and its
double approaches the identity.

### C2 -- every torsion order gives a cycle whose every interior power is hard

Verdict: `[FALSIFIED FOR THE PROPOSED COUNTING ARGUMENT]`.  At composite order, nonunit powers are
not bijective and can collapse into easy lower-order subgroups.

### C3 -- prime torsion gives a completely hard recurrence polygon

Verdict: `[PAPER-PROVED]` by Theorems A--B.  Every nonzero exponent is a group automorphism, so one
finite union bound selects an entire hard cyclic orbit.

### C4 -- the polygon proves Brown growth from time zero

Verdict: `[FALSE AS A CONCLUSION]`.  The theorem constrains arbitrarily late recurrence anatomy.  It
does not bound the first selected `tau`, complexity between rational slices, or initial monotonicity.

### C5 -- the hard slices are Haar-random

Verdict: `[FALSIFIED AS NECESSARY]`.  Their hardness is a torsion-code avoidance theorem.  The local
two-query separator can remain nonzero at every slice and every time.

## 8. Hostile audit

1. **Existential recurrence time.**  Kronecker density gives no useful upper bound on the first
   polygon-shadowing time.  No Brown onset or expected recurrence scale follows.
2. **Not every recurrence.**  The theorem constructs arbitrarily late recurrence sequences with the
   stated anatomy.  Other recurrence sequences may have easy interior slices.
3. **Discrete rational frame.**  Complexity is proved at `k-1` equally spaced times, not on the
   complete continuous interval.  Local simulation gives neighborhoods around each slice only after
   a separate speed bound.
4. **Prime order is load-bearing.**  Composite-order extension requires a stratified count over all
   divisor subgroups; it is not silently asserted.
5. **Finite gate alphabet.**  Continuously parameterized gates require a robust parameter net and
   its entropy.
6. **Complexity scale.**  The lower bound is `Theta(D)` for an equal-amplitude `D`-phase orbit.  It is
   not global maximal complexity in the full `D^2`-dimensional Choi state space.
7. **Choi specialization.**  Uniform spectral weights are automatic for normalized Choi states, not
   for arbitrary initial pure states.
8. **Locality claim is a composition.**  Permanent non-Haar separation and generic maximal
   projective rank are imported formal corpus theorems.  The new statement is their composition with
   the torsion-polygon law.
9. **Closest internal theorem.**  The formalized static Choi alternation law and the paper-proved
   arithmetic window law already give recurrence--hardness--recurrence triples.  They neither force
   the hard time to be the midpoint nor put all nontrivial rational slices of one recurrence cycle
   in the hard set.  Only that stronger polygon constraint is assigned to this card.
10. **Classical engines.**  Hoeffding concentration, finite-group power automorphisms, Bertrand's
   postulate, and Kronecker density are classical.  None is a standalone novelty claim.
11. **Literature boundary.**  Fractional-revival research classifies specially commensurate quantum
    walks; Brown--Susskind and subsequent complexity work study growth, saturation, and eventual
    recurrence.  Targeted searches found no theorem forcing a complete hard prime-torsion polygon
    inside one irrational static recurrence torus.  This absence is not priority certification.
12. **Black-hole interpretation is conditional.**  If a holographic complexity--volume/action
    dictionary applies, the hard slices correspond to large-interior epochs inside selected
    recurrence cycles.  No gravity theorem is claimed.
13. **Lean gate partly closed.**  Finite-grid cap moments, target translations, all-power avoidance,
    and the replica-budget polygon theorem are exact Lean theorems.  Arbitrary normalized target
    rays, autonomous shadowing, and circuit asymptotics must still be composed formally before a
    final manuscript claims the full card.

## 9. External boundary

- Brown and Susskind, *The Second Law of Quantum Complexity* (arXiv:1701.01107), conjecture the
  growth--plateau--recurrence history but do not give a torsion-polygon theorem.
- Oszmaniec--Kotowski--Horodecki--Hunter-Jones, *Saturation and recurrence of quantum complexity in
  random local quantum dynamics* (arXiv:2205.09734), prove saturation and recurrence for refreshed
  random dynamics, not the rational-slice anatomy of one fixed Hamiltonian.
- Chan--Coutinho--Tamon--Vinet--Zhan, *Quantum Fractional Revival on Graphs* (arXiv:1801.09654),
  studies exact transport structure at fractional revival times for commensurate graph spectra.  It
  does not bound circuit complexity of torsion powers in a maximal irrational phase torus.
- Classical coding/concentration theory supplies the cap estimate; projective-torus density is an
  application of Kronecker's theorem.  The assembled quantum-complexity application remains
  `[NOVELTY UNVERIFIED]` pending citation-graph and expert review.

## Gates

- [x] torsion target-cap bound uniform in order and eigenbasis
- [x] prime power-orbit avoidance
- [x] exponential multiplicity of complete hard prime-torsion polygons
- [x] dense-flow recurrence-polygon shadowing
- [x] bounded-dependence circuit-capacity specialization
- [x] linear-in-`D` hard slices
- [x] exponentially many slices in one recurrence cycle
- [x] ordinary static-local and permanent non-Haar composition on paper
- [x] hostile and preliminary external audit
- [x] exact finite-grid moment, translated-cap, and prime all-power avoidance Lean core
- [ ] Lean composition through arbitrary rays, recurrence shadowing, and circuit asymptotics
- [ ] effective first polygon time / Brown onset

## 10. Lean core advance -- 2026-08-14

Three unconditional modules now certify the new combinatorial and finite-Fourier core:

1. `HTGeometry/PrimeTorsionOrbitAvoidance.lean` proves the general finite-automorphism survivor
   bound and the exact lower count
   `p^d - (p-1)|bad|` for complete nonidentity prime-torsion avoidance.
2. `HTGeometry/FiniteGridCoherenceMoment.lean` proves a stronger modulus--replica separation than
   the original proof used: whenever `2n < M`, the exact `2n`-th coherence moment on the `M`-torsion
   grid equals `M^d` times the permutation floor.  Deterministic Markov counting yields
   
   \[
   |C_{M,n}(u)|u^{2n}
   \le M^d n!\Bigl(\sum_i w_i^2\Bigr)^n.
   \]
   
   The module also proves translation invariance and the full finite-target union bound.
3. `HTGeometry/PrimeTorsionTargetCapPolygon.lean` composes those results.  For prime `p`, `2n<p`,
   nonnegative weights, positive threshold `u`, and `N` targets, the explicit sufficient condition
   
   \[
   (p-1)N n!\Bigl(\sum_i w_i^2\Bigr)^n<u^{2n}
   \]
   
   produces one torsion phase whose every nonzero scalar multiple avoids every translated target
   cap.

This is stronger structurally than tying grid modulus to `2n+1`: replica order controls the cap
estimate while prime order independently controls polygon length.  It is still a discrete phase
dictionary theorem; no claim about first physical occurrence time follows.
