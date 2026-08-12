# Source-formation interaction work, QFI conservation, and cofinal phase law

- **ID:** ULF-ISDM-1
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL FORMATION / INTERACTION / PASSIVITY / INFORMATION MECHANICS
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-PROVED CORE] [MECHANISM, NOT ROUTE]
  [FINITE RECONSTRUCTION] [EXACT WORK--QFI CONSERVATION]
  [COFINAL PROPERNESS PHASE] [LITERAL PRIME SPECIALIZATION] [NOT RH]
- **Lean:** `HTGeometry.ConstitutiveInteractionSpectrumMechanics`

## 1. The mechanism

This theorem does not identify another receiver for an RH defect.  It gives one generation law.

1. A factorized source forms independent local law cells.
2. Multiplication generates one irreducible interaction channel for every finite support.
3. Orthogonal projection to interaction degree at most `D` is a passive observer.
4. The observer's lost work is exactly the energy in interactions of degree greater than `D`.
5. Coherent phase execution turns the same lost work into lost quantum Fisher information, with
   universal factor four.
6. Under cofinal formation, tightness of the interaction-degree ledger is a genuine properness
   phase; escape means every fixed-complexity observer asymptotically loses all nonconstant work.

The field content is this coupling.  Biased Walsh coordinates, Hoeffding decomposition, Parseval,
and pure-state QFI are parent machinery when separated.

## 2. Finite source formation and interaction basis

Let `I` be finite.  On

\[
 \Omega_I=\{0,1\}^I
\]

take the product law with independent coordinates `B_i` and parameters

\[
 0<q_i<1,\qquad w_i=q_i(1-q_i).
 \tag{ISD.1}
\]

Put

\[
 \psi_i={B_i-q_i\over\sqrt{w_i}},
 \qquad
 \psi_S=\prod_{i\in S}\psi_i,
 \qquad \psi_\varnothing=1.
 \tag{ISD.2}
\]

Independence and centering give

\[
 \mathbb E(\psi_S\psi_T)=\mathbf 1_{S=T}.
 \tag{ISD.3}
\]

There are `2^|I|` functions and `2^|I|` characters, so they form an orthonormal basis of
`L^2(Omega_I)`.  Consequently every `f` has the unique reconstruction

\[
 f=\sum_{S\subseteq I}\widehat f(S)\psi_S,
 \qquad
 \widehat f(S)=\mathbb E(f\psi_S),
 \tag{ISD.4}
\]

and Parseval conservation

\[
 \boxed{\|f\|_2^2=\sum_{S\subseteq I}|\widehat f(S)|^2.}
 \tag{ISD.5}
\]

Thus the full interaction packet jointly reconstructs the source observable.  No scalar summary
does.

## 3. Passive observation and exact work defect

Let

\[
 \Pi_{\le D}f=\sum_{|S|\le D}\widehat f(S)\psi_S.
 \tag{ISD.6}
\]

This is an orthogonal projection, hence a contraction.  Parseval splits exactly:

\[
 \boxed{
 \|f\|_2^2-\|\Pi_{\le D}f\|_2^2
 =\sum_{|S|>D}|\widehat f(S)|^2\ge0.}
 \tag{ISD.7}
\]

The right side is not named curvature.  It is the exact passive work defect of a bounded-complexity
observer.  For `D<E`, the defects compose:

\[
 \boxed{
 W_D(f)=W_E(f)+\|\Pi_{\le E}f-\Pi_{\le D}f\|_2^2.}
 \tag{ISD.8}
\]

This is constitutive passive-cycle mechanics on an interaction filtration: no work is destroyed;
it moves into the newly hidden degree band.

## 4. Multiplicative parity generates a second product law

Take the multiplicative parity observable

\[
 P_I=\prod_{i\in I}(1-2B_i).
 \tag{ISD.9}
\]

For one coordinate,

\[
 1-2B_i=(1-2q_i)-2\sqrt{w_i}\,\psi_i.
 \tag{ISD.10}
\]

Multiplying the local expansions gives

\[
 \widehat P_I(S)=
 \prod_{i\in S}(-2\sqrt{w_i})
 \prod_{i\notin S}(1-2q_i).
 \tag{ISD.11}
\]

Set

\[
 a_i=4q_i(1-q_i).
 \tag{ISD.12}
\]

Since `(1-2q_i)^2=1-a_i`, the squared interaction coefficients are

\[
 \boxed{
 |\widehat P_I(S)|^2
 =\prod_{i\in S}a_i\prod_{i\notin S}(1-a_i).}
 \tag{ISD.13}
\]

Their sum is one.  Therefore source parity does not merely have an interaction decomposition: its
work ledger is itself a second product Bernoulli law on interaction supports, with activation
probabilities `a_i`.  Its coordinate marginals reconstruct every `a_i`.  When the source chamber
marks `0<q_i<1/2`, the smaller root of `a_i=4q_i(1-q_i)` reconstructs `q_i`; hence the marked work
ledger reconstructs the full product source.

## 5. Fourth-organ theorem: hidden work is hidden coherent information

On `ell^2(Omega_I)`, use amplitudes `sqrt(P(omega))`.  For a real generator `g`, the coherent
orbit

\[
 |\Psi_t^g\rangle
 =\sum_{\omega\in\Omega_I}\sqrt{\mathbb P(\omega)}
   e^{it g(\omega)}|\omega\rangle
 \tag{ISD.14}
\]

has pure-state quantum Fisher information

\[
 \mathcal I(g)=4\operatorname{Var}(g).
 \tag{ISD.15}
\]

Constants do not contribute.  Applying this to `P_I` and its degree truncation gives the exact
cross-organ conservation law

\[
 \boxed{
 \mathcal I(P_I)-\mathcal I(\Pi_{\le D}P_I)
 =4\sum_{|S|>D}|\widehat P_I(S)|^2
 =4W_D(P_I).}
 \tag{ISD.16}
\]

Thus algebraic interaction formation, positive Hilbert work, passive observation, and coherent
phase information are four executions of one ledger.  The QFI theorem is predicted by the first
three; it is not input to their definition.

## 6. Literal prime formation and the global properness phase

For a finite prime aperture `F` and exponent `sigma>0`, take the Euler-shell Boolean source

\[
 q_p(\sigma)={1\over1+p^\sigma}.
 \tag{ISD.17}
\]

The parity-interaction activation is

\[
 a_p(\sigma)
 =4q_p(\sigma)(1-q_p(\sigma))
 ={4p^\sigma\over(1+p^\sigma)^2}.
 \tag{ISD.18}
\]

For every prime,

\[
 \boxed{p^{-\sigma}\le a_p(\sigma)\le4p^{-\sigma}.}
 \tag{ISD.19}
\]

Indeed `p^sigma>=1`, so `(1+p^sigma)^2` lies between `p^(2sigma)` and
`4p^(2sigma)`.

Let `F_n` increase to all primes, and let `K_n` be the random interaction degree under the work
law `(ISD.13)`.  Its mean and variance are

\[
 \mu_n=\sum_{p\in F_n}a_p,
 \qquad
 \operatorname{Var}K_n=\sum_{p\in F_n}a_p(1-a_p)\le\mu_n.
 \tag{ISD.20}
\]

### Theorem 6.1 — formation/properness dichotomy

1. If `sigma>1`, then `sum_p a_p(sigma)<infinity`.  For every `epsilon>0` there is `D` such that

   \[
   \sup_n\mathbb P(K_n>D)<\epsilon.
   \tag{ISD.21}
   \]

   Proof: Markov gives `P(K_n>D)<=mu_infinity/(D+1)`.

2. If `0<sigma<=1`, then `mu_n->infinity`, and for every fixed `D`,

   \[
   \boxed{\mathbb P(K_n\le D)\longrightarrow0.}
   \tag{ISD.22}
   \]

   Proof: for `mu_n>D`, Chebyshev gives

   \[
   \mathbb P(K_n\le D)
   \le{\operatorname{Var}K_n\over(\mu_n-D)^2}
   \le{\mu_n\over(\mu_n-D)^2}\longrightarrow0.
   \]

The prime reciprocal theorem and `(ISD.19)` give the claimed convergence/divergence.  Hence the
work ledger is tight exactly for `sigma>1` and escapes every fixed interaction degree exactly for
`0<sigma<=1`.

At the critical value `sigma=1`, the empty coefficient energy tends to zero because
`prod_p(1-a_p)=0`.  Therefore

\[
 \boxed{
 \mathcal I(P_{F_n})\longrightarrow4,
 \qquad
 \mathcal I(\Pi_{\le D}P_{F_n})\longrightarrow0
 \quad(D\text{ fixed}).}
 \tag{ISD.23}
\]

The observation can remain finite and recurrent at every aperture while all nonconstant coherent
information migrates beyond every fixed formation degree.

## 7. Reciprocal formation-phase selection interface

Define

\[
 \operatorname{Phase}(\sigma)=
 \begin{cases}
  \text{tight},&\sigma>1,\\
  \text{escaping},&0<\sigma\le1.
 \end{cases}
 \tag{ISD.24}
\]

For `0<sigma<2`, reflection sends `sigma` to `2-sigma`, and

\[
 \boxed{
 \operatorname{Phase}(\sigma)=\operatorname{Phase}(2-\sigma)
 \quad\Longleftrightarrow\quad \sigma=1.}
 \tag{ISD.25}
\]

This is a selection interface, not an RH proof.  With `sigma=2 Re rho`, a literal pre-zero
source comparison that intertwines functional-equation reflection and preserves the global
formation phase would force `Re rho=1/2`.  Constructing that comparison without using the zero or
its real part is the remaining producer theorem.

## 8. Hostile boundaries

1. Product independence is load-bearing.  For dependent sources the Hoeffding sectors require a
   different orthogonalization and `(ISD.13)` need not be a product law.
2. Parity is load-bearing for the second product ledger.  A general observable has arbitrary
   squared interaction coefficients.
3. The finite theorem cannot see the phase transition.  Properness is a cofinal statement.
4. Unbounded interaction degree is not hypertranscendence.  A separate differential realization
   must identify these degrees with strict prolongation layers.
5. QFI does not itself select the critical point; at the critical point it tends to the maximal
   value four.
6. Equation `(ISD.25)` becomes arithmetic only after a source-native reflection comparison.  A
   comparison fitted from a Xi zero is circular.
7. No Route-R, Route-L, Stokes, Mass, Hankel, or recurrence endpoint theorem is claimed here.
   Those are possible executors of the mechanism, not its definition.

## 9. Relationship to existing corpus

- Prime-residue interaction spectra and irreducible `n`-ary laws already prove existence and
  strictness of high interaction layers.  They do not provide this positive work ledger or the
  properness phase.
- Finite Walsh observation laws already prove uniform Parseval and threshold bounds.  They do not
  identify the source-biased parity ledger or its cofinal prime threshold.
- Prime Boolean--Mass--Hankel--QFI fusion proves a different conservation law on degree-one clock
  covariance.  The present law controls all interaction degrees and their migration.
- Global formation properness proves scale-orbit escape through full source work.  The present law
  identifies a concrete complexity filtration and the exact information transported to infinity.
- Constitutive passive-cycle mechanics supplies the abstract defect composition law.  Equation
  `(ISD.8)` is its source-generated orthogonal realization.

## 10. Parents

Finite biased Walsh/Hoeffding decomposition, Efron--Stein/ANOVA, Parseval, Poisson-binomial tail
bounds, and pure-state QFI as four times variance are classical parents.  The claim here is not
priority for those ingredients.  The theorem package records the exact constitutive coupling
forced by the Euler-shell product source.

## Gates

- [x] source formation specified before route execution
- [x] all-degree interaction generation and joint reconstruction
- [x] exact passive work conservation
- [x] fourth-organ QFI prediction and proof
- [x] cofinal tight/escaping properness phase
- [x] reciprocal phase classifier
- [x] Lean finite formation, reconstruction, passivity, work--QFI, prime phase, and reflection core
- [x] Lean analytic core of the cofinal fixed-degree escape limit `(ISD.22)`:
      `GaloisForLFunctions.HTGeometry.InteractionDegreeEscape.tendsto_mean_div_gap_sq` certifies
      that the Chebyshev bound `mu/(mu-D)^2` vanishes as the mean diverges, for every fixed degree
      threshold `D`, by the gap estimate `mu - D >= mu/2` past `mu >= 2D`
- [ ] Lean probabilistic wrapper of `(ISD.22)--(ISD.23)`: `P(K_n <= D) <= Var K_n/(mu_n - D)^2`
      together with the critical-value statement at `sigma = 1`
- [ ] source-native reflection comparison preserving formation phase
- [ ] RH selection consequence

- 2026-08-12 — the analytic core of the fixed-degree escape limit certified in Lean; only the
  probabilistic wrapper remains on this card.
