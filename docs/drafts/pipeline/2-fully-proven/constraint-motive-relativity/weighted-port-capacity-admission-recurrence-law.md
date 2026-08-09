# Weighted port capacity, admission, and recurrence law

- **ID:** `cmr-weighted-port-capacity-admission-recurrence`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / CAPACITY--TOPOLOGY--TIME CALIBRATION
- **Status:** `[PAPER-PROVED] [HOSTILE ACCEPT] [BRIDGE/CLASSICAL SYNTHESIS]`
  `[CAPACITY/POSITIVITY/TOPOLOGY/RECURRENCE/PROLONGATION]`
  `[ROUTE-E/STOKES ABSTRACT BRIDGE, NOT LITERAL IDENTIFICATION]`
  `[NOT HT BY ITSELF] [NOT RH] [NO LEAN WRITTEN OR BUILT]`
- **Parents:** `prime-port-algebraic-continuous-separation-law.md`;
  `prime-phase-port-recurrence-completion-law.md`.
- **Statement:** For a weighted prime Hilbert chart, continuous port admission, finite effective
  capacity, positive filling cost, closedness of the constraint, recurrence, and time-jet domains
  are governed by one explicit capacity hierarchy. Divergent capacity makes the constraint dense
  and the Hausdorff port vanish.

## Goal

Add the capacity organ to the same source-dependent reduction/completion/time geometry. Replace
the vague “uncertainty” between precise source coefficients and precise observer port by an exact
reciprocity law.

## 1. Weighted source and moving port

Let `P` be a countable prime set, choose weights `w_p>0` and coefficients `a_p ne 0`, and define

\[
 H_w=\left\{x:\sum_p w_p|x_p|^2<\infty\right\},
 \qquad
 \|x\|_w^2=\sum_pw_p|x_p|^2.
\tag{CA.1}
\]

On finite-support vectors put

\[
 \lambda_t(x)=\sum_pa_pp^{-it}x_p.
\tag{CA.2}
\]

For finite `F subset P`, define port capacity and its jet hierarchy

\[
 C_{F,n}=\sum_{p\in F}\frac{|a_p|^2(\log p)^{2n}}{w_p},
 \qquad n\ge0.
\tag{CA.3}
\]

Write `C_n=sup_F C_(F,n)` in `[0,infinity]`.

## 2. Exact capacity--cost reciprocity

### Theorem 1

For nonempty finite `F` and `z in C`,

\[
 \boxed{
 \inf\{\|x\|_w^2:\operatorname{supp}x\subset F,\ \lambda_t(x)=z\}
 =\frac{|z|^2}{C_{F,0}}.}
\tag{CA.4}
\]

The unique minimizer is

\[
 x_p^{\min}
 =\frac{z\,\overline{a_pp^{-it}}}{w_pC_{F,0}},
 \qquad p\in F.
\tag{CA.5}
\]

Thus

\[
 \boxed{
 C_{F,0}\cdot E_F^{\min}(z)=|z|^2.}
\tag{CA.6}
\]

#### Proof

Weighted Cauchy--Schwarz gives

\[
 |\lambda_t(x)|^2
 \le\left(\sum_{p\in F}w_p|x_p|^2\right)
     \left(\sum_{p\in F}\frac{|a_p|^2}{w_p}\right).
\]

This proves the lower bound. Substitution of `(CA.5)` gives `lambda_t(x_min)=z` and norm square
`|z|^2/C_(F,0)`, proving equality and uniqueness. `[PROVED HERE]`

`C_(F,0)` is exactly the one-port Riesz/Schur capacity `A P^(-1) A^*`. Formula `(CA.6)` is the
precise capacity--precision reciprocity: more filling directions increase capacity while reducing
the least source energy needed to realize a fixed observer value.

## 3. Capacity equals admission and closedness

### Theorem 2

The algebraic port `(CA.2)` extends continuously to `H_w` if and only if

\[
 \boxed{C_0<\infty.}
\tag{CA.7}
\]

When `(CA.7)` holds, `||lambda_t||^2=C_0` for every `t`, its kernel is closed of codimension one,
and cotangent reduction leaves `H(C)`.

If `C_0=infinity`, the finite-support kernel of `lambda_t` is dense in `H_w`; its continuous
annihilator is zero and Hausdorff cotangent reduction vanishes.

#### Proof

Riesz representation identifies the squared functional norm with
`sum_p |a_p|^2/w_p`, proving `(CA.7)` and the closed case.

Suppose `C_0=infinity`. Given finite-support `x`, set `S=lambda_t(x)`. On a disjoint finite set
`F`, add the negative of the minimizer `(CA.5)` with target `S`. The corrected vector lies in the
kernel and differs from `x` by norm `|S|/sqrt(C_(F,0))`. Tail capacities are unbounded, so this
can be made arbitrarily small. Finite-support vectors are dense in `H_w`, hence the kernel is
dense. The annihilator and reduction conclusions follow. `[PROVED HERE]`

### Corollary 2.1 — topology is inverse capacity

The port survives Hausdorff completion exactly when its total capacity is finite. When capacity
diverges, finite-cutoff unit-port energy tends to zero and the constraint becomes dense:

\[
 C_{F,0}\to\infty
 \quad\Longleftrightarrow\quad
 E_F^{\min}(1)\to0
 \quad\Longrightarrow\quad
 \overline{\ker\lambda_t}=H_w.
\tag{CA.8}
\]

This makes algebraic-to-continuous Hausdorff port loss a capacity phase, not a separate
decoration. Correctly transported quotient completion still commutes with reduction.

## 4. Recurrence and jet admission hierarchy

### Theorem 3

Assume `C_0<infinity`. Then `t mapsto lambda_t` is a norm-continuous, norm-precompact recurrent
orbit in `H_w'`.

For every `n>=1`, the curve is `C^n` as an `H_w'`-valued curve exactly when

\[
 \boxed{C_n<\infty.}
\tag{CA.9}
\]

If `(CA.9)` holds, its `n`-th derivative has coefficient
`(-i log p)^n a_p p^(-it)` and squared norm `C_n`.

#### Proof

After Riesz identification, the orbit is the diagonal unitary orbit of the vector
`(a_p/sqrt(w_p)) in ell^2`. It is norm-continuous by dominated convergence. It is totally bounded:
truncate the vector uniformly in time, and use compactness of the finite coordinate torus. Hence
its closure is compact. Finite-coordinate Kronecker recurrence plus a uniformly small tail gives
norm recurrence.

Differentiation forces the displayed coefficient. Riesz representation makes it bounded exactly
when the series `(CA.3)` converges. When it converges, dominated convergence of difference
quotients in the weighted dual norm proves differentiability. Conversely coordinate tests force
the coefficient, so no bounded derivative exists when `C_n=infinity`. `[PROVED HERE]`

### Corollary 3.1 — recurrent port with singular infinitesimal time

Take `a_p=1` and

\[
 w_p=p(\log p)^2.
\tag{CA.10}
\]

Then

\[
 C_0=\sum_p\frac1{p(\log p)^2}<\infty,
 \qquad
 C_1=\sum_p\frac1p=\infty.
\tag{CA.11}
\]

Thus the global port orbit is norm-continuous, norm-precompact and recurrent with compact closure,
and regularly reducible, while
its infinitesimal prime-log time generator is not a continuous port in the same Hilbert chart.

#### Proof

The first series is bounded by the convergent integer series
`sum_(n>=2)1/(n(log n)^2)`. Euler's prime harmonic theorem gives divergence of the second. Apply
Theorems 2 and 3. `[PROVED HERE]`

This is an exact phase geometry of time: global recurrence and infinitesimal dynamics occupy
different admission strata.

## 5. Source specializations

1. **Unweighted augmentation:** `a_p=w_p=1` has `C_0=infinity`; this recovers dense-kernel
   `ell^2` erasure.
2. **Euler half-density port:** `a_p=(log p)/sqrt(p)`, `w_p=1` has
   `C_0=sum_p(log p)^2/p=infinity`; every finite cutoff exists and the global Hilbert port is
   absent.
3. **Right of half density:** `a_p=(log p)p^(-sigma)`, `w_p=1` has finite capacity exactly for
   `sigma>1/2`.
4. **Time jets:** multiplying by `(log p)^n` moves from `C_0` to `C_n`; the hierarchy records
   which infinitesimal observers remain continuous.

For item 3, convergence for `sigma>1/2` follows by comparison with an integer `p`-series after
absorbing logarithms into a small power; divergence for `sigma<=1/2` follows from Euler's prime
harmonic divergence.

## 6. What this explains and what it does not

The theorem couples five formerly separate organs:

1. relation/port kernel;
2. positive capacity and minimum filling energy;
3. topology/closedness/Hausdorff reduction;
4. recurrence and phase-blind capacity;
5. deformation/prolongation through jet admission.

It is the abstract capacity skeleton underlying Route-E conductance and the Stokes one-port Schur
formula, but it does not identify either route's literal incidence, labels, directed flux, or
published constants with `(CA.1)--(CA.3)`. The Mass half-density coefficient supplies a literal
specialization, but its full outgoing Abel boundary is not constructed by this theorem.

It also does not prove HT: an unbounded capacity/jet hierarchy is weaker than absence of all
polynomial differential relations. It does not construct black-hole geometry: recurrent port plus
singular generator is an exact operational morphology, not a horizon algebra or wormhole length.

## 7. Conjecture/failure loops

### Loop A — capacity is only a positive scalar shadow

**Failed:** capacity determines minimum filling cost, functional admission, kernel closedness, and
Hausdorff reduction through `(CA.4)--(CA.8)`.

**Survivor:** capacity is a transition invariant between relation, positive, and topological
doctrines.

### Loop B — global recurrence implies admitted generator

**Failed:** `(CA.10)--(CA.11)` gives a norm-precompact recurrent norm-continuous orbit with
unbounded
infinitesimal generator.

**Survivor:** time geometry requires an admissibility scale, not one Hilbert space.

### Loop C — tune weights to prove RH

**Failed as circular/irrelevant:** weights change observer topology; they do not produce source
nullhomology or constrain Xi zeros.

**Survivor:** any physical or RH comparison must derive its weights/action from source and then
pass the explicit capacity tests. Fitting weights to retain a desired port is theatre.

## 8. Route-independent predictions

1. A port whose finite capacities diverge cannot survive as a continuous scalar after Hausdorff
   Hilbert reduction.
2. Any claimed one-port positive geometry has an exact minimum filling cost; disagreement with
   `(CA.4)` identifies a different metric or a nonlinear/non-Hilbert chart.
3. Recurrence and bounded capacity do not imply an admitted Hamiltonian generator; the jet
   capacity hierarchy must be reported.
4. A common Route-E/Stokes/Mass realization must match not only one scalar capacity but also kernel
   topology, minimizers, time transport, and jet domains.
5. Hypertranscendental dynamics, if realized, should appear as failure of every finite admissible
   jet-capacity stage to be conservative, not as capacity divergence alone.

## 9. Literature/corpus boundary

Riesz representation, Cauchy--Schwarz minimization, almost-periodic pure-point unitary orbits, and
weighted graph domains are classical. The theorem claims no generic novelty. Its role is the exact
field synthesis: capacity is simultaneously positive energy, dual norm, closed-range criterion,
reduction phase, recurrence metric, and derivative-domain hierarchy for one source port.

## 10. No-go closure

- **Exact killing mechanisms:** raw Witt rank does not control reduction; recurrence does not
  control generator admission; capacity divergence erases Hausdorff port.
- **Strongest positive survivor:** capacity--cost equality `(CA.6)`, capacity--closure law
  `(CA.7)--(CA.8)`, and capacity-jet recurrence law `(CA.9)--(CA.11)`.
- **New insight:** making source resolution larger reduces unit-port filling cost until the port
  becomes topologically invisible. This is a precise complementarity principle rather than a
  metaphorical uncertainty relation.
- **Status:** dependency-closed paper proof; hostile review accepted mathematics and classified it
  as a strong classical/corpus bridge, not GR-level core; no Lean written.

## Log

- 2026-08-09 — derived weighted capacity hierarchy from the same prime phase-port field and closed
  cost, closedness, recurrence, and derivative-admission equivalences.
- 2026-08-09 — hostile review accepted formulas and hypotheses; classified result as strong
  five-organ bridge with supplied weights, not a literal Route-E/Stokes/Mass unification.
