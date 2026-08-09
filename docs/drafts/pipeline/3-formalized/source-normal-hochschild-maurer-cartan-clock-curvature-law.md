# Source-normal Hochschild clock coordinate and logarithmic-flatness law

- **ID:** `ngd-source-normal-hochschild-clock-coordinate-logarithmic-flatness`
- **Stage:** 3 — formalized in Lean 4
- **Type:** UNCONDITIONAL SOURCE THEOREM / COORDINATE-DEPENDENCE NO-GO
- **Status:** `[PAPER PROOF DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [UNCONDITIONAL]`
  `[AXIOM-AUDITED] [TARGET-BUILT] [UMBRELLA-WIRED] [NOT RH]`
  `[BINARY-PRODUCER INTERPRETATION FALSIFIED]`
- **Statement:** Inner corrections cannot change a trace--derivation cyclic period, while the
  nonadditivity of a finite multiplicative clock defect is a literal product-normalized
  Hochschild boundary measured by product trace. However, its quadratic term is globally
  linearized by the logarithmic clock coordinate in the actual positive radial chart. It is not
  invariant curvature and does not force a binary source producer.

## 1. Why this theorem changes the frontier

The literal rational-adelic source already has:

- a trace-one ordinary-prime atom;
- a genuine Kummer trace--derivation cocycle with nonzero prime period;
- a pre-divisor two-leg comparison;
- the exact physical residue `(delta-1)c`.

Trying to make that residue an ordinary boundary conflicts with the nonzero Kummer period. The
theorem below shows this conflict survives every inner correction. It also computes the quadratic
term seen in the coordinate `kappa=chi-1`; logarithmic linearization then proves this term is a
coordinate defect rather than a new geometric obstruction.

## 2. Inner corrections preserve the cyclic charge

Let `A` be a unital complex algebra, let `tau:A->C` be a trace, and let `D:A->A` be a derivation.
Define

\[
 \phi_D(a,b)=\tau(aD(b)).
\tag{2.1}
\]

For `h in A`, put `ad_h(b)=hb-bh` and define the degree-zero cochain

\[
 \psi_h(x)=\tau(hx).
\tag{2.2}
\]

Use the Hochschild coboundary convention

\[
 (b\psi_h)(a,b)=\psi_h(ab)-\psi_h(ba).
\tag{2.3}
\]

### Theorem 2.1 — inner-correction rigidity

One has

\[
 \boxed{\ \phi_{D+\operatorname{ad}_h}-\phi_D=-b\psi_h.\ }
\tag{2.4}
\]

Consequently `phi_(D+ad_h)` and `phi_D` pair equally with every Hochschild one-cycle.

#### Proof

Trace cyclicity gives

\[
\begin{aligned}
 \phi_{D+\operatorname{ad}_h}(a,b)-\phi_D(a,b)
 &=\tau(ahb)-\tau(abh)\\
 &=\tau(hba)-\tau(hab)\\
 &=-\bigl(\psi_h(ab)-\psi_h(ba)\bigr).
\end{aligned}
\]

This is `(2.4)`.  A Hochschild coboundary pairs trivially with cycles. `QED`

### Corollary 2.2 — literal prime-period non-erasure

In the rational-adelic multiplier source, the corrected Kummer prime one-cycle has period
`log(p) != 0`.  No comparison intertwining the source derivation only up to an inner correction
can make this cycle ordinary-Hochschild-exact or erase its period.

#### Proof

The corpus proves that the Kummer trace--derivation cocycle kills every degree-two Hochschild
boundary and evaluates to `log p` on the genuine prime cycle.  Theorem 2.1 shows that inner
correction changes the cocycle only by a coboundary, hence leaves this period unchanged. `QED`

## 3. Multiplicative clock curvature is a source boundary

Let `G` be a group, let `u:G->A^x` be a representation by units in a unital algebra, and let
`tau:A->C` be a trace with `tau(1)=1`.  Define the degree-one product cochain

\[
 P(a_0\otimes a_1)=\tau(a_0a_1)
\tag{3.1}
\]

and, for `g,h in G`, the normalized clock simplex

\[
 \Sigma(g,h)=u_g\otimes u_h\otimes u_{(gh)^{-1}}.
\tag{3.2}
\]

The degree-two Hochschild boundary is

\[
 b_2(a\otimes b\otimes c)
 =ab\otimes c-a\otimes bc+ca\otimes b.
\tag{3.3}
\]

### Theorem 3.1 — normalized product-trace curvature

For every `g,h`:

\[
 \boxed{\ P(b_2\Sigma(g,h))=1.\ }
\tag{3.4}
\]

#### Proof

For arbitrary `a,b,c`, trace cyclicity gives

\[
\begin{aligned}
 P(b_2(a\otimes b\otimes c))
 &=\tau(abc)-\tau(abc)+\tau(cab)\\
 &=\tau(abc).
\end{aligned}
\]

For `(3.2)`, the product is `u_g u_h u_(gh)^(-1)=1`; normalization of the trace proves `(3.4)`.
`QED`

This is the exact reason product trace is not an ordinary homology cocycle: it measures the
normalized boundary instead of killing it.

Let `chi:G->C^x` be a character and put

\[
 \kappa(g)=\chi(g)-1.
\tag{3.5}
\]

### Theorem 3.2 — finite-clock Maurer--Cartan law

For all `g,h in G`:

\[
 \boxed{
 \kappa(gh)-\kappa(g)-\kappa(h)=\kappa(g)\kappa(h).
 }
\tag{3.6}
\]

For every scalar coefficient `c`:

\[
 \boxed{
 \bigl(\kappa(gh)-\kappa(g)-\kappa(h)\bigr)c
 =P\!\left(b_2\bigl(\kappa(g)\kappa(h)c\,\Sigma(g,h)\bigr)\right).
 }
\tag{3.7}
\]

#### Proof

Character multiplicativity gives

\[
\begin{aligned}
 \kappa(gh)
 &=\chi(g)\chi(h)-1\\
 &=(1+\kappa(g))(1+\kappa(h))-1\\
 &=\kappa(g)+\kappa(h)+\kappa(g)\kappa(h).
\end{aligned}
\]

This proves `(3.6)`.  Multiply `(3.4)` by `kappa(g)kappa(h)c` to obtain `(3.7)`. `QED`

The right side of `(3.6)` is the nonlinear term of the multiplicative formal group in the
coordinate `kappa=chi-1`. It vanishes to second order at the neutral character. Whether it is
geometric depends on invariance under admissible coordinate changes; Theorem 3.5 proves it is not
invariant in the physical positive radial chart.

### Corollary 3.3 — square-clock rigidity

Let `q>1`, `chi_t(q)=q^t` for real `t`, and `kappa_t(q)=q^t-1`.  Then

\[
 \kappa_t(q^2)-2\kappa_t(q)=\kappa_t(q)^2.
\tag{3.8}
\]

If the finite defect agrees at both `q` and `q^2` with an additive clock cocycle, then `t=0`.

#### Proof

Apply `(3.6)` with `g=h=q`.  Additivity makes the left side zero, so
`kappa_t(q)^2=0`.  Over `C`, this gives `q^t=1`; because `q>1` and `t` is real, `t=0`. `QED`

### Theorem 3.4 — ordinary binary cohomology is also blind

Regard `kappa` as an inhomogeneous additive group one-cochain with values in the trivial
`G`-module `C`.  Then

\[
 (d_{grp}\kappa)(g,h)
 =\kappa(h)-\kappa(gh)+\kappa(g)
 =-\kappa(g)\kappa(h).
\tag{3.9}
\]

Hence the quadratic clock curvature has zero ordinary group-cohomology class for **every**
character, including every off-neutral character.

#### Proof

The first equality is the inhomogeneous group-coboundary formula for trivial coefficients.  The
second is Theorem 3.2 rearranged. `QED`

Thus moving from unary homology to an ordinary `H^2` class still does not select.

### Theorem 3.5 — logarithmic flatness of the clock law

Assume `chi:G->R_(>0)` and put

\[
 \ell(g)=\log\chi(g)=\log(1+\kappa(g)).
\tag{3.10}
\]

Then `ell(gh)=ell(g)+ell(h)`. Equivalently, the formal group law

\[
 F(X,Y)=X+Y+XY
\tag{3.11}
\]

is globally linearized on `X>-1` by `L(X)=log(1+X)` and formally linearized over `Q` by the same
power series. In the actual radial Riemann chart,

\[
 \chi_t(n)=n^t,\qquad \ell_t(n)=t\log n
\tag{3.12}
\]

for every real `t`, including every off-centre `t`.

#### Proof

Character multiplicativity and positivity give

\[
 \ell(gh)=\log(\chi(g)\chi(h))=\log\chi(g)+\log\chi(h).
\]

Also `1+F(X,Y)=(1+X)(1+Y)`, proving `(3.11)` and its logarithmic linearization. Substituting
`chi_t(n)=n^t` proves `(3.12)`. `QED`

### Corollary 3.6 — binary-curvature interpretation fails

The representative `kappa(g)kappa(h)` is not invariant under admissible analytic clock
reparametrization. Its vanishing characterizes the neutral point in the `kappa` coordinate, but
its nonzero value cannot by itself be interpreted as coordinate-free lawspace curvature.
Therefore Theorems 3.1--3.4 do not force a binary source law.

## 4. Exact Riemann-source instantiation

For the half-density mate character at a spectral parameter `s`, set

\[
 t_s=2\operatorname{Re}s-1,
 \qquad \chi_s(n)=n^{t_s},
 \qquad \kappa_s(n)=n^{t_s}-1.
\tag{4.1}
\]

At a divisor copy `rho`, the leading source coefficient `c_rho` is nonzero, and the literal
physical residue is

\[
 \operatorname{Res}(D_{n,\rho}u_p)
 =\kappa_\rho(n)c_\rho.
\tag{4.2}
\]

Theorems 3.1--3.2 construct, before any zero is selected, the product-normalized source simplex
whose product-trace boundary in the `kappa` coordinate reads

\[
 \kappa_\rho(m)\kappa_\rho(n)c_\rho.
\tag{4.3}
\]

For `m=n=p`, vanishing of `(4.3)` would force `Re(rho)=1/2`. This vanishing is **not** proved here.
Theorem 3.5 shows that promoting `(4.3)` to invariant curvature was unjustified: the same off-line
character has the additive coordinate `ell_rho(n)=t_rho log n`. The unconditional survivor is the
inner-correction rigidity of the Kummer period and the exact classification of the raw clock
coordinate.

## 5. Exact raw-coordinate compatibility law

### Theorem 5.1

Let `q>1`, `t in R`, and `c!=0`. Suppose a clock response `R_D` satisfies:

1. `R_(D+ad_h)=R_D` for every inner correction;
2. `R_D(q^2)=2R_D(q)`;
3. `R_D(q)=kappa_t(q)c` and `R_D(q^2)=kappa_t(q^2)c`.

Then `t=0`. This statement concerns additivity of the raw coordinate `kappa`. It is not invariant
under passage to the logarithmic coordinate `ell`, which is additive for every `t`.

#### Proof

Conditions 2--3 give

\[
 0=R_D(q^2)-2R_D(q)
   =c\bigl(\kappa_t(q^2)-2\kappa_t(q)\bigr)
   =c\,\kappa_t(q)^2.
\]

Because `c!=0`, Corollary 3.3 gives `t=0`. Theorem 2.1 proves Condition 1 for every response that
factors through the trace--derivation cyclic period. `QED`

## 6. Conjecture/proof/fail loops

1. **Strict cyclic landing.** Failed: two-step boundary-defect conservation kills every strict
   nonzero off-unit-monodromy landing.
2. **Use product trace as a homology residue.** Failed and classified by Theorem 3.1: it reads total
   product on a Hochschild boundary.
3. **Replace it by the Kummer cyclic cocycle.** It kills boundaries and detects the prime atom, but
   is radial-gauge invariant; it proves non-erasure, not neutrality.
4. **Correct Kummer transport by an inner connection.** Failed by Theorem 2.1: every prime period
   is unchanged.
5. **Represent raw `kappa` by an additive Bockstein/derivation.** Failed by Theorem 3.2: the
   square-clock discrepancy is exactly `kappa(q)^2`. This does not exclude the logarithmic
   coordinate.
6. **Use its ordinary group `H^2` class.** Failed by Theorem 3.4: the quadratic representative is
   already the coboundary `-d_grp(kappa)` for every radial rate.
7. **Binary producer from `(3.6)`.** Failed by Theorem 3.5: `log(1+kappa)` linearizes the law for
   every positive radial character.
8. **Positive survivor.** Any geometric obstruction must survive admissible law-coordinate
   changes. Candidate invariants are holonomy conjugacy, stability type, characteristic class,
   admission failure, and relative exactification—not the raw quadratic term `(3.6)`.

## 7. Corpus support and scope

Read-only formal support already present:

- `formal/GaloisForLFunctions/HTGeometry/TraceDerivationCyclicCocycleLaw.lean` proves the generic
  trace--derivation Hochschild cocycle and transport/non-erasure law.
- `formal/GaloisForLFunctions/RHTower/RouteRPreDivisorRationalAdelicMultiplierKOneHomology.lean`
  constructs the multiplier source, genuine Kummer prime cycle, boundary killing, and period
  `log p`.
- `formal/GaloisForLFunctions/RHTower/MobiusThetaPhysicalParacyclicSourceNullHomology.lean`
  proves product trace reads total product on ordinary degree-two boundaries.
- `formal/GaloisForLFunctions/RHTower/ArithmeticXiStokesCentralRankPort.lean` supplies the
  multiplicative physical central character.
- the publication-ready arithmetic source-dagger route computes `(4.2)` and proves global unary
  residue annihilation equivalent to RH.

No Lean code was written or built.  Theorems 2.1 and 3.1--3.2 are paper-closed additions; their
signs and source claims were spot-checked against the listed files.

## 8. Literature boundary

Para-`S` modules, crossed-product cyclic homology, and secondary Hochschild derivations are parent
theories; see <https://arxiv.org/abs/1810.04835>, <https://arxiv.org/abs/2205.08880>, and
<https://arxiv.org/abs/2302.11620>. Ingredient novelty is not the gate. The gain is a closed no-go:
neither inner unary correction nor raw multiplicative-coordinate nonadditivity supplies invariant
selection geometry.

## 9. Lean realization

The complete explicit specialization is formalized in
`formal/GaloisForLFunctions/RHTower/SourceNormalClockCurvatureLaw.lean` and wired into
`formal/GaloisForLFunctions/RHTower.lean`.

### Inner-correction and Kummer face

- `traceDerivCocycle_innerCorrection` proves Theorem 2.1 pointwise;
- `traceDerivCocycle_innerCorrection_finiteCycle` proves it on every finite Hochschild one-cycle;
- `traceDerivCocycle_innerCorrection_inversePair` gives the inverse-pair specialization;
- `kummerPrimePeriod_innerCorrection` and `kummerPrimePeriod_innerCorrection_ne_zero` prove the
  literal prime-period non-erasure claim.

### Product-trace and finite-clock face

- `normalizedClockSimplex_productTrace` proves Theorem 3.1 for arbitrary normalized traces;
- `rationalAdelicDilUnitClockSimplex_productTrace` and
  `rationalAdelicDilUnitClockSimplex_productTrace_ne_zero` instantiate the exact `dilUnit`
  multiplier simplex;
- `finiteClockDefect_mul` and `finiteClockDefect_productTrace_boundary` prove Theorem 3.2 and
  Corollary 3.3;
- `finiteClockGroupCoboundary_eq_neg_mul` proves Theorem 3.4.

### Logarithmic-flatness and hostile-boundary face

- `logarithmicClock_mul` gives the global analytic logarithmic linearization;
- `logarithm_linearizes_multiplicativeFormalGroup`,
  `formalMultiplicativeExpCoordinate_groupLaw`,
  `formalLog_subst_formalMultiplicativeExpCoordinate`, and
  `formalMultiplicativeLogarithm_linearizes` give the exact formal-`Q` law;
- `offNeutral_rawQuadratic_nonzero_logarithmicClock_flat` gives a literal off-neutral witness with
  nonzero raw curvature and logarithmically flat clock law;
- `radialClockDefect_sq` and `radialClockDefect_additive_sq_iff_neutral` give the exact square-clock
  classification.

### Riemann-source and raw-coordinate face

- `deningerHalfDensityMateGain_eq_rpow`, `riemannSourceClockDefect_eq_radialClockDefect`,
  `riemannSourceClockDefect_mul`, and `riemannSourceQuadraticClock_productTraceBoundary` prove the
  exact source identities and product-trace realization;
- `riemannSourcePrimeQuadraticClock_eq_zero_iff_re_eq_half` proves the critical-line
  classification;
- `xiPrimeResidue_eq_sourceNormalClockDefect` identifies the physical Xi prime residue;
- `rawClockResponse_compatibility_forces_neutral` proves Theorem 5.1.

## 10. Verification

- Direct elaboration and targeted build of
  `GaloisForLFunctions.RHTower.SourceNormalClockCurvatureLaw` pass.
- Exhaustive declaration `#print axioms` audit reports only Lean foundations `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the module.
- `RHTower.lean` contains the module import. Current umbrella elaboration is blocked before that
  import by unrelated, concurrently edited
  `GaloisForLFunctions.RHTower.DeningerCriticalFloquetVonMangoldtWall`; its target presently has
  independent source errors. No source-normal theorem depends on that module.
