# Route C interim verdict: horizontal charge, current closure, and infinitesimal reopening

- **ID:** `route-c-horizontal-charge-interim-verdict`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM SYNTHESIS / ROUTE VERDICT,
  `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `../../1-in-progress/euler-horizontal-charge-separator.md`;
  `euler-shift-pair-incidence-resultant.md`;
  `shifted-hardy-leakage-static-continuity-no-go.md`;
  `infinitesimal-hardy-leakage-horizontal-layer-resolvent.md`
- **Statement:** The uncancelled Poincare--Lelong pair current constructs the exact horizontal
  charge without zero factorization, but its positivity records the collision-conserved total
  incidence and gives no absolute off-diagonal bound.  Bare static leakage continuity also fails.
  Route C is nevertheless not closed: first-order normalization of the leakage retains a fixed
  horizontal layer as a positive Laplace--Hankel Gram operator.  The remaining problem is to
  construct its ordinate-diagonal projection from the Euler source and prove an absolute norm
  bound, or equivalently to bound the positive-real thin slice of the current.

## Verdict

```text
Route C as bare leakage continuity: CLOSED.

Route C as infinitesimal ordinate-diagonal leakage: OPEN.

Route C as an exact source-current target:
  constructed, but the required absolute estimate is OPEN.

Unconditional RH in Lean: NOT OBTAINED.
```

The route should not generate more unnormalized-continuity, finite-residue, relative-density, or
current-existence infrastructure.  Its live target is a source-defined ordinate-diagonal
first-order leakage operator with an absolute norm bound, or the equivalent positive-real
thin-slice estimate before the Xi divisor is expanded.

## 1. Exact charge carrier

For a nonzero entire `F`, set

```text
F_-(c,u)=F(c-u),       F_+(c,u)=F(c+u).
```

The map `(c,u) |-> (c-u,c+u)` is biholomorphic.  If `rho` and `sigma` are zeros of orders
`m_rho,m_sigma`, their corresponding intersection point has local multiplicity

```text
m_rho m_sigma.                                            (1)
```

For `F=Xi`, twice the mass with `u>0` real and `Im c in I` is exactly

```text
Omega_E(I)=O_I
 = sum_(gamma in I) H_gamma^2
   - sum_(Im rho in I) m_rho^2.                           (2)
```

This is proved in `euler-shift-pair-incidence-resultant.md`.

## 2. Infinite source construction is closed

Normalize `dd^c` by Poincare--Lelong.  The two shift divisors intersect properly, so

```text
J_Xi
 = dd^c log|Xi(c-u)| wedge dd^c log|Xi(c+u)|              (3)
```

is a canonical locally finite positive zero-cycle on `C^2`.  It is defined from the completed
function, without selecting or enumerating its zeros.

For any compactly supported cutoff `kappa` with `kappa(0)=1`, the thin-slice limit

```text
2 lim_(epsilon->0+)
  integral 1_(Im c in I) 1_(Re u>0)
    kappa(Im u/epsilon) dJ_Xi(c,u)                         (4)
```

exists, is cutoff-independent, and equals `(2)`.  Thus construction of the infinite integer
measure is no longer an open problem.

## 3. Why reduced Hardy leakage is not the charge

At a common zero of `F(c-u)` and `F(c+u)`, quotient reduction cancels

```text
min(m_rho,m_sigma),                                       (5)
```

while the intersection current carries the product `(1)`.  The reduced shifted quotient therefore
deletes precisely the exceptional-shift incidence needed for horizontal charge.  Leakage rank and
rank deficit obey the wrong multiplicity law.

The static norm proposal also fails in the smallest model.  For one off-line displacement `a` and
`0<omega<a`, the rank-one Hardy leakage satisfies

```text
rank L_(a,omega)=1,       ||L_(a,omega)||=omega/a.         (6)
```

Hence `L_(a,omega)` tends to zero in operator norm as `omega` decreases to zero although the
off-line channel persists.  The unit jump occurs only at the moving crossing `omega=a`.  Using it
to prevent entry requires an additional deformation of `a`, not a static constraint on Xi.

## 4. Why positivity of the current is collision-blind

At `u=0`, a zero of multiplicity `m` contributes intersection multiplicity `m^2`.  Removing the
`m` identity copies leaves the diagonal multiplicity charge `m(m-1)`.  Therefore the reduced real
shift current carries

```text
O_I+M_I=C_I-N_I.                                          (7)
```

When a simple reflected pair enters the critical line, its two units of positive-`u` mass become
the two reduced diagonal units of a double zero.  The total positive current is conserved.  A
positive-mass or total-intersection estimate cannot distinguish entry; Route C needs an absolute
estimate on the *relative open stratum* `u>0`.

## 5. What the static no-go did not close

For a fixed same-ordinate collection of transverse layers `a_j>0` with multiplicities `m_j`, the
local leakage has the operator-norm expansion

```text
L_omega=omega T_A+o(omega),
```

where the Paley--Wiener kernel of `T_A` is

```text
K_A(x,y)=2 sum_j m_j exp(-a_j(x+y)).
```

Thus

```text
T_A>=0,
trace(T_A)=sum_j m_j/a_j,
||T_A||>=max_j m_j/a_j.
```

For zeta, `0<a_j<1/2`, so any layer forces `||T_A||>2`.  The unique power normalization with a
finite nonzero static limit is therefore `omega^(-1)L_omega`.  Bare continuity loses the channel;
its first derivative retains and amplifies it.

The obstruction is now global rather than local: before a zero ordinate is selected, different
ordinates appear as oscillatory exponential modes and the positivity of a single fiber is not
available.  Extracting the ordinate-diagonal block from the Euler source without first reading the
divisor is the live construction problem.

## 6. Exhaustion of the closed source mechanisms

The current pipeline proves:

1. finite and continuous source summaries are too flexible;
2. relative-density estimates cannot exclude one off-line orbit;
3. finite positive stationary phase detectors retain the prime pole at `s=1`;
4. reduced leakage loses exceptional-shift product multiplicity;
5. norm continuity at `omega=0` permits a persistent off-line channel;
6. the uncancelled current exists canonically but total positivity is collision-blind; and
7. a residue or divisor expansion of `(3)` merely reconstructs the target.

These statements close the listed unnormalized and closed-current mechanisms.  They do not close
the infinitesimal ordinate-diagonal mechanism above and do not prove a logical impossibility theorem
for every future arithmetic estimate on `(4)`.

## 7. Exact remaining theorem

`[OPEN CORE]` For a genuinely new bounded interval `I`, prove directly from the fixed
Euler--Gamma--theta source that

```text
2 lim_(epsilon->0+)
  integral 1_(Im c in I) 1_(Re u>0)
    kappa(Im u/epsilon) dJ_Xi(c,u) < 2.                   (8)
```

Because `(8)` is an even nonnegative integer, it would force zero positive-real-shift mass on `I`.
Doing this for every window would prove RH.  The proof may not expand `J_Xi` into `(1)`, assume an
RH-equivalent Herglotz/inner condition, or replace the absolute bound by an asymptotic proportion.

No theorem currently derives `(8)` from Euler--Gamma data.  Restating `(8)` as positivity,
closability, rank zero, absence of residues, or support on the diagonal does not advance the open
core.

An equivalent operator target is to construct the source-defined ordinate-diagonal first-order
leakage `D_E(I)` and prove

```text
||D_E(I)||<=2.                                            (9)
```

The finite-layer theorem proves that `(9)` excludes every right-hand layer in `I`.  The missing
step is not the threshold calculation; it is the non-conclusion-fed source construction and bound.

## 8. Scientific-novelty verdict

No result in this Route C closure is promoted as new scientific knowledge.

- Local product multiplicity and Poincare--Lelong intersection currents are standard complex
  analytic intersection theory.
- The rank-one leakage formula is standard Hardy/model-space theory.
- The charge-transfer identity is elementary multiplicity algebra.
- The remaining condition `(8)` is an exact RH-bearing target, not a proved estimate.

The route verdict is valuable because it removes false mechanisms and fixes the unique surviving
object.  It does not pass the novelty gate by relabelling standard parent theory.

## 9. Lean verdict

No Lean card is created.  The current formal tree does not contain positive currents, proper
analytic intersections, or Hardy model spaces at the strength needed for `(3)`--`(6)`.  A finite
multiset or scalar-ratio wrapper would not formalize the actual theorem.

If `(8)` is proved on paper, the required Lean endpoint is the complete chain

```text
completed Euler--Gamma source
  -> J_Xi and its thin slice
  -> absolute mass < 2
  -> zero off-line charge in every window
  -> RiemannHypothesis.
```

Every arrow must be unconditional and axiom-audited.  Until then, Route C has no formal RH proof.

## Gates

- [x] 0 -> 1: the current, bare leakage, and first-order leakage objects and kill conditions
  isolated.
- [x] 1 -> 2: shift intersection, current construction, cutoff independence, quotient
  cancellation, static leakage no-go, and collision-blindness proved on paper.
- [ ] 2 -> 3: no significant fully proved theorem selected for Lean; `(8)` / `(9)` is open.
- [ ] 3 -> 4: no unconditional RH proof.
