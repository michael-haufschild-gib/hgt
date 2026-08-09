# Hedenmalm prime-normal Jordan-grade separation

- **ID:** `hedenmalm-prime-normal-jordan-grade-separation`
- **Stage:** 1-in-progress
- **Type:** FROZEN CONJECTURE / ROUTE-N FRONTIER CORRECTION
- **Source:** `rh-current-frontier-map.md` Route N; hostile collision audit against the marked
  half-character, prime-log-jet Gram, Hedenmalm divided-chain, and prime-translation anomaly cards
- **Statement:** On every Hedenmalm root module, marked prime characters transported by their
  canonical flat connection have the same all-prime domain in every Jordan grade, whereas ordinary
  prime-character jets acquire a sharp prime-log moment and already fail the sub-log-square domain
  at grade one on the critical line.
- **Frozen label:** `[N-JET-GRADE-SEPARATION-1]`, superseded after attack by
  `[N-MARKED-ENDPOINT-DOUBLET-1]`
- **Scientific status:** `[CONJECTURE FROZEN] [INTERNAL NOVELTY AUDIT PARTIAL] [NOT RH] [NO LEAN YET]`

## Goal

Correct Route N's current open statement before another source-domain attack. The existing map asks
one uniform sub-log-square estimate to retain the complete Jordan tower. If ordinary spectral jets
are meant, that estimate contains an independent simplicity demand. The intended theorem separates
multiplicity transport from horizontal detection: Jordan grades use the canonical connection of the
ordinary-prime character; only grade zero remains an RH-bearing source-admission problem.

This does not prove grade-zero admission and does not weaken it. It prevents a proof of RH from being
silently upgraded to RH plus simplicity by a non-geometric choice of jet operator.

## Exact frozen objects

For a prime `p`, put `L_p=log p` and define the marked centered half-character column

```text
h_p(z) = p^(-1/2) (exp(+i z L_p/2), exp(-i z L_p/2)).
```

Its odd scalar soldering is the known Hedenmalm prime-normal multiplier

```text
b_p(z) = -i [h_p(z)_+ - h_p(z)_-]
       = 2 p^(-1/2) sin(z L_p/2).
```

Define the diagonal connection on two-component entire columns by

```text
nabla_p g = partial_z g - diag(+i L_p/2, -i L_p/2) g.       (N.1)
```

The connection is fixed before any Xi zero is selected.

## Frozen theorem package

### T1 — ordinary first-jet wall

For every real `x`,

```text
||partial_z h_p(x)||^2 = (log p)^2/(2p),                    (N.2)
```

and therefore

```text
sum_(p<=X) ||partial_z h_p(x)||^2
  >= (log X)^2/4 - (39/2) log X - 25/2.                    (N.3)
```

In particular the ordinary first marked jet is not `o((log X)^2)` at any real spectral point.
The same phenomenon in the odd scalar soldering has oscillatory phase, but the marked source-normal
carrier already proves that the full-tower ordinary-jet demand is stronger than the grade-zero RH
criterion.

### T2 — canonical flat removal of prime-log Jordan cost

The connection `(N.1)` is the unique diagonal constant connection satisfying

```text
nabla_p h_p = 0.                                           (N.4)
```

For every entire scalar `F` and every `j>=0`,

```text
nabla_p^j (h_p F) = h_p F^(j).                             (N.5)
```

Hence, at every real `x`,

```text
sum_(p<=X) ||nabla_p^j(h_p F)(x)||^2
  = 2 |F^(j)(x)|^2 sum_(p<=X) 1/p
  = o((log X)^2).                                          (N.6)
```

Multiplicity is retained in `F^(j)(x)` while the ordinary-prime character remains parallel. No
prime-log moment is charged merely for moving up the Jordan filtration.

### T3 — Route-N grade split

Under the already formalized Hedenmalm conormal law

```text
ell_z^[j](T_p f)
  = p^(-s(z)) sum_(r<=j) binom(j,r)(-i log p)^(j-r) ell_z^[r](f),
```

ordinary differentiation is exactly the triangular prime-log prolongation. Passing to the marked
flat frame conjugates this prolongation to coefficient differentiation `(N.5)`. Thus:

```text
full Jordan transport = flat algebraic transport + grade-zero boundary admission.   (N.7)
```

The surviving Route-N estimate is the grade-zero statement only:

```text
for every grade-zero root mode f in the closed theta Grushin domain,
sup_X H_X^(-1) sum_(p<=X) ||A_p(B)f||^2 < infinity.         (N.8)
```

Higher grades must be transported covariantly. Requiring `(N.8)` of ordinary raw jets would force
semisimplicity/simplicity in addition to horizontal reality.

## Conjecture -> attack -> pivot log

### C0 — unmarked half-character lift

**Conjecture.** Retaining both half-character orientations removes the Route-N obstruction.

**Attack.** Corpus search found the exact marked half-character torsor, odd soldering, reflected
energy, and all-prime diagonal-inverse obstruction already proved and formalized. The lift alone is
`[REDISCOVERED] [BRIDGE]`, not new knowledge and not a source-domain proof.

**Pivot.** Compare ordinary and covariant Jordan prolongations, which the marked card does not do.

### C1 — raw full-tower sub-log-square descent

**Conjecture.** One source-domain sub-log-square estimate can hold unchanged on every ordinary
Jordan grade.

**Attack.** `(N.2)` and the corpus theorem
`RHTower.Sieve.sum_prime_log_sq_div_ge` give `(N.3)` without RH, zero data, or asymptotics. Grade one
already sits at the log-square wall on the critical line. The universal Mertens-normal prime-log-jet
Gram law independently identifies these log moments as system-blind leading data.

**Verdict.** `[FALSIFIED AS STATED]`. Raw full-tower descent is not the RH criterion.

**Pivot.** Use the character's canonical connection and test whether it is compatible with the
source conormal/Jordan law.

### C2 — covariant grade separation

**Conjecture.** `(N.4)`--`(N.7)` convert all higher-grade source admission to grade-zero admission
without losing analytic multiplicity.

**Attack list.**

1. Prove exact flatness, uniqueness, Leibniz iteration, and energy identities.
2. Pin the gauge conjugation to the formalized Hedenmalm conormal prime-jet law.
3. Test against divided-chain recurrence and multiple-zero fibers.
4. Test against the existing cofinal diagonal-inverse no-go: no inverse or bounded Hilbert
   diagonal is to be asserted.
5. External exact-conjunction audit after paper closure.

**Attack result.** The strong scalar reading is false. Let

```text
S_odd(v_+,v_-) = -i(v_+-v_-),       K=ker S_odd=span(1,1),
Gamma_p = diag(+iL_p/2,-iL_p/2).
```

Although `partial_z-Gamma_p` is flat on the marked doublet, it descends through `S_odd` only if
`K` is `Gamma_p`-invariant. But

```text
Gamma_p(1,1)=(+iL_p/2,-iL_p/2) notin K                    (N.9)
```

for every prime. Thus there is no scalar quotient connection making both half-characters parallel.
Using `(N.5)` after scalar soldering silently changes the carrier.

**Verdict.** `[FALSIFIED IN THE SCALAR CARRIER]`.

### Positive survivor — soldering curvature theorem

Put

```text
e_p(z)=h_p(z)_+ + h_p(z)_-,
o_p(z)=-i(h_p(z)_+ - h_p(z)_-)=b_p(z).
```

Direct differentiation gives the exact two-channel system

```text
partial_z (e_p,o_p)^T
  = (L_p/2) [[0,-1],[1,0]] (e_p,o_p)^T.                  (N.10)
```

Hence

```text
partial_z o_p=(L_p/2)e_p,      partial_z e_p=-(L_p/2)o_p. (N.11)
```

The prime-log Jordan cost is the second fundamental form of the nonparallel odd soldering line
inside the flat marked bundle. On the real axis the full marked first-jet energy is

```text
||partial_z h_p||^2=(L_p)^2/(2p),                         (N.12)
```

so the log-square wall `(N.3)` is precisely the cofinal squared norm of this curvature.

#### Paper proof

Differentiate `exp(+/- izL_p/2)`. This gives
`partial_z h_{p,+}=+iL_p h_{p,+}/2` and
`partial_z h_{p,-}=-iL_p h_{p,-}/2`. Adding and taking `-i` times the difference proves
`(N.10)`--`(N.11)`. For real `z`, both exponentials have modulus one, so the two squared component
norms are each `L_p^2/(4p)`, proving `(N.12)`. Summing and applying the already formalized explicit
lower bound

```text
sum_(p<=X) (log p)^2/p >= (log X)^2/2-39log X-25
```

proves `(N.3)`. Finally `(N.9)` is the same calculation on the kernel generator and proves
non-descent. No analytic, divisor, RH, simplicity, or asymptotic premise occurs. `QED`.

### C3 — source-derived marked endpoint doublet

**Frozen conjecture `[N-MARKED-ENDPOINT-DOUBLET-1]`.** Keep the marked doublet through source-normal
completion instead of quotienting to its odd channel. For continuous logarithmic aperture `L>0`,
define the source window

```text
C_L(x)=exp(-L/2) integral_[x-L/2,x+L/2] k(u)du.             (N.13)
```

Its center derivative and covariant width derivative recover both source-defined endpoints:

```text
partial_x C_L
  = exp(-L/2)[k(x+L/2)-k(x-L/2)],

2(partial_L+1/2)C_L
  = exp(-L/2)[k(x+L/2)+k(x-L/2)].                          (N.14)
```

After Fourier transform and source-normal division by `XiC`, `(N.14)` is exactly the marked
even/odd pair. At `L=log p` its squared prime-normal value is

```text
4/p (|cos(z log p/2)|^2+|sin(z log p/2)|^2)
  = 4/p cosh(Im(z) log p),                                 (N.15)
```

independent of the vertical clock `Re(z)`. Covariant Jordan jets remain in this rank-two bundle;
ordinary scalar jets are recovered only by applying the curved soldering afterward.

The new source-domain target is: prove the endpoint doublet `(N.14)`, not merely its odd interval
quotient, has a closed source-normal Besicovitch landing on the theta Grushin domain before root
specialization. This remains RH-bearing at grade zero. Its advantage is exact multiplicity transport
without an accidental simplicity condition and removal of finite-prime clock recurrence from the
energy itself.

**Next attacks.**

1. Prove `(N.13)`--`(N.15)` from the actual theta source, including endpoint regularity.
2. Audit whether the even endpoint channel survives the same source-normal quotient as the odd
   interval anomaly or carries an uncancelled source line.
3. Test closedness against source-linear superselection: the conjecture keeps a direct marked
   doublet and asserts no reflected-sector sewing or diagonal inverse.
4. Derive the exact finite-cutoff operator row and seek a source estimate before zero
   specialization.

## Collision and novelty boundary

- Marked half-character, root torsor, odd soldering, reflected radial energy, and diagonal-inverse
  obstruction: corpus-owned; no novelty claimed.
- Prime-log moment asymptotics and multiplicative-regularization blindness: corpus-owned; no novelty
  claimed.
- Hedenmalm divided Jordan chain and symmetric-carrier simplicity obstruction: corpus-owned and
  explicitly classified as a non-new bridge.
- Candidate delta: exact non-descent/soldering-curvature law `(N.9)`--`(N.12)` and its source-window
  endpoint-doublet pivot `(N.13)`--`(N.15)`. Ordinary prime-normal prolongation is not a removable
  artefact inside the scalar carrier; its log cost measures failure of the flat marked connection
  to descend.
- Current primary-literature search found Hedenmalm's June 2026 paper but no prime-normal,
  prime-log-Jordan, or covariant marked-jet treatment. External novelty remains provisional until
  the theorem is dependency-closed and the exact conjunction is searched again.

## Hostile scope

1. Flat marked transport does not prove `(N.8)` or the new endpoint-doublet landing.
2. It does not create a positive form, bounded diagonal inverse, or ordinary-`L2` completion.
3. It does not prove Xi zeros simple; it removes an accidental simplicity demand from the RH lane.
4. It does not evade the generic-source falsifier. Generic positive sources with nonreal Fourier
   zeros must still fail grade-zero descent.
5. It does not replace the source-normal nonsummable topology by a summable Hilbert row.

## Gates

- [x] 0 -> 1: exact source-pure statement frozen; collisions and falsifiers recorded
- [ ] 1 -> 2: formalize dependency-closed soldering-curvature survivor; close or kill C3; exact
  conjunction novelty audit
- [ ] 2 -> 3: unconditional Lean theorem package; umbrella wiring; lint and axiom audit
- [ ] 3 -> 4: only if scientific novelty/significance survives hostile review

## No-go closure for C1

- **Exact killing mechanism:** ordinary differentiation of the marked prime character contributes
  `(log p)^2/(2p)` at first grade, whose finite-prime sum has an unconditional log-square lower
  bound.
- **Strongest positive survivor:** canonical flat connection `(N.1)` makes the character parallel
  and moves the complete Jordan filtration into coefficient jets, preserving prime-harmonic rather
  than prime-log energy at every grade.
- **New insight:** Route N has two independent obligations—horizontal grade-zero admission and
  multiplicity transport. Conflating them creates a false simplicity-strengthened frontier.
- **Status:** T1 arithmetic input already formalized; T2 elementary paper proof open; T3 exact
  pinning to Hedenmalm conormal declarations open.

## No-go closure for scalar C2

- **Exact killing mechanism:** odd soldering kernel is not invariant under the marked flat
  connection; therefore connection does not descend to scalar prime-normal quotient.
- **Strongest positive survivor:** exact soldering-curvature system `(N.10)` and source-derived
  center/width endpoint doublet `(N.13)`--`(N.14)`.
- **New insight:** log-square Jordan wall is geometric curvature of scalarization, not loose
  arithmetic. Correct full-multiplicity carrier must remain marked until after covariant jets.
- **Status:** soldering-curvature theorem paper-proved and dependency-closed; Lean formalization now
  mandatory. Endpoint-doublet closed landing remains conjectural.

## Log

- 2026-08-09 — card created after C0 collision and C1 falsification; C2 frozen.
- 2026-08-09 — C2 scalar reading falsified by connection non-descent; curvature survivor
  paper-proved; C3 marked source-endpoint doublet frozen.
