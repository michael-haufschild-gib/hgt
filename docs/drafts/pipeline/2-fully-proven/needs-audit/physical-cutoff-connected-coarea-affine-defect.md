# Physical-Cutoff Connected Coarea Affine Defect

- **ID:** physical-cutoff-connected-coarea-affine-defect
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · `(AC25)`, `(35m60)`--`(35m65)`, `(SP10)`--`(SP16)`
- **Statement:** The low root-density packet and complete high-cutoff response obey one exact prime-adjunction trace recursion whose sole inhomogeneous term is the connected incidence/coarea forcing; its unique affine drift is the negative complete survival product, hence it is centered exactly in the parity-annihilated sector.

`[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
`[POSITIVE SURVIVOR OF COERCIVE-TRACE NO-GO] [TERMINAL SIGNED TRACE OPEN]`

## Goal

Close the algebraic half of the density-versus-response pairing without defining a residual from
the terminal covariance.  The theorem must produce the low density, complete observed high packet,
future prime dressing, and physical zero-mode switch from one identity.  It is not the missing
`M^{-1}` estimate and does not prove `(AC25)`, `FCRJ`, or RH.

## Gates

- [x] 0 → 1 in-progress: exact finite statement, source-pure definitions, hostile tests fixed
- [x] 1 → 2 fully-proven: dependency-closed finite proof below
- [ ] 2 → 3 formalized: exact Lean declarations, direct build, and axiom audit
- [ ] 3 → 4 publication-ready: not proposed; this is bridge infrastructure

## Statement

Let `R` be a commutative ring, let `S` be a finite set of prime coordinates, and fix natural
numbers `q,H`.  At an observation point `x`, write `chi_p(x)` for the incidence of coordinate `p`
and `theta_p` for its reference root density.  Define

```text
C_S(q)=sum_(T subset S, q product(T)<=H)
         (-1)^|T| product_(p in T)theta_p,

H_S(q;x)=sum_(T subset S, H<q product(T))
          (-1)^|T| product_(p in T)chi_p(x),

L_S(q;x)=-H_S(q;x).
```

Thus `C_S` is the low density, `H_S` is the complete observed high packet, and `L_S` is its signed
coarea orientation.  For a finite observation set `U`, weights `w_x`, and a reference mass `J`, put

```text
tau_S(q)=J C_S(q)-sum_(x in U)w_x L_S(q;x)
        =J C_S(q)+sum_(x in U)w_x H_S(q;x).             (CJ1)
```

For `p notin S`, exact subset splitting gives

```text
C_(S+p)(q)=C_S(q)-theta_p C_S(qp),
L_(S+p)(q;x)=L_S(q;x)-chi_p(x)L_S(qp;x).               (CJ2)
```

Consequently the joined trace satisfies

```text
tau_(S+p)(q)
 =tau_S(q)-theta_p tau_S(qp)
  +sum_(x in U)w_x(chi_p(x)-theta_p)L_S(qp;x).         (CJ3)
```

The last summand is the connected incidence/coarea forcing.  Iterating `(CJ3)` automatically
future-dresses every forcing by all later prime transfers.  If the high field is expanded into the
`K/G` profiles of `(SP10)`--`(SP15)`, the one connected product produces all four ports together;
there is no separate, noncanonical allocation of `(SP16)`.

The empty-set trace is the exact physical zero-mode switch:

```text
tau_empty(q)=J                    if q<=H,
tau_empty(q)=sum_(x in U)w_x      if H<q.              (CJ4)
```

Finally specialize the incidence to its reference density.  The affine field has drift

```text
-H_S(q;theta)-C_S(q)
 =-product_(p in S)(1-theta_p).                        (CJ5)
```

For quadratic roots, `theta_p=nu_h(p)/p`.  If every coordinate in `S` is prime, `(CJ5)` vanishes
exactly when

```text
2 in S and 2 does not divide h.                        (CJ6)
```

Thus, when `2 in S`, the canonical same-identity affine field is centered exactly for odd gaps.
Every even gap carries the forced negative singular-series ramp.

## Paper proof

Every subset of `insert p S` is uniquely either `T subset S` or `insert p T` with `T subset S`.
In the second class the cardinality gains one, the coefficient gains the factor `-theta_p` (or
`-chi_p(x)`), and the cutoff `q product(insert p T)<=H` becomes
`qp product(T)<=H`.  This proves both identities in `(CJ2)`.

Insert `(CJ2)` into `(CJ1)`.  Add and subtract
`theta_p sum_x w_x L_S(qp;x)`.  Regrouping gives `(CJ3)` exactly.  No estimate, positivity, or
periodic completion is used.

For `S=empty`, the only subset is empty.  Its product is one.  Hence the low sum is one and the
high sum zero when `q<=H`, while the low sum is zero and the high sum one when `H<q`; this proves
`(CJ4)`.

The low and high cutoff predicates partition the complete Boolean cube, so finite product
expansion gives

```text
C_S(q)+H_S(q;theta)=product_(p in S)(1-theta_p).
```

Negating proves `(CJ5)`.  For `theta_p=nu_h(p)/p`, the already-proved prime-local root
classification gives a zero survival factor only for `p=2` with `2` not dividing `h`; finite
product zero classification proves `(CJ6)`.  This closes every paper dependency.

## Hostile audit

- **`(35m55)`: survives only as an exact decomposition.**  If the connected forcing in `(CJ3)` is
  deleted, the forced affine drift `(CJ5)` remains and reproduces the homogeneous Euler mismatch.
  The theorem does not claim that drift is small.
- **`(35m66)` and generalized-prime bursts:** raw squares of `L_S` or of the connected forcing can
  still grow exponentially.  `(CJ3)` keeps their signs and future dressing; it supplies no positive
  energy estimate and is not universal cancellation.
- **Fixed log phases:** the deletion-contraction algebra also exists for phase-twisted coefficients.
  Therefore `(CJ3)` is a bridge, not an arithmetic discriminator.  A quantitative successor must
  use the literal real Möbius orientation and ordinary-integer observation functional.
- **Endpoint cells:** `(CJ4)` retains the actual weighted lattice mass above the cutoff rather than
  replacing it by `J`.  This is the complete-period/physical-zero-mode switch required by `(PF13)`.
- **RH-equivalence:** tracing the terminal iterate against the physical `W_h` and summing in `h`
  is exactly `(AC25)` after Duhamel expansion.  Calling that terminal bound a corollary of `(CJ3)`
  would be circular.

## Exact new route insight

The invariant causal atom is not a separately normalized density or response.  It is the pair
`(L_S,C_S)`, whose prime insertion has one and only one inhomogeneous term:
`(chi_p-theta_p)L_S`.  The density term and all four response ports are two faces of this same
connected forcing.  Its mean obstruction is not an unspecified Jordan mass but the exact survival
ramp `(CJ5)`, supported on even gaps once parity is present.

This materially narrows the representation of `(AC25)`, but it does not narrow its quantitative
strength: the terminal signed trace remains RH-equivalent.

## Lean plan

Reuse `truncatedAliasSum`, `truncatedAliasHighSum`, and the quadratic survival-product parity theorem
from `PhysicalCutoffAliasResponseJoining.lean` and
`ReducedFrequencyMobiusAliasCollapse.lean`.  Formalize `(CJ2)`--`(CJ6)` in one narrow RHTower
module.  Do not add analytic integration-by-parts infrastructure for the optional Abel form.

## Log

- 2026-07-18 — coercive coarea norm rejected; exact connected trace recursion and forced-drift
  classification extracted as the positive survivor.
- 2026-07-18 — dependency-closed paper proof and hostile audit completed; terminal signed trace kept
  open.
