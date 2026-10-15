# HCF structural research after first-contact rigidity

Status: active; no new qualifying result yet.

Objective: a further unconditional structural advance for HCF, beyond the
completed single-window transition and finite first-contact rigidity. An
estimate, RH equivalence, conditional source receiver, or repackaging of those
results does not satisfy this task.

Plan:
1. Search the current Lean corpus for unresolved structural obstacles and
   mechanisms that can remove them. Use completed prior proofs as input.
2. Conjecture, attack, and record what each failure rules out or exposes.
3. Formalize a successful dependency-closed structural theorem with no added
   source or RH premises; continue the loop until this is achieved.
4. Focused foreground builds only; direct final `lake env lean` audits, standard
   axiom checks, umbrella imports, index/lint, and cleanup of owned scratch.

Constraints: no web, novelty search, old research markdown, numerical
experiments, heartbeat changes, full/umbrella builds, commits, or pushes.
Preserve concurrent work, including the in-progress even-sector source work.

Starting mathematical facts: actual even ground energy strictly decreases with
aperture; a unique possible heat-window transition is proved. Every actual
finite heat-Hankel first contact has a strictly positive preceding head, a
single normalized null direction, positive quadrature with simple real nodes,
and a strictly earlier first contact at the next rank. Neither result orients
the completed prime--Gamma source. Ground-generator classification allows
derivative chains, so generator existence alone does not prove simplicity.

Search/conjecture ledger follows as the work progresses.

## Conjecture loop

1. Ground-generator existence might force simplicity. Rejected: the actual
   polynomial-generator theorem allows derivative chains. Boundary-source
   nonvanishing on the whole constrained sector does not imply nonvanishing
   or injectivity on the ground space. No valid source argument closes this.
2. At every heat time, regular Hankel heads should be cofinal, and every gap
   should have an exact polynomial-kernel classification. Paper mechanism:
   after a regular head of size n, take its canonical monic admission P.
   Nondegeneracy gives a first j with L(X^j P) nonzero; orthogonality gives
   j >= n. Set d = j - n + 1. Then the block X^r P, 0 <= r < d,
   is orthogonal to the old head and has a nonzero constant anti-diagonal,
   with zero entries before it. For 0 <= k <= d, the kernel at size n+k
   consists exactly of Pq with deg q < min(k,d-k). Polynomial division and
   the highest coefficient of q prove both directions. Thus n+d is the
   next regular head, every intervening head is singular, and recursion
   produces a cofinal regular ladder without a generic-time assumption.
   This is an exact classification, not a positivity receiver or estimate.
   Core classification, cofinality, covering existence and uniqueness now
   pass Lean. The exact kernel parametrization is a linear isomorphism from
   `Fin (min k (d-k)) -> R`; its nullity formula and the constant
   anti-diagonal Gram block also pass focused Lean builds. Full inertia and
   source orientation are not claimed by this argument.
3. Every genuine gap should produce an explicit hyperbolic plane orthogonal
   to its old head. Let Q = X^(d-1) P, delta = L(P Q) != 0 and
   R = Q - L(Q^2)/(2 delta) P. Then L(P^2) = L(R^2) = 0 and
   L(P R) = delta. Hence U = P + R/delta and V = P - R/delta have
   Gram matrix diag(2,-2). This is a constructive resolution of the zero
   pivot, not a sign assumption. Paper proof closed; Lean audit underway.

Corpus searches used the documented research command in deep mode, followed
by exhaustive focused Lean-source searches. The normal-block search was
partial but its file inventory complete; no existing normal-index/kernel-gap
classification was found. Ground search completed. Source declarations are
checked directly rather than trusting stale compiler-index metadata.
