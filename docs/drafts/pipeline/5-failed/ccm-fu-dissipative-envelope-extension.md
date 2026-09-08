# CCM-FU: universal extension with nonempty-energy dissipation

- Stage: 5-failed.
- Type: unconditional arithmetic obstruction with a formal positive survivor.
- [Frozen question and experiment protocol](../1-in-progress/ccm-fu-dissipative-envelope-extension.md).
- [Analytic proof and Lean certificate](../3-formalized/ccm-fu-transverse-dissipation-trap.md).

## Refuted claim

Let Q(P) be actual retained energy, H(P) its head, V(P)=Q(P)-H(P)^2,
Psi(P) the maximum of Q(P) and all immediate successor energies, and
B=Q(empty). The proposed rule required every proper state with
Psi(P)≤B to have an available prime p satisfying both
Psi(P+p)≤B and V(P+p)≤V(P).

At cutoff 25, the actual core P={2,7,11,13,17,19,23} leaves exactly
primes 3 and 5. Lean proves Psi(P)+1/5<B, and for EACH available prime,
V(P)+1/500<V(P+p) and Psi(P+p)+1/250<Psi(P). Thus every next operation
forces nonempty-energy growth despite strictly improving full successor
admission. The counterexample also rejects existence of a nonempty-energy
dissipating next move at every proper state without the admission restriction.

## Strong positive survivor

The actual remaining field has coordinates h at the empty label,
a at {3}, b at {5}, and c at {3,5}. Analytic bounds prove h<0 and
a,b,c>0. The two nonempty-energy changes are 2bc-a² and 2ac-b²;
both are positive. The full-energy changes are 2ha+2bc and 2hb+2ac;
both are negative. The head square pays for the forced growth elsewhere.
The final step in either of the two complete remaining orders also
strictly lowers full energy. All these comparisons are formal, including
the current and successor envelope identities used by the public theorem.

For arbitrary real a,b,c, a sharp replacement inequality survives:

`min((a+c)^2,(b+c)^2) ≤ (3/2)(a²+b²+c²)`.

The factor 3/2 is necessary and sufficient for a uniform inequality of
this form; a=b=1, c=2 attains equality. This exact boundary is closed
in Lean for all signs. It permits bounded transient growth at one
two-coordinate step; iterating the factor supplies no uniform RH bound.

This retires mandatory local nonempty-energy dissipation only. It leaves
plain admitted successor extension, specially selected dissipating paths,
and uniform control of the final signed arithmetic sum open. A surviving
energy argument must budget transfers between head and remaining field.

## Evidence and closure

The [RunPod diagnostic](../2-fully-proven/computations/ccm-fu-dissipative-envelope-extension-2026-09-08/README.md)
screened all 8,860 stored states and independently reconstructed the
witness at 80 digits. Its reachability and finite path results remain
numerical guidance. No numerical value supplies a Lean premise.

The literal witness and the sharp replacement inequality have complete
paper proofs and Lean proofs in MobiusDivisorTransverseDissipationTrap.
The source intervals are proved in DivisorTwentyTwoAnalyticBounds.
Both exact leaves passed foreground Lean emission. All five new public
theorems were axiom-audited once: only propext, Classical.choice and
Quot.sound occur. See the formal certificate for final lint and build scope.
