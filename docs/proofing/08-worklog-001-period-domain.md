# C-2026-06-18-001 Proof Attempt: D_infty Period Domain

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

```text
RH <=> F_zeta lies in the interior of D_infty = Sp_infty(R)/U(infty),
off-line zero = hyperbolic/boundary direction.
```

## Attempt

In finite-dimensional Hodge/period-domain geometry, being in the interior is a
positivity condition on a polarization. Boundary approach corresponds to
degeneration of that positive form. Thus the claim would follow from a period
map `F_zeta` whose polarization form has negative-square index `kappa_-`.

If

```text
F_zeta in interior <=> kappa_- = 0,
kappa_- = # off-line zero pairs,
```

then the claim is equivalent to RH.

## Weakened Theorem

Given a period map with faithful polarization index equal to the off-line zero
count, interiority is equivalent to RH.

## Obstruction

No period map `F_zeta`, infinite symplectic domain model, or comparison theorem
is defined in the consolidated corpus. The statement is currently a coordinate
reading of the faithful positivity apex.

## Missing

Construct `D_infty`, define `F_zeta`, prove its polarization index is
`kappa_-`, and prove boundary directions are exactly off-line pairs.
