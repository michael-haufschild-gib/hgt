# Formation-transfer germ mechanism law

- **ID:** ULF-FTGM-LEAN-1
- **Stage:** 3-formalized
- **Type:** UNIVERSAL MECHANISM CORE
- **Status:** `[LEAN CERTIFIED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/universal-law-field/formation-transfer-germ-mechanics/poisson-boolean-information-transfer-cocycle-and-boundary-germ-tomography-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationTransferGerm.lean`

## Certified laws

For arbitrary observer work `W`, source density `C`, and multiplicative depths `m,n,k`, Lean proves

\[
 T_W(m,nk)=kT_W(m,n)+T_W(mn,k),
 \qquad T_W(m,n)=nW(m)-W(mn),
\]

and

\[
 H_C(mn)=nH_C(m)+T_W(m,n),
 \qquad H_C(m)=mC-W(m).
\]

It also proves:

- directed transfer swaps under functional-equation label exchange;
- symmetric transfer is invariant;
- positive exponential germs recover their decay by logarithmic cofinal slope;
- their multiplicative scale identity retains amplitude data;
- all laws hold simultaneously in `formationTransferGerm_mechanism`.

The capstone has no mathematical premise.  `#print axioms` reports only Lean/mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration is used.

## Verification

Executed successfully:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveFormationTransferGerm.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveFormationTransferGerm
```

Final build: `1942/1942` jobs passed.

Project-wide lint currently fails on pre-existing unreachable RHTower/HTGeometry modules created
elsewhere in the shared worktree.  It reports no defect in this module, which is wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Exact scope

This certifies formation-transfer mechanics and exponential-germ tomography.  It does not yet
certify the paper card's concrete Bernoulli relative-entropy asymptotics or Stokes comparison.
Those claims remain Stage 2 until separately formalized.
