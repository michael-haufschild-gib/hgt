# HB source-FE spectral-local kernel rigidity

- **ID:** HC55
- **Stage:** 3-formalized
- **Type:** THEOREM / HARD FRONTIER / MULTIPLICITY-FIBRE CLASSIFICATION
- **Source:** HC52 arbitrary-kernel Ward classification; HC53 reflection-orbit extinction; HC54
  line-conjugate nonlocal survivor; literal finite Xi source packets
- **Statement:** A reflection-real source-FE Ward kernel supported within equal Xi spectral fibres has
  a zero row at every tilted divisor copy; consequently spectral locality plus trivial left radical
  makes packet covariance equivalent to RH.

## Corpus-led conjecture

The literal Peierls packet space indexes every zero with its full divisor multiplicity.  Define
spectral-fibre locality by

```text
K(q,r) != 0  =>  support(q) = support(r).
```

This is strictly weaker than diagonal support: `K` may mix every multiplicity copy over one zero.
It is also exactly the property violated by HC54's canonical survivor, whose nonzero row at `q`
lands at `Jq = 1-conj(q)`.

The literal source and normalized FE cocycle depend only on the underlying Xi zero, not its
multiplicity label.  Hence equal spectral support gives `kappa(r)=kappa(q)`.  For a nonzero
spectral-local coefficient, reflection reality reduces the Ward equation to

```text
conj(K(q,r)) * kappa(q)^2 = conj(K(q,r)),
```

so `kappa(q)^2=1`; HC51's exact source calculation forces `Re(q)=1/2`.  Therefore every tilted row
is identically zero.  A trivial left radical forbids such a row because the basis packet at `q`
would lie in it.

## Formal result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFESpectralLocalKernelRigidity`.
Lean proves:

1. literal BM unit source amplitude and normalized source-FE cocycle descend from multiplicity
   copies to Xi divisor support;
2. any nonzero same-support coefficient of a reflection-real Ward kernel forces that support onto
   the critical line;
3. every tilted row of a reflection-real, spectrally local Ward kernel vanishes, with arbitrary
   multiplicity-copy mixing allowed;
4. the corresponding tilted basis packet lies in the finite-packet form's left radical;
5. trivial left radical forces a nonzero entry in every row;
6. spectral locality, reflection reality, and trivial left radical make full finite-packet
   source-FE covariance equivalent to RH; and
7. HC54's canonical line-conjugate permutation kernel is spectrally local exactly when RH holds.

This closes every fixed-form loophole confined to one Xi support fibre, not merely diagonal or
two-copy FE-orbit couplings.  Away from RH, HC54's unconditional nondegeneracy must be genuinely
cross-spectral.  Remaining hard producer is source-dynamical: derive spectral locality of the
physical augmented Einstein/Teukolsky Peierls current before divisor selection.

## Hostile checks discharged

- Fibre constancy was unfolded from literal source definitions; no cocycle descent was postulated.
- All `XiZeroCopy` multiplicity labels remain; locality permits arbitrary within-fibre mixing.
- Row nonvanishing was derived from trivial left radical by an explicit finite-packet basis test.
- Reverse implication was proved for arbitrary reflection-real coefficients under RH.
- HC54 kernel locality was classified exactly, including normalized source-extinction cases.
- No off-line zero existence was assumed.

## Novelty boundary as of 2026-08-28

Required corpus searches found diagonal rigidity (HC52), full within-FE-orbit extinction (HC53),
and the nonlocal line-conjugate permutation survivor (HC54), but no same-spectral-fibre
multiplicity classification or radical-to-RH endpoint.  Green--Hollands--Sberna--Toomani--
Zimmerman (arXiv:2210.15935, revised 2024) derive a symmetric conserved Kerr bilinear form and
orthogonality of QNMs with distinct complex frequencies from local currents and time-translation
symmetry.  Targeted primary-literature searches through 2026 found no Xi-divisor source-FE Ward
kernel theorem of this form.  Search is bounded, not exhaustive.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed source/cocycle descent and row-extinction proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC54 constructed an unconditional nondegenerate Ward form supported
  on `q <-> 1-conj(q)`.  Corpus search identified same-spectral-fibre locality as the exact physical
  separator left by that no-go.
- 2026-08-28 — Proved literal source/cocycle fibre descent, nonzero-entry rigidity, full tilted-row
  extinction, basis-radical obstruction, radical-to-row nonvanishing, and packet-covariance iff RH.
- 2026-08-28 — Proved HC54's canonical survivor is spectrally local iff RH, so its off-wall
  nondegeneracy necessarily crosses distinct Xi supports.
- 2026-08-28 — Direct `lake env lean` and target-only `lake build` passed (`11923/11923`). All ten
  public theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint
  reports no HC55 failure; remaining errors are unrelated pre-existing umbrella reachability gaps.
