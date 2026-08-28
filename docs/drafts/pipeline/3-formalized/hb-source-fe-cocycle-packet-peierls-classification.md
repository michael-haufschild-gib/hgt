# HB source-FE cocycle packet Peierls classification

- **ID:** HC51
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-FE WARD CLASSIFICATION / FIXED-vs-TRANSPORTED PEIERLS FORM
- **Scientific status:** `[LEAN-PROVED] [NOVELTY-PLAUSIBLE] [SOURCE-SPECIFIC] [RH-BEARING]`
- **Parent:** `hb-source-fe-cocycle-fixed-pairing-rigidity.md`
- **RH used:** no
- **Computation used:** no

## Audited frontier

`ThetaCuspHawkingBMSourceFECocycleFixedPairingRigidity.lean` constructed the literal unit-source
anti-linear FE cocycle `kappa(q)`, proved

```text
kappa(Rq) conjugate(kappa(q)) = 1,
```

and classified fixed Peierls preservation on one basis fibre.  Corpus search found no full-packet
transport and no classification of all diagonal Peierls forms invariant under that source
transport.  Thus a live loophole remained: tilted defects might cancel after reflection reindexing
or under a nontrivial fixed diagonal reweighting.

The read-only frontier map was not modified.

## New theorem package

For finite Xi packets, Lean constructs the anti-linear map

```text
T(single q c) = single (Rq) (kappa(q) conjugate(c))
```

and proves `T(T(x))=x` unconditionally.

For every diagonal complex-bilinear Peierls form

```text
B_w(x,y) = sum_q w(q) x(q) y(q),
```

Lean proves the exact classification

```text
B_w(Tx,Ty) = conjugate(B_w(x,y)) for every finite x,y
iff
w(Rq) kappa(q)^2 = conjugate(w(q)) for every q.             (HC51-Ward)
```

Necessity is witnessed on a single basis vector, while sufficiency is proved on the full finite
packet.  Therefore neither cross-fibre interference nor reflection reindexing can cancel a tilted
Ward defect.

The source-forced transported weight

```text
w_source(q) = conjugate(kappa(q))
```

solves `(HC51-Ward)` unconditionally.  Hence transported Peierls geometry is not the missing RH
input.  Lean then proves both exact fixed-form endpoints:

```text
B_source = B_fixed on all finite packets  iff  RH,
B_fixed(Tx,Ty) = conjugate(B_fixed(x,y)) for all x,y  iff  RH.
```

Finally, for every everywhere-nonzero reflection-real fixed diagonal weight

```text
w(Rq) = conjugate(w(q)),
```

its full-packet Ward covariance is equivalent to RH.  Thus no nondegenerate real/positive fixed
diagonal renormalization can evade the HC50 obstruction.

## Mathematical significance

HC51 closes the complete algebraic packet-classification burden left by HC50:

1. literal source transport exists on every finite Xi superposition;
2. every invariant diagonal form is governed by one exact reflection-orbit equation;
3. cross-orbit cancellation is impossible;
4. transported form is canonical and unconditional;
5. identifying any nondegenerate reflection-real fixed physical Peierls form with that transport is
   precisely the RH-bearing Ward step.

This does not prove RH.  Remaining HB producer is now strictly physical: derive from literal
augmented Einstein--Teukolsky source/constraint/corner dynamics that the fixed physical Peierls
form, rather than merely the source-transported form, obeys the HC51 Ward equation.  Same
fixed-vs-transported distinction is the shared reflected-wall obstruction appearing in FZZ-P,
RBH, and PW-B.

## Bounded novelty audit

Primary-source search through 2026-08-28 found no statement of `(HC51-Ward)`, its canonical source
solution, or its fixed-form rigidity:

- Green--Hollands--Sberna--Toomani--Zimmerman construct a symmetric conserved complex-bilinear
  Teukolsky form from physical reflection, but do not attach the Riemann-Xi source cocycle or
  classify packetwise invariant weights: <https://arxiv.org/abs/2210.15935>.
- Spiers--Pound--Moxon construct the literal nonlinear second-order Teukolsky source, without this
  FE/Peierls packet classification: <https://arxiv.org/abs/2305.19332>.
- Suzuki's August 2026 screw-function framework leaves its cofinal self-adjoint limit conjectural:
  <https://arxiv.org/abs/2606.09096>.
- Connes--Consani--Moscovici leave spectral/determinant convergence as the RH-bearing step:
  <https://arxiv.org/abs/2511.22755>.

Novelty claim is limited to this project-specific source-cocycle/Peierls classification and its
formal theorem package; it is not an exhaustive literature-wide priority claim.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEPacketPeierlsClassification
```

Principal declarations:

- `hbXiPeierlsUnitSourceFEPacketTransport`
- `hbXiPeierlsUnitSourceFEPacketTransport_single`
- `hbXiPeierlsUnitSourceFEPacketTransport_involutive`
- `HBXiPeierlsUnitSourceFEWeightWard`
- `forall_hbXiPeierlsWeightedDot_packetTransport_iff_weightWard`
- `hbXiPeierlsUnitSourceFETransportedWeight_weightWard`
- `hbXiPeierlsUnitSourceFETransportedWeightedDot_packetWard`
- `forall_hbXiPeierlsUnitSourceFETransportedWeightedDot_eq_fixed_iff_rh`
- `forall_hbXiPeierlsDot_unitSourceFEPacketTransport_iff_rh`
- `forall_hbXiPeierlsWeightedDot_packetTransport_iff_rh_of_reflectionReal`

Verification:

- direct `lake env lean` check passed;
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEPacketPeierlsClassification`
  passed (`11919/11919`); no umbrella/full build was run;
- all 19 public theorem axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint reports no HC51 issue; repository-wide lint still reports unrelated unreachable
  modules owned by other work;
- module is imported by `GaloisForLFunctions.RHTower` umbrella.

