# HB source-FE QNM-generator locality no-go

- **ID:** HC56
- **Stage:** 3-formalized
- **Type:** THEOREM / CLASSIFICATION / PRODUCER NO-GO
- **Source:** HC55 spectral-local rigidity; literal topological-black-hole QNM frequency;
  finite Xi Peierls packets and physical diagonal pairing
- **Statement:** Symmetry of an arbitrary finite-packet kernel form under the literal BM QNM
  time-translation generator is equivalent to spectral-fibre locality; the physical identity
  kernel has this conservation unconditionally while its source-FE Ward law remains equivalent
  to RH.

## Corpus-led conjecture

For fixed overtone `n`, let

```text
omega_n(q) = QNMPlus(n, xiSpectralPoint(q))
G_n e_q = omega_n(q) e_q.
```

The literal QNM formula is affine with nonzero slope in the Xi support, so
`omega_n(q)=omega_n(r)` exactly when `q` and `r` lie over the same Xi zero.  For arbitrary kernel
form `B_K`, infinitesimal time-translation conservation is

```text
B_K(G_n x,y) = B_K(x,G_n y).
```

Testing on basis packets gives

```text
K(q,r) * (omega_n(q)-omega_n(r)) = 0.
```

Thus generator symmetry is exactly HC55 spectral-fibre locality, including arbitrary multiplicity
mixing.  Conversely same-fibre support makes the coefficient equation hold and lifts to every
finite packet.

## Formal result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMGeneratorLocalityNoGo`.
Lean proves:

1. the literal positive-branch BM QNM frequency has an exact affine Xi-support formula;
2. at fixed overtone, equality of QNM frequencies is equivalent to equality of Xi supports;
3. full finite-packet generator symmetry is equivalent to its ordered-pair coefficient law;
4. that coefficient law is equivalent to HC55 spectral-fibre locality;
5. the physical identity kernel form is exactly the corpus Peierls dot product, is reflection-real,
   spectrally local, and left-nondegenerate;
6. both the packet dot product and constructed global two-channel Peierls pairing are symmetric
   under the literal QNM generator unconditionally;
7. source-FE covariance of the same physical identity kernel is equivalent to RH; and
8. HC54's canonical line-conjugate survivor is QNM-generator symmetric exactly under RH.

## No-go closure

- **Exact killing theorem/mechanism:**
  `forall_hbXiPeierlsKernelForm_qnmGenerator_symmetric_iff_spectralLocal` proves stationary QNM
  generator symmetry contains exactly spectral locality and no FE Ward information.  The physical
  identity kernel satisfies generator symmetry unconditionally, while
  `forall_hbXiPeierlsPhysicalIdentityKernelForm_packetTransport_iff_rh` proves its source-FE Ward
  covariance remains exactly RH-strength.
- **Strongest positive survivor:** conserved BM QNM bilinear forms are completely classified at the
  Xi packet level: they may mix arbitrary divisor multiplicity copies but cannot couple distinct Xi
  supports.  This is a multiplicity-exact QNM orthogonality theorem, not merely a negation.
- **New insight:** HC55's locality premise is genuinely supplied by stationary source dynamics, but
  locality and FE--Schwarz covariance are independent.  Remaining HB producer must couple the
  QNM generator/current to functional-equation reflection; ordinary Noether time conservation is
  exhausted.
- **Status:** dependency-closed paper proof and Lean formalization; target build and axiom audit pass.

## Hostile checks discharged

- Used literal topological-black-hole QNM frequency rather than an invented coordinate.
- Proved frequency separation in both directions with full divisor-support equality.
- Lifted coefficient law to arbitrary finite packets by finite-support induction.
- Retained multiplicity labels and all within-fibre kernel matrices.
- Identified identity-kernel form exactly with corpus Peierls dot product and then the global
  two-channel pairing.
- Kept generator symmetry logically separate from source-FE Ward covariance.

## Novelty boundary as of 2026-08-28

Required corpus searches found literal BM QNM frequencies, direct-sum Peierls pairing, HC55
spectral-local rigidity, and many time-oriented frequency identities, but no arbitrary-kernel
QNM-generator symmetry classification.  Green--Hollands--Sberna--Toomani--Zimmerman
(arXiv:2210.15935, revised 2024) derive conserved Kerr bilinear forms and different-frequency QNM
orthogonality; Gajic--Warnick (arXiv:2407.04098) define QNMs as eigenvalues of the infinitesimal
time-translation generator.  Targeted primary-literature searches found no Xi-divisor/source-FE
separation theorem or comparison with the FE Ward law.  Search is bounded, not exhaustive.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed frequency-separation and kernel-classification proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC55 proved spectral locality plus nondegeneracy closes arbitrary fixed
  kernels.  Corpus QNM-frequency and Peierls modules identified stationary generator symmetry as
  strongest available source-native locality mechanism.
- 2026-08-28 — Proved exact QNM frequency separation, coefficient-law equivalence, and complete
  arbitrary finite-packet generator-symmetry iff spectral-locality classification.
- 2026-08-28 — Identified physical identity kernel with Peierls dot product and proved unconditional
  generator symmetry of the full constructed two-channel Peierls pairing.
- 2026-08-28 — Proved generator symmetry does not supply source-FE Ward: physical identity kernel
  covariance remains iff RH; HC54 survivor gains generator symmetry iff RH.
- 2026-08-28 — Direct `lake env lean` and target-only `lake build` passed (`11924/11924`). All 15
  public theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint
  reports no HC56 failure; remaining errors are unrelated pre-existing umbrella reachability gaps.
