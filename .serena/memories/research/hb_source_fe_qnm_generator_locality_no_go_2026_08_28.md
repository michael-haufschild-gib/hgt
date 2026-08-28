# HC56 — HB source-FE QNM-generator locality no-go (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEQNMGeneratorLocalityNoGo`

Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-qnm-generator-locality-no-go.md`

Results:
- Literal positive-branch BM QNM frequency is affine with nonzero slope in Xi support.
- At fixed overtone, QNM frequency equality iff Xi support equality.
- For arbitrary finite-packet kernel `K`, full infinitesimal QNM-generator symmetry iff ordered coefficient law `K(q,r)ω(q)=K(q,r)ω(r)`.
- That law iff HC55 spectral-fibre locality; arbitrary mixing among multiplicity copies over one zero remains allowed.
- Physical identity-kernel form equals corpus `hbXiPeierlsDot`; it is reflection-real, spectrally local, and left-nondegenerate.
- Packet dot and constructed global two-channel `hbXiPeierlsPairing` are QNM-generator symmetric unconditionally.
- Source-FE covariance of same physical identity kernel iff RH.
- HC54 line-conjugate kernel is QNM-generator symmetric iff RH.

No-go:
Ordinary stationary/Noether time-translation conservation supplies exactly spectral locality, not FE–Schwarz Ward covariance. HC55 locality is therefore source-dynamical, but independent of RH-bearing Ward law. Remaining HB producer must link the QNM generator/current to functional-equation reflection; ordinary time conservation is exhausted.

Audit:
- direct `lake env lean`: pass
- target-only build: 11924/11924 pass
- 15 public theorem axiom checks: only `propext`, `Classical.choice`, `Quot.sound`
- umbrella wired
- formal lint: no HC56 issue; only unrelated pre-existing reachability failures
- bounded literature audit: arXiv:2210.15935 (conserved Kerr QNM bilinear form/orthogonality), arXiv:2407.04098 (QNMs as time-generator eigenvalues), no Xi/source-FE comparison.