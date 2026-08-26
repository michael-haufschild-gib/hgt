# Nonlinear BM FE-reflection boundary producer (2026-08-26)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNonlinearFEReflectionBoundaryProducer.lean`; imported from `formal/GaloisForLFunctions/RHTower.lean`.

## Construction

For Xi copy q and common horizon amplitude H, define the literal BM folded boundary defect
[
d_q(H)=(T(1-\rho)-T(\bar\rho))H.
]
Pair the complete retarded total renormalized ++- angular periods on FE-reflected and Schwarz-conjugated sectors:
[
P_q=P_{ret}(q_{FE})+P_{ret}(q_{Sch}).
]
Existing total Green identity gives
[
\operatorname{Im} P_q=\|\mathcal R_{FE}\|^2+\|\mathcal R_{Sch}\|^2>0
]
for every nonzero theta seed, including all direct, causal/continuum, and orthogonal-helicity pieces; arbitrary real conservative finite part remains allowed.

Define causal quarter-turned nonlinear boundary current
[
J_q(d)=d-iP_q|d|^2d.
]
New exact optical power identity:
[
\Re(\bar d J_q(d))=|d|^2+(\operatorname{Im}P_q)|d|^4.
]
Hence every nonzero defect has strictly positive boundary power. Algebraically, coefficient
(1-iP_q|d|^2) has real part (1+(\operatorname{Im}P_q)|d|^2>0), so
[
J_q(d)=0\iff d=0.
]
For nonzero common horizon amplitude:
[
J_q=0\iff T(1-\rho)=T(\bar\rho).
]
Together with `d4BMXiSecondHarmonicBoundaryTransfer_reflect_conj_collision_iff`, this stationary law is copywise equivalent to Re rho=1/2.

## Scientific boundary

This is a concrete nonlinear, source-free folded boundary equation using the actual total retarded Einstein-Teukolsky period; it is not derived from gauge, real structure, KMS, causality alone, or horizon matching. The remaining physical incidence is whether the exact nonlinear gravitational boundary variational/impedance law is precisely source-free in this folded channel. Do not claim Einstein dynamics has independently forced J=0 without that incidence.

## Verification

Direct targeted Lean compile passed. `#print axioms` for all 12 new declarations returned only `[propext, Classical.choice, Quot.sound]`. Formal lint still fails only on pre-existing umbrella-unreachable modules; new module is reachable. Scratch and explicitly created target/dependency oleans were removed. No docs/route ledgers/git touched.

## Failed conjectures before pivot

1. Closed FE source cycle: endpoint closure does not imply zero work in dissipative horizon dynamics.
2. Nonzero ++- mixing alone: damps homogeneous FE-odd data but forced scattering can sustain mismatch.
3. Independent formation-depth/bounded-work replication: finite black-hole energy permits shrinking amplitudes, so no uniform per-copy lower bound.
