# Hawking--Teukolsky charge-decay resonance ladder (2026-08-25)

Quadratic source incidence into the dealiased theta-Jost channel is impossible: open Xi strip plus the BM half-integer decay lattice excludes equality. The dealiased Jost object remains a genuine scattering receiver, but not a second-order Einstein source target.

New exact mechanism: let z be centered spectral coordinate, omega_0(z) the fundamental positive BM QNM, omega_0# = -star omega_0 its real-field partner, and Omega_n^-(Lz) the negative dealiased QNM. Phase charge -2 forces two more partners than direct modes. Exact Hawking decay arithmetic yields the affine ladder

- direct multiplicity r_k = 4k+2
- partner multiplicity s_k = 4k+4
- degree m_k = 8k+6
- target overtone n_k = 5k+3

with exact complex detuning
F_k(z) - Omega^-_{5k+3}(Lz) = 4(k+1) i Im(z).

Thus each rung reaches the actual Birmingham--Mokhtari gravitational Jost zero iff Im(z)=0. First rung is sextic: A^2 (bar A)^4 hits third negative overtone with detuning 4 i Im(z). Full resonant projection has canonical shape A^2 (bar A)^4 Phi(|A|^8). This is frequency/Jost incidence; full Einstein--Teukolsky radial/helicity projection must still prove at least one coefficient nonzero. Topology/KMS/passivity alone cannot force that coefficient or gap closure.

Formalized in:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyChargeDecayResonanceLadder.lean
Imported by formal/GaloisForLFunctions/RHTower.lean.
Corrected stale second-order-source claim in ThetaCuspHawkingQuadraticDealiasedJostPolarization.lean.

Verification: targeted Lean compile passed; all nine new theorems use only propext, Classical.choice, Quot.sound; lint has only pre-existing unreachable-module failures. No git. Temp/build artifacts cleaned.

Local novelty collision audit via scripts/formal_tools.py research found no existing 8k+6 / 5k+3 charge-decay ladder. Scientific novelty remains unverified.