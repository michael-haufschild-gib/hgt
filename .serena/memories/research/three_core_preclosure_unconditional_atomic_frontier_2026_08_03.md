# Three-core preclosure/unconditional/atomic frontier (2026-08-03)

Requested chain: global essential edge via preclosure Wold–Gamma/BV extension; nonseparable beyond-l1 cancellation; divisor-independent atomic positive descent/non-erasure.

Closed facts:
- Local essential edge is Lean-proved: `tendsto_primeFirstTrace_anisotropicEssentialGraph`.
- All ordinary closure/rigging escapes are Lean-excluded: `primeFirstTraceClock_completeNoEscapeUniversality`.
- Global atomic non-erasure is Lean-proved: `reflectedGaussian_globalAtomicNonErasure`.
- Covariant centered-flow capacity is Lean-proved: `xiCenteredFlowConservedCapacity_eq_multiplicityMass`; static capacity and global countercharacter triviality are exactly RH.

New result:
- `formal/GaloisForLFunctions/RHTower/GammaSignedUnconditionalOrbitNoShorting.lean`, wired in `RHTower.lean`.
- Canonical cross-prime/depth product >= 6, so `sinh(frequency)>=35/12>1`.
- If actual scalar Gamma orbit is unconditionally summable at z=1 and vanishes along all imaginary modular displacements, coefficients vanish. Thus an unordered scalar `HasSum` cannot be a genuinely beyond-l1 cancellation; scalar unconditional summability forces physical amplitude l1 and existing Bohr uniqueness applies.
- Card: `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/gamma-signed-unconditional-orbit-no-shorting.md`.
- Verification: direct `lake env lean`, formal lint, `LAKE_JOBS=1 lake build GaloisForLFunctions.RHTower.GammaSignedUnconditionalOrbitNoShorting`; axiom audit only propext/Classical.choice/Quot.sound. No stale Lean processes.

Exact surviving open cores:
1. Strict squarefree preclosure comparison from Wold–Gamma/BV essential edge to relative determinant/Contou–Carrere–Meyer extension and literal Gamma/co-Poisson/Sonin boundary.
2. Nonscalar relative/distribution-valued or divisor-coupled arithmetic annihilation before frequency separation. Conditional enumeration requires an independent source order law and is not unordered/divisor-independent.
3. Source-first triviality of horizontal prime-tail modular cocycle; this is RH-equivalent. Non-erasure and covariant descent are no longer open.

Updated docs: active `riemann-arithmetic-conormal-socle-gauge-law.md` three-core audit and `rh-current-frontier-map.md` unordered scalar closure.