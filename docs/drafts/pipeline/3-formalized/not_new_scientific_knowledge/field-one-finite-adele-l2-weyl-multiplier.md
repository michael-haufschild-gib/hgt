# Finite-adele Haar-L² Weyl multiplier

- **ID:** `field-one-finite-adele-l2-weyl-multiplier`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `unit-modulus-l2-multiplier`
- **Statement:** the standard finite-adele Weyl phase acts unitarily on additive Haar
  \(L^2(\mathbb A_f)\), and this action extends the compactly supported locally constant
  Bruhat multiplier exactly.

## Theorem

The compact-open integral subgroup gives local compactness of the additive group
\(\mathbb A_f\). Equip it with its Borel structure and additive Haar measure. For
\(r\in\mathbb A_f\), the phase
\[
  x\longmapsto\psi_f(rx)
\]
is continuous and has norm one. It therefore defines a linear isometric equivalence of
\(L^2(\mathbb A_f)\), with additive composition law.

Every finite Bruhat test is continuous with compact support, hence belongs to Haar \(L^2\).
The embedding \(C_c^{\mathrm{lc}}(\mathbb A_f)\to L^2(\mathbb A_f)\) intertwines the algebraic
and Hilbert-space Weyl multipliers.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneFiniteAdeleL2WeylMultiplier`
- **Core theorems:** `norm_fieldOneFiniteAdeleL2WeylPhase`,
  `fieldOneFiniteAdeleL2WeylUnitary_ae`,
  `fieldOneFiniteAdeleL2WeylUnitary_add_apply`,
  `fieldOneFiniteBruhatToL2_ae`,
  `fieldOneFiniteAdeleL2WeylUnitary_bruhat`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: Borel Haar and unit-phase types identified
- [x] 1 → 2: dependency-closed Haar-\(L^2\) and Bruhat compatibility proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
