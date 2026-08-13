# Hedenmalm Ward-defect transverse Green source

- **ID:** `P-G149`
- **Stage:** `1-in-progress`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
- **Parents:** `P-G124`, `P-G148`
- **Module:** `formal/GaloisForLFunctions/RHTower/HedenmalmWardDefectTransverseGreenSource.lean`

## Conjecture loop

1. `[FAILED]` Extend the inverse-square five-shift coefficient as a bounded continuous scalar at
   the critical boundary. P-G148 boundary rigidity forbids this, and any nonzero continuous
   tangent extension would charge the infinitely populated critical-line divisor.
2. `[PIVOT]` Move the singularity into the inverse graph of P-G124's source-derived positive Ward
   defect. Its mass and Euclidean energy are defined before the transverse coordinate is divided.
3. `[PROVED]` For every Xi multiplicity copy `q`, with `z=xiSpectralPoint(q)`, exact Ward geometry
   gives

   ```text
   WardEnergy(q) = 2 Im(z)^2 WardMass(q)^2.
   ```

4. `[PROVED]` Define source Green weight without spectral distance,

   ```text
   G_W(q) = 2 WardMass(q)^2 / WardEnergy(q).
   ```

   Lean's totalized inverse and strict positivity of Ward mass yield the unconditional identity

   ```text
   G_W(q) = Im(z)^(-2).
   ```

   Thus `G_W=0` precisely on the critical line, is positive off it, and obeys the inverse graph
   law `G_W * WardEnergy = 2 WardMass^2` off the kernel.
5. `[PROVED]` Replacing P-G148's coordinate inverse square by `G_W` gives exactly the same
   critical-feature five-shift current. Every strict-right Xi copy therefore retains nearest-
   integer source charge at least `64/2025`.

## New knowledge

The singular transverse normalization is not an external scalar counterterm. It is the Green
inverse of the positive Euclidean energy hidden by same-fibre Ward cancellation. Repeated Route-P
realification, Krein, and inverse-square obstructions are one mechanism: signed Ward conservation
creates a positive defect with a critical-line kernel, and the required separator lives on that
defect's unbounded inverse graph.

This closes source origin and kernel classification of the singular factor. It does not give the
remaining arithmetic trace ceiling. Next producer must estimate this Ward-Green graph in the
height-local critical-feature frame; replacing it by a bounded scalar destroys the exact inverse
law.

## Gates

- [x] bounded tangent-extension failure audited
- [x] exact Ward energy factorization
- [x] source Green inverse identity
- [x] inverse graph law and kernel classification
- [x] exact P-G148 current realization
- [x] universal Xi-copy quantum retained
- [x] direct Lean check
- [x] exact module build
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] arithmetic Ward-Green trace ceiling
- [ ] unconditional RH
