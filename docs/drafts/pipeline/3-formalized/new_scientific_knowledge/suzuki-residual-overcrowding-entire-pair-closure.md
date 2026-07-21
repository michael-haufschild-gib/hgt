# Formal endpoint core of Suzuki residual-overcrowding closure

- **ID:** `suzuki-residual-overcrowding-entire-pair-closure-formal`
- **Status:** formalized and audited
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-residual-overcrowding-entire-pair-closure.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`
- **RH used:** no
- **Computation used:** no

## Formalized content

The paper theorem proves that interior residual is escaped-label Clark overcrowding and that
common-gauge entire-pair normality eliminates it.  Its new dependency-closed endpoint connector is
formalized in the existing compactified phase module:

```text
tendsto_suzukiDonoghueKernel_atTop
tendsto_suzukiDonoghueKernel_atBot
```

For every complex `z`, both projective real ends of

```text
K_z(t)=z+(z²+1)/(t-z)
```

converge to `z`.  Hence mass escaping through either compactified endpoint contributes the same
linear Nevanlinna kernel.  Combined with Suzuki evenness, this is the exact analytic connector
behind the paper identity “endpoint residual mass = linear Herglotz coefficient.”

## Boundary of the formal layer

The full escaped-label tail identity uses weak convergence of the aperture-indexed concrete Clark
probabilities, which are not yet constructed in Lean.  Local zero-count closure uses Rouche on the
source characteristic family; the repository already contains locally uniform zero-transfer
machinery, but adding an abstract wrapper would not formalize Suzuki's missing common-gauge pair
normality.  Those source and measure-topology statements therefore remain paper-level.

## Audit

- [x] direct `lake env lean GaloisForLFunctions/RHTower/SuzukiCompactifiedPhaseProfile.lean`
- [x] exact `lake build GaloisForLFunctions.RHTower.SuzukiCompactifiedPhaseProfile`
- [x] SOTA import source check
- [x] `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- [x] global formal lint
- [x] `git diff --check`
