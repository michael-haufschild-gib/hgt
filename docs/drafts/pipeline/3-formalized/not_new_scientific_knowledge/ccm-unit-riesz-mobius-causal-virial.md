# CCM unit-Riesz Möbius causal virial

- **ID:** `ccm-unit-riesz-mobius-causal-virial`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM, finite exact source algebra
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-markov-virial-landau-law.md`

## Formal theorem surface

Module:

`GaloisForLFunctions/RHTower/CCMUnitRieszMobiusCausalVirial.lean`

For a finite critical Möbius boundary it defines the boundary mass, logarithmic moment, causal
complement, exact step primitive, and causal virial.  Lean proves unconditionally

```text
finiteCriticalMobiusCausalVirial T K
 =1-(1+T)exp(-T)+finiteCriticalMobiusLogMoment K
 =1-(1+T)exp(-T)-finiteCriticalMobiusLogDefect K.
```

Principal declarations:

- `finiteCriticalMobiusCausalVirial_eq_logMoment`;
- `finiteCriticalMobiusCausalVirial_eq_one_sub_logDefect`.

This records the elementary cancellation so it cannot be rediscovered and mislabeled as the RH
advance.  No bound on the logarithmic defect is proved.

## Gates

- [x] finite boundary and logarithmic moment
- [x] finite causal primitive/complement
- [x] exact virial collapse
- [x] source-facing logarithmic-defect convention
- [ ] global Markov convolution theorem
- [ ] source-specific half-unit lower bound
- [ ] RH

