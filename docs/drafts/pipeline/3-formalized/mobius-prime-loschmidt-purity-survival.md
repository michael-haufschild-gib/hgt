# Finite prime Möbius transfer as a Loschmidt amplitude

- **ID:** `mobius-prime-loschmidt-purity-survival`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** standard finite-spectrum quantum dynamics applied to the existing prime source
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeMobiusLoschmidtPurity.lean`
- **Physics source:** G. Styliaris, N. Anand, L. Campos Venuti, and P. Zanardi,
  *Quantum coherence and the localization transition*, Phys. Rev. B **100** (2019), 224204,
  DOI `10.1103/PhysRevB.100.224204`, especially Appendix C.

## Formalized value law

For a finite prime aperture `S` and real `sigma`, the existing normalized signed transfer

```text
L_S(z) = product_(p in S) (1-p^(-sigma) exp(-log(p) z))/(1+p^(-sigma))
```

has the exact squarefree imaginary-time expansion

```text
L_S(i n) = sum_(T subset S) (-1)^|T| P_sigma(T) exp(-i n log product(T)).
```

This is the Loschmidt amplitude of a finite diagonal Hamiltonian with squarefree energy levels
`log product(T)`.  The coefficient law `P_sigma` and its signed square-root amplitude were already
present in `MobiusFiniteSchurTransfer`.

Unique factorization distinguishes the squarefree products.  The in-tree Gelfond--Schneider theorem
also distinguishes their time-one unitary phases: equality of two phases would make a nontrivial
positive rational number raised to `I` algebraic.  The existing finite-exponential-pencil theorem
then gives

```text
Cesaro_n |L_S(i n)|^2
  -> Purity(S,sigma)
   = sum_(T subset S) P_sigma(T)^2
   = product_(p in S) (1+p^(-2 sigma))/(1+p^(-sigma))^2
   > 0.
```

Thus the finite signed prime transfer cannot converge to zero along imaginary integer time by
destructive phase cancellation.

## Direct corpus application

The formal theorem consumes, without a new abstract interface:

1. `finitePrimeSignedSchurTransfer_squarefreeExpansion`,
   `finitePrimeSquarefreeProbability`, and `finitePrimeSquarefreeAmplitude`;
2. `primeSupportProduct_injective`;
3. `algebraicBase_imaginaryNatPower_transcendental`;
4. `tendsto_finiteExponentialPencil_cesaro_norm_sq` and
   `not_tendsto_finiteExponentialPencil_zero`.

The exported theorem certificate is:

- `positiveRational_cpow_I_ne_one`;
- `finitePrimeSquarefreeLoschmidtMode_injective`;
- `finitePrimeSignedSchurTransfer_imaginaryNat_eq_exponentialPencil`;
- `finitePrimeSquarefreeLoschmidtPurity_eq_probability_sq`;
- `finitePrimeSquarefreeLoschmidtPurity_eq_prod`;
- `finitePrimeSquarefreeLoschmidtPurity_pos`;
- `tendsto_finitePrimeSignedSchurTransfer_imaginaryNat_cesaro_norm_sq`;
- `not_tendsto_finitePrimeSignedSchurTransfer_imaginaryNat_zero`.

This is a quantitative cancellation-resistant value law for an existing arithmetic transfer.  It
does not give a lower bound uniform in the aperture and does not prove RH.

## Candidate competition

1. **Quantum dephasing / Schur multiplier.** Rejected.  The paper-level diagonal-Fock card already
   records the abstract Schur-product implication, and the only unconditional concrete
   specialization found here kills all cross-node coupling.
2. **Lee--Yang logarithmic derivative as a passive response.** Deferred.  A useful version needs a
   source-value or cofinal convergence theorem; the finite abstract response alone does not close
   the existing prime--archimedean comparison premise.
3. **Loschmidt purity of the signed prime transfer.** Selected because it is an exact identity for
   an existing source object and directly consumes four existing formal APIs.

## Verification

- `lake build GaloisForLFunctions.RHTower.PrimeMobiusLoschmidtPurity`: passed, 8665 jobs;
- axiom audit of the six principal theorems: only `propext`, `Classical.choice`, and `Quot.sound`;
- `python3 scripts/formal_tools.py lint`: passed;
- `GaloisForLFunctions.RHTower` umbrella reached 10102/10103 modules, then failed in the unrelated
  dirty file `XiCTaylorThetaTailPhaseAdaptedProuhetPacket.lean`; the new module and its dependency
  cone built successfully.

## Gates

- [x] formalize the squarefree phase and coefficient normal form
- [x] prove unit modulus and phase injectivity
- [x] identify `L_S(i n)` with the finite exponential pencil
- [x] prove the exact Cesaro purity limit
- [x] prove the independent-prime purity product
- [x] prove non-decay along imaginary integer time
- [x] run axiom, target-build, and lint checks
- [ ] uniform-in-aperture purity lower bound or cofinal survival law
- [ ] RH
