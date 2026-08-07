# Suzuki--Donoghue spectral-measure connectors

- **Status:** formalized analytic interface
- **Source theorem:**
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/suzuki/suzuki-donoghue-defect-spectral-measure-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueSpectralMeasure.lean`
- **Unconditional:** yes
- **RH:** not assumed and not proved

## Formalized content

Suzuki's canonical Herglotz carrier is exactly the quotient of the parity-selected extension
functions:

```text
m(z)=-i W_1(z)/W_{-1}(z).                                (1)
```

Source parity makes this quotient odd wherever finite.  The scalar Donoghue resolvent kernel has
the exact identities

```text
z+(z^2+1)/(t-z)
  =(tz+1)/(t-z)
  =(1+t^2)/(t-z)-t.                                      (2)
```

Thus a spectral probability `nu` produces Nevanlinna measure `(1+t^2)nu` with no linear term at
infinity.  At a simple boundary point `Theta(x)=1`,

```text
Res_x i(1+Theta)/(1-Theta)=-2i/Theta'(x).                 (3)
```

If `Theta'(x)=i q` with positive boundary phase speed `q`, the residue is `-2/q`; the corresponding
positive Clark/Nevanlinna atom has weight `2/q`.

Lean declarations:

```text
suzukiHerglotz_eq_twoAngleDonoghueQuotient
suzukiHerglotz_neg_of_parity
suzukiDonoghueKernel
suzukiDonoghueKernel_eq_mobius
suzukiDonoghueKernel_eq_nevanlinna
suzukiUpperCayleyInv_residue_at_one
suzukiUpperCayleyInv_phase_residue_at_one
```

## Exact scope

The paper theorem identifies Suzuki's full finite-aperture measure as the spectral probability of
the normalized positive deficiency vector and gives atom weights

```text
(1+x^2)|F(-x)|^2/(||v_+||_T^2 ||v_x||_T^2).              (4)
```

The source Hilbert space, unbounded minimal operator, self-adjoint extension, and spectral
projections do not yet exist in Lean.  Equation `(4)` is therefore not hidden behind an abstract
axiom or wrapper here.  This module formalizes precisely the dependency-closed analytic layer that
will consume those objects once constructed.

## Novelty boundary

Donoghue, Livsic, and Clark theory are classical.  Candidate novelty belongs to the exact
restricted-Weil source identification and weight formula in the Stage 2 card.  This module is its
verified connector, not a claim that generic spectral theory is new.

## Gates

- [x] exact two-angle quotient
- [x] parity oddness
- [x] zero-linear-term kernel decomposition
- [x] simple-pole residue transfer
- [x] reciprocal positive phase-speed law
- [x] exact-file Lean check
- [ ] concrete source operator and spectral projections in Lean
- [ ] cofinal tightness and non-clock theorem
- [ ] Xi divisor identification
- [ ] RH

## Log

- 2026-07-21 — dependency-closed analytic interface formalized and wired into the RH SOTA ledger.
