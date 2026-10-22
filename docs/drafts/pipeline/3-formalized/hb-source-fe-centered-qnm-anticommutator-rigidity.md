# HB source-FE centered-QNM anticommutator rigidity

- **ID:** HC57
- **Stage:** 3-formalized
- **Type:** THEOREM / REFLECTION-COUPLED CLOCK WARD / HARD FRONTIER
- **Source:** HC56 QNM-generator locality no-go; literal source-FE packet involution; centered Xi
  spectral coordinate
- **Formal module:**
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity`
- **Result:** The anticommutator of literal anti-linear source-FE transport with the centered BM QNM
  generator is the exact diagonal-reflected Xi-tilt charge. Its global vanishing is equivalent to
  RH.

## Proven theorem

Subtract the fixed overtone/redshift offset from the literal BM QNM frequency:

```text
Omega_n(q) = omega_n(q) - (i/4 - i d_n) = xiSpectralPoint(q)/2.
```

Let `Gbar_n e_q = Omega_n(q)e_q` and let `T_FE` be literal anti-linear source-FE packet transport.
Lean proves:

1. `Omega_n(q) = xiSpectralPoint(q)/2`, so centering removes every overtone dependence.
2. FE reflection negates `Omega_n`.
3. `conj(Omega_n(q)) + Omega_n(Rq) = i * (Re(q)-1/2)`.
4. The source-FE cocycle is nowhere zero, derived from its already-proved involutive law.
5. On a basis packet,

```text
(T_FE Gbar_n + Gbar_n T_FE)(c e_q)
  = i * (Re(q)-1/2) * kappa(q) * conj(c) * e_Rq.
```

6. For every finite packet `x`, the coefficient at `r` is exactly

```text
i * (Re(Rr)-1/2) * kappa(Rr) * conj(x(Rr)).
```

7. The defect vanishes on the unit packet `e_q` iff `Re(q)=1/2`.
8. Global defect vanishing for all finite packets is equivalent to RH.
9. Equivalently, `T_FE Gbar_n = -Gbar_n T_FE` on every packet iff RH.

## Exact new insight

HC56 showed ordinary stationary/Noether time conservation supplies only spectral-fibre locality.
HC57 identifies the missing reflection-coupled clock charge exactly: anti-linearity converts the
FE-odd centered frequency into the transverse Xi tilt `i(Re(q)-1/2)`. The cocycle cannot erase that
charge because involutivity forces it to be nonzero. Thus the remaining HB producer is no longer an
unspecified covariance principle: it is derivation of this exact anticommutator's vanishing from
augmented Einstein/Teukolsky source dynamics.

## Hostile checks discharged

- Centered the literal BM QNM frequency by its actual fixed overtone/redshift term.
- Preserved anti-linearity of source-FE transport.
- Tracked reflected support and cocycle coefficient exactly.
- Derived cocycle nonvanishing rather than assuming it.
- Proved arbitrary finite-packet coefficient formula, not only basis behavior.
- Proved global equivalence without assuming existence of an off-line zero.
- Used no hypotheses, new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations.

## Novelty boundary as of 2026-08-28

Required corpus searches found source-FE packet involutivity, centered-coordinate reflection laws,
HC56 time-generator locality, and unrelated centered-clock countertransports, but no anticommutator
between literal BM source-FE transport and centered QNM generator. Primary literature on Kerr QNM
currents and `t-phi` reflection (arXiv:2210.15935) gives conserved bilinear forms and
different-frequency orthogonality, but targeted searches found no Xi-source cocycle
anticommutator or RH-equivalent clock-defect formula. Search is bounded, not exhaustive.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity.lean`
  — passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity`
  — passed (`11925/11925`).
- `#print axioms` on all 11 public theorems — only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint reports no HC57 issue; repository-wide failure remains the pre-existing set of 18
  unrelated umbrella-reachability errors.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed proof established
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC56 proved stationary generator symmetry supplies locality but not
  source-FE Ward covariance.
- 2026-08-28 — Proved exact basis and arbitrary-packet anticommutator formulas, cocycle
  nonvanishing, basis critical-line equivalence, and global RH equivalence in Lean.
- 2026-08-28 — Passed direct Lean, target-only build, 11-theorem axiom audit, lint scope check, and
  umbrella audit; promoted to formalized.
