# HB source-FE linear/anti-linear reflection coherence

- **ID:** HC59
- **Stage:** 3-formalized
- **Type:** THEOREM / SEMILINEAR REFLECTION CLASSIFICATION / HARD FRONTIER
- **Source:** HC57 clock anticommutator; HC58 physical source transduction; complex-linear Kerr
  `t-phi` reflection current algebra
- **Formal module:**
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence`
- **Result:** Complex-linear and literal anti-linear source-FE reflections have complementary
  defects. Simultaneous source reflection, involution, and centered-clock oddness is equivalent to
  RH in either realization.

## Proven theorem

For literal source cocycle `kappa(q)`, define complex-linear transport

```text
L_kappa(x)(r) = kappa(Rr) * x(Rr),
```

beside literal anti-linear transport

```text
T_kappa(x)(r) = kappa(Rr) * conj(x(Rr)).
```

Lean proves:

1. `L_kappa` is a genuine complex-linear map with exact basis and coefficient formulas.
2. `L_kappa Gbar_n = -Gbar_n L_kappa` on every finite packet unconditionally.
3. `L_kappa^2(x)(q) = kappa(Rq) kappa(q) x(q)`.
4. `kappa(Rq) kappa(q)=1` iff `Re(q)=1/2`.
5. `L_kappa^2(e_q)=e_q` iff `Re(q)=1/2`.
6. Global involutivity of `L_kappa` is equivalent to RH.
7. `L_kappa(i e_q) != T_kappa(i e_q)` for every Xi copy, so the maps cannot be silently
   identified.
8. Full involutive/clock-odd coherence for either `L_kappa` or `T_kappa` is equivalent to RH.
9. The two coherence predicates are equivalent even though the transports differ as maps.

## Exact new insight

The complex-linear `t-phi` reflection algebra used by conserved complex-bilinear QNM currents does
not provide literal source-FE reflection for free. Complex-linearity makes centered-clock
anticommutation automatic but leaves the unconjugated cocycle phase in the square. Anti-linearity
cancels that phase and makes the literal transport involutive, but then clock anticommutation leaves
the HC57 transverse charge. Off the critical wall one can retain either unconditional involution or
unconditional clock oddness, not both. The missing HB producer is therefore semilinear reflection
coherence, not ordinary current conservation.

## Hostile checks discharged

- Retained literal source cocycle and changed only coefficient semilinearity.
- Constructed `L_kappa` as a Lean complex-linear map.
- Proved arbitrary-packet anticommutation.
- Derived involution failure from exact anti-linear cocycle law plus cocycle reality classification.
- Proved pointwise and global converses.
- Exhibited concrete imaginary-packet separation.
- Added no hypotheses or axioms.

## Novelty boundary as of 2026-08-28

Required corpus searches found HC57 anti-linear clock defect, cocycle reality iff critical line,
source cocycle involutivity, and generic linear-reflection algebra, but no linearization of literal
HB source-FE transport or complementary involution/anticommutation classification. Green et al.
(arXiv:2210.15935) construct a complex-bilinear conserved QNM form using `t-phi` reflection and
state complex-linearity plus time-generator symmetry; targeted primary-source searches found no
comparison with an anti-linear zeta functional-equation source cocycle or RH coherence theorem.
Search is bounded, not exhaustive.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence.lean`
  — passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFELinearAntilinearClockReflectionCoherence`
  — passed (`12024/12024`).
- `#print axioms` on all 11 public theorems — only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint reports no HC59 issue; repository-wide failure remains 18 pre-existing unrelated
  umbrella-reachability errors.
- Module wired into `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof established
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC58 made clock defect a physical nonlinear source observable and
  conserved-current search exposed complex-linear versus anti-linear reflection mismatch.
- 2026-08-28 — Proved exact linear transport, unconditional clock oddness, square formula,
  pointwise/global involution classification, imaginary-packet separation, and both coherence
  equivalences in Lean.
- 2026-08-28 — Passed direct Lean, target-only build, 11-theorem axiom audit, lint scope check, and
  umbrella audit; promoted to formalized.
