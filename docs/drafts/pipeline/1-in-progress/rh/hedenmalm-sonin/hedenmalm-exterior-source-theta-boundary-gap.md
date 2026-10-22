# P-G156: Exterior source / theta boundary gap

- **Stage:** `1-in-progress`
- **Route:** P, coefficient-faithful exterior source
- **Status:** paper proof and Lean formalization complete; source neutralization remains open

## Conjecture loop

### C1 — bound four Lagrange contours separately

**Failed as route architecture.** Finite interpolation gives exact source contours but no
packet-independent boundary norm. Separate sup-norm estimates pay the conditioning of arbitrary
finite Xi nodes and ignore exterior cancellation.

### C2 — replace interpolation by a holomorphic unit clock

**Failed.** The bounded clock must depend only on one real spectral coordinate. A nonconstant
holomorphic function cannot have unit modulus throughout an open strip; raw holomorphic
translation clocks recover the transverse Cartan amplification that previously made Cesaro modes
diverge.

### C3 — regard contour growth as the missing producer

**Rejected as too low-level.** The corpus already localizes Route P's source obstruction through
the exact theta Green-square law

```text
G B² = B* G B + i R₂ B.
```

Positive bulk is complete. Only the oriented rank-two boundary current remains. Reflection-pair
cancellation and squaring kill its sign without forcing fibrewise neutrality.

### C4 — identify the exterior quantum with nonneutral theta boundary

**Proved.** For a finite packet `S`, fixed center `t`, and a retained multiplicity copy `q`, let

```text
E(S,t) = fixedPacketEnergy(S,1,t) + fixedPacketEnergy(S,1,t-1).
```

Analytic multiplicity is positive, so the complete packet energy dominates the local
fixed-center energy at `q.1`. If the actual theta rank-two boundary flux at `q` is nonzero, its
centered spectral point is off the real axis. The fixed-center exterior quantum then gives

```text
4 * (96/145)^2 <= localFixedCenterEnergy(q,t) <= E(S,t)
```

whenever `|height(q)-t|<=1/2`. Conversely, any strict subquantum bound on `E(S,t)` forces the
same-fibre theta boundary flux to vanish.

For an admissible reflection-closed Xi rectangle, the coefficient-faithful four-contour Cesaro
sequence converges exactly to `E(S,t)`. Hence a nonneutral theta fibre forces a literal
prime--Gamma source-contour limit above the same uniform quantum.

## New knowledge

Route P's new four-leg contour and older theta Green-square operator are two presentations of one
obstruction. Polynomial interpolation growth is not the mathematical core. The missing theorem
is source-side, same-oriented-fibre neutralization of `i R₂ B` before reflection pairing or
positive squaring. Any proposed contour estimate that does not control this current cannot close
RH; any strict subquantum estimate that does control it automatically neutralizes the current.

This is stronger than another RH-equivalent zero-side predicate: it gives a quantitative map from
one concrete source operator current to one concrete four-contour source limit, including analytic
multiplicity and a fixed gap.

## Literature audit

Hedenmalm's 2026 preprint constructs the theta differential-operator pair and isolates
self-adjointness as the missing spectral mechanism, but does not contain this prime--Gamma
four-contour exteriorization or the uniform boundary-current gap:
<https://arxiv.org/abs/2606.17494>. Classical Weil positivity supplies RH criteria, not this
source-to-source quantitative bridge. No matching theorem was found in the checked primary
literature.

## Lean

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmExteriorSourceThetaBoundaryGap.lean`

- [x] multiplicity-square domination
- [x] nonneutral boundary current implies exterior quantum lower bound
- [x] subquantum packet bound implies same-fibre boundary neutrality
- [x] coefficient-faithful source Cesaro landing plus boundary-current quantum
- [x] direct `lake env lean` check
- [x] targeted final module build (`13013/13013`)
- [x] standard-axiom audit (`[propext, Classical.choice, Quot.sound]`)
- [x] umbrella import

## Remaining hard core

Prove same-fibre neutrality of theta rank-two boundary current from completed Euler--Gamma source
orientation, or equivalently prove a strict subquantum estimate for coefficient-faithful source
Cesaro packets. Reflected sums, ungraded `B²` traces, arbitrary interpolation, and generic positive
bulk estimates are formally inadequate.
