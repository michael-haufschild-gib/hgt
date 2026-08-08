# Four-shadow zeta source boundary-value problem

- **ID:** `ngd-four-shadow-zeta-source-boundary-value`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE / FIELD CONSTRUCTION TARGET
- **Status:** `[OPEN CORE] [SOURCE-PURE REQUIRED] [CIRCULARITY NOT EXCLUDED] [NOT RH]`
  `[NO LEAN WRITTEN]`
- **Statement:** Extend the flat Dirichlet Maurer--Cartan source by predeclared relation/capacity and
  normalized Gamma/theta data so one source charge has faithful Route-L, Route-E, Mass, and odd
  Weil pushforwards before Xi-zero specialization.

## Exact starting point

The Pipeline-2 cards prove that

\[
 \Theta_E=M*\delta E=\Lambda
\]

has exact flat Route-L, primitive-prime Mass, reflection-odd Weil, and Stokes-normal shadows. They
also prove two independence results:

1. the arithmetic differential algebra does not select Route-E's labeled relation, conductance,
   Hall allocation, capacity, or directed seam;
2. it does not normalize the full archimedean Gamma/theta completion.

These are missing source coordinates, not reasons to retreat into either route.

## Conjectural source field

Construct, before divisor specialization,

\[
 \mathscr Z_{\rm src}
 = (\mathcal A,E,M,\delta,\Theta_E;
    R_E,\mathcal C_E;
    G_\infty,\nu_\infty;
    \star,\text{ports}),
 \tag{1}
\]

where:

- `R_E` is a literal labeled incidence/relation object;
- `C_E` is its source capacity/order law;
- `G_infty` is a Gamma/theta source module;
- `nu_infty` is a source normalization not invariant under arbitrary symmetric entire factors;
- `star` and marked ports retain unsquared reflection orientation.

There should be source-witnessed pushforwards

\[
 \theta_\zeta\longmapsto
 \bigl(\Omega_{\mu,\Gamma},
       J_E^{\rm residual},
       J_M^{\rm Abel/out},
       q_W^-\bigr)
 \tag{2}
\]

with coefficient fidelity on declared quotients, label preservation, strict admission, odd
orientation, and cofinal survival.

## Why this is a boundary-value problem

Equation `(2)` is not selection. NGD must additionally specify a presentation-invariant
connection, Einstein contraction `E_NGD`, transgression `tau`, and boundary data. The RH-bearing
problem is existence and uniqueness of a global source-witness section with marked nonerasure.
Neither a positive norm nor vanishing of an already specialized defect may be inserted as a source
axiom.

## Conjecture/proof/fail loops

### Loop 1 — Dirichlet current alone selects all four shadows

**Failed.** Parallel labeled Route-E flows have identical arithmetic current and boundary.
Symmetric entire multipliers change Gamma torque while preserving the Dirichlet algebra.

**Survivor.** Two extra source coordinates in `(1)` are logically necessary.

### Loop 2 — Route E and Mass are one current

**Failed at present.** They share oriented chain degree, but the exact bridge covers only symmetric
opposite-sign incidence. Physical Route-E direction/capacity and the full Mass outgoing class are
not identified.

**Next test.** Construct one literal source relation whose two pushforwards preserve labels and
whose relative filling profiles are finite in both charts. A capacity-profile mismatch is a
falsifier, not a technical nuisance.

### Loop 3 — reflection symmetry normalizes Gamma completion

**Failed.** `exp(c(s-1/2)^2)` preserves reflection and reality while changing logarithmic torque.

**Next test.** Derive `nu_infty` from the literal theta heat equation, local archimedean asymptotic,
or a source boundary condition that excludes the whole multiplier family without using Xi zeros.

### Loop 4 — four faithful pushforwards solve RH

**Failed as an inference.** Representation is already largely complete. A global source section and
nonerasing boundary law remain independent.

**Survivor.** `(2)` is a necessary field-construction theorem, not the final selection theorem.

## Falsifiers

1. Prove source-label/capacity requirements for `J_E` and `J_M` incompatible.
2. Prove every source-natural Gamma normalization retains a nontrivial symmetric-entire torsor.
3. Produce source-preserving reducer presentations with different localized curvature classes.
4. Construct a nonzero declared source charge erased by every proposed pushforward despite the
   claimed conservative pairing.

Any item falsifies the current four-shadow formulation and forces a higher source field.

## Gates

- [x] flat arithmetic seed constructed
- [x] exact Route-L/Mass/Weil/Stokes local shadows proved
- [x] Route-E and Gamma nonselection laws proved
- [ ] literal `R_E` and `C_E` constructed from source
- [ ] literal normalized `G_infty` constructed from source
- [ ] four pushforwards typed in one source-witness bifibration
- [ ] presentation invariance proved
- [ ] jointly conservative charge pairing proved
- [ ] RH boundary-value problem shown noncircular

## Lean-return note

No Lean code should be written until `(1)`--`(2)` are dependency-closed on paper. Exact finite
subtheorems already in Pipeline 2 can later be formalized separately.

## Log

- 2026-08-08 — created after exact three-local-shadow theorem and two source nonselection laws.
