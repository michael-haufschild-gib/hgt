# Route R degree-six Gamma-corona local/global fracture

- **ID:** `route-r-degree-six-gamma-corona-local-global-fracture`
- **Stage:** 3-formalized
- **Formalized companion:** `./route-r-degree-six-gamma-corona-local-global-fracture-formalized.md`
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW EXACT BRIDGE] [NOT RH]`
- **Parents:** `../1-in-progress/route-r-degree-six-bv-green-physical-cyclic-producer.md`,
  `./route-r-degree-six-bv-green-cyclic-reader-wall.md`
- **Statement:** Route R's fixed degree-six BV--Green physical boundary and canonical ordered
  `(2,3)` Gamma/Cartier port satisfy an exact division-free identity; the literal coordinate-local
  source action vanishes in the singular corona, so the remaining comparison is exactly failure
  of the algebraic corona quotient to commute with all-prime globalization.

## Goal

Replace the unstructured equality

```text
R_phys(B_6) = tau_6(B_6)
```

by one strict operator comparison in the already constructed cross-prime singular corona.  The
result must identify actual values, not only equal zero sets, and must keep the source-local action
separate from the physical full-support action.

## Internal and external frontier

`[CORPUS]` The following inputs are unconditional:

1. `tau_6(B_6)=0` for the explicit normalized source reader;
2. `R_phys(B_6)=2 sinh(a_rho log 6)`, where `a_rho=2 Re(rho)-1`;
3. the canonical ordered `(2,3)` Gamma/Cartier port is
   `Gamma_23(rho)=a_rho G_23(rho)c_rho`, with `G_23(rho)>0` and `c_rho!=0`;
4. the cross-prime packet Hilbert space has dense finite arithmetic core `A`, full-support horizon
   `h`, and nonzero algebraic corona class `[h]` in `H/A`.

Closed-ideal Calkin and corona constructions are standard operator theory.  The present quotient is
deliberately different: `A` is dense and not closed, so `H/A` is algebraic and non-Hausdorff.  The
project-specific exact comparison below is not supplied by that literature.  External baseline:

- P. Motakis and D. Puglisi, *The compact operators on c0 as a Calkin algebra*,
  <https://arxiv.org/abs/2403.04137>.
- R. Hagger, M. Lindner, and M. Seidel, *Essential pseudospectra and essential norms of
  band-dominated operators*, <https://arxiv.org/abs/1504.00540>.

## Conjecture / falsification loop

### C19 — Sonin principal-relative trace plus logarithmic Weyl derivation

`[FALSIFIED AS THE PRODUCER]`  The Sonin trace is genuinely cyclic, but the logarithmic Weyl
defect is a noncompact infinite-rank band, not a Schatten-1 relative correction.  It cannot be
identified with the fixed physical boundary by principal-relative cyclicity.

### C20 — literal `(2,3)` source action is coordinate-local

`[PROVED]`  Let `i_0=(2,3)` and `P_i0` be coordinate restriction on the cross-prime packet Hilbert
space.  For every packet `z`, `P_i0 z` has one-point support, hence belongs to the concrete finite
arithmetic source core `A`.  Therefore

```text
pi(P_i0 z)=0 in H/A.                                      (1)
```

Multiplying `P_i0` by any source Gamma coefficient does not change `(1)`.

### C21 — source locality automatically equals physical globalization

`[FALSIFIED]`  The physical action is not coordinate-local.  It is scalar multiplication on the
full-support horizon:

```text
Gamma_global(rho)(c_rho [h])
  = Gamma_23(rho) [h].                                    (2)
```

Since `[h]!=0`, `(1)` and `(2)` agree exactly when `Gamma_23(rho)=0`.  The finite source action
and physical action are two distinct extensions.  Calling them equal is the open theorem.

### C22 — recover globalization by a cofinal sum of local actions

`[FALSIFIED IN THIS CORONA]`  Finite coordinate sums applied to `h` lie in `A` and have zero
corona class, while their Hilbert-space limit is `h` and has nonzero corona class.  Thus the
algebraic quotient map is discontinuous and cannot interchange that cofinal sum with projection.
Any successful all-prime Stokes law needs new source structure beyond continuity, finite-stage
exactness, or countable summation in this quotient.

## Theorem

Put

```text
a_rho = primeDepthBVWoldXiCenteredRate rho,
c_rho = ccmRationalAdelicPrimeXiCartierCoefficient rho,
G_23  = routeRTwoThreeGammaCoorientedGauge rho,
s_6   = routeRDeningerHyperbolicSinc (a_rho * log 6).
```

Then:

1. `G_23>0`, `c_rho!=0`, and `2 log(6) s_6>0`.
2. The exact division-free comparison is

   ```text
   (G_23*c_rho) * (R_phys(B_6) : C)
     = (2*log(6)*s_6 : C) * Gamma_23(rho).                (3)
   ```

3. If `L_rho` is the literal coordinate-local Gamma action on the packet Hilbert space and
   `x_rho=c_rho h`, then

   ```text
   pi(L_rho x_rho)=0.                                     (4)
   ```

4. If `P_rho` is the existing physical scalar Gamma action on the singular corona, then

   ```text
   P_rho(pi x_rho)=Gamma_23(rho)[h].                      (5)
   ```

5. Consequently the following are equivalent:

   ```text
   P_rho(pi x_rho) = pi(L_rho x_rho)
   Gamma_23(rho) = 0
   R_phys(B_6) = tau_6(B_6)
   Re(rho)=1/2.
   ```

Items `(3)`--`(5)` are strict identities.  Only the final equivalence invokes existing exact
zero-set classifications.

## Complete proof

The source reader gives `tau_6(B_6)=0`.  Existing radial comparison gives

```text
R_phys(B_6)=2*sinh(a_rho*log 6).
```

The hyperbolic-sinc identity `x*sinc_h(x)=sinh(x)` changes this to

```text
R_phys(B_6)=2*a_rho*log(6)*s_6.                           (6)
```

The cooriented Gamma theorem gives

```text
Gamma_23(rho)=a_rho*G_23*c_rho.                          (7)
```

Multiplying `(6)` by `G_23*c_rho`, multiplying `(7)` by `2 log(6)s_6`, and commuting scalar
factors proves `(3)` without division.  Positivity of `G_23`, positivity of hyperbolic sinc and
`log(6)>0`, and nonvanishing of the leading Xi jet prove item 1.

For `(4)`, coordinate restriction to `{i_0}` equals the Hilbert realization of the finitely
supported coefficient `single i_0 (x_rho i_0)`.  The finite coefficient realization is the image
of the actual cross-prime arithmetic witness span.  Hence `L_rho x_rho` belongs to `A`, and the
quotient map kills it.

Equation `(5)` is the existing physical action formula.  The horizon class is nonzero, so `(4)`
and `(5)` agree iff `Gamma_23(rho)=0`.  Both multipliers in `(3)` are nonzero, hence this is
equivalent to `R_phys(B_6)=0`.  The source equality `tau_6(B_6)=0` gives the desired reader
equality, and the already proved radial classification gives `Re(rho)=1/2`.

Every dependency is closed on paper.

## Frontier effect

Source-side singular annihilation is now constructed, but it acts locally.  Physical action acts
globally on the retained horizon.  Remaining Route R theorem is no longer “find a cyclic reader”
or “find a singular corona”: prove one coefficient-faithful all-prime comparison intertwines these
two explicit actions.  Finite-stage exactness and topological continuity cannot prove it, because
the singular corona quotient provably fails the required local-to-global interchange.

This does not prove RH.  It removes freedom from the producer and exposes exact operation whose
source derivation is missing.

## Gates

- [x] exact source and physical operations separated
- [x] internal collision and failed-route audit
- [x] external operator-quotient baseline checked
- [x] conjecture/falsification cycles C19--C22
- [x] dependency-closed paper proof
- [x] Lean formalization and umbrella wiring
- [ ] unconditional local/global intertwining
- [ ] RH

## Log

- 2026-08-07 — exact degree-six/Gamma bridge and local/global corona fracture proved on paper.
- 2026-08-07 — Lean module wired; rebuilt `.olean` present and newer than source.
