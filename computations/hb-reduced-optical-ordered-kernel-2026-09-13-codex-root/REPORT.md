# Reduced optical ordered kernel: critical line without arithmetic heights

## Result

The exact scalar coefficient in equations (13)-(14) of the current two-sided source-current reduction does **not** vanish through the optical interior at actual zeta zeros. Across zeros 1-128 and 2,048 interior `(L,x)` points per parameter, its median relative ordered-branch mismatch on `Re rho=1/2` was `0.709166`; no sampled interior point was below `1e-10`. Best value was `2.0882538248e-7`, at zero 95, `L=37.6976094`, `x=0.578125`; 140-digit recomputation at the exact zeta ordinate confirmed it.

The geometry is more structured than generic non-cancellation:

- Complementary exchange `rho -> 1-rho` makes the coefficient antisymmetric to 140-digit accuracy. On the critical line it is purely imaginary.
- 4,093/4,096 broad complex root searches converged. Among 2,162 roots deduplicated by optical point, 2,150 lay on `Re rho=1/2` within `3.46e-77`. Twelve off-line roots were found, mostly on the real axis plus one validated pair represented by `rho=2.29458570748657+2.92469607010442i`; none survived other optical points.
- The only root persistent across all nine independent cross-sections was the forced self-complementary point `rho=1/2` (`delta=0`), which is not a nontrivial Xi zero.
- At `x=0`, `d=L-1` gives `q_plus=q_minus=L`, so every primitive difference vanishes identically. This is a moving-characteristic endpoint identity, not extinction.
- Removing the onset row barely changed median mismatch (`0.709166` complete versus `0.706474`); retaining either primitive face alone gave `0.709672`/`0.709686`. Endpoint subtraction creates sharp local near-cancellations—the best complete value was about 3,180 times smaller than either face-only best—but not global vanishing.

Actual zeta heights have no detected special alignment with the moving critical-line root families. For zeros 1-256, actual median `log10(best residual)=-3.08394`, with 28 hits below `1e-4`, one below `1e-6`, and none below `1e-8`. Thirty-two controls jittered each height inside its local zeta-spacing cell. Empirical one-sided ranks were `p=0.818` for median best residual and `p=0.242` for the `1e-6` hit count. Thus the near-hit at zero 95 is consistent with optical/root-grid multiplicity, not arithmetic selection.

## Big picture

This source layer manufactures an RH-like **axis** but not an RH-like **spectrum**. Complementary branch symmetry fixes `Re rho=1/2`, forces a single phase there, and makes cross-section-specific zeros abundant. Their heights drift with optical geometry and do not recognize zeta ordinates. Critical-line location alone is therefore cheap in this landscape: many non-arithmetic response functions inherit it from the same involution.

For HB Identification, boundary assembly is consequential—subtracting two individually ordinary faces creates much sharper cancellations—but the retained reduced bulk remains nonzero. A complete action comparison cannot omit moving-characteristic, compact-onset, lift/contact, angular Green, SS/SV/VV, or terminal faces.

For HB Selection, the pointwise reduced radial source is falsified as a standalone selector. It neither vanishes at actual Xi parameters nor has a nonzero common root across cross-sections. Its positive residue is a local critical-line confinement mechanism: almost every nonreal intrinsic root found is on the line.

For RH, viable HB proof space narrows to a **global coherence mechanism**. Arithmetic information must synchronize the moving optical zero families through the literal angular modular source and remaining physical faces, or prove the complete diagnostic is a nonzero transfer of the original Xi occurrence. A route relying only on complementary symmetry, pure-imaginary phase, or one optical-section zero cannot distinguish zeta from density-matched heights and cannot prove RH. Conversely, a complete all-face computation that stays nonzero at actual critical Xi samples would falsify this extinction route, not RH itself.

## Method and validation

Protocol froze four hypotheses and mechanically applied all 24 scientific-method attacks before outcomes. Tests included branch splitting, onset/endpoint ablations, complementary reversal, small/extreme/boundary cases, inverse roots, off-axis controls, and density-matched height controls. Computation used the corpus formulas directly; no angular eigenfunction or fitted physical response was introduced.

Pod 1 evaluated 5,242,880 landscape points plus 17,301,504 actual/control height points. Pod 2 ran 576 zeta-seeded inverse attempts, 4,096 broad-seed attempts at 70 digits, and 140-digit independent challenges. Exact-zero generation used `mpmath.zetazero`. Double-complex sweeps were challenged with independent arbitrary precision. Formula signs and endpoint orientation follow the current corpus card; this is not a Lean proof or interval certificate.

Repository revision: `9d774a1ea257311ad02f21d521ec31441b980657`.

## Next experiment forced by result

Compute the literal angular/current completion attached to this coefficient, not another radial statistic: pair `R M_Z Q` with the original modular source and add compact onset, lift/contact, characteristic and terminal terms on identical finite domains. Test whether these terms synchronize the moving critical-line zeros at actual Xi heights. This is the discriminating boundary between a symmetry-only landscape and an arithmetic HB selector.
