# Two radial channel blind spots; other channels remain available

Numerical observations, not certified root enclosures or Lean theorems. Pod B completed in 5.640 seconds including cleanup. Together with initial H3: 7.785 wall seconds. Remote outputs downloaded and checksums verified.

The same low-height boxes were subdivided into 16 horizontal tiles per diagonal channel and tested at 100 digits. A 192-sample-per-edge full-box challenge gave winding one in each box; local circles around the found roots also gave winding one. These agree with isolated simple zeros at:

| Source branch, reader side | rho |
|---|---|
| false, false | 0.41975606342742267250 + 6.33368244620312040928 i |
| true, true | 0.92253956862230623509 + 6.87045384057317382058 i |

Both use the actual source polynomial and its prescribed first endpoint subtraction, with unit amplitude. Both are spectral controls, not asserted Xi zeros, and lie below the first cached zeta-zero ordinate 14.13472514. Source and reader Boolean meanings are explicit in moment.py and the protocol.

Fresh root solves at 50/100/160 digits have maximum normalized residuals below 6e-51, 4e-101 and 4.5e-161 respectively. Independently implemented elementary endpoint series at 190 digits reproduce the small residuals at the rounded roots and the nonzero rho+.001 anchors, with anchor disagreement below 2.70e-185. The base-period and retained boundary terms cancel; each term itself is nonzero. No boundary term was dropped. Normalization is M/(2 B(3,w+1)), which has the same zeros throughout these boxes.

Positive salvage: at the false/false zero, the other normalized magnitudes are approximately 818.05, 1186.40 and 0.93786; at the true/true zero they are approximately 0.73454, 1027.84 and 2572.00. The independent supplement confirms all eight channel values at 190 digits, with maximum absolute discrepancy 4.06e-185. It also confirms the true/true source by the corpus's fixed rational defect integral, using two endpoint substitutions at increasing precision (maximum discrepancy 1.32e-191 at the final level). Available channels avoid each individual blind spot in these computations. This does not prove common-zero exclusion or identify a superposed physical source, whose mixed terms would have to be supplied.

Consequence for HB: the unrestricted claim that either individual diagonal radial moment never vanishes anywhere in the critical strip has numerical counterexamples. Its restriction to actual Xi zeros remains unrefuted. The strongest useful survivor is a possible height-restricted or multiple-channel survival statement, not an extinction law. Current source already has existential low/high survival bands for true/true; these observations isolate a finite-height obstruction between such bands. They do not supply the missing complete causal-action identification or selection premise.

Next discriminating work: ask whether a proposed mechanism truly needs strip-wide individual-channel nonvanishing, or whether a height-restricted or multiple-channel statement suffices. Independent fixed rational source quadrature is now complete. Do not enlarge the same zero scan merely to accumulate agreement. All raw rejected searches, contour samples and independent validations are retained. Reproduce: python guard.py challenge.py, using the recorded environment and unchanged copied moment.py.
