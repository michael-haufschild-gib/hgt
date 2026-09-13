# Actual radial source moment: first contour challenge

Numerical experiment; no new Lean proof. Completed on pod A in 2.145 seconds including guard/cleanup, using at most 14 workers and one library thread per worker. All remote output checksums verified after download.

Computed the complete first-subtracted elementary fundamental source moment in all four branch/reader combinations, on 20 rectangles covering .01 <= Re rho <= .99, .1 <= Im rho <= 80. Each rectangle used 24 and 48 samples per edge at 50 digits. The absolutely convergent original-source implementation anchor agreed with the hypergeometric representation to absolute error 8.05e-47.

Two low boxes were unresolved: (false,false) had winding one on both meshes; (true,true) changed from zero to one. The five interior-height Newton seeds located no admitted root. Their failure did not refute the contour evidence. All other sampled boxes had numerical winding zero, with no certified absence claim.

The challenge experiment, on the other pod, subsequently located and validated both low-box roots through subdivision, better seeds, 50/100/160-digit solves, an independent endpoint series and local contours. See the sibling hb-radial-moment-challenge-2026-09-13 report. Original H3 raw output remains unchanged.

Consequence: coarse phase meshes and unsuccessful interior Newton seeds cannot decide radial blind spots. The retained endpoint boundary term must remain part of the source. Whole-action identification, onset, angular nonvanishing, and physical selection are outside this calculation. Source-only cached Lean search was partial/pending; current source additionally supplies existential low/high nonvanishing bands for one channel, not a global strip certificate.

Reproduce with the recorded Python environment: python guard.py experiment.py. PROTOCOL.md freezes objects, controls and interpretation; source-provenance.json records the exact inspected source hashes. The directory's pipeline category does not confer proof status.
