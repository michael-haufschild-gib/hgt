# Arithmetic controls for inverse-value transport

The two carriers are the primitive real Dirichlet L-functions with characters chi_4=(0,1,0,−1) and chi_5=(0,1,−1,−1,1). Their Hurwitz-zeta expressions and analytic derivatives were evaluated directly. Previously checked completion, parity and root-number data were retained; this experiment used five cached positive roots and eight trivial roots per carrier. Those cached roots are not a newly certified complete census.

All 130 prescribed 50-digit paths completed. The large target circle w(u)=1−exp(2πiu) sent positive root labels 2–5 to their predecessors for both carriers. The first positive root reached −1 for conductor 4 and 0 for conductor 5. Those trivial roots in turn reached the corresponding first negative-height root. The other tested trivial roots were fixed. The smaller target circle fixed all five tested positive roots of conductor 4, but exchanged labels 4 and 5 for conductor 5.

Five selected paths survived 100/160-digit repetition, smaller steps and independent Euler–Maclaurin Hurwitz sums. These checks support the stated selected connections; they do not certify all 130 paths.

For the larger RH landscape, shared predecessor transport weakens its interpretation as a property peculiar to zeta. The low-height attachments and small-loop exchanges nevertheless differ between the carriers. A useful proof mechanism would need the additional arithmetic structure that makes the zero fibre rigid, not merely a pattern of inverse transport shared by several functions. These controls neither inherit HB physics nor prove their generalized RH statements.

Positive salvage: distinguish broadly shared transport from carrier-dependent branch attachments. The next discriminating question concerns finite versus escaping approaches to the value 1, and whether the critical-value graph explains their distribution.

Reproduce with `python guard.py experiment.py`. Literal characters, completion checks, cached roots, full paths, failures, environment and original checksums are included. No Lean builds or new-theorem claim.
