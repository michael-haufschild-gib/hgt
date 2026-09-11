# Route L: fixed-six boundary readout of the complete source tail

- **ID:** L-C27
- **Date:** 2026-09-11
- **Stage:** 3-formalized; targeted build, complete axiom audit and global lint passed
- **Type:** THEOREM (Lean); 29 theorems checked and axiom-audited
- **Module:** `GaloisForLFunctions.RHTower.DeningerGammaSixFixedDilationTailReader`
- **Source:** [source-selected completion attack](../1-in-progress/route-l-source-selected-completion-attack.md), C27
- **Statement:** The actual complete integral correction, cut off in its original integer coordinate, has an explicit nonzero normalized second boundary variation at the fixed dilation six. Every finite diagonal repair has the same eventual normalized readout.
- **RH status:** unproved; comparison with the fixed physical reader at the original horizontal anchor is still missing.

## Exact mathematical target

Retain the source and admitted domain of C24--C26. On the spectral
diagonal put `c=XiC^(k)(w)*XiC^(l)(w)`,
`s=1/2+i*w`, `|Im(w)|<1`, and `Re(s)>1/3`. Let
`R=T-c*Q` be the correction of the actual complete integral operator.
No leading--tail cross term is removed from `R`.

Let `E_M` be the original coordinate projection onto `a>=6^M` in the
ordinary-integer endomorphism algebra. The cutoff operator is `E_M*R`,
defined before its diagonal is read. For `M>=3`, define its actual
second boundary coefficient at dilation six by

`J_M = lim_(epsilon->0+) D_epsilon(6,E_M*R)/epsilon^2`.

Every positive Abel parameter is admitted. The preceding second-boundary
theorem identifies this limit, without assuming its existence or value,
as `log(6)*sum_(a>=6^M, 6 divides a) r_a`.

Write `C_m=M_6(m,w)^2-1` for the complete tensor multiplier and
`N_m=((successor(6)/6):Complex)^(m*s)` for its already fixed spectral
normalizer. Put `q=N_1^(-1)`, so `|q|<1`. The proved limit is

`N_M*J_M -> 2*mu(successor(6))*c*(log(6))^2/[6*(1-q)]`.

The right side is nonzero whenever `c!=0`. Thus every sufficiently late
cutoff has nonzero second boundary coefficient at the same dilation six.
The starting cutoff may depend on the source. This is stronger than
existence of a varying detecting dilation, but is not a statement that
the uncut fixed-six coefficient is always nonzero.

## Dependency-closed paper proof

1. Restore the exact offset `a=n+216` in C26's literal remainder identity.
   The Fourier--Laplace formula, actual half-density square, and flattening
   identity give `r_a=c*C_m/a` whenever
   `6^m<=a<6^(m+1)`, `m>=3`. All three tensor remainder contributions
   remain in `C_m`. The source supplies absolute summability of `r`.
2. The divisible part of this shell has harmonic mass
   `h_(m-1)=(1/6)*sum_(j=6^(m-1)..6^m-1) 1/j`.
   This follows from the exact bijection `a=6*j`, including both interval
   endpoints. The current harmonic-number limit `H_n-log(n+1)->gamma`
   implies `h_m->log(6)/6`.
3. Absolute summability permits regrouping the complete source tail by
   its literal shell-depth fibers. Each fiber is the existing finite
   integer shell. The exact cutoff condition is `M<=m`. Therefore
   `J_M=log(6)*c*sum_(j>=0) C_(M+j)*h_(M+j-1)`.
   This equality connects the sum to `E_M*R`; it is not an assigned
   value of an inadmissible integral or an alternative diagonal.
4. C23 proves `N_m*C_m->2*mu(successor(6))`. The normalizer has the exact
   power law `N_m=N_1^m`, hence `q^j*N_(M+j)=N_M`. Its base is greater
   than one and `Re(s)>0`, proving `|q|<1` directly.
5. Put `b_m=N_m*C_m*h_(m-1)`. The two proved limits give
   `b_m->2*mu(successor(6))*log(6)/6`. A convergent complex sequence is
   bounded. Consequently `|q^j*b_(M+j)|<=B*|q|^j` for every `M,j`,
   with a summable geometric majorant. Filter-level Tannery yields
   `sum_j q^j*b_(M+j)->[2*mu(successor(6))*log(6)/6]/(1-q)`.
   The exact power law identifies this sum with the normalized complete
   tail in step 3. This controls cancellation between all shells.
6. The successor's Möbius coefficient is nonzero by its source definition;
   `log(6)>0`, `1-q!=0`, and the asserted `c` is nonzero. The full limit
   is therefore nonzero, which gives eventual nonzero actual coefficients.
7. For any operator `F` with finite diagonal support, the diagonal of
   `E_M*F` vanishes for every sufficiently large `M`. Linearity of the
   actual diagonal boundary coefficient shows that replacing `R` by
   `R+F` leaves `J_M` unchanged eventually. Finite diagonal support also
   preserves summability and every positive-parameter Gibbs admission.
   Thus the same normalized limit holds for the repaired original source.
8. Only now specialize to an admitted Xi divisor. At multiplicity-top
   orders `k=l=q_rho`, the source multiplicity theorem discharges
   `c=[XiC^(q_rho)(w_rho)]^2!=0`. Every sufficiently late cutoff of each
   finite diagonal repair consequently fails to have zero second
   boundary limit at the fixed dilation six. No RH, cyclicity, or
   reader-agreement premise occurs.

## Scope and surviving comparison problem

This is a positive source-retention theorem at a fixed arithmetic label.
The full complex tail, its exact coordinate cutoff, and its singular
normalization are kept. Finite diagonal support is not finite operator
rank; the theorem does not reconstruct off-diagonal entries.

The Abel parameter tends to zero for each fixed cutoff first. The source
depth then tends to infinity under its specified normalization. No
uniform joint-limit or interchange of those two limits is claimed.
Critical top-jet sources also have the nonzero retained limit. Its
vanishing is therefore not an RH condition. The normalized scalar
readout still requires a source-derived identification with the existing
Sonin/Burnol physical evaluation, preserving the original horizontal
anchor and the relevant source arithmetic actions.

## Search and method audit

Two deep/method searches covered complex geometric moving-tail limits
and regrouping summable series by finite logarithmic fibers. Both were
partial: pending generation `823339`, semantic coverage
`2196271/2336767`, with local reranking deadlines and interrupted
retrieval. Candidate lemmas and source arguments were inspected; no
proof ideas or ingredient sets were returned. Generic positive weighted
averages did not apply to the complex correction. Direct source reads
supplied the exact shell, Tannery, harmonic-number, fiberwise-summation,
and complex-power APIs checked in scratch.

Broad arXiv searches used `cascade`, `memory`, `intermittency`, and
`coalescence`, preferring June--September 2026. Several retrieved
machine-learning and fluid papers were unrelated. The
[September polymer paper](https://arxiv.org/html/2609.02064v1),
Theorem 1.1 and Section 1.3, derives a correlation derivative using the
specified model's boundary terms and intrinsic symmetries. It supplies
no arithmetic symmetry here. Together with the previously inspected
[September geometric-smoothing argument](https://arxiv.org/html/2609.05290v1),
it motivates proving the complete retained response and its domination
from the actual source rather than importing a probability model.

Further broad terms `balayage`, `sewing`, and `transport` returned
mostly older or unrelated material despite the recent-date preference.
The inspected [balayage paper](https://arxiv.org/html/2401.11043v2),
Section 1.1, assumes a strictly positive definite kernel, consistency,
and domination/maximum principles. No matching kernel and principles
have been derived for this complex arithmetic source. Its sweeping
construction therefore supplies no physical-reader comparison here.

## Verification

All 29 theorems passed `lake env lean /tmp/route_l_fixed_six_tail.lean`
without warnings. The targeted final command
`lake build GaloisForLFunctions.RHTower.DeningerGammaSixFixedDilationTailReader`
passed (171 seconds for the new module). All 29 reports from
`lake env lean /tmp/route_l_fixed_six_axioms.lean` contain only
`propext`, `Classical.choice`, and `Quot.sound`. The module is wired
into `RHTower.lean`; whitespace checks passed. No numerical experiment,
full build, or umbrella build was used. All owned Lean processes completed.

The original global lint run reported unrelated unreachable modules.
The subsequent C29 audit ran `scripts/formal_tools.py lint` successfully
with exit status zero and `formal lint passed`, clearing that final gate.
The source, targeted build and complete axiom audit recorded above are
unchanged; this card is now formalized. The unrelated modules were not
modified by this task.
