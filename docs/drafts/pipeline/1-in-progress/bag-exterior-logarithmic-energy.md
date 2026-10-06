# BAG actual exterior logarithmic energy

2026-10-06,01ax. Next hard target: prove arbitrarily rapid N-saving for the
full weighted logarithmic Fourier energy of the actual physical exterior
remainder, uniformly over sigma in[1,2]^2. This attaches the existing pure
physical exterior jets to the actual moving Mellin profiles. Current local
selected-family audit99827/log03 is running; no premature global claim.

Corpus: ChiCubicPhysicalExteriorDecay788 gives arbitrary polynomial spatial
weight and N-saving for every fixed pure physical derivative, outside the
complete positive stationary box[1/4,4]^2. CompactMellinLocalization supplies
chi=1 on an OPEN neighborhood of that box, compact support inside(1/8,8)^2,
and all smoothness. PositiveQuadrantMellinLines supplies exact weighted log
Schwartz realization and its literal Euler operators. Lexical search
/tmp/bag-exterior-log-euler-search-01ax.json completed,9 hits; no coverage or
compiler-freshness metadata in lexical output. Definitions and private
HasFDeriv/fderiv proof sources16–96 inspected. No candidate/source-argument
or ingredient groups returned. Private smoothness proof gives membership
only; its input-dependent constants are not uniform budgets.

Conjectured proof. Let exterior physical input be(1-chi)*f_N. Its pure jets
of orders0,1,2 vanish throughout the stationary box because chi=1 on an open
neighborhood. Outside, actual pure-jet decay and the bounded cutoff jets give
uniform rapid N-saving with arbitrary polynomial spatial decay. Keep all
cutoff derivative terms. General weighted log differentiation is exactly
L_sigma(f) -> L_sigma(E_i f), E_i f=-sigma_i*f-x_i*D_i f.
Thus the second pure derivative is L_sigma(E_i(E_i f)), with physical terms
sigma_i^2*f+(2*sigma_i+1)*x_i*D_i f+x_i^2*D_i^2 f.

The exact full nonnegative log substitution gives density
x^(2*sigma0-1)*y^(2*sigma1-1) times physical squared norm. On the compact
parameter box these factors are bounded by(1+x)^3*(1+y)^3. Proved arbitrary
physical decay then gives admitted uniform mass for the exterior profile
and BOTH pure second logarithmic derivatives, with arbitrary N-saving.
A separated inverse-square majorant admits the resulting physical integral;
all Jacobians and axis endpoints are included. Exact Fourier differentiation
turns the two pure second-derivative masses into fourth spectral moments.
Mass plus those moments controls the complete H^2 Fourier weight and hence
every needed order1<s<3/2. Mixed derivative budgets are unnecessary.

No actual uniform exterior log estimate is yet formalized. Required proofs:
exact Euler identities on the literal Schwartz objects; coordinate pure-jet
identification with the existing iteratedDeriv theorem; all cutoff-product
terms/support; full weighted two-coordinate substitution and admission;
actual N-uniform tail assembly. Do not replace these with premises.
Further endgame: Mellin/source-weighted tails, lower-growth arithmetic bound,
moving-test signed cancellation/full sharp action, moments/common-height.

2026-10-06 01ax current scratch /tmp/bag-exterior-logarithmic-energy-01ax.lean.
Audit84538/log01 and71576/log02 accepted the exact weighted two-coordinate
log mass substitution and actual all-order pure-jet identification, but
complex-specialized module tactic algebra failed in Euler helpers. Keeping
the native proof polymorphic in a real normed target and constructing the
local gradient with our explicit coordinate maps repaired those issues.
Audit40097/log03 accepted exact first/second Euler identities, affine-line
jet identities, physical exterior attachment, full weighted log mass
identity, cutoff jet formulas/vanishing/support/bounds except one product
fderiv rewrite needing an explicitly typed function lambda. Corrected it.
Current audit85413/log04 adds uniform cutoff jet control through order2 and
actual rapid exterior pure-jet decay on the COMPLETE positive quadrant,
using exact zero on the stationary box. No final exterior log energy closure
yet; no hypotheses, axioms, or resource increases introduced.

Next assembly: exact E_i^2 f = sigma_i^2 f+(2sigma_i+1)x_i D_i f+x_i^2 D_i^2 f.
The three actual exterior jet bounds give arbitrary N-saving for this
physical Euler combination with any fixed polynomial spatial weight.
The proved log mass formula has densityx^(2sigma0-1)y^(2sigma1-1), bounded
by(1+x)^3(1+y)^3 on sigma in[1,2]^2. Choose a fixed sufficient spatial weight
and dominate by the admitted separated inverse-square kernel; do not optimize
constants. Apply to exterior and both twice-Euler inputs. Fourier pure second
moments then give full H^2 energy and hence the desired lower orders.

2026-10-06 01ax checkpoint: scratch91235/log09 terminal0PASS.
Exact full weighted log mass, both second derivative masses and the PUBLIC
actual exterior H^2 arbitrary-power decay theorem pass standard3 axiom
prints. No physical cutoff term, logarithmic Jacobian or axis endpoint was
removed. Uniform compact sigma square, arbitrary natural k, actual selected
family. Appended exact full local+exterior energy assembly; audit17612/log10
running. Production promotion, umbrella wiring, imported axioms/index/lint
still pending; do not record production closure yet.

Next arithmetic insight, not yet a theorem: pole distance must be saturated
as (1/logN+|t|)/(1+|t|). The corpus's logarithmic upper and reciprocal bounds
near Re(s)=1, combined with exact uniform finite Euler comparison, should
yield T^epsilon times a background1 plus both actual axes profiles. Using
unsaturated pole distance globally would waste powers of T and fail the
physical regularity pairing. Moving-test tails still require trace control;
a bare uniform weighted L2 bound alone does not control concentrations on
shrinking transverse axes. Local compact log multipliers can supply Mellin
frequency derivatives; exterior moments must be paid from actual jets.

CLOSED: production99895 and imported axioms37031 PASS;947lines/API5.
Full proof/audit ledger is P2/P3 bag-exterior-logarithmic-energy. Index85730
PASS, lint41249 global17unrelated failures/noownedfinding. Nexthardtarget
P1 bag-source-saturated-pole-transfer. RH remains unproved.
