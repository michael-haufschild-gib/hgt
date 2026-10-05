# BAG complete labelled local source at physical prime height

Route: full prime-height inverse profile, keeping all prime factors.
Status: dependency-closed paper proof and Lean formalization audited; C28.56ag.18.
No signed asymptotic estimate or RH proof.

Let P be every prime up to M=floor(2N), N>1. For a distinguished label p,
define W_p(x)=log(p)*product_q (tag_q(x_q) if q=p else base_q(x_q)) on the
FULL product of prime-square grids. Its Fourier multiplier at integer n is
exactly the existing distinguished entry E_p(|n|), by finite product-sum
interchange and the proved local tag/base Fourier laws. Summing labels
recovers the complete local-grid source, hence the original critical source
on every finite Fourier test.

On covered positive integer frequencies a,b,c, E_p(a),E_q(b),E_r(c) vanish
unless a=p,b=q,c=r. The TWO original equality projectors therefore transfer
exactly to the two LABEL exclusions p!=r and q!=r, including the restored
intersection. Extend by linearity to the actual full finite Fourier test;
the proved complete lattice Poisson identity identifies it with the actual
lifted Schwartz test. No product/separability replacement of the amplitude.

For a fixed third label r, contract its entire third local grid inside the
two tangential lattice sums. Whole-block absolute summability justifies
this finite exchange. Partial Poisson and E_r(n)=log(r)*1_(n=r) reduce the
third source exactly to log(r) times the complete physical-height test.
If r is outside the physical band, the full physical slice is zero; no
unproved endpoint extension is used.

Hence the actual smoothed noncontracting cubic is the sum over r of log(r)
times the first/second local-grid pair action with both label sums excluding
r, evaluated at the complete physical-height test. At prime r each surviving
first/second label contributes its BASE r-factor. Factor those two bases
out of the products. Group the remaining complete profile by x_r=k,y_r=l;
its finite fibre sum keeps every other prime coordinate and both label sums.
This gives sum_(k,l) base_r(k)*base_r(l)*H_r(k,l).

Dephase H_r by the nonvanishing exact local bilinear character. The proved
full-profile prime-square inverse-fibre identity then gives the exact sum
over d in F_r: zero fibre is the full axes/intersection term, while each
nonzero fibre is r^-2 times its full weighted inverse curve, paired with
the additive character at d. Its complete two-frequency Kloosterman formula
is available. No zero mode, negative atom, mixed phase or remaining factor
is discarded. The original actual cutoff family supplies the support data
and preserves the original log^2(N)/N sharp/smooth norm error.

Remaining hard target: growing signed cancellation of this COMPLETE profile
sum, pairing the nonzero negative cone pole with every near-cone/tail sector.
Exact finite Fourier identities and fixed-modulus norm bounds are not this
saving. Growing moments, moving cofactors, common-height self-return and RH
remain open.


## Formal result and audit (continuation01ak)

- ChiRamanujanCriticalGridSource: adds ramanujanLabelledLocalGridWeight and
  its exact all-integer Fourier law. The existing total Fourier law now
  follows by summing labels; the original total-weight definition is unchanged.
- ChiRamanujanLabelledGridAction:354 lines,19 public declarations. Exact
  full labelled tensor, both projector exclusions, complete cofactor/base
  factorization and full axes/inverse-profile action.
- ChiPrimeGaussianCubicLocalPrimeHeight:196 lines,6 public declarations.
  Each third labelled grid selects its physical height, including exact zero
  outside the supported band. Whole-block summability justifies both finite/
  infinite exchanges. The actual full smoothed cubic equals
  bagLocalPrimeHeightInverseAction. exists_bagLocalPrimeHeightInverseFamily
  is hypothesis-free and keeps the original log^2(N)/N normalized complex
  sharp/smooth error tending to zero.

Final production commands used lake --old env lean on each changed leaf
with its own -o target; handles19667,89834,53950 all exited0 with empty logs.
All28 audit targets (27 new public declarations plus the revised old Fourier
law) use only propext, Classical.choice, Quot.sound; corrected scratch audit
31638 exited0. Earlier audit74421 printed the same28 standard-only results
but one optional LinearMap.sum_apply name probe needed its fifth universe
parameter; only the scratch probe changed. Index39694 passed; all28 API
entries verified and both new imports occur once. No umbrella/full build.
Lint74630:22 unreachable modules outside these leaves and174 large-file
warnings; no new-leaf or proof-debt finding. Global lint is not clean.

The exact dephasing is algebraic division by a nonzero character. It does
not imply small profile derivatives, small Fourier mass, separability, a
stationary approximation, or a growing signed saving. The actual transverse
source retains exp(-2*pi*i*r*(xi*upsilon)) and its coupled r-dependent
transition. Its shifted cofactor phases must remain in the next estimate.
The hard target is the norm of the COMPLETE height sum, including the zero
axes/intersection and all nonzero inverse fibres, at o(N/log^2 N). The
nonzero negative cone residue must cancel with the full near-cone/tail
source. Growing moments, moving cofactors, common-height self-return and RH
remain open. This closes the exact coupling gap of ag.17 only.
