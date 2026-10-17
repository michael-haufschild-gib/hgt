# Two separate heat grids do not reconstruct a spectral packet

Status: paper-proved and Lean-audited obstruction and countable positive survivor.

## Failed claim

Injectivity of the paired prime-log phase clock does not imply that the two
separate heat-trace sequences determine a spectral packet. The traces do
not record which first-grid eigenvalue belongs to which second-grid eigenvalue.

## Exact obstruction

For arbitrary h,k>0 set a=2*pi/h, b=2*pi/k, A=1+(a+b)^2. The packets
`{A,A,A+i(a+b),A-i(a+b)}` and `{A+ia,A-ia,A+ib,A-ib}` have positive integer
multiplicities, are closed under conjugation, and lie strictly inside
`Im(w)^2<Re(w)`. Their real heat traces are

`F(t)=2 exp(-At)(1+cos((a+b)t))`,
`G(t)=2 exp(-At)(cos(at)+cos(bt))`.

At nh, the phase at is 2*pi*n, so cosine addition gives F=G. At nk use
bt=2*pi*n instead. At t*=2*pi/(a+b), F=4 exp(-At*) and
G=4 exp(-At*)cos(a*t*)<F, since 0<a*t*<2*pi. This includes distinct prime-log
steps. These are abstract admissible spectral packets, not actual Xi zeros.

## Strongest positive survivor

Mixed samples at `t0+m log(p)+n log(q)` recover the full summable coupling.
For jointly distinct paired coordinates (x_j,y_j) tending to (0,0), with
no pair zero, choose a complex r outside the countable forbidden slopes
`-x_j/y_j` and `(x_l-x_j)/(y_j-y_l)`. Then z_j=x_j+r*y_j is nonzero,
injective, and tends to zero. Zero denominators are resolved by joint
distinctness and nonvanishing. All mixed moments of summable coefficients
converge, since both coordinate sequences are bounded. Binomial expansion
turns their vanishing into vanishing of every positive moment at z_j.
The corpus theorem `coeff_eq_zero_of_atomicMoments_vanish` forces every
coefficient to vanish. The auxiliary r is only a proof device.

For distinct complex frequencies w_j with real parts tending to infinity,
the two positive prime-log heat coordinates tend to zero and are jointly
injective: norms determine the real part and paired phases determine the
imaginary part. With coefficients c_j regularized by exp(-t0*w_j), all
mixed heat samples determine each c_j whenever the regularized weights
are absolutely summable. Comparing two packets uses their common union
support and coefficient difference. No reality, sign, or RH premise enters.

This closes the proposed marginal reconstruction route by an exact
coupling boundary. It does not establish source positivity or RH.

## Formalization

- `RHTower/HeatGridMarginalAmbiguity.lean`: explicit conjugate packets,
  both marginal equalities, strict trace separation, and spectral parabola.
- `RHTower/HeatMixedMomentDeterminacy.lean`: countable scalar projection,
  mixed-moment convergence and determinacy, paired heat injectivity, and
  recovery from regularized mixed prime-log samples.

Dependency-closed paper proof: complete above. Both narrow `:olean` builds
and final separate `lake env lean` audits passed without warnings. All 18
public declarations have only `propext`, `Classical.choice`, and `Quot.sound`
in their axiom closure. Umbrella imports and index refresh passed. Repository
lint exited 1 on 22 unrelated unreachable OddSector and HTGeometry modules;
neither module in this contribution has a lint error.
