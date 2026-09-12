# Route L: original native Mellin extraction with its prime prefix

- **ID:** RH-L-C70
- **Stage:** 1-in-progress
- **Target:** Full-source fixed Gamma/BV reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C69 proves the full raised-jet Schwartz-test balance, retaining both original
collars, finite prefixes and distinct critical Xi-jet contacts. Its named
leaf build and lint passed and were revalidated at the start of C70.

## Conjecture and original-source proof mechanism

At the unchanged source parameter `v`, the native Mellin parameter is
`s=m*(1/2+i*v)`. The original coordinate is `x=exp(-u/m)` and the
half-density reconstruction is
`A_(k,p,m)(exp(-u/m))=exp(u/2)*Raw_(k,p,m)(u)`.
Changing variables in the complete admitted integral should give

`Mellin(A_(k,p,m))(s) = (1/m)*RawMultiplier_(p,m)(v)*Xi^(k)(v)`.

The original raw multiplier must remain
`1/zeta(s)-sum_(n<p) mu(n)*n^(-s)`, with its actual zero-index convention.
The previously proved raw-source Fourier–Laplace admission applies when
`|Im(v)|<1` and `1/m<Re(1/2+i*v)`. At every actual Xi divisor, a cofinal
choice of native depth meets this condition without moving the divisor.
This suggests an unconditional cofinal theorem on the original source,
with all multiplicity orders retained.

The next comparison still has to respect the second collar's exact
exchange `s -> 1-s`. The depth correction cannot be removed to replace
that exchange by `m*rho -> m*(1-rho)`. At large native depths, the reflected
Fourier-side Mellin parameter can require endpoint subtractions. C69's
contact formula supplies the zeroth contribution; higher endpoint terms
must be derived from the original source moments before any continued
reading is identified with the fixed quadratic conormal reader.

No fixed-reader equality, ordinary cyclicity, norm equality, stationary
source or zero-location assumption is a permitted input.

## Paper proof and next conjecture

1. Use the proved integrability and value of the complete original raw
   Fourier–Laplace source at `v`. Substitute `x=exp(t)`, then `u=-m*t`.
   The derivative Jacobians give the exact factor `1/m`; both changes
   transfer integrability as well as the value. The exponent reduces to
   `exp(-i*v*u)` using the native half-density reconstruction.
2. Absolute Möbius L-series convergence at `Re(m*s(v))>1` justifies the
   actual finite-head plus infinite-tail decomposition. Its tail is
   `zeta(m*s(v))^-1-sum_(n<p) LSeries.term(mu,m*s(v),n)`.
   The zero term uses the original `LSeries.term` convention.
3. At the unchanged divisor `rho`, positivity of `Re(rho)` gives the
   required domain at all sufficiently large native depths. The normalized
   prime residual tends to `mu(p)=-1`; its exact scalar relation to the raw
   residual makes the latter eventually nonzero. Multiplication by `1/m`
   and the actual top Xi jet retains a nonzero admitted Mellin read.
4. For depth `d=m+1` and each `0<=j<m`, put `r=(j+2)/d` and
   `v=i*(1/2-r)`. Then `0<r<=1`, `|Im(v)|<1`, and `1/d<r`.
   Hence the very same source formula admits its moment of order `j+1`:

   `integral_(x>0) x^(j+1)*A_(k,p,d)(x) dx`
   `= (1/d)*(zeta(j+2)^-1-prefix_p(j+2))*Xi^(k)(i*(1/2-(j+2)/d))`.

This finite moment window supplies actual source integrability for a
Fourier endpoint Taylor argument. It does not supply convergence of an
infinite moment expansion, nor a common remainder estimate as depth varies.
The next conjecture is that a sufficiently long finite Taylor subtraction
can be justified at each original depth before the reflected Mellin read
is compared with the fixed quadratic reader.

**Failed shortcut:** formal cancellation of reciprocal-zeta factors using
a functional equation does not compare the original integrals. The
absolute Mellin domains for `s` and `1-s` are disjoint. Endpoint
corrections and any continuation residues must first be identified from
those integrals. A holomorphic scalar identity also does not identify
squared conormal norms. No route is retired here.

## Lean verification

The complete scratch passed `lake env lean
/tmp/MobiusThetaNativeMellinExtraction.lean` (session 50521, exit 0).
One unreachable `ring` was then removed. The final named audit passed
`lake build GaloisForLFunctions.RHTower.MobiusThetaNativeMellinExtraction`
(session 64640, exit 0; leaf 88 seconds, 12,625 dependency jobs).
Log: `/tmp/route-l-native-mellin-extraction-build.log`.

The 259-line leaf is wired into `GaloisForLFunctions/RHTower.lean` at
line 6283. Its only option is `autoImplicit false`; no proof-limit or
transparency changes were introduced. Public theorems:

- `mobiusThetaNativeCollarTail_hasMellin_at_divisor_cofinal` (line 144).
- `mobiusThetaNativeCollarTail_hasMellin_prefix_at_divisor_cofinal` (line 159).
- `mobiusThetaNativeCollarTail_top_mellin_ne_zero_cofinal` (line 178).
- `mobiusThetaNativeCollarTail_positive_moment_window` (line 201).

No full or umbrella build was run. No numerical experiment, axiom
reporting or new axiom was used. `scripts/formal_tools.py lint` passed (session 65365, exit 0; existing
large-file warnings only), recorded in
`/tmp/route-l-native-mellin-extraction-lint.log`. All owned scratch, search
and build processes terminated; no owned Lean process remains.
RH and fixed-reader agreement remain **UNPROVED**.


## Whole-corpus search audit

The direct research tool was used with deep and hybrid mechanisms, cached
whole-corpus scope and no module filter. All 20 returned candidate statements
and all 20 source-method statements/assumption lists were read in each of
the three searches that supplied them. The interrupted deep counterterm
search supplied 20 declaration locations, no candidate or method records;
its partial output prompted the broader hybrid retry. Source-only entries
are not compiler evidence, and definitions are not admission proofs.

- `route-l-native-mellin-dilation-admission-search.json`: deep, generation
  883688, coverage snapshot 883705; 57,217 files, 47,575 Lean files,
  738,678 declarations, 44,736 pending compiler records. Partial text/source
  retrieval, no proof ideas, one unverified ingredient group. Useful:
  actual raw/internal-jet Fourier–Laplace integral-of-norm summability,
  Mellin change of scale, and `ChronologicalWeightedMellin`'s positive-ray
  Möbius interchange at `Re(s)>1`. The latter was read in full and explicitly
  requires admission of its input weight. The polylog sharp-coefficient
  method assumes half-line location and source decay; it cannot supply them.
- `route-l-native-fourier-mellin-counterterms-search.json`: deep, generation
  883748, coverage 883750; 57,220 files, 738,738 declarations. Text/source
  interruption and semantic timeout; no method or candidate output. Its
  declaration hits included original Green residues and endpoint Mellin
  constructions. No absence conclusion follows from this partial search.
- `route-l-native-fourier-mellin-counterterms-hybrid-search.json`: generation
  883807, coverage snapshot 883832/current 883834; 57,220 files, 738,737
  declarations, 44,737 pending compiler records. Partial text/source
  retrieval, no proof ideas/groups. Endpoint finite-part definitions alone
  provide no remainder bounds. Read the actual quadratic endpoint
  integrability/holomorphy proof and heat-multiplier divided-difference
  bound: each needs a source-specific bound uniform on its stated domain.
  MellinRapid and Sonin/Hardy hypotheses are not available by renaming the
  native source. The monic/positive-moment counterexample also prevents
  inferring a positive measure from coefficient positivity alone.
- `route-l-native-fourier-moment-window-search.json`: deep, 300-second
  budget, generation 883845, coverage snapshot 883914/current 883915;
  57,226 files, 47,582 Lean files, 738,737 declarations, 44,743 pending
  compiler records. Partial text/source retrieval, no proof ideas. The
  unverified Taylor ingredient group pairs a real Taylor theorem with a
  monic polynomial *definition*: it is not a source comparison. Useful
  verified-library shapes: Fourier differentiation consumes actual norm
  moments; Taylor integral remainder consumes finite smoothness;
  DeningerFourierBoundedDerivs supplies derivative bounds from all moments.
  Its full proofs and the general Deninger even-preimage moment proof were
  read. Those general preimage results do not by themselves extract the
  prime-prefix native moment values or identify the fixed reader.

## Broad recent-paper audit

Broad single-word arXiv search `sewing`, latest announcements first, followed
empty broad web queries `sewing` and `threshold` with 2026 dates. Screened
visible results only; the result-page tool output was partial. Selected two
mathematical papers among rough analysis, conformal geometry, Liouville
number, field-theory, garment-generation and robotics hits.

- [Friz–Song–Zhang–Zhang, Rough backward stochastic differential equations,
  v2, 10 September 2026](https://arxiv.org/html/2609.06606v2): read assumptions
  A_par/A_f, Lemmas 3.1–3.2 and the comparison argument in §4.1. The method
  derives an exponential representation of the actual difference equation;
  conditional BMO/VMO estimates justify uniform integrability before
  discarding a martingale contribution. It requires an actual Brownian
  filtration, controlled rough semimartingale solutions, Lipschitz drift,
  bounded terminal data and ordered inputs. None is supplied for the native
  RH reader. Transfer attempt fails at the source equation and uniform
  bound, not at a missing name. The useful demand is to prove admission of
  the original comparison before a nonlinear norm conclusion.
- [Maibach–Peltola, Universality of the conformal anomaly,
  August 2026](https://arxiv.org/pdf/2608.23201): read the main classification
  statement, locality/cocycle conditions and genus-zero normalization and
  comparison mechanism in §5.1. Local Frölicher-smooth real one-dimensional
  modular functors with the same central charge admit a sewing-compatible
  isomorphism. Locality means independence from external boundary
  reparametrizations; it is a substantive condition. The construction
  first matches cocycles and fixes a constant normalization. No such
  functor/locality proof or fixed-normalization match has been constructed
  for the native prime source. An abstract isomorphism cannot replace the
  required equality of the already fixed Gamma/BV readings.

Neither paper contributes an assumed theorem to the Lean proof.

## Sharpened next endpoint target

The finite window has the right length for the unchanged reflected
parameter, not merely for a fixed low-order Taylor expansion. Put `d=m+1`,
`s=d*rho`, and `sigma=1-s`. Evenness of the literal native tail transfers
its admitted positive-ray moments of orders `0,...,m` to full-line norm
moments. The zeroth order is already C65; C70 supplies orders `1,...,m`.
The corpus Fourier derivative theorem then gives `C^m` regularity and a
finite bound `C_m` on the derivative of order `m` of `F=Fourier(A)`.

Subtract the actual Taylor polynomial of `F` through order `m-1` at zero.
The real-variable, complex-valued Taylor integral remainder bounds the
residual by `C_m*x^m/m!` on `0<x<=1`. At the unchanged reflected Mellin
parameter its weighted density is bounded by a constant times

`x^(Re(sigma)+m-1) = x^(d*(1-Re(rho))-1)`.

The exponent is strictly greater than `-1` for every original Xi divisor,
using only the proved open strip. At cofinal depths `d*Re(rho)>1`, the far
ray also converges absolutely because `F` is bounded and `Re(sigma)<0`.
This gives a paper mechanism for an admitted complete Fourier Mellin
remainder with the source-forced Taylor contacts retained. It requires
formal transfer of each original moment to the full line and explicit
Taylor coefficients; it is **not yet a Lean theorem**.

Next attack: formalize this precise remainder admission, then derive the
regularized Fourier-kernel/Mellin value and compare with the original
second collar. Gamma factors, all restored polynomial contacts and their
parameter responses must remain explicit before testing the fixed
quadratic reader. This mechanism does not assert those readings agree.
