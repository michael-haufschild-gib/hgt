# Complex-time exponential generation, phase recurrence, and normalization-wall law

- **ID:** `ulf-grm-complex-time-exponential-generation`
- **Stage:** 2 — fully proven on paper
- **Type:** UNIVERSAL MECHANISM / LITERAL EULER-SHELL REALIZATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FOUR-ORGAN FUSION] [LEAN CORE CERTIFIED] [NOT RH]`

## 1. Higher pivot: straight admission is not execution

For a positive probability carrier `w=(w_x)` and centered score `r=(r_x)`, the formal tangent is

\[
h_x=w_xr_x,\qquad \sum_xh_x=0.
\tag{CTG.1}
\]

If `r` is unbounded below, every straight Euler step `w+epsilon h` has a negative tail. The
straight admission radius is zero. Nevertheless the nonlinear path

\[
w_t(x)=\frac{w_xe^{tr_x}}{Z(t)},
\qquad Z(t)=\sum_xw_xe^{tr_x}
\tag{CTG.2}
\]

is positive wherever `Z(t)<infinity`, and `d w_t/dt|_0=h`. Thus the radial cone measures linear
Euler executability, not general integrability of a generative law.

The missing field coordinate is the domain of the exponential partition function.

## 2. Complex-time generating law

Let

\[
\mathcal Z(z)=\sum_xw_xe^{zr_x}
\tag{CTG.3}
\]

on its open absolute-convergence strip `S`, and put `Psi(z)=log mathcal Z(z)` wherever a logarithm
branch is chosen. Then:

1. the real slice `z=t` is positive exponential execution `(CTG.2)`;
2. the imaginary slice `z=is` is the phase reporter
   \[
   \Phi(s)=\sum_xw_xe^{isr_x};
   \tag{CTG.4}
   \]
3. derivatives at zero are the moment/prolongation tower
   \[
   \mathcal Z^{(k)}(0)=\sum_xw_xr_x^k;
   \tag{CTG.5}
   \]
4. normalized observable response is covariance:
   \[
   \frac d{dt}\mathbb E_{w_t}[f]
   =\operatorname{Cov}_{w_t}(f,r).
   \tag{CTG.6}
   \]

### Proof

Absolute convergence on compact substrips permits termwise differentiation, proving `(CTG.5)`.
Normalization gives `sum w_t=1`; differentiation of the quotient gives

\[
\dot w_t(x)=w_t(x)(r_x-\mathbb E_{w_t}r),
\tag{CTG.7}
\]

and summing `f_x dot w_t(x)` proves `(CTG.6)`. Substituting `z=is` proves `(CTG.4)`. QED.

## 3. Positive observation and exact Fisher conservation

Let `K_(xy)>=0` be a finite or summably admitted Markov kernel with `sum_yK_(xy)=1`. Define

\[
v_y=\sum_xw_xK_{xy},\qquad
v_ys_y=\sum_xw_xK_{xy}r_x.
\tag{CTG.8}
\]

Thus `s_y=E[r|y]` on occupied output atoms. Then

\[
\boxed{
\sum_xw_xr_x^2
=\sum_yv_ys_y^2
 +\sum_{x,y}w_xK_{xy}(r_x-s_y)^2.}
\tag{CTG.9}
\]

For centered `r`, both observed and source scores are centered. Hence

\[
\boxed{\operatorname{Var}_v(s)\le\operatorname{Var}_w(r),}
\tag{CTG.10}
\]

with exact lost information equal to the final nonnegative term in `(CTG.9)`.

### Proof

Expand the square in the last term. Row stochasticity changes the `r_x^2` term to
`sum_xw_xr_x^2`; `(CTG.8)` changes the cross term to `-2sum_yv_ys_y^2`; the remaining term is
`sum_yv_ys_y^2`. Rearrangement proves `(CTG.9)`. QED.

This is the positive-observer data-processing law for nonlinear generation. Unlike the straight
gauge, it permits unbounded scores when the required exponential moments exist.

## 4. Literal marked Euler-shell realization

For the marked shell source `a_m(n)` and `sigma>1`, let

\[
P_{m,\sigma}(n)=\frac{a_m(n)n^{-\sigma}}{S_m(\sigma)},
\qquad
\mu_\sigma=\mathbb E_{P_{m,\sigma}}\log n,
\qquad
r_\sigma(n)=-\log n+\mu_\sigma.
\tag{CTG.11}
\]

The score is centered and unbounded below. Its complex partition law is exactly

\[
\boxed{
\mathcal Z_\sigma(z)
=e^{z\mu_\sigma}\frac{S_m(\sigma+z)}{S_m(\sigma)}.}
\tag{CTG.12}
\]

For real `t` with `sigma+t>1`, exponential tilting is not an analogy but the next shell Gibbs
fibre:

\[
\boxed{(P_{m,\sigma})_t=P_{m,\sigma+t}.}
\tag{CTG.13}
\]

For imaginary time,

\[
\mathcal Z_\sigma(is)
=e^{is\mu_\sigma}\frac{S_m(\sigma+is)}{S_m(\sigma)},
\tag{CTG.14}
\]

which is the centered phase/recurrence correlation. Derivatives give centered log-moments. The
same `S_m` has the established HT realization.

### Proof

Substitute `(CTG.11)` into `(CTG.3)`:

\[
\sum_na_m(n)n^{-\sigma}e^{z(-\log n+\mu_\sigma)}/S_m(\sigma)
=e^{z\mu_\sigma}S_m(\sigma+z)/S_m(\sigma).
\]

For real `t`, the normalized coefficient is proportional to `a_m(n)n^{-(sigma+t)}`, proving
`(CTG.13)`. QED.

## 5. Exact normalization-wall interpretation

The real negative-time lifetime of `(CTG.13)` is

\[
\boxed{\tau_-(\sigma)=\sigma-1.}
\tag{CTG.15}
\]

At `t=1-sigma`, the partition function hits the shell abscissa and diverges. The physical
half-density matching condition is `sigma=1/m<1`, so it lies beyond this positive exponential
chart. Therefore the normalization wall is not a failure of straight-line positivity; it is the
finite boundary of the nonlinear generating semigroup itself.

This also sharpens hypertranscendence. HT is not noncompact observed motion. It is non-finite
differential closure of the complex-time generating law, while noncompactness appears in its
unwrapped score history or at the finite real-domain boundary.

## 6. Four organs are one law, not four analogies

One function `(CTG.12)` now has four exact faces:

1. **positive generation:** real exponential tilts `P_(sigma+t)`;
2. **phase/recurrence:** imaginary boundary values `S_m(sigma+is)/S_m(sigma)`;
3. **moment/Hankel/HT prolongation:** derivatives in complex time;
4. **completion/normalization:** the real-domain boundary `sigma+t=1`.

The unifying mechanism is therefore not curvature. It is **complexified intervention flow with a
source-determined domain of execution**.

## 7. Joint reconstruction and conservation

The phase face determines the atomic score distribution when its characteristic function is known
for all real `s`. The real face determines its Laplace transform on an interval. Analytic
continuation makes them boundary values of one germ. Positive Markov observation loses exactly the
conditional-variance term `(CTG.9)`. Consequently a family of observers is generatively complete
when:

1. their combined characteristic reporters reconstruct the score law;
2. their Markov losses sum to zero only for the trivial source ambiguity;
3. their common exponential domain reconstructs the source normalization wall.

This is stronger than coefficient faithfulness and stronger than finite Gram legality.

## 8. Fourth-organ prediction

For every positive coarse observer of the Euler-shell score, its Fisher information is bounded by
the full shell log-variance, and the exact deficit is its conditional log-variance. Therefore any
claimed finite receiver whose Fisher information exceeds

\[
\operatorname{Var}_{P_{m,\sigma}}(\log n)
\tag{CTG.16}
\]

cannot be a positive Markov shadow of this literal source. Equality predicts that the observer
fibres preserve the log clock almost surely. This is a falsifiable theorem for any future compact
positive carrier or route receiver.

## 9. RH gate, only now

The first legitimate selection target is no longer a source-native null relation. It is:

1. construct an off-divisor arithmetic intervention whose complex-time partition germ lands in a
   jointly conservative family of route observers;
2. prove a source-derived common real-domain extension across the critical normalization wall, or
   prove that off-critical divisor orientation would force a forbidden Fisher increase;
3. use reflection to identify the maximal common domain with the central fibre.

No such extension or forbidden-increase theorem is claimed here. The theorem identifies a typed
mechanism whose failure would genuinely select, rather than redescribe, RH.

### Exact Burnol/Cartier selection interface

The corpus separately proves that every hypothetical strict-right Xi divisor strictly amplifies
one fixed positive two-head energy. Therefore:

> If that two-head receiver can be realized, before divisor specialization, as the second moment
> of a positive Markov score shadow of the common arithmetic source, then no strict-right divisor
> exists; reflection gives RH.

This implication is immediate from `(CTG.10)` and the already-formalized strict amplification
theorem. The premise is not currently proved. In particular the existing Burnol divided-shift
current is signed and the singular Cartier transfer is not a constructed Markov kernel. Treating
it as one would simply rename the missing non-amplification producer. The gain is a sharp
construction target: build the stochastic kernel, source probability, and score-current identity
`(CTG.8)`, or prove no such realization can exist and pivot again.

## 10. Hostile boundaries

1. Straight radius zero does not imply nonintegrability; `(CTG.13)` is the counterexample.
2. Exponential moments on one side do not imply a two-sided analytic strip.
3. Phase recurrence does not determine real-domain width without analytic/source growth data.
4. Markov positivity is load-bearing for `(CTG.9)` and `(CTG.10)`.
5. HT does not force orbit noncompactness.
6. The half-density fibre remains beyond the proved positive chart; naming analytic continuation
   does not construct a positive carrier there.

## 11. Lean certification boundary

`GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics` certifies the finite universal
core: normalized exponential tilt, its centered infinitesimal tangent, tangent conservation, exact
Markov second-moment/Fisher conservation, data processing, and the equality classification by
score preservation on every positive kernel edge. It also certifies that strict receiver
amplification excludes every positive Markov realization. The countable Euler-shell identity `(CTG.12)`
and its abscissa boundary remain paper-level in this card; their constituent shell formulas are
formalized in the existing Euler-shell theorem family.
