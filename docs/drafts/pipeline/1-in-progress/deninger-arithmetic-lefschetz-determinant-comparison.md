# Arithmetic Lefschetz and determinant comparison

- **ID:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with dependency-closed uniqueness reduction
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** The trace distribution of the derived rational-Witt arithmetic flow equals
  Deninger's prime--archimedean Lefschetz distribution; its regularized determinant is therefore
  the completed zeta characteristic quotient.

## Goal

Connect constructed arithmetic \(H^0,H^1,H^2\) to primes and to \(\zeta\).  Existing Lean
proofs establish the analytic explicit formula and the Xi characteristic target.  Missing
work is a source comparison from the derived coefficient complex, not another proof of the
explicit formula.

## Gates

- [x] 0 → 1 in-progress: exact comparison statement, uniqueness reduction, falsifiers
- [ ] 1 → 2 fully-proven: construct cohomological trace and determinant and prove comparison
- [ ] 2 → 3 formalized: source comparison plus determinant uniqueness in Lean
- [ ] 3 → 4 publication-ready: integrate with arithmetic cohomology and Hodge theorem

## Existing unconditional target

The repository already proves, analytically:

1. the positive-time distributional explicit formula
   \[
     \mathcal T_{\mathrm{spec}}
       =\mathcal T_{\mathrm{prime}}+\mathcal T_\infty+\mathcal T_{\mathrm{end}};
                                                                            \tag{1}
   \]
2. the characteristic quotient identity for the analytic Xi module;
3. equality of the logarithmic derivative of the Xi characteristic section with the
   prime--Gamma resolvent trace on the Euler half-plane.

These are comparison targets only.  They do not construct arithmetic cohomology.

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_LEFSCHETZ_TRACE_COMPARISON]`

Let \(H^q_{\mathrm{dyn},c}\) and \(\Theta_q\) arise from the completed derived rational-Witt
coefficient complex.

1. **Test-operator trace class.** For every
   \(\varphi\in C_c^\infty(\mathbb R_{>0})\),
   \[
      K_{\varphi,q}
        =\int_0^\infty\varphi(t)e^{t\Theta_q}\,dt
   \]
   is trace class in the arithmetic nuclear/Hilbert rigging, and
   \[
      \mathcal L_{\mathrm{coh}}(\varphi)
        =\sum_{q=0}^2(-1)^q\operatorname{Tr}K_{\varphi,q}                \tag{2}
   \]
   is continuous in the test-function topology.

2. **Fixed-orbit localization.** The Schwartz kernel of `(2)` localizes to closed prime
   orbits, the real-place fixed contribution, and endpoint fixed classes.  With Deninger's
   orientation convention,
   \[
      \mathcal L_{\mathrm{coh}}
        =\mathcal T_{\mathrm{prime}}+\mathcal T_\infty+\mathcal T_{\mathrm{end}}.
                                                                            \tag{3}
   \]
   Combined with `(1)`, this proves
   \(\mathcal L_{\mathrm{coh}}=\mathcal T_{\mathrm{spec}}\) without inserting zeros into
   the source.

3. **Regularized determinant.** For \(q=0,1,2\), the closed generators admit determinant
   sections \(D_q(s)=\det_\infty(s-\Theta_q)\), with
   \[
      D_0(s)=s,\qquad D_2(s)=s-1,                                      \tag{4}
   \]
   and the logarithmic derivative of \(D_1\) equals the degree-one resolvent trace on
   \(\Re s>1\).

4. **Normalization and analytic continuation.** \(D_1\) is entire, nonzero on
   \(\Re s>1\), has the same finite-order growth class as \(\xi\), and is normalized at one
   fixed \(s_0\) in that half-plane by
   \[
      D_1(s_0)=\xi(s_0).                                                 \tag{5}
   \]

5. **Spectral divisor.** The zero divisor of \(D_1\), with algebraic multiplicities, is the
   discrete spectrum of \(\Theta_1\).  There is no residual determinant divisor invisible
   to the operator spectrum.

## Dependency-closed determinant uniqueness

`[PROVED HERE] [DAC_LOG_DERIV_DETERMINANT_UNIQUENESS]`

Let \(D\) and \(\xi\) be holomorphic and nonvanishing on the connected half-plane
\(\Re s>1\).  If
\[
  \frac{D'}D=\frac{\xi'}\xi
\]
there, then \(D=c\xi\) for a nonzero constant \(c\).  Indeed,
\((D/\xi)'=0\), so connectedness makes \(D/\xi\) constant.  Condition `(5)` forces \(c=1\).
If both functions extend to entire functions, the identity theorem gives
\[
 D_1=\xi\quad\text{on }\mathbb C.                                      \tag{6}
\]
Mathlib's `logDeriv_eqOn_iff` already packages the connected-domain constant-multiple step.

Consequently clauses 1--4 imply
\[
 2\,\frac{D_1(s)}{D_0(s)D_2(s)}
   =\widehat\zeta(s),                                                    \tag{7}
\]
away from \(0,1\), and then meromorphically everywhere.  Clause 5 turns `(6)` from a
function identity into the required spectrum--zero identification.

## Step-by-step attack

1. Construct \(K_{\varphi,q}\) first on the dense regulator image.
2. Use the finite-stage Kähler--Riemann/Leichtnam trace theorem, then
   prove the pro-nuclear convergence required by
   `DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`.  A single finite-harmonic
   lamination is ruled out.
3. Use bounded-geometry smoothing estimates for the leafwise Dirac/Hodge operator and the
   transverse flow to extend the limit operator as trace class.
4. Derive fixed-orbit terms at a single prime-power orbit from the oriented power
   correspondence; then prove locally finite summation in test-function support.
5. Derive the real contribution from the regulator boundary, not from a preloaded Gamma
   factor.
6. Match `(3)` to the already formalized analytic distribution `(1)`.
7. Construct \(D_1\) from heat/resolvent regularization and prove its logarithmic derivative
   law.
8. Apply determinant uniqueness `(6)`, then prove the spectral-divisor clause.

## Hostile audit and falsifiers

- Equality `(1)` alone is not a cohomological Lefschetz theorem.  Clause 2 requires a kernel
  localization proof from the arithmetic complex.
- A measured trace can miss finite or density-zero spectral defects.  Clause 5 is mandatory;
  determinant equality without a faithful spectral-divisor theorem does not prove RH.
- Equality of logarithmic derivatives determines a function only up to a nonzero constant.
  Normalization `(5)` is mandatory.
- Trace class for each finite prime packet does not imply trace class after summing all primes.
  Uniform locally finite estimates in the test topology are mandatory.
- No positivity or critical-line information is assumed here.  Those come from the
  source Hodge theorem after the spectrum comparison is proved.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`.  Existing analytic Lean closes the target side.
Open core is source trace-class localization, real-boundary contribution, determinant
construction, and faithful spectral-divisor identification.

## References

- Christopher Deninger, *Some analogies between number theory and dynamical systems on
  foliated spaces*: https://www.emis.de/journals/DMJDMV/xvol-icm/14/Deninger.MAN.html
- Christopher Deninger, *Number theory and dynamical systems on foliated spaces*:
  https://arxiv.org/abs/math/0204110
- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
