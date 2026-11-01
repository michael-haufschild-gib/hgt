# Three orthogonal RH approaches: source and obstruction audit

- **ID:** ARGON-3
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3110/argon.md`, §§2.2–2.4.
- **Goal:** Find and formalize substantive unconditional consequences of the three proposed approaches; prove precise obstructions where mechanisms fail. A missing proof does not establish impossibility of a paradigm.

## A. Gauss–Mayer and loop-Eisenstein scattering

`TheLoopEisensteinReflectionCarriesTheHodgeDefect.lean` defines `reflectionPoles` as denominator zeros, not analytic poles. Its RH equivalence is proved. Numerator noncancellation and the bridge to the Mayer operator require separate verification.

`SelbergScatteringNativeResidual.lean` already proves that every actual Xi scattering energy has strictly positive optimal residual in the original modular self-adjoint domain, including critical zeros. Reusing self-adjoint spectral exclusion would therefore reject the desired zeros too. This existing obstruction is not a new result.

`SelbergScatteringPolynomialXiObstruction.real_on_all_xi_copies_iff` further classifies fixed polynomial changes of the native Casimir: only real constants send all actual Xi copies into a real spectrum. Arbitrarily high genuine critical-line scattering poles defeat every nonconstant polynomial. Thus polynomial recentering does not repair the domain obstruction.

**Open target:** Identify a source-specific resonance exclusion mechanism surviving this domain obstruction.

**Conjecture A1:** A rational function of the native Casimir is real on infinitely many critical-line Casimirs iff it is a real constant. This extends the polynomial obstruction to fixed rational/Padé spectral changes. Pole-free evaluation points must be used; totalized division at poles must not create spurious real values.

**Proof mechanism under audit:** Write `C(t)=3/16+t²/4+it/4`. The identity `C(-t-i)=C(t)` gives one reflection. Real values on an infinite real set force Schwarz reflection of `R(C(t))`, giving the second reflection `t↦-t+i`. Their composition forces period `2i`; a rational function with nonzero additive period is constant. Polynomial composition preserves coprimeness, so the corpus theorem `FieldShift.shift_periodic_quotient_constant` applies after rescaling the period.

**Algebraic reduction:** In a reduced fraction `P/Q` with monic `Q`, set `A=P∘C`, `B=Q∘C`. Infinite reality implies `ĀB=AB̄`. Coprimeness forces `B | B̄`; equal degree and the real leading coefficient of `B` give `B=B̄`. The existing polynomial classifier makes `Q=1`, then makes `P` a real constant. For a nonconstant fraction the nonzero cross polynomial has degree at most `2(deg P+deg Q)`, giving a finite interpolation bound. The bound four is attained for degree-one numerator and denominator by `i(z-3/2)/(z-1/2)` at `t=±√7/2, ±√15/2`.

**Surviving changes of spectral variable:** For `λ=(ρ/2)(1-ρ/2)` and `E=(ρ-1/2)²`, `ρ=E+4λ-1/4` gives a quadratic relation. Separately, the corpus already constructs a single-valued entire transform `F` with `F(C(t))=cosh(4πt)` (`SelbergScatteringEntireTransform`). Its actual operator packets have zero limiting defect iff the original zero is critical (`SelbergScatteringEntireXiPackets.xiEntirePacket_residual_zero_iff`). Recovering a real-looking scalar therefore does not supply the missing source-specific spectral occurrence. A1 concerns fixed rational scalar transports, not general Padé approximation of transfer operators.

## B. Böttcher and arithmetic period rigidity

`AlgebraicVerticalFirstJets.lean` detects all polynomial partial derivatives only at algebraic torus points with algebraic coefficients. Applying it at a zeta zero requires an independently proved arithmetic realization. The proposed nonlinear equation and realization have not been specified.

**Existing exact obstruction to direct prime-coordinate application:** `SixExponentials/PrimePowers.lean`, `not_all_three_prime_cpow_isAlgebraic`, proves that three distinct prime powers `p^ρ`, `q^ρ`, `r^ρ` cannot all be algebraic when `ρ.im ≠ 0`. Thus actual Xi zeros cannot supply the algebraic torus point required by the cited Baker first-jet theorem on three or more prime coordinates. This is already formalized mathematics, not a new result of this investigation.

`BottcherContinuation.basin_monodromy_image_eq_dyadicRootsOfUnity` gives the same full dyadic-root multiplier group for every disconnected quadratic basin. The unmarked group alone cannot distinguish parameters within this class; a proposed zero-location detector needs additional marked periods and a proved map from zeta to those data. The corpus theorem concerns `z²+c`, not arbitrary meromorphic flows near infinity.

`bottcher-pruefer-sem-monodromy-rh.md` already isolates an exact attempted realization: a natural transgression between the completed Euler–Maclaurin contour boundary and the dyadic Böttcher tower. Both the canonical coupling and its source trivialization remain open. `BottcherPrueferXiCharge.lean` proves only the multiplicity-character consumer; replacing its missing coupling by the arbitrary character `ζ_n^ord(Xi)` is explicitly a closed shortcut.

**Open target:** Construct an exact arithmetic realization or prove an obstruction for a precise proposed class. Audit existing Böttcher monodromy and hypertranscendence results before formulating that class.

**Differential-equation boundary:** `ZetaHypertranscendence.zeta_hypertranscendentalOver_gammaCoefficientField` excludes every nonzero finite algebraic differential equation for zeta over `ℂ(s)⟨Γ⟩`. Constant arithmetic periods are already in `ℂ`. Adding variable theta coefficients requires their differential-algebraic realization in the same upper-end meromorphic field; the available elliptic theta logarithmic-derivative theorem uses a different carrier. This does not exclude Mahler/q-difference realizations or special-value period relations.

## C. Two-place Krein reciprocity

`TheGluingFormulaAtEveryPlace.lean` gives the full index identity. Its state is defined on rational affine transformations: the successor term uses the p-adic norm, but `ratCorr` remains a global, archimedean-continuous dilation correlation. Compact Fourier support of local indicators does not establish compact support or even p-adic continuity of this correlation.

**Conjecture C1:** Every p-adic principal-unit neighborhood, viewed as a subgroup of positive rational slopes, retains the entire negative index of `ratCorr`.

**Paper mechanism:** Weak approximation for the inequivalent real and p-adic absolute values makes each principal-unit group dense in positive real slopes. Its logarithms are therefore dense in ℝ. `negIndex_orbitKernel_comp` then preserves the exact zero-count index. This proves an obstruction to removing negative squares by localizing slopes; it does not exclude a genuinely global two-place argument.

**Positive survivor:** Exact preservation of the spectral index at every p-adic resolution, rather than merely failure of one continuity estimate. Formalization in progress. The separate conjecture that `ratCorr` has no p-adically continuous extension remains to be proved.

**Strengthening C2:** Every principal-unit neighborhood approximates every global value of `ratCorr`. Since its coprime mixed difference is nonzero, a fixed positive oscillation survives in all such neighborhoods. This would rule out p-adic continuity at the identity unconditionally, including under RH.

**Next boundary C3:** The same index and value preservation should hold for any finite intersection of principal-unit neighborhoods at distinct primes, by simultaneous weak approximation. This concerns finite adelic localization; imposing unit conditions at every prime leaves only the positive rational slope `1`.

## Gates

- [x] Scope: three approaches, confirmed by user.
- [ ] Dependency-closed paper proofs of new results.
- [ ] Lean formalization, direct file checks, transitive axiom audits, umbrella imports.
- [ ] Positive survivor audited before any route retirement.
