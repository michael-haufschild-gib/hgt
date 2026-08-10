# Route U crossing law — reconnaissance and attack typing

- **ID:** ULF-FIELD-6
- **Stage:** 1-in-progress
- **Type:** TYPED ATTACK ANALYSIS on a named frontier source theorem (map §10, chain 4)
- **Parents:** rh-current-frontier-map.md (Route U dossier); in-tree anchors read this
  session: `XiShiftedHankelFirstCrossing.lean`, `XiShiftedHankelBoundaryHilbertChargeFlow.lean`
  (through line ~1075), `XiShiftedHankelBoundaryExtensionClass.lean`,
  `XiShiftedHankelAdmittedGammaLorentzLanding.lean` headers
- **Status:** [RECON COMPLETE] [TYPED NO-GO DERIVED] [ODD GENUINE CROSSING LEAN-PROVED]
  [HYPERBOLIC SOURCE PLANE LEAN-PROVED] [OFF-CRITICAL NEGATIVE-INDEX AMPLIFICATION LEAN-PROVED]
  [FOLDED-NODE RANK LEAN-PROVED] [FIXED CASSINI ALL-JET BRIDGE LEAN-PROVED]
  [SOURCE INDEX EXCLUSION OPEN] [NOT RH]

## The open core, read from the tree (exact)

For every `y>0`, at a genuine two-sided right-hand first crossing with null datum c
(head block PosDef, face singular, c ≠ 0, last coordinate ≠ 0), with
P = finiteHankelNullMonicPolynomial c (real simple roots, flat quadrature — in-tree):

the now Lean-closed determinant parity law adaptively selects `m>=0` and proves

    CROSSING CONSEQUENCE:  L_y(X·(P X^m)²) < 0,

with every lower flat-shadow defect through degree `2n+2m` equal to zero. Therefore the sole
surviving obligation is the crossing-conditioned exclusion

    OBLIGATION:  0 <= L_y(X·(P X^m)²).

The two statements contradict directly. For `m=0`, this is the original ordinary-contact
consumer `not_xiShiftedHankelFirstCrossing_of_primeArchPair_pos`; higher stationary contacts no
longer require a separate even branch. Strict positivity is sufficient but no longer necessary.

Lower constraints now have a closed polarized form. For `P_j=P X^j`, every pairing with
`i+j<2m+1` vanishes, while every pairing on `i+j=2m+1` equals same first defect `delta<0`.
Consequently `A=P X^m` and `B=P X^(m+1)` have exact completed-source Gram determinant
`-delta^2<0`. Viable source proof must exclude birth of this hyperbolic plane after flat isotropic
flag; controlling only marked scalar discards most adaptive crossing data.

The critical/off-critical split strengthens this again. Odd contact annihilates every square
`(P Q)^2`, `deg Q<=m`. Any finite critical-line prefix with more than `n+m` distinct shifted nodes
makes its critical restriction strictly positive, so the complete off-critical restriction is
strictly negative on `P · Poly_{≤m}`. Thus a genuine crossing forces an `(m+1)`-dimensional
off-critical negative sector, not only one hyperbolic plane. The negative sector localizes to a
finite FE--Schwarz quartet completion. Its support contains at least `m+1` distinct
conjugation-folded shifted nodes, so multiplicity, quartet duplication, and collisions cannot pay
the index. If a finite packet covers the divisor, its folded-node image has cardinality greater
than `m` (hence `m<#copies`); the former `m<2·(#copies)` annihilator bound is strictly weaker.

Folded-node equivalence is independent of nonnegative mass shift. More strongly, put
`Psi=xiSquaredSeamCassiniSource`. For every `y>0` and every `n`, Lean now proves

    -2 D^n(logDeriv Psi)(1-y) = n! xiShiftedReciprocalMoment(y,n).

Thus mass flow is exact translation of the basepoint of one fixed source. The full Hankel block,
all lower flat defects, polynomial functional, and crossing-conditioned negative form transport
identically; no phase-changing quadratic-form congruence is involved. The `41/2` restriction belongs
only to the optional prime--Gamma wrapper, not the Cassini-source crossing law. This still does not
finish the sign problem: a bare zero Cassini-orbit cap is RH itself. Remaining theorem must derive
odd-contact exclusion from special analytic/arithmetic structure of this source at its zero-free
real centers.

Canonical redundant-frame analysis also removes critical-line tail control from the open core:
critical-line capacity is automatically summable and finitely absorbable for every fixed frame.
Only signed off-critical capacity/index remains.

Structural reading (from the flat-quadrature layer): at a first crossing the truncated moment
sequence has a unique flat finitely-atomic representing quadrature with atoms at the roots of
P; X·P² vanishes at every atom; so L_y(X·P²) is exactly the FIRST UNSEEN moment discrepancy —
the true source sequence's next odd moment minus the value forced by its own degenerate
quadrature. If the first discrepancy is delayed by `2m` extra flat jets, the lifted reporter
`P X^m` exposes it as `L_y(X(P X^m)^2)`. Determinant sign change forces odd delay and negative
orientation. The remaining obligation says this self-selected Stieltjes reporter cannot be
negative for the completed prime–Gamma source at its own hypothetical degeneration.

## Typed no-go (derived this session): the unrestricted strengthening is group-3

**Claim.** The statement "L_y(X·P²) > 0 for EVERY nonzero real polynomial P, for every y in
the window" is equivalent to RH — hence inadmissible as a proof target.

*Derivation.* (⇐) RH gives the route's shifted-Hankel positivity (far-right positivity
extends; no crossing exists), and a strictly positive-definite Stieltjes-type functional has
L(X·P²) > 0 for all P. (⇒) Unrestricted odd-block positivity over the window excludes every
right-hand first crossing for every face dimension (the consumer theorem applied at each
crossing needs only its null P, a special case); by the route's Lean-closed architecture
("excluding every right-half first crossing proves required shifted-Hankel positivity and
RH"), RH follows. ∎

**Consequence (the typing).** Any admissible attack must consume the first-crossing
constraint ESSENTIALLY — the constraint that P is the null polynomial of an actual singular
face of the same functional (equivalently: the statement to be proven is vacuous under RH and
must be established as a self-destruction law for impossible configurations, from the
unconditional source side). Approaches that prove dominance for a P-class defined without
reference to the functional's own degeneration (all real-rooted P, all P with roots in a
fixed set, fixed corona/reporter classes) either prove group-3 statements or fall into the
route's recorded dead subclasses — which this typing now explains uniformly: every listed
dead subclass (generic moment positivity, positive atoms, tied-power sectors, root location,
stochastic order, factorial carriers, fixed corona reporters, Gamma lifetime, three-point
positivity, reflection aggregation) is a fixed-face or unrestricted-class mechanism.

Field consilience (recorded, no claim of novelty): this is the Θ2/Θ4 pattern at the U face —
fixed proper faces are blind; the crossing datum is the "future-sensitive reporter" the
frontier map's design survivor demands; U's obligation has exactly the admissible shape.

## What a viable attack must therefore look like (open directions, honestly unproven)

1. **Self-referential moment identity:** express `L_y(X·(P X^m)²)` at a singular face through the
   face's own quadrature data (nodes = roots of P, weights from the head block) plus the
   source-side tail — seek an identity in which the prime discrepancy's pairing against X·P²
   is constrained BY the degeneration itself (the crossing forces exact relations among
   moments up to 2n+2; the discrepancy at 2n+3 may inherit a sign from the source's
   completed structure. The lower-defect annihilation through `2n+2m` is now mandatory input, not
   optional decoration; any estimate ignoring it discards the adaptive information that selected
   `m`.
   Exact strengthened target: prove zero-free-real-center jet rigidity for the fixed Cassini
   source—its normalized log-derivative jets cannot have all adaptive lower Padé defects zero and
   the first odd shifted-square defect negative. Full transport is now exact; remaining work is to
   exploit source structure, not control mass-shift distortion.
2. **Window structure:** the constant 41/2 bounds the shift window — locate its origin in
   `XiShiftedHankelBoundaryQuadratureSource` (likely tied to the first Xi zero's scale or the
   negative-binomial parameter) before any estimate; an attack valid only in a sub-window is
   still a typed contribution if the consumer accepts it.
3. **Route T cross-check (secondary target, recorded):** T's open core (cofinal cancellation
   of centered von Mangoldt atoms via exact joint pairing before norms) is E1-class
   oscillatory transport; the corpus's formalized modulus-first cap bars norm-first
   approaches; this program has no mechanism for T beyond what the corpus records — T stays
   secondary with no claim.

## Log

- 2026-08-09 — recon of U anchors executed; open core stated exactly from the tree; the
  unrestricted-strengthening group-3 no-go derived and recorded (the cycle's typed
  contribution); admissible-attack shape typed; next reads named
  (`SquaredXiCompleteMonotonicity`, `XiShiftedHankelBoundaryQuadratureSource`). No Lean.
- 2026-08-09 — heavy conjecture loop exposed and paper-proved the higher-contact replacement:
  `../../3-formalized/mass-shifted-pade-contact-parity-law.md`. A full right-positive crossing
  has an earliest nonzero flat-quadrature Padé defect `delta_(2n+d)` with forced sign
  `(-1)^d delta_(2n+d)>0`. The current flux is only `d=1`; stationary contacts require the new
  alternating hierarchy. Frozen source target `(U-Pade)` asks the completed prime--Gamma source
  for the opposite sign at the adaptively selected first defect.
- 2026-08-10 — determinant attack closed the geometric gap in Lean. The actual determinant germ
  has the same first order as the first flat defect; head PosDef persists automatically; a genuine
  two-sided loss has odd order `2m+1`; and the completed source then satisfies
  `L_y(X(P X^m)^2)<0`. Even/Hamburger contact is impossible. Route U now has one exact open core:
  exclude this negative adaptive shifted square using its own lower-defect constraints.
- 2026-08-10 — full delayed-contact polarization closed in Lean: lifted flag pairings vanish below
  first odd anti-diagonal, first anti-diagonal equals defect, and every genuine crossing creates a
  prime--Gamma hyperbolic two-plane with determinant `-delta^2<0`. Open core sharpened from scalar
  sign to source exclusion of one-index Krein birth after an adaptive flat flag.
- 2026-08-10 — canonical redundant frames, exact leverage/relative-trace laws, and finite positive
  absorption removed all critical-line capacity from the hypothesis. A no-crossing criterion now
  depends only on subunit off-critical canonical capacity.
- 2026-08-10 — arbitrary-multiplier null identity upgraded the lifted flag to the complete space
  `P · Poly_{≤m}`. Its critical restriction is positive definite and its off-critical restriction
  negative definite. Finite off-critical support obeys contact ceiling `m<2|T|`. Open core is now
  signed off-critical negative-index exclusion.
- 2026-08-10 — finite negative-sector localization strengthened to arbitrary extensive
  completions, then specialized to explicit FE--Schwarz quartet completion. One atom contributes
  one negative coordinate only after quotienting by the conjugation fold
  `(Re z,|Im z|)`; every odd contact needs at least `m+1` distinct folded nodes. Sharp finite-cover
  ceiling is `m<#folded(T)<=|T|`.
- 2026-08-10 — folded-node equivalence and finite count proved invariant under every nonnegative
  mass shift. Adaptive Route-U orbit rank now lands exactly at fixed shift-one Cassini coordinates;
  remaining source theorem must preserve crossing negativity, not merely count Cassini orbits.
- 2026-08-10 — exact all-jet bridge proved: every positive-mass shifted moment is a normalized jet
  of one fixed Cassini source at `1-y`. Hankel blocks, flat defects, polynomial functionals, and
  genuine-crossing negativity now transport identically and without the prime--Gamma window.
- 2026-08-10 — degree-one conjecture loop survived proof audit. For `F(y)=Re M_y(0)`, Lean proves
  `det H_2=-(F^3/2)(1/F)''` and identifies terminal flux with `F^2(1/F)'''/6`. On `y=t^2<1`,
  `1/F=t*thetaCuspHyperbolicPartition/thetaCuspHyperbolicFlux`; the quotient's first three named
  jets are actual derivatives. A flat-negative first face is exactly the source event
  `tq''=q'` with `q'''<0`. Next admissible first-minor target is contact-only rigidity
  `tq''=q' -> q'''>=0`, not unrestricted Hankel positivity.
- 2026-08-10 — degree-one contact was pushed completely into theta cumulants. With
  `A=thetaCuspHyperbolicFlux/thetaCuspHyperbolicPartition`, Lean differentiates `A` through the
  fourth cumulant and proves `N=-A^2-tAA'-t^2AA''+2t^2(A')^2=-8t^6 det H_2`. The displayed
  mean--variance--third--fourth-cumulant flow is `N'`; on `N=0`, it equals `tA^3q'''`. Hence the
  exact first-minor source obstruction is `N=0,N'<0`, and the smallest closing theorem is
  `N=0 -> N'>=0`.
- 2026-08-10 — conjecture C54-A (inverse-response concavity for every even log-concave law) failed
  exactly, not numerically.  For the symmetric three-point law with center/side mass ratio `r`,
  `q(y)=r sqrt(y)/sinh(sqrt(y))+sqrt(y)coth(sqrt(y))` has
  `q''(0)=(7r-8)/180`; every `r>8/7` gives the wrong curvature.  Generic log-concavity therefore
  cannot close the theta contact, and no such theorem is imported.
- 2026-08-10 — C54-B/C55 survived proof audit and is Lean-closed in
  `XiShiftedHankelCassiniContactFourthCumulant.lean`.  With elasticity `e=tA'/A`, contact eliminates
  the third cumulant and factors the exact flow as
  `N'=3A^2/t(1-e)(1-2e^2)-t^2 A K4`.  A new variable-shift `85`-to-`4` resolvent contraction,
  derived only from the critical strip and first-zero height gap, proves `77/85<e<1` for every
  `0<t<1`; hence the geometric factor is always strictly negative.  The same contraction proves
  the third and fourth theta Esscher cumulants are strictly negative throughout the strip.  This
  rules out positivity-only and generic PF2/log-concavity closures: remaining degree-one theorem is
  a quantitative *negative* fourth-cumulant reserve at the self-selected contact, not a cumulant
  sign.  Module is wired through `RHTower.lean` and passes direct `lake env lean`.
- 2026-08-10 — C56 killed the sector-only fourth-cumulant closure and extracted its sharp positive
  survivor.  For one positive real reciprocal atom `c` and one conjugate pair `1±is`, exact
  degree-one contact has total pair weight
  `q=c C/((1+s^2)s^2)`, `C=c^2+2(s^2-1)c+1-3s^2`, and terminal flux
  `c C ((c-1)^2+s^2)/(c-1+s^2)`.  Thus for positive contact weight its sign is exactly
  `sign(c-1+s^2)`: angular sector control discards the decisive relative radial scale.  The exact
  narrow-sector packet `c=1/2`, `s=1/6`, common pair weight `63/37` has positive first four
  moments, null root `31/34`, flat first minor, and terminal flux `-35/612`.  All claims are
  axiom-clean and directly compiled in
  `XiShiftedHankelCassiniOneOrbitContactOrientation.lean`, umbrella-wired through `RHTower.lean`.
  Remaining admissible degree-one theorem is therefore a source-conditioned cross-scale transport
  inequality, equivalently a positive-channel energy-barycenter lower bound; contact, cumulant
  signs, endpoint height, and sector width cannot supply it alone.
- 2026-08-10 — C57 converted C56's radial comparison into an exact Xi height law and closed it in
  Lean.  For denominator `A+iB`, pair intrinsic velocity is
  `(A^2-B^2)/(A(A^2+B^2))`; a critical atom at height `eta` is adverse exactly when
  `eta^2>A-y+2AB^2/(A^2-B^2)`.  For a Xi orbit with centered displacement `delta` and ordinate
  `gamma`, this threshold is
  `gamma^2-delta^2+8A delta^2 gamma^2/(A^2-4delta^2 gamma^2)`.  The second term is strictly
  positive for every genuinely off-critical orbit: horizontal phase displacement imposes a
  positive radial phase tax.  Thus low critical zeros stabilize while high critical zeros drive
  adverse orientation; fixed-sector estimates erase exactly this ordering.  Module
  `XiShiftedHankelCassiniPhaseTaxHeightThreshold.lean` is umbrella-wired and passes direct
  `lake env lean`.  Remaining source theorem must control a contact-weighted height barycenter
  relative to orbit-dependent taxed thresholds.
- 2026-08-10 — C58 lifted degree-one contact from moments to a literal countable interaction
  network.  For every absolutely summable complex packet through fourth power, ordered pair
  energy `E_ij=z_i z_j (z_i-z_j)^2` and transport `E_ij(z_i+z_j)` satisfy
  `sum E_ij=2(m0*m2-m1^2)` and
  `sum E_ij(z_i+z_j)=2(m0*m3-m1*m2)`.  Lean specializes both identities to the full
  multiplicity-exact Xi zero-copy divisor.  At an actual flat face total pair energy is exactly
  zero, while total transport is exactly twice positive response times terminal flux.  Thus a
  negative crossing is a zero-energy signed network whose energy barycenter moves adversely;
  source closure must constrain cross-pair transport, not individual atom angles or cumulant
  signs.  Module `XiShiftedHankelCassiniPairEnergyTransport.lean` is umbrella-wired and passes
  direct `lake env lean`.
