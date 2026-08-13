# Mass-shifted adaptive terminal-source resistance law

- **ID:** MSST-ATSR-1
- **Stage:** 3-formalized
- **Type:** THEOREM / SHARP NO-GO BOUNDARY
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, after the vacuum-free
  hard-edge source-capacity/worldline law
- **Statement:** The literal current/adjacent completed `P^sharp` producer induces a canonical
  probability law on all current Gauss roots.  Each probability share times the source terminal
  product is exactly previous norm times the fourth hard-root monomial.  This turns terminal-mass
  escape into one precise admission-dependent loss of tightness, but supplies no selected-root
  floor without a further arithmetic localization theorem.

## Goal

Replace the residual positive-terminal-mass/zero-terminal-mass dichotomy by an exact all-root law
formed from current and adjacent admissions before reflection aggregation.  Determine whether that
law prevents source loss at the selected hard root or only classifies the remaining escape.

## Gates

- [x] 0 → 1 in-progress: conjecture frozen after corpus and hostile-route audit
- [x] 1 → 2 fully-proven: complete paper proof and exact no-go survivor
- [x] 2 → 3 formalized: Lean source, umbrella wiring, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone novelty audit not claimed

## Conjecture loop

### C1 — fixed-corona landing

**Conjecture.** Inject the fixed Gamma corona into a finite hard-edge ground mode and use
surjective erasure to contradict nonzero critical survival.

**Failure.** Existing corpus proves every product-continuous Hausdorff linear reporter on the fixed
corona is zero, while the corona itself is infinite-dimensional.  A finite Hankel face can only be
an observation, not a faithful source carrier.  Any surviving producer must be admission-indexed
and formed before reflection, rather than a fixed map out of the corona.

### C2 — reciprocal terminal resistance

Let `P_n` be the current monic orthogonal admission, let `x` run over its simple Gauss roots, let
`lambda_x` be the Christoffel/Gauss weight, and put `h_j=L(P_j^2)`.  Define

\[
 r_x:=\frac{\lambda_xP_{n-1}(x)^2}{h_{n-1}}.
\]

**Proof route.** Gaussian exactness applied to `P_(n-1)^2` gives

\[
 \sum_{P_n(x)=0}\lambda_xP_{n-1}(x)^2=h_{n-1},
 \qquad r_x>0,
 \qquad \sum_xr_x=1.                                      \tag{ATSR.1}
\]

Confluent Christoffel--Darboux and the three-term recurrence give the equivalent current/adjacent
forms

\[
 r_x=\frac{P_{n-1}(x)}{P_n'(x)}
     =-\frac{P_{n+1}(x)}{\beta_nP_n'(x)},
 \qquad \beta_n=\frac{h_n}{h_{n-1}}>0.                  \tag{ATSR.2}
\]

Thus `r_x` is not a fixed observer coordinate.  It is selected by the current and adjacent
admissions on the same moving face.

### C3 — source-terminal probability landing

Let `C_x^circ` be endogenous effective capacity of the literal two-amplitude vacuum-free completed
`P^sharp` source, let `rho_x=lambda_x/x` be absolute Padé residue, and let

\[
 \Gamma_x:=\rho_x C_x^\circ
           =y x^4\lambda_xP_n'(x)^2
\]

be hard terminal source product.  Combining (ATSR.1) with confluent Christoffel--Darboux yields

\[
 \boxed{\quad r_x\Gamma_x=y x^4h_{n-1}.\quad}             \tag{ATSR.3}
\]

Where every displayed terminal product is nonzero, the all-root nonlinear aggregate is

\[
 \boxed{\quad
   \sum_{P_n(x)=0}\frac{y x^4h_{n-1}}{\rho_xC_x^\circ}=1.
 \quad}                                                   \tag{ATSR.4}
\]

This is an arithmetic source law: current/adjacent amplitudes form `C_x^circ` before completed
aggregation, and the resulting terminal products are normalized only afterward by their own
admission shares.  No orientation map or fixed linear reporter occurs.

### C4 — selected hard root has a uniform share floor

**Conjecture.** The root selected by hard-edge renewal satisfies `r_x >= c > 0` uniformly.

**Failure.** Already for two ordered roots `a<b` and an interlacing previous root `alpha`,

\[
 P_2=(X-a)(X-b),\qquad P_1=X-\alpha,
 \qquad r_a=\frac{\alpha-a}{b-a},\qquad
 r_b=\frac{b-\alpha}{b-a}.
\]

Choosing `alpha=a+theta(b-a)` realizes `(r_a,r_b)=(theta,1-theta)` for every `0<theta<1`.
Therefore orthogonal interlacing and probability conservation alone allow a selected share to
collapse arbitrarily.  Any pointwise lower bound must use literal shifted-Xi arithmetic or a
source-defined selection theorem.

## Novelty and literature audit

- Generic identities (ATSR.1)--(ATSR.2) are classical Jacobi/Gauss spectral-measure facts and are
  not claimed as new.  Van Assche's majorization theorem explicitly connects consecutive zeros by
  Christoffel-number doubly stochastic weights.
- Corpus search found no theorem coupling those shares to the admission-sensitive vacuum-free
  mixed/completed `P^sharp` capacity, terminal mass, and moving hard chart as in (ATSR.3)--(ATSR.4).
  This route-specific fusion is `[NOVELTY UNVERIFIED]` until a wider publication audit.
- Current 2025 elliptic Christoffel--Darboux work extends kernel/recurrence structure but does not
  provide the shifted-Xi completed-source coupling or a selected hard-root share floor.

## Exact remaining burden

Equations (ATSR.1)--(ATSR.4) eliminate unspecified terminal loss.  Remaining obstruction is one of:

1. **admission localization:** prove selected false-RH hard root retains positive `r_x`;
2. **nonproper diffusion:** show `r_x` cannot disperse through `n asymp sqrt(y)` roots;
3. **arithmetic compactness:** identify a shifted-Xi source moment forcing an atom in the limiting
   resistance measure;
4. **zero-terminal radical branch:** if the selected share collapses, use its exact adjacent/current
   ratio in the parity-doubled contact flag rather than another orientation map.

## Verification plan

1. [x] Formalize finite Gauss terminal shares, positivity, total mass one, confluent ratio, and
   current/adjacent expression in `HTGeometry`.
2. [x] Formalize pointwise source product (ATSR.3) for generic and literal shifted-Xi vacuum-free
   capacities in `RHTower`.
3. [x] Formalize all-root aggregate (ATSR.4) in a division-free form first; add quotient form only under
   proven nonvanishing.
4. [x] Formalize exact two-root collapse boundary.
5. [x] Wire umbrellas; run `lake env lean` per new file, one final targeted `lake build`, axiom audit,
   and stale-process check.  No numerical computation.

## Formal theorem inventory

`HTGeometry/GaussTerminalSourceResistance.lean` proves:

- positive normalized terminal shares and total mass one;
- preceding/current-derivative and current/adjacent-derivative ratio coordinates;
- equality of preceding and adjacent share constructions;
- exact two-root affine realization of every share, hence no uniform selected-share floor from
  interlacing alone.

`RHTower/XiShiftedCanonicalAdmissionTerminalSourceResistance.lean` proves:

- generic division-free source fusion (ATSR.3);
- generic reciprocal all-root conservation (ATSR.4) under exactly necessary nonvanishing;
- literal shifted-Xi positivity and probability conservation;
- literal Padé-residue/vacuum-free completed-capacity fusion and reciprocal aggregate;
- current/adjacent canonical-admission ratio and unconditional division-free capstone.

Both modules pass direct `lake env lean` checks and targeted `lake build`.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  Repository lint reaches both new modules but remains
red because unrelated concurrent RHTower modules are not yet wired into their umbrella; no new
module or forbidden declaration from this card appears in lint failures.

## Log

- 2026-08-13 — card opened.  Fixed-corona landing rejected from existing topology and
  infinite-dimensionality theorems.  Source-resistance probability law frozen; selected-root floor
  falsified by exact two-node interlacing family.
- 2026-08-13 — paper proof dependency-closed and formalized.  Added division-free rootwise fusion,
  quotient aggregate under nonvanishing, literal shifted-Xi specialization, exact ratio coordinates,
  and sharp two-node nonuniformity boundary; wired both theorem-area umbrellas.
