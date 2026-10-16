# Contribution 019: original-topology native density

Status: **FORMALIZED, AUDITED — 19/100**. One structural contribution combining
HF original source synthesis and topology with RN actual native range and
finite convolution solvability.

The unconditional theorem `RHTower.deningerMeyerFiniteNativeModes_dense` proves
that actual finite native full-multiplicity Xi modes are dense in the original
strong Meyer-cohomology topology. Entire divided-difference contour blocks
retain whole Xi germs; grouped contour control gives a convergent series in
all original source gauges. Global Xi synthesis identifies its class, and
Gaussian source removal reaches every original forcing.

`RHTower.deningerMeyerOriginalConvolution_nativeApproximation` gives finite
native forcing/solution pairs for EVERY original source symbol and forcing:
the repaired equation is exact at each stage, and both sequences converge in
the original quotient topology to the original forcing and its unique repaired
solution. This removes the original-Frechet finite-mode approximation obstacle.
It is not an arbitrary infinite-packet admission or a native BV convergence result.

Main source: `formal/GaloisForLFunctions/RHTower/DeningerMeyerFiniteNativeDensity.lean`.
All eleven leaves passed direct `lake --old env lean` audits with fresh oleans;
all eleven umbrella imports are unique. All 76 public declarations passed the
exhaustive axiom audit using only `propext`, `Classical.choice`, `Quot.sound`.
Global formal lint passed, with only existing large-file warnings. Formal API,
gap and overview indexes and the Lean search index were refreshed. Exactly 16
owned scratch files were removed. No full or umbrella builds, new axioms,
proof placeholders, heartbeat changes, numerical experiments, commits or pushes.

Remaining: convergence of native BV representatives, prescribed arbitrary
infinite packets, compact-open topological identification, geometric cup/trace
identification, positive Hodge compatibility and directed prime--Gamma work sign.
Routine density, finite approximation and continuous-operator consequences
belong to this same contribution and must not be counted again.

## Research history (chronological)

Baseline: **18/100**. Previous goal turn classified as progress: all seven
018 source/artifact pairs are fresh, uniquely wired, and the current main
declaration and ledger agree. Goal attachment reread. The full objective is
100 separately justified structural contributions; no nineteenth result is
counted yet.

Mission: unconditional structural RH progress from current Lean evidence.
Continue hgtl7 conjecture/attack/paper-proof/formalization. No web, external
novelty checking, old research markdown, numerical experiments, subagents,
full or umbrella builds, heartbeat increases, commits or pushes. One owned
foreground Lean process at a time. Preserve unrelated concurrent work.
Serena memories checked; relevant 018 memory read. Architecture/testing docs
absent. No update_plan tool is available; this card is the durable plan.

Plan:
1. Search the full current corpus for original spectral topology, signed
   arithmetic operator decomposition and source-level boundary pairing.
2. Attack candidate conjectures for falsity, circularity, prior coverage and
   structural significance. No routine 018 word or forcing-domain corollary
   counts; the existing Hilbert inverse and integrating factor are baseline.
3. Finish a dependency-closed paper proof before new Lean; then sequential
   direct leaf audits, axioms, umbrella wiring, lint/index and exact cleanup.

Current audit boundaries: native BV solvability does not identify arbitrary
Hilbert packets with original sources and does not orient prime--Gamma work.
The map's major open cores are signed source control, original topology and
full arithmetic identification, not further spectral receivers.

Conjecture/attack log:
- A new compact smooth CHMD operator core is duplicate: current source now
  contains `CHMDCompactSmoothOperatorCore`. Do not count it or edit concurrent
  CHMD work. A global stationary conjugacy also cannot be inferred from its
  local bounded inverses: theta multiplication has no paid global inverse.
- Direct use of 017's horizontal interpolation on the Xi divisor fails its
  geometry: unitized Mellin zeros escape in real part, while Xi zeros stay
  in the critical strip. No arbitrary Xi packet admission follows.
- Gaussian removal in every original source gauge is ALREADY proved in
  `DeningerMeyerGaussianSourceApproximation`. It is an ingredient, not 019.
- Selected conjecture under attack: the actual finite causal Xi modes are
  dense in the ORIGINAL strong Meyer cohomology topology. The mechanism must
  control groups of full-multiplicity zeros, with no separation or simplicity
  assumption and no inference from Hilbert density.

Candidate mechanism (paper proof being checked):
For F the Mellin transform of an actual source, first take
F_e(s)=exp(e*s^2)*F(s), e>0. On a good rectangle Gamma_T with vertical sides
-1 and 2, define an entire projector kernel

  B_T(s)=(1/(2*pi*i))*integral_Gamma_T
    [F_e(w)/xi(w)] * dslope(xi,s,w) dw.

Here dslope(xi,s,w)=(xi(s)-xi(w))/(s-w), extended by xi' on the
diagonal. Its entireness avoids estimating separate residues or inverse
zero gaps. Cauchy gives B_T=F_e-xi*H inside the rectangle and B_T=-xi*H
outside. Hence every full Xi germ inside is preserved and every outside
germ vanishes. Source-native full-Xi synthesis and the existing finite causal
range classification turn B_T into an actual finite causal source class.

Choose good heights T_n in [N+4n,N+4n+1]. The difference B_(T_(n+1))-B_(T_n)
is a contour over two horizontal shells. The corpus's good horizontal Xi
ratios and its Gamma floor control 1/xi exponentially in height on these
contours; the vertical sides have the unconditional exterior floor. Gaussian
damping therefore makes the contour mass summable with every polynomial
height weight. Away from a shell, the Cauchy denominator is at least one;
near the shell, the rectangle maximum principle applied to the entire
difference gives the same control on a padded rectangle. The rapid strip
decay of xi pays all vertical weights outside the padded shell. Thus the
shell projectors are summable in every Mellin-strip weight, without any
bound on zero multiplicity or separation.

The resulting entire strip-regular sum has a literal inverse Mellin source;
line-integral gauge estimates give convergence in every original weighted
derivative seminorm. Its Xi jets equal F_e's, so global source-native Xi
synthesis identifies the limit class with the Gaussian-smoothed input.
Finally Gaussian removal puts every original class in the closure of the
finite causal modes. This is a topology theorem, not an arbitrary-packet
surjectivity assertion; it does not claim convergence of native BV amplitudes
or positivity.

Paper proof completed after the following checks:
- `PaperThetaConvolutionGauge.mem_meyerFiniteHedenmalmRange_iff` supplies the
  exact original-source finite native range from vanishing of all outside
  full jets. This is the RN/HF bridge used by the contour construction.
- `exists_xi_horizontal_ratio_nat_bound`, `xi_floor_two`, and the Xi
  functional equation pay both good horizontal sides and both fixed vertical
  sides. `deningerMeyerXiQuotient_verticalExponential` already uses precisely
  these source inputs; it is not being assumed for a meromorphic quotient.
- Each shell contour has bounded length because adjacent chosen heights are
  between three and five apart. Its ratio mass is bounded by a fixed
  polynomial times exp(-e*T_n^2+C*T_n). For a strip |Re s|<=r, use a padded
  rectangle of width max(r,3)+1 and one extra unit above/below the shell.
  Every point on that boundary is distance at least one from the integration
  contour. Cauchy's outside identity bounds the entire shell projector there;
  the rectangle maximum principle fills the padded rectangle. Outside it the
  same outside identity applies directly. Xi's own strip-Schwartz bounds pay
  vertical weights outside the shell; inside, the weight costs at most a
  polynomial in T_n. Thus every weighted-strip seminorm is eventually bounded
  by 2^(-n). No estimate of an individual residue is needed.
- `DeningerMeyerStripSeries` constructs the entire strip-regular sum and
  passes every derivative to the limit. The difference quotients are
  holomorphic uniformly under finite contour integration: analyticity of
  dslope in either variable, symmetry, and a derivative bound on a containing
  compact ball give the local domination required by
  `differentiableAt_integral_of_cauchy_dominated`.
- For strong inverse-Mellin convergence, the weighted-strip tail at weight
  n+2 controls the nth derivative's vertical line integral by an integrable
  multiple of (1+y^2)^(-1). The tail of the common summable majorant tends
  to zero. Apply `deningerMeyerInverseMellinSource_gauge_le` for every integer
  line and derivative order. This supplies the ORIGINAL source topology,
  not only compact-open convergence. Continuity of the actual quotient map
  then gives the same convergence in cohomology.
- Every fixed Xi germ lies inside Gamma_(T_n) eventually. Locally uniform
  derivative convergence therefore preserves its exact full germ. Global
  source-native Xi synthesis identifies the limiting class with the smoothed
  input; Gaussian source removal gives density for every original class.

Verdict: **SURVIVES PRELIMINARY ATTACK**. All paper steps are now dependency
closed. The new insight is the entire divided-difference contour projector,
which controls whole divisor groups and their original source seminorms
without zero separation, simplicity, or an arbitrary infinite-packet premise.
Formalization starts only after this proof. The intended capstone is density
of the union of actual finite Hedenmalm/Meyer ranges in original strong
cohomology, with finite native approximations of continuous original-source
solution operators as a consequence. No arbitrary BV spatial convergence or
original-topology/compact-open equivalence is claimed.

Search record: first topology/operator/boundary deep reports and targeted
Meyer/CHMD reports were non-partial with no errors (about 72.8k files, 1.079M
declarations; compiler coverage largely pending/stale/source-only). The broad
contour report timed out partially in text/source/semantic retrieval; its
available hits were retained. Source verification, not retrieval rank or
compiler metadata, determines applicability.

Formalization progress (still **18/100**, no completion claim):
- `HTGeometry/EntireDividedDifferenceContour.lean` and
  `HTGeometry/DividedDifferenceCauchyProjection.lean` pass direct leaf Lean
  audits. They prove entireness through the moving diagonal and the exact
  inside/outside Cauchy identities. No individual zero residues are used.
- `RHTower/DeningerMeyerSourceSeries.lean` is under its first direct audit.
  The source convergence step simplifies using existing original Frechet
  completeness: summability of every defining gauge gives source summability.
  A weighted Mellin-line bound pays each gauge. Continuous Mellin jets then
  pass the full germs directly to the source sum, avoiding an intermediate
  compact-open reconstruction limit.
- The same paper proof can use the central rectangle and disjoint upper/lower
  shell rectangles as separate summands. Each Xi germ belongs to exactly one
  block. Finite sums have finite full-Xi support by the existing band-finiteness
  theorem. Telescoping is optional and not needed for density.
- Additional owned scratch: `/tmp/hgt_rh019_topology_api.lean`.
  Original `/tmp/hgt_rh019_api.lean` remains for exact cleanup. Eight owned
  search JSON files remain. No subagents or full builds have been run.

Further progress:
- `DeningerMeyerSourceSeries.lean` now passes: gauge summability implies actual
  source summability; one weighted Mellin line controls each original gauge.
- `DeningerMeyerXiContourBounds.lean` now passes. For each strip and weight,
  a single Xi constant controls EVERY block by its contour quotient, boundary
  length and a polynomial height weight. The padded-rectangle maximum principle
  removes the interior cluster singularities. This is an ingredient, not a
  counted estimate contribution.
- `DeningerMeyerXiContourSource.lean` is written and under first direct audit:
  actual inverse-Mellin source, exact inside full jets, exact outside zero jets.
- Remaining work: actual good-height sequence and Gaussian quotient control;
  summability of its disjoint blocks; finite native range membership; original
  cohomology density; audits, umbrellas, lint/index, cleanup, ledger/map/memory.
- Additional owned scratch: `/tmp/hgt_rh019_contour_api.lean`.
- An elementary simplification avoids quantitative asymptotic machinery:
  Gaussian regularization of the entire function `exp(-i*B*s)` supplies arbitrary
  weighted bounds for `exp(B*t-e*t^2)`. These imply eventual block domination by
  `(n+1)^(-2)` along heights above `n`. The same summable majorant works for every
  strip and derivative weight. No numerical calculation is involved.

Current owned module status:
- Passed direct audits: `EntireDividedDifferenceContour`,
  `DividedDifferenceCauchyProjection`, `DeningerMeyerSourceSeries`,
  `DeningerMeyerXiContourBounds`, `DeningerMeyerXiContourSource`,
  `DeningerMeyerGaussianContourMass`.
- `DeningerMeyerXiContourHeights` is under first audit; it constructs actual
  spaced good heights from the existing horizontal-ratio theorem.
- `DeningerMeyerXiContourQuotient` is written but not yet audited. It currently
  contains contour geometry, zero-freeness and inverse-Xi control. Append the
  Gaussian Mellin input quotient theorem before its final audit.
- No new leaf has been wired into an umbrella yet. No nineteenth contribution
  is counted. Existing passes remain ingredients until original density closes.

Latest status:
- Heights and Quotient now pass direct audits. The latter proves the actual
  Gaussian Mellin-input quotient bound on both shell borders, using the good
  height floors and the fixed-edge Xi floor.
- `DeningerMeyerXiContourSeries.lean` is under first audit. It defines central
  block 0 and upper+lower shell block n+1, proves each is original strip-regular,
  and proves weighted eventual domination by the common majorant and actual
  source summability. No axiom or placeholder is present in the written code.
- `/tmp/hgt_rh019_density_api.lean` has been created but not run yet. It checks
  the Nat.find, continuous series, closure and finite-native range interfaces
  needed for the capstone. Total owned API scratch: api, topology_api,
  contour_api, density_api (all prefixed hgt_rh019_).

Capstone implementation plan:
1. Add a germ/partition leaf after Series. Prove schedule height StrictMono
   directly from upper/lower offset bounds. Xi roots cannot have absolute
   ordinate equal to any scheduled height (`horizontal_ne_zero`, plus
   `xi_eq_zero_of_mem_divisor_support rho`). Choose the least n with
   abs(im rho) < height n using Nat.find; it exists from height_ge and
   exists_nat_gt. Block n preserves the full input germ and all other blocks
   vanish there. For n=0 use central rectangle; for n=k+1 choose the positive
   or negative shell according to the root ordinate. Inside/outside jet laws
   are already paid in XiContourSource.
2. Continuity of `deningerMeyerStrongLogMellinJetCLM` passes the summable source
   series to every full jet. `tsum_eq_single` identifies its jet with the input.
   `deningerMeyerCohomology_eq_of_XiJets_eq` identifies the source sum class with
   the Gaussian-smoothed input class.
3. Every natural finite head lies in actual native range for
   `(xiSupportsUpTo_finite (height N)).toFinset`: outside that set every block
   in range N has zero full jets, and jet evaluation is linear. Use exactly
   `PaperThetaEndpoint.mem_meyerFiniteHedenmalmRange_iff`.
4. Quotient continuity and source summability put each Gaussian class in the
   closure of the finite native ranges. Existing Gaussian source removal puts
   every original class in that closure. State the unconditional Dense theorem.
5. An original-topology finite-solution approximation result for the existing
   repaired convolution inverse can demonstrate the new solution class, but
   is part of this ONE contribution. No BV/native amplitude convergence claim.
6. Then final leaf/axiom audits, unique umbrella imports, lint/index, exact
   scratch cleanup, formalized card, ledger19/map/memory. Keep goal active100.

Latest audit update:
- `DeningerMeyerXiContourSeries` passes, including actual ORIGINAL source
  summability of the Gaussian contour blocks. Nine owned leaves now pass.
- `DeningerMeyerXiContourGerms` is written, not yet audited. It contains the
  generic band jet formula, strict monotonicity of heights, block-window jet
  formula and unique block membership of each actual Xi root via Nat.find.
- Density API scratch is now running. Next: audit Germs, then add the capstone
  density/finite-solution approximation leaf. No umbrella wiring/count yet.
- Exact finite inverse invariance is available in
  `PaperThetaConvolutionFredholm.meyerFiniteConvolutionInverse_mem`; this source
  was read in full. Together with the existing continuous original inverse,
  density gives finite native solutions converging in original cohomology for
  EVERY original forcing and EVERY original convolution kernel. Native BV
  amplitude convergence is not asserted.

Capstone draft update:
- Density API finished. The actual sequence interface is
  `mem_closure_iff_seq_limit` (not Dense.exists_seq_tendsto). `map_tsum`,
  `HasSum.tendsto_sum_nat`, Nat.find_min/spec, native range iff and band finiteness
  interfaces were verified. Exploratory API errors are only absent candidate
  names; the scratch files are not project leaves and will be removed.
- Germs is under first direct audit.
- `DeningerMeyerFiniteNativeDensity.lean` has been written but is NOT audited.
  It contains continuous-jet identification of the source sum, native finite
  head membership, Gaussian closure, and the closed unconditional theorem
  `deningerMeyerFiniteNativeModes_dense`. Final finite-solution approximation
  corollary remains to add after density checks.
- Serena symbol lookup was attempted for the original inverse continuity
  theorem and rejected because the formal path is ignored. Source rg/reads
  remain the available fallback for Lean symbols.

Integration update:
- Germs now passes. The full-multiplicity block partition is verified.
- All TEN passed ingredient leaves are uniquely wired into HTGeometry/RHTower
  umbrellas. No umbrella build was run.
- FiniteNativeDensity is under its first direct leaf audit. It now also contains
  `deningerMeyerOriginalConvolution_nativeApproximation`, for every original
  forcing/kernel, with finite native forcing/solution ranges, exact repaired
  equations, and original-topology convergence of both sequences.
- The capstone is not wired or counted until its audit passes. Still18/100.

Capstone direct audit passed:
- `lake --old env lean -o .../DeningerMeyerFiniteNativeDensity.olean GaloisForLFunctions/RHTower/DeningerMeyerFiniteNativeDensity.lean` exited 0, no warnings.
- `deningerMeyerFiniteNativeModes_dense` is closed and unconditional in the original scoped quotient topology.
- `deningerMeyerOriginalConvolution_nativeApproximation` pays exact finite native repaired equations and original-topology convergence for every original forcing and source symbol.
- All eleven leaves are now uniquely wired. Ten ingredient artifacts plus the capstone artifact are fresh. No umbrella build.
- Final audit covers all 76 new public declarations via /tmp/hgt_rh019_axioms.lean; log /tmp/hgt_rh019_axioms.log. Both are owned cleanup paths.
- Lean repairs were parameter inclusion in the Gaussian-closure helper and replacing unnecessary simplification with definitional equality. No hypotheses or heartbeat changes.

Final scope review:
- This closes the specifically recorded original-Frechet finite causal density obstacle. It is stronger than Hilbert density because the contour series converges in every defining original source gauge before passing to the literal quotient.
- The closed main theorem has no premises. The solution theorem quantifies only over actual source data and arbitrary actual cohomology forcing. All existence and regularity inputs are discharged in the corpus.
- Grouped divided-difference contours retain the complete local Xi germ without individual residue estimates or separation assumptions. Gaussian removal then reaches every original class.
- This does not assert an unconditional basis expansion of an unsmoothed input, convergence in native BV norms, admission of arbitrary prescribed infinite packets, a continuous inverse to compact-open comparison, a geometric cup identification, positive Hodge compatibility, or RH.
- Global `scripts/formal_tools.py lint` exited 0: formal lint passed. Its only output besides success is existing large-file warnings. All earlier unrelated umbrella omissions are now absent.
- Axiom audit remains running; count stays 18 until terminal audit and cleanup.

Axiom-audit script repair:
- The first exhaustive audit printed standard axioms for 74 declarations, including both capstones. Its two errors were generated names truncated at an apostrophe: rectangleIntegral'_const_mul and rectangleIntegral'_sub. Source names were verified, the scratch script corrected, and the full 76-declaration audit rerun. No project proof changed.
- Frontier map HF/RN now records the proved density and exact-solution approximation, with native BV and positivity limits explicit.
- Formal index refresh is running. Owned cleanup additionally includes /tmp/hgt_rh019_lint.log and /tmp/hgt_rh019_index.log.

Final closure:
- Corrected exhaustive axiom audit exited 0; all 76 declarations matched the
  source manifest and used only the three standard logical axioms.
- Index command exited 0 and refreshed LEAN_API, LEAN_GAPS, LEAN_OVERVIEW and
  the Lean search database. No new source changes followed the direct audits.
- Final audit verified every one of the eleven source/olean pairs and unique
  umbrella imports. Exactly the sixteen recorded /tmp/hgt_rh019_* files were
  deleted; the owned prefix is empty. No owned build remains active.
- Contribution 019 counts once. The 100-contribution goal remains active.
