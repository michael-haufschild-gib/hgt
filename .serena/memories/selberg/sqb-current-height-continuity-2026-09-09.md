# SQB20: complete current height continuity and rectangle mass — audited

RH remains UNPROVED; unbudgeted goal ACTIVE. Frontier map READ ONLY. No subagents, external computation, Runpod, web, commit or push. Preserve shared peer changes.

Module `formal/GaloisForLFunctions/RHTower/SelbergMaassCurrentHeightContinuity.lean`, namespace matching module, 24 public theorems. Imports PeriodCurrentRigidity plus Mathlib Deriv.Inverse and LeftRightNhds. Wired once into RHTower.lean. Stage1/stage3 cards `sqb-current-height-continuity.md`; universal STATUS adds route-independent persistence-across-slices constraint. Frontier not edited.

## Main mathematical progress
For original finite Maass vector F, D=sum |Fq|², A_x=Re sum Fq,xx conj(Fq), B_x=sum ||Fq,xx||. Previous SQB18 proved complete E_e(y)=-integral_0^1 A_x/sqrt(D+e²) -> E0(y)=-integral A_x/sqrtD >=0 with bound |signed quotient|<=B_x, retaining nodal concentration.

New theorem `periodCurrentLimit_continuousAt` line155: E0 continuous at EVERY positive height, including common-zero heights. Proof: generic differentiable real-parameter normed-vector source has only countably many zeros with nonzero derivative (HasDerivAt.eventually_ne; countable isolated-right-within set). Apply to F and F_x: outside union of two countable sets, F=0 implies F_x=F_xx=0. Finite q intersection gives B_x=0 at a.e. common zero on each fixed height. Original C² gives joint A_x/B_x continuity on upper half-plane. Away from nodes signed quotient continuous; at node with B_x=0 squeeze by B_x proves joint continuity too. Thus a.e.x height-continuity even at nodal heights. Compact rectangle source B_x bound permits DCT in height. DOES NOT require nodal set measure zero or source analyticity.

`periodCurrentEnergy_continuousAt`: each complete regulated E_e also continuous in height using signed quotient and same compact bound. On 0<a<=b, uniform 0<=E_e(y)<=int B_x<=C. Thus DCT in height proves `periodCurrentEnergy_band_tendsto` and literal `horizontalCurrent_rectangle_tendsto` line304:
 int_a^b int_0^1 H_e(x+iy) dx dy -> int_a^b E0(y)dy,
where H_e is FULL original pair+phase+regulator-gradient horizontal current. No pointwise H_e limit integrated; no explicit nodal measure assumed.

`exists_positive_current_band`: E0(y0)>0 gives 0<a<y0<b and E0>=E0(y0)/2 throughout Icc a b. `exists_positive_current_band_mass`: limiting mass positive. `exists_eventually_positive_horizontal_rectangle` line312: source-dependent c>0 bounds actual iterated rectangle H_e mass below for ALL sufficiently small regulators. `current_band_mass_eq_zero_iff` line322: for 0<a<b, limiting mass0 iff every E0(y)=0 on Icc a b including endpoints. `nonflat_node_positive_horizontal_rectangle`: prior original nonflat-node positivity supplies the positive-height premise.

No positive current height/nonflat node asserted to exist. No uniform c, band width, quotient-area quarter bound, full-Xi occurrence, Fubini identification with quotient measure, explicit nodal measure or flat-node exclusion established. Flatness in prior SQB19 refers HORIZONTAL first derivative, not full gradient. Source acceleration-flat node here means all horizontal SECOND derivatives zero. Do not confuse these.

## Audits ALL PASS
Scratch `/tmp/sqb20_height.lean` log `/tmp/sqb20_height.log`, canonical source check `/tmp/sqb20_height_source.log` no warnings. Preflight sole stale leaf `/tmp/sqb20_height_preflight.log`. Final `lake build GaloisForLFunctions.RHTower.SelbergMaassCurrentHeightContinuity` compiled only leaf4.7s,8820cached dependency graph jobs; `/tmp/sqb20_height_build.log`. Replayed unrelated EvenL2LogUnitary ring info is cached, not failure. No full/umbrella build.
24/24 per-declaration axiom inventories only propext/Classical.choice/Quot.sound in `/tmp/sqb20_axioms.{lean,log}`; names `/tmp/sqb20_audit_names.txt`. All24 indexed exactly once `/tmp/sqb20_indexed_declarations.json`; umbrella once; index/lint PASS `/tmp/sqb20_{index,lint}.log` (preexisting large-file warnings). Whitespace clean; owned Lean/Lake processes0. All compiler/index/lint sessions collected.

## Broad discovery
OR corpus searches, no per-module cap/full result metadata: `/tmp/sqb20_zero_set_broad.json` 1160rows460modules (level set/Stampacchia/derivative zero/zero set/nodal/Sobolev chain); `/tmp/sqb20_continuity_broad.json`137rows82modules (integral continuity/parameter integral/lower semicontinuity/energy continuity/DCT/positive band). Metadata discovery is NOT proof inspection. Actual source reads included original source acceleration, nodal rigidity, FourierModes compact rectangles, Mathlib Deriv.Inverse, LeftRightNhds, DCT, interval positivity. Do not assume analyticity from analytic-zero-set search hits.

## Verified Lean APIs/pitfalls
- `countable_setOf_isolated_right_within (s:=...)`; `HasDerivAt.eventually_ne (c:=0) hnonzero`; filter via `nhdsWithin_mono x subset`. `self_mem_nhdsWithin.mono` can elaborate wrong: use filter_upwards [self_mem_nhdsWithin] with z hz. `eventually_false_iff_eq_bot.mp`.
- `Set.Countable.ae_notMem volume` or `measure_eq_zero_iff_ae_notMem.mp (hc.measure_zero volume)`; `ae_all_iff` finite coordinates.
- Bind explicit `hF q : ContDiffOn R 2 (field N f q) upper` before differentiating; raw quotientForm proof leaves unreduced function coercions. Bind hp:0<(point x y).im explicitly before `.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)`. `simpa only [dir,Function.comp_def] using hd.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)`.
- Before rw value at ContinuousAt hypothesis, change to Tendsto f (nhds z) (nhds (f z)). `squeeze_zero_norm bound hB` then works.
- `ContinuousAt.congr_of_eventuallyEq` wants newfunction =eventually oldfunction. `h.neg.congr_of_eventuallyEq he` works; `he.continuousAt_iff` unavailable.
- `intervalIntegral.continuousAt_of_dominated_interval` args: eventual measurable wrt restricted uIoc; eventual ae x -> x in uIoc -> norm bound; IntervalIntegrable bound; ae x -> x in uIoc -> ContinuousAt. `IntervalIntegrable.aestronglyMeasurable_restrict_uIoc` for last band DCT; `.1.aestronglyMeasurable` restricts Ioc and fails unless rewrite.
- `pathEnergy_nonneg` must explicitly change/type result as periodCurrentEnergy before rw abs_of_nonneg (rw syntactic mismatch otherwise).
- `mem_nhds_iff_exists_Ioo_subset` yields <l,u,<hl,hu>,hs>, not flat5tuple. Filter neighborhoods `.inter` may not elaborate; filter_upwards.
- `intervalIntegral.integral_eq_zero_of_ae` absent. Use integral_congr to zero then simp.
- `intervalIntegral.integral_congr` supplied membership uIcc; DCT uses uIoc. `simpa using Ioc_subset_Icc_self hx` handles0..1 min/max. Generic rewrite uIcc_of_le hab/uIoc_of_le hab.

Next work must still supply source-supported positivity/exclusion or a quantitative comparison with amplitude mass, then independent full-Xi occurrence. Height continuity closes thickness passage; it does not manufacture the missing global fraction.