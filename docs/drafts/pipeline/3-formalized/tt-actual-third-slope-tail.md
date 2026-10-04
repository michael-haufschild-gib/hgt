# C69: actual third-slope tail from flat boundary selection

Route TT, formalized, 2026-10-04. Target: unconditional eventual
positivity of the actual normalized third-minor slope. Global sign,
fourth transported Schur gap and all-rank closure remain open.

## Corpus basis
C65 exact source compactification, moments and cubic/slope identities;
C66–68 actual boundary selection and all-order decay of both transverse
coordinates. Axis-flow search /tmp/tt_c69_axis_flow_search.json:
partialfalse, complete inventory, generation1224665. Existing exact
flow algebra supports polynomial induction; no ready tail theorem.

## Paper proof under audit
Write h=1/k, r=k²(9-u²), t=k(1-3J/u). Actual r,t decay faster than
every power of h; all polynomial observables differ from axis by a
similarly flat term (proved by constants/addition/multiplication by
coordinates). Axis specialized moments s2,s4,s6 have the C65 values
-6⁴24, 6⁶324², -6⁸1524³ at h0. Axis s8 vanishes once with quotient
value6¹⁰10524⁴; s10 vanishes twice with quotient value-6¹²94524⁵.
These two exact coefficient identities now pass Lean.

The cubic identity then gives P_axis=h²A(h), with
A(0)=6²⁴24⁹720>0. Axis field is Hh=-36h²-12h³ and Hr=Ht=0.
Using Q=(6-h)HP+(17h-66)(Hh/h)P gives Q_axis=h³B(h),
B(0)=1944A(0)>0. Flat polynomial evaluation transfers this to
k³Q_actual→B(0). Since Q_actual=h¹⁹S_actual and k>0 eventually,
S_actual is eventually positive. The existing exact incidence must
then identify this with the actual normalized third-minor derivative.

## Status
All four production leaves passed foreground direct `lake env lean`:
ThetaCuspRatioAxisMoments, ThetaCuspRatioFlatEvaluation,
ThetaCuspRatioAxisSlope, ThetaCuspRatioActualSlopeTail. Scratch audit2
for the actual tail capstones passed standard3 only. Production imports
are wired into RHTower. Imported axiom audit29865 exit0: all ten printed capstones depend only on
propext, Classical.choice and Quot.sound. The printed actual-tail types
contain no premises. Index73324 exit0 refreshed the generated catalog;
lint16833 exited1 with12 unrelated umbrella omissions and no owned
errors. No full/umbrella build was run. Owned C69 scratch sources/caches cleaned.

Actual capstones, no hypotheses:
- actual_scaledSlope_tendsto: k³Q_actual→1944*axisMinorMass.
- actualSquareSlope_eventually_pos.
- normalized_third_slope_eventually_pos:
  eventually 0<deriv ThetaCuspOddDirectionTransport.normalizedD x.

All factorization identities are exact Lean algebra; no external
mathematical computation or limit raises. Initial failures were
coefficient finite-sum simplification, polynomial C rational casts,
and real/complex casts, not false mathematical identities.
