# CLG/TTF compensated odd positivity from physical scale seven

RH remains unproved. Goal stays active. This turn made progress beyond `mem:rh_frontier/clg_ttf_effective_compensated_odd_tail_2026_09_07`.

## Current exact source conclusion
On q=π exp(2x)≥7, for every 0≤C≤3e9:
(H+CΔG)/(φ⁶q⁹) ≥5e9>0, where φ=first atom, H=native odd rank-three determinant, Δ=leading odd minor, G=3Φ²+2xΦΦ′.
The proved inequality 16x≤q for x≥0 gives the explicit physical ray x≥7/16.
Canonical K*∈(1e9,3e9) is positive on [0,137/2000] ∪ [7/16,∞).
Weighted corrected determinant positive for every a>0 on r≥7/8, plus prior compact r≤137/1000.
Remaining global-source comparison: compact gap (137/2000,7/16), then all-order mixed hierarchy. Existing q≥7 theorem also covers the part of this physical interval already beyond scale seven. Global mixed rank-six positivity NOT proved.

## Sharp signed cooling and exact factorization
ε=exp(-3(q-π))/399, R=Φ/φ−1.
Scalar Laplace recurrence L(0,m,z)=z^m, L(n+1,m,z)=2mL(n,m,z)−2L(n,m+1,z).
For n≤10,z≥18: 0≤(-1)^n L(n,0,z)≤(2z)^n. Finite shifted-polynomial expansions are kernel proved.
Actual CoolingJet n m = integral L(n,m,qt)exp(-B(x)t) against COMPLETE higher spectral measure.
Support t≥3 gives signed bound for q≥6 by the leading spectral moment.
Calibration and π<3.15 give 0≤(-1)^n R^(n)≤(6q)^n ε for n≤10,q≥7.
Exact local reflected error: first reflected product B_x(t)=φ(x+t)φ(x−t), L_x(t)=R(x+t)+R(x−t)+R(x+t)R(x−t).
j_n−b_n = sum choose(n,i)b_i ℓ_(n−i), at ALL orders.
|ℓ_n|≤2(6q)^nε+(12q)^nε² for n≤10,q≥7.
All odd first reflection jets vanish; b0=φ².

## Explicit five-entry error and determinant arithmetic
Normalized A_k=(-1)^k j_(2k)/(φ²q^k); B_k analog first atom.
First B_k intervals:
[8,9], [180,210], [7000,8500], [300000,500000], [20000000,40000000].
On u=1/q∈[0,1/7], exact positive Bernstein identities give first determinant≥8e10 and 0≤first head≤27000.
exp21≥1.3e9 from exp1>2.718; exp3π<12704.
For m≤5, q^mε≤7^m*(32/1300000000), squared variant too.
Actual normalized entry errors:
1/75000, 1/250, 5/4, 450, 175000.
Generic cubic telescope updates e,a,b,c,d. Absolute coefficient ceilings respectively:
27000, 350000000000, 17000000000, 600000000, 9010000.
Retain first leading cofactor on e error; retain difference of two nonnegative terms in other coefficients.
Total error≤1e10; actual H/(φ⁶q⁹)≥7e10 and 0<Δ/(φ⁴q⁴)≤28000.
Sharp first slope |φ′|≤2qφ on q≥7. Full mass≤1.01φ, full |slope|≤2.01qφ.
Together with 16x≤q, G/(φ²q⁵)≥-13/(50*7³), so adverse correction≤63.674e9; normalized compensated floor5e9 is proved.

## New production modules, all checked and umbrella-wired
HTGeometry (ROOT namespace HTGeometry):
LogarithmicLaplaceScoreBounds
FirstAtomOddScaleSevenBounds
FirstAtomOddScaleSevenLower
ScaleSevenHankelPerturbation
RHTower:
ThetaCuspSharpFiniteCooling
ThetaCuspFactoredReflectionError
ThetaCuspFactoredReflectionBound
ThetaCuspFirstAtomScaleSevenProfiles
ThetaCuspScaleSevenLikelihood
ThetaCuspScaleSevenEntryErrors
ThetaCuspScaleSevenOddDeterminant
ThetaCuspScaleSevenCompensationSource
ThetaCuspScaleSevenCompensatedTail

13 modules, 85 public declarations, 1928 lines, largest302. No outside declaration conflicts.
Every module passed targeted foreground lake env lean; identical scratch copied and needed oleans retained. Imports exactly once, no full/umbrella builds. Formal lint passed.
Only 5 NEW capstones audited: signed finite cooling, all-order factorization, normalized compensated lower bound, canonical outside-gap positivity, weighted tail positivity. All only propext/Classical.choice/Quot.sound. Do NOT re-audit these or prior corpus next turn.

## Docs
New paper: docs/drafts/pipeline/3-formalized/clg-ttf-scale-seven-compensated-tail.md.
Current Stage1 target, CLG frontier map section, TCD status, universal whole-integration-domain rule evidence, and old compact/effective-tail proof cross-references updated.
Owned /tmp/clg_gap_stage and nine exploration/generator/audit files were removed after verification; no owned Lean/Lake process remains. No commit/push. Other tasks edit shared tree; preserve unrelated changes.

## Next useful work
Need actual compact source control between x=137/2000 and q=7. Exploratory complete-source samples suggested canonical compensation stays positive there; this is guidance ONLY.
Finite signed cooling already works by leading moment on q≥6, but calibrated factor-six epsilon needs n/3≤q−π (n≤10). Lowering the determinant endpoint further requires sharper compensation or error budgeting; do not assume the q≥7 estimates imply it.
Alternative compact route: extend existing modular orbit tube and prove exact corrected determinant polynomial on genuinely source-controlled boxes. Existing all-center source-to-polynomial identities are in ThetaCuspOddCompactSourceCoordinates; old [0,137/2000] tube is in ThetaCuspModularCompactTube.

## Lean pitfalls
Use formal cwd; RHTower imports need -M8192. One foreground Lean process only.
No source numerical evaluation supplies a premise. Polynomial coefficients generated symbolically were verified by ring/positivity in Lean.
Do not globally replace 30 by7 inside a derivative formula: the genuine first slope polynomial is -8q³+30q²−15q.
For local reflection identity, avoid Tendsto inference at affine neighborhoods: use Ioo_mem_nhds (-x)<0<x and linarith.
ContDiffAt finite-order .of_le needs explicit result type ℝ n.
Use Pi.sub_apply to simplify functions from Integrable.sub.
Never concatenate absolute bars and multiplication as |*; insert whitespace.
For simp abs natural casts, supply the ℝ type explicitly.
After rewriting normalized determinant, unfold HilbertMetric.signedEvenHankelThreeDet in both hypotheses AND goal before linarith.
