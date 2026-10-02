# Complete actual compact Gamma marking

- **ID:** li-clock-compact-gamma-marking
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [complete source-correlation envelope paper](li-clock-source-correlation-envelope.md), final404 plan M01–M10.
- **Statement:** Actual positive and negative Gamma jump measures, restricted to Ioc(0,T) and marked by exp(pu), separately equal fixed finite common-density measures for every p>1. All compact bounded tests have genuine L1 and exact density integrals; their signed density difference is 1_(u>0)P(u)/u.

## Mathematical boundary

Every actual coefficient and Gamma row is retained. The row0 law is Dirac, with actual coefficient0 discharged by the source density theorem. Complete full norm sums precede factoring and subtraction. Positive and negative carriers may overlap; no Jordan decomposition, probability normalization, global marked finiteness, P sign, M15 or RH result is asserted. Entire source-envelope E01–E21 remains a separate unfinished formalization.

## Gates and source

LOCAL_FINAL_READY: `formal/GaloisForLFunctions/RHTower/LiClockThetaCompactGammaMarking.lean`,335 lines, SHA256 `02539934ef19beef3b97680ded36a8b9c0c10cc85881600f82b411c354e8608a`. Exactly10 public declarations (3 definitions/7 theorems),16 private (1 definition/15 theorems). Root and independent complete26 body/type/API reviews PASS; all10 final404 literal contracts exact. Four complete row helper copies match FINAL SignedGammaJumps under name-only substitutions.

Fresh pinned APIs35010/66881 pass; whole37908 and direct6238 exit0 with empty logs. ALL26 scratch axioms69939 and ALL10 imported public axioms95305 exit0, exactly propext/Classical.choice/Quot.sound, no extra diagnostic. Targeted named27263 exit0 (44s), no leaf diagnostic; all166 replayed diagnostic bodies byte-match earlier final gate logs,68 upstream warnings retained. Unique umbrella import and all10 generated API rows verified; index12777 exit0.

Global lint83680 remains NON-GREEN with10 unrelated unreachable modules and size warnings elsewhere; no finding for this335-line leaf. Complete log delta against fully read Retention lint checked. No full/umbrella build, numerical experiment or unrelated repair. Complete tree-gate record `/tmp/li_root_theta_compact_gamma_marking_tree_gates.json`; literal26 ledger and exact metadata `/tmp/li_root_theta_compact_gamma_marking_ledger.md`, `/tmp/li_root_theta_compact_gamma_marking_metadata.json`.

## All ten public contracts

Local notation P below is the literal `liEvenCrossActualClockPrimitive`.

```lean
def liClockThetaUndampedJumpCoefficient (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    (-1 : ℝ)^(j-1) * normalizedPrimeArchMoment (j-1) / (2*j : ℝ)
```

```lean
def liClockThetaMarkedJumpDensity (positive : Bool) (u : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun u =>
    ∑' j : ℕ,
      max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ)) u
```

```lean
def liClockThetaCompactMarkedGammaMeasure
    (p : ℝ) (positive : Bool) (T : ℝ) : Measure ℝ :=
  ((liClockThetaGammaJumpMeasure p positive).restrict (Ioc 0 T)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (p*u)))
```

```lean
theorem liClockThetaUndampedJumpCoefficient_eq_scaled
    {p : ℝ} (hp : 1 < p) (j : ℕ) :
    liClockThetaUndampedJumpCoefficient j =
      p^(2*j) * liClockThetaLogJumpCoefficient p j
```

```lean
theorem liClockThetaMarkedJumpDensity_series
    (positive : Bool) {u : ℝ} (hu : 0 < u) :
    Summable (fun j : ℕ =>
      ‖max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ)‖) ∧
    HasSum (fun j : ℕ =>
      max (if positive then liClockThetaUndampedJumpCoefficient j
        else -liClockThetaUndampedJumpCoefficient j) 0 *
        u^(2*j-1) / ((2*j-1).factorial : ℝ))
      (liClockThetaMarkedJumpDensity positive u) ∧
    (∀ p : ℝ, 1 < p →
      Real.exp (p*u) * liClockThetaGammaJumpDensity p positive u =
        liClockThetaMarkedJumpDensity positive u)
```

```lean
theorem liClockThetaMarkedJumpDensity_admission (positive : Bool) :
  (∀ u : ℝ, 0 ≤ liClockThetaMarkedJumpDensity positive u) ∧
  (∀ T : ℝ, 0 < T →
    IntegrableOn (liClockThetaMarkedJumpDensity positive) (Ioc 0 T))
```

```lean
theorem liClockThetaCompactMarkedGammaMeasure_admission
    {p T : ℝ} (hp : 1 < p) (hT : 0 < T) (positive : Bool) :
  IsFiniteMeasure (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  (∀ᵐ u ∂liClockThetaCompactMarkedGammaMeasure p positive T, u ∈ Ioc 0 T) ∧
  liClockThetaCompactMarkedGammaMeasure p positive T =
    (volume.restrict (Ioc 0 T)).withDensity
      (fun u => ENNReal.ofReal (liClockThetaMarkedJumpDensity positive u))
```

```lean
theorem liClockThetaCompactMarkedGammaMeasure_eq
    {p q T : ℝ} (hp : 1 < p) (hq : 1 < q) (hT : 0 < T)
    (positive : Bool) :
  liClockThetaCompactMarkedGammaMeasure p positive T =
    liClockThetaCompactMarkedGammaMeasure q positive T
```

```lean
theorem liClockThetaCompactMarkedGammaMeasure_test
    {p T : ℝ} (hp : 1 < p) (hT : 0 < T) (positive : Bool)
    (h : ℝ → ℝ) (hh : Measurable h)
    (hC : ∃ C : ℝ, ∀ u ∈ Ioc 0 T, |h u| ≤ C) :
  Integrable h (liClockThetaCompactMarkedGammaMeasure p positive T) ∧
  IntegrableOn (fun u => h u * liClockThetaMarkedJumpDensity positive u)
    (Ioc 0 T) ∧
  (∫ u, h u ∂liClockThetaCompactMarkedGammaMeasure p positive T) =
    ∫ u in Ioc 0 T, h u * liClockThetaMarkedJumpDensity positive u
```

```lean
theorem liClockThetaMarkedJumpDensity_sub (u : ℝ) :
  liClockThetaMarkedJumpDensity true u -
    liClockThetaMarkedJumpDensity false u =
  (Ioi (0 : ℝ)).indicator (fun u => P u / u) u
```

## Complete independent audit

# Compact actual Gamma marking: complete independent audit

**PASS_SCRATCH_REVIEW — ALL335 source lines, ALL26 declarations and ALL10 exact public contracts. No mathematical blocker.**

Frozen source `/tmp/li_root_theta_compact_gamma_marking_core.lean`, SHA256 `02539934ef19beef3b97680ded36a8b9c0c10cc85881600f82b411c354e8608a`. Final404 approved plan SHA256 `b932f414f23598558a396ce3c8ad6c317f4c817325e2e2a6ecb8d083792ff782`. Ledger248 SHA256 `bfad68e6a52b7296aea86a9f269979cd2f0ecd334735bbad7bf9198a94dfdf23`; metadata466 SHA256 `ad82796e2204fdecd16786fce38c311f8f2401b69a4e0063352cd351ba10b1c1`; owner certificate9 SHA256 `994c43d9990a29707e4b93fe761e010a00118265fe22018bd83098957c358cc6`.

Read every source body and contract, both fresh API scripts, complete248 ledger, complete26 axiom reports and owner certificate. No compiler, numerical computation, new agent or tree/source edit. No reliance solely on compiler exit.

## Exact contracts and ALL26 body dispositions

| Range / visibility | Complete declaration | Disposition |
|---|---|---|
| 10–12 / public | `liClockThetaUndampedJumpCoefficient` | PASS: M01: literal actual a_j, a0=0 explicitly before truncated Nat subtraction or denominator cancellation. |
| 14–19 / public | `liClockThetaMarkedJumpDensity` | PASS: M02: full nonnegative coefficient row sum with positive-ray indicator; no finite prefix or hypothetical all-order moment sign. |
| 21–24 / public | `liClockThetaCompactMarkedGammaMeasure` | PASS: M03: actual full Gamma jump measure restricted to Ioc0T then marked by exp(pu); no normalized law substituted. |
| 26–35 / public | `liClockThetaUndampedJumpCoefficient_eq_scaled` | PASS: M04: exact a_j=p^(2j)ell_j(p), j0 separate and p>1 implies p>0; full scalar denominator cancellation valid. |
| 37–42 / private | `sgm_density_measurable` | PASS: Complete renamed FINAL copy: zero row measurable; positive row indicator of measurable polynomial/exponential on Ioi. |
| 44–52 / private | `sgm_density_nonneg` | PASS: Complete renamed FINAL copy: j0 and u<=0 zero, hp>0 and positive u give every Gamma factor nonnegative. |
| 54–79 / private | `sgm_rowDensity_le` | PASS: Complete renamed FINAL copy: j>0 identity p*(pu)^(2j−1)/(2j−1)!*exp(−pu); exponential full-term fence gives <=p. Factorials nonzero, j0 retained. |
| 81–88 / private | `sgm_density_summable` | PASS: Complete renamed FINAL copy: true arbitrary nonnegative summable weights dominated pointwise by p*w_j; all real u, every row retained. |
| 90–93 / private | `sgm_term` | PASS: Exact full marked row term, identical factorial and max-part expression used in public series. |
| 95–97 / private | `sgm_part_nonneg` | PASS: Both Bool cases max(part,0)>=0; no raw moment sign used. |
| 99–109 / private | `sgm_part_le_abs` | PASS: Both max parts bounded by actual |ell_j|; handles negative coefficients without assuming alternation. |
| 111–127 / private | `sgm_part_scaled` | PASS: p^(2j)>0 lets both max parts factor through exact scaled coefficient; negative part sign and j0 correct. |
| 129–142 / private | `sgm_marked_row_eq` | PASS: Every row exact exp cancellation, positive u and p>1; j0 explicit avoids Gamma Dirac/density confusion. |
| 144–157 / private | `sgm_term_hasSum` | PASS: Full actual coefficient absolute summability -> both part summability -> full row summability -> HasSum multiplied by finite exp(pu). Cancellation only after genuine full admission. |
| 159–181 / public | `liClockThetaMarkedJumpDensity_series` | PASS: M05: choose actual p=2 to obtain every positive-u full norm summability and HasSum; then all p>1 equality from admitted rows, no AE-only or finite-prefix substitute. |
| 182–185 / private | `sgm_gamma_measurable` | PASS: Measurable full Gamma density from complete measurable countable series; independent of any RH sign. |
| 187–191 / private | `sgm_marked_measurable` | PASS: Measurable complete marked density, positive-ray indicator retained. |
| 193–201 / private | `sgm_marked_eq` | PASS: Extends p-invariant marked equality to ALL real u: u<=0 all Gamma row densities and marked indicator zero. |
| 203–224 / public | `liClockThetaMarkedJumpDensity_admission` | PASS: M06: full marked densities nonnegative all real u; actual p2 Gamma L1 times exp(2u), bounded on Ioc0T, gives genuine compact L1 for each sign. |
| 226–238 / private | `sgm_measure_eq` | PASS: Actual PUBLIC GammaJumpDensity_admission gives full measure/density equality incl eliminated zero-weight Dirac. Restriction and withDensity multiplication then exact ofReal product produce common marked density. |
| 240–256 / public | `liClockThetaCompactMarkedGammaMeasure_admission` | PASS: M07: genuine nonnegative compact L1 -> finite density lintegral -> finite measure; AE strict-left support via absolute continuity of restricted volume. Literal full measure equality exported. |
| 258–264 / public | `liClockThetaCompactMarkedGammaMeasure_eq` | PASS: M08: each sign separately equals SAME full common-density restriction for p,q>1,T>0; no Jordan or probability inference. |
| 266–293 / public | `liClockThetaCompactMarkedGammaMeasure_test` | PASS: M09: measurable test bounded only on Ioc0T yields product L1; measurable finite ENNReal density and genuine product L1 give test L1 against actual carrier BEFORE integral equality. Arbitrary real bound C sufficient via AE norm bound; no global boundedness assumption. |
| 295–301 / private | `sgm_parts_sub` | PASS: Both sign cases exact max(ell,0)−max(−ell,0)=ell, including ell0. |
| 303–318 / private | `sgm_signed_eq_sub` | PASS: Both actual weighted part sums independently admitted using absolute coefficient bound; tsum subtraction then exact term difference, no formal divergent cancellation. |
| 320–332 / public | `liClockThetaMarkedJumpDensity_sub` | PASS: M10: p2 complete signed series equals exp(−2u)P/u on Ioi; exp cancellation yields exact marked difference, u<=0 remains zero. Single-Xi normalization, complete actual primitive, no pointwise sign inferred. |

All ten public complete definition bodies/theorem types independently match M01–M10 in final404 after whitespace-only comparison. All26 ledger contracts match source with outer declaration indentation ignored; actual theorem proof delimiter checked. Owner body hashes are SHA256 of stripped complete declaration, not untrimmed blocks; ALL26 verified using that convention. Independent untrimmed body hashes/full literal contracts recorded in matching audit metadata.

## Copied-source and actual admission fidelity

FINAL `LiClockThetaSignedGammaJumps.lean` pin `fdda232106c1dd11b7226566691396024ce05286ed7a09f16fa261a0de0c6b9d` verified. ALL four copied row declarations match the complete FINAL type/body after ONLY `sgm_`→corresponding `sgWeighted_` name substitutions; no mathematical change. Exact original/assembly ranges and renamed hashes recorded. Original rows666–718 read fully, not just their statements.

Primary actual-source blocks read: literal coefficients/parts/jump measure/densities19–47; complete absolute coefficient admission and genuine signed primitive series585–658; PUBLIC full carrier/density L1 and zero-degree handling1202–1241. `LiClockThetaGammaMixture.lean:38–62` literal row density is zero for j0, but row LAW is dirac0. M03 retains actual complete jump law; PUBLIC density admission eliminates that atom using actual ell0=0. No replacement of a Dirac row by a density without zero-weight proof.

Actual a_j=(-1)^(j−1)M_(j−1)/(2j) for j>0 and a0=0. No assumption M_j>=0 or alternating actual log coefficients. Both max parts retain every signed raw coefficient and every factorial. Public p>1 domain unchanged; no extension below the absolute coefficient-L1 domain. Fixed p2 is an existing actual source witness for marking, not an empirical cutoff.

The marked identity uses exact rate-p Gamma shape2j density: exp(pu) cancels exp(−pu), p^(2j) cancels coefficient damping, and both factorial/2j factors combine with the literal primitive series. Full positive/negative row summability admitted independently before tsum subtraction. At positive u, marked difference=P(u)/u; at u0 and negative u, Ioi indicator is mandatory.

Positive/negative marked carriers are not claimed to be Jordan parts and may overlap. Common density shows each carrier separately independent of p after compact restriction, without normalizing into probabilities or asserting marked global finite mass.

## Genuine compact L1 and measure/test guards

Actual GammaJumpDensity is integrable on the full real line for each p>1 and each Bool part. On Ioc0T, exp(2u)<=exp(2T); bounded multiplication proves marked density genuinely L1. Measurability and all-real nonnegativity established before compact measure conversion.

Source carrier equality, restriction-withDensity and iterated withDensity product yield literal common marked density. Nonnegative true compact L1 then gives finite ENNReal density lintegral and IsFiniteMeasure; absolute continuity transfers support Ioc0T. No totalized infinite real mass used.

For measurable h bounded on Ioc0T, product integrability precedes test integrability via measurable finite density, then Bochner integral equality. Bound C need not be explicitly replaced by max(C,0): the actual AE norm bound is the exact input to `Integrable.bdd_mul`; no extra guard is required or added. Negative-ray tests remain unrestricted outside compact support.

Installed primary Mathlib bodies checked: `WithDensity.lean:141` finite measure from finite lintegral; `:215` exact restricted-density equality; `:538/:545` two-density product; `HasFiniteIntegral.lean:99` nonnegative ofReal finite-integral equivalence; `Integrable.lean:805` density/test integrability equivalence with AE finite density; `Bochner/ContinuousLinearMap.lean:310–320` integral-toReal density identity. Every used measurability/finiteness assumption is explicitly proved by caller.

## Complete gate evidence and boundary

- Fresh API35010 and66881 owner-reported terminal0, both logs EMPTY; read all31+32 pinned `have := @Name` probes. Whole37908 owner-reported terminal0, exact335 core log EMPTY. No reviewer compiler.
- ALL26 axes69939 owner-reported terminal0. Complete actual26-line log parsed independently: all26 unique reports match exact source order/namespace and only `[propext, Classical.choice, Quot.sound]`; no extra diagnostics.
- Queries lie before the namespace closure, not in an exact appended source prefix. Removing all26 print commands and ONE added blank reconstructs exact335 source bytes. This correspondence checked independently; all mathematical declarations unchanged. Axiom log SHA256 `4fd4891f97268a2b566bce4570800870b8ce62dcb7ba46278de527989018471d`; axiom scratch SHA256 `009548f7d403157f5a9bd73e8c32f18e67e2b70241f73df6cf5168f3520654d8`.
- Frozen335 source rehashed unchanged at completion. No new private/public source assumption, options override, proof debt or stronger export.

**PASS.** Independent full mathematics/source/API audit complete. Root retains tree promotion and named/direct/imported public axiom gates. Result establishes exact complete actual compact marking/invariance/test identities and signed density decomposition. Literal P>=0, M15, D0 and RH remain OPEN.
