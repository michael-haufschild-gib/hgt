# Map of the corpus's RH frontier: 384 producers, 225 hypotheses, none discharged

- **ID:** `rh-producer-map-corpus`
- **Stage:** 1-in-progress
- **Type:** CORPUS SURVEY (no new mathematics claimed)
- **Scientific status:** `[SURVEY]` `[NOT A RESULT]` `[NAVIGATIONAL]`
- **Why:** after five hand derivations in one session reproduced formalized corpus material, the
  cheapest way to stop that is a map of what the corpus already reduces RH to.

## 1. The inventory

Extracted mechanically from `formal/GaloisForLFunctions` (both `RHTower` and `HTGeometry`):

```text
theorems named riemannHypothesis_of_*                        384
distinct defined `Prop`s appearing in their hypotheses       225
of those, hypotheses some theorem concludes                  184
of those, with a producer whose statement names no other Prop 95
of those, with an `exists_` or hypothesis-free producer      112 (overlapping count)
```

Producer kinds, counted over all RH hypotheses:

```text
_iff_          401      relocations — move the problem, discharge nothing
direct         341      syntactically hypothesis-free, but many are `_of_riemannHypothesis`
conditional    275      producer with its own undischarged Prop hypotheses
exists_         48      genuine existence theorems
```

**None of the 384 has all its hypotheses discharged**, which is forced: if one did, RH would be
proved in the tree. The value of the map is the *shape* of what is left.

## 2. The load-bearing pattern

The dominant producer kind is `_iff_`. That is the corpus's characteristic move: an RH-sufficient
condition is shown equivalent to another condition, repeatedly, without any branch terminating in an
unconditional theorem. `RHLadder` alone carries 23 RH producers and has 40 theorems concluding it,
almost all equivalences.

The `_of_riemannHypothesis` producers are the *easy direction* and appear throughout. A syntactic
filter for "hypothesis-free producer" catches them, so the `direct` count above is inflated; read it
as an upper bound.

## 3. The clearest statement of the corpus's own open theorem

`RHTower/XiCTaylorOrientedCoefficientCurrent.lean`, whose header says outright:

> *"This module is an algebraic normal form for the open source theorem. It does not prove that the
> canonical Xi coefficients satisfy the current inequality."*

The chain is:

```text
exists_xiCTaylorSuperaccurateSchedule                        -- the schedule EXISTS, proved
XiCTaylorAnisotropicOrientedCoefficientSublinearUpper N      -- the open inequality
  := ∀ σ, 0 < Re σ < 1/2 → ∀ ε > 0, ∀ᶠ n,
       Im( P_n′(z_n)·conj P_n(z_n) )  <  ε(n+1)·|P_n(z_n)|²
riemannHypothesis_of_xiCTaylorAnisotropicOrientedCoefficientSublinearUpper
```

with `P_n` the finite Xi Taylor polynomial at the schedule stage and `z_n` the anisotropic centred
point. Two facts make this the cleanest frontier statement in the tree:

- `orientedPolynomialCurrent P z = Im(P′ conj P) = −½·∂_vertical |P(z)|²`, so the condition is that
  the squared modulus of the finite Taylor polynomial cannot fall vertically faster than a sublinear
  rate — a **finite coefficient inequality**, no zeros, no asymptotics of `ζ`.
- Since `logDeriv P = ∑ 1/(z − ρ_k)` over the polynomial's own roots,
  `Im logDeriv P(z) = ∑ (Im ρ_k − Im z)/|z − ρ_k|²`, so the condition is literally about where the
  *approximants'* zeros sit relative to the test point in the left strip.

The converse `..._of_riemannHypothesis` is proved, so this is an **equivalence**: an honest
restatement of RH, open in the hard direction.

## 4. Consequence for the Jensen/Pólya lane

`jensen-polya-unconditional-frontier.md` was worked on the assumption that the Jensen ladder is where
the corpus's frontier sits. It is not: **the corpus contains no Jensen polynomial and no hyperbolicity
predicate at all** (searching "Jensen polynomial hyperbolic Xi Taylor coefficients" returns only
Hardy-coefficient material), while it contains 384 RH producers in other lanes. The Jensen lane is a
*new* lane for this corpus, not its frontier — which is a reason to work it or to drop it, but the
choice should be made knowing that.

Two lanes that the map shows are close to the theta work already done:

- `ThetaCuspRelaxedFourthMomentConcentration` — 2 RH producers, 9 hypothesis-free producers, sitting
  next to `ThetaCuspKernelLogConcavity` and `ThetaCuspFullReflectionFourthTuran`, both unconditional.
- `ThetaCuspUpperAdjacentRatioSeparation` — 2 RH producers, 7 producers, same neighbourhood.

Those are the places where the corpus's *proved* theta machinery is nearest to an RH producer, and
they are the natural next audit.

## 5. Honest note

This card contains no mathematics. It is a navigational artifact produced because I spent four
sections of another card rebuilding `ThetaCuspKernelLogConcavity.lean`. Its only claim is the
inventory, which is mechanical and reproducible from the tree.

## Gates

- [x] inventory of RH producers and their hypotheses
- [x] producer-kind classification
- [x] the corpus's own stated open theorem identified with its exact statement
- [ ] audit `ThetaCuspRelaxedFourthMomentConcentration` — what exactly is undischarged
- [ ] audit `ThetaCuspUpperAdjacentRatioSeparation` — same

## 6. The theta lane bottoms out in two explicit first-atom moment inequalities

The audit of §5's two candidates is the sharpest thing in this survey. `PrimeArchThetaCumulantRatioSplit`
defines both RH hypotheses as **explicit rational-coefficient inequalities on the raw even moments of
the theta source**, `m_j = thetaCuspRawEvenMoment j`:

```text
ThetaCuspUpperAdjacentRatioSeparation      :  14 m₂²    ≤  9 m₁ m₃
ThetaCuspRelaxedFourthMomentConcentration  :  16 m₀ m₂  ≤ 45 m₁²
```

together with the exact identity `m₀(9m₁m₃ − 14m₂²) + m₂(45m₁² − 16m₀m₂) = 3C`,
`C = 3m₀m₁m₃ + 15m₁²m₂ − 10m₀m₂²`.

### 6.1 The tail is already discharged

`PrimeArchThetaSourceAtomDomination.thetaCuspRelaxedFourthMomentConcentration_of_first_atom` reduces
the full-source inequality to the **first atom alone**, with the domination loss absorbed into one
explicit constant:

```text
16·(3005/2997)·a₀·a₂  ≤  45·a₁²        ⟹   ThetaCuspRelaxedFourthMomentConcentration
```

with `a_j = thetaCuspAtomRawEvenMoment j 1`. There are four such reductions
(`_of_first_atom`, `_of_first_atom_singleLoss`, `_of_firstAtomHalfDensityRemainder`,
`_of_reflectedBudget`) and two equivalences (`_iff_susceptibility_upper`,
`_iff_fullBornWittenSuperpotentialMoment`). **The higher-atom tail is not the obstruction; it is
already paid for.**

### 6.2 In dispersion coordinates

With `D_n := m_n m_{n+2}/m_{n+1}² − 1` — the squared coefficient of variation of the tilted measure,
nonnegative for free by Cauchy–Schwarz (`GammaRenormalizedTuranWindow.dispersion_nonneg`) — the two
conditions are, exactly,

```text
D₀ ≤ 45·2997/(16·3005) − 1 = 1.80502…        (concentration, upper)
D₁ ≥ 14/9 − 1 = 0.5556…                      (separation, lower)
```

So the corpus's theta lane reduces RH to a **two-sided window on two adjacent dispersions of the
first theta atom**: the zeroth must be concentrated below `1.805`, the first spread above `0.556`.
Both are quantitative, neither follows from positivity, and they pull in opposite directions.

### 6.3 Why the soft route fails here, with numbers

Strong log-concavity does not deliver `D₀ ≤ 1.805`. The corpus's own floor gives
`−(log φ₁)″ ≥ 4πe^{2x} ≥ 4π`, so Brascamp–Lieb with `g = x²` gives

```text
D₀ = Var(x²)/E(x²)²  ≤  4E[x²]/(λ E[x²]²)  =  4/(λ E[x²]) ,      λ = 4π ,
```

which needs `E[x²] ≥ 4/(1.805·4π) = 0.176`. But `φ₁(x) = e^{x/2}·2s(2s−3)e^{−s}` with `s = πe^{2x}`
decays double-exponentially, so its mass sits on `x ≲ 0.2` and `E[x²] ≈ 10^{−2}`. The bound comes out
around `30`, not `1.8`. **Off by more than an order of magnitude**, and the reason is structural: the
measure concentrates where `x²` is small, so the *relative* fluctuation of `x²` is large exactly where
Brascamp–Lieb is weakest.

The generic log-concave bound is no better: `{M_k/k!}` log-concave gives `M₀M₄ ≤ 6M₂²`, i.e.
`D₀ ≤ 5`, attained by the exponential — a factor `2.8` short, with equality for a density the theta
atom is nothing like.

### 6.4 What this says about the lane

`D₀ ≤ 1.805` is a **tight numerical fact about one explicit function**, not a soft consequence of any
regularity the corpus has proved. Under the project's no-computation rule it is exactly the kind of
statement that cannot be established, and under any rule it needs the actual value of a ratio of
three specific transcendental integrals.

That is the honest end of this lane, and it is worth stating because the lane looks, from the outside,
like the most advanced in the tree: unconditional log-concavity, unconditional fourth-order source
Turán, four independent tail reductions — and then a single ratio that has to be evaluated.

## Gates

- [x] audit `ThetaCuspRelaxedFourthMomentConcentration` — reduced to `16(3005/2997)a₀a₂ ≤ 45a₁²`
- [x] audit `ThetaCuspUpperAdjacentRatioSeparation` — reduced to the adjacent-ratio analogue
- [x] restated in dispersion coordinates: `D₀ ≤ 1.805`, `D₁ ≥ 0.556`
- [x] shown that strong log-concavity misses `D₀` by an order of magnitude, with the reason
- [ ] whether any structural route reaches a *tight* ratio of first-atom moments

## 7. How tight is `D₀ ≤ 1.805`? Few percent — and that settles the method question

I asked whether there is a route to a tight first-atom moment ratio that is not evaluation. The way
to answer it is to find out how much room the inequality has.

**Normalisation, checked.** `thetaCuspRawEvenMoment n = 2∫_{x>0} x^{2n}·thetaCuspFullSource x`, and
`iteratedDeriv (2n) Xi 0 = (−1)ⁿ · thetaCuspRawEvenMoment n` — so these are exactly the Xi Taylor
coefficients: `ξ(½+z) = ∑_n (b_n/(2n)!) z^{2n}` with `b_n = 2∫x^{2n}Φ`. `thetaCuspSourceTerm` is `2φ_n`
in the classical normalisation, a factor that cancels in every ratio.

**Orientation estimate** (quadrature on the first atom `φ₁(x) = e^{x/2}2s(2s−3)e^{−s}`, `s = πe^{2x}`,
sampling `x = 0, .1, .2, .4, .6, .8, 1`; stated as orientation, not as a proof step):

```text
∫φ₁ ≈ 0.2545   →  Ξ(0) ≈ 0.509   against the classical ξ(½) = 0.49712…   (+2.4%)
∫x²φ₁ ≈ 1.107e−2 ,  ∫x⁴φ₁ ≈ 1.44e−3
D₀ = b₀b₂/b₁² − 1  ≈  1.99      from my own three values
D₀                 ≈  1.71      substituting the classical ξ(½) and c₂ for b₀, b₁
```

The two routes **straddle the threshold `1.80502`**. My quadrature is worth a few percent, and `D₀`
is a ratio that amplifies a `3%` error in `b₁` into `7%`. **So the numerics cannot decide the
inequality**, and I am not claiming it false — but they do decide the *method* question:

> **The corpus's constant `45/16` is tight to within a few percent.**

That is the answer to §6's question, and it is negative. A constant with a few-percent margin cannot
be reached by any argument carrying slack: not Brascamp–Lieb (§6.3, off by 10×), not generic
log-concavity (`D₀ ≤ 5`, off by 2.8×), not any comparison against an extremal density. The constant
must have been chosen as the largest that the downstream Ward/susceptibility argument tolerates, and
what is left is the true value of `b₀b₂/b₁²` — three specific transcendental integrals — to a few
percent.

**Consequence for the lane.** `ThetaCuspRelaxedFourthMomentConcentration` is not "an open estimate";
it is a numerical assertion about the fourth Taylor coefficient of `ξ` at `½`, with the sign of the
margin unknown to me. Under this project's no-computation rule it is unreachable, and if it is false
the RH producers consuming it are vacuous. **Either way it is not a route**, and that is worth more
than another cycle of machinery above it.

The same applies to `ThetaCuspUpperAdjacentRatioSeparation` (`D₁ ≥ 5/9`), which I have not estimated.

## Gates

- [x] normalisation verified against `iteratedDeriv Xi 0` and the classical `ξ(½)`
- [x] tightness of `45/16` established at the few-percent level
- [x] all soft routes excluded by the margin, with the factors (10×, 2.8×)
- [ ] the sign of the margin — requires evaluation, which this project forbids

## 8. Correction to §6–§7: the two numerics are a low-block lemma, not the endpoint

§7 concluded "`ThetaCuspRelaxedFourthMomentConcentration` … is not a route." **That is wrong, and the
error was not reading the RH producer's full hypothesis list.** From
`PrimeArchThetaHankelDegreeTail`:

```lean
/-- Two explicit source-pure theta moment-ratio inequalities, together with prime–Gamma Hankel
nonnegativity only for integer polynomials of degree at least two, imply the Riemann hypothesis. -/
theorem riemannHypothesis_of_thetaCuspRatioSplit_of_primeArchDegreeTwoTail
    (hupper  : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration)
    (htail   : PrimeArchSourceTraceHankelIntDegreeTwoTailNonnegative) :
    RiemannHypothesis
```

There is a **third** hypothesis, and it is an infinite family. So RH is not being derived from four
Taylor coefficients — the hostile check I was running passes, and my framing of §7 was the thing at
fault.

**The actual role of the two numerics.** `primeArchSourceMomentHankelDeterminantsPositive_iff_
riemannHypothesis` makes Hankel-determinant positivity equivalent to RH. The two moment-ratio
inequalities **discharge the low block** — sizes `0`, `1`, `2` — via
`det_primeArchSourceMomentHankelMatrix_two_pos_of_ratioSplit_of_one_strict`, leaving

```text
PrimeArchSourceMomentHankelDeterminantTailFromThreePositive
```

— *"only one scalar leading determinant in each size `n ≥ 3` remains."*

So the lane's structure is:

```text
RH  ⟺  all Hankel determinants positive
        ├── sizes 0,1,2 : discharged by two explicit moment-ratio inequalities  (tight numerics)
        └── sizes ≥ 3   : PrimeArch…DeterminantTailFromThreePositive            ← the open frontier
```

That is a genuine and substantial reduction, and the frontier is the **tail**, not the numerics. §7's
tightness measurement stands as a measurement — `45/16` really is tight to a few percent — but its
consequence is only that *this lemma* needs evaluation, not that the lane is closed. A tight lemma in
a chain is normal; a tight *endpoint* would have been the problem.

**What §7 got right and should be kept:** the normalisation check against `ξ(½)`, the observation that
Brascamp–Lieb misses by `10×` and generic log-concavity by `2.8×`, and the conclusion that no
slack-carrying argument reaches `45/16`. What it got wrong is the scope of "not a route".

## Gates

- [x] RH producer's full hypothesis list read — three hypotheses, not two
- [x] role of the two numerics identified: they discharge Hankel sizes `0,1,2`
- [x] §7's "not a route" withdrawn
- [ ] `PrimeArchSourceMomentHankelDeterminantTailFromThreePositive` — the actual open frontier here

## 9. The theta lane's frontier, read to the bottom

```lean
def primeArchSourceMomentHankelMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => analyticTraceMoments (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) (i + j)

def PrimeArchSourceMomentHankelDeterminantsPositive : Prop := ∀ n, 0 < (primeArchSourceMomentHankelMatrix n).det

theorem primeArchSourceMomentHankelDeterminantsPositive_iff_xi :
    PrimeArchSourceMomentHankelDeterminantsPositive ↔ XiCentralMomentHankelDeterminantsPositive
```

So the lane is: **RH ⟺ the Xi central-moment sequence is positive definite** — the Hamburger moment
condition, i.e. the Li/Keiper picture. Classical as an equivalence.

What the corpus adds is the **low-block discharge**: the two theta moment-ratio inequalities kill
sizes `0,1,2`, leaving `∀ n ≥ 3, 0 < det H_n`. That is a genuine reduction and it is new in the tree,
but it removes three cases from an infinite family; the frontier is the same family it always was.

**And it is the same wall in new coordinates.** The free direction is exactly
`GammaRenormalizedTuranWindow.hankel_nonneg_of_measure`: if the sequence were the moment sequence of
a positive measure, every Hankel form would be PSD for nothing. It is not free here because the
moments are computed from the **prime–archimedean side**, and identifying them with the moments of a
positive measure *is* RH. Prime-side data gives numbers; positivity is what must be created.

That is `positivity-creators-versus-transporters` again, reached from a fifth direction in one
session.

## 10. Session conclusion: where every lane terminates, and why

| lane | terminates at | kind of obstruction |
|---|---|---|
| hypertranscendence / finite-phase | Ostrowski 1920; zero-blind invariant | **known theorem** + wrong invariant |
| Deninger weight-one polarization | axioms ⟺ `Re = 1/2` | **equivalence to the conclusion** |
| Jensen/Pólya kernel side | Pólya 1926 / de Bruijn 1950; kernel not `PF₅` | **known** + **certified cap** |
| Jensen/Pólya `d = 4` | tight inequality on `γ(0..8)` | **tight numeric** |
| theta Hankel (corpus's own) | `∀ n ≥ 3, det H_n > 0`, prime-side moments | **positivity must be created** |

Five lanes, five terminations, and the last three are the same obstruction in different coordinates:
**the source data supplies numbers and lower bounds; every criterion consumes an upper bound or a
positivity that the source does not supply.** The corpus named this before I arrived
(`positivity-creators-versus-transporters`); what this session adds is that it survives being reached
from the hypertranscendence side, the Laguerre/Jensen side, the log-concavity side, the total-positivity
side, and the Hankel side.

No lane examined today fails for a reason specific to its own machinery. That is the finding, and it
is negative.

## 11. Correction and sharpening of §10: positivity IS created — the Gamma normalization destroys it

§10 said "positivity must be created". That is imprecise, and checking the fifth creator class —
Gram/squares, which I had not surveyed — makes it precise and changes the conclusion.

**Positivity is created, unconditionally, on the prime side.** From
`VonMangoldtGammaFactorialNormalizationNoGo`:

> *"every shifted raw moment matrix `M(i,j) = m_(r + a_i + a_j)` is a cofinal positive semidefinite
> Gram. In particular the unnormalized odd block `[[m₁,m₃],[m₃,m₅]]` is positive semidefinite."*

and `VonMangoldtSuccessorBianchiHankelWeld` builds a coupled Gram that *"is exactly a positive Hankel
moment matrix at every finite aperture and every jet order"*.

**And the Gamma/factorial normalization destroys it, provably.** Same file:

> *"The trace-Hankel lane uses a different normalization: its odd logarithmic moments are divided by
> `1!`, `3!`, `5!` in the first two-by-two block. This file proves that the distinction is
> structural … the determinant of `[[m₁, m₃/3!],[m₃/3!, m₅/5!]]` is [negative]."*

`VonMangoldtGammaBetaReflectionRankOneRepairNoGo` then closes the obvious repair: scaling by `2^{x+1}`
and taking first-prime dominance gives the limit form `L(i,j) = (log 2)^{i+j+2}/(i+j+1)!`, which two
explicit columns compress to `(log 2)²·diag(−1/12, −1/100800)` — **negative index two**, so no single
positive boundary channel can repair it.

### 11.1 What this changes

The wall is not "positivity cannot be created". It is:

> **Raw prime-side Grams are positive for free; the factorial/Gamma normalization required to match
> the Xi trace-Hankel lane sends them negative, with a certified negative determinant, and the
> negative index is two, so rank-one repair is impossible.**

That is a far sharper statement than §10's, it is supported by *proved* corpus theorems rather than my
judgement, and it identifies the villain precisely: **the Gamma factor**.

### 11.2 It is the same villain as Finding B

`jensen-polya-unconditional-frontier.md` §4 found, independently and from the Jensen side, that the
renormalization `γ(n) = n!·b(n)/(2n)!` is exactly what converts the free log-convexity of a Stieltjes
moment sequence into the log-concavity RH needs — "the entire difficulty of the lane sits in a
Gamma-factor renormalization of a manifestly positive moment sequence". The corpus has the **proved**
version of the same phenomenon on the prime side, with an explicit negative determinant and a
negative-index-two obstruction to repair.

Two lanes, reached independently, converge on one object: **the Gamma factor is where free positivity
dies.** That is the most precise form of the session's diagnosis, and unlike §10's version it is a
theorem in the tree rather than a pattern I asserted.

### 11.3 The one surviving frontier in this class

`VonMangoldtSuccessorBianchiHankelWeld` keeps positivity at every finite aperture and states its own
gap:

> *"It does not claim that its raw boundary vectors have a cofinal Hilbert limit; **that singular
> normalization is the remaining source frontier**."*

So in the Gram class the open question is not positivity but a **limit**: whether the finite-aperture
positive Hankel Grams admit a cofinal Hilbert limit. That is a different kind of obstruction from
every other in §10 — not an evaluation, not an equivalence, not a cap — and it is the only one of the
six that is neither proved impossible nor barred by this project's rules.

## Gates

- [x] fifth creator class (Gram/squares) surveyed — 480 unconditional PSD conclusions in the tree
- [x] §10's "positivity must be created" corrected: it *is* created, then normalized away
- [x] the destroyer identified as the Gamma/factorial normalization, with two proved no-gos
- [x] convergence with Finding B established — same object, one side proved
- [ ] cofinal Hilbert limit for the successor–Bianchi weld — the surviving frontier

## 12. Two corrections to the map, and a connection to the Deninger result

### 12.1 The `rh=` ranking is contaminated by parameter types

`SoninPositiveAperture` appeared in §1's table with `rh = 9` — the second-largest cluster. It is

```lean
def SoninPositiveAperture := {a : ℝ // 0 < a}
```

a **positive real number**, i.e. *data*, not a condition. My extractor counted every defined
capitalised identifier in an RH producer's statement, so parameter types inflate the ranking. The
inventory counts (`384`, `225`, the producer-kind split) are unaffected — those count theorems and
producers — but **the per-hypothesis `rh=` column must be read with a parameter-type filter**, and
`SoninPositiveAperture` is not a frontier. Recorded rather than silently re-run, because the same
artifact will bite the next person who uses the table.

### 12.2 The weld's frontier may be obstructed by a theorem proved elsewhere this session

`VonMangoldtSuccessorBianchiHankelWeld` states its own open step as a **cofinal Hilbert limit** of the
raw boundary vectors. Independently, `RHTower/DeningerCompleteCarrierSpectrumBounded.lean` proves,
axiom-clean:

```text
isSymmetric_I_smul_shiftedTheta         I·(θ − ½) is symmetric for the Hodge metric
theta_continuous                        on a COMPLETE carrier, Hellinger–Toeplitz makes θ bounded
exists_eigenvalue_norm_bound            hence every eigenvalue has modulus ≤ ‖θ‖
not_completeSpace_of_unbounded_spectrum unbounded spectrum ⟹ the carrier is not complete
```

The zeta zeros have unbounded imaginary parts. So **any carrier on which the Frobenius-flow generator
acts with the zeta spectrum is not a Hilbert space** — it must be pre-Hilbert, which is exactly the
corpus's own prescription that nuclear cohomology be formed before Hilbert completion.

That gives a concrete check for the weld's frontier, which I state as a check and not a result:

> **Does the cofinal limit required by the successor–Bianchi weld have to carry an unbounded
> operator?** If it does, `not_completeSpace_of_unbounded_spectrum` forbids the limit from being a
> Hilbert space, and the corpus's phrase *"that singular normalization is the remaining source
> frontier"* is naming the same obstruction from the other side. If it does not — if the limit is only
> required to carry the positive Hankel forms — the two are unrelated and the frontier stands.

I have not established which, and the distinction is decidable by reading what the downstream
consumer needs from the limit. That is the next concrete task in this lane and it is a reading task,
not a proof task.

## Gates

- [x] `rh=` ranking artifact identified and recorded (`SoninPositiveAperture` is data, not a condition)
- [x] Hellinger–Toeplitz obstruction connected to the weld's stated frontier, as a check
- [ ] determine whether the weld's cofinal limit must carry an unbounded operator

## 13. The reading task, done — and it reverses §11.3 and §12.2

I said the weld's "cofinal Hilbert limit" was the one live frontier, and that the next step was to
read what its downstream consumer needs. Done, and both claims were wrong.

**First: "cofinal Hilbert limit" occurs exactly once in the whole tree** — in the weld's own docstring.
It is not a `Prop`, not a hypothesis, and nothing consumes it. It is an author's note about what the
construction does not do, not a stated obligation. §11.3's "the only one of the six neither proved
impossible nor barred" was therefore about a frontier that does not exist as a formal object, and
§12.2's Hellinger–Toeplitz check has no target. Both withdrawn. This is the third time today I have
treated a docstring remark as an open theorem — the same failure as `DAoverGammaField`.

**Second: the limit is already proved.** The weld's one consumer,
`VonMangoldtSuccessorPrincipalRelativeHankel`, states:

> *"The finite successor–pointed-Bianchi weld has a divergent head Gram and a divergent tail Gram.
> Their source-fixed difference is nevertheless canonical … This file proves absolute summability at
> every order, finite-dimensional cofinal convergence, and an exact all-order Hankel law … **It does
> not assert positivity or identify the current with the completed Euler/Xi trace.**"*

So the chain is:

```text
finite apertures    positive Hankel Gram                      PROVED (weld)
cofinal limit       exists, all-order Hankel law              PROVED (principal relative)
positivity of the limit                                       NOT ASSERTED   ← frontier
identification with the completed Euler/Xi trace              NOT ASSERTED   ← frontier
```

**And the reason positivity is lost is the same as everywhere else.** The limit is a *difference* of
two divergent Grams. Positivity is free at every finite aperture and is not preserved by the principal
subtraction that makes the object finite.

## 14. The law, now with three proved instances

| where | the regularization | what it destroys | status |
|---|---|---|---|
| prime-side trace-Hankel | division by `1!, 3!, 5!` | Gram positivity — determinant goes negative, negative index two, rank-one repair impossible | **proved** (`VonMangoldtGammaFactorialNormalizationNoGo`, `…RankOneRepairNoGo`) |
| successor–Bianchi weld | principal subtraction head − tail of two divergent Grams | positivity of the cofinal limit | **stated as not asserted** |
| Jensen/Pólya | `γ(n) = n!·b(n)/(2n)!` | converts free log-convexity into the log-concavity RH needs | derived (Finding B), and it is the same factor |

> **The regularization that makes the object finite is exactly what kills the positivity that was free
> before it.**

That is the sharpest form this session's diagnosis reaches. It is not new mathematics; it is a
structural statement about this corpus's obstruction, and unlike §10's version it rests on proved
theorems in two of three instances rather than on a pattern I asserted. It also predicts where to
look: a route survives only if its regularization is *positivity-preserving* — which is exactly what
total positivity, Gram/square, and interlacing constructions are for, and exactly what the factorial
and principal-subtraction normalizations are not.

## Gates

- [x] "cofinal Hilbert limit" traced — a docstring remark, no formal object, nothing consumes it
- [x] §11.3 and §12.2 withdrawn
- [x] the real frontier located: positivity of the cofinal limit, and its identification with the Xi trace
- [x] the law stated with three instances, two of them proved in the tree
- [ ] a regularization of the prime-side Gram that is positivity-preserving — the only shape that survives

## 15. The mechanism behind the law, and the criterion it gives

§14 said the regularization is what kills positivity. Here is *why*, in one line, and the criterion
that follows.

### 15.1 Normalization is a Hadamard product

Normalizing a raw moment matrix entrywise, `m (i+j) ↦ c (i+j) · m (i+j)`, is the **Hadamard product
with the Hankel matrix of the normalizer**. By the Schur product theorem, `PSD ⊙ PSD = PSD`. Hence

> **A Hankel normalization `c` preserves positivity of every raw moment matrix iff the Hankel
> matrices of `c` are themselves positive semidefinite — i.e. iff `c` is a positive-definite
> sequence.**

Two immediate corollaries:

- **Separated divisors always work.** `c (i+j) = d i · d j` gives a Hadamard product with a rank-one
  positive matrix, so positivity survives with no hypothesis on `d` — this is diagonal congruence.
- **The factorial divisor is not separated**, because `log (i+j)!` is not additive in `i` and `j`,
  and it fails the criterion at the very first minor:

```text
det [[1/0!, 1/1!], [1/1!, 1/2!]] = det [[1, 1], [1, 1/2]] = −1/2 < 0 .
```

So `VonMangoldtGammaFactorialNormalizationNoGo`'s negative determinant is **not a fact about the von
Mangoldt moments at all** — it is a fact about the divisor sequence `1/k!`, which is not a moment
sequence. Any positive Gram normalized that way goes negative; the arithmetic is irrelevant.

### 15.2 Lean

`HTGeometry/HankelNormalizationPositivity.lean`, axiom-clean, registered, build green:

```text
hankel, hankel_normalize_eq_hadamard        normalization = Hadamard with the normalizer's Hankel
posSemidef_hankel_normalize                 PSD normalizer + PSD moments ⟹ PSD normalized
posSemidef_rankOne                          v i · v j is PSD
posSemidef_separated_normalize              d i · d j divisors preserve positivity unconditionally
det_reciprocalFactorialTwo                  = −1/2
not_posSemidef_hankel_reciprocalFactorial   1/k! is not a positive-definite sequence
```

### 15.3 What the criterion is worth

It converts the corpus's computed obstruction into a structural one, and it says exactly which
regularizations can survive:

| normalizer | positivity-preserving? | why |
|---|---|---|
| `d i · d j` (congruence) | **yes**, always | rank-one Hadamard |
| `r^{i+j}`, `r > 0` | **yes** | separated, `d k = r^k` |
| `1/(i+j+a)` | **yes** | `∫₀¹ t^{i+j+a−1}dt`, a moment sequence |
| `1/(i+j)!` | **no** | first minor `−1/2` |
| `1/(2i+2j+1)!` (the corpus's) | **no** | same reason |

So the shape that survives is a normalizer that is *itself* a moment sequence, and the factorial —
which is what the Gamma factor supplies in every lane examined today — is exactly the one that is
not. **That is the mechanism behind Finding B, behind the trace-Hankel no-go, and behind the Jensen
`n!/(2n)!` obstruction: one property of one sequence.**

## Gates

- [x] mechanism identified: normalization is Hadamard, criterion is Schur
- [x] separated/congruence divisors shown unconditionally safe (Lean)
- [x] `1/k!` shown not positive-definite at the first minor (Lean)
- [x] the corpus's no-go explained as a property of the divisor, not of the arithmetic
- [ ] whether the lane admits a *moment-sequence* normalizer that also renders the Gram finite

## 16. The question of §15.3, answered: the dichotomy is exact

**Is there a normalizer that is both a moment sequence and strong enough to make the divergent
prime-side Gram finite?** Yes — and answering it exposes the trade-off exactly.

### 16.1 An index-independent normalizer cannot work

By partial summation against Mertens, `∑_{n≤N} Λ(n)/n = log N + O(1)`, the head Gram entries are

```text
H i j  =  ∑_{n≤N} (Λ(n)/n) · log^{i+j} n   ~   L^{i+j+1}/(i+j+1) ,      L = log N .
```

A fixed normalizer `c (i+j)` cannot render this finite, because `L → ∞` and `c` does not depend on
`L`. **The normalizer must depend on the aperture.**

### 16.2 The aperture-dependent normalizer that works is separated

Take `c^{(L)} (i+j) = L^{−(i+j+1)}`. Then

```text
L^{−(i+j+1)} = L^{−1} · (L^{−i}) · (L^{−j}) ,
```

a **diagonal congruence times a positive scalar** — positivity-preserving with no hypothesis at all
(`posSemidef_separated_normalize`, and scaling by `L^{−1} > 0` is harmless). And it works:

```text
L^{−(i+j+1)} · H i j  →  1/(i+j+1)   =   ∫₀¹ t^{i+j} dt      (hilbertMatrix_eq_moment)
```

— the **Hilbert matrix**, the moment matrix of Lebesgue measure on `[0,1]`, positive definite.

So a positivity-preserving regularization of the divergent prime-side Gram exists, is elementary, and
its limit is positive definite. §15.3's question has answer **yes**.

### 16.3 And it costs everything

The limit `1/(i+j+1)` contains **no arithmetic**. It is determined by the leading Mertens asymptotic
alone; any sequence with `∑_{n≤N} w(n) = log N + O(1)` and `w ≥ 0` gives the same limit. Every
subleading term — which is where the zeros live — is scaled away by `L^{−(i+j+1)}`.

That is exactly why the corpus subtracts instead of scaling. The principal subtraction removes the
divergent leading part and **retains** the arithmetic in the difference, at the cost of positivity.

> **Dichotomy.**
> *Separated scaling*: positivity survives (congruence), arithmetic does not (limit is Hilbert).
> *Principal subtraction*: arithmetic survives (the difference is canonical), positivity does not.
>
> The two are the same operation viewed multiplicatively and additively, and no regularization of a
> divergent Hankel Gram can be both multiplicative-separated and arithmetic-retaining, because
> separated scaling is determined by the leading asymptotics.

### 16.4 Status

This is the sharpest form of the obstruction reached today, and it is elementary once stated: three
lines of partial summation, one observation that `L^{−(i+j+1)}` is separated, and one that a
congruence limit sees only the leading term. It explains, in a single mechanism, why
`VonMangoldtGammaFactorialNormalizationNoGo` fails (`1/k!` is not a moment sequence),
why `VonMangoldtSuccessorPrincipalRelativeHankel` cannot assert positivity (it subtracts), and why
Finding B's `n!/(2n)!` behaves as it does.

**It is not a route to RH and I do not present it as one.** It is a statement about what
regularizations of this object can do, and it closes the question I posed in §15.3 rather than
leaving it open.

## Gates

- [x] §15.3 answered: a positivity-preserving aperture-dependent normalizer exists (`L^{−(i+j+1)}`)
- [x] its limit identified as the Hilbert matrix, positive definite, arithmetic-free
- [x] the dichotomy stated: separated scaling keeps positivity and loses arithmetic; subtraction the reverse
- [x] all three corpus instances explained by the single mechanism

## 17. §16 was mis-framed; the correct statement is stronger and is now a theorem

§16 framed the trade-off as *separated scaling* versus *principal subtraction*. That framing is wrong,
and the reason exposes a better statement.

**Non-separated positivity-preserving normalizers exist.** By §15's criterion a normalizer preserves
positivity iff it is a moment sequence, and `c k = 1/(k+1) = ∫₀¹ tᵏdt` is a moment sequence that is
**not** of the separated form `d i · d j`. So "must be non-separated" was never a no-go.

**But the real obstruction is not about separation at all.** It is:

> **A convergent multiplicative regularization is blind to everything below the leading term.**
>
> If `f L = A·L^{k+1} + B·L^k + r L` with `r L / L^k → 0`, and `c L · L^{k+1} → δ`, then
> `c L · f L → A·δ`. The subleading coefficient `B` and the remainder never appear.

`HTGeometry/MultiplicativeRegularizationBlind.lean`, axiom-clean, registered, build green:
`tendsto_mul_regularized`, `mul_regularized_indep_subleading` (the same limit for *any* two
subleading data).

**Why that is the sharp form.** For the prime-side Gram, `H i j = ∑_{n≤N} w(n) log^{i+j} n` with
`∑_{n≤N} w(n) = log N + O(1)`, so `A_{i+j} = 1/(i+j+1)` and **the arithmetic lives entirely in `B`
and beyond**. Convergence of `c·H` forces `c^{(L)}_k · L^{k+1} → γ_k` — the leading term must be
exactly compensated — and then the theorem says the limit is `γ_{i+j}/(i+j+1)`, independent of the
arithmetic. This holds for **every** multiplicative normalizer, whether or not it is separated,
whether or not it preserves positivity.

So the corrected statement is:

| regularization | arithmetic | positivity |
|---|---|---|
| multiplicative, convergent (any `c`) | **provably lost** — `tendsto_mul_regularized` | inherited iff `c` is a moment sequence (§15) |
| subtractive (head − tail) | retained — the difference is canonical | **not inherited** |

§16's "separated vs not" was a distinction without a difference; the operative split is
**multiplicative vs subtractive**, and the multiplicative side is now closed by a theorem rather than
by an example.

**What it leaves.** Any arithmetic-retaining regularization of this Gram must be subtractive or
otherwise non-multiplicative, and for such a regularization positivity has to be *proved*, not
inherited. That is exactly the gap `VonMangoldtSuccessorPrincipalRelativeHankel` declines to assert,
and it is now the only remaining shape in this lane.

## Gates

- [x] §16's separated/non-separated framing withdrawn — non-separated moment normalizers exist
- [x] the correct no-go proved: convergent multiplicative regularization is subleading-blind (Lean)
- [x] the operative split identified as multiplicative vs subtractive
- [ ] positivity of a subtractive regularization — proved, not inherited: the remaining shape

## 18. The subtractive branch, reduced to a Loewner domination

§17 left one shape: an arithmetic-retaining regularization must be subtractive, and its positivity has
to be proved rather than inherited. That question can be restated so that both sides are manifestly
positive.

**The object.** The weld keeps one diagonal block and its forced mixed block, discarding the other:

```text
D = ∑ₙ cₙ ( uₙuₙᵀ + ½(uₙvₙᵀ + vₙuₙᵀ) ) ,
```

with `u` the successor feature, `v` the pointed-Bianchi feature, `u + v` the head feature. `D` is not
a Gram and inherits no positivity — the corpus's `…PositiveFiniteGram_firstCurvature_neg` and
`…PointedBianchiCross_firstCurvature_pos` are exactly the two signs that cancel.

**Completing the square** turns it into a difference of two Grams:

```text
uuᵀ + ½(uvᵀ + vuᵀ) = (u + ½v)(u + ½v)ᵀ − ¼ vvᵀ
```

so, exactly,

> **`D ⪰ 0`  ⟺  `¼ · Gram(v)  ⪯  Gram(u + ½v)`.**

Both sides are Grams with nonnegative weights, hence positive semidefinite. **The open question is a
domination between two positive objects, not a sign.** That is a better-posed problem: it is the kind
of statement Cauchy–Schwarz, interlacing, or a Schur-complement argument can address, whereas "is this
indefinite-looking block positive" is not.

`HTGeometry/GramCompletionOfSquare.lean`, axiom-clean, registered, build green:
`gram`, `mixed`, `shift`, `gram_add_mixed_eq`, `gram_add_mixed_posSemidef_iff`,
`gram_posSemidef_of_nonneg`.

**What it does not do.** It does not prove the domination, and the domination is not automatic:
termwise it would require `vₙ ∥ (uₙ + ½vₙ)`, i.e. `vₙ ∥ uₙ`, and the features here are
`uₙ(i) ∝ log(n+1)ⁱ − log(n)ⁱ` against `vₙ(i) ∝ log(n)ⁱ`, which are not proportional. So the
comparison is genuinely global.

**Where that leaves the lane.** The chain is now:

```text
RH ⟺ all Hankel determinants positive                         classical
     sizes 0,1,2 discharged by two theta moment inequalities   corpus
     sizes ≥ 3: positivity of the subtractive limit            open
       ⟺ ¼·Gram(v) ⪯ Gram(u + ½v)                              this section
```

and the last line is the first form of the question in which both objects are positive.

## Gates

- [x] the subtractive block written as a difference of two Grams (Lean, exact)
- [x] positivity restated as a Loewner domination between positive objects
- [x] termwise domination ruled out — the comparison is global
- [ ] the domination itself

## 19. The domination evaluated: the arithmetic is one Abel sum

§18 reduced the subtractive branch to `¼·Gram(v) ⪯ Gram(u + ½v)`. Evaluating that on a test vector
collapses it completely.

**The form.** With `aₙ = ⟨x,uₙ⟩`, `bₙ = ⟨x,vₙ⟩`, so `aₙ+bₙ = ⟨x,hₙ⟩` is the head pairing:

```text
⟨x, D x⟩ = ∑ₙ cₙ[(aₙ + ½bₙ)² − ¼bₙ²] = ∑ₙ cₙ aₙ(aₙ + bₙ) ,
```

— **the successor–head correlation**. The corpus's features are successive evaluations of one log-jet
function (`finiteVonMangoldtSuccessorPositiveFeature` uses the jet *difference* at `p+2`,
`…HeadFeature` the jet at `p+3`, and their sum identity is
`finiteVonMangoldtSuccessor_add_pointedBianchi_eq_headFeature`), so `aₙ = Pₙ₊₁ − Pₙ` and
`aₙ + bₙ = Pₙ₊₁`. The elementary identity `(b−a)b = ½(b−a)² + ½(b²−a²)` then gives, exactly,

```text
⟨x, D x⟩ = ½ ∑ₙ cₙ (Pₙ₊₁ − Pₙ)²  +  ½ ∑ₙ cₙ (Pₙ₊₁² − Pₙ²) .
```

**The first sum is nonnegative for free.** The second is a weighted telescope; Abel summation turns it
into boundary terms minus `∑ₙ (cₙ₊₁ − cₙ)Pₙ₊₁²`. With `c` the von Mangoldt weight `Λ(n)/n`, the
difference `cₙ₊₁ − cₙ` is `+Λ` at a prime following a composite and `−Λ` at a composite following a
prime — it oscillates with the primes.

> **So the positivity of the subtractive limit is governed by a single explicit prime-side Abel sum
> against `P²`, and by nothing else.**

`HTGeometry/GramCompletionOfSquare.lean` (extended), axiom-clean, build green: `sub_mul_self_split`,
`quadratic_form_split`, `quadratic_form_free_part_nonneg`,
`quadratic_form_nonneg_of_telescope_nonneg`.

### 19.1 What this settles and what it does not

It **settles the shape**: the Loewner domination of §18 is not a matrix problem at all. It is one
scalar inequality — a lower bound on `∑ₙ (Λ(n)/n − Λ(n+1)/(n+1))·P(log n)²` over polynomials `P` with
`P(0) = 0` — and everything else in the chain is free.

It does **not** settle the sign. I attempted a counterexample with a decreasing test polynomial; it
fails because the corpus's jet depths start at `1` (`positiveLogJetDepth i = i+1`), so `P(0) = 0` is
forced and a positive decreasing `P` on the log range is not available. Whether a peaked `P`
concentrated where `cₙ₊₁ − cₙ > 0` drives the form negative is exactly the open question, and it is
now a question about one Abel sum rather than about a matrix.

### 19.2 The circle closes on the corpus's own diagnosis

That Abel sum is a **prime-side upper bound on a quadratic form in `P`** — precisely the object
`positivity-creators-versus-transporters` says every lane needs and no lane supplies. So the last
surviving branch of the last surviving lane terminates at the same place, but this time the
termination is *derived*: nine sections of reduction, each exact, ending at one explicit sum over
primes, with everything else discharged as free.

That is the most useful form of a negative result I can produce: not "the lane fails", but "the lane
is exactly one prime-side Abel estimate, and here it is".

## Gates

- [x] the Loewner domination evaluated to `∑ cₙ aₙ(aₙ+bₙ)`, the successor–head correlation
- [x] split into a free square plus a weighted telescope (Lean, exact)
- [x] the arithmetic localized to `∑ (cₙ₊₁ − cₙ)Pₙ₊₁²` and nowhere else
- [x] counterexample attempt recorded and its failure explained (`P(0) = 0` is forced)
- [ ] the sign of the Abel sum

## 20. The sign, settled: the successor–head form is indefinite

§19 reduced the last branch to the sign of `∑ₙ cₙ(Pₙ₊₁ − Pₙ)Pₙ₊₁`. It is negative, and a **single
weighted source point** suffices.

At one point the form is `c(P t₁ − P t₀)P t₁` with `t₀ < t₁`, negative as soon as

```text
0 < P t₁ < P t₀ ,
```

i.e. the test function is positive at the later point and decreasing between the two. The constraint
`P 0 = 0` — forced by `positiveLogJetDepth i = i + 1`, and the reason my first counterexample attempt
failed in §19.1 — forbids a *globally* decreasing positive `P`, but not a locally decreasing one. The
quadratic

```text
P t = t(a − t) ,      t₁ < a < t₀ + t₁
```

does it: `P 0 = 0`; `P t₁ > 0` since `t₁ < a`; and `P t₀ − P t₁ = (t₀ − t₁)(a − t₀ − t₁) > 0` since
both factors are negative. Such an `a` exists for **every** `0 < t₀ < t₁`, because `t₁ < t₀ + t₁` —
no numerics, no properties of the primes, no bound on `log 2` or `log 3`.

`HTGeometry/GramCompletionOfSquare.lean`, axiom-clean, build green:
`exists_quadratic_decreasing_positive`, `successorHead_form_neg`.

### 20.1 Consequences

- The Loewner domination `¼·Gram(v) ⪯ Gram(u + ½v)` of §18 is **false**.
- The subtractive block `D = ∑ cₙ(uₙuₙᵀ + ½(uₙvₙᵀ + vₙuₙᵀ))` is **not positive semidefinite**,
  already at a one-point aperture with jet depths `{1,2}`.
- So the branch §17 identified as the only surviving shape — *arithmetic-retaining regularization,
  positivity proved rather than inherited* — **cannot be completed for this weld**. The positivity
  that `VonMangoldtSuccessorPrincipalRelativeHankel` declines to assert is not merely unproved; it is
  unavailable.

### 20.2 What this does and does not close

It closes the **weld's** subtractive branch, not subtractive regularization in general. Any weld that
keeps a diagonal block and its mixed block while discarding the other diagonal block has this form and
therefore this obstruction; the escape is a *different* subtraction, one whose kept part is not of the
shape `uuᵀ + ½(uvᵀ + vuᵀ)`.

And it is worth being precise about what was cheap here. Nine sections of reduction were needed to
reach a question this small, and once reached it took two lines. That is the argument for reducing
before estimating — the same reduction chain that made the answer trivial also made it *findable*,
whereas at §11 the same fact was invisible behind four layers of Gram and normalization language.

## Gates

- [x] the sign settled: the form is indefinite, one point and a quadratic suffice (Lean)
- [x] §18's Loewner domination **refuted**
- [x] the weld's subtractive branch closed
- [ ] whether a differently shaped subtraction avoids the `uuᵀ + ½(uvᵀ + vuᵀ)` form

## 21. The escape is closed too: finiteness and positivity exclude each other for the whole class

§20 closed the weld and named the escape — *a differently shaped subtraction*. The escape is closed
by the same two-line argument, applied to the general combination

```text
α·uuᵀ + β·½(uvᵀ + vuᵀ) + γ·vvᵀ .
```

Because the pairings `⟨x,uₙ⟩` and `⟨x,vₙ⟩` are unconstrained, positivity against every feature family
is exactly positivity of the scalar form `α a² + β ab + γ b²`, i.e.

```text
0 ≤ α ,    0 ≤ γ ,    β² ≤ 4αγ .
```

`HTGeometry/GramCompletionOfSquare.lean`, axiom-clean, build green: `blockCombination_nonneg_iff`,
`mixed_vanishes_of_second_block_discarded`, `second_block_pos_of_mixed_ne_zero`.

**The trade-off, complete:**

| requirement | forces |
|---|---|
| cancel the successor curvature defect | `β ≠ 0` — a mixed block is needed |
| positivity | `γ ≥ β²/(4α) > 0` — a positive share of the second diagonal block must be kept |
| finiteness | `γ = 0` — the second diagonal block is the divergent one and must go |

The second and third are incompatible: **`γ = 0` forces `β = 0`**
(`mixed_vanishes_of_second_block_discarded`), and `β = 0` is exactly the uncancelled successor
Gram — positive, but carrying the negative curvature the mixed block existed to cancel.

> **No linear combination of the three blocks is simultaneously finite, positive, and
> curvature-cancelling.** The weld is not one unlucky choice of coefficients; the whole
> two-parameter family is excluded.

### 21.1 Status of the lane

```text
RH ⟺ all Hankel determinants positive                          classical
     sizes 0,1,2 discharged by two theta moment inequalities     corpus (tight numerics)
     sizes ≥ 3 via the weld:
       multiplicative regularization  → arithmetic-blind         §17, proved
       subtractive, weld shape        → not PSD                  §20, refuted
       subtractive, any block shape   → finite ⊕ positive ⊕ cancelling impossible   §21, proved
```

Every branch of the weld route is now closed by a theorem rather than left open. The lane's remaining
options are outside this family entirely: a regularization that is neither multiplicative nor a linear
combination of the three blocks, or a different pair of features whose curvature defect does not need
cancelling.

### 21.2 Honest assessment

None of §17–§21 is deep. `blockCombination_nonneg_iff` is the discriminant of a binary quadratic form;
`successorHead_form_neg` is one quadratic; `tendsto_mul_regularized` is three limits. What took the
work was **arriving at questions small enough for those tools** — nine sections of exact reduction
through Gram, Hadamard, Loewner, Abel and scalar coordinates. The mathematics at the end is trivial;
the reduction is the content, and its output is that a route the corpus had left open at
*"does not assert positivity"* is not merely unproved but impossible in three distinct ways.

## Gates

- [x] the general block combination criterion proved (Lean)
- [x] `γ = 0 ⟹ β = 0`: discarding the divergent block forbids the mixed block
- [x] the finite/positive/cancelling trilemma stated and closed
- [x] all three branches of the weld route closed by theorems
- [ ] a regularization outside this family, or features with no curvature defect

## 22. The last branch closes by circularity, and the weld route is complete

§21 left one escape: *a feature pair with no curvature defect to cancel*. Closing it needs one
observation about what the defect is.

**The defect is Hankel, not positivity.** A weighted Gram `G i j = ∑ₙ cₙuₙ(i)uₙ(j)` is positive
semidefinite for free; it is a *moment* matrix only when it depends on `i + j` alone. The corpus's
mixed block exists to repair that — `…Cross_hankelCurvature_eq_neg_successor` is exactly the
statement that the cross block cancels the successor's Hankel-shift defect. So the trilemma of §21 is
sharper than I stated it: it is **Hankel ⊕ positive ⊕ finite**, and "curvature-cancelling" means
"Hankel".

**Power features have no defect.** `uₙ(i) = tₙ^i` gives `G i j = ∑ₙ cₙ tₙ^{i+j}` — Hankel and positive
semidefinite with no correction at all (`gram_power_isHankel`, `gram_power_nonneg`, axiom-clean).

**But that is the conclusion, not a route.** A finite positive semidefinite Hankel matrix *is* a
truncated moment matrix (Hamburger), hence representable by a power family against a positive
measure. So "a feature pair with no curvature defect" means precisely "the Gram is already the moment
matrix of a positive measure" — which for the prime-side data is exactly what was to be proved. And
the power family that would represent it, `tₙ = log n` against `Λ(n)/n`, is the divergent object the
differencing was introduced to repair in the first place.

### 22.1 The weld route, complete

```text
sizes ≥ 3 via the weld:
  multiplicative regularization       arithmetic-blind                    §17  proved
  subtractive, weld shape             not PSD                             §20  refuted
  subtractive, any block combination  finite ⊕ positive ⊕ Hankel impossible  §21  proved
  no-defect features                  ⟺ the conclusion (Hamburger)        §22  circular
```

**Every branch is closed**, three by theorems and one by circularity. The route the corpus left open
at *"does not assert positivity or identify the current with the completed Euler/Xi trace"* is now
closed at the first clause, and the closure is structural rather than an estimate.

### 22.2 What this session's negative results amount to

| lane | closed by |
|---|---|
| hypertranscendence / finite-phase | Ostrowski 1920 + zero-blindness of the DA type |
| Deninger weight-one polarization | axioms ⟺ `Re = 1/2` |
| Jensen/Pólya kernel side | Pólya 1926, de Bruijn 1950, certified `¬PF₅` |
| Jensen/Pólya `d = 4` | tight numeric on `γ(0..8)` |
| theta Hankel weld | §17, §20, §21, §22 — four branches, three theorems |

The last row is the only one where the closure is **new**: the others are literature or evaluation
walls, this one is a set of small theorems about the object itself. That is the session's actual
output, and it is negative knowledge — precise, checked, and of a kind that stops future spend.

## Gates

- [x] the defect identified as Hankel, not positivity — sharpening §21
- [x] power features shown defect-free (Lean)
- [x] the no-defect branch closed by Hamburger circularity
- [x] the weld route closed in all four branches

## 23. `D₀ ≤ 1.805` cannot be settled by regularity — the log-concave class straddles it

§7 said the constant `45/16` is tight to a few percent and concluded it "needs evaluation". That was
an assertion. Here it is a theorem.

The inequality is `16 m₀m₂ ≤ 45 m₁²`, i.e. `D₀ = m₀m₂/m₁² − 1 ≤ 45/16 − 1 = 1.80502…`. Two
log-concave densities on `[0,∞)` sit on opposite sides:

| density | `(m₀, m₁, m₂)` | `16m₀m₂` vs `45m₁²` | `D₀` |
|---|---|---|---|
| uniform on `[0,1]`, `Mₖ = 1/(k+1)` | `(1, 1/3, 1/5)` | `3.2 ≤ 5` **holds** | `4/5` |
| exponential `e^{−x}`, `Mₖ = k!` | `(1, 2, 24)` | `384 > 180` **fails** | `5` |

and `4/5 < 45/16 − 1 < 5`. `HTGeometry/MomentRatioClassStraddle.lean`, axiom-clean, registered, build
green: `uniform_satisfies`, `exponential_violates`, `uniform_dispersion`, `exponential_dispersion`,
`threshold_between`, `logConcave_class_undecidable`.

**Consequence.** No argument using only log-concavity — or any weaker regularity, since the class only
grows — can decide `ThetaCuspRelaxedFourthMomentConcentration`. The exponential is the extremal case
of the standard log-concave moment bound `M₀M₄ ≤ 6M₂²`, which is why that bound gives only `D₀ ≤ 5`;
and the uniform density shows the class reaches well below the threshold. **The threshold is interior
to the class**, so membership in it carries no information about the inequality.

This closes the *method* question for `D₀` the way §21 closed it for the weld: not "we have not found
a regularity argument" but "no regularity argument of this kind exists". What remains is the value of
one ratio of three specific integrals — a fact about the individual kernel, which this project's
no-computation rule forbids establishing.

It also retires my §16.3 remark that Brascamp–Lieb "misses by 10×". The miss is not a weakness of
Brascamp–Lieb; **any** class-based bound misses, because the class contains counterexamples.

## Gates

- [x] the straddle exhibited with exact moment triples (Lean)
- [x] `D₀`'s method question closed: regularity cannot decide it
- [x] §16.3's framing corrected — the failure is the class's, not the tool's
- [ ] the value itself — barred by this project's rules
