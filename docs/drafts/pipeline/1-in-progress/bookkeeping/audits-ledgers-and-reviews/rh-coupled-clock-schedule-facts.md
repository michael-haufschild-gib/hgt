# Coupled prime/clock schedule: source attack

Owner: critical-clock product task. Global exhaustive schedule and RH remain open.

## Frozen target

Construct an exhaustive increasing prime-core history and advancing cutoffs
whose actual signed mixed payments, plus copied diagonals, cover cumulative
cutoff growth with one bounded initial action and every required integer wall
controlled. Do not replace this target by a sparse history or fixed-core limit.

## Corpus facts and failed compositions

- `exists_mobiusDivisorUniformReserveHistory` selects sparse actual pairs with
  an all-cutoff *unweighted* quadratic budget. It does not consume prescribed
  omitted primes, and does not bound the logarithmically weighted action.
- `exists_mobiusDivisorEvenCore_prescribed_prime_pair_reserve` includes every
  prescribed prime above a core-dependent threshold with a smaller partner;
  it strictly decreases the complete fixed-core coefficient. It gives no
  bound on that threshold as the core changes. A least-omitted-prime recursion
  therefore cannot currently invoke it at every stage.
- `exists_mobiusDivisorFiniteDebtFamilyTailReserveProducer` decreases every
  debt in a fixed finite family on a common eventual cutoff tail. Its constants
  depend on that family. Strict improvement alone does not imply complete
  repayment or termination of a prescribed insertion.
- The preceding clock-growth theorem forces positive logarithmic cost at every
  fixed finite prime core. Merely waiting for a reserve threshold is not free.

## Closed local producer [BRIDGE]

The source does pay a whole finite clock block after a prescribed sufficiently
large prime insertion. Scratch theorem
`exists_mobiusDivisorPrescribedClockBlock` is closed, with only `propext`,
`Classical.choice`, and `Quot.sound` in its axiom audit.
Promoted module:
`formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedClockBlock.lean`.
Named final audit passed:
`lake build GaloisForLFunctions.RHTower.MobiusDivisorPrescribedClockBlock`.
The module is imported by the RH umbrella; no full or umbrella build was run.
Index refresh and whitespace checks passed. Global lint retains the same four
unrelated unreachable modules recorded in `rh-finite-clock-counting-facts.md`;
no new failure was reported. Owned Lean processes exited and the scratch Lean
file was removed. Logs: `/tmp/hgt-coupled-clock-{proof,final-build,index,lint}.log`.

Exact statement: for every finite prime core `P`, there is `T(P)` such that
every prescribed prime `r>=T(P)` belongs to a prime core `Q` extending `P`
by at most two fresh primes, and for every integer `k>=1` there is `c>0` such
that, eventually in `M`, simultaneously for every integer `M<=L<=k*M`,

`W_1(Q,L)/L² + c log M <= W_1(P,M)/M²`.

`Q` is selected before `k`; no correlation or action-bound premise is assumed.
Empty cores use the first-prime reserve; odd cores use the literal eventual
release sign; nonempty even cores use the smaller-partner prescribed pair.

Proof: write the exact logarithmic clock defect as
`(1+log M) E(P,M)-W_1(P,M)`. Its original finite counting sum is
`sum log(M/r) r F_P(M,r)^2`. The source amplitude bound and square-root
telescoping prove

`0 <= (1+log M) E(P,M)-W_1(P,M) <= 4 C(P)² M²`,
where `C(P)=(3/5)*2^(P.card-1)` with natural subtraction in the exponent.

The known strict coefficient release then dominates this bounded defect and
the fixed clock increment `log k`, producing a positive multiple of `log M`
as actual payment throughout the entire next clock block.

More precisely, put `a=kappa(P)`, `b=kappa(Q)`, `epsilon=(a-b)/4>0`,
and `K=4 C(P)²`. Besides the two source-convergence thresholds, the proof
requires `epsilon log M >= K+(b+epsilon) log k`. It yields the margin
`epsilon log M`. Thus the cost and clock capacity remain explicit in the
paper proof; no uniformity in growing cores was inferred.

## Global construction attempt: unresolved quantifiers

The local theorem has order `P -> threshold -> prescribed prime -> extension
-> growth factor -> starting cutoff`. A forward exhaustive schedule needs
to pay an omitted prime from its already reached state and clock. These
quantifiers have not been reversed or controlled.

Two attempted compositions fail to establish the requested result:

- Choosing the least omitted prime need not satisfy `r>=T(P)`. Strict release
  for distant prescribed primes says nothing about that particular old debt.
- Choosing the next clock after learning a block's starting threshold may
  incur unpaid growth before that threshold. A finite-horizon diagonal choice
  of a later initial clock changes the initial budget; the preceding positive
  logarithmic source lower bound prevents calling that change free.

The next missing result is an actual repayment rule for a specified omitted
prime at the current clock, with its constants stable along the constructed
history. No global schedule, bounded critical action, or RH conclusion has
been obtained.

The proved block controls the retained core `Q`; it does not process every
active prime at its clock walls. Exhaustion as `n -> infinity` alone is not
completion at the original cutoff. A global construction must also control
the action after all primes relevant to each original wall are processed,
or supply an independent uniform comparison that proves that control.

## Current-clock source-depth boundary

The [current-clock depth certificate](../../rh-current-clock-depth-facts.md) proves
that certain inherited prime debts over every nonempty even prime core
cannot be repaid using only bounded-quotient helper windows. Even at an
arbitrarily later cutoff `L ≥ M`, repayment requires a fresh helper `q`
with `L/q ≥ η log L`. Helper sets and thresholds may change with the cutoff.
The positive survivor is a uniform lower bound from exactly preserved old
samples. This closes the bounded-quotient repair shortcut; an exhaustive
producer controlling deeper child fields remains missing.

## Current-clock positive producer

The [current-clock payment certificate](../../rh-current-clock-payment-facts.md)
constructs actual batches of size `capacity-1` with the full logarithmic
weight retained. Every prefix costs at most `R² M`; the endpoint removes
the initial weighted receiving square plus `delta M²`. Constants are uniform
over admitted cores, and the literal initial core has a premise-free instance.
This produces current-wall payment, but not transport to the next wall or
repayment of the larger debts requiring increasing child depth.

## Search audit

The focused schedule search completed with `partial=false` over an inventory
of 59,050 files and 761,601 indexed declarations; compiler metadata remained
mostly source-only. The broad exhaustion-method and log-defect searches
returned partial results. Their usable reserve, amplitude, and moment hits
were checked directly against source and in scratch Lean. No numerical
experiment or generic finite-exhaustion theorem supplied the missing payment.

## External method discrimination

Broad searches `viability` and `balancing` found
[Altschuler–Tikhomirov, September 2026](https://arxiv.org/abs/2609.14975),
whose theorem concerns freely chosen signs for independent random binary
arrivals, and [Karatzas–Kim, July 2026](https://arxiv.org/abs/2607.18705),
whose abstract distinguishes several pathwise viability/boundedness notions.
Neither supplies a source theorem for fixed Möbius signs and their dependent
prime mergers. No theorem from either paper is assumed.
