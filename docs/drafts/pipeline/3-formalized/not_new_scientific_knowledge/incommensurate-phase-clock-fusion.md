# Incommensurate phase reporters recover a real clock exactly

- **ID:** `incommensurate-phase-clock-fusion`
- **Status:** FORMALISED IN LEAN 4
- **Type:** quantum/cosmological clock observability theorem with RHTower specialization
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/IncommensuratePhaseClock.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeLogIncommensuratePhaseClock.lean`
- **Scientific novelty:** not claimed; the gain is a reusable exact-recovery interface

## Value relation

A single real clock phase at rate `a` is

\[
  P_a(t)=e^{iat}.
\]

For `a != 0`, it has period `2 pi/a`; therefore it cannot identify unrestricted real time.

Fuse two phase reporters:

\[
  P_{a,b}(t)=\bigl(e^{iat},e^{ibt}\bigr).
\]

If `b/a` is irrational, then

\[
  P_{a,b}(t_1)=P_{a,b}(t_2)\quad\Longleftrightarrow\quad t_1=t_2.
\]

The proof is exact.  Equality of the first phase gives

\[
  a(t_1-t_2)=2\pi n,
\]

and equality of the second gives

\[
  b(t_1-t_2)=2\pi m
\]

for integers `m,n`.  A nonzero clock difference would imply `b/a=m/n`, contradicting
irrationality.

For an arbitrary source coordinate `clock : X -> Real`, the paired phase reports satisfy

\[
  P_{a,b}(clock(x))=P_{a,b}(clock(y))
    \quad\Longleftrightarrow\quad clock(x)=clock(y).
\]

Thus phase fusion loses exactly the fibers already present in the clock coordinate and no
additional information.  It preserves and reflects injectivity.

## Physical interpretation

Finite-dimensional and Page--Wootters quantum-clock time states are superpositions whose clock
readout is carried by energy-dependent phases.  See
[Paiva et al., *Quantum Time and the Time-Dilation induced Interaction Transfer mechanism*,
arXiv:2407.00161](https://arxiv.org/abs/2407.00161).

Time--frequency quantum metrology treats frequency as an independent resource for time estimation;
see [Descamps--Fabre--Keller--Milman, arXiv:2210.05511](https://arxiv.org/abs/2210.05511).

Primordial standard clocks encode the scale factor through oscillatory features of massive-field
signals; see [Chen--Namjoo--Wang, *Quantum Primordial Standard Clocks*,
arXiv:1509.03930](https://arxiv.org/abs/1509.03930).  The theorem isolates a model-independent
observability fact: one oscillatory feature has a period ambiguity, while two incommensurate clock
frequencies remove the global ambiguity exactly.

The formal theorem does not assert that any experiment supplies noiseless phases or that a
particular cosmological model contains an irrational pair.  It gives the exact deterministic
interface once those phase values are available.

## Lean declarations

General HTGeometry:

- `phaseClockValue`;
- `phaseClockPair`;
- `norm_phaseClockValue`;
- `phaseClockValue_add_period`;
- `not_injective_phaseClockValue`;
- `phaseClockPair_injective`;
- `phaseClockPair_eq_iff`;
- `phaseClockPair_comp_injective_iff`;
- `phaseClockPair_comp_eq_iff`.

RHTower:

- `primeLogPhaseClockPair`;
- `primeLogPhaseClockPair_injective`;
- `primeLogPhaseClockPair_eq_iff`;
- `primeLogPhaseClockPair_two_three_injective`;
- `primeLogPhaseClockPair_two_three_comp_eq_iff`;
- `primeLogPhaseClockPair_two_three_comp_injective_iff`.

The RHTower specialization uses the already formalized theorem that

\[
  \frac{\log q}{\log p}
\]

is irrational for distinct primes.  Hence the concrete pair `(log 2, log 3)` is a globally faithful
real clock.

## Corpus gain

This is an exact nonlinear recovery theorem complementary to the linear Hilbert reporter-fusion
APIs.  It discharges the global phase-branch ambiguity whenever a real clock is exposed through two
incommensurate unit-phase channels.  The theorem applies to a hypertranscendental clock without
assuming or inventing an evolution law: the fused observation has precisely the same value fibers
as the original clock.

## No-go and positive replacement

**No-go.** A single noiseless phase value is still globally nonfaithful.  More phase precision or
larger Fisher information cannot remove the exact period lattice by itself.

**Positive statement.** Two incommensurate phase channels have trivial common period and recover the
unrestricted real clock value exactly.  Each channel is noninjective alone, while their fusion is
injective.

## RH pressure test

The `(log 2,log 3)` phase pair can recover any real RHTower height or source-clock coordinate from
its two phase values without branch choices.  This can discharge phase-recovery premises in future
source constructions.

It does not prove that a recovered height is zero, that a Xi zero lies on the critical line, or that
the prime--Gamma residual has the required sign.  Turning faithful readout into an RH criterion
without a source law would merely restate the target.  The positive RH relevance is narrower:
period ambiguity is no longer an obstruction once two distinct prime phases are genuinely exposed.

## Verification

- `lake build +GaloisForLFunctions.HTGeometry.IncommensuratePhaseClock`
- `lake env lean GaloisForLFunctions/HTGeometry/IncommensuratePhaseClock.lean`
- `lake build +GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock`
- `lake env lean GaloisForLFunctions/RHTower/PrimeLogIncommensuratePhaseClock.lean`
- no numerical computation and no full build
