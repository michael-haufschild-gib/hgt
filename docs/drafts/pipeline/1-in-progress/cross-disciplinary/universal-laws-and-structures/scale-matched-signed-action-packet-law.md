# Scale-matched signed action packets generate the complexity front

- **ID:** `scale-matched-signed-action-packet-law`
- **Stage:** 1 -- in progress
- **Type:** bold conjecture / proposed universal growth primitive
- **Parent:** `../2-fully-proven/observer-dimension-replica-action-crowding-law.md`
- **Status:** `[SUPERSEDED] [HISTORICAL FAILURE LEDGER] [NO LEAN]`
- **Date:** 2026-08-08

## 2026-08-08 frontier correction

The full-packet formulation below is no longer the minimal open claim.  The paper-proved
`../2-fully-proven/radial-krylov-projected-complete-incidence-law.md` shows, before target
selection, that the original complete occupied-image replica action is bounded by its
Krylov-projected action plus the single factorial error

```text
2 r (B T)^(K+1)/(K+1)!.
```

It preserves every source fibre sheet, the projected occupied endpoint image, duplicate
invariance, and one-time return removal.  Radial scaling of a linear Hamiltonian ensemble changes
time but leaves the random Krylov flag and projected target image exactly fixed.  Therefore signed
packet contraction outside the causal carrier is proved and must not be left inside the conjecture.
The only live claim is contraction of the **carrier incidence action** itself at growing `K,r`.
It is now frozen precisely in `quenched-krylov-circuit-incidence-front-law.md`.  Everything below
is retained as the historical conjecture/failure record and is not an active paper claim.

## Public sentence

**Conjecture:** each additional copy of a quantum history takes one additional scale-matched unit
of physical time to forget; when every copy has dephased, complexity reaches its plateau, and only
recurrence can undo it.

## Why a new primitive is necessary

The corpus now proves that collision controls completed plateau capacity, locality controls the
maximum approach/escape speed, and metric Diophantine dimension controls recurrence exponents.  It
also proves that every attempt to resolve replica actions separately fails at Brown scale:
exponentially many actions crowd in an `O(n)`-dimensional observer space, and even their
amplitude-weighted absolute small-gradient mass has a central-bin floor.

The missing candidate object is therefore a **signed packet**, not an individual action.  Its
content is the complex sum of all return-free replica actions that one finite-resolution observer
cannot resolve separately.  The parent theorem now constructs it exactly as
`P_(k ne 0)(nu_1^{*r})`, followed by observer-action pushforward.  The conjecture says local static
dynamics cancels the resulting packets in order of replica size: order `r` becomes Haar-small
after time proportional to `r` up to a polynomial locality factor, until `r` reaches Hilbert
dimension.

## Frozen conjecture -- replica front law

Use the ordinary fixed-strength nearest-neighbour Pauli shell on `n` qubits, `D=2^n`, with one
independently uniform efficiently preparable stabilizer seed.  Fix constant errors
`0<epsilon_-<epsilon_+<1`, a finite local gate dictionary, and a target-independent return
filtration.  For each `1<=r<=cD`, form the common collision-adaptive light filter, remove the chosen
return sector once at source level, compress the complete depth

\[
 s_r=\left\lfloor{c_0r\over\log M_n}\right\rfloor               \tag{1}
\]

circuit image by its optimal occupied-endpoint design, and retain the **complex signed sum** of all
off-diagonal replica actions inside each unresolved observer packet.

There are universal constants `c,c_0,c_1,c_2>0` and a polynomial `p` such that, with pair
probability `1-o(1)`, the total return-free signed packet defect satisfies

\[
 \boxed{
 \mathcal E_{n,r}(t)\le e^{-c_1r}
 \quad\text{for every}\quad
 p(n)r\le t\le e^{c_2D},\qquad 1\le r\le cD.}                   \tag{2}
\]

Here `E_(n,r)(t)` must be constructed from the parent's exact signed lift
`nu_r^off=P_(k ne 0)(nu_1^{*r})`: remove `k=0` once, push forward to the finite-resolution
observer-action and occupied-incidence quotient, sum all fibre sheets with their complex
coefficients, evaluate the observer-action Fourier character as in the parent's `(29)--(30)`, and
only then apply the quotient norm.  It must be invariant under
circuit-label duplication, observer-coordinate duplication, and refinement of a packet partition.
Equation `(2)` is not permitted to mean a targetwise union, an absolute small-action majorant, or
stepwise deletion of the return sector.

## Physical meaning and shadows

If `(2)` holds, choose `r` proportional to `t/p(n)` until `r=cD`.  The completed diagonal moment and
occupied-incidence theorem then give

\[
 C_{\epsilon_-}(e^{-itH}\chi)
 =\Omega\!\left({\min\{t/p(n),D\}\over\log M_n}\right)          \tag{3}
\]

outside the one paid return sector.  Thus:

| Shadow | Consequence of one packet law |
|---|---|
| local simulation cone | matching upper speed and no instantaneous jump |
| replica order `r<t/p(n)` | linear pre-plateau lower growth |
| maximal useful `r=Theta(D)` | plateau depth `Theta(D/log n)` |
| temporal union at fixed `r` | doubly-exponential continuous plateau |
| metric Diophantine return | later return to the easy seed |
| all-time low-dimensional support | locality remains singular from Haar throughout |

The risky new prediction is the **replica front**: moment order, not spectral gap, is the clock of
complexity growth.  Fixed-order spectral ramps and late completed-phase plateaux are its low-order
and infinite-time shadows.

## Why this is not “known theory plus one sharper hypothesis”

- Random-circuit design growth uses fresh gates at every step; `(2)` uses one quenched static
  generator forever.
- Random-matrix spectral ramps control a second-order trace statistic; `(2)` controls growing
  return-free target-incidence packets through `r=Theta(D)`.
- Ordinary phase equidistribution is qualitative and late-time; `(2)` orders dephasing by replica
  scale and predicts the full pre-saturation slope.
- Worst-action Diophantine and transversality bounds are incompatible with observer crowding; `(2)`
  relies on cancellation among the crowded actions rather than excluding them.

## Falsifiers

The conjecture is false if any of the following occurs with nonvanishing pair probability:

1. an off-return signed packet retains magnitude `e^{-o(r)}` at some `t>=p(n)r`;
2. a circuit-dependent selector can align packet signs after optimal incidence compression;
3. a conserved or coboundary packet survives source-first return removal;
4. the packet definition cannot be made invariant under refinement of observer cells;
5. one static local family has the proved completed plateau but an arbitrarily long pre-front delay.

## Exact open core -- corrected

`[OPEN CORE]` For the ordinary fixed-strength local shell, prove a quenched growing-replica bound
on the positive carrier incidence action

```text
integral_(R^c)
  ||Proj_(span{(P_K z)^(tensor r):z in Z_s})
      (P_K exp(-itH)psi_0)^(tensor r)||^2 dmu,
```

with `K` scale-matched to `BT`, strong enough to beat the projected occupied circuit-image entropy
through `r=Theta(D)`.  The return set is fixed independently and paid once.  This is the exact
causal part that the proved factorial reduction cannot discard.

Promising discriminators, not assumptions:

- a spacetime-dual transfer operator whose nontrivial packet sector has a uniform gap;
- convolution by `nu_1` on the signed multiplicity lift, with the return projection applied only
  after the full power;
- a signed replica cavity operator on the occupied incidence quotient;
- an associated-graded jet/Pauli action in which local word depth produces cancellation rather than
  mere linear span;
- an exact convolution transfer from a provable static spectral-ramp model, upgraded from fixed
  trace order to adaptive state packets.

## Hostile preliminary attack

- **Not implied by the current corpus.** Completed-time orthogonality supplies the endpoint
  `r=Theta(D)` only after an unquantified horizon.
- **Not implied by Ippoliti's static ramp.** That theorem is second order, time-smoothed,
  thermodynamic, and sector-restricted; local simulation keeps state complexity polynomial at ramp
  onset.
- **Not implied by dual unitarity.** Existing contractions are fixed replica order or trace
  observables and do not survive the adaptive circuit incidence operation through `r=Theta(D)`.
- **Could be false.** A static one-parameter orbit has exact quasiperiodicity and may contain
  coherent packet revivals before the final recurrence scale.
- **Definition now exact only before quotient norm.** The parent convolution law closes sheet
  multiplicity, source-first return removal, and Fourier evaluation.  A partition-invariant
  occupied-incidence norm and its interaction with adaptive circuit targets remain unproved.
- **Positivity survives for the seed.** For `z=chi`, filtered one-copy coefficients are
  nonnegative, so the lift is a positive measure.  Cancellation must arise from its Fourier
  character, not from the word “signed” or from total-variation contraction.

Verdict: `[SURVIVES PRELIMINARY ATTACK]` as a falsifiable universal target, not as a theorem.

## Required next move

Do not spend effort on the exterior Taylor packet; it is already factorially closed.  Attack the
projected carrier action above.  The radial--Krylov rigidity theorem permits exact disintegration
into a fixed-shell angular carrier geometry and radial time mixture.  A dimension estimate alone is
invalid: one projected target parallel to the carrier makes rank one action maximal.  Required new
input is quenched angular incidence anti-concentration for the actual shallow-circuit image, not a
minimum gap, raw Jacobian, targetwise union, or stepwise killed transfer operator.
