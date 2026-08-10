# Collective-repair spectral threshold conjecture and hostile gate

- **ID:** ULF-ALM-2
- **Stage:** 1-in-progress
- **Type:** MECHANISM CONJECTURE / COLLECTIVE-LAW-BIRTH LABORATORY
- **Status:** [MECHANISM NOT OBJECT] [CONJECTURE ATTACKED] [SURVIVING FINITE CELL]
  [PERRON--FROBENIUS/GORDAN/M-MATRIX PARENTS] [NOT AUTOCATALYSIS] [NOT RH]

## 1. Exact frontier

Three certified boundaries are already available.

1. Arbitrary state-indexed compatibility realizes every transition graph and is vacuous.
2. Diagonal self-evaluation and certificate-bearing mutation give source-normal middle mechanisms.
3. ULF-ALM-1 proves that one dependent repair can preserve semantic reach while birthing a viable
   history direction and destroying strict progress.

The remaining question is not whether one repair can do this. It is whether **interaction among
repairs** can create a regime unavailable to every repair in isolation.

## 2. Candidate mechanism

Let the old semantic rules be the basis vectors of `R^2`. For a coupling parameter `alpha>0`, add

\[
 r_1=(-\alpha,1),\qquad r_2=(1,-\alpha).
 \tag{CR.1}
\]

For execution multiplicities `(x_1,x_2,t_1,t_2)`, the semantic boundary is

\[
 D_\alpha(x,t)=
 (x_1-\alpha t_1+t_2,\;x_2+t_1-\alpha t_2).
 \tag{CR.2}
\]

The two repairs exchange the two resource directions through the swap operator

\[
 J(t_1,t_2)=(t_2,t_1),\qquad J^2=1,
 \tag{CR.3}
\]

and their dependency matrix is `C_alpha=alpha I-J`.

## 3. Bold conjecture

> **Collective repair threshold law.** Individually nonviable repairs can jointly create a viable
> circulation exactly when repair retention reaches the spectral radius of their interaction.
> At the threshold, strict progress is transduced into a singular repair-only history; above it,
> a full-support positive history is born. The interaction observer may remain recurrent and
> unchanged throughout this transition.

For the swap cell, the predicted threshold is `alpha=1`:

| chamber | predicted law |
|---|---|
| `0<alpha<1` | strict progress exists; feasible zero-history is trivial |
| `alpha=1` | repair-only feasible ray; symmetric inverse becomes singular |
| `alpha>1` | canonical full-support positive circulation; open positive-cost history |

Every one-repair subsystem is predicted to remain nonviable for all `alpha>0`.

## 4. Hostile conjecture loops

### Loop A -- one repair already carries the transition

`[FALSIFIED]`. With only `r_1`, a zero history has old second coordinate `-t_1`; feasibility forces
`t_1=0`. The same argument applies to `r_2`.

**Stronger survivor:** viability, if present, is an irreducibly collective property of the two
repairs.

### Loop B -- recurrent interaction forces viability

`[FALSIFIED]`. The swap has exact period two for every `alpha`, but the viability chamber changes at
`alpha=1`.

**Stronger survivor:** recurrence and viability are independent axes; spectral gain relative to the
recurrent interaction is load-bearing.

### Loop C -- positive carrier and loss of progress are unrelated events

`[FALSIFIED]` in this cell. Below threshold, coordinate sum is a strict progress certificate. At and
above threshold, a nonzero nonnegative zero-history contradicts every strict certificate.

**Stronger survivor:** the threshold is a Gordan-alternative transmutation between dual progress
and primal circulation.

### Loop D -- singular response is decorative

`[FALSIFIED]`. On the symmetric mode `s=(1,1)`,

\[
 C_\alpha s=(\alpha-1)s.
\]

Producing unit symmetric semantic load with symmetric repair therefore costs exactly
`1/|alpha-1|` in amplitude. The same threshold controls inverse failure and carrier birth.

### Loop E -- this proves autocatalysis

`[FALSIFIED]`. No catalyst, food set, replication kinetics, or positive growth exponent is present.
The theorem concerns feasible circulation and repair interaction only.

**Positive survivor:** call the phenomenon collective viability, not autocatalysis.

### Loop F -- this is new Perron--Frobenius mathematics

`[REDISCOVERED/BRIDGE]`. Perron--Frobenius theory, singular `M`-matrices, Gordan alternatives,
stoichiometric flux cones, and collectively autocatalytic sets own the ingredients. Recent explicit
catalysis work also proves that stoichiometry alone can be inconclusive and that some cores require
superposed circuits.

**Field residue:** the exact repair interpretation couples five mechanisms in one source-fixed
event: individual nonviability, collective carrier birth, coercivity loss, singular response, and
open lineage while observed interaction recurrence is stationary.

### Loop G -- threshold value one is coordinate artefact

`[FALSIFIED as an invariant claim; repaired statement survives]`. The number one comes from the
normalization of the swap coupling. The invariant statement is comparison of `alpha` with the
spectral radius `rho(J)=1`.

## 5. Literature boundary

Relevant parents:

- Müller--Flamm--Stadler, *What makes a reaction network chemical?*, arXiv:2201.01646: Gordan/Minty
  alternatives relate positive cycles and thermodynamic potentials;
- Ahmadinejad--Jambulapati--Saberi--Sidford, *Perron--Frobenius Theory in Nearly Linear Time*,
  arXiv:1810.02348: positive eigenvectors and singular/nonsingular `M`-matrix regimes;
- Hordijk--Wills--Steel, *Autocatalytic Sets and Biological Specificity*, arXiv:1307.2860:
  collectively autocatalytic food-generated sets;
- Golnik--Gatter--Stadler--Vassena, *Autocatalytic Cores in Reaction Networks with Explicit
  Catalysis*, arXiv:2603.02770: explicit-catalysis cores, Metzler structure, and superposition of
  elementary circuits.

These sources prevent a novelty claim for the linear ingredients. None is used to infer catalysis
or kinetics from the cell.

## 6. Exact paper target

Prove, without external route assumptions:

1. semantic surjectivity and exact kernel graph for every `alpha`;
2. trivial feasible kernel for each one-repair subsystem;
3. exact subcritical progress/no-cycle chamber;
4. exact critical repair-only ray;
5. canonical supercritical full-support circulation;
6. failure of every strict progress functional at and above threshold;
7. exact symmetric inverse amplification;
8. period-two interaction independent of chamber;
9. zero-endpoint histories with linearly unbounded execution cost at and above threshold.

If these close, promote the exact finite theorem to Stage 2. Do not generalize to arbitrary
irreducible nonnegative matrices before the finite mechanism is certified.

## 7. Scope

This candidate supplies no repair selector, source value of `alpha`, catalyst, infinite-dimensional
compactness, cofinal transport, proof-route endpoint, or RH implication. Its significance is a
collective mechanism unavailable to inspection of repairs one at a time.

## Log

- 2026-08-10 -- conjectured after the anti-oracle audit showed that source-normal diagonal and
  certificate-bearing mutation already close the easier structured-endogeneity gap.
- 2026-08-10 -- recurrence-causes-viability, individual-repair, autocatalysis, and novelty claims
  killed; spectral coalition threshold survived as the exact finite paper target.
