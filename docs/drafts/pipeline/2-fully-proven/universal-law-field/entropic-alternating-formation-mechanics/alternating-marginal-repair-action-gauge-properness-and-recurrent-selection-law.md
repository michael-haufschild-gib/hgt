# Alternating marginal repair, action conservation, gauge properness, and recurrent selection law

- **ID:** `ULF-EAFM-1`
- **Stage:** 2 — fully proven on paper
- **Type:** BRIDGE / CALIBRATION THEOREM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [SINKHORN/IPFP CALIBRATION]`
  `[ENTROPIC REPAIR GENESIS] [EXACT ACTION CONSERVATION] [FUNCTIONAL REFLECTION]`
  `[GAUGE-PROPER FORMATION] [RECURRENT SELECTION] [LEAN-CERTIFIED] [NOT FIELD CORE] [NOT RH]`
- **Lean:** `GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation`

## 1. Higher pivot

The frontier's receivers are abundant. Its recurring failure is that a legal local correction does
not generate the next correction and no global source law prices the whole repair history. Static
formation Laplacians classify an already supplied response packet. Conditional-KL ledgers classify
an already supplied path law. Neither makes current failure produce the next legal operation.

This card isolates a clean finite calibration: **alternating entropic formation**. A positive incidence
packet carries two incompatible marginal laws. Failure of one marginal generates its unique
multiplicative repair. That repair changes the other marginal and therefore generates the next
legal repair. Positivity, relation incidence, observer information, functional reflection, hidden
gauge history, and global properness are consequences of one recursion rather than independent
slots.

The mathematics is the finite positive core of Sinkhorn/IPFP and information projection. The field
programme uses it as a typed calibration, not as its first or universal mechanism. The stronger
pre-existing endogenous-relaxation theorem already generates legality, least repair, completion,
recurrence, open lineage, and proper work from one source Laplacian. Here the target marginals and
alternation schedule remain supplied externally.

## 2. Positive bipartite source

Let `I,J` be nonempty finite sets. Let

\[
 a=(a_{ij})_{I\times J},\qquad a_{ij}>0,
 \tag{EAF.1}
\]

and let positive target marginals `r=(r_i)` and `c=(c_j)` have the same total mass

\[
 M=\sum_i r_i=\sum_j c_j>0.
 \tag{EAF.2}
\]

Write

\[
 s_i(a)=\sum_j a_{ij},\qquad t_j(a)=\sum_i a_{ij}.
 \tag{EAF.3}
\]

The endogenous repair operations are

\[
 (R_r a)_{ij}={r_i\over s_i(a)}a_{ij},\qquad
 (C_c a)_{ij}={c_j\over t_j(a)}a_{ij}.
 \tag{EAF.4}
\]

They are legal because every row and column mass is positive. Direct summation gives

\[
 s(R_ra)=r,\qquad t(C_ca)=c.
 \tag{EAF.5}
\]

They are also generated uniquely inside the legal multiplicative classes. If
`b_ij=u_i a_ij` and `s(b)=r`, then

\[
 u_i s_i(a)=r_i,
 \qquad
 u_i={r_i\over s_i(a)},
 \qquad
 b=R_ra.
 \tag{EAF.5a}
\]

The column statement is identical. Lean proves both uniqueness laws as
`bipartiteRowRepair_unique` and `bipartiteColumnRepair_unique`.

The next operation is not prewritten: applying `R_r` generally changes `t`, and applying `C_c`
generally changes `s`. Current residual therefore generates the next repair.

## 3. Entropic Pythagoras

For strictly positive finite arrays define unnormalized relative entropy

\[
 \mathcal D(x\Vert y)
 =\sum_{i,j}\left(x_{ij}\log{x_{ij}\over y_{ij}}-x_{ij}+y_{ij}\right).
 \tag{EAF.6}
\]

It is nonnegative and vanishes exactly when `x=y`.

### Theorem 3.1 — marginal repair is an exact information projection

If `x` has row marginal `r`, then

\[
 \boxed{
 \mathcal D(x\Vert a)
 =\mathcal D(x\Vert R_ra)+\mathcal D(R_ra\Vert a).}
 \tag{EAF.7}
\]

If `x` has column marginal `c`, then

\[
 \boxed{
 \mathcal D(x\Vert a)
 =\mathcal D(x\Vert C_ca)+\mathcal D(C_ca\Vert a).}
 \tag{EAF.8}
\]

### Proof

Put `u_i=r_i/s_i(a)`. Since `(R_ra)_{ij}=u_i a_{ij}`,

\[
 \log{x_{ij}\over a_{ij}}
 =\log{x_{ij}\over(R_ra)_{ij}}+\log u_i.
 \tag{EAF.9}
\]

The difference between the two sides of `(EAF.7)` is

\[
 \sum_i\log u_i
 \left(\sum_jx_{ij}-\sum_j(R_ra)_{ij}\right)=0
 \tag{EAF.10}
\]

because both row sums equal `r_i`. The column proof is identical. Nonnegativity and the equality
criterion are Gibbs' inequality. Equivalently, disintegrate a joint law into marginal and
conditional kernel; `(EAF.7)` is the exact KL chain rule with the conditional kernel held fixed.

The latter formulation is Lean-formalized without finite-state or absolute-continuity shortcuts:

\[
 D(\mu\otimes\kappa\Vert\nu\otimes\eta)
 =D(\mu\otimes\kappa\Vert\mu\otimes\eta)
  +D(\mu\otimes\eta\Vert\nu\otimes\eta).
 \tag{EAF.11}
\]

## 4. Global alternating action

Define the repair history

\[
 a_{2n+1}=R_r a_{2n},\qquad a_{2n+2}=C_c a_{2n+1}.
 \tag{EAF.12}
\]

The strictly positive product packet

\[
 x^*_{ij}={r_ic_j\over M}
 \tag{EAF.13}
\]

has both target marginals, so it is a predeclared feasible witness independent of the iteration.

### Theorem 4.1 — exact repair-action conservation

For every `N>=1`,

\[
 \boxed{
 \mathcal D(x^*\Vert a_0)
 =\mathcal D(x^*\Vert a_N)
  +\sum_{k=0}^{N-1}\mathcal D(a_{k+1}\Vert a_k).}
 \tag{EAF.14}
\]

Hence accumulated repair action is monotone and bounded above by the initial mismatch.

### Proof

At an even step `x^*` has the required row marginal, so `(EAF.7)` applies. At an odd step it has
the required column marginal, so `(EAF.8)` applies. Summing the identities telescopes.

### Corollary 4.2 — recurrent repair selects exact balance

If `a_N=a_0` for some `N>=2`, then

\[
 \boxed{s(a_0)=r,\qquad t(a_0)=c,}
 \tag{EAF.15}
\]

and every repair step is stationary.

### Proof

Substitute `a_N=a_0` in `(EAF.14)`. The finite initial divergence cancels, leaving a finite sum of
nonnegative repair costs equal to zero. Every cost vanishes, hence every consecutive pair is equal.
The first row repair being stationary gives `s(a_0)=r`; the following column repair being
stationary gives `t(a_0)=c`.

This is the new selection shape: **closed observed repair history plus positive conserved action
forces a fixed formation law**. Recurrence alone does not select; positivity alone does not select;
their fusion through a source-generated repair recursion does.

The Lean theorems `repairHistory_conservation` and `repairHistory_cycle_stationary` prove the full
finite-history law for arbitrary finite measures and extended KL divergence. They assume only exact
Pythagorean repair and finite target divergence, not a matrix model. The two-step theorem remains
as the smallest concrete corollary.

### Theorem 4.3 — global approximate-recurrence selection

Let a history `p_n` carry a finite real formation potential `Phi(p_n)` and nonnegative generated
actions `A_n` satisfying

\[
 \Phi(p_n)=\Phi(p_{n+1})+A_n.
 \tag{EAF.15a}
\]

Assume the potential is cofinally recurrent: for every `epsilon>0` and every cutoff `K`, some
`N>=K` satisfies

\[
 |\Phi(p_N)-\Phi(p_0)|<\varepsilon.
 \tag{EAF.15b}
\]

Then

\[
 \boxed{A_n=0\quad\text{for every }n.}
 \tag{EAF.15c}
\]

Indeed, telescoping `(EAF.15a)` gives

\[
 \Phi(p_0)-\Phi(p_N)=\sum_{j<N}A_j\ge A_n
 \qquad(N>n).
 \tag{EAF.15d}
\]

Choosing a recurrent `N>n` with potential gap below `A_n/2` contradicts `A_n>0`. This replaces
exact periodicity by cofinal approximate recurrence. Lean formalizes both the global conservation
identity and this selector as `realActionRepairHistory_conservation` and
`recurrentRealActionRepairHistory_stationary`.

## 5. Functional reflection is repair exchange

Transpose is the coordinate-free exchange of the two incidence ports. Directly,

\[
 \boxed{(R_ra)^\mathsf T=C_r(a^\mathsf T),\qquad
        (C_ca)^\mathsf T=R_c(a^\mathsf T).}
 \tag{EAF.16}
\]

It also preserves relative entropy:

\[
 \mathcal D(x^\mathsf T\Vert a^\mathsf T)=\mathcal D(x\Vert a).
 \tag{EAF.17}
\]

Thus functional reflection does not fix each repair. It exchanges the two repair laws and reverses
their composition order. This is stronger than declaring a reflection-invariant endpoint and more
honest than treating the involution as a selector. The action is information-neutral while the
alternating repair work can remain positive.

Lean proves both repair-transpose identities definitionally.

## 6. Hidden history and quotient properness

Write positive diagonal formation in logarithmic potentials:

\[
 F_a(x,y)_{ij}=e^{x_i+y_j}a_{ij}.
 \tag{EAF.18}
\]

The potential pair has a global gauge action

\[
 (x,y)\longmapsto(x+q\mathbf1_I,y-q\mathbf1_J),
 \tag{EAF.19}
\]

which leaves `F_a` unchanged. It is the exact closed-observer/open-history direction: `q` can escape
while the formed packet is stationary.

### Theorem 6.1 — exact stabilizer and positive formation radical

If every `a_ij>0`, then

\[
 F_a(x,y)=a
 \iff
 \exists q,\ x_i=q\ (\forall i),\ y_j=-q\ (\forall j).
 \tag{EAF.20}
\]

Define the infinitesimal formation energy

\[
 \mathcal E_a(x,y)=\sum_{i,j}a_{ij}(x_i+y_j)^2.
 \tag{EAF.21}
\]

Then

\[
 \boxed{
 \mathcal E_a(x,y)=0
 \iff
 (x,y)\text{ is a global gauge vector}.}
 \tag{EAF.22}
\]

Consequently `E_a` is positive definite and proper on the finite-dimensional quotient

\[
 (\mathbb R^I\oplus\mathbb R^J)/
 \mathbb R(\mathbf1_I,-\mathbf1_J).
 \tag{EAF.23}
\]

### Proof

If `F_a(x,y)=a`, positivity permits cancellation of `a_ij`; injectivity of `exp` gives
`x_i+y_j=0` for every pair. Fixing one `j_0` shows every `x_i=-y_{j_0}`; fixing one `i_0` then
shows every `y_j=y_{j_0}`. The converse is immediate. For `(EAF.22)`, every summand in
`(EAF.21)` is nonnegative and every weight is strictly positive, so zero total energy is equivalent
to the same equations `x_i+y_j=0`. A positive-definite quadratic form on a finite-dimensional
quotient has compact sublevels.

This quotient is not an arbitrary gauge declaration. It is forced simultaneously by exact
formation stabilizer and the Fisher/Gram radical. Lean proves gauge invariance, reflection
invariance, `(EAF.20)`, and `(EAF.22)`.

## 7. Fusion across five structurally different organs

| Organ | Generated shadow |
|---|---|
| relation/allocation | positive bipartite incidence and prescribed marginals |
| generation | current marginal residual uniquely generates the next scaling repair |
| positivity/information | KL Pythagoras and nonnegative repair action |
| functional equation | transpose exchanges row and column repair laws |
| recurrence/history/properness | recurrent packet forces balance; escaping potentials survive only in the one gauge kernel |

The exact conservation identity `(EAF.14)` is the fusion law. The recurrent fixed-point theorem is
its withheld prediction. Neither was used to define the matrix repairs.

The mechanism also explains two recurring corpus phenomena without identifying them:

1. positive scalar observation naturally forgets one coorientation/gauge direction;
2. global selection requires properness only after quotienting that unavoidable direction.

## 8. Sharp boundaries and no-gos

1. **Strict positivity is load-bearing.** With zero entries the gauge kernel splits by connected
   components of the support graph, and existence of a packet with marginals `(r,c)` becomes the
   Hall/transport feasibility problem.
2. **Feasibility is load-bearing.** Without one common `x^*`, Pythagorean steps need not telescope
   against the same target, so recurrence does not force balance.
3. **Finite divergence is load-bearing.** Extended equality `infinity=infinity+cost` cannot be
   cancelled.
4. **Reflection is not selection.** Transpose exchanges repairs and preserves action; it does not
   make the action zero.
5. **Gauge escape is real.** No observer of the formed matrix can recover the central potential
   line. Properness is exact only on the quotient.
6. **No convergence theorem is claimed.** Classical Sinkhorn theory proves much more under
   positivity. This card needs only one-step Pythagoras and finite recurrent selection.
7. **No RH conclusion.** A literal arithmetic source must still produce one positive bipartite
   packet whose two marginal repairs are the relevant reflected formation laws before Xi
   specialization. Fitting `a,r,c` from an already known divisor fails the source gate.

## 9. Exact bridge consequence

The common frontier grammar receives one exact entropic realization:

\[
 \boxed{
 \text{marginal failure}
 \to\text{least multiplicative repair}
 \to\text{new transverse failure}
 \to\text{alternating history}.}
 \tag{EAF.24}
\]

Its laws are:

1. repairs are source-local and residual-generated;
2. every repair pays an exact nonnegative action;
3. the action is conserved globally by Pythagorean telescoping;
4. reflection exchanges repair types;
5. recurrence selects the balanced law;
6. potential history is proper modulo one forced global gauge.

This does not found the field: the targets `(r,c)` and alternating schedule are external data, and
the stronger endogenous-relaxation laboratory predates it. Its positive survivor is nevertheless
useful and exact: any finite-action history satisfying the same Pythagorean ledger, including a
cofinally approximately recurrent real potential, has zero generated action at every step. A
future arithmetic realization may use that theorem, but constructing such a realization is a
separate source-generation problem.

## 10. Parent boundary

Sinkhorn scaling, iterative proportional fitting, Csiszár information projections, and Hilbert
projective contraction are established parent mathematics. Useful references include Nathanson's
finite positive-matrix account ([arXiv:1902.04544](https://arxiv.org/abs/1902.04544)) and Eckstein's
Hilbert-projective convergence framework ([arXiv:2311.04041](https://arxiv.org/abs/2311.04041)).
This card makes no external novelty claim. Its role is an exact Sinkhorn/Bregman bridge and a
reusable recurrent-action calibration inside this corpus, not the field core.

## 11. Lean certificate

`ConstitutiveEntropicAlternatingFormation.lean` formalizes:

- common-conditional marginal repair and exact KL Pythagoras;
- arbitrary finite-history action conservation and recurrent-cycle stationarity;
- global real-action conservation and cofinal approximate-recurrence selection;
- row/column mass repair and transpose exchange;
- logarithmic potential formation and global gauge invariance;
- exact positive stabilizer and energy radical;
- reflection invariance of formation energy.

The formal capstones are unconditional theorems over mathlib's extended KL divergence and finite
positive incidence packets. No axiom, `sorry`, computation certificate, or enlarged heartbeat is
used.

## Log

- 2026-08-13 — extracted after positive-face, cofinal-kernel-birth, completed-Witt, variable-
  recovery, and Schur-recursion pivots collided with existing corpus mechanisms.
- 2026-08-13 — paper proof closed; full finite-history theorem elaborated and integrated into the
  universal-law-field Lean module.
- 2026-08-13 — hostile whole-corpus audit demoted the field-core interpretation: the earlier
  abelian-relaxation theorem already supplies a stronger endogenous legality/repair/history/work
  mechanism. The Lean theorem remains valid as a bridge and positive survivor.
