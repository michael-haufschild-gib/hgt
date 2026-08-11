# Collective-repair spectral threshold and open-history law

- **ID:** ULF-ALM-2
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM / COLLECTIVE-LAW-BIRTH LABORATORY
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [COLLECTIVE VIABILITY] [SPECTRAL THRESHOLD] [COERCIVITY TRANSMUTATION]
  [SINGULAR RESPONSE] [OPEN HISTORY] [BRIDGE] [LEAN-CERTIFIED] [NOT AUTOCATALYSIS] [NOT RH]

## 1. Source law

Let the old semantic state space be `V=R^2`, with old rule vectors

\[
 e_1=(1,0),\qquad e_2=(0,1).
 \tag{CT.1}
\]

For `alpha>0`, adjoin two repairs

\[
 r_1=(-\alpha,1),\qquad r_2=(1,-\alpha).
 \tag{CT.2}
\]

For nonnegative execution multiplicities `x_1,x_2,t_1,t_2`, define

\[
 D_\alpha(x_1,x_2,t_1,t_2)
 =x_1e_1+x_2e_2+t_1r_1+t_2r_2.
 \tag{CT.3}
\]

Equivalently,

\[
 D_\alpha(x,t)
 =(x_1-\alpha t_1+t_2,\;x_2+t_1-\alpha t_2)
 =x-(\alpha I-J)t,
 \tag{CT.4}
\]

where `J(t_1,t_2)=(t_2,t_1)` is the swap. A **feasible circulation** is a nonzero vector
`(x,t)>=0` in `ker D_alpha`.

## 2. Conservative semantics and exact history graph

### Theorem 2.1

For every real `alpha`:

1. `D_alpha` is surjective;
2. its kernel is the graph
   \[
   \boxed{
   x_1=\alpha t_1-t_2,\qquad
   x_2=\alpha t_2-t_1.}
   \tag{CT.5}
   \]

#### Proof

Every `y in R^2` equals `D_alpha(y_1,y_2,0,0)`, proving surjectivity. Expanding
`D_alpha(x,t)=0` gives the two equations in `(CT.5)`, and substituting those equations back gives
zero. QED.

Thus the two repairs do not enlarge semantic reach. They change the feasible history cone.

## 3. Irreducibly collective viability

### Theorem 3.1 -- neither repair is viable alone

For every `alpha>0`, each subsystem consisting of the two old rules and only one repair has trivial
feasible kernel.

#### Proof

With only `r_1`, put `t_2=0` in `(CT.5)`. Then `x_2=-t_1`. Feasibility gives both `t_1>=0` and
`-t_1>=0`, hence `t_1=0`, and then `x_1=x_2=0`. The argument for `r_2` is symmetric. QED.

This is the load-bearing nonadditivity: no individual repair contains the viable mechanism.

## 4. Exact spectral phase transition

### Theorem 4.1 -- subcritical, critical, and supercritical chambers

Assume `alpha>0`.

1. **Subcritical chamber `0<alpha<1`.** The feasible kernel is `{0}`. The functional
   \[
   \ell(u,v)=u+v
   \tag{CT.6}
   \]
   is strictly positive on all four rule vectors.
2. **Critical chamber `alpha=1`.** The feasible kernel is exactly
   \[
   \boxed{
   \{(0,0,t,t):t\ge0\}.}
   \tag{CT.7}
   \]
   The born circulation uses both repairs and no old rule.
3. **Supercritical chamber `alpha>1`.** The vector
   \[
   \boxed{h_\alpha=(\alpha-1,\alpha-1,1,1)}
   \tag{CT.8}
   \]
   is a strictly positive full-support circulation.
4. At and above threshold no linear functional is strictly positive on all four rule vectors.

#### Proof

Suppose `(x,t)>=0` and `D_alpha(x,t)=0`. Summing the two boundary coordinates gives

\[
 0=x_1+x_2+(1-\alpha)(t_1+t_2).
 \tag{CT.9}
\]

If `alpha<1`, every summand in `(CT.9)` is nonnegative. Hence all vanish. In particular
`t_1+t_2=0`, so `t_1=t_2=0`, and `(CT.5)` gives `x=0`. Further,

\[
 \ell(e_1)=\ell(e_2)=1,
 \qquad
 \ell(r_1)=\ell(r_2)=1-\alpha>0,
\]

proving strict progress.

At `alpha=1`, equations `(CT.5)` become `x_1=t_1-t_2` and `x_2=t_2-t_1`. Nonnegativity forces
`t_1=t_2`; then `x_1=x_2=0`. Conversely every vector in `(CT.7)` is feasible and lies in the
kernel.

If `alpha>1`, direct substitution in `(CT.4)` gives `D_alpha(h_alpha)=0`, and every coordinate in
`(CT.8)` is strictly positive.

Finally, at `alpha=1` use the nonzero feasible circulation `(0,0,1,1)`; above threshold use
`h_alpha`. If a functional were strictly positive on every rule, applying it to the positive
linear combination defining either zero-boundary circulation would give a strictly positive number
equal to zero. Contradiction. QED.

The spectral language is exact: `J` has eigenvalues `1,-1`, so its spectral radius is one. The
positive symmetric mode crosses from progress to circulation precisely when `alpha` crosses
`rho(J)`.

## 5. Singular response at carrier birth

Let `C_alpha=alpha I-J` and `s=(1,1)`. Then

\[
 \boxed{C_\alpha s=(\alpha-1)s.}
 \tag{CT.10}
\]

### Theorem 5.1 -- exact symmetric amplification

For every `epsilon>0`, at `alpha=1+epsilon`, the unique symmetric repair vector cancelling the
unit symmetric old load is

\[
 t_\epsilon=\epsilon^{-1}s,
 \tag{CT.11}
\]

and its `l^1` execution size is `2/epsilon`.

#### Proof

Equation `(CT.10)` gives

\[
 C_{1+\epsilon}(\epsilon^{-1}s)=s.
\]

On the one-dimensional symmetric line, multiplication is by the nonzero scalar `epsilon`, so the
preimage is unique. Both coordinates of `t_epsilon` equal `1/epsilon`; their sum is `2/epsilon`.
QED.

Thus carrier birth and inverse-response blow-up occur at the same threshold. This does not select
the threshold; `alpha` remains source data.

## 6. Recurrent interaction, open lineage

### Theorem 6.1

1. `J^2=I`, while `J(1,0)=(0,1)!=(1,0)`. Hence the visible interaction has exact period two for
   every `alpha`.
2. For `alpha>=1` and `n in N`, let
   \[
   H_n=n h_\alpha.
   \tag{CT.12}
   \]
   Then `D_alpha(H_n)=0` and
   \[
   \boxed{\|H_n\|_1=2\alpha n.}
   \tag{CT.13}
   \]
   Consequently semantic endpoint is stationary while positive execution history is unbounded.
3. No potential depending only on the semantic endpoint can integrate unit execution cost on these
   histories.

#### Proof

The swap identities are immediate. Linearity and Theorem 4.1 give `D_alpha(H_n)=0`. Since
`alpha>=1`, all coordinates of `h_alpha` are nonnegative, and their sum is

\[
 2(\alpha-1)+2=2\alpha.
\]

This proves `(CT.13)` and unboundedness. Every `H_n` starts and ends at the same semantic state, so
any endpoint-potential difference is zero; unit execution cost is `2 alpha n>0` for `n>0`. QED.

The recurrent dependency observer is identical in all three chambers. It does not determine
viability, singularity, coercivity, or lifted cost.

## 7. Exact mechanism law

The cell proves the following route-independent law.

\[
\boxed{
\begin{array}{c}
\text{individually nonviable conservative repairs}\\
\text{can cross a collective spectral threshold}
\end{array}
\Longrightarrow
\begin{array}{c}
\text{positive carrier birth}\\
\text{strict-progress loss}\\
\text{singular inverse response}\\
\text{open zero-endpoint lineage.}
\end{array}}
\tag{CT.14}
\]

This strengthens ULF-ALM-1. Viability need not be visible in any repair separately; it can be born
only from repair interaction. Therefore a theory auditing proposed laws one route, component, or
repair at a time can miss the first viable composite.

## 8. Hostile scope

1. Perron--Frobenius, singular `M`-matrix, Gordan-alternative, flux-cone, and collectively
   autocatalytic-set ingredients are established mathematics. This theorem is a `[BRIDGE]` and a
   new field calibration, not a priority claim for those ingredients.
2. The theorem proves circulation, not explicit catalysis, replication, kinetics, or persistence.
3. Period two does not cause the transition; the parameter relative to spectral radius does.
4. The source does not select `alpha=1`.
5. The theorem is finite-dimensional and gives no cofinal compactness or formation law.
6. It supplies no proof-route endpoint or RH implication.

## 9. Parent boundary

Primary parents:

- Müller--Flamm--Stadler, *What makes a reaction network chemical?*, arXiv:2201.01646;
- Ahmadinejad--Jambulapati--Saberi--Sidford, *Perron--Frobenius Theory in Nearly Linear Time*,
  arXiv:1810.02348;
- Hordijk--Wills--Steel, *Autocatalytic Sets and Biological Specificity*, arXiv:1307.2860;
- Golnik--Gatter--Stadler--Vassena, *Autocatalytic Cores in Reaction Networks with Explicit
  Catalysis*, arXiv:2603.02770.

## 10. Lean certification

The exact two-resource mechanism is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveCollectiveRepairThreshold`. Its unconditional capstone
contains semantic surjectivity, one-repair nonviability, all three chambers, the strict-progress
transition, period-two interaction, and unbounded zero-boundary history. Separate certified
theorems give the exact kernel graph, symmetric eigenmode, inverse amplification, uniqueness,
history-size law, and endpoint-potential no-go.

Direct foreground elaboration and the leaf build pass. Axiom prints for significant declarations
and the unconditional capstone report only `propext`, `Classical.choice`, and `Quot.sound`. The
module is wired into `HTGeometry.UniversalLawField`; its final foreground build passes with 11,587
jobs. The module contains no `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, computational
certificate, route hypothesis, or RH premise. Full formal lint reaches the module and reports no
target error; its nonzero exit is caused by unrelated unwired `RHTower.Sieve.*` and
`HTGeometry.AbelianZetaGas.NaturalBoundary` modules.

## Log

- 2026-08-10 -- all nine clauses dependency-closed on paper after hostile separation of recurrence,
  autocatalysis, source selection, and mathematical-priority claims.
- 2026-08-10 -- exact mechanism formalized in Lean and wired into the Universal Law Field umbrella.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
