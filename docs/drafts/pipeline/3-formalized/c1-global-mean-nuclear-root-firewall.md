# C1 global-mean nuclear-root firewall

- **ID:** C1-NR
- **Stage:** 3-formalized
- **Type:** [BRIDGE] [NOVELTY UNVERIFIED]
- **Scope:** literal adjacent-prime, all-depth normalized Pluecker carrier; not all C1.
- **Result:** its positive square root is nuclear; exact half-normalized completed Xi moment landing is impossible. First-trace mismatch alone remains open. RH is not proved.

## Corpus basis / surviving edge

Checked `formal_tools.py research` for global-mean factorization, nuclear roots, Schatten-half,
denominator bounds and exact moment landing. `GlobalMeanFirstTrace` reduces the scalar first
coefficient to raw occupation minus collision, but its `8/125` bound does not separate Xi.
`CriticalAdjacentPrimeCofinalFeshbach` supplies literal denominator decay; `PhysicalPluckerFirstTraceNoGo`
supplies exact reciprocal-depth node scaling; `RectangularTraceNorm` and `NuclearRankOneSchatten`
supply nuclear ideal laws. `SoninRegularizedMomentWeldNoGo` supplies ordered-moment rigidity, not a C1
conclusion. No matching C1 root-budget theorem found. Test the exact all-moment LAND edge, not a new
positivity package.

## Frozen source theorem / paper proof

Write `z=(e,n)`, `p=p_n`, `c=e+1/2`, `D_z=DenominatorTerm z`, `D=sum D_z>0`,
`w_z=D_z/D`. Existing bounds give

`D_z <= C c^-2 (log p)^4 p^-4`, with literal `C=368640 aperture^2/gap^4>0`.

Every one of the four node roots satisfies
`sqrt(node_z,i) <= (log 2)^-1/(e+1)`, including successor-depth coordinates.
Consequently

`sqrt(w_z)*sqrt(node_z,i) <= sqrt(C/D)*(log 2)^-1 * c^-2 * (log p)^2/p^2`.

Both one-dimensional majorants are summable: depth is a shifted p-series of exponent 2;
prime enumeration injects into the natural log-square/p-square series. Thus the literal root
incidence mass `sum_z sum_i sqrt(w_z)*sqrt(node_z,i)` is finite, without discarding labels.

Let `T` be the existing positive global-mean polarized operator and `b_u` its physical coordinate
orthonormal basis. Local centered coordinates have modulus at most the corresponding node root;
the six local probabilities sum to one. Hence their contribution to `Re <b_u,T b_u>` is at most
`sum_(z,i:label(z,i)=u) w_z node_z,i`. The dispersion term contributes at most twice this sum:
use `|a-b|^2 <= 2|a|^2+2|b|^2`, its literal factor `1/2`, normalized block mass one, and coordinate
means in `[0,1]`. All sums commute by nonnegativity / existing absolute nuclear convergence.

Therefore `||sqrt(T)b_u|| <= sqrt(3)*sum_(z,i:label(z,i)=u) sqrt(w_z)*sqrt(node_z,i)`.
Summing over physical labels costs no additional overlap multiplicity. The rank-one expansion
`sqrt(T)=sum_u |sqrt(T)b_u><b_u|` converges absolutely in nuclear norm, bounded by `sqrt(3)` times
the root incidence mass. Completeness of the coordinate basis identifies the sum with the actual
positive square root. This proves the source theorem without Xi selection or a target budget.

## Hostile audit / significance

- Do not assume block weights are dyadic; their actual majorant is used above.
- Do not take square roots termwise in the ordered double dispersion series: its naive root
  majorant need not sum. Collapse each physical diagonal first; normalization removes the extra
  packet index.
- This is stronger than positive trace class: it asserts summability of square roots of eigenvalues.
- It neither proves the disputed first trace unequal nor retires arbitrary signed, unbounded,
  or source-renormalized C1 transports. It tests this exact positive carrier's full moment landing.
- Positive survivor: coefficient-labelled, depth-sensitive nuclear-root budget stable under bounded
  transport. A surviving Xi architecture must evade that ideal, not merely restore one trace.

## Literature boundary

Nuclear decompositions, basis-diagonal root estimates and ideal stability are classical, not new
discoveries. Bourin--Uchiyama, *A matrix subadditivity inequality for f(A+B) and f(A)+f(B)*,
[Theorem 1.1](https://arxiv.org/pdf/math/0702475), includes the finite trace-square-root principle and
explicitly identifies the trace case as classical. Our proof uses the corpus nuclear-series API
directly, not an unformalized infinite-dimensional extension. Only the arithmetic application to
this literal carrier is a candidate new corpus result; no literature-absence claim.

## Verification state

- Paper source-root budget: dependency-closed above.
- Lean root budget, incidence profile, actual operator root, bounded transport and exact moment exclusions: five
  modules `GammaSewnPluckerNuclearRootBudget`, `GammaSewnPluckerNuclearRootIncidence`,
  `GammaSewnPluckerGlobalMeanNuclearRoot`, `GammaSewnPluckerNuclearRootTransportNoGo`,
  `GammaSewnPluckerGlobalMeanMomentNoGo`; wired and individually checked. `/tmp/HgtC1RootAudit.lean`:
  seven principal theorems use only `propext`,
  `Classical.choice`, `Quot.sound`. Formal lint passes; no full/umbrella build.
- Final unconditional theorem:
  `not_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_exact_primeArch_moments`.
  Generic consumer: `not_nuclear_half_normalized_primeArch_energy_moments`.
  This closes the literal all-moment candidate, not the wider class-space architecture.

## Exact bounded-transport consequence

For arbitrary bounded `A,B` on the literal physical Hilbert space, `A sqrt(T) B` is Schatten-one
by the two-sided nuclear ideal law. It therefore cannot have exactly the approximation-number
sequence of `xiOrderedSignedPrimeOperator`, which the corpus proves is not Schatten-one.
This exclusion is unconditional, retains every singular multiplicity, and allows nonlocal
bounded mixing. The additional all-moment exclusion below discharges the half-versus-full Xi
normalization explicitly, without assuming that spectral landing is given.

## Full moment exclusion: formalized bridge

The literal C1 convention requires `2 Tr(T^(r+1)) = normalizedPrimeArchMoment r`, not the
undoubled identity. Put `a_n=s_n(sqrt(T))` and repeat each singular value twice:
`b_n=a_(n/2)`. This is a decreasing nonnegative summable sequence; its squared positive power sums
are exactly twice those of `a`. Positive functional calculus and Lidskii give
`Tr(T^(r+1))=sum_n a_n^(2r+2)`. No square root of Xi is assumed here.

Suppose the exact C1 moment equalities hold. Every source Hankel quadratic becomes
`sum_k b_k^2*(sum_i v_i*b_k^(2i))^2 >= 0`; finite interchange is justified by summability and
boundedness of `b`. The corpus complete-Hankel capstone yields RH **inside the contradiction**.
Its multiplicity-exact Xi moment theorem then identifies the squared positive power sums of `b`
with those of the ordered full reciprocal-Xi singular sequence. Ordered moment determinacy gives
equality of the two decreasing sequences. But `b` is summable and the Xi sequence is not. Thus
the exact all-moment C1 landing is impossible. This argument does not settle its isolated first trace.

No added arithmetic assumption is present: only the hypothetical exact moment landing enters the
contradiction. Positive survivor is the proved root-incidence budget above. The repeated-spectrum
bridge and final theorem pass Lean, including their standard-axiom audit.
