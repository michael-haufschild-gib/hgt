# The Möbius Fisher connection has the exact anti-causal Ward boundary budget

- **ID:** `mobius-fisher-contact-commutator-ward-budget`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HT-TO-RH SOURCE WARD LAW
- **Scientific status:** `[PROVED HERE] [NOT AN RH PROOF] [COMPLETED GRAPH INCIDENCE OPEN]`
- **Parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `../3-formalized/not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`
  - `not_new_scientific_knowledge/ccm-hankel-boundary-relative-trace-four-unit-law.md`
  - `../3-formalized/luders-pinching-sonin-commutator-discharge.md`
- **Statement:** The normalized derivative of the pointed squarefree-Möbius source projection is
  a canonical self-adjoint rank-two observable of total Hilbert--Schmidt energy tending to four.
  Its scaled divisor-cutoff commutator has an explicit critical limit whose boundary density is
  eight.  The factor two in the existing commutator RH criterion converts that density back to
  the sharp four-unit threshold.

## Pointed Fisher connection

For `sigma>1`, put `epsilon=sigma-1`.  Use the normalized squarefree-Möbius source state and its
completed tangent

```text
psi_sigma(d)=Z(sigma)^(-1/2) mu(d)d^(-sigma/2),
chi_sigma=-2epsilon(log d-m_sigma)psi_sigma,             (1)
```

where

```text
||psi_sigma||=1,
<psi_sigma,chi_sigma>=0,
C_sigma:=||chi_sigma||^2 ->4.                            (2)
```

Let `Pi_sigma=|psi_sigma><psi_sigma|`.  The canonical self-adjoint Fisher connection is

```text
X_sigma
 =2sqrt(2) epsilon partial_sigma Pi_sigma
 =2^(-1/2)(|chi_sigma><psi_sigma|
             +|psi_sigma><chi_sigma|).                  (3)
```

It is fixed by the pointed source line; there is no choice of input vector, target vector, or
metric.  Rank-one Hilbert--Schmidt polarization and `(2)` give

```text
||X_sigma||_HS^2=C_sigma ->4.                            (4)
```

## General rank-two cutoff Ward identity

Let `P` be an orthogonal projection, `Q=1-P`, and abbreviate

```text
a=||P psi||^2,
b=||P chi||^2,
c=<P psi,P chi>,
C=||chi||^2,                                             (5)
```

for unit `psi` and `chi` orthogonal to `psi`.  Put

```text
X=2^(-1/2)(|chi><psi|+|psi><chi|).                       (6)
```

Then

```text
||[P,X]||_HS^2
 =(C-b)a+(1-a)b-2 Re(c^2)                               (7)
 =(C-b)a+(1-a)b-2|c|^2+4(Im c)^2.
```

Indeed,

```text
QXP=2^(-1/2)(|Qchi><Ppsi|+|Qpsi><Pchi|).                (8)
```

The two diagonal rank-one energies in `(8)` are `(C-b)a/2` and `(1-a)b/2`.
Since `<Qpsi,Qchi>=-<Ppsi,Pchi>`, the Hilbert--Schmidt cross pairing of the two
rank-one terms is `-conj(c)^2`, whose real part is `-Re(c^2)`.  Thus the energy of
`(8)` is half the first line of `(7)`.  Self-adjointness makes the opposite corner its adjoint, so
the commutator has twice that energy.  Finally
`Re(c^2)=|c|^2-2(Im c)^2`, proving the second line.

The previously claimed phase-blind correction `-2|c|^2` is therefore valid exactly when
`Im c=0`.  It is false for a general complex source line.  The squarefree-Mobius specialization
below has real coordinate functions and a diagonal real cutoff, so its truncated overlap `c` is
real and the original real formula is recovered without an added hypothesis.

Equation `(7)` is the source Ward law: the complete cutoff curvature of a pointed Fisher
connection is determined by the `2 x 2` truncated Gram matrix of its state and tangent.

## Critical local Gram limit

Let

```text
Y_sigma=epsilon log d
```

under the Born law `|psi_sigma(d)|^2`.  For `u>0`, let `P_(sigma,u)` be the source projection onto
`Y_sigma<=u`.  The proved critical boundary-layer law gives

```text
Y_sigma => Y,       Y~Exp(1),
epsilon m_sigma->1.                                       (9)
```

The three entries in `(5)` are bounded truncated moments on every fixed window.  Since the
limiting exponential law has no atom at `u`, `(9)` gives

```text
a_sigma(u)->a(u)=integral_0^u exp(-y)dy
                         =1-exp(-u),

c_sigma(u)->c(u)=integral_0^u 2(1-y)exp(-y)dy
                         =2u exp(-u),

b_sigma(u)->b(u)=integral_0^u 4(1-y)^2exp(-y)dy
                         =4[1-(1+u^2)exp(-u)].             (10)
```

The squarefree overlap `c_sigma(u)` is real.  Combining `(2)`, the real specialization of `(7)`,
and `(10)` proves the exact critical commutator energy

```text
E_W(u)
 :=lim_(sigma->1+) ||[P_(sigma,u),X_sigma]||_HS^2

 =4[(2+u^2)exp(-u)-2(1+2u^2)exp(-2u)].                  (11)
```

In particular,

```text
lim_(u->0+) E_W(u)/(2u)=4.                              (12)
```

For `0<u<=2`, the pointwise bound `4(1-y)^2<=4` on `[0,u]` gives `b(u)<=4a(u)`.
Dropping the negative term in `(7)` then gives the useful finite-window estimate

```text
E_W(u)<=8a(u)=8(1-exp(-u)).                             (13)
```

The eight units in `(13)` are not an enlarged RH threshold.  A self-adjoint cutoff commutator
contains two adjoint boundary orientations.  The RH consumer divides its energy by `2u`, so
`(12)` is exactly the four-unit boundary value.

## Conditional completed-source theorem

Let `D_Xi` be the closed anti-causal logarithmic-source operator and `P_u` its physical output
cutoff.  Suppose the finite squarefree Fisher connections `(3)`, after the explicit
prime--Gamma/Sonin source completion, produce Hilbert--Schmidt operators `A_(N,u)` such that:

1. on one source-defined graph core of `D_Xi`,

   ```text
   A_(N,u)f -> [P_u,D_Xi]f weakly;                       (14)
   ```

2. their completed commutator energy does not exceed the source Ward limit,

   ```text
   limsup_N ||A_(N,u)||_HS^2<=E_W(u).                    (15)
   ```

Then weak Hilbert--Schmidt lower semicontinuity and `(13)` give

```text
||[P_u,D_Xi]||_(HS,ext)^2<=8(1-exp(-u)).                 (16)
```

Therefore

```text
limsup_(u->0+) 1/(2u)||[P_u,D_Xi]||_(HS,ext)^2<=4,       (17)
```

and the existing anti-causal Cauchy-energy theorem proves the Riemann hypothesis.

The implication `(14)`--`(17)` is complete.  The proof-bearing open theorem is the direct
prime--Gamma/Sonin graph incidence `(14)` together with the nonexpansive source comparison `(15)`.

## Anti-theatre consequences

1. A Lüders disturbance is a two-sided off-diagonal object.  Targeting the one-sided strip
   `P_uD_Xi` with a four-unit source while using a two-sided pinching loses the exact factor two.
   The native target is `[P_u,D_Xi]`, for which the corpus already has the sharp RH criterion.
2. The bare pointed projection commutator has scaled profile `4(1-exp(-u))^2`; it vanishes too
   rapidly at the boundary.  Differentiating the pointed source line first produces `(3)` and the
   correct linear Ward profile `(12)`.  No clock reparameterization is used.
3. Gamma's rank-one resolution curvature cannot supply the transverse term: its boundary
   direction is source-independent.  Gamma/Sonin completion must transport the source connection
   `(3)`, not replace it by a universal factorial boundary vector.
4. The complex rank-two Ward law is phase-sensitive.  Replacing `Re(c^2)` by `|c|^2` erases the
   nonnegative orientation defect `4(Im c)^2` and is false unless the observed state--tangent
   overlap is real.  The positive survivor is the exact phase decomposition `(7)`, while the
   arithmetic source discharges the real-overlap interface through its concrete real form.

## General HT consequence

A normalized constrained HT source line has a canonical finite-rank connection even when its
full clock has no finite differential handle.  For every observation projection, the boundary
Ward curvature of that connection depends only on the truncated state--tangent Gram matrix
`(a,b,c)`, including the orientation term `4(Im c)^2`.  Complex phase is therefore a genuine
boundary value invariant, not removable decoration.  Infinite HT complexity and finite boundary
energy still separate cleanly: the former enters through whether the completed observation
preserves the pointed graph, while the latter is already fixed by the source line's Fisher
geometry.

## Gates

- [x] source-defined pointed Fisher connection constructed
- [x] exact complex rank-two cutoff Ward identity and phase-defect classification proved
- [x] all three critical local Gram entries computed
- [x] exact critical commutator profile computed
- [x] sharp four-unit boundary density recovered with the native factor two
- [x] one-sided Lüders factor mismatch removed
- [x] conditional commutator-to-RH implication closed
- [ ] construct the finite prime-power/Gamma/Sonin image of `(3)`
- [ ] prove direct graph-core convergence `(14)`
- [ ] prove the completed source comparison `(15)`
- [ ] RH

## Lean bridge certificate (2026-07-19)

The finite-`sigma` operator theorem and its hypothesis interfaces are now formalized:

- `HTGeometry/HilbertSchmidtRankOne.lean` centralizes the generic rank-one Hilbert--Schmidt norm
  and cross-polarization laws formerly duplicated in `RHTower`.
- `HTGeometry/RankTwoFisherCutoffWard.lean` proves the phase-correct complex law `(7)`, its
  `4(Im c)^2` decomposition, and the exact real-overlap classification.
- `HTGeometry/LpCoordinateProjection.lean` constructs arbitrary coordinate cutoffs as
  self-adjoint idempotents and proves exact cutoff-mass and cutoff-overlap value relations.
- `RHTower/MobiusCriticalFisherCutoffWard.lean` constructs `P_(sigma,u)` on the completed
  squarefree carrier, proves `a_sigma(u)` is exactly the existing critical-clock CDF, realizes
  `b_sigma(u)` and `c_sigma(u)` as the tangent norm and state--tangent overlap, proves
  `Im c_sigma(u)=0`, and derives the phase-free finite-`sigma` Ward law without caller-supplied
  projection, adjoint, orthogonality, or phase hypotheses.

Targeted compilation and the ordinary-axioms audit pass.  The exact remaining Lean-local bridge is
not the finite-rank Ward algebra: it is the critical convergence of the hard-cutoff first and
second centered moments `c_sigma(u)` and `b_sigma(u)` to `(10)`.  Beyond that remains the already
identified prime--Gamma/Sonin completed graph incidence and nonexpansive comparison `(14)`--`(15)`.

## Critical-limit Lean certificate (2026-07-19)

`RHTower/MobiusCriticalFisherCutoffLimits.lean` closes the remaining source-side limit bridge
identified above.  It proves:

- the all-orders cap--cut law
  `cappedMoment(k)=cutMoment(k)+u^k(1-cutMass)` for every natural `k`;
- generic summable first- and second-order centering laws, discharging the raw-moment interface;
- the exact hard-cut first and second moment limits;
- `c_sigma(u) -> 2u exp(-u)` and
  `b_sigma(u) -> 4[1-(1+u^2)exp(-u)]`;
- the completed finite-`sigma` commutator energy converges to the closed Ward profile `(11)`; and
- the one-sided normalized Ward profile converges to the sharp four-unit boundary value `(12)`.

All statements are unconditional and the ordinary-axioms audit passes.  Thus there is no longer a
Lean-local gap in `(9)`--`(12)`.  The exact remaining RH core is still the prime--Gamma/Sonin graph
incidence and nonexpansive completed-source comparison `(14)`--`(15)`; the present certificate does
not discharge either global source-completion theorem.

## Global finite-window strengthening (2026-07-19)

The closed profile permits a strict strengthening of `(13)`: Lean proves

```text
0 <= E_W(u) <= 8(1-exp(-u))     for every u >= 0.
```

Thus the paper's auxiliary restriction `u<=2` is unnecessary.  The proof uses the exact limiting
Gram entries: `a(u)>=0`, `b(u)>=0`, and
`b(u)<=4a(u)` because `4a(u)-b(u)=4u^2 exp(-u)`.  The two negative Ward corrections then give the
global bound.  This is a genuine strengthening of the source theorem, but it still remains
source-side and does not construct the completed graph comparison `(14)`--`(15)`.

The strengthened coefficient is sharp: Lean also proves

```text
lim_(u->0+) E_W(u)/(1-exp(-u)) = 8.
```

Hence no uniform bound `E_W(u)<=C(1-exp(-u))` can use `C<8`; the native two-orientation
normalization is forced at the source boundary rather than being an artifact of the proof.

## Conditional-implication Lean certificate

The last `[PROVED HERE]` item without a Lean witness was the conditional completed-source theorem
`(14)`--`(17)`: the card asserted the implication is complete while its two inputs stay open.  That
implication is now formalized in

`formal/GaloisForLFunctions/RHTower/MobiusFisherContactWardBudget.lean`

with the two open inputs appearing exactly as explicit hypotheses and nothing else assumed.

| Card item | Lean name |
|---|---|
| weak (entrywise) Hilbert--Schmidt lower semicontinuity | `RHTower.hsNormSq_le_of_tendsto_entries` |
| **`(14)`–`(16)`** the completed-source budget | `RHTower.completedSourceWardBudget` |
| the eight-unit budget has boundary density four | `RHTower.tendsto_eightMulCDF_div_two_mul` |
| **`(17)`** the four-unit boundary density of any profile inside it | `RHTower.eventually_div_two_mul_lt_of_le_eightMulCDF` |

`hsNormSq_le_of_tendsto_entries` is the analytic ingredient the card names ("weak Hilbert--Schmidt
lower semicontinuity") and is proved unconditionally: if the matrix entries of Hilbert--Schmidt
kernels converge and the energies are eventually `≤ B`, then every finite entry block of the limit
is a limit of finite blocks bounded by `B`, so the limiting energy is `≤ B`.  Weak operator
convergence on a total set supplies exactly this entrywise hypothesis, which is the content of
`(14)`.

`completedSourceWardBudget` then reads: for `u ≥ 0`, a completed family `A_N` of Hilbert--Schmidt
kernels with

* `(14)` entries converging to the kernel `K` of `[P_u, D_Xi]`, and
* `(15)` `hsNormSq (A_N) ≤ E_W(u)` eventually,

satisfies `hsNormSq K ≤ 8(1 − e^(−u))`, which is `(16)`; it composes the lower semicontinuity with
the already formalized global window bound
`RHTower.squarefreeMobiusCriticalFisherCutoffWardLimit_le_eight_mul_CDF`.  Finally
`eventually_div_two_mul_lt_of_le_eightMulCDF` gives `(17)`: any window profile inside the eight-unit
budget has `E(u)/(2u) < 4 + ε` near the boundary for every `ε > 0`, because
`8(1 − e^(−u))/(2u) → 4`.

### Remaining

Nothing in the formalisation of this card's own theorems: `(3)`, `(4)`, `(7)` (complex and
phase-blind forms with the exact real-overlap classification), `(10)`, `(11)`, `(12)`, `(13)` and
now the conditional implication `(14)`–`(17)` all compile with `#print axioms` equal to
`propext, Classical.choice, Quot.sound`.  The unchecked gates — the finite prime-power/Gamma/Sonin
image of `(3)`, the graph-core convergence `(14)`, the completed source comparison `(15)`, and RH —
are open **research**, and they are precisely the hypotheses of
`RHTower.completedSourceWardBudget`.
