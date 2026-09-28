# Bilateral exponential repair scale, reporter exchange, and recurrent boundary law

- **ID:** ULF-ECMPL-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Bilateral exponentially weighted convolution algebras form a strict repair scale.
  Every horizontal source intervention shifts a boundary reporter outside its current fibre and is
  bounded only after the next source-weight repair; reflection and phase remain isometric, phase
  observation is periodic, and the projective completion supports every finite horizontal
  intervention. Thus terminating execution at each fibre can coexist with nonterminating legal
  completion history.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[SECOND NON-REWRITING COMPLETION LABORATORY] [LEAN CORE CERTIFIED] [NOT RH]`

## 1. Bilateral source fibres

For `a>=0`, define

\[
 \mathcal A_a
 =\left\{x=(x_k)_{k\in\mathbb Z}:
   \|x\|_a:=\sum_{k\in\mathbb Z}e^{a|k|}|x_k|<\infty\right\}.
 \tag{BER.1}
\]

Use Cauchy formation

\[
 (x*y)_n=\sum_{j\in\mathbb Z}x_jy_{n-j}.
 \tag{BER.2}
\]

For `z in C`, the exponential reporter is

\[
 \chi_z(x)=\sum_{k\in\mathbb Z}x_ke^{zk}.
 \tag{BER.3}
\]

Define reflection, phase, and horizontal intervention by

\[
 (Rx)_k=x_{-k},\qquad
 (U_t x)_k=e^{-itk}x_k,\qquad
 (T_cx)_k=e^{ck}x_k.
 \tag{BER.4}
\]

The source label is the integer clock `k`; none of these operations is fitted from a target zero.

## 2. Banach formation and exact reporter domain

### Theorem 2.1 — bilateral formation algebra

For every `a>=0`, `A_a` is a unital Banach algebra and

\[
 \|x*y\|_a\le\|x\|_a\|y\|_a.
 \tag{BER.5}
\]

### Proof

The weight is submultiplicative:

\[
 e^{a|j+\ell|}\le e^{a|j|}e^{a|\ell|}.
\]

Absolute Tonelli applied to the Cauchy product gives `(BER.5)`. Completeness is weighted `ell^1`
completeness, and the atom at zero is the unit. QED.

### Theorem 2.2 — exact reporter strip

`chi_z` is a continuous character on `A_a` exactly when

\[
 |\operatorname{Re}z|\le a.
 \tag{BER.6}
\]

In that chamber its norm is one.

### Proof

Put `b=Re z`. If `|b|<=a`, then

\[
 |e^{zk}|=e^{bk}\le e^{|b||k|}\le e^{a|k|},
\]

so `|chi_z(x)|<=||x||_a`. Equality of the operator norm follows from the unit atom.

Conversely, for the atom `delta_k`,

\[
 \frac{|\chi_z(\delta_k)|}{\|\delta_k\|_a}=e^{bk-a|k|}.
 \tag{BER.7}
\]

If `b>a`, let `k->+infinity`; if `b<-a`, let `k->-infinity`. The ratio is unbounded. QED.

In multiplicative coordinate `w=e^z`, the continuous character space is the closed annulus

\[
 e^{-a}\le |w|\le e^a.
 \tag{BER.8}
\]

This is a geometric shadow of the repair grade, not an additional choice.

## 3. Operation laws and sharp grade loss

### Theorem 3.1 — reflection and phase are fibrewise isometries

For every real `t`,

\[
 \|Rx\|_a=\|x\|_a,
 \qquad
 \|U_tx\|_a=\|x\|_a.
 \tag{BER.9}
\]

They act on reporters by

\[
 \chi_z(Rx)=\chi_{-z}(x),
 \qquad
 \chi_z(U_tx)=\chi_{z-it}(x).
 \tag{BER.10}
\]

### Proof

Reflection preserves `|k|`; phase multiplication has modulus one. Reindexing or direct
substitution gives `(BER.10)`. QED.

### Theorem 3.2 — horizontal intervention consumes exact repair grade

For all `a>=0` and `c in R`,

\[
 T_c:\mathcal A_{a+|c|}\longrightarrow\mathcal A_a
 \tag{BER.11}
\]

is bounded with norm one, and

\[
 \chi_z(T_cx)=\chi_{z+c}(x).
 \tag{BER.12}
\]

If `c ne 0`, `T_c` is unbounded as an endomorphism of every fixed `A_a`. The loss `|c|` in
`(BER.11)` is sharp.

### Proof

Since `ck<=|c||k|`,

\[
 e^{a|k|}|e^{ck}x_k|
 \le e^{(a+|c|)|k|}|x_k|.
\]

The zero atom proves norm one. Equation `(BER.12)` is termwise multiplication. For `c>0`, the
endomorphism norm on positive atoms has ratio `e^{ck}->infinity`; for `c<0`, use negative atoms.
The same rays prove that no smaller uniform grade loss works. QED.

This is the first decisive law: functional reflection and recurrent phase are legal within one
fibre, but a nonneutral horizontal source intervention is necessarily a morphism between fibres.

## 4. Endogenous critical-completion chain

Fix `c>0` and set

\[
 a_n=nc,
 \qquad
 \mathcal A^{(n)}=\mathcal A_{a_n}.
 \tag{BER.13}
\]

At stage `n`, the positive boundary reporter `chi_(a_n)` is continuous. Its execution after the
marked intervention is

\[
 \chi_{a_n}(T_cx)=\chi_{a_{n+1}}(x).
 \tag{BER.14}
\]

The right side is not continuous on `A^(n)` by Theorem 2.2, but is continuous on `A^(n+1)`.

### Theorem 4.1 — failure generates the next least repair

For every `n>=0`:

1. `chi_(a_n)` is admitted on `A^(n)`;
2. executing `T_c` produces the nonadmitted reporter `chi_(a_(n+1))`;
3. `A^(n+1)` admits that reporter;
4. `T_c:A^(n+1)->A^(n)` has norm one;
5. the inclusion `A^(n+1) subset A^(n)` is strict.

### Proof

The first four clauses are Theorems 2.2 and 3.2. For strictness, the bilateral sequence

\[
 x_k={e^{-(n+1/2)c|k|}\over(1+|k|)^2}
 \tag{BER.15}
\]

lies in `A^(n)` because its weighted absolute series has the exponentially decaying factor
`e^{-c|k|/2}`. It does not lie in `A^(n+1)` because its weighted terms grow like
`e^{c|k|/2}/(1+|k|)^2` and do not even tend to zero. QED.

No challenge list was appended. The marked horizontal operation transports the admitted boundary
reporter to the first reporter excluded by the current fibre; that failure uniquely identifies the
next exponential weight in this scale.

### Theorem 4.2 — self-catalytic repair is generated by the current reporter

For `a>0`, let `r_a(k)=e^(ak)` be the positive boundary-reporter coefficient and let `S_a=T_a` be
multiplication by that same coefficient. Then

\[
 r_a^2=r_{2a},\qquad
 \chi_a(S_ax)=\chi_{2a}(x),\qquad
 S_a:\mathcal A_{2a}\longrightarrow\mathcal A_a
 \text{ has norm }1.
 \tag{BER.15a}
\]

The generated reporter `chi_(2a)` is not continuous on `A_a` but is continuous on `A_(2a)`.
Starting from any `a_0>0`, define `a_(n+1)=2a_n`. Then `a_n=2^n a_0`, and at every stage the
newly admitted boundary reporter is also the coefficient of the next legal intervention:

\[
 r_{a_n}^2=r_{a_{n+1}},\qquad
 \chi_{a_n}(S_{a_n}x)=\chi_{a_{n+1}}(x).
 \tag{BER.15b}
\]

### Proof

The coefficient identity is `e^(a k)e^(a k)=e^(2ak)`. The reporter exchange and norm-one repair
map are Theorem 3.2 with `c=a`. Theorem 2.2 gives noncontinuity before repair and continuity after
repair. Induction gives `a_n=2^n a_0`. QED.

This closes the fixed-promoter objection to Theorem 4.1. The challenge at stage `n+1` is not read
from a prewritten external ladder: the output admitted at stage `n` is itself the multiplier whose
execution generates the next excluded reporter.

## 5. Stable projective receiver and open completion history

Define

\[
 \mathcal A_\infty=\bigcap_{a\ge0}\mathcal A_a
 \tag{BER.16}
\]

with its projective locally convex topology.

### Theorem 5.1 — stable global execution

`A_infinity` is a complete locally convex convolution algebra. Reflection, every phase `U_t`, and
every horizontal intervention `T_c` act continuously on it. Every exponential reporter `chi_z` is
continuous.

### Proof

Completeness follows because `A_infinity` is the projective limit of the Banach fibres. Formation
and reflection are continuous in every seminorm by `(BER.5)` and `(BER.9)`. For fixed output grade
`a`, `(BER.11)` bounds `T_c` by the input seminorm at `a+|c|`. Phase is isometric. For `chi_z`,
choose any grade `a>=|Re z|` and apply Theorem 2.2. QED.

The finite stages never stabilize: every one has a next nonadmitted boundary reporter. The
projective receiver stabilizes execution only by retaining the complete open repair history.

## 6. Closed phase projection and open lifted lineage

Because the clock is integral,

\[
 U_{t+2\pi}=U_t.
 \tag{BER.17}
\]

Thus every phase observation is periodic and recurrent inside every fixed fibre. In contrast, the
minimal horizontal repair grade needed after `n` repeated positive interventions is `nc`, which
diverges.

### Corollary 6.1 — exact recurrence/lineage separation

The same source has:

1. closed periodic phase observation at every finite stage;
2. a strictly open, unbounded horizontal repair lineage;
3. exact functional reflection on every stage;
4. stable joint execution only in the projective receiver.

This is an exact non-RH realization of “closed observer projection with open lifted history.” It
does not claim that every recurrent system has such a lift.

## 7. Fourth-organ prediction

The repair theorem predicts a prolongation boundary not used in its construction. Multiplication
by the clock `k` is unbounded on every fixed boundary character but is continuous with arbitrarily
small positive collar loss, because polynomial growth is dominated by `e^{epsilon|k|}`. Therefore
all finite clock jets act continuously on `A_infinity`, while no finite fibre carries the complete
horizontal jet calculus without loss.

Consequently:

\[
 \boxed{
 \text{unbounded prolongation depth belongs to repair history, not to one completed fibre}.}
 \tag{BER.18}
\]

This does not identify hypertranscendence with noncompactness. It supplies a legal common receiver
for infinite prolongation while the phase orbit remains periodic.

## 8. Hostile significance audit

### Conjecture A — one exponential Banach completion carries the field

**False.** Theorem 3.2 makes every nonzero horizontal intervention unbounded on every fixed fibre.

**Survivor:** operation-indexed scale morphisms and the projective receiver.

### Conjecture B — adding a boundary reporter completes the source once

**False.** The marked intervention sends it to the next excluded reporter by `(BER.14)`.

**Survivor:** failure-generated strict repair chain. The stronger self-catalytic law `(BER.15a)`--
`(BER.15b)` rules out the objection that this is merely a fixed externally supplied promoter list.

### Conjecture C — recurrence closes the underlying law history

**False.** Phase is periodic while repair grade diverges.

**Survivor:** exact recurrence/lineage separation.

### Conjecture D — this weighted algebra is new mathematics

**False.** Weighted group/Beurling algebras, Köthe and power-series spaces, Banach scales, and
projective limits are established machinery. Recent adjacent work includes arXiv:2508.05569 on
weighted convolution/differential subalgebras and arXiv:2507.00897 on convolution operators on
power-series spaces.

**Survivor:** the exact endogenous-completion interpretation and its role as a second
non-rewriting laboratory for source-generated critical completion.

### Conjecture E — the theorem selects the RH centre

**False.** `A_infinity` admits every horizontal reporter. The theorem constructs legal lineage; it
does not force a physical source into a neutral-only domain.

**Survivor:** source-to-physical landing must be a morphism of repair scales or projective
receivers. A single common Banach/Hilbert fibre is now the wrong type.

## 9. Cross-laboratory fusion

The word-completion laboratory and this analytic laboratory share one causal law:

\[
 \boxed{
 \text{current failure}
 \to\text{least conservative repair}
 \to\text{changed executable overlap}
 \to\text{next failure}.}
 \tag{BER.19}
\]

| law | word completion | bilateral exponential completion |
|---|---|---|
| current failure | critical peak | shifted reporter not continuous |
| repair | orient joining rule | strengthen exponential weight |
| conserved layer | equational congruence | old reporters and convolution laws |
| changed execution | new rewrite overlap | next horizontal reporter |
| open resource | rule/overlap depth | exponential repair grade |
| stationary observer | quotient theory | periodic phase orbit |

The mechanisms are not isomorphic, yet the causal formation law is exact in both. This closes the
second non-rewriting gate of source-generated critical completion.

## 10. Lean target

The unconditional finite core to formalize is:

1. bilateral exponential basis weight and reporter ratio;
2. exact in-strip bound;
3. off-strip positive/negative ray escape;
4. sharp tilt grade inequality and reporter exchange;
5. concrete unit-step repair chain;
6. self-catalytic dyadic repair generated by the current boundary reporter;
7. phase periodicity and reflection weight invariance.

Full Banach completion and projective-limit topology remain paper-proved until reusable bilateral
weighted-`ell^1` infrastructure is built.

## 11. Promotion gate

- [x] Banach algebra and exact character strip;
- [x] reflection/phase isometry;
- [x] sharp horizontal grade loss;
- [x] strict failure-generated repair chain;
- [x] projective stable receiver;
- [x] periodic phase/open-lineage separation;
- [x] word/analytic cross-laboratory mechanism table;
- [x] Lean core scratch-certified and umbrella-wired;
- [ ] third nonisomorphic source laboratory;
- [ ] literal arithmetic repair-scale landing;
- [ ] RH consequence.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BilateralExponentialConvolutionAlgebra`, `GaloisForLFunctions.HTGeometry.BilateralExponentialRepairScale`, `GaloisForLFunctions.HTGeometry.ConstitutiveBilateralExponentialRepair`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.BilateralExponentialConvolutionAlgebra` (97 constants), `GaloisForLFunctions.HTGeometry.BilateralExponentialRepairScale` (106 constants), with the finite core `GaloisForLFunctions.HTGeometry.ConstitutiveBilateralExponentialRepair` (30 constants); axiom audit clean. Namespace `BilateralRepair`; `𝒜_a` is `Fibre a` (`[Fact (0 ≤ a)]`), sequences via `Fibre.seq`.

| Claim | Lean declaration |
|-|-|
| (BER.1)–(BER.4) weight, fibre, Cauchy formation, reporter, reflection, phase, intervention | `expWeight`, `Admissible`, `wnorm`, `Fibre`, `conv`, `reporter`, `reporterCoeff`, `reflectSeq`, `phaseSeq`, `tiltSeq` |
| Thm 2.1 submultiplicative weight, (BER.5) | `expWeight_add_le`, `Admissible.conv`, `wnorm_conv_le` |
| Thm 2.1 commutative unital Banach algebra (Cauchy product commutative/associative, unit `δ₀`, completeness via `ℓ¹` isometry) | `conv_comm`, `conv_assoc`, `conv_unitSeq`, `Fibre.instCommRing`, `Fibre.instNormedCommRing`, `Fibre.instNormedAlgebraComplex`, `Fibre.norm_one_eq`, `Fibre.isometryEquivLp`, `Fibre.instCompleteSpace` |
| Thm 2.2 `χ_z` continuous character exactly on `|Re z| ≤ a`, norm one | `reporter_conv`, `Fibre.reporterHom`, `Fibre.reporterCLM`, `Fibre.norm_reporterCLM`, `Fibre.exists_reporter_clm_iff` |
| (BER.7) atom ratio `e^{bk-a|k|}` | `Fibre.reporter_atom_ratio` |
| (BER.8) character space = annulus `e^{-a} ≤ |w| ≤ e^a` (every character is a strip reporter) | `Fibre.abs_re_le_iff_annulus`, `Fibre.exists_reporter_of_algHom`, `Fibre.hasSum_atoms` |
| Thm 3.1 (BER.9)–(BER.10) reflection and phase isometries; reporter action | `Fibre.reflect`, `Fibre.phase`, `wnorm_reflectSeq`, `wnorm_phaseSeq`, `reporter_reflectSeq`, `reporter_phaseSeq` |
| Thm 3.2 (BER.11)–(BER.12) `T_c : 𝒜_{a+|c|} → 𝒜_a` norm one, `χ_z(T_c x) = χ_{z+c}(x)` | `Fibre.tilt`, `Fibre.norm_tilt`, `wnorm_tiltSeq_le`, `reporter_tiltSeq`, `Fibre.reporter_tilt` |
| Thm 3.2 unbounded on every fixed fibre; loss `|c|` sharp | `tiltSeq_unbounded`, `tiltSeq_loss_sharp` |
| Thm 4.1 (BER.13)–(BER.15) failure-generated strict repair chain | `repairChain`, `repairChain_strict`, `separatingSeq`, `admissible_separatingSeq`, `not_admissible_separatingSeq`, `Fibre.inclusion`, `Fibre.inclusion_injective` |
| Thm 4.2 (BER.15a)–(BER.15b) self-catalytic dyadic repair | `selfCatalytic`, `dyadicRepair` |
| Thm 5.1 (BER.16) `𝒜_∞ = ⋂ 𝒜_a` complete, locally convex, continuous formation; `R`, `U_t`, `T_c` continuous; every `χ_z` continuous | `receiverSubalgebra`, `Receiver`, `Receiver.range_seq`, `Receiver.isClosed_receiver`, `Receiver.instCompleteSpace`, `Receiver.locallyConvexSpace`, `Receiver.continuous_mul`, `Receiver.reflect`, `Receiver.phase`, `Receiver.tilt`, `Receiver.reporterHom`, `Receiver.continuous_reporterHom` |
| (BER.17) phase periodicity; Cor 6.1 repair grade `nc` exact and divergent | `phaseSeq_add_two_pi`, `Fibre.phase_add_two_pi`, `Receiver.phase_add_two_pi`, `tiltSeq_iterate`, `iterate_repair_grade`, `tendsto_repair_grade` |
| §7 (BER.18) clock multiplication: small collar loss, unbounded on fixed fibres, all finite jets continuous on `𝒜_∞` | `admissible_clockSeq`, `wnorm_clockSeq_le`, `clockSeq_unbounded`, `Receiver.clock`, `Receiver.seq_clock_pow` |
| §8 audit: fixed Banach fibre fails (A); `𝒜_∞` admits every reporter (E) | `tiltSeq_unbounded`, `Receiver.reporterHom` |
| §10 finite core | `stageWeight`, `boundaryReporter`, `nextReporter_not_uniformly_bounded`, `dyadicReporter_self_generates_next` |

## Log

- 2026-08-14 — theorem derived after character-domain collapse failed to produce its own physical
  landing. Weighted-algebra novelty rejected; endogenous analytic repair genealogy retained.
- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
