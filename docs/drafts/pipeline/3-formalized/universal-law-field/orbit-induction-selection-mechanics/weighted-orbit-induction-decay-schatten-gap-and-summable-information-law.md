# Weighted orbit induction: decay, Schatten, gap, and summable-information law

- **ID:** ULF-OISM-2
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ULF-OISM-1
- **Statement:** For transported copies of one local operator weighted by a source amplitude
  sequence, operator norm is controlled by \(\ell^\infty\), compactness exactly by \(c_0\),
  Schatten class exactly by \(\ell^p\), and closed range exactly by a uniform nonzero amplitude
  gap.  Independent packet information is finite exactly when the local divergences are summable.
  Thus global selection holds in the nonsummable regime and fails sharply in the decaying regime.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [WEIGHTED ORBIT FORMATION] [EXACT DECAY THRESHOLDS]
  [GLOBAL SELECTION BOUNDARY] [LEAN-PENDING] [NOT RH]

## 1. Setup

Let \(I\) be countably infinite, let \(H,K\) be nonzero Hilbert spaces, let
\(D:H\to K\) be bounded and nonzero, and let \(U_i,V_i\) be unitaries on \(H,K\).  For a bounded
scalar family \(a=(a_i)_{i\in I}\), define

\[
 \operatorname{Ind}_a(D)
 =\bigoplus_{i\in I}a_iV_iDU_i^{-1}.
\tag{WOI.1}
\]

Write

\[
 \|a\|_\infty=\sup_i|a_i|,
 \qquad
 \alpha_*(a)=\inf_{i:a_i\ne0}|a_i|.
\tag{WOI.2}
\]

The convention is that closed-range statements concern the orthogonal complement of the full
kernel, including all zero-amplitude blocks.

## 2. Exact norm and reduced gap

### Theorem 2.1

One has

\[
 \boxed{
 \|\operatorname{Ind}_a(D)\|=\|a\|_\infty\|D\|.}
\tag{WOI.3}
\]

If at least one \(a_i\ne0\), then

\[
 \boxed{
 \gamma(\operatorname{Ind}_a(D))
 =\alpha_*(a)\gamma(D).}
\tag{WOI.4}
\]

Consequently \(\operatorname{ran}\operatorname{Ind}_a(D)\) is closed exactly when

\[
 \boxed{
 \operatorname{ran}D\text{ is closed}
 \quad\text{and}\quad
 \alpha_*(a)>0.}
\tag{WOI.5}
\]

#### Proof

For \(x=(x_i)\),

\[
 \|\operatorname{Ind}_a(D)x\|^2
 =\sum_i|a_i|^2\|DU_i^{-1}x_i\|^2
 \le\|a\|_\infty^2\|D\|^2\|x\|^2.
\]

Vectors supported in one coordinate, with that coordinate approximating the norm of \(D\), prove
the reverse inequality after taking the supremum over \(i\).  On the orthogonal complement of the
kernel, every nonzero coordinate lies in \(U_i(\ker D)^\perp\).  The sharp blockwise lower bound is
\(|a_i|\gamma(D)\), so the infimum over nonzero blocks gives `(WOI.4)`.  Hilbert closed range is
equivalent to positive reduced minimum modulus, proving `(WOI.5)`. QED.

### Corollary 2.2 -- homogeneous Fredholm threshold

Assume every \(a_i\ne0\).  Then:

1. \(\operatorname{Ind}_a(D)\) is upper semi-Fredholm exactly when \(D\) is bounded below and
   \(\alpha_*(a)>0\);
2. it is lower semi-Fredholm exactly when \(D\) is surjective and \(\alpha_*(a)>0\);
3. it is Fredholm exactly when \(D\) is invertible and \(\alpha_*(a)>0\).

If \(\ker D\ne0\) or \(\ker D^*\ne0\), the corresponding local defect is repeated infinitely.
The remaining condition is closed range, supplied by `(WOI.5)`.

## 3. Exact compactness and essential norm

Assume now that \(D\) is compact and nonzero.

### Theorem 3.1 -- \(c_0\) is the compactness boundary

\[
 \boxed{
 \operatorname{Ind}_a(D)\text{ is compact}
 \quad\Longleftrightarrow\quad
 a\in c_0(I).}
\tag{WOI.6}
\]

More sharply,

\[
 \boxed{
 \|\operatorname{Ind}_a(D)\|_{\mathrm{ess}}
 =\bigl(\limsup_{i\to\infty}|a_i|\bigr)\|D\|,}
\tag{WOI.7}
\]

where the limsup means the infimum, over finite \(F\subset I\), of
\(\sup_{i\notin F}|a_i|\).

#### Proof

If \(a\in c_0\), truncate `(WOI.1)` to a finite set \(F\).  Each finite truncation is compact and

\[
 \|\operatorname{Ind}_a(D)-\operatorname{Ind}_{a1_F}(D)\|
 =\sup_{i\notin F}|a_i|\|D\|\longrightarrow0.
\]

Hence the full operator is compact.

For the lower essential-norm bound, choose a subnet or sequence of distinct indices with
\(|a_i|\to\limsup|a_i|\), and use the orthonormal block vectors from ULF-OISM-1 with a unit vector
\(x\) satisfying \(\|Dx\|\) arbitrarily close to \(\|D\|\).  Every compact perturbation sends
those block vectors to zero, giving the lower bound in `(WOI.7)`.  Finite block truncation gives the
matching upper bound.  Equation `(WOI.6)` follows. QED.

Thus homogeneous orbit induction is the special case \(a_i=1\), where the full local norm survives
in the Calkin algebra.  Decay to zero is not a technical improvement; it changes the global ideal
class.

## 4. Schatten threshold

Let \(1\le p<\infty\), and assume \(D\in\mathcal S_p(H,K)\) is nonzero.

### Theorem 4.1 -- \(\ell^p\) is the Schatten boundary

\[
 \boxed{
 \operatorname{Ind}_a(D)\in\mathcal S_p
 \quad\Longleftrightarrow\quad
 a\in\ell^p(I).}
\tag{WOI.8}
\]

In that case

\[
 \boxed{
 \|\operatorname{Ind}_a(D)\|_{\mathcal S_p}^p
 =\left(\sum_i|a_i|^p\right)\|D\|_{\mathcal S_p}^p.}
\tag{WOI.9}
\]

#### Proof

The singular values of a block diagonal operator are the multiset union of the singular values of
its blocks.  Unitary transport does not change them, and multiplying a block by \(a_i\) multiplies
all its singular values by \(|a_i|\).  Therefore

\[
 \sum_{i,n}s_n(a_iV_iDU_i^{-1})^p
 =\sum_i|a_i|^p\sum_ns_n(D)^p,
\]

which is finite exactly under `(WOI.8)` and gives `(WOI.9)`. QED.

For \(p=1\), trace-class global admission is therefore exactly an \(\ell^1\) source-amplitude
budget.  Local trace class alone says nothing cofinally.

## 5. Weighted positive Gram

Let \(\mathcal D_a=\operatorname{Ind}_a(D)\).  Then

\[
 \boxed{
 \mathcal D_a^*\mathcal D_a
 =\bigoplus_i|a_i|^2U_i(D^*D)U_i^{-1}.}
\tag{WOI.10}
\]

Thus positive formation squares the amplitude sequence.  In particular:

1. Gram compactness is equivalent to \((|a_i|^2)\in c_0\), the same as \(a\in c_0\);
2. Gram trace class is equivalent to \(a\in\ell^2\) when \(D\) is Hilbert--Schmidt;
3. output phases and \(V_i\) disappear, while all decay thresholds remain.

This is a precise phase/decay separation: positivity forgets phase but not cofinal amplitude.

## 6. Independent packet information

Let \((P_i,Q_i)\) be probability pairs on standard Borel spaces.  For finite \(F\subset I\), put

\[
 P_F=\bigotimes_{i\in F}P_i,
 \qquad
 Q_F=\bigotimes_{i\in F}Q_i,
 \qquad
 j_i=J(P_i,Q_i).
\tag{WOI.11}
\]

Use one common recovery kernel on each pair, possibly depending on \(i\) but not on whether the
input law is \(P_i\) or \(Q_i\).

### Theorem 6.1 -- summability is the information boundary

For every finite \(F\), common recovery preserves exact work and

\[
 \boxed{J(\widetilde P_F,\widetilde Q_F)=\sum_{i\in F}j_i.}
\tag{WOI.12}
\]

Consequently, for any increasing exhaustion \(F_n\uparrow I\),

\[
 \boxed{
 \sup_nJ(\widetilde P_{F_n},\widetilde Q_{F_n})<\infty
 \quad\Longleftrightarrow\quad
 \sum_{i\in I}j_i<\infty.}
\tag{WOI.13}
\]

#### Proof

Finite-product additivity holds for each directed relative entropy.  The common-kernel chain rule
preserves each directed term.  Add the two directions to obtain `(WOI.12)`.  Since \(j_i\ge0\),
monotone convergence of finite partial sums gives `(WOI.13)`. QED.

Homogeneous information induction has \(j_i=j\), so bounded work forces \(j=0\).  Weighted or
inhomogeneous induction can retain nonzero local information at finite total work exactly when the
local divergences are summable.

## 7. Global selection phase diagram

The operator and information thresholds give four distinct regimes.

| source amplitudes / information | global operator | global information | selection consequence |
|---|---|---|---|
| \(a\notin c_0\), \(\sum j_i=\infty\) | essential | infinite | strongest zero-defect pressure |
| \(a\in c_0\setminus\ell^p\), \(\sum j_i=\infty\) | compact, not \(S_p\) | infinite | ideal repaired, work still selects |
| \(a\in\ell^p\), \(\sum j_i<\infty\) | Schatten | finite | nonzero defect can remain admitted |
| \(\alpha_*(a)>0\) | possible closed range | homogeneous gap | Fredholm selection if local block invertible |

No one scalar “smallness” captures this phase diagram.  Ideal class, reduced gap, and information
budget are independent axes generated by the same weighted orbit.

## 8. Functional-equation neutrality

If an involution \(\sigma:I\to I\) satisfies \(|a_{\sigma(i)}|=|a_i|\), transports blocks by unitary
duality, and exchanges \((P_i,Q_i)\) by measurable bijections, then it preserves:

1. \(\|a\|_\infty\), \(\alpha_*(a)\), \(c_0\), and every \(\ell^p\) norm;
2. operator norm, essential norm, Schatten norm, and reduced gap;
3. every \(j_i\) and their total sum.

Thus functional equation remains information-neutral and threshold-neutral.  It cannot decide
which side of the phase diagram the source occupies.

## 9. Sharp no-gos

1. **Infinite orbit always forces neutrality. -- False.** Any nonzero compact \(D\) with
   \(a\in c_0\) has compact global induction.
2. **Compact global defect forces neutrality. -- False in the weighted regime.** It forces
   \(a_i\|D\|\to0\), not \(D=0\).
3. **Trace-class local blocks give trace-class formation. -- False.** Global trace class requires
   \(a\in\ell^1\).
4. **Amplitude decay gives closed range. -- False.** If infinitely many nonzero amplitudes tend to
   zero, `(WOI.4)` gives reduced minimum modulus zero and nonclosed range whenever \(D\) has a
   nonzero closed-range part.
5. **Finite total information means equal local packets. -- False.** It means only
   \(\sum_i j_i<\infty\).
6. **Positive Gram repairs decay. -- False.** It squares amplitudes and retains the same \(c_0\)
   compactness wall.

## 10. New source gate

For a literal arithmetic orbit, the decisive quantities are now explicit:

\[
 \boxed{
 \limsup_i|a_i|,
 \quad
 \inf_{i:a_i\ne0}|a_i|,
 \quad
 \sum_i|a_i|^p,
 \quad
 \sum_iJ(P_i,Q_i).}
\tag{WOI.14}
\]

The next source theorem must compute or sharply bound these four quantities for one neutral-only
defect.  Another local compactness, positivity, or functional-equation theorem cannot settle any
of them.

## 11. Uniform recovery--regularization uncertainty

Weighted completion suggests a false escape: choose decaying amplitudes to make every problematic
orbit summable, then recover the original coefficient data afterward.  Uniform recovery forbids
this.

### Theorem 11.1 -- cofinal recovery lower bound

Let (X_n,Y_n) be normed spaces, let (T_n:X_n\to Y_n) and (L_n:Y_n\to X_n) be bounded linear
maps with

\[
 L_nT_n=1_{X_n}.
\tag{WOI.15}
\]

Then for every (x_n\in X_n),

\[
 \boxed{
 \|T_nx_n\|\ge {\|x_n\|\over\|L_n\|}.}
\tag{WOI.16}
\]

Consequently:

1. if (sup_n\|L_n\|<\infty) and (\|x_n\|\to\infty), then
   (\|T_nx_n\|\to\infty);
2. if (\|x_n\|\to\infty) while (sup_n\|T_nx_n\|<\infty), then
   (\|L_n\|\to\infty);
3. no uniformly recoverable formation can regularize a divergent source history into one bounded
   target history.

#### Proof

Equation `(WOI.15)` gives

\[
 \|x_n\|=\|L_nT_nx_n\|\le\|L_n\|\,\|T_nx_n\|,
\]

which is `(WOI.16)`.  The three consequences follow immediately. QED.

### Corollary 11.2 -- diagonal completion dichotomy

For the diagonal formation (A_a(x_i)=(a_ix_i)) with every (a_i\ne0), the coordinatewise inverse
is bounded exactly when

\[
 \inf_i|a_i|>0.
\tag{WOI.17}
\]

Therefore every amplitude sequence that regularizes a nonsummable source vector by tending to zero
destroys bounded common recovery.  In the language of Sections 2--4:

\[
 \boxed{
 \text{compact/Schatten regularization of an infinite homogeneous orbit}
 \quad\Longrightarrowquad
 \text{no bounded coefficient-faithful decoder}.}
\tag{WOI.18}
\]

This is the exact completion uncertainty needed by the field programme.  Regularization and
recovery are not two independent design choices; their product has the lower bound `(WOI.16)`.

## 12. Lean boundary

The paper proof uses only block Hilbert operators, compact approximation, singular-value
additivity, and finite-product relative entropy.  Formalization should be split into:

1. weighted block norm and reduced minimum modulus;
2. compactness/essential norm via finite truncations and weakly-null block vectors;
3. Schatten sum identity;
4. finite-product KL/Jeffreys additivity and monotone partial sums.

The read-only API audit found reusable local infrastructure:

- `HTGeometry/HilbertClosedRange.lean` for closed-range/lower-bound equivalences;
- `HTGeometry/HilbertSchmidt.lean` and `HTGeometry/HilbertSchmidtOperator.lean` for compact and
  Hilbert--Schmidt operators;
- `HTGeometry/RectangularTraceNorm.lean` for rectangular approximation numbers and Schatten
  membership;
- `HTGeometry/SchattenOneBanach.lean` for the trace-class carrier;
- `HTGeometry/ConstitutiveFunctionalEquationPacketLift.lean` for common-kernel KL isometry.

No ready-made countable Hilbert block-operator plus essential-norm wrapper was found.  That missing
infrastructure should be built once and reused by both ULF-OISM cards.  No Lean files are changed
during the active read-only formal audit.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.WeightedOrbitInduction`, `GaloisForLFunctions.HTGeometry.WeightedOrbitInductionGap`, `GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten`, `GaloisForLFunctions.HTGeometry.WeightedOrbitPacketInformation`, `GaloisForLFunctions.HTGeometry.WeightedOrbitSelectionLaw`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.WeightedOrbitInduction` (61), `GaloisForLFunctions.HTGeometry.WeightedOrbitInductionGap` (45),
`GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten` (19), `GaloisForLFunctions.HTGeometry.WeightedOrbitPacketInformation` (22),
`GaloisForLFunctions.HTGeometry.WeightedOrbitSelectionLaw` (43); axiom audit clean. Orbit induction is built on
`RHTower.rectangularBlockOperator` (`HTGeometry.OrbitInductionEssentialization`).

| Claim | Lean declaration |
|-|-|
| (WOI.1)–(WOI.2) `Ind_a(D)`, `‖a‖_∞`, `α_*(a)` | `weightedInduction`, `ampSup`, `ampGap` |
| Theorem 2.1 (WOI.3) `‖Ind_a D‖ = ‖a‖_∞ ‖D‖` | `norm_weightedInduction` |
| (WOI.4) `γ(Ind_a D) = α_*(a) γ(D)` | `reducedMinModulus`, `reducedMinModulus_weightedInduction` |
| (WOI.5) closed range iff `ran D` closed and `α_* > 0` | `isClosed_range_weightedInduction_iff_ampGap` (also `isClosed_range_weightedInduction_iff`) |
| Corollary 2.2 semi-Fredholm / Fredholm thresholds; infinite repetition of local defects | `isUpperSemiFredholm_weightedInduction_iff`, `isLowerSemiFredholm_weightedInduction_iff`, `isBoundedFredholm_weightedInduction_iff`, `not_finiteDimensional_ker_weightedInduction`, `finiteDimensional_range_orthogonal_weightedInduction_iff` |
| Theorem 3.1 (WOI.6) compact iff `a ∈ c₀` | `isCompactOperator_weightedInduction_iff`, `isCompactOperator_weightedInduction_iff_tendsto`, `tailSup_eq_zero_iff`, `tailSup_eq_zero_iff_tendsto` |
| (WOI.7) essential norm `= limsup ∣aᵢ∣ · ‖D‖` | `rectEssentialNorm_weightedInduction` |
| Theorem 4.1 (WOI.8) `S_p` iff `a ∈ ℓ^p` (every `p > 0`) | `memRectSchattenClass_weightedInduction_iff`, `memRectSchattenClass_weightedInduction_iff_memℓp`, `memRectSchattenClass_one_weightedInduction_iff` |
| (WOI.9) Schatten energy identity; trace norm for `p = 1` | `tsum_rpow_rectApproxNumber_weightedInduction`, `rectTraceNorm_weightedInduction` |
| §5 (WOI.10) weighted positive Gram; phases disappear | `adjoint_weightedInduction`, `gram_weightedInduction`, `gram_weightedInduction_eq_of_norm_eq` |
| §5 items 1–2: Gram compact iff `c₀`; Gram trace class iff `ℓ²` (HS `D`) | `isCompactOperator_gram_weightedInduction_iff`, `memRectSchattenClass_one_gram_weightedInduction_iff` |
| Theorem 6.1 (WOI.12) additivity after common recovery | `independentPacket`, `klDiv_independentPacket`, `formationJeffreys_independentPacket_recovery`, `formationJeffreys_independentPacket_recovery_eq` |
| (WOI.13) bounded along exhaustion iff summable | `iSup_formationJeffreys_exhaustion`, `formationJeffreys_exhaustion_bounded_iff`, `exists_bound_formationJeffreys_exhaustion_iff` |
| homogeneous information: bounded work forces `j = 0` | `tsum_const_formationJeffreys_ne_top_iff` |
| §7 phase diagram (four regimes, all realized) | `phaseDiagram_essential`, `phaseDiagram_compact_not_schatten`, `phaseDiagram_schatten`, `phaseDiagram_gap`, `amplitude_regimes` |
| §8 functional-equation neutrality | `amplitude_neutrality`, `operator_neutrality`, `information_neutrality` |
| §9 no-gos 1–6 | `noGo_infiniteOrbit_compact`, `exists_compact_weightedInduction_nonzero_block`, `noGo_compact_forces_decay`, `noGo_traceClass_homogeneous`, `noGo_decay_not_closed`, `exists_finite_information_unequal_packets`, `isCompactOperator_gram_weightedInduction_iff` |
| §10 (WOI.14) source gate | `weightedOrbit_sourceGate` |
| Theorem 11.1 (WOI.15)–(WOI.16) and consequences 1–3 | `norm_le_norm_leftInverse_mul`, `div_norm_leftInverse_le`, `tendsto_norm_formation_of_bounded_recovery`, `tendsto_norm_recovery_of_bounded_formation`, `not_bounded_recovery_and_regularization` |
| Corollary 11.2 (WOI.17) diagonal left inverse iff `inf ∣aᵢ∣ > 0` | `diagonalFormation`, `exists_leftInverse_diagonalFormation_iff`, `not_exists_leftInverse_diagonalFormation_of_tendsto` |
| (WOI.18) compact/Schatten regularization ⇒ no bounded decoder | `not_exists_leftInverse_of_isCompactOperator`, `not_exists_decoder_weightedInduction` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
