# Super-Gaussian DA Coefficient Floor

- **ID:** supergaussian-da-coefficient-floor
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / CANDIDATE LAW
- **Scientific status:** `[CONJECTURE] [NOVELTY OPEN] [SIGNIFICANCE PASSES IF TRUE]`
- **Statement:** A nonpolynomial differentially algebraic entire function cannot have Taylor coefficients that decay faster than every Gaussian.

## Goal

Find the first coefficient-scale law for arbitrary complex DA entire functions that distinguishes finite algebraic-differential constraint from unrestricted entire interpolation. The law is posed independently of zeta or RH. Its downstream value is that it would close the only non-arithmetic escape in the entire-complex-time heat obstruction.

## Gates

- [x] `0 -> 1`: exact statement, equivalent growth formulation, algebraic-coefficient case, all-linear-order case, low-nonlinear-differential-order case, and sharp adjacent examples identified.
- [ ] `1 -> 2`: prove the arbitrary-order theorem unconditionally or produce a counterexample and retire the claim.
- [ ] Novelty gate: inspect the complete Lipshitz-Rubel gap theorem and the older Valiron/Strelitz slow-growth literature for an exact arbitrary-order parent.
- [ ] `2 -> 3`: formalize the whole unconditional theorem in Lean with no axioms, `sorry`, or hidden analytic imports.

## Conjecture `[OPEN CORE]`

Let

`f(z)=sum_(n>=0) a_n z^n`

be entire and differentially algebraic over `C(z)`. Suppose that for every `A>0` there is `C_A>0` such that

`|a_n| <= C_A exp(-A n^2)`                                                     `(SG)`

for every `n>=0`. Then `f` is a polynomial.

Equivalently, no transcendental DA entire function has

`log M_f(r)=o((log r)^2)`.                                                      `(QL0)`

The equivalence is unconditional. `(SG) => (QL0)` follows by completing the square in

`M_f(r) <= C_A sum_n exp(-A n^2+n log r)`.

Conversely, under `(QL0)`, Cauchy's estimate at `r=exp(cn)` gives

`log |a_n| <= log M_f(exp(cn))-cn^2 = -cn^2+o(n^2)`;

choosing `c>A` and absorbing finitely many indices gives `(SG)`.

### Intrinsic divisor form `[PROVED EQUIVALENT]`

Condition `(QL0)` is equivalent, after removing a monomial and a nonzero constant, to being a genus-zero canonical product whose zero-counting function satisfies

`n_f(r)=o(log r)`.

Thus the conjecture is equivalently:

> `[CONJECTURE — logarithmic divisor-density floor]` Every transcendental DA entire function of ordinary order zero has `limsup n_f(r)/log r>0`.

For the attack, denote

`delta_log(f)=limsup_(r->infinity) n_f(r)/log r`

and call it the logarithmic divisor density. No novelty is claimed for this elementary density. The candidate law is the nontrivial statement that the DA stratum has a hard floor `delta_log(f)>0`, whereas the unrestricted entire stratum contains canonical products with `delta_log(f)=0`.

The complete Jensen-Hadamard equivalence is proved in `2-fully-proven/not_new_scientific_knowledge/quadratic-subtype-canonical-divisor-equivalence.md`.

## Proved strata

### Algebraic Taylor coefficients `[PROVED] [BRIDGE]`

If every `a_n` is algebraic, Popken's lower bound gives constants `alpha,beta>0` such that every coefficient is either zero or

`|a_n| >= alpha n^(-beta n log n)`.

This is incompatible with `(SG)` unless only finitely many coefficients are nonzero. The complete proof is recorded in `2-fully-proven/not_new_scientific_knowledge/arithmetic-entire-heat-da-finite-spectrum.md`.

### Differential order at most two `[PROVED] [BRIDGE]`

If a transcendental entire function satisfies an ADE of differential order at most two over `C(z)`, the Valiron-Zimogljad-Strelitz theorem gives positive ordinary order. Condition `(QL0)` gives ordinary order zero. Hence `(SG)` forces polynomiality for every DA function of minimal differential order at most two, without any arithmetic hypothesis.

The complete heat consequence is recorded in `2-fully-proven/not_new_scientific_knowledge/entire-heat-multiplicative-da-order-three-floor.md`.

### D-finite functions of arbitrary linear order `[PROVED] [BRIDGE]`

If `(a_n)` is P-recursive and one tail coefficient is nonzero, solving its finite-width polynomial recurrence forward forces an infinite subsequence with

`|a_(n_k)| >= exp(-O(n_k log n_k))`.

This contradicts `(SG)`. Hence every D-finite series satisfying `(SG)` is a polynomial, with no restriction on its linear differential order or coefficient field. The complete proof is recorded in `2-fully-proven/not_new_scientific_knowledge/entire-heat-holonomic-finite-spectrum.md`.

### Wide Newton plateaux and monomial jets `[PROVED] [BRIDGE]`

Condition `(SG)` forces active maximum-term indices with logarithmic-radius plateau widths tending to infinity. At the midpoint of those plateaux, every fixed finite jet of `f` is exponentially close, uniformly on the circle, to the jet of the single central Taylor monomial.

Consequently, the top-degree/minimal-weight face of every autonomous ADE for `f` has zero rational-normal-curve principal symbol. The complete proof is recorded in `2-fully-proven/not_new_scientific_knowledge/supergaussian-wide-newton-plateau-monomialization.md`.

### Finite secant detection `[PROVED] [BRIDGE]`

For differential order `m`, sums of at most `ceil((m+1)/2)` monomial jets are already Zariski dense in the complete order-`m` jet space. Hence every nonzero ADE face has a finite secant detection rank bounded by `ceil((m+1)/2)`.

The direct confluent-Vandermonde proof is recorded in `2-fully-proven/not_new_scientific_knowledge/finite-jet-secant-detection-rank.md`.

### Fixed-modulus Newton blindness `[PROVED] [BRIDGE]`

Every admissible infinite Taylor-modulus profile has an HT phase realization. In particular, `exp(z)` and an HT entire function can have coefficient moduli `1/n!` term by term, hence identical maximum-term functions, logarithmic Newton envelopes, active indices, transition radii, plateau widths, order, and type.

The proof combines algebraically independent phases with Ostrowski's finite-basis theorem and is recorded in `2-fully-proven/not_new_scientific_knowledge/fixed-taylor-modulus-newton-geometry-ht-blindness.md`. Thus Newton geometry can organize an ADE attack but can never replace the exact complex coefficient identities of the assumed ADE.

### Log-superlacunary full-support magnitudes `[PROVED HERE] [NOVELTY AUDIT]`

Suppose the coefficients are eventually nonzero, put `b_n=-log|a_n|`, and assume

`b_(n+1)/b_n -> infinity`.

Then the series is HT over `C(z)` for every possible choice of coefficient phases. Mahler's integer normalization turns a hypothetical ADE into integral coefficient identities. Each such identity must have two grouped convolution atoms whose logarithmic magnitudes differ by only `O(log N)`, while the log-superlacunary condition makes the minimizing atom unique with an `omega(log N)` gap.

The complete unconditional paper proof is recorded in `2-fully-proven/needs-audit/log-superlacunary-taylor-magnitude-hypertranscendence.md`. It remains under scientific-novelty audit and is not Lean-formalized. This closes a phase-uniform, arbitrary-complex, full-support stratum of `(SG)` without coefficient arithmetic.

### Transcendental Taylor log-ratio `[PROVED HERE] [NOVELTY AUDIT]`

Let `rho>1` be transcendental. If the coefficients are eventually nonzero, `b_n=-log|a_n|` is eventually positive, and

`b_(n+1)/b_n -> rho`,

then the series is HT over `C(z)` for every coefficient-phase sequence. Arbitrary subleading fluctuations are allowed.

The stronger necessary DA law is arithmetic: if a DA full-support series has a finite log-ratio limit `rho>1`, then `rho` must be algebraic. Moreover some nonzero integer Laurent polynomial `Q` with `Q(1)=Q(rho)=0` has shift defect

`|sum_r d_r b_(n_k+r)|=O(log n_k)`

along an infinite subsequence. This is obtained by pigeonholing the bounded pair of convolution atoms that an integer ADE must keep at its Archimedean bend.

The complete unconditional paper proof is recorded in `2-fully-proven/needs-audit/da-taylor-log-ratio-algebraicity-resonance-law.md`. It remains under scientific-novelty audit and is not Lean-formalized. This closes every transcendental finite-ratio phase fiber in `(SG)` and supplies a necessary characteristic of the remaining algebraic-ratio DA candidates.

### Hierarchically resonance-broken geometric magnitudes `[PROVED HERE] [NOVELTY AUDIT]`

The actual general law is this. Let `h_n=o(lambda^n)` for some `lambda>1`. Suppose that every nonzero bounded integer relation

`sum_r d_r lambda^r=0`

is broken at the lower scale by

`|sum_r d_r h_(n+r)|/log n -> infinity`.

Then every eventually full-support profile

`-log|a_n|=A lambda^n+h_n`

forces HT over `C(z)` for every phase sequence. If `lambda` is transcendental, there are no leading Laurent relations and the condition is vacuous. For every `lambda>1`, including rational and algebraic ratios, the choice

`h_n=B exp(n^alpha)`, `B>0`, `0<alpha<1`,

satisfies the condition.

This closes the first genuinely resonant stratum. Distinct bounded convolution patterns may satisfy an exact Laurent-polynomial relation at the leading `lambda^n` scale. When they do, their difference at the stretched-exponential lower scale has asymptotic size

`exp(n^alpha)n^(-j(1-alpha))`,

at the first nonzero moment `j`. This is still `omega(log n)` and therefore too large for an ADE bend. The perturbation is negligible relative to `lambda^n`, and the adjacent logarithmic ratio still tends to `lambda`.

The complete unconditional paper proof is recorded in `2-fully-proven/needs-audit/hierarchical-resonance-breaking-taylor-magnitude-hypertranscendence.md`. It remains under scientific-novelty audit and is not Lean-formalized.

### Stretched-exponential ratio-one magnitudes `[PROVED HERE] [NOVELTY AUDIT]`

For `B>0` and `0<alpha<1`, every eventually full-support profile

`-log|a_n|=B exp(n^alpha)`

forces HT over `C(z)` for every phase sequence. Here the adjacent logarithmic ratio tends to `1`, so neither the log-superlacunary theorem nor the log-ratio algebraicity law applies.

Two new ingredients close this stratum. First, eventual strict convexity makes the least active top-degree source-sum shift win; within it, any unbounded imbalance costs more than a fixed surviving balanced pattern. Second, every nonzero fixed integer difference has first nonvanishing moment asymptotic

`C exp(n^alpha)n^(-j(1-alpha))=omega(log n)`.

Thus both atoms at a hypothetical ADE bend are confined to fixed offsets, where finite-difference separation contradicts the mandatory `O(log N)` gap. The complete unconditional paper proof is recorded in `2-fully-proven/needs-audit/stretched-exponential-taylor-log-magnitude-hypertranscendence.md`. It remains under scientific-novelty audit and is not Lean-formalized.

### Polynomial log-magnitudes impose an ADE degree floor `[PROVED HERE] [NOVELTY AUDIT]`

For the unresolved polynomial profiles

`-log|a_n|=B n^beta`, `beta>1`,

the anti-bend method does not prove arbitrary-order HT: sufficiently high finite differences can fall to logarithmic size or below. It does prove the exact complexity bound

`deg_Z^ADE(f) >= ceil(beta)`

for every DA realization and every phase sequence.

If an integer ADE had total `Y`-degree `D<beta`, convexity would confine both atoms at its bend to fixed-offset, degree-`D` patterns in the least active source-sum shift. Newton's identities force two distinct `D`-element patterns to differ in some power moment `j<=D`; their valuation gap is then

`C n^(beta-j)(1+o(1)) >= C n^(beta-D)=omega(log n)`,

a contradiction. The complete unconditional paper proof is recorded in `2-fully-proven/needs-audit/polynomial-taylor-log-magnitude-ade-degree-floor.md`. It is a degree floor, not a full HT theorem, and its scientific significance remains provisional.

## Constraint attack

Write `v_n=-log|a_n|`, with `v_n=+infinity` when `a_n=0`. Condition `(SG)` says that the finite values of `v_n` escape every quadratic scale. For a fixed ADE

`P(z,f,f',...,f^(m))=0`,

coefficient extraction produces finitely many convolution patterns with polynomial weights in the indices. On the lower convex envelope of `(n,v_n)`, a coefficient of total index `N` is governed tropically by the least sum of finitely many `v_j` subject to a fixed additive constraint.

Mahler's normalization first removes a false obstruction: even if the original ADE has arbitrary complex constants, a DA formal series satisfies some ADE with rational-integral coefficients. Thus recurrence weights cannot be Liouville-small. After grouping identical coefficient monomials, each nonzero weight is an integer of at least unit modulus.

The resulting proved necessary law is:

> `[PROVED — Archimedean tropical bend law]` At every sufficiently large nonvacuous coefficient index of an integer-normalized ADE, two distinct grouped convolution atoms have logarithmic magnitudes within `O_P(log N)`.

The log-superlacunary theorem contradicts this law by additive isolation. The exact target that would close the whole conjecture is now:

> `[CONJECTURE — persistent-bend obstruction]` An integer differential recurrence cannot sustain logarithmic-width convolution bends at every sufficiently large coefficient index for an eventually full-support sequence with `b_n/n^2->infinity`.

This is stronger than a support-gap theorem: all coefficients may be nonzero. It must prove that near-equal convolution valuations cannot persist, rather than merely locate a unique monomial. The unresolved range is now more precise. Comparable adjacent `b_n` are not enough to sustain bends, leading-scale algebraic resonance is not enough, an asymptotically negligible stretched-exponential layer can destroy every finite leading relation, and even a pure ratio-one stretched-exponential profile is excluded by convex confinement. A counterexample or proof must therefore address profiles whose bounded convolution relations remain exact or logarithmically close through arbitrarily high finite-difference depth.

### Jet-face reformulation

At Wiman-Valiron maximum points, a central Taylor monomial `c z^nu` has jet

`(Y_0,...,Y_m)=(c z^nu, c nu z^(nu-1),...,c (nu)_m z^(nu-m))`.

After the harmless falling-factorial normalization, its leading jet lies on the rational normal curve

`Y_j = X T^j  (0<=j<=m)`.

The kernel of the symbol map

`C[Y_0,...,Y_m] -> C[X,T],   Y_j |-> X T^j`

is the toric ideal of this curve, generated by its quadratic Hankel minors. `[PROVED] [SEARCH]` The classical one-dominant-term theorem and its same-weight refinement say, in this language, that the leading Wiman face of any ADE for a transcendental order-zero entire function must lie in this monomial-jet ideal. The direct wide-plateau proof for `(SG)` is recorded above; it is parent-theory material rather than new science.

The stronger live target is:

> `[CONJECTURE — finite jet-osculation]` Under `(SG)`, the widening Newton plateaux force every successive normal symbol of the ADE to vanish along the monomial-jet curve. Equivalently, the dominant face lies in every power of the monomial-jet ideal. Krull separation would then make that face zero, contradicting minimality of the ADE.

The exact open lemma is not first-order Wiman approximation. It is the iteration step: after the leading face vanishes on all monomial jets, show that the first nonzero normal linearization cannot be cancelled by the exponentially smaller neighboring Taylor blocks. This is the point at which Valiron's critical quadratic-type construction can survive but quadratic type zero is expected to fail.

### Finite secant ceiling `[PROVED ALGEBRAIC HALF]`

A cluster of `k` near-maximal Taylor monomials has a jet on the `k`-secant variety of the rational normal curve. For an ADE of differential order `m`, clusters of only

`k_m=ceil((m+1)/2)`

arbitrary monomials already have Zariski-dense jets in `C^(m+1)`. Thus no nonzero order-`m` face can be invisible to all such clusters. The direct confluent-Vandermonde proof is recorded in `2-fully-proven/not_new_scientific_knowledge/finite-jet-secant-detection-rank.md`.

The remaining split is now sharper, but it is not a density-versus-recurrence dichotomy:

1. `[OPEN CORE]` Show that the actual exponent/amplitude transition clusters of a super-Gaussian series satisfying an ADE are Zariski dense at the finite detection rank. Then the dominant ADE face is zero.
2. `[OPEN CORE]` If those clusters are trapped in a proper algebraic transition locus, use the full coefficient hierarchy of the assumed ADE—not the trapping geometry alone—to show that its successive lower faces force finite support or a contradiction.

The tempting shortcut "proper algebraic transition locus implies P-recursive coefficients" is false. The card `5-failed/algebraic-newton-trapping-implies-recurrence.md` constructs a super-Gaussian HT entire series with adjacent equal-amplitude transitions in one fixed proper algebraic locus but algebraically independent coefficients. The algebraic secant ceiling is complete; the open content is now an ADE-specific compatibility law between its dominant transition ideal and all lower Newton faces.

## Counterexample pressure

1. **Valiron's order-zero third-order solution does not kill the claim.** Its theta-product construction lies at the quadratic logarithmic scale; it shows why differential order three is the first live stratum, not that quadratic type zero is attainable.
2. **Ordinary order is too coarse.** Order zero includes both the Valiron quadratic scale and the strictly smaller `(QL0)` class.
3. **Lipshitz-Rubel gaps are adjacent but not sufficient.** Their theorem constrains lacunary support. `(SG)` permits full support and asks about coefficient magnitude.
4. **Arbitrary complex equation constants are not the obstruction.** Mahler's normalization supplies an ADE with rational-integral coefficients, so grouped recurrence weights are integers and cannot be Liouville-small. The genuine arbitrary-phase obstruction is that two or more distinct coefficient monomials may have nearly equal magnitudes and cancel. The proved bend law isolates the exact scale: any DA recurrence must supply such a tie within `O(log N)` at every large nonvacuous index.
5. **Linear recurrences cannot yield a counterexample.** Finite-width polynomial recurrence propagation forces a factorial-scale nonzero subsequence. Any counterexample must be genuinely nonlinear DA, not merely D-finite of high order.
6. **Closure operations checked so far do not yield a counterexample.** Affine rescaling, differentiation, integration, algebraic operations, and polynomial composition preserve the quadratic logarithmic scale of the known theta-type order-zero DA examples rather than lowering it to type zero.
7. **Divisor sparsity alone is not the whole invariant at the critical scale.** Bank records Wittich's HT geometric divisor `(lambda^n)` and Valiron's DA inversion-symmetrized divisor `(lambda^n+lambda^(-n))`. Both have logarithmic zero density of constant scale. The open zero-density floor concerns the strictly sparser regime `n(r)=o(log r)`; any proof must still account for algebraic symmetry of the divisor rather than counting alone.
8. **First-face degeneration is not enough.** The arbitrary-order Wiman-Valiron theorem already permits cancellations among maximal-degree terms of the same differential weight. The new content must control the first nonzero normal derivative after that cancellation; merely restating the dominant-face theorem is rediscovery.
9. **Algebraic transition trapping alone does not force recurrence or DA.** For algebraically independent `t_n in [1,2]`, the coefficients `a_n=t_n exp(-n^3)` have strictly convex logarithmic Newton data, adjacent equal-amplitude transitions, and widening plateaux, yet the resulting entire function is HT by Ostrowski's finite-basis obstruction. Any rigidity argument must use the assumed ADE's complete coefficient identities and lower faces; transition geometry by itself has no access to amplitude transcendence.
10. **Even the complete coefficient-modulus profile is not a universal DA/HT classifier.** The profile `|a_n|=1/n!` supports both `exp(z)` and an HT phase twist. This does not refute the restricted super-Gaussian conjecture; it shows that its missing lower-face law must use an ADE-specific phase-sensitive consequence rather than Newton geometry alone.

## Exact downstream consequence if proved

For a jointly entire one-sided periodic heat orbit

`u(t,z)=sum_n a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`,

entire backward time implies `(SG)` for `h(w)=sum_n a_nw^n`. The conjecture would therefore give the unconditional dichotomy

`h is a polynomial  OR  h is HT over C(w)`.

This would rule out every implementation of an entire-complex-time lattice heat route whose proposed transition is a DA/HT change of the multiplicative anchor, regardless of coefficient arithmetic or ADE order. It would not rule out the actual de Bruijn-Newman route, its continuous kernel, or any method using data not factored through this DA/HT bit.

## Literature boundary

1. G. Valiron, *Sur les fonctions entieres d'ordre nul et les equations differentielles*, Bull. Soc. Math. France 53 (1925), 34-42: third-order order-zero DA example and second-order slow-growth obstruction under additional hypotheses.
2. Sh. Strelitz, *Three Theorems on the Growth of Entire Transcendental Solutions of Algebraic Differential Equations*, Canad. J. Math. 35 (1983), 1110-1128: the order-two positive-order wall and Valiron example.
3. L. Lipshitz and L. A. Rubel, *A Gap Theorem for Power Series Solutions of Algebraic Differential Equations*, Amer. J. Math. 108 (1986), 1193-1213: support-gap obstruction, not yet verified as a magnitude theorem.
4. C. Krattenthaler and T. Rivoal, *Arithmetic properties of the Taylor coefficients of differentially algebraic power series*, arXiv:2502.09259: Maillet upper bounds and Popken lower bounds in the algebraic-coefficient stratum.
5. C. Garay-Lopez, J. Luviano-Flores, and C. Valencia-Negrete, *Elementary solutions of ordinary tropical differential equations, and vanishing orders of solutions of algebraic differential equations*, arXiv:2606.21829: a finite tropical framework for supports and local `t`-adic orders of ADE solutions. Its valuation is non-Archimedean and local; it does not control the Archimedean magnitudes `-log|a_n|` of successive Taylor coefficients. It is therefore methodological parent material, not the target theorem.
6. S. B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic Differential Equations*, Funkcial. Ekvac. 23 (1980), 335-349: proves HT for specific finite Gamma-ray configurations and an odd/even law for canonical products with zeros `(n^p)`. Its introduction records Wittich's HT geometric divisor `(lambda^n)` and Valiron's DA inversion-symmetrized divisor `(lambda^n+lambda^(-n))`. The paper does not prove an arbitrary `n(r)=o(log r)` divisor theorem.
7. W. Bergweiler, P. J. Rippon, and G. M. Stallard, *Dynamics of meromorphic functions with direct or logarithmic singularities*, Theorem 13.1: the arbitrary-order Wiman-Valiron dominant-face theorem groups maximal-degree differential monomials by differential weight and forces positive order when no same-weight coefficient sum cancels. This source-settles the first rational-normal-curve face obstruction but not finite osculation after cancellation.
8. The dimension formula `dim Sec_k(C_m)=min(2k-1,m)` for the rational normal curve is classical. It source-settles the finite secant ceiling but does not imply that the Newton clusters of one fixed entire function realize a dense subset of that secant variety.

Valiron's 1925 paper and Strelitz's 1983 synthesis have now been inspected in full for the relevant claims: the known third-order DA example has geometric zero scale and positive quadratic logarithmic type, while every second-order transcendental entire ADE solution has positive ordinary order. Bank's 1980 paper has also been inspected in full and does not contain the arbitrary sparse-divisor floor. No arbitrary-order theorem or counterexample at quadratic logarithmic type zero has yet been verified. Scientific novelty remains explicitly open until the full Lipshitz--Rubel gap theorem and any remaining higher-order slow-growth parents are inspected.

## Log

- 2026-07-11 — Opened the arbitrary-order coefficient-floor problem after proving its algebraic-coefficient and differential-order-at-most-two strata.
- 2026-07-11 — Closed the D-finite stratum in every linear differential order by direct P-recursive tail propagation; the open class is now genuinely nonlinear, order at least three, and non-arithmetic.
- 2026-07-11 — Recast the conjecture exactly as a logarithmic divisor-density floor using a complete Jensen-Hadamard reduction; Bank's canonical-product results show that divisor symmetry, not sparsity alone, is the next obstruction.
- 2026-07-11 — Proved arbitrarily wide Newton plateaux and uniform finite-jet monomialization. The resulting principal-face degeneracy was source-settled by the classical arbitrary-order Wiman-Valiron theorem; the open core is the next normal/osculation layer.
- 2026-07-11 — Proved the sharp finite secant detection ceiling `ceil((m+1)/2)`. The algebraic half is classical; the open content is whether ADE-constrained super-Gaussian clusters realize dense jets or satisfy a stronger lower-face compatibility obstruction.
- 2026-07-11 — Falsified the shortcut from algebraically trapped transition clusters to P-recursive coefficients. The live trapped-cluster branch now requires a new ADE-specific lower-face compatibility law.
- 2026-07-11 — Strengthened the counterexample to an HT series and proved general fixed-modulus Newton blindness: exact Taylor magnitudes can be held fixed while DA/HT status changes through phases alone.
- 2026-07-11 — Completed the relevant Valiron, Strelitz, and Bank primary-source audit. Their exact theorems stop at the order-two wall, the critical geometric-density example, and special Gamma-ray/polynomial-zero configurations; none closes the arbitrary `n(r)=o(log r)` case.
- 2026-07-11 — Proved the phase-uniform log-superlacunary full-support stratum and the Archimedean tropical bend law. Mahler normalization eliminates Liouville-small equation weights; the open core is persistent near-ties between distinct coefficient convolutions in the non-superincreasing super-Gaussian range.
- 2026-07-11 — Proved a second phase-uniform full-support stratum with `-log|a_n|=A rho^n` for transcendental `rho>1`. Constant adjacent ratios do not rescue DA; the remaining escape requires persistent bounded additive relations or near-relations in the logarithmic magnitudes.
- 2026-07-11 — Closed the first algebraically resonant phase-uniform stratum: `b_n=A lambda^n+B exp(sqrt n)` is HT-forcing for every `lambda>1`. The smaller scale breaks every bounded relation left by the leading geometric scale.
- 2026-07-11 — Extracted the intrinsic Archimedean shift-defect law: an exponentially balanced profile with every nonzero fixed integer shift defect `omega(log n)` forces HT for every phase. For algebraic leading ratio, all resonances compress to the canonical residue `m_lambda(S)b`.
- 2026-07-11 — Entered the ratio-one regime: proved that `b_n=B exp(n^alpha)`, `0<alpha<1`, forces HT for every phase by least-shift selection, convex bounded confinement, and fixed-difference separation.
- 2026-07-11 — At the polynomial boundary, proved the quantitative residue that survives: `b_n=B n^beta` forces every integer ADE to have total dependent-variable degree at least `ceil(beta)`; full HT remains open once the ADE degree reaches the moment-cancellation depth.
