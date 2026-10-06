# Reciprocal-fusion work classification, weighted compactness, and exact factorization law

- **ID:** ULF-RFTM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [NOVELTY UNVERIFIED]`
  `[WORK FORCED BY FUSION] [EXACT RECOVERY FACTORIZATION] [SHARP COMPACTNESS THRESHOLD]`
  `[ADAPTIVE ESCAPE CLASSIFIED] [NOT RH] [LEAN-PROVED]`

## 1. Mathematical delta

Reversal does not choose a work, and strict work on every finite coordinate does not give global
properness. This theorem closes both gaps in one mechanism.

First, a normalized direct/reflected fusion identity uniquely forces the scalar reciprocal work

\[
 \omega(t)=e^t+e^{-t}-2=2(\cosh t-1)=4\sinh^2(t/2).
\tag{RFT.1}
\]

Second, source complexity weights decide whether the resulting countable work is globally proper.
For weights `a_j >= 1`, every work sublevel is compact in `ell^1` exactly when
`sum_j a_j^(-2)` converges. The same work is realized as the squared complexity-weighted separation
of the two legs of an exact recovery factorization; reciprocal positive Grams reconstruct every
radial coordinate, while functional reversal exchanges them.

This is an unconditional formation-topology theorem. It contains no RH parameter or target route.

## 2. Local fusion law

Define `(RFT.1)` for real `t`.

### Theorem 2.1 — fusion identity and rigidity

The function `omega` satisfies

\[
 \boxed{
 \omega(x+y)+\omega(x-y)
 =\omega(x)\omega(y)+2\omega(x)+2\omega(y).}
\tag{RFT.2}
\]

Conversely, let `F:R->R` be twice continuously differentiable and assume

\[
 F(0)=0,
\tag{RFT.3}
\]

\[
 F(x+y)+F(x-y)=F(x)F(y)+2F(x)+2F(y)
 \quad(x,y\in\mathbb R),
\tag{RFT.4}
\]

\[
 F''(0)=2.
\tag{RFT.5}
\]

Then

\[
 \boxed{F=\omega.}
\tag{RFT.6}
\]

Thus normalized reciprocal work is forced by direct/reflected composition; it is not an arbitrary
even gauge.

### Proof

The hyperbolic addition formulas give

\[
 \cosh(x+y)+\cosh(x-y)=2\cosh x\cosh y.
\]

Substituting `omega=2(cosh-1)` and expanding proves `(RFT.2)`.

For uniqueness put

\[
 f=1+\frac12F.
\]

Equations `(RFT.3)--(RFT.4)` become d'Alembert's equation

\[
 f(x+y)+f(x-y)=2f(x)f(y),
 \qquad f(0)=1.
\tag{RFT.7}
\]

Putting `x=0` shows `f(-y)=f(y)`, hence `f'(0)=0`. Differentiate `(RFT.7)` twice with respect to
`y` and set `y=0`. Since `f''(0)=F''(0)/2=1`,

\[
 2f''(x)=2f(x)f''(0)=2f(x).
\]

Therefore `f''=f`, with `f(0)=1` and `f'(0)=0`. The unique solution is `f=cosh`: explicitly, for
`g=f-cosh`, one has `g''=g`, `g(0)=g'(0)=0`; the functions `g'-g` and `g'+g` solve first-order
homogeneous equations with zero initial value, so both vanish. Hence `F=2(cosh-1)=omega`. QED.

## 3. Complexity-weighted formation space

Let `a=(a_j)_(j>=0)` be real weights satisfying

\[
 a_j\ge1.
\tag{RFT.8}
\]

For a real sequence `x=(x_j)`, define the extended work

\[
 \mathcal W_a(x)=\sum_{j\ge0}a_j^2\omega(x_j)\in[0,+\infty].
\tag{RFT.9}
\]

Let

\[
 \mathcal X_a=\{x:\mathcal W_a(x)<\infty\}.
\tag{RFT.10}
\]

For `x,y in X_a`, define the fusion interaction

\[
 \mathcal I_a(x,y)
 =\sum_j a_j^2\omega(x_j)\omega(y_j).
\tag{RFT.11}
\]

### Theorem 3.1 — global fusion and group closure

The space `X_a` is an abelian group under coordinatewise addition and reversal `x -> -x`. Moreover

\[
 \boxed{
 \mathcal W_a(x+y)+\mathcal W_a(x-y)
 =\mathcal I_a(x,y)+2\mathcal W_a(x)+2\mathcal W_a(y).}
\tag{RFT.12}
\]

Every term in `(RFT.12)` is finite.

### Proof

All summands are nonnegative. Since `a_j>=1`,

\[
 \omega(y_j)\le \mathcal W_a(y)
\]

for every `j`. Consequently

\[
 \mathcal I_a(x,y)
 \le \mathcal W_a(y)\mathcal W_a(x)<\infty.
\tag{RFT.13}
\]

Apply `(RFT.2)` coordinatewise, multiply by `a_j^2`, and sum. The right side is finite by
`(RFT.13)`, so both nonnegative works on the left are finite and equality `(RFT.12)` holds by
monotone convergence of the partial sums. Evenness of `omega` gives `-x in X_a`; zero is admitted;
closure under addition was just proved. QED.

## 4. Exact recovery realization

Let `H=ell^2(N_0;C)`. Every `x in X_a` lies in `ell^2`: the elementary inequality

\[
 \boxed{\omega(t)\ge t^2}
\tag{RFT.14}
\]

follows from `cosh t>=1+t^2/2`, and `(RFT.8)--(RFT.9)` then give

\[
 \sum_j|x_j|^2\le\sum_j a_j^2x_j^2\le\mathcal W_a(x).
\tag{RFT.15}
\]

In particular `x` is bounded. Define the positive diagonal operator

\[
 S_xe_j=e^{x_j/2}e_j.
\tag{RFT.16}
\]

It is bounded and invertible. Put

\[
 Q_x=S_x,
 \qquad B_x=S_x^{-1}=S_{-x}.
\tag{RFT.17}
\]

Let `A_a` be the source-complexity diagonal `A_ae_j=a_je_j` on its natural domain.

### Theorem 4.1 — reciprocal exact factorization

For every `x in X_a`:

\[
 \boxed{B_xQ_x=Q_xB_x=I,}
\tag{RFT.18}
\]

\[
 \boxed{Q_x^*Q_x=\operatorname{diag}(e^{x_j}),
 \qquad B_xB_x^*=\operatorname{diag}(e^{-x_j}),}
\tag{RFT.19}
\]

and the two positive Grams multiply to the identity. Reversal `x -> -x` swaps them. Furthermore,
the diagonal operator `A_a(Q_x-B_x)` is Hilbert--Schmidt and

\[
 \boxed{
 \|A_a(Q_x-B_x)\|_{\rm HS}^2
 =\mathcal W_a(x).}
\tag{RFT.20}
\]

Formation composition is exact:

\[
 \boxed{S_{x+y}=S_xS_y.}
\tag{RFT.21}
\]

Thus `(RFT.12)` is the work law of direct and reflected exact recovery composition.

### Proof

All operators are diagonal. Equations `(RFT.18)`, `(RFT.19)`, and `(RFT.21)` follow coordinatewise.
The diagonal of `A_a(Q_x-B_x)` is

\[
 a_j(e^{x_j/2}-e^{-x_j/2}).
\]

Its squared modulus is

\[
 a_j^2(e^{x_j}+e^{-x_j}-2)=a_j^2\omega(x_j).
\]

The sequence of these diagonal coefficients lies in `ell^2` by `(RFT.9)`. In particular it is
bounded, so `Q_x-B_x` maps `H` into the natural domain of `A_a`, and their composition is the
bounded diagonal Hilbert--Schmidt operator with those coefficients. Summation proves both the
Hilbert--Schmidt assertion and `(RFT.20)`. QED.

## 5. Sharp global properness threshold

For `C>=0`, put

\[
 K_C(a)=\{x\in\ell^1(\mathbb N_0;\mathbb R):\mathcal W_a(x)\le C\}.
\tag{RFT.22}
\]

### Theorem 5.1 — compactness iff reciprocal-square complexity is summable

The following are equivalent:

1. for every `C>=0`, the sublevel `K_C(a)` is compact in `ell^1`;
2. for some `C>0`, the sublevel `K_C(a)` is bounded in `ell^1`;
3. the reciprocal complexity is square-summable:

   \[
   \boxed{\sum_{j\ge0}a_j^{-2}<\infty.}
   \tag{RFT.23}
   \]

When `(RFT.23)` holds, every finite-work sequence belongs to `ell^1`, and

\[
 \boxed{
 \sum_{j\ge N}|x_j|
 \le \mathcal W_a(x)^{1/2}
 \left(\sum_{j\ge N}a_j^{-2}\right)^{1/2}.}
\tag{RFT.24}
\]

Hence work excludes adaptive coordinate escape. For the canonical depth weights `a_j=j+1`, all
sublevels are compact.

### Proof: sufficiency

Assume `(RFT.23)`. By `(RFT.14)` and Cauchy--Schwarz,

\[
\begin{aligned}
 \sum_{j\ge N}|x_j|
 &=\sum_{j\ge N}a_j|x_j|a_j^{-1}\\
 &\le
 \left(\sum_{j\ge N}a_j^2x_j^2\right)^{1/2}
 \left(\sum_{j\ge N}a_j^{-2}\right)^{1/2}\\
 &\le \mathcal W_a(x)^{1/2}
 \left(\sum_{j\ge N}a_j^{-2}\right)^{1/2}.
\end{aligned}
\]

This proves `(RFT.24)`, membership in `ell^1`, uniform boundedness of every `K_C(a)`, and uniform
vanishing of its tails. Each finite coordinate head is bounded because
`a_j^2x_j^2<=W_a(x)<=C`. A diagonal subsequence argument on successive finite heads, combined with
the uniform tail bound, gives an `ell^1`-convergent subsequence from every sequence in `K_C(a)`.

If `x^(n)->x` in `ell^1`, then every coordinate converges. Fatou's lemma for the nonnegative
summands gives

\[
 \mathcal W_a(x)\le\liminf_n\mathcal W_a(x^{(n)}).
\]

Thus `K_C(a)` is closed. It is therefore compact.

### Proof: necessity

Suppose instead that

\[
 S_N=\sum_{j=0}^{N}a_j^{-2}\longrightarrow\infty.
\]

Fix an arbitrary `C>0`. Choose `0<delta<=1` such that `M delta^2<=C`, where
`M=cosh(1)` is the constant in `(RFT.27)` below. For sufficiently large `N`, define the
finite-support sequence

\[
 x_j^{(N)}=
 \begin{cases}
 \delta a_j^{-2}S_N^{-1/2},&j\le N,\\
 0,&j>N.
 \end{cases}
\tag{RFT.25}
\]

Then

\[
 \sum_ja_j^2|x_j^{(N)}|^2=\delta^2,
 \qquad
 \|x^{(N)}\|_1=\delta S_N^{1/2}\longrightarrow\infty.
\tag{RFT.26}
\]

Because `a_j>=1` and `S_N>=1`, every coordinate of `x^(N)` lies in `[-1,1]`. On that compact
interval there is a finite constant `M` with

\[
 \omega(t)\le Mt^2.
\tag{RFT.27}
\]

For completeness, `(RFT.27)` follows from the mean-value estimate
`|sinh u|<=cosh(1)|u|` for `|u|<=1` and
`omega(t)=2 integral_0^t sinh(u)du`; one may take `M=cosh(1)`. Therefore

\[
 \mathcal W_a(x^{(N)})le
 M\sum_ja_j^2|x_j^{(N)}|^2=M\delta^2\le C.
\]

Thus every positive work sublevel is unbounded in `ell^1` when `(RFT.23)` fails. In particular
item 2 fails, and item 1 fails. This proves necessity and all equivalences. Since
`sum_(j>=0)(j+1)^(-2)<infinity`, the depth-weight corollary follows. QED.

## 6. Scale selection and determinant boundary

### Theorem 6.1 — bounded amplified work selects zero

For every `d>1` and `x in X_a`,

\[
 \boxed{
 \sup_{n\ge0}\mathcal W_a(d^nx)<\infty
 \quad\Longleftrightarrow\quad x=0.}
\tag{RFT.28}
\]

If `(RFT.23)` holds, then `S_x-I` and `S_x^{-1}-I` are trace class and

\[
 \boxed{
 \det_{\rm Fr}(S_x)=
 \exp\left(\frac12\sum_jx_j\right).}
\tag{RFT.29}
\]

Nevertheless determinant neutrality does not imply factorization neutrality: for
`x=(t,-t,0,...)`, `t!=0`, one has `det_Fr(S_x)=1` but `W_a(x)>0`.

### Proof

If `x=0`, all works vanish. If `x!=0`, choose `j` with `x_j!=0`. Since
`omega(t)->infinity` as `|t|->infinity`,

\[
 \mathcal W_a(d^nx)\ge a_j^2\omega(d^nx_j)\longrightarrow\infty.
\]

This proves `(RFT.28)`.

Under `(RFT.23)`, Theorem 5.1 gives `x in ell^1`. Since `x` is bounded, the mean-value theorem gives
one constant `C_x` such that

\[
 |e^{\pm x_j/2}-1|\le C_x|x_j|.
\]

Both diagonal differences are therefore trace class. Absolute convergence of `sum x_j` permits
the diagonal Fredholm-product calculation

\[
 \det_{\rm Fr}(S_x)
 =\prod_je^{x_j/2}
 =\exp\left(\frac12\sum_jx_j\right),
\]

which is `(RFT.29)`. The two-coordinate counterexample is immediate. QED.

## 7. Joint reconstruction and conservation ledger

The theorem produces one exact multi-organ ledger:

\[
 \boxed{
 \begin{array}{rcl}
 B_xQ_x=Q_xB_x&=&I,\\
 (Q_x^*Q_x)(B_xB_x^*)&=&I,\\
 x&=&\log(Q_x^*Q_x),\\
 \mathcal W_a(x)&=&\|A_a(Q_x-B_x)\|_{\rm HS}^2,\\
 S_{x+y}&=&S_xS_y,\\
 \rho(x)&=&-x.
 \end{array}}
\tag{RFT.30}
\]

It fuses:

1. exact common recovery;
2. functional-equation reversal;
3. reciprocal positive-Gram reconstruction;
4. source complexity/admission;
5. global topology and bounded-orbit selection;
6. determinant history and its exact insufficiency.

The carrier is completely constant, yet the factorization field has a forced local work and a
sharp global compactness phase.

## 8. Conjecture-to-proof/failure loops

### Loop A — reversal canonically determines work

**[FALSIFIED].** Every even function with zero at the origin is reversal invariant; bounded examples
are nonproper.

**Survivor.** Binary direct/reflected fusion plus second-order normalization forces `omega` by
Theorem 2.1.

### Loop B — the forced local work is new scalar analysis

**[REDISCOVERED].** The rigidity step is d'Alembert's functional equation and its spherical-function
theory is classical.

**Survivor.** The useful delta is not the scalar formula but its exact role as a recovery-leg fusion
law feeding the global topology.

### Loop C — unweighted work is globally proper

**[FALSIFIED].** The translates `t e_n` have constant work and no convergent subsequence.

**Survivor.** Theorem 5.1 gives the sharp weight criterion rather than an ad hoc stronger norm.

### Loop D — positive work on every fixed ray excludes adaptive escape

**[FALSIFIED].** When `sum a_j^(-2)=infinity`, the sequences `(RFT.25)` have uniformly bounded work
and unbounded `ell^1` norm.

**Survivor.** Reciprocal-square complexity summability is exactly the global compactness law.

### Loop E — determinant neutrality selects the recovery factorization

**[FALSIFIED].** Opposite radial coordinates cancel in determinant while adding positive work.

**Survivor.** Reciprocal positive Grams jointly reconstruct the entire radial packet.

### Loop F — the theorem proves RH

**[FALSIFIED].** No arithmetic source is shown to produce the coordinate `x`, its complexity grading,
or bounded physical work.

**Survivor.** A future source comparison has a precise target: land in `X_a`, intertwine reflection,
and prove one uniform work bound. Compactness and selection then require no further route estimate.

## 9. External and internal collision audit

The scalar rigidity is classical d'Alembert/spherical-function theory; a modern general parent is
Elqorachi, *On the integral d'Alembert's and Wilson's functional equations*, arXiv:1603.02064.
Weighted Orlicz and weighted Sobolev sequence-space compact embeddings are established; a current
adjacent source is Vuillermot, *On the compactness of embeddings for a class of weighted
Orlicz--Sobolev sequence spaces*, arXiv:2503.19454. Infinite-dimensional positive-definite operator
symmetric spaces and restricted Hilbert--Schmidt groups are also established.

Internally, ULF-FFM-2 supplies the finite recovery torsor, ULF-FLPM-2 supplies response-frame
properness and adaptive-escape classification, and ULF-FDPM-2 supplies source-depth graph
properness. None states the fusion rigidity `(RFT.2)--(RFT.6)` together with the sharp nonlinear
factorization compactness threshold `(RFT.23)`.

Verdict: `[BRIDGE]`. Parent ingredients are occupied. The exact formation-law coupling is new to the
corpus and gives a real global topology, but no external priority claim is made.

## 10. Exact boundary and next gate

The theorem is diagonal/commutative. Its weights are marked source-complexity data, not derived from
an arbitrary exact recovery torsor. It does not treat noncommuting positive Grams, indefinite
factorizations, continuous spectra, or a literal arithmetic source comparison.

The next gate is not another scalar work. It is a noncommutative direct/reflected fusion law whose
flat restriction is `(RFT.2)`, whose complexity ideal has a sharp compactness criterion, and whose
commutator defect carries information not present in radial Grams.

## 11. Lean target

After hostile paper audit, formalize exactly:

1. fusion identity and `C^2` rigidity;
2. finite-support weighted work and direct/reflected fusion;
3. bounded amplified work iff zero;
4. sharp finite-prefix countermodels when reciprocal-square weights diverge;
5. a sequence-level compactness/tail theorem if existing topology infrastructure supports the exact
   paper statement without weakening it.

No diagonal-operator wrapper counts unless exact recovery, reciprocal Grams, and the weighted-work
identity are all certified.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ReciprocalWorkFusionRigidity`, `GaloisForLFunctions.HTGeometry.ReciprocalWorkWeightedCompactness`, `GaloisForLFunctions.HTGeometry.ReciprocalRecoveryFactorization`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.ReciprocalWorkFusionRigidity` (§2, (RFT.14), (RFT.27)),
`GaloisForLFunctions.HTGeometry.ReciprocalWorkWeightedCompactness` (§3, §5, (RFT.28), Loop C) and
`GaloisForLFunctions.HTGeometry.ReciprocalRecoveryFactorization` (§4, (RFT.29), §7).  New names live
in the namespace ReciprocalFusion under GaloisForLFunctions.HTGeometry (prefix `ReciprocalFusion.`
below).  Weights are `a : ℕ → ℝ` with `1 ≤ a j`; `H = ℓ²(ℕ; ℂ)`; the Fredholm determinant is the
corpus determinant `RHTower.fredholmDetOp` (`det(I + T) = det₂(I + T) e^{tr T}`) in the standard basis
`HilbertSchmidt.lpBasis`; trace class is `RHTower.MemSchattenClass 1`.  Corpus inputs: bounded
diagonals (`LpDiagonal.lpDiag`, `LpDiagonal.memℓp_diag`), Hilbert–Schmidt diagonals
(`HilbertSchmidt.diagOp`, `HilbertSchmidt.hsNormSq_diagOp`), Schatten-one real diagonals
(`realSummableDiagonalOperator`, `realSummableDiagonalOperator_memSchattenClass_one`), the entire
regularized determinant as a limit of finite sections (`tendsto_finiteDet2_entireDet2`,
`finiteDet2_eq_prod`) and the basis formula for traces
(`RHTower.opTrace_eq_tsum_basis_of_memSchattenClass_one`).

| Claim | Lean declaration |
|-|-|
| (RFT.1) `ω(t) = eᵗ + e⁻ᵗ - 2 = 2(cosh t - 1) = 4 sinh²(t/2)`, `ω ≥ 0`, even, `ω = 0` iff `t = 0` | `ReciprocalFusion.reciprocalWork`, `ReciprocalFusion.reciprocalWork_eq_cosh`, `ReciprocalFusion.reciprocalWork_eq_sinh_sq`, `ReciprocalFusion.reciprocalWork_nonneg`, `ReciprocalFusion.reciprocalWork_neg`, `ReciprocalFusion.reciprocalWork_zero`, `ReciprocalFusion.reciprocalWork_eq_zero_iff` |
| Theorem 2.1, (RFT.2) fusion identity | `ReciprocalFusion.reciprocalWork_fusion` |
| Theorem 2.1, (RFT.3)–(RFT.7) a `C²` solution with `F(0) = 0`, `F''(0) = 2` is `ω`; `f'' = f`, `f(0) = 1`, `f'(0) = 0` forces `cosh` | `ReciprocalFusion.eq_reciprocalWork_of_fusion`, `ReciprocalFusion.eq_zero_of_deriv_deriv_eq_self`, `ReciprocalFusion.hasDerivAt_reciprocalWork`, `ReciprocalFusion.hasDerivAt_reciprocalWork_deriv`, `ReciprocalFusion.reciprocalWork_rigidity` |
| (RFT.14) `ω(t) ≥ t²`; (RFT.27) `ω(t) ≤ cosh(1) t²` on `|t| ≤ 1` | `ReciprocalFusion.sq_le_reciprocalWork`, `ReciprocalFusion.reciprocalWork_le_cosh_one_mul_sq`, `ReciprocalFusion.cosh_one_le_two` |
| (RFT.8)–(RFT.11) weights, extended work in `[0, ∞]`, `X_a`, fusion interaction | `ReciprocalFusion.workTerm`, `ReciprocalFusion.extendedWork`, `ReciprocalFusion.work`, `ReciprocalFusion.interaction`, `ReciprocalFusion.interactionTerm`, `ReciprocalFusion.extendedWork_lt_top_iff`, `ReciprocalFusion.extendedWork_eq_ofReal` |
| Theorem 3.1 `X_a` is an additive group closed under reversal | `ReciprocalFusion.admissible`, `ReciprocalFusion.mem_admissible_iff`, `ReciprocalFusion.workTerm_neg` |
| Theorem 3.1, (RFT.12)–(RFT.13) global fusion, all terms finite, `ℐ ≤ 𝒲(x)𝒲(y)` | `ReciprocalFusion.global_fusion`, `ReciprocalFusion.reciprocalWork_le_workTerm`, `ReciprocalFusion.workTerm_le_work` |
| (RFT.15) `∑ x_j² ≤ ∑ a_j² x_j² ≤ 𝒲(x)`, `x` bounded | `ReciprocalFusion.sq_summable_and_le`, `ReciprocalFusion.bounded_of_summable_workTerm` |
| (RFT.16)–(RFT.17) `S_x`, `Q_x = S_x`, `B_x = S_x⁻¹`, the complexity diagonal `A_a` on its natural domain | `ReciprocalFusion.expDiag`, `ReciprocalFusion.recoveryQ`, `ReciprocalFusion.recoveryB`, `ReciprocalFusion.complexityDomain`, `ReciprocalFusion.complexityOp` |
| Theorem 4.1, (RFT.18) `B_xQ_x = Q_xB_x = I` | `ReciprocalFusion.recovery_inverse` |
| Theorem 4.1, (RFT.19) `Q*Q = diag(e^{x_j})`, `BB* = diag(e^{-x_j})`, product `I`, reversal swaps the Grams | `ReciprocalFusion.adjoint_expDiag`, `ReciprocalFusion.recovery_grams` |
| Theorem 4.1, (RFT.20) `Q - B` maps into `dom A_a`; `A_a(Q - B)` Hilbert–Schmidt with `‖·‖²_HS = 𝒲_a(x)` | `ReciprocalFusion.defectWeight`, `ReciprocalFusion.norm_defectWeight_sq`, `ReciprocalFusion.complexity_defect_hilbertSchmidt` |
| Theorem 4.1, (RFT.21) `S_{x+y} = S_xS_y` | `ReciprocalFusion.recoveryQ_add`, `ReciprocalFusion.expDiag_add` |
| Theorem 5.1, (RFT.22)–(RFT.23) all sublevels compact in `ℓ¹` ⇔ one positive sublevel bounded ⇔ `∑ a_j⁻² < ∞` | `ReciprocalFusion.sublevel`, `ReciprocalFusion.compactness_tfae` |
| Theorem 5.1 sufficiency: closedness (Fatou), total boundedness, compactness | `ReciprocalFusion.isClosed_sublevel`, `ReciprocalFusion.totallyBounded_sublevel`, `ReciprocalFusion.isCompact_sublevel` |
| Theorem 5.1, (RFT.24) finite work lies in `ℓ¹` with the uniform tail bound | `ReciprocalFusion.tail_bound`, `ReciprocalFusion.tsum_mul_le_sqrt_mul_sqrt` |
| Theorem 5.1 necessity, (RFT.25)–(RFT.27) bounded-work sequences of unbounded `ℓ¹` norm | `ReciprocalFusion.summable_of_isBounded_sublevel` |
| Theorem 5.1 depth weights `a_j = j + 1` | `ReciprocalFusion.isCompact_sublevel_depth` |
| Theorem 6.1, (RFT.28) bounded amplified work iff `x = 0` | `ReciprocalFusion.bounded_amplified_work_iff` |
| Theorem 6.1, (RFT.29) `S_x - I`, `S_x⁻¹ - I` trace class; `det(S_x) = exp(½∑x_j)` | `ReciprocalFusion.fredholmDet_recovery_of_threshold`, `ReciprocalFusion.fredholmDet_recovery`, `ReciprocalFusion.expDiag_sub_one`, `ReciprocalFusion.coordMatrix_realSummableDiagonalOperator`, `ReciprocalFusion.entireDet2_diagMul_neg_one`, `ReciprocalFusion.summable_abs_exp_sub_one` |
| Theorem 6.1 `x = (t, -t, 0, …)`: determinant `1`, work `> 0` | `ReciprocalFusion.determinant_neutral_not_work_neutral` |
| (RFT.30) ledger: `x = log(Q*Q)`, the Gram determines `x` | `ReciprocalFusion.gram_reconstructs`, `ReciprocalFusion.gram_injective` |
| Loop C: unweighted translates `t eₙ` have constant work, pairwise distance `2|t|`, no Cauchy subsequence | `ReciprocalFusion.unweighted_translates` |

§1, the interpretation of §7, Loops A, B, D, E, F (D and E are the necessity half of Theorem 5.1 and
the determinant counterexample above), §9 and §10 are commentary and state what is not claimed.

## Log

- 2026-08-12 — reversal-only conjecture falsified; binary fusion identified as missing law.
- 2026-08-12 — normalized fusion rigidity proved by d'Alembert reduction.
- 2026-08-12 — unweighted global properness falsified by coordinate escape.
- 2026-08-12 — reciprocal-square complexity criterion proved necessary and sufficient.
- 2026-08-12 — exact diagonal recovery, reciprocal-Gram, weighted-Hilbert--Schmidt, scale-selection,
  and determinant-boundary laws proved.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
