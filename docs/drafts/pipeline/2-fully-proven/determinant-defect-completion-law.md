# Determinant-defect completion law

- **ID:** `determinant-defect-completion-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / candidate parent law
- **Source:** user-directed parent-law search above `residue-corrected-determinant-cofinal-torsion-spectrum`
- **Statement:** Completing finite-rank spectral determinants in Schatten order `p` forgets exactly
  the first `p-1` cyclic power traces; the minimal Hausdorff determinant completion restores their
  renormalized values as a jet-character fibre, and every cofinal determinant/torsion anomaly is
  transport in this fibre.

## Goal

Find and prove one genuinely universal law of which corrected residue jets, cofinal determinant
clusters, relative torsion characters, spectral-suspension sharpness, Mertens ordering spectra,
number-field endpoint cancellation, and failure of determinant-line descent are specializations or
realization theorems.

Pure Hadamard factorization is not enough: divisor plus `exp(P)` is classical. Pure graph-factor
topology is not enough: it would only rename the factorization already present in the paper. New
content must identify the defect fibre intrinsically from the completion functor and prove a
universal property independent of zeta regularization.

## Candidate law

Let `Fin` be finite-rank operators and let `S_p` be its Schatten-`p` completion. On finite rank,

\[
 \log\det(I-zA)=-\sum_{j\ge 1}\frac{\operatorname{Tr}(A^j)}jz^j.
\]

Exactly the tail `j >= p` extends continuously to `S_p`; the first `p-1` power traces do not.
Write

\[
 J_{<p}:=z\mathbf C[z]/(z^p),\qquad
 \mathcal G_p:=\exp(J_{<p}).
\]

**[CONJECTURE — MINIMAL DETERMINANT COMPLETION.]** In the category of Hausdorff topological
spectral extensions of the finite-rank determinant graph over `S_p`, the initial extension on which
the full determinant character is continuous is a principal `G_p`-extension

\[
 \mathcal G_p\longrightarrow \widehat{\mathcal D}_p
 \longrightarrow \mathcal S_p,
\]

with universal character

\[
 (A,P)\longmapsto e^{P(z)}\det_p(I-zA).
\]

Equivalently, every compatible Hausdorff regularization factors uniquely through the stable
Schatten core and the `p-1` missing trace coordinates. The fibre is not imposed: it is the
continuous-character dual of the exact failure of the first `p-1` cyclic traces to extend.

**[CONJECTURE — ZETA TRANSgression.]** For a zeta-admissible inverse `A=L^{-1}`, minimal
subtraction supplies the canonical lift

\[
 P_L(z)=\sum_{j=1}^{p-1}b_j(L)z^j,
 \qquad
 b_j(L)=-\frac1j\bigl(\operatorname{FP}_{s=j}\zeta_L(s)
 +H_{j-1}\operatorname{Res}_{s=j}\zeta_L(s)\bigr).
\]

Thus harmonic residue correction is the coordinate expression of the universal completion map,
not an extra local correction. Relative determinant torsion is the transition character of the
principal extension.

**[CONJECTURE — REALIZATION/SURJECTIVITY.]** Graded spectral suspension gives a right inverse to
the defect map on every finite jet. Hence every `G_p` direction occurs while stable Schatten core,
integer residues, and divisor remain fixed. Arithmetic Mertens systems give nonlinear cofinal
slices of this universal boundary; interval classifications and universal endpoint cancellation
are realization geometry inside one fibre.

## Stronger coordinate-free theorem now isolated

Let `V` be a finite-dimensional complex parameter space and let a finite-rank operator pencil be
`A : V -> Fin(H)`. Put

\[
 D_A(v)=\det(I-A(v)),\qquad
 D_{p,A}(v)=\det_p(I-A(v)).
\]

Use the product of the operator-norm topology on `Hom(V,S_p)` and compact-open topology on
`Hol(V)`. The exact candidate is

\[
 \overline{\{(A,D_A):A:V\to\operatorname{Fin}(H)\}}
 =\left\{(A,e^P D_{p,A}):
 A:V\to\mathcal S_p,\ 
 P\in\bigoplus_{k=1}^{p-1}\operatorname{Sym}^k(V^*)\right\}.       \tag{DC}
\]

Moreover the displayed parametrization is a homeomorphism and is natural under linear pullback
`W -> V`, unitary conjugacy, and direct sum. Thus determinant completion has canonical principal
fibre

\[
 \exp J_{<p}(V),\qquad
 J_{<p}(V)=\bigoplus_{k=1}^{p-1}\operatorname{Sym}^k(V^*).
\]

This is no longer labelled merely conjectural: a dependency-closed proof is recorded below.

### Necessity proof

For finite-rank pencils,

\[
 D_A(v)=D_{p,A}(v)
 \exp\left(-\sum_{k=1}^{p-1}\frac1k\operatorname{Tr}(A(v)^k)\right).
\]

If `A_n -> A` in `Hom(V,S_p)` and `D_{A_n} -> F` compact-open, continuity of `det_p` gives
`D_{p,A_n} -> D_{p,A}`. Their quotient is nonzero near `0` and equals `exp(P_n)`, where `P_n(0)=0`
and `deg P_n < p`. The normalized holomorphic logarithm forces convergence of every coefficient
of `P_n`; the finite-dimensional polynomial space is closed. Hence
`F=exp(P) D_{p,A}` with `P in J_{<p}(V)`. The same normalized logarithmic derivatives recover `P`
continuously, proving injectivity and continuity of inverse.

### Sufficiency proof: vanishing micro-spectra

Choose finite-rank pencil approximants `A_n -> A`. It suffices to construct a finite diagonal
pencil `B_n`, on an orthogonal complement, such that `||B_n||_{S_p} -> 0` and

\[
 \operatorname{Tr}(B_n(v)^k)
 =-kP_k(v)-\operatorname{Tr}(A_n(v)^k),\quad 1\le k<p.       \tag{M}
\]

Every homogeneous form of degree `k` is a finite linear combination of pure powers `ell(v)^k`.
For one term `c ell(v)^k`, take `N` copies of each of the `k` diagonal tuple eigenvalues

\[
 t\omega^r\ell,\qquad r=0,\ldots,k-1,\qquad
 t^k=\frac{c}{kN},\qquad \omega^k=1.
\]

Its trace moment of order `q` vanishes unless `k` divides `q`, its `k`-th moment is exactly
`c ell^k`, and its Schatten cost is

\[
 kN|t|^p=(kN)^{1-p/k}|c|^{p/k}.
\]

Because `k<p`, this tends to zero as `N -> infinity`. Construct degrees in increasing order.
Degree-`k` blocks do not alter earlier moments; absorb their higher moments into later targets.
Choose multiplicities after each residual target is known, making total Schatten cost less than
`1/n`. This proves (M), hence (DC).

### Sharp rank--energy law

For every finite-rank `B` of rank `R` and `k<p`,

\[
 |\operatorname{Tr}(B^k)|
 \le R^{1-k/p}\|B\|_p^k.                                  \tag{RE}
\]

The root-of-unity block above attains equality. Therefore retaining a nonzero degree-`k` defect
while `||B||_p=epsilon` requires and permits exact rank scale

\[
 R\asymp |c|^{p/(p-k)}\epsilon^{-pk/(p-k)}.
\]

At `k=p` the exponent disappears and a vanishing `S_p` perturbation cannot retain a moment.
Thus cutoff `p-1` is forced quantitatively, not chosen by regularization convention.

### Statistics/geometry trichotomy at zero

Suppose all low trace moments converge while `B_n -> 0` in `S_p`.

1. Unrestricted complex spectra realize all of `C^{p-1}` by root-of-unity blocks.
2. Positive spectra retain only a nonnegative first moment: bounded `Tr(B_n)` and
   `||B_n||_infinity -> 0` force every higher moment to zero.
3. Self-adjoint spectra retain only an arbitrary first moment and nonnegative second moment;
   bounded `Tr(B_n^2)` forces moments of degree at least three to zero.
4. Z/2-graded positive spectra realize all of `R^{p-1}`. Forward-difference multiplicities
   `(-1)^{j-r} binom(j,r)` cancel degrees below `j` and retain `j!` in degree `j`.

Consequently superdeterminants are not an artificial sharpness device: group completion is
mathematically necessary to recover the full higher anomaly hierarchy from positive operators.

## Lean status (2026-08-17)

Already in the corpus, from the micro-spectrum layer:

| Card item | Declaration | Module |
|---|---|---|
| root-of-unity block moments vanish below `k` | `rootMicroSpectrumMoment_eq_zero_of_lt` | `RHTower/DeterminantDefectMicroSpectrum` |
| ...and are exactly `c ell^k` at `k` | `rootMicroSpectrumMoment_self` | same |
| realization of a prescribed degree-`k` defect | `exists_rootMicroSpectrum_realizing`, `exists_rootMicroSpectrumPencil_realizing` | same |
| the `p -> q` completion transition and its cocycle | `determinantCompletionTransition`, `determinantCompletionTransition_cocycle` | same |
| the transition preserves the completed character | `determinantCompletionTransition_preserves_character` | same |
| trichotomy 2: positive packets keep only the first moment | `sum_pow_le_max_pow_mul_sum` | `HTGeometry/MicroSpectrumMomentCollapse` |
| trichotomy 3: self-adjoint packets keep only the first two | `abs_sum_pow_le_max_pow_mul_sum_sq` | same |
| trichotomy 4: forward differences cancel below `j`, retain `j!` | `alternating_binomial_sum_pow_eq_zero`, `alternating_binomial_sum_pow_eq_factorial` | same |

New in `HTGeometry/RankEnergyLaw.lean` (umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| **`(RE)`**: `sum a_i^k <= R^{1-k/p} (sum a_i^p)^{k/p}` | `sum_rpow_le_card_rpow_mul` |
| equality for a flat packet (the root-of-unity block) | `sum_rpow_const` |
| **the forced rank scale** at moment `c` and energy `eps` | `card_rpow_ge_of_moment` |
| **the cutoff is forced**: at `k = p` the rank factor is one | `card_rpow_eq_one_of_eq` |
| the Schatten cost `(kN)^{1-p/k}|c|^{p/k}` of a degree-`k` block | `block_cost` |

`(RE)` is proved by Jensen against the counting measure (`Real.rpow_arith_mean_le_arith_mean_rpow`),
which is exactly the Hölder step of the paper proof; `block_cost` is the exact cost identity the
sufficiency construction needs, and `card_rpow_eq_one_of_eq` is the quantitative statement that the
cutoff at `p-1` is forced rather than conventional.

### What remains

The topological statement `(DC)` itself -- that the closure of the finite-rank determinant graph is
the displayed parametrized set, and that the parametrization is a homeomorphism.  Its two halves
need: continuity of `det_p` on Schatten-`p` (Gohberg--Krein/Simon, not in mathlib), and the
normalized-logarithm convergence argument for the polynomial factor.  Mathlib has no Schatten
`det_p`; the corpus carries a regularized determinant only in the diagonal Fock model
(`BosonicFockDiagonalModel.regularizedFredholmDet_eq_exp_neg_traceSeries`).  Building `det_p` on
Schatten classes is the missing infrastructure for this card.

## What must be proved rather than named

1. Define category of determinant extensions so the claimed initial object is neither tautological
   nor false.
2. Prove first `p-1` cyclic power traces are exactly the obstruction: no hidden continuous
   spectral coordinates and no smaller Hausdorff refinement suffice.
3. Prove classification of compatible determinant characters, not merely entire functions with a
   fixed divisor.
4. Derive zeta corrected coordinates functorially from relative-zeta translation.
5. Prove graded suspension is universal on associated graded, not only one explicit example.
6. Recover every theorem of current manuscript through named specialization maps.

## Collision boundary

- Hadamard--Weierstrass factorization already gives `divisor + exp(P)` for finite-order entire
  functions.
- Gohberg--Krein/Simon regularized determinants already give continuity of `det_p` on `S_p` and
  removal of low trace terms.
- Transition identity det_(p+1)=det_p exp((sign) Tr(T^p)/p) is classical; summability-tower
  novelty claim is only its role as transition map between newly identified graph-closure fibres.
- Hartmann--Lesch already gives fixed-operator zeta/Fredholm factorization.
- Quillen, Bismut--Freed, Wodzicki, Kontsevich--Vishik, Paycha--Scott, and determinant torsor/
  gerbe theories already provide geometric carriers and local anomalies.
- Connes--Kreimer/Birkhoff factorization already interprets counterterms as a renormalization
  group.

Candidate-new residue is the **minimal Hausdorff completion universal property**, its exact
identification with the lost low cyclic traces, and the surjective cofinal realization theorem.
If this reduces to a formal graph closure or classical determinant classification, retire it.

## Summability filtration upgrade

For every real Schatten exponent r >= 1, put m = ceil(r). The same proof gives

\[
 \overline{\operatorname{Graph}(\det_{\mathrm{fin}})}
 \cong \operatorname{Hom}(V,\mathcal S_r)\times
 \exp\!\left(\bigoplus_{1\le k<r}\operatorname{Sym}^k(V^*)\right),
\]

with regularized core det_m. Degree-k micro-spectrum cost is N^(1-r/k), and sharp rank exponent
is r/(r-k). Therefore anomaly fibre jumps only when summability crosses an integer.

For integers p < q, natural embedding of completions is

\[
 (A,P)\longmapsto
 \left(A,P-\sum_{j=p}^{q-1}\frac{\operatorname{Tr}(A(\cdot)^j)}j\right).
\]

It preserves completed determinant character because
det_q = det_p exp(sum_{p<=j<q} Tr(A^j)/j). Transition polynomials satisfy exact cocycle, so
associated new layer at threshold p is Sym^p(V*).

## Falsifiers

- A source proving same initial/principal-extension theorem for Schatten determinant graphs.
- A compatible regularization requiring an invariant not determined by `A` and the truncated
  power-trace jet.
- A nonzero continuous extension of a low power trace to `S_p` that shrinks the predicted fibre.
- Failure of uniqueness because category permits arbitrary invisible factors; then axioms are too
  weak and must be strengthened without baking in conclusion.
- Suspension realizes polynomial characters algebraically but not by admissible zeta operators;
  then surjectivity is only formal and cannot support general-journal claim.

## Gates

- [x] 0 → 1: candidate stated; classical shadow separated; falsifiers explicit
- [x] 1 → 2: concrete graph closure, homeomorphism, multivariable proof, sharp rank law,
  statistics trichotomy, real-exponent phase law, and summability tower proved on paper
- [ ] 2 → 3: unconditional Lean formalization of universal algebra/topology core
- [ ] 3 → 4: rewritten standalone paper and hostile review

## Log

- 2026-08-04 — Parent-law search opened. Pure Hadamard and abstract factor transport rejected as
  insufficient. Minimal determinant completion and lost-cyclic-trace duality isolated as first
  serious candidate.
- 2026-08-04 — Proved coordinate-free multivariable determinant-graph closure by normalized-log
  necessity and root-of-unity micro-spectrum sufficiency. Proved sharp rank--energy exponent and
  positive/self-adjoint/graded-positive defect classification.
- 2026-08-04 — Extended law to every real Schatten exponent and proved natural summability tower.
  Lean module RHTower/DeterminantDefectMicroSpectrum.lean compiles: root-block cancellation,
  exact pure homogeneous pencil realization, and transition cocycle are unconditional.
- 2026-08-04 — Proved family completion. For compact Hausdorff `X`, closure of continuous
  finite-support pencils is
  `C(X, Hom(V,S_p)) x C(X,J_<p(V))`; same holds sheafwise for holomorphic bases. Root-free
  weighted cyclic blocks realize a coefficient `c(x) ell^k` with matrix entries linear in
  `c(x)`, lower moments zero, exact `k`th moment, and uniform cost `O(N^(1-p/k))`. This removes
  branch-choice obstruction and identifies family fibre as continuous/holomorphic gauge group.
- 2026-08-04 — Found closest conceptual predecessor: Quillen's 1989 conjectural principal bundle
  under bounded-degree polynomial functions, and N. V. Dang, *Analysis & PDE* 15 (2022), 1--62,
  which proves local elliptic renormalized determinants form a torsor under local polynomial
  counterterms. This is a required citation, not a collision with (DC): Dang fixes elliptic
  background, imposes microlocal locality, and subtracts counterterms; (DC) classifies closure of
  raw finite-rank determinants under Schatten convergence and proves every unconstrained fibre
  direction by vanishing micro-spectra. Conversely, (DC) does not replace Dang's locality theorem.
  Manuscript novelty boundary now states both directions explicitly.
- 2026-08-04 — Rewritten 29-page manuscript around parent law and passed internal hostile review
  at an *Advances in Mathematics*/*Mathematische Annalen*-level submission bar. Final Tectonic
  compile has no box, citation, or reference warnings; all pages visually inspected. Four
  determinant/residue-jet Lean sources pass, determinant-stack top module builds, principal
  declarations have only standard Lean axioms, umbrella import and API index are present, and no
  route-owned Lean process remains. Repository-global umbrella/lint attempt is separately red
  from unrelated concurrent sieve declaration collision and unrelated unreachable modules; this
  card's targeted stack is clean.

## Lean progress -- the sharp rank--energy law `(RE)`

`formal/GaloisForLFunctions/HTGeometry/RankEnergyPowerSum.lean` (new, umbrella-wired,
axiom-clean) proves the card's sharp rank--energy law and the spectral identity it needs.

| Card item | Declaration |
|---|---|
| **the power-sum bound** `∑ a_i^k <= R^{1-k/p} (∑ a_i^p)^{k/p}` for a nonnegative packet on `R` levels and `0 < k <= p`, real exponents throughout | `sum_rpow_le_card_rpow_mul_sum_rpow` |
| a conjugated matrix has conjugated powers | `pow_conj_diagonal` |
| **the trace power of a Hermitian matrix is the eigenvalue power sum** | `trace_pow_eq_sum_eigenvalues_pow` |
| the eigenvalue form of the bound | `abs_sum_eigenvalues_pow_le_rank_energy` |
| **`(RE)`**: `‖Tr(B^k)‖ <= n^{1-k/p} · (∑ |lambda_i|^p)^{k/p}` for Hermitian `B` | `norm_trace_pow_le_rank_energy` |

The proof of the power-sum bound is Jensen for `x |-> x^{p/k}` against uniform weights, so the
constant `R^{1-k/p}` is exactly the one attained by a flat packet: the bound is sharp, and the
`k = p` degeneration in which the exponent disappears is visible in the statement itself.  This is
the quantitative reason the cutoff sits at `p-1` rather than being a regularization convention.

Scope note.  `(RE)` is certified here for Hermitian `B`, where the singular values are the moduli
of the eigenvalues and `(∑ |lambda_i|^p)^{1/p}` is literally the Schatten norm.  For a general
finite-rank `B` the same statement additionally needs Weyl's majorant inequality
`∑ |lambda_i|^k <= ∑ s_i^k`, which mathlib does not carry; the Hermitian case is what the card's
statistics/geometry trichotomy and the self-adjoint branch actually use.

## Lean progress -- the statistics/geometry trichotomy at zero

`formal/GaloisForLFunctions/HTGeometry/MicroSpectrumMomentCollapse.lean` (new, umbrella-wired,
axiom-clean) proves the sign-regime part of the trichotomy and the graded realisation identity.

| Card item | Declaration |
|---|---|
| **item 2**: a positive packet with bounded first moment loses every moment of degree at least two, since `∑ a_i^k <= (max a_i)^{k-1} ∑ a_i` | `sum_pow_le_max_pow_mul_sum` |
| **item 3**: a self-adjoint packet with bounded second moment loses every moment of degree at least three, since `\|∑ a_i^k\| <= (max \|a_i\|)^{k-2} ∑ a_i^2` | `abs_sum_pow_le_max_pow_mul_sum_sq` |
| the squeeze that turns either bound into "the moment tends to zero" | `tendsto_zero_of_abs_le_mul` |
| **item 4**: forward-difference multiplicities `(-1)^{j-r} C(j,r)` cancel every degree below `j` | `alternating_binomial_sum_pow_eq_zero` |
| **item 4**: and retain exactly `j!` in degree `j` | `alternating_binomial_sum_pow_eq_factorial` |

Both moment-collapse bounds are elementary and sharp in the exponent: the surviving degree is
exactly the one whose moment is assumed bounded.  So positivity really cannot carry a higher
anomaly, and the card's conclusion -- that group completion is mathematically necessary rather
than an artificial sharpness device -- is a consequence of these two displayed inequalities.

The forward-difference identities are derived from mathlib's `fwdDiff_iter_pow_eq_zero_of_lt` and
`fwdDiff_iter_eq_factorial` by evaluating `fwdDiff_iter_eq_sum_shift` at the origin, so the
explicit alternating-binomial form the card uses is now available directly.

## Lean progress -- the vanishing micro-spectrum construction

`formal/GaloisForLFunctions/HTGeometry/RootBlockMomentSelection.lean` (new, umbrella-wired,
axiom-clean) proves the selection mechanism of `(M)` and its cost law.

| Card item | Declaration |
|---|---|
| the `k` diagonal eigenvalues `t ω^r` of one selecting block | `unitRoot`, `rootBlock`, `unitRoot_isPrimitiveRoot` |
| **its trace moment of order `q` vanishes unless `k` divides `q`** | `sum_rootBlock_pow` |
| **and its `k`-th moment is exactly `k t^k`** | `sum_rootBlock_pow_self` |
| every eigenvalue of the block has modulus `\|t\|`, so its Schatten cost is `k N \|t\|^p` | `norm_rootBlock` |
| **the cost `(kN)^{1-p/k}\|c\|^{p/k}` tends to zero as `N` grows, precisely because `k < p`** | `tendsto_rootBlock_schattenCost` |

The cost law is stated so that the `k = p` degeneration is visible in the hypothesis: the limit is
proved from `k < p` alone, and at `k = p` the exponent `1 - p/k` is zero and the statement is
false.  Together with `(RE)` this is the card's claim that the cutoff `p-1` is forced
quantitatively rather than chosen by convention -- one bound says a moment below the order can be
written for free, the other says a moment at the order cannot.

### What remains

Assembling the blocks of `(M)` into a full pencil -- degrees in increasing order, absorbing higher
moments into later targets, and the choice of multiplicities -- together with the necessity
direction of `(DC)`, which needs `det_p` and the compact-open topology on holomorphic families.
