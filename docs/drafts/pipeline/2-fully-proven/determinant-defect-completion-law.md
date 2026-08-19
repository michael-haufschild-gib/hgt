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

## Lean progress -- the vanishing micro-spectrum construction `(M)` is assembled

`formal/GaloisForLFunctions/HTGeometry/MicroSpectrumMomentAssembly.lean` (new, umbrella-wired,
axiom-clean) closes the first of the two items in "What remains": the blocks of `(M)` are now run
in increasing order of degree and assembled into one spectrum.

| Card item | Declaration |
|---|---|
| `N` copies of a root-of-unity block of order `k` and radius `t` | `rootBlockMultiset` |
| its power sums: `N k t^q` in the degrees divisible by `k`, zero otherwise | `sum_map_pow_rootBlockMultiset` |
| its Schatten `p` energy, `N k ‖t‖^p` | `sum_map_normPow_rootBlockMultiset` |
| **one block writes one moment inside any energy budget**, disturbing no lower moment | `exists_block_realizing` |
| **`(M)`**: every prescribed target for the moments `1, …, n` with `n < p` is realised by a finite spectrum inside any Schatten `p` budget | `exists_multiset_moment_realization` |

Two things make the assembly finite and exponent-free.

*Increasing order.*  A block of order `k` contributes only in degrees divisible by `k`, hence
nothing at all below `k`.  So when the induction reaches degree `k` the residual target is already
determined by the blocks already placed, and placing the `k`-block cannot spoil any earlier
degree.  The higher degrees it does disturb are absorbed by the later stages, exactly as the card
says.

*The cost identity needs no fractional exponent.*  Distributing a target `R` over `N` copies of a
`k`-block of radius `t` fixes `‖t‖^k = ‖R‖/(kN)`, so

`kN‖t‖^p = kN · ‖t‖^k · ‖t‖^{p−k} = ‖R‖ · ‖t‖^{p−k}`,

and `p − k ≥ 1`.  More copies means smaller `t` means smaller energy, with only natural-number
exponents.  At `k = p` the factor `‖t‖^{p−k}` is `1` and the mechanism disappears -- the same
quantitative reason for the cutoff at `p − 1` that `(RE)` gives from the other side.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

### What remains

Only the necessity direction of `(DC)`: the closure of the finite-rank determinant graph.  The
corpus already owns the `p = 2` analytic input --
`HTGeometry/RegularizedDeterminantLimit.entireDet2` (the entire Hilbert--Carleman determinant of a
Hilbert--Schmidt kernel) together with
`HTGeometry/EntireDet2HilbertSchmidtContinuity.tendsto_entireDet2_of_hsNorm_sub_tendsto_zero`
(continuity of `det₂` under Hilbert--Schmidt convergence), and `fredholmDet1` for the trace-class
correction -- so the `p = 2` case of `(DC)` is reachable from what is already proved.  General `p`
needs `det_p` on Schatten `p`, for which the standard route is Simon's
`det_p(1 + A) = det₁(1 + R_p(A))` with `R_p : S_p → S_1` continuous.

## Lean progress -- the `p = 2` sufficiency of `(DC)`, at the level of the forgotten coordinate

`formal/GaloisForLFunctions/HTGeometry/FiniteRankTracePrescription.lean` (new, umbrella-wired,
axiom-clean) proves the sufficiency half of `(DC)` in the case the corpus's determinant stack can
already see: `p = 2`, where the only forgotten coordinate is the trace.

| Card item | Declaration |
|---|---|
| `M` equal diagonal entries placed beyond the truncation block | `HilbertSchmidt.diagBlock`, `diagBlock_eq_zero_of_notMem`, `isHS_diagBlock` |
| its Hilbert--Schmidt energy `M‖t‖²` | `hsNormSq_diagBlock` |
| its diagonal trace `M t` | `hsTraceDiag_diagBlock` |
| **every Hilbert--Schmidt kernel is approximated in Hilbert--Schmidt norm, to any accuracy, by finitely supported kernels of *any* prescribed diagonal trace** | `exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq` |

This is the sufficiency mechanism of `(M)` at `k = 1`, `p = 2`, and it is exponent-free: spreading
the required trace over `M` equal diagonal entries gives trace `M t` and energy `M‖t‖² = |t M|²/M`,
so the energy vanishes while the trace stays put.  The trace -- the one coordinate `det₂` forgets
-- is therefore genuinely free in the limit, which is what the completion law asserts.

Together with `MicroSpectrumMomentAssembly.exists_multiset_moment_realization` (the same statement
for all the moments `1, …, p−1` at once, for every `p`) the *spectral* content of the sufficiency
direction of `(DC)` is now formal at every order; what remains on that side is only its transport
into the operator model at general `p`, which is the same `det_p` infrastructure the necessity
direction needs.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

## Lean progress -- `(DC)` closed in both directions at Schatten order two

Two further modules (new, umbrella-wired, axiom-clean) close the coordinate-free theorem `(DC)`
completely in the case `p = 2`, `dim V = 1`, where the pencil is `A(z) = zK` and the fibre
`J_{<2}(V) = Sym¹(V*)` is the single linear jet `−cz`.

`formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantTraceRecovery.lean`

| Card item | Declaration |
|---|---|
| `det(1+zM) e^{−z·tr M}` has no linear term | `taylorCoeff_finiteDet2_one` |
| the same for a Hilbert--Schmidt kernel | `detCoeff_one_eq_zero`, `deriv_entireDet2_zero` |
| the completed character `e^{P(z)} det_p(1−zA)` | `completedDet2` |
| **the normalized logarithmic derivative recovers `P`** | `deriv_completedDet2_zero`: `D'(0) = −c` |
| ...hence injectivity of the parametrization | `completedDet2_inj` |
| **necessity**: every compact-open limit is again a completed determinant, and the coordinate converges | `tendsto_completionCoefficient` |

`formal/GaloisForLFunctions/HTGeometry/FiniteRankDeterminantCompletion.lean`

| Card item | Declaration |
|---|---|
| a block kernel's regularized determinant is the finite one | `entireDet2_eq_finiteDet2_of_support` |
| `D_A(v) = D_{p,A}(v) exp(−∑_{k<p} Tr(A^k)/k)` at `p = 2` | `det_one_sub_smul_blockMatrix`: `det(1 − z·K|ₛ) = det₂(1−zK)·e^{−z·tr K}` |
| **sufficiency**: every `G_p` direction occurs | `exists_finiteRank_det_tendsto_completedDet2` |

Sufficiency is proved by `(M)` at `k = 1`: `FiniteRankTracePrescription` supplies finitely supported
kernels approaching `K` in Hilbert--Schmidt norm whose diagonal trace is *exactly* the prescribed
`c`, and the block determinants of those kernels are, by
`det_one_sub_smul_blockMatrix`, precisely the completed determinants `det₂(1−zK_n)e^{−cz}`; the
Hilbert--Schmidt continuity of `det₂` then transports them to `det₂(1−zK)e^{−cz}`.

Necessity needs no closedness argument at all in this case: the coordinate is an explicit
continuous functional of the determinant, `c = −D'(0)`, because the regularized determinant is
*flat* at the origin -- the trace counterterm is defined to kill the linear term. Local uniform
convergence of the determinants therefore forces convergence of the coordinates directly.

So at `p = 2` the closure of the finite-rank determinant graph over the Hilbert--Schmidt kernels is
exactly the set of completed determinants, the parametrization is injective, and the coordinate map
is continuous in both directions. The residual gap in `(DC)` is entirely the passage to general `p`
(a `det_p` on Schatten-`p`, i.e. Simon's `det_p(1+A) = det₁(1+R_p(A))`) and to `dim V > 1`, where
the fibre is a polynomial rather than a single scalar; the mechanism -- flatness of the
regularization below degree `p`, and free prescription of the low moments at vanishing Schatten
cost -- is now formal, the latter at every order via
`MicroSpectrumMomentAssembly.exists_multiset_moment_realization`.

Axiom audit for all nine declarations: `propext`, `Classical.choice`, `Quot.sound`.

## Lean progress -- the multivariable fibre at Schatten order two

The card's `(DC)` is stated for a pencil over a finite-dimensional parameter space `V`, with fibre
`⊕_{k=1}^{p-1} Sym^k(V*)`.  At `p = 2` that fibre is `Sym¹(V*)`, the linear forms on `V`, and the
several-variable statement needs no new analysis: a pencil is *linear*, so restricting it to a
coordinate axis turns the parameter into the spectral variable.  Two new modules, both
umbrella-wired and axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantScaling.lean`

| Card item | Declaration |
|---|---|
| the Hilbert--Schmidt scaling laws | `HilbertSchmidt.hsNorm_smul`, `hsComp_smul_left`, `hsComp_smul_right`, `hsPow_smul`, `hsTrace_hsPow_smul` |
| **rescaling the kernel rescales the spectral variable**, in the exponent and on the disc | `HilbertSchmidt.fredholmExp_smul`, `HilbertSchmidt.fredholmDet_smul` |
| **the same for the entire representative**: `det₂(1 − z·cK) = det₂(1 − (cz)K)` | `entireDet2_smul` |

`formal/GaloisForLFunctions/HTGeometry/PencilDeterminantCompletion.lean`

| Card item | Declaration |
|---|---|
| Hilbert--Schmidt kernels are closed under finite sums | `isHS_zero`, `isHS_finsetSum` |
| the kernel of a linear pencil `A(v) = ∑ vᵢ Aᵢ` | `pencilKernel`, `isHS_pencilKernel` |
| **its restriction to a coordinate axis is a rescaled kernel** | `pencilKernel_axis` |
| the fibre coordinate `P ∈ Sym¹(V*)` | `linearJet`, `linearJet_axis` |
| the completed character `e^{P} det₂(1 − A(·))` of a pencil | `completedPencilDet` |
| **the axis restriction of a pencil completion is a one-variable completion** | `completedPencilDet_axis` |
| **each coefficient of the jet is a derivative at the origin along its axis** | `deriv_completedPencilDet_axis` |
| **the fibre coordinate of a pencil is faithful** | `linearJet_eq_of_completedPencilDet_eq` |
| **multivariable necessity at order two**: coefficientwise Hilbert--Schmidt convergence plus axiswise locally uniform convergence forces every jet coefficient to converge, to the completed determinant of the limit kernel | `tendsto_pencilJet` |

`entireDet2_smul` is what makes the reduction legitimate, and it is proved without any analysis:
the defining exponent `∑_{n≥2} zⁿ tr(Kⁿ)/n` picks up exactly `cⁿ` under `K ↦ cK`, so it depends on
`cz` alone, and uniqueness of the entire representative transports the identity off the disc.

So at `p = 2` the determinant-completion law now holds in the card's multivariable form: the fibre
is `Sym¹(V*)`, the parametrization is injective, and the coordinate map is continuous, in every
finite number of parameters.  What remains for `(DC)` in full is only the passage to general `p`,
where the fibre acquires the higher symmetric powers and the regularized determinant `det_p` must
be constructed on Schatten-`p` -- the spectral side of which is already formal at every order via
`MicroSpectrumMomentAssembly.exists_multiset_moment_realization`.

Axiom audit for all listed declarations: `propext`, `Classical.choice`, `Quot.sound`.

## Lean progress -- the regularized determinant at every order

The card's opening display

`log det(I − zA) = −∑_{j ≥ 1} Tr(A^j) z^j / j`,   "exactly the tail `j ≥ p` extends"

is now formal at every order, not only at `p = 2`.  Two new modules, umbrella-wired and
axiom-clean.

`formal/GaloisForLFunctions/HTGeometry/FiniteRegularizedDeterminantOrder.lean`

| Card item | Declaration |
|---|---|
| the scalar tail `∑_{k ≥ g+1} w^k/k = −log(1−w) − ∑_{k=1}^{g} w^k/k` | `tsum_pow_div_add_succ`, `exp_neg_tsum_pow_div_add_succ` |
| **`det_{g+1}(1 + zM) = det(1 + zM)·exp(∑_{k=1}^{g} (−z)^k Tr(M^k)/k)`** | `finiteDetOrder` |
| at order two it is the corpus determinant | `finiteDetOrder_one` |
| the Schur product form -- a product of scalar primary factors of genus `g` | `finiteDetOrder_eq_prod` |
| stability under reindexing | `finiteDetOrder_submatrix` |
| **the trace-series identity at every order**: `exp(−∑_{k ≥ g+1} z^k Tr(M^k)/k) = det_{g+1}(1 − zM)` | `exp_neg_traceSeries_eq_finiteDetOrder_neg_fin`, `exp_neg_traceSeries_eq_finiteDetOrder_neg` |

`formal/GaloisForLFunctions/HTGeometry/RegularizedDeterminantForgetting.lean`

| Card item | Declaration |
|---|---|
| **the exponent vanishes to order `g+1`**: it is `z^{g+1}` times a series in `z`, so no trace below order `g+1` occurs in it | `traceSeries_eq_pow_mul` |
| **the determinant forgets the first `g` power traces**: two matrices whose power traces agree from order `g+1` on have the same order-`g+1` regularized determinant | `finiteDetOrder_neg_eq_of_traceTail_eq` |

The second theorem is the card's *forgetting* half, stated exactly: `det_p` is a function of the
tail `Tr(A^p), Tr(A^{p+1}), …` alone, so `Tr(A), …, Tr(A^{p-1})` are genuinely absent from it -- and
that is what makes them the fibre coordinates of the completion.  The proof is the exponential
formula and nothing else; the previously available `g = 1` case is the `finiteDetOrder_one`
instance.

Axiom audit: `propext`, `Classical.choice`, `Quot.sound`.

### What the general-`p` completion still needs

The *analytic* half: `det_p` on the Schatten-`p` ideal, i.e. Simon's `det_p(1+A) = det₁(1 + R_p(A))`
with `‖R_p(A)‖₁ ≤ c_p ‖A‖_p^p`, so that the finite-order determinant above extends continuously.
The spectral half is complete at every order
(`MicroSpectrumMomentAssembly.exists_multiset_moment_realization` for sufficiency, and the two
theorems above for the forgetting), and the whole law is closed at `p = 2` in the card's
multivariable form.

## Lean progress -- `det_p` on an `ℓ^p` spectrum

The card's remaining analytic item is a regularized determinant of order `p` that extends the
finite-rank one continuously.  `formal/GaloisForLFunctions/HTGeometry/SchattenSpectralDeterminant.lean`
(new, umbrella-wired, axiom-clean) builds it on the spectral side, where a Schatten-`p` datum is an
`ℓ^p` family of eigenvalues, by exactly the construction the corpus already uses at order two
(`fredholmExp`/`fredholmDet`): the regularized exponent is the trace series from exponent `p`
upwards, and the determinant is the negative exponential of it.

| Card item | Declaration |
|---|---|
| the spectral-side Schatten-`p` datum | `IsSchattenSpectrum` |
| **an `ℓ^p` spectrum is bounded** | `exists_bound_of_isSchattenSpectrum` |
| every power above the Schatten exponent is summable | `summable_normPow_of_le`, `summable_pow_of_le` |
| the power traces, and their geometric bound `‖tr(A^{k+p})‖ ≤ B^k ‖A‖_p^p` | `schattenTracePower`, `norm_schattenTracePower_le` |
| the order-`p` regularized exponent, convergent inside the reciprocal spectral radius | `schattenDetExp`, `summable_schattenDetExp` |
| **the order-`p` regularized determinant** | `schattenDet` |
| **it forgets every trace below `p`** -- the card's forgetting half, now in the completed setting | `schattenDet_congr` |
| every finite family is an `ℓ^p` spectrum, and its power traces are the matrix power traces of its diagonal | `isSchattenSpectrum_of_finite`, `schattenTracePower_diagonal` |
| **it extends the finite-rank order-`p` determinant** | `schattenDet_eq_finiteDetOrder` |
| **it is continuous in the power traces** under a common geometric bound | `tendsto_schattenDet_of_tendsto_tracePower` |

Three points are worth recording.

1. The *forgetting* property is now a one-line consequence of the definition rather than a theorem
   about finite matrices: `det_p` is literally a function of the traces from `p` upwards.  Combined
   with `finiteDetOrder_neg_eq_of_traceTail_eq` this closes the forgetting half of the card at every
   order, on finite rank and in the completion alike.
2. The extension statement is exact: on a finite spectrum the new determinant *is*
   `finiteDetOrder (p-1)` of the diagonal, with no limit and no approximation, so the completion
   genuinely extends the finite-rank object the card starts from.
3. Continuity is proved in the form the card's limit argument uses -- convergence of the power
   traces under one geometric bound -- via Tannery's theorem, so no operator topology is needed.

What remains for the operator side is the identification of an operator's `det_p` with the `det_p`
of its eigenvalue sequence, i.e. a Lidskii-type theorem, and the entire (rather than disc-level)
extension at order `p`, which needs the order-`p` Carleman coefficient bound.  Both are independent
of the card's algebraic content, which is now formal at every order.

## Lean progress -- Lidskii for every power trace, and the operator-side `det_p`

The remaining operator-side item was the identification of an operator's `det_p` with the `det_p`
of its eigenvalue sequence.  Two new modules (umbrella-wired, `lake build` green, axioms =
`propext`/`Classical.choice`/`Quot.sound`) supply it.

`formal/GaloisForLFunctions/HTGeometry/LidskiiPowerTrace.lean`

| Card item | Declaration |
|---|---|
| **the trace of an operator diagonal on the signed greedy family** | `opTrace_eq_tsum_of_sgVec_diagonal` |
| **Lidskii for power traces**: `tr(Sᵐ) = ∑ₙ λₙ(S)ᵐ` | `opTrace_pow_eq_tsum_sgVal_pow` |

The corpus's Lidskii theorem is for the operator itself; the completion needs *every* power trace.
The greedy eigenvectors of a compact self-adjoint `S` diagonalize far more than `S`: any operator
acting on them by scalars and killing their joint orthogonal complement has its trace computed by
the same Hilbert-basis extension.  That abstraction is proved once, and powers are the special
case: `Sᵐ eₙ = λₙᵐ eₙ` unconditionally from `apply_sgVec`, and `S u = 0` forces `Sᵐ u = 0`.

`formal/GaloisForLFunctions/HTGeometry/SchattenOperatorDeterminant.lean`

| Card item | Declaration |
|---|---|
| the operator-side order-`p` regularized determinant | `opSchattenDetExp`, `opSchattenDet` |
| the spectral power traces are the operator power traces | `schattenTracePower_sgVal_eq_opTrace_pow` |
| **the operator determinant is the determinant of its spectrum** | `opSchattenDetExp_eq_schattenDetExp`, `opSchattenDet_eq_schattenDet` |
| **it forgets every trace below `p`**, in the operator formulation | `opSchattenDet_congr` |

So `det_p` is now defined directly on the operator by the same series in its own power traces, and
agrees with the spectral `det_p` of the signed greedy eigenvalue sequence whenever each power from
`p` upwards is trace class.  Combined with `schattenDet_eq_finiteDetOrder` this gives the full
chain finite rank → spectrum → operator at every order `p`.

What remains for the card at general `p` is only the *quantitative* half -- Simon's
`‖R_p(A)‖₁ ≤ c_p‖A‖_p^p`, which upgrades the disc-level determinant to an entire function -- and it
is independent of both the algebraic content and this identification.

## Lean progress -- the normalized-logarithm half of `(DC)`'s necessity

The necessity direction of `(DC)` has two halves: continuity of `det_p` on the Schatten class, and
the argument that *the polynomial factor converges* -- "the normalized holomorphic logarithm forces
convergence of every coefficient of `P_n`; the finite-dimensional polynomial space is closed".  The
second half is now formal, unconditionally and independently of any Schatten-class analysis.

`formal/GaloisForLFunctions/HTGeometry/BoundedDegreePolynomialLimit.lean` (new, umbrella-wired,
axioms = `propext`/`Classical.choice`/`Quot.sound`)

| Card item | Declaration |
|---|---|
| the interpolant of a limiting sample vector, and its degree bound | `lagrangeLimitPoly`, `natDegree_lagrangeLimitPoly_le` |
| a bounded-degree polynomial is its own interpolant | `eq_lagrangeLimitPoly_of_natDegree_le` |
| **values converge to the values of the limit polynomial** | `tendsto_eval_of_tendsto_samples` |
| **and so does every coefficient** | `tendsto_coeff_of_tendsto_samples` |

This is "the finite-dimensional polynomial space is closed", in the only form the argument needs: a
polynomial of degree at most `J` is a *linear* function of its values at `J+1` fixed nodes, so
convergence of those values is convergence in the space.  The corpus already owned the linear
recovery (`coeff_eq_sum_gaussianLagrange`, `gaussianLagrangeNodes`), so only the limit statement was
new.

`formal/GaloisForLFunctions/HTGeometry/NormalizedPolynomialFactorLimit.lean` (new, umbrella-wired,
axiom-clean)

| Card item | Declaration |
|---|---|
| the antiderivative normalized to vanish at the origin | `normalizedAntiderivative`, `coeff_normalizedAntiderivative_zero`, `coeff_normalizedAntiderivative_succ`, `natDegree_normalizedAntiderivative_le` |
| **the normalized polynomial factor converges** | `exists_limit_of_tendsto_derivative_samples` |

This is the "normalized holomorphic logarithm" step, with the logarithm eliminated: `exp` is not
injective, so the values of `exp P_n` do not determine `P_n`, but the *logarithmic derivative*
`P_n' = (exp P_n)'/(exp P_n)` does, and the normalization `P_n(0) = 0` recovers `P_n` from `P_n'`.
So convergence of the logarithmic derivatives at `p` fixed nodes forces coefficientwise convergence
of the polynomial factors, and the limit is a polynomial with the same degree bound and the same
normalization -- which is exactly the statement that the fibre `exp J_{<p}` is closed.

What remains for `(DC)` is only the *analytic* half: continuity of `det_p` on the Schatten class,
i.e. Simon's `‖R_p(A)‖₁ ≤ c_p‖A‖_p^p`.  At `p = 2` the corpus already owns it
(`EntireDet2HilbertSchmidtContinuity.tendsto_entireDet2_of_hsNorm_sub_tendsto_zero`), so the `p = 2`
case of `(DC)` is now complete on both halves.

## Lean progress -- `(DC)`'s necessity in the finite-rank category, at every order

The necessity direction of `(DC)` is now proved wherever the objects are finite rank, at every
order, with no Schatten-class analysis at all.  Three new modules (umbrella-wired, axioms =
`propext`/`Classical.choice`/`Quot.sound`).

`formal/GaloisForLFunctions/HTGeometry/GeneralNodePolynomialLimit.lean`

| Card item | Declaration |
|---|---|
| the interpolant, its degree bound, and self-interpolation at arbitrary nodes | `nodeLimitPoly`, `natDegree_nodeLimitPoly_le`, `eq_nodeLimitPoly_of_natDegree_le` |
| the linear coefficient recovery at arbitrary nodes | `coeff_eq_sum_lagrangeBasis` |
| coefficientwise convergence from sample convergence | `tendsto_coeff_of_tendsto_samples_at` |
| values converge when coefficients do | `tendsto_eval_of_tendsto_coeff` |
| **the normalized polynomial factor converges, at arbitrary nodes** | `exists_limit_of_tendsto_derivative_samples_at` |

The nodes must be free rather than fixed, because the recovery has to run *inside* the region where
the limit function does not vanish.

`formal/GaloisForLFunctions/HTGeometry/ExpPolynomialFactorClosure.lean`

| Card item | Declaration |
|---|---|
| the derivative of the exponential of a polynomial | `deriv_exp_polynomial` |
| **the exponential-polynomial fibre is closed under locally uniform limits** | `exists_poly_limit_of_tendstoLocallyUniformlyOn_exp` |

`formal/GaloisForLFunctions/HTGeometry/FiniteDeterminantGraphClosure.lean`

| Card item | Declaration |
|---|---|
| the polynomial of the first `g` power traces | `tracePolynomial`, `eval_tracePolynomial`, `coeff_tracePolynomial_zero`, `natDegree_tracePolynomial_le` |
| **the factorisation on finite rank**: `det(1+zM) = det_{g+1}(1+zM)·exp(P_M(z))` | `det_one_add_smul_eq_finiteDetOrder_mul_exp` |
| the finite-rank determinant and its regularization are analytic in the parameter | `analyticAt_det_one_add_smul`, `analyticAt_finiteDetOrder` |
| **`(DC)`'s necessity: the closure of the finite-rank determinant graph** | `exists_poly_limit_of_tendsto_finiteDet` |

`exists_poly_limit_of_tendsto_finiteDet` is the card's necessity argument, formalised: if the
finite-rank determinants converge locally uniformly to `F` and their order-`g+1` regularizations to
`E`, and both limits are nonzero at `g+1` distinct points, then `F = E·exp(Q)` with `Q` of degree at
most `g` and `Q(0) = 0`.  The mechanism is exactly the card's: the logarithmic derivatives satisfy
`P_n' = F_n'/F_n − E_n'/E_n`, derivatives of locally uniform limits of holomorphic functions
converge, and the finite-dimensional polynomial space is closed.  No quotient of locally uniform
limits is ever formed -- the two families are differentiated separately, which is what makes the
argument work without any bound-away-from-zero estimate.

So the fibre `exp J_{<p}` is Lean-certified as *exactly* the ambiguity of the completion, in the
finite-rank category, at every `p`.  What `(DC)` still needs is the passage from finite rank to the
Schatten class, i.e. continuity of `det_p` there -- Simon's `‖R_p(A)‖₁ ≤ c_p‖A‖_p^p`.  At `p = 2` the
corpus already owns that continuity, so the `p = 2` case of `(DC)` is complete on both halves.

## Lean progress -- `(DC)`'s necessity on the spectral side, at every order

The finite-rank closure of the previous section is now carried to the Schatten-`p` determinant of a
spectrum, which is where the corpus's `det_p` and the card's sufficiency construction both live.
Three new modules (umbrella-wired, axioms = `propext`/`Classical.choice`/`Quot.sound`).

`formal/GaloisForLFunctions/HTGeometry/ExpFactorPointwiseClosure.lean`

| Card item | Declaration |
|---|---|
| **the fibre is closed under pointwise convergence of values and derivatives at the nodes** | `exists_poly_limit_of_tendsto_exp_samples` |

Stating the closure pointwise rather than locally uniformly is what makes it usable on the spectral
side: for a series-defined determinant, locally uniform convergence is exactly the hard part, while
the value and the derivative at finitely many points are directly computable.

`formal/GaloisForLFunctions/HTGeometry/SchattenDetDerivative.lean`

| Card item | Declaration |
|---|---|
| the terms of the regularized exponent and their derivatives | `schattenDetExpTerm`, `deriv_schattenDetExpTerm`, `norm_schattenDetExpTerm_le` |
| **termwise differentiation inside the reciprocal spectral radius** | `hasSum_deriv_schattenDetExp`, `deriv_schattenDetExp_eq` |
| the regularized exponent is differentiable there | `differentiableAt_schattenDetExp` |
| **the derivative of the exponent is continuous in the power traces** | `tendsto_deriv_schattenDetExp_of_tendsto_tracePower` |
| the derivative of the determinant, and its continuity in the power traces | `deriv_schattenDet_eq`, `tendsto_deriv_schattenDet_of_tendsto_tracePower` |

The geometric majorant `‖tr(A^{k+p})‖ ≤ S B^k` that makes `det_p` converge also makes it
differentiable termwise, and the differentiated series carries the *same* majorant with one power of
`r` removed -- so the derivative inherits the continuity in the power traces that the determinant
already had.  No uniform convergence and no Vitali-type theorem is used.

`formal/GaloisForLFunctions/HTGeometry/SpectralDeterminantGraphClosure.lean`

| Card item | Declaration |
|---|---|
| the order-`p` determinant never vanishes, and is differentiable | `schattenDet_ne_zero`, `differentiableAt_schattenDet` |
| **`(DC)`'s necessity on the spectral side, at every order** | `exists_poly_limit_of_tendsto_spectralDet` |

`exists_poly_limit_of_tendsto_spectralDet` is the card's `(DC)` necessity with `det_p` of a spectrum
in place of the finite-rank determinant: a family of determinants factored as `det_p(λ_n)·exp(P_n)`
with `deg P_n < p` and `P_n(0) = 0`, whose spectra converge in the power traces from `p` upwards
under a common geometric bound, has limit `det_p(μ)·exp(Q)` with `Q` in the same finite-dimensional
space.  So the fibre `exp J_{<p}` is exactly the ambiguity, at every order, on the spectral side --
matching `MicroSpectrumMomentAssembly.exists_multiset_moment_realization`, which is the sufficiency
direction in the same category.

Both directions of `(DC)` are therefore Lean-certified at every `p` in the spectral category, and on
finite rank.  The remaining gap is the *operator* category at `p > 2`: the identification of the
Schatten-`p` operator norm topology with convergence of the power traces, i.e. Simon's
`‖R_p(A)‖₁ ≤ c_p‖A‖_p^p`.  Mathlib has no Schatten ideals at all, so that is a construction from
scratch and is the only thing between this card and stage 3.

## Lean progress -- the Schatten scale: approximation numbers are submultiplicative

The remaining item is the operator side at `p > 2`, whose foundation is the *ideal scale* structure
of the Schatten classes.  The corpus already owned the approximation numbers, the class
`MemSchattenClass p`, the trace norm, and the additive Ky Fan inequality; the multiplicative half
was missing from both mathlib and the corpus and is now proved.

`formal/GaloisForLFunctions/HTGeometry/ApproxNumberMultiplicative.lean` (umbrella-wired, axioms =
`propext`/`Classical.choice`/`Quot.sound`)

| Card item | Declaration |
|---|---|
| **submultiplicativity**: `a_{m+n}(ST) ≤ a_m(S)·a_n(T)` | `approxNumber_comp_add_le` |
| the iterate bound `a_{k·n}(Tᵏ) ≤ a_n(T)ᵏ` | `approxNumber_pow_le` |

The proof is the classical one, and it is short once the corpus's finite-rank algebra is in place:
if `F` and `G` are near-optimal approximants of `S` and `T`, then
`ST − (FT + (S−F)G) = (S−F)(T−G)` and the subtracted operator has rank at most `m+n`, so the error
is at most `‖S−F‖·‖T−G‖`.  Only the `ε`-bookkeeping of the two infima is new.

`formal/GaloisForLFunctions/HTGeometry/SchattenPowerIdeal.lean` (umbrella-wired, axiom-clean)

| Card item | Declaration |
|---|---|
| a nonnegative summable family stays summable after `k`-fold repetition | `summable_comp_nat_div` |
| the approximation numbers of a power | `approxNumber_pow_le_div` |
| **powers move down the Schatten scale**: `T ∈ S_p ⟹ Tᵏ ∈ S_{p/k}` | `memSchattenClass_pow` |

`memSchattenClass_pow` is exactly the statement the order-`p` determinant needs of its operator:
every power at or above the Schatten exponent lands in `S_1`, i.e. is trace class, which is the
hypothesis `opSchattenDetExp_eq_schattenDetExp` carries.  The exponent bookkeeping is exact --
`(a^k)^{p/k} = a^p` -- so no constant appears, and the `k`-fold repetition of the index is handled by
fibering the partial sums over `m ↦ m/k`, each fibre having at most `k` elements.

This is the first layer of the Schatten ideal scale.  What Simon's estimate still needs on top of it
is the Hölder inequality for the `‖·‖_p` norms and the trace-norm bound on the regularized remainder
`R_p(A) = (1+A)exp(∑_{k<p}(−1)^k A^k/k) − 1`.

## Lean progress -- Hölder on the Schatten scale, and the determinant identification from class
membership alone

Three further modules (umbrella-wired, axioms = `propext`/`Classical.choice`/`Quot.sound`) turn the
submultiplicativity of the previous section into the ideal-scale inequalities, and use them to
remove the last hypothesis from the operator-side determinant identification.

`formal/GaloisForLFunctions/HTGeometry/SchattenHolder.lean`

| Card item | Declaration |
|---|---|
| **Hölder for the Schatten scale**: `S ∈ S_p`, `T ∈ S_q`, `p⁻¹+q⁻¹ = r⁻¹` ⟹ `ST ∈ S_r` | `memSchattenClass_comp` |
| **powers at or above the exponent are trace class** | `memSchattenClass_one_pow` |

The proof needs no operator theory beyond `approxNumber_comp_add_le`: `a_m(ST) ≤ a_{m/2}(S)·a_{m/2}(T)`
turns the Schatten sum into a doubled copy of a series product, and mathlib's
`NNReal.summable_mul_rpow_of_Lp_Lq` closes it.

`formal/GaloisForLFunctions/HTGeometry/SchattenPowerHilbertSchmidt.lean`

| Card item | Declaration |
|---|---|
| a power lands in Schatten 2 once twice its exponent dominates `p` | `memSchattenClass_two_pow` |
| **a balanced split is a Hilbert–Schmidt factorisation** | `exists_hilbertSchmidt_factorization_pow` |
| every power above `p` splits | `exists_hilbertSchmidt_factorization_pow_of_le` |

The corpus's operator trace is defined through a Hilbert–Schmidt factorisation, so a regularized
determinant of order `q` needs every power from `q` upwards written as a product of two
Hilbert–Schmidt operators.  Splitting `T^m` in half and moving each half down the scale does it:
`T^a ∈ S_{p/a}`, which is `S_2` as soon as `2a ≥ p`, and `memSchattenClass_two_iff_isHilbertSchmidt`
(already in the corpus) converts.  The balanced split works for every `m ≥ p + 1`.

`formal/GaloisForLFunctions/HTGeometry/SchattenClassDeterminantIdentification.lean`

| Card item | Declaration |
|---|---|
| **the operator `det_q` is the `det_q` of its spectrum, from class membership alone** | `opSchattenDet_eq_schattenDet_of_memSchattenClass`, `opSchattenDetExp_eq_schattenDetExp_of_memSchattenClass` |

This removes the factorisation hypothesis that `opSchattenDet_eq_schattenDet` was carrying: for a
compact self-adjoint operator in *any* Schatten class `S_p`, the order-`q` operator determinant
equals the order-`q` determinant of its signed greedy spectrum, at every integer order `q ≥ p + 1`.
So on the operator side the chain finite rank → spectrum → operator is now unconditional on the
Schatten scale, and the only quantitative input still missing for `(DC)` at general `p` is the
*norm* statement -- Simon's `‖R_p(A)‖₁ ≤ c_p‖A‖_p^p` -- rather than any structural one.

## Lean progress -- the Schatten norms and their quantitative Hölder inequality

`formal/GaloisForLFunctions/HTGeometry/SchattenNorm.lean` (umbrella-wired, axioms =
`propext`/`Classical.choice`/`Quot.sound`) supplies the *quantitative* half of the scale, which the
class-membership statements of the previous sections did not carry.

| Card item | Declaration |
|---|---|
| the tsum companion of the `k`-fold repetition bound | `tsum_comp_nat_div_le` |
| **the Schatten `p`-norm**: the `ℓ^p` norm of the approximation numbers | `schattenNorm`, `schattenNorm_nonneg` |
| at `p = 1` it is the corpus's trace norm | `schattenNorm_one_eq_traceNorm` |
| **Hölder in the `r`-th power form** | `tsum_rpow_approxNumber_comp_le` |
| **Hölder for the Schatten norms**: `‖ST‖_r ≤ 2^{1/r}‖S‖_p‖T‖_q` for `p⁻¹+q⁻¹=r⁻¹` | `schattenNorm_comp_le` |

The constant `2^{1/r}` is the price of the two-fold index shift in
`a_m(ST) ≤ a_{m/2}(S)·a_{m/2}(T)`; the sharp Hölder inequality has constant one, but nothing in this
card's argument needs sharpness -- Simon's `c_p` is not required to be optimal either.

With this the Schatten scale carries both its structural and its quantitative content: membership is
closed under products at the conjugate exponents, powers move down the scale, powers above the
exponent split into Hilbert–Schmidt factors, and the norms obey Hölder.  What Simon's estimate still
needs is the trace-norm bound on the regularized remainder
`R_p(A) = (1+A)exp(∑_{k<p}(−1)^k A^k/k) − 1`, whose expansion is a series of products of `p` or more
copies of `A`; each such product is trace class by `memSchattenClass_comp`, and
`schattenNorm_comp_le` is what turns that into the norm bound `c_p‖A‖_p^p`.

## Lean progress -- the trace norm of a power, with a constant linear in the exponent

`formal/GaloisForLFunctions/HTGeometry/SchattenTraceNormPower.lean` (umbrella-wired, axioms =
`propext`/`Classical.choice`/`Quot.sound`).

| Card item | Declaration |
|---|---|
| above the exponent, the `s`-energy is the `p`-energy times an operator-norm factor | `rpow_approxNumber_le`, `tsum_rpow_approxNumber_le` |
| **the trace norm of a power**: `‖Tᵏ‖₁ ≤ k·M^{k−p}·‖T‖_p^p` with `M = max(‖T‖,1)` | `traceNorm_pow_le` |

One correction to the plan recorded in the previous section is worth stating explicitly, because it
changes the route rather than just the constant.  **Iterating the Hölder inequality is the wrong way
to bound `‖Aᵏ‖₁`.**  Each application of `schattenNorm_comp_le` costs a factor `2^{1/r}`, and the
exponents `r` shrink like `p/i`, so `k` applications cost
`2^{(2+3+⋯+k)/p} = 2^{(k(k+1)/2−1)/p}` -- superexponential in `k`.  The remainder `R_p(A)` is a
*power series* in `A`, so a constant of that shape cannot be summed and the estimate would fail.

The approximation numbers give the right shape directly, with no Hölder at all: `aₙ(Aᵏ) ≤ a_{n/k}(A)ᵏ`
turns the trace norm into `k` copies of the `k`-th energy, and the `k`-th energy is the `p`-energy
times `M^{k−p}`.  The constant is `k` -- *linear* -- which a power series absorbs.

So the estimate that Simon's bound consumes is now available in a summable form:
`‖Aᵏ‖₁ ≤ k·M^{k−p}·‖A‖_p^p` for every `k ≥ p`.  What remains is the scalar side: the coefficients of
`(1+x)exp(∑_{k<p}(−1)^k x^k/k) − 1` vanish below degree `p` -- because that function is
`exp(∑_{k≥p}(−1)^{k+1}x^k/k)` -- and summing `|cₖ|·k·M^{k−p}` against them gives `c_p‖A‖_p^p`.

## Lean progress -- products of Schatten operators, structurally and quantitatively

Two further modules (umbrella-wired, axioms = `propext`/`Classical.choice`/`Quot.sound`) carry the
two-factor Hölder inequality along a list, which is the shape the telescoping identity for power
traces consumes.

`formal/GaloisForLFunctions/HTGeometry/SchattenListProduct.lean`

| Card item | Declaration |
|---|---|
| **a product of `n` Schatten-`p` operators lies in Schatten `p/n`** | `memSchattenClass_list_prod` |
| hence trace class once the list is long enough | `memSchattenClass_one_list_prod` |

`formal/GaloisForLFunctions/HTGeometry/SchattenListProductNorm.lean`

| Card item | Declaration |
|---|---|
| the accumulated Hölder constant | `schattenProdConst`, `schattenProdConst_nonneg` |
| **the norm of a product**: `‖X₁⋯Xₙ‖_{p/n} ≤ C(p,n)·∏‖Xᵢ‖_p` | `schattenNorm_list_prod_le` |

The constant `C(p,n)` accumulates a factor `2^{k/p}` at the `k`-th step, so it grows
superexponentially in `n` -- the same phenomenon recorded in the previous section.  That is
intrinsic to the approximation-number route and harmless *here*, because the list length is fixed in
every use: the telescoping identity
`Aᵏ − Bᵏ = ∑_{j<k} A^j(A−B)B^{k−1−j}` has exactly `k` factors in each term for a *fixed* `k`, and
the geometric bound in `k` that the determinant series needs is supplied separately by
`traceNorm_pow_le`, whose constant is linear.

Together with the corpus's `norm_opTrace_le_traceNorm` this gives the continuity of every power
trace in the Schatten norm: each telescoping term is a product of `k ≥ p` Schatten-`p` operators, so
it is trace class with trace norm at most `C(p,k)·‖A‖_p^j·‖A−B‖_p·‖B‖_p^{k−1−j}`, and its trace is
bounded by that.  What remains is the telescoping identity itself and the assembly.

## Lean progress -- telescoping, and the power traces controlled by the Schatten norm

`formal/GaloisForLFunctions/HTGeometry/TelescopingPowerTrace.lean` (umbrella-wired, axioms =
`propext`/`Classical.choice`/`Quot.sound`).

| Card item | Declaration |
|---|---|
| **the telescoping identity in a ring**: `aᵏ − bᵏ = ∑_{j<k} a^j(a−b)b^{k−1−j}` | `sub_pow_eq_sum_mul_sub_mul` |
| each telescoping term is a product of `k` Schatten-`p` operators, hence trace class | `memSchattenClass_one_telescope_term` |
| the Schatten-1 class is closed under finite sums | `memSchattenClass_one_sum` |
| the trace of a finite sum is bounded by the sum of the trace norms | `norm_opTrace_sum_le` |
| **the power traces are controlled by the telescoping terms** | `norm_opTrace_pow_sub_le` |

`norm_opTrace_pow_sub_le` is the estimate `(DC)`'s necessity direction needs on the operator side:
for two Schatten-`p` operators whose difference is again Schatten-`p` -- which is exactly what
convergence *in* `Hom(V, S_p)` supplies -- and any `k ≥ p`,

`‖tr(Aᵏ) − tr(Bᵏ)‖ ≤ ∑_{j<k} ‖A^j(A−B)B^{k−1−j}‖₁`,

and each summand is bounded by `C(p,k)·‖A‖_p^j·‖A−B‖_p·‖B‖_p^{k−1−j}` through
`schattenNorm_list_prod_le`.  So every power trace from `p` upwards is continuous in the Schatten
norm, which is precisely the hypothesis `tendsto_schattenDet_of_tendsto_tracePower` and
`tendsto_deriv_schattenDet_of_tendsto_tracePower` consume -- and therefore the hypothesis of
`exists_poly_limit_of_tendsto_spectralDet`, the closure statement.

The telescoping term is written as the product of the list
`replicate j A ++ (A−B) :: replicate (k−1−j) B`, whose length is exactly `k`; that is why
`memSchattenClass_one_list_prod` applies with no case analysis on whether `j` or `k−1−j` vanishes.

## Lean progress -- power traces are continuous in the Schatten norm

Two further modules (umbrella-wired, axioms = `propext`/`Classical.choice`/`Quot.sound`) close the
quantitative chain from the Schatten norm to the power traces.

`formal/GaloisForLFunctions/HTGeometry/SchattenNormMonotone.lean`

| Card item | Declaration |
|---|---|
| **the `ℓ^s ⊆ ℓ^1` norm inequality** for `0 < s ≤ 1` | `tsum_le_rpow_tsum_rpow` |
| **the trace norm is at most the Schatten-`s` norm** | `traceNorm_le_schattenNorm` |

This is the step that converts a product estimate stated at the exponent `p/n` into one for the
trace norm: normalising by the `ℓ^s` norm makes every entry at most one, and on `[0,1]` a smaller
exponent gives a larger power.

`formal/GaloisForLFunctions/HTGeometry/SchattenPowerTraceContinuity.lean`

| Card item | Declaration |
|---|---|
| **the quantitative telescoping estimate** | `traceNorm_telescope_term_le` |
| the whole difference against the Schatten norm of the difference | `norm_opTrace_pow_sub_le_mul` |
| **the power traces converge** | `tendsto_opTrace_pow_of_tendsto_schattenNorm` |

`tendsto_opTrace_pow_of_tendsto_schattenNorm` is the operator-side continuity the completion needs:
if `‖Aₙ − B‖_p → 0` with `‖Aₙ‖_p` bounded, then `tr(Aₙᵏ) → tr(Bᵏ)` for every `k ≥ p`.  Composed with
`tendsto_schattenDet_of_tendsto_tracePower` and
`tendsto_deriv_schattenDet_of_tendsto_tracePower` this gives convergence of `det_p` and of its
derivative, and hence -- through `exists_poly_limit_of_tendsto_spectralDet` -- the closure of the
determinant graph with the operators presented in the Schatten topology rather than by their
spectra.

The estimate is `‖tr(Aᵏ) − tr(Bᵏ)‖ ≤ K(p,k,C,‖B‖_p)·‖A−B‖_p` with an explicit constant: the
telescoping sum contributes `k` terms, each a product of exactly `k` Schatten-`p` factors, each
bounded by `schattenProdConst p k · ‖A‖_p^j · ‖A−B‖_p · ‖B‖_p^{k−1−j}`.
