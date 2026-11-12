# Coherence theory of reciprocity families (CRF)

- **ID:** crf
- **Stage:** 1-in-progress
- **Type:** programme card (goal loop)
- **Source:** docs/reports/review-1111/obstacles-summary.md §2.9 (also §1.6, §2.5 = B175, §3 = B184, §2.18)
- **Statement:** develop the field: B175 (signed cancellation across the rows), coherent directions
  of the sextic kernel, the reflection of a signed Gram, B184 (tower of corrections, common
  abscissa), with Lean in `formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/`.

## Goal
Answer the questions of §2.9 (README §6): Q1 = B175, Q2 coherent directions, Q3 reflection of a
pair, Q4 = B184, Q5 transport below the wall, Q6 coherence exponent of Gauss sums, Q7 cancellation
inside the mean square, Q8 function-field analogues.

## Lean modules
| Module | Content | State |
|---|---|---|
| `TheWallOfTheFrameIsAPhaseLFunction` | `H = L_A(6s−3)·E`, `E` holomorphic, within ½ of 1 on `Re s > σ > ½`; `framePremise_iff` (½<σ≤2/3): frame premise ⇔ zero-free continuation of `L_A` to `Re w > 6σ−3`; `heckeLFunction_transport(_phase)`: below the wall a zero `ρ` of `L(s,ψ)` gives a zero `6ρ−3` of the phase `L`-function. The factorization part duplicates the peer module `FamilyContinuationTheory/TheSexticGrossencharacterFactorizesTheProbeCorrection` (A139, cutoff-free); switch to importing it once its olean exists | clean; olean built |
| `TheAverageRowIsBlindToTheTarget` | row local series `= rowLocalSum(χ_π(u))` (`hasSum_localTerm_rowLocalSum`); `average_rowLocalSum`: the `μ₆`-mean kills the modes `ρ, ρ⁻¹` and the target term `−ηρ⁻¹X`; `averageRowFactor_eq`; `norm_averageRowLocalFactor_sub_one_le` (`9Q^{−198/100}` on the floor region); `exists_averageRowCorrection_cutoff`: the average row is holomorphic, within ½ of 1 in `x` on `Re x > max(51/100, 1−Re w)` | clean |
| `ShortColumnsAreIncoherent` | `tsum_phase_mul_comp_eq` (row sum of `e(⟨n,θ⟩)` = `|det B|⁻¹ Σ_m f̂(B^{−*}(m−θ))`); `tsum_norm_le_of_far` (dual sum `≤ C(μδ)^{−M}`, `M > d`); `norm_tsum_column_le` (short columns incoherent) | clean |
| `TheRowRootNumberCarriesTheMoebiusSign` | `sexticGaussPow_prime` (bridge); `rowGauss_product_prime`; `rowGauss_defect_mul`; `rowGauss_product`: `χ_c(4)g¹_c g²_c = (−1)^{|s|} c g³_c` for squarefree `c = Π_{π∈s} π` | clean |
| `ShortColumnsOfTheEisensteinLatticeAreIncoherent` | `card_mul_eq_sum_dual` (Fourier inversion with a primitive character); `traceChar_mul_eval_eq_phase` (ψ_c(hn) = e(⟨n,θ_h⟩)); `two_mul_eisNormZ_le` / `sqrt_le_norm_sub_thetaH` (`c ∤ h` ⇒ dist(θ_h, ℤ²)² ≥ 2/(3N)); `norm_tsum_eisensteinColumn_le` (mean-zero column of modulus c: row sum `O((μ√(2/(3N)))^{−M})`, sharp range `N(c) < U^{1−ε}`) | clean |
| `TheWallIsThePriceOfCompletion` | `hasSum_localTerm_uncompleted` (j = 0, l ≤ 1: `rowLocalSum` with `R = 0`); `rowLocalSum_sub_uncompleted` (completed part `∝ R`); `uncompleted_principal_factor`; `exists_uncompletedCorrection_cutoff` (no wall on `Re s > ½`) | clean |
| `TheRowRootNumberIsAnAngularTwist` | `normSq_sexticGaussPow_prime`, `normSq_sexticGaussPow_prod` (`|g^{(j)}_c|² = |c|²`, `6 ∤ j`); `rowRootNumber_eq_angularTwist` (`g̃¹ = μ(c)(c/|c|)χ̄_c(4)g̃³ conj g̃²`) | clean |
| `TheGramOfTwoRowsIsACompletedSum` | `tsum_column_eq_dual(Of)` (exact reflection of any column on `O/(c)`); `sum_pairColumn_traceChar` (mixed Gauss CRT); `gramEntry_eq_completedSum` (Q3, M1) | clean |
| `TheShortSexticGramIsDiagonal` | `sexticGaussPow_zero_prime/prod` (`g_c^{(j)}(0) = 0`); `sum_pairColumn_eq_zero` (distinct squarefree rows orthogonal on `O/(u₁u₂)`); `norm_gramEntry_le` (short Gram entries negligible) | clean |

## Paper notes (derivations, with status)

**N1 [Lean] The wall.** Principal local factor `h = E_loc/(1−R)`, `R = A Q^{3−6s}`;
`‖E_loc − 1‖ ≤ 9Q^{−e}`, `e ≤ min(6σ−2, 1+σ, 2)`. Hence Q4/Q5 first half: the frame's nonvanishing
premise at `σ ∈ (½, 2/3]` is exactly zero-freeness of `L_A` on `Re w > 6σ−3`; below it the frame
is a transport law.

**N2 [D] The wall is common to all rows and bites only at the residue.** In the complete local
identity (`hasSum_localTerm`, external Lemma 7.1) every row `u` and every layer `j` has the factor
`(1 − R)⁻¹`, `R = κ⁶Q⁴X⁶V`, independent of `u` and `j`: it comes from the joint family
`(l, m) ↦ (l + 2, m + 1)` (a sixth power `π⁶` in the cube part of the completed theta index and in
the frequency). In three variables it is `L(6x+6z−4, ψ₆η⁶)`. On the floor contours
(`Re x ≥ 51/100`, `Re z ≥ 17/50`) its argument has real part `≥ 1.1`: harmless. At the signal
(residue `z = 1/6`) its argument is `6x − 3`: the wall. The remaining principal-row integral after
extracting the residue sits at `Re z < 1/6`, where the argument is further left. So the wall is
intrinsic to extracting the signal from the completed probe; removing the joint sixth power by a
coprimality condition moves it to the direct side (D3(iii) of the summary).

**N3 [D] The floor bin is a first moment of ratios.** External (7.5), (7.13): row `u` contributes
`ξ(u) q_u^{−z} ζ(6z) L(w,χ_•(u)) H_{η,u}/L(x, ηχ_•(u))`; `ξ` a fixed periodic phase mod `b*`.
The floor bin is `Σ_{u∈B₀}` of these on the floor contours. Expanding `L(w,·)` (plain columns)
and `1/L(x,η·)` (Möbius columns) gives the kernel `χ_•(u)(N) ≈ (u/N)_6` (reciprocity): rows `u`,
columns `N`, amplitudes `ξ(u) q_u^{−z} H_{η,u}` (`H_{η,u}` itself depends on `u` through
`ρ_p = χ_p(u)`). Over the full family the principal columns (`N` a sixth power, times the
classes where `ξ·(·/N)_6` is principal) are coherent: a main term of size `U` with an explicit
Euler product (the diagonal of the ratio). **B175 has to be posed after this principal part is
evaluated**; the trivial floor bound `R = 1` is sharp for the principal part (H2).

**N4 [D] The selection obstruction.** `B₀` is selected by zero locations, so it carries no
arithmetic structure; a signed estimate must pass to the full family. `Σ_{B₀} = Σ_all − Σ_comp`
with `|comp| ≤ U^{R(δ)}`, `δ` just above the floor (a power saving `U^{1−cδ}`), but the floor
values `1/L(x, ηχ_u)` are not defined (or not bounded) for the rows of the complement; replacing
them by Dirichlet polynomials valid on `B₀` is the polynomial-completion step, and its exponent
model is FG's `le_max_approxRem_approxComplete` (no gain without cancellation in the completed
row sum). Open: the completion with exact character-sum cancellation in `u` for each column.

**N5 [C]/[A] Coherence exponents.** Normalized Gauss sums of order `n₀` summed over the modulus
have the bias `X^{½+1/n₀}` (Kubota–Patterson residue; `5/6` for cubic). Observations: the
phase transition of FG's floor-bin curve is at `R_crit(n) = ½ + 1/n` (`2/3` at `n = 6`, the
sextic residue exponent), and the free floor `(n−2)/(n−1)` is attained at `R₀ = 5/6` (the cubic
residue exponent). Not yet a theorem: the floor-bin amplitudes are `ξ(u)`-phases, not Gauss sums
(N3); the Gauss sums sit inside `H_{η,u}` and the Poisson coefficients.

**N6 [D] Exponent bootstrap (model only).** If the floor-bin row exponent equals the current
half-plane, `R₀ = β`, FG's symmetric curve gives `σ₀(β) = ½ + (36β−14)/(12(6β−1))` at `n = 6`;
the fixed points of `σ₀(β) = β` are `5/6` (attracting, slope `1/4`) and `1/3`. Status: a model,
not a mechanism of the probe — the rows carry no Möbius factor (N3). Kept as the reason why
`5/6` is self-consistent, not as a route.

**N7 [Lean] The average row is target-free.** The principal component of the row family (mean
over `ρ ∈ μ₆`) has local factor `ζ(6z)ζ(6w)L(6x+6z−4)·G`, `G − 1 = O(Q^{−198/100})` on the floor
region; the target reciprocal lives in the mode `ρ⁻¹` (`−(1−R)⁻¹ηX`), read only on the principal
row. So the saturation of the floor bin along the principal twists (`R = 1` sharp) is harmless:
its contribution to the high side is a residue at `z = 1` of size `Z^{Re x}` with `x` on the floor
contour (paper).

**N8 [D] B175 as a first moment, and a resolution scheme.** Floor bin = Σ over rows of the mode
expansion `Σ_N c_N χ_N(u)`. (1) mode 0 = average row: target-free (N7). (2) short columns
(conductor `< U^{1−ε}`): Poisson in `u` makes the full-family sum `O((N/U)^A)`. (3) the complement
of `B₀` is controlled by moments of the zero-detector polynomials (the same mechanism as the row
counts of B174), so the selection by zeros is not an obstruction in itself. (4) long columns come
from the dual side of the approximate functional equation of `L(w, χ_•(u))`, whose amplitude is the
root number of the row character, a normalized sextic Gauss sum: their coherence is the sextic
Kubota residue `U^{½+1/6}` [C] — the binding part. (5) the approximation error of `1/L` on the
buffered floor. Conjecture: after (1)–(3), `R₀ = ½ + 1/6 = 2/3 = R_crit(6)` for the floor bin.

**N9 [Lean]+[C] Row root numbers.** `rowGauss_product` with the cube identity
(`compositeCubicGauss_cube`: `g̃₃³ = μ(c)·c/|c|`) gives `g̃₆(c) = χ̄_c(4)g̃₂(c)g̃₃(c)²
= μ(c)(c/|c|)·conj(g̃₃(c))·(finite phase)`. The long columns of the floor bin are a Möbius-signed
family of conjugate cubic Gauss sums twisted by an angular character of infinity type one; by
equidistribution of arguments of cubic Gauss sums (Heath-Brown–Patterson [C]) there is no
metaplectic main term: the long columns are expected incoherent. Their bound needs Type I (theta at
nonpolar points) and Type II (cubic large sieve over ℤ[ω], not in corpus).

**N10 [C]/[D] B175 with classical tools; parity of the order.** Long columns via Heath-Brown's
decomposition: Type II by the cubic large sieve `(Q + N + (QN)^{2/3})`, Type I by the cubic theta
function: `U^{5/6+ε}` (Heath-Brown's exponent for cubic Gauss sums over primes). FG's curve:
`R₀ = 5/6 ↦ θ = (n−2)/(n−1)`, half-plane `5/6` = the free floor. So classical tools take the floor
bin from `13/15` to `5/6` and stop; `s > 0` on the floor bin ⇔ improving `(QN)^{2/3}` (the cubic
large sieve conjecture `Q + N`): below `5/6` B175 is a named problem (T8). Q7: below √(column
length) every family cancels completely (Module 5); above, order two is sharp (`sieveNorm_sharp`),
odd orders open; the sign law needs odd order: sign-carrying ⇔ sieve not known sharp.

## Conjecture ledger
- C1 (PROVED, Lean): wall of the frame = phase `L`-function; frame premise ⇔ zero-free `L_A`.
- C2 (open): tower — the probe's phases are `ψ₆η⁶`, `ψ₆(π) = (π̄/|π|)⁶` of infinite order; the
  correction map `ψ₆^kη ↦ ψ₆^{6k+1}η⁶` has no periodic orbit.
- C3 (open): B175 after the principal part (N3, N7) — is the remainder of row exponent `< 1`?
  Scheme N8; binding part = root-number (Gauss-sum) coherence.
- C4 (PROVED, Lean): the average row is target-free (N7).
- C5 (PROVED, Lean): short columns are incoherent (Poisson in the rows).
- C6 (PROVED, Lean): the Möbius sign of a squarefree row modulus in its Gauss sums (`rowGauss_product`).
- C7 (open, [C]-supported): the long columns have no coherent main term (infinity type one twist).
- C8 (PROVED, Lean): sharp short-column incoherence over ℤ[ω] (`norm_tsum_eisensteinColumn_le`).
- C9 ([D]/[C]): classical tools give R₀ = 5/6 for the floor bin; below needs the cubic large sieve conjecture.
- C13 (PROVED, Lean): Q7 — the short sextic Gram is diagonal (`norm_gramEntry_le`).
- C12 (PROVED, Lean): Q3 — the Gram entry of two rows is a completed sum of products of their Gauss sums (`gramEntry_eq_completedSum`).
- C11 (PROVED, Lean): N9's root-number form is native (`rowRootNumber_eq_angularTwist`).
- C10 (PROVED, Lean): the wall is the price of completion; completion is needed for the reflection [C] (external Prop 5.1): the four source conditions exclude each other within the cubic probe.

## Log
- 2026-11-11 — created; README first draft; modules 1–4 clean; README v2 (pillars, §7 floor bin as first moment).
