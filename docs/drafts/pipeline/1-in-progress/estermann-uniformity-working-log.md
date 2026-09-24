# Estermann lane — working log

Route-level record for the twisted divisor sum. Object-level facts extracted from this work are
MUST-382 / CANNOT-383 / CANNOT-384 in `universal-law-field/STATUS.md`; nothing else from here
belongs there.

## Built (all axiom-clean, wired into `GaloisForLFunctions.RHTower`)

| module | content |
|---|---|
| `EstermannMeanZeroTwist` | main term `(γ − log x − 2 log q)/(qx)` is independent of the twist; `exists_bound_norm_estermann_meanZero`, `exists_bound_norm_estermann_character` |
| `EstermannProgressionOrthogonality` | `summable_estermannSmoothedTerm`; `sum_twist_eq_progression` : `∑_{a mod q} e(−ab/q) S_a = q ∑_{N≡b(q)} d(N)e^{−Nx}`, exact, every modulus |
| `EstermannPrimeProgression` | `exists_bound_norm_estermann_weighted` (main term retained); `estermannSmoothedSum_zero`; `sum_zmod_eq_add_sum_units`; `exists_bound_norm_estermann_prime_progression` |
| `EstermannScaledTwist` | `stdAddChar_scale`, `estermannCoeff_scale`, `estermannSmoothedSum_scale` : `S_{q}(d·m) = S_{q/d}(m)` |
| `EstermannGeneralProgression` | `exists_reducedMain`; `exists_bound_norm_estermann_general_progression` |
| `EstermannRightEdgeExplicit` | `divisorSquareMass`; `norm_estermannZeta_le_divisorSquareMass` (`Re s ≥ 2`, modulus-free) |
| `EstermannLeftEdgeExplicit` | `norm_estermannZeta_left_edge_le` : `≤ K q³ e^{π|t|}` |
| `EstermannLeftEdgePolynomial` | `norm_estermannZeta_left_edge_poly_le` : `≤ K q³|t|³`, `|t| ≥ 1` |
| `EstermannConvexityExplicit` | `norm_estermannZeta_left_edge_uniform_le`; `modulusNormalizer`; `norm_estermannPLTest_edge`, `norm_estermannPLTest_strip`; `norm_estermannZeta_critical_line_le` : `≤ C q^{3/2}(1+|t|)³`, every `t` |
| `EstermannSmoothedErrorExplicit` | `estermannGammaWeight`; `norm_estermannMellinIntegrand_one_le`; `norm_estermann_smoothed_error_le` : `≤ C q^{3/2} x^{−1/2}` |
| `EstermannProgressionUniform` | `reducedModulus`; `norm_estermannSmoothedSum_sub_reducedMain_le`; `norm_progression_sub_main_le` : `≤ C q^{5/2} x^{−1/2}`, every modulus and residue |

## The chain

1. Main term twist-independent (character-sum collapse `∑_{c mod q} expZeta(c/q,s) = q^{1−s}ζ(s)`,
   giving `D = q^{1−2s}ζ² + q^{−s}R_a` with an `a`-free double pole), so mean-zero unit weights
   annihilate it.
2. Additive orthogonality turns the twists into the progression `N ≡ b (q)`.
3. `gcd(a,q)` sends every residue twist to a unit twist of `q/gcd`, carrying that modulus's main
   term; the prime case is the instance `c_q(b) = −1`.
4. Right edge `q⁰` (Dirichlet series, unimodular twist); left edge `q³` (functional equation, with
   the explicit `‖Γ(2+it)‖ ≤ √(2π|t|/(1−e^{−2}))·3|t|·e^{−π|t|/2}` cancelling the cosine growth).
5. Normalising by `q^{s−2}` (modulus `q^{σ−2}`, so `1` and `q^{−3}` on the two edges) makes both
   edge constants `q`-free; `‖s+2‖ ≥ (1+|t|)/2` absorbs the height. Phragmén–Lindelöf uses only the
   edge constants, so the propagated bound has no modulus in it; unwinding restores `q^{2−σ}`.
   On the critical line `‖s−1‖² = 1/4 + t²` exactly, and `(1+|t|)² ≤ 8(1/4+t²)`, so no height
   restriction is needed.
6. The error integral meets that with `‖Γ(1/2+iv)‖ ≤ √(2π)e^{−π|v|/2}`; the product is integrable
   with an absolute integral and the `x`-dependence is `‖x^{−(1/2+iv)}‖ = x^{−1/2}`.
7. `q' ∣ q` gives one constant for all twists; the `q`-fold average costs `card (ZMod q) = q`.

## Open core

Not more uniformity — see CANNOT-384. The modulus sum needs cancellation between moduli
(Kloosterman / spectral shifted-convolution input). Per CANNOT-371 the lane bounds the proportion
of zeros on the critical line, not RH.

## Modulus aspect: the Kloosterman mode decomposition

`EK-1` (inverse twist, `EstermannKloostermanTwist`). Pairing the family against `e(a⁻¹b/q)` rather
than `e(ab/q)` makes each coefficient a complete Kloosterman sum:
`∑_{a ∈ (ZMod q)ˣ} e(a⁻¹b/q) D(s,a/q) = ∑_N d(N) S(N,b;q) N^{−s}` for `Re s > 1`.
The ordinary twist `e(ab/q)` is diagonal in the multiplicative characters and gives
`τ(χ)L(s,χ̄)²` component by component, which is a restatement of GRH; the inverse twist is the only
pairing of the family that is not diagonal, because inversion is not a group homomorphism.

`EK-2` (Weil saving, `EstermannKloostermanSaving`). For an odd prime modulus and `b ≠ 0` every
first frequency obeys `|S(m,b;p)| ≤ 2√p`: for `m` a unit the sum is the Weil normalisation
`∑_{x≠0} ψ(x + mb/x)`, and for `m = 0` it collapses to the Ramanujan value `−1`. Hence
`‖∑_{a} e(a⁻¹b/p) D(s,a/p)‖ ≤ 2√p ∑_N d(N)N^{−σ}` against the trivial `(p−1)∑_N d(N)N^{−σ}`.
A twist average of `p−1` functions each of size `≍ 1` is of size `≍ √p`: the modulus aspect of the
family cancels, and the saving is exactly the square root of the number of terms. This is the first
unconditional `q`-aspect saving for the family.

`EK-3` (what the mixing is). For prime `q`, expanding both additive characters in multiplicative
ones gives `S(m,n;q) = (q−1)^{−1} ∑_χ χ̄(mn) τ(χ)²`. Weil's bound is therefore exactly square-root
cancellation in the character sum of **squared Gauss sums**, i.e. of the root numbers
`ω_χ = τ(χ)²/q` of the Dirichlet L-functions mod `q`. Equivalently: in the additive Fourier basis
the inversion involution `a ↦ a⁻¹` has matrix `q^{−1}S(m,−n;q)`, so Weil says this involution is
flat at the scale `2q^{−1/2}` — the largest delocalisation a unitary `q × q` matrix can have. The
Estermann functional equation, which acts on the family through that inversion, is at level `q` a
maximally mixing operator; at level one it degenerates to a scalar, which is why the level-one
symmetry carries no information about zeros.

`EK-4` (where ζ sits, and the obstruction). The polar decomposition
`D(s,a/q) = q^{1−2s}ζ(s)² + q^{−s}R_a(s)` holds for every unit `a` and every `s ≠ 1`, so the whole
ζ-content of the family is one twist-independent term, and any weighted average over the reduced
residues carries `ζ(s)²` with coefficient `q^{1−2s}` times the **total weight**. For the inverse
twist at a prime modulus that total is the Ramanujan value `−1`, so every mode `b ≠ 0` carries
exactly `−q^{1−2s}ζ(s)²` and the mode `b = 0` carries `φ(q)q^{1−2s}ζ(s)²`. The modulus exponent of
that content is `1−2σ`, below `1/2` throughout `σ > 1/4` and exactly `0` on the critical line, while
Weil's bound for a nonzero mode has exponent `1/2`. **The ζ-content of a mode therefore lies a
factor `q^{2σ−1/2}` — exactly `√q` on the critical line — below the accuracy that square-root
cancellation certifies, so mixing within one modulus cannot constrain ζ.** The only weights that
keep ζ at the size of the bound are those with total of order `q`, i.e. the essentially constant
ones, and for those the coefficients are Ramanujan sums, which provably do not cancel.

`EK-5` (across moduli). The zero mode is `∑_N d(N)c_q(N)N^{−s}`, and Ramanujan's generating
function `∑_q c_q(N)q^{−w} = σ_{1−w}(N)/ζ(w)` makes the zero mode summed over moduli a `1/ζ`
object whose continuation past `Re w = 1` is RH itself. The nonzero modes summed over moduli are
the Kloosterman-sum Dirichlet series, whose abscissa Weil's bound moves from `2` to `3/2` and whose
poles are the exceptional eigenvalues of the hyperbolic Laplacian. With CANNOT-384 this locates the
remaining content exactly: RH is the continuation of the zero mode across moduli, and Weil settles
everything else within a modulus.

`EK-6` (the functional equation exchanges the two twists). Applying the Estermann functional
equation term by term to the **additive** twist produces the **inverse** twist, because the
functional equation carries the inversion `a ↦ ā`:
`∑_a e(ab/q)D(1−s,a/q) = A(s)(∑_a e(a⁻¹b/q)D(s,a/q) + cos(πs)∑_a e(−a⁻¹b/q)D(s,a/q))`,
`A(s) = 2q^{2s−1}(2π)^{−2s}Γ(s)²`. The two averages have opposite arithmetic: the additive twist is
the divisor function in an arithmetic progression (for prime `q`,
`∑_a e(ab/q)D(s,a/q) = q∑_{N ≡ −b (q)} d(N)N^{−s} − ζ(s)²`) and has no cancellation over the
residues, while the inverse twist has Kloosterman coefficients and square-root cancellation. The
functional equation transports the cancellation across the critical line.

`EK-7` (the saving reaches the progression). Combining EK-6 with EK-2 at `Re s = 2` gives an
unconditional left edge for the additive twist with the Weil saving built in:
`‖∑_a e(ab/p)D(−1+it,a/p)‖ ≤ 8(2π)^{−4}(∑_N d(N)N^{−2}) p³√p e^{π|t|}`,
against `p³φ(p)` from the trivial per-term estimate. Interpolating between this left edge
(exponent `7/2`) and the unchanged right edge (exponent `1`) puts the critical-line exponent at
`9/4` in place of the convexity value `5/2`: the divisor function in a progression to a prime
modulus inherits a `q^{1/4}` saving from Weil's theorem. This is below the `θ < −1/2` that
CANNOT-384 requires, so the no-go stands; it is the first place in this lane where modulus-aspect
cancellation reaches the progression at all.
