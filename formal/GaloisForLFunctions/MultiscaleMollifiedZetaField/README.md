# Multiscale Analysis of the Mollified Zeta Field (MZF)

Namespace `GaloisForLFunctions.MultiscaleMollifiedZetaField`; umbrella `MultiscaleMollifiedZetaField.lean`.
Every theorem is unconditional unless it is an equivalence with RH, an implication from a named law, or a statement about
a named model.

## 1. Motivation

Route WD reads the zeros of `ζ` through the mollified field `F = ζM`, `M` a Dirichlet polynomial. Its results all come from
one method, second moment plus Jensen, and that method has three proved limits: polynomial length has a moment floor
`1 + 1/(8+6θ)` (APR); moments do not determine the log-mean (Π19); occupied-window bounds lose a factor `log V` against
the target `D_win` (CDG).

Two branches remain, and they fail for different reasons.

- **The density branch** (`D_win`, clustering) is sub-RH. A unit window holds about `log V` zeros, so counting them one at a
  time loses `log V`.
- **The RH branch** asks for a bound on `∫_1^T|ζM_{T^θ}(½+it)|²dt` with `T`-exponent independent of `θ`. Its exact θ-slope
  is `2·zetaZeroWidth`, so closing the slope to `0` is RH (card `WD-LONG-MOEBIUS-SLOPE-LAW`). This is the **residual**.

Probabilistic number theory has a known way past union bounds: `log|ζ(½+it)|` behaves as a log-correlated field with primes
in dyadic scales as branching steps, and barrier arguments control maxima of such fields (Fyodorov–Hiary–Keating,
Arguin–Bourgade–Radziwiłł, Harper). MZF builds that language for the mollified field in this corpus and asks exactly what it
can and cannot reach on each branch.

## 2. Objects

| Object | Meaning |
|---|---|
| Mollified error | `E_M = ζM − 1`, `M = Σ_{n≤N} b_n n^{−s}` |
| Prefix cancellation | the coefficients of `ζM` vanish on `2 ≤ n ≤ y` |
| Line Poisson weight | `P_ρ(u) = δ/(π(δ² + (u−γ)²))`, the harmonic measure of `Re z > ½` seen from `ρ = ½+δ+iγ` |
| Exponent field | `e_X(u) = log|E_X(½+iu)| / log X`, `E_X = ζM_X − 1` |
| Prime blocks | `P_k(t) = Σ_{e^{e^{k−1}} < p ≤ e^{e^k}} Re p^{−σ−it}`, the branching steps |
| Prime walk | `S_k(t) = Σ_{j≤k} P_j(t)` |
| Barrier event | `S_k` stays under a prescribed curve for all `k` in a scale range |
| Length regimes | below the window `X ≤ T^{1−ε}`: primes behave independently; above the window `X ≥ T^{1+ε}`: the Selberg-integral regime; compact window `X → ∞` at fixed height |
| Near-line receivers | `D_win`, `D_zero`, clustering, the shifted-defect detector (CDG) |

## 3. Language

- **Floor, cap.** A floor is a lower bound for a functional of `E` forced by a zero; a cap is an upper bound forced by a zero-free
  region.
- **`L⁰` statement.** A statement about the size of `E` on most points of a window, with no moment. It is the weakest form
  of a size statement and survives restriction to any event.
- **Slope.** The rate `lim log(functional)/log X` in the length.
- **Hole.** A point where `|E| ≥ 1`. Every zero of `F` lies in a hole; a hole need not contain a zero.
- **Last scale.** The primes near `T^{Θ(1)}`, where products exceed `T` and mean values stop.
- **Bohr lift.** The Dirichlet polynomial read as a function on the torus of primes; independence means Haar measure on it.

## 4. Mechanisms

**A. Half-plane Jensen at a zero.** On `Re z ≥ ½`, an entire function of polynomial growth satisfies
`log|F(ρ)| ≤ ∫P_ρ log|F(½+iu)|du`. Apply it to `y^{z−½}(z−1)E_M(z)`: the coefficients of `E_M` start after `y`, so the factor
`y^{z−½}` costs nothing as `Re z → ∞`, and it gains `δ log y` at `ρ`. At a zero `E_M(ρ) = −1`. So a zero forces a floor on the
logarithmic mean of `|E_M|`, not only on its mean square.

**B. Floor against cap.** A zero-free region caps `log|E_X|` pointwise by `(width+ε) log X`. At a zero of nearly maximal depth the
Poisson mean reaches that cap, and a function under a cap whose mean reaches the cap is close to the cap in measure.

**C. Barrier as truncation.** On a barrier event `exp(±P_k)` equals a short Taylor polynomial up to a small relative error, so a
mollifier of admissible length imitates the exact Euler factor there.

**D. Bohr transfer.** Below the window, moments of a Dirichlet polynomial in `p^{−it}` equal the Steinhaus expectation up to the
off-diagonal, so barrier statements transfer to independent random walks.

## 5. Questions

1. **The central question.** Does a barrier on partial prime sums give `P(unit window of [V,2V] holds a zero of depth ≥ A/log V) ≤ ε(A)`
   with `ε(A) → 0` independent of `V`?
2. **The residual.** What is the weakest statement about `E_X` equivalent to closing the θ-slope, and does the multiscale method
   reach any part of it?
3. **Barrier to detector.** Can a barrier event be turned into the detector shape of `D_win`, given that size-only detectors fail at
   scale `V/log V` (Fejér–Dirichlet)?
4. **The last scale.** What exactly stops at the last scale, and what replaces the mean-value theorem there (B28)?
5. **Negative moments.** How do `Σ|ζ′(ρ)|^{−2}` and the residues `N^{ρ−s}/(ρζ′(ρ))` enter, and what do they link to in ADO?

## 6. Tools

**To develop.** Selberg's central limit theorem for `ζ` with the dyadic prime decomposition; twisted second moments against products
of short Euler pieces, within known length; barrier probability estimates for the prime-sum walk; half-plane Jensen with
prefix amplification; the exponent-rigidity calculus.

**Used from the corpus.** Boundary Jensen on the disc (`circleIntegrable_and_sum_log_add_le_circleAverage`), Littlewood's Mertens bound
(`mobiusMertens_subpower_of_zeroFree`), the Möbius field (`mobField`), the sharp mean value, Soundararajan moments for prime
polynomials, the Steinhaus model and its barrier modules, Barban–Vehov two-length mean squares, the Selberg explicit formula for
`ζ′/ζ`, the near-line receivers (CDG), the length laws (APR).

## 7. Traps

| Trap | Truth |
|---|---|
| A barrier gives `D_win` because it gives maxima | That success is an analogy; a zero is not a large value of the field |
| Size detection reaches `V/log V` | The Fejér–Dirichlet polynomial occupies `≥ V/12` windows with every `L^p` and `log⁺` defect of that size |
| Restriction to a good event lowers the slope | To be settled by the rigidity law; the slope is a statement about almost every point |
| Primes are independent at every length | Only below the window; at bounded height a prime block is nearly one rotating phase |
| Proportion results reach `D_win` | The root model has proportion one and every exponential depth rate and fails `D_win` |
| Formalizing the slope law closes the residual | Closing the slope is RH |

## 8. Context

| Programme | Interface |
|---|---|
| CDG (`ConjugateDiagonalGeometry/NearLineLogMean`) | receivers `D_win`, `D_zero`, detector sharpness, root model, the eight clustering forms |
| APR (`ArithmeticProduction`) | necessary-length laws, zero floors, Selberg-integral dictionary, filters and mimic battery |
| RHTower | Steinhaus model and Euler barrier, Selberg near-line density, mean values, explicit formula |
| ADO (`ArithmeticDiscreteness`) | small values of `ζ′`, repulsion; link through negative moments |
| ZCG, FFP | sign-free readers of the same zeros; heat and Jensen-polynomial coordinates |

MZF serves WD's density branch as a programme and its RH branch by exact limits. The sign routes (CHT, SWC, FADF) do not enter.

## 9. Success and contribution criteria

**The programme succeeds if** it answers the central question, in either direction, in Lean; or if it proves `D_win`, or a theorem saying
which class of inputs cannot reach it.

**A contribution must:**
1. be unconditional, with every analytic input proved; an implication from a named law must state that law and whether it is an
   equivalence with RH;
2. state the outcome on the mimic battery: impure factor, root model, Fejér–Dirichlet detector, Liouville twin;
3. name its length regime and compare it with the necessary-length laws;
4. for a limit theorem, name the model at which the tool stops and extract the sharp positive statement;
5. improve a pillar, answer a question of section 5, or add a tool used by another module.
