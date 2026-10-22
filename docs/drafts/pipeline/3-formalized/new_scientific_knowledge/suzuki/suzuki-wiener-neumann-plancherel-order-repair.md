# Uniform Wiener domination repairs the \(\ell^1\)--Plancherel order in Suzuki's global carrier

- **ID:** `suzuki-wiener-neumann-plancherel-order-repair`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT RIGGING REPAIR / VECTOR-VALUED FOURIER NO-GO AND SOURCE-SPECIFIC SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Corrects:** `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-wiener-cutoff-closed-graph-relation.md`
- **Literature boundary:** Kwapień's Fourier-type-\(2\) characterization; scalar Plancherel;
  Wiener--Neumann inversion.

## 1. The hidden order error

The global carrier construction first proves

```text
chat in L2_frequency(ell1_valuation).                    (1)
```

It then treated inverse Fourier transform as if it implied

```text
c in L2_position(ell1_valuation).                        (2)
```

This implication is false for general \(\ell^1\)-valued functions. Plancherel extends
isometrically to Hilbert-valued \(L^2\), not to \(\ell^1\)-valued \(L^2\). Kwapień's theorem
places this inside the general fact that Fourier type \(2\) characterizes Hilbertizable Banach
spaces.

The Suzuki carrier nevertheless survives for a source-specific reason absent from `(1)`: after
widening the high-pass margin, every valuation coefficient of the Wiener inverse is dominated by
one fixed summable geometric kernel. This proves the stronger mixed norm

```text
chat in ell1_valuation(L2_frequency),                    (3)
```

for which scalar coordinatewise Plancherel is legal. It yields

```text
c in ell1_valuation(L2_position)
  subset L2_position(ell1_valuation)
  subset L2_position(ell2_valuation).                    (4)
```

Thus the claimed physical rigging is correct only after the uniform-domination repair below.

## 2. Explicit counterexample to the general order swap

Choose a nonzero scalar Schwartz function \(\phi\) whose Fourier transform is supported in an
interval of length less than one. Choose \(R\) larger than that length and a sequence

```text
(a_n) in ell2(N) \ ell1(N).                              (5)
```

Define

```text
chat_n(xi)=a_n phihat(xi-nR).                            (6)
```

The frequency supports are disjoint. Hence at every \(\xi\) at most one coordinate is nonzero and

```text
||chat||_(L2_xi(ell1_n))^2
 =sum_n |a_n|^2 ||phihat||_2^2<infinity.                 (7)
```

Scalar inverse Fourier transform gives

```text
c_n(x)=a_n exp(i nR x)phi(x).                            (8)
```

Therefore

```text
sum_n |c_n(x)|=|phi(x)|sum_n|a_n|=infinity              (9)
```

wherever \(\phi(x)\ne0\). Thus `(1)` does not imply `(2)`. `QED`

This is an explicit obstruction, not merely an appeal to Banach-space theory.

## 3. Uniform coefficient domination theorem

Let \(G\) be a countable discrete group and let \(\ell^1(G)\) be its convolution algebra. Suppose

```text
h_xi=L(xi)delta_0+q(xi)delta_0+t,                        (10)
```

where

```text
|q(xi)|<=C,
t in ell1(G),
M=||t||_1.                                               (11)
```

Choose the high-pass support so that

```text
L(xi)>=L_0>2(C+M).                                      (12)
```

Put

```text
r_xi=[q(xi)delta_0+t]/L(xi),
r_* =[C delta_0+|t|]/L_0.                               (13)
```

Here \(|t|\) is the coefficientwise absolute-value measure. Then

```text
||r_*||_1=(C+M)/L_0<1/2,                                (14)
```

and coefficientwise

```text
|r_xi^(star k)(nu)|<=r_*^(star k)(nu).                  (15)
```

The Neumann inverse

```text
h_xi^(-1)
 =L(xi)^(-1)sum_(k>=0)(-r_xi)^(star k)                  (16)
```

therefore has coefficients bounded by the fixed kernel

```text
K(nu)
 =L_0^(-1)sum_(k>=0)r_*^(star k)(nu),                   (17)

K in ell1(G),
||K||_1<=1/[L_0-(C+M)].                                 (18)
```

Indeed `(15)` follows by induction from

```text
|alpha star beta|<=|alpha| star |beta|
```

for discrete convolution. Summing `(15)` proves `(17)`--`(18). `QED`

## 4. Correct mixed norm for the literal two-root carrier

Let \(B_-,B_+\in L^2(\mathbb R)\) be the two exterior Hardy amplitudes and define

```text
chat(xi)
 =h_xi^(-1) star
   [exp(+iaxi)B_-(xi)e_-+exp(-iaxi)B_+(xi)e_+].         (19)
```

The two root phases have modulus one. By `(17)`,

```text
|chat_nu(xi)|
 <=K_-(nu)|B_-(xi)|+K_+(nu)|B_+(xi)|,                  (20)
```

where each translated root kernel has the same \(\ell^1\) norm as \(K\). Therefore

```text
sum_nu ||chat_nu||_(L2_xi)
 <=||K||_1[||B_-||_2+||B_+||_2]
 <infinity.                                             (21)
```

This is `(3)`.

Apply scalar Plancherel to every coordinate:

```text
sum_nu ||c_nu||_(L2_x)
 =sum_nu ||chat_nu||_(L2_xi)<infinity.                  (22)
```

Minkowski gives

```text
||c||_(L2_x(ell1_nu))
 =||sum_nu |c_nu(x)||_(L2_x)
 <=sum_nu||c_nu||_2.                                    (23)
```

The pointwise inequality \(\|z\|_2\le\|z\|_1\) then gives the Hilbert carrier inclusion in `(4)`.
Absolute evaluation is now a bounded map

```text
ell1_nu(L2_x) -> L2_x                                   (24)
```

and reconstructs the high-frequency physical mode in position space, not only frequencywise.

## 5. Widening the cutoff loses no source information

The previous carrier chose a high-pass where merely

```text
L(xi)>C+M.
```

Replace it by a smooth high-pass supported in `(12)`. The removed annulus is compact in frequency.
It joins the existing low port

```text
u_low=(1-chi)(D)u.
```

Every derivative of this enlarged low port is bounded and its inverse Fourier transform is entire
of finite exponential type. Hence it remains Gamma-subcritical in every physical boundary chart.
No zero, divisor, or raw Evans datum is divided out; the low port is retained exactly.

Thus uniform margin `(12)` is a legal representation change, not a simplification.

## 6. Consequence for the cutoff graph relation

The repaired carrier has

```text
c in ell1_nu(L2_x) intersect L2_x(ell2_nu).             (25)
```

Any scalar \(L^2\)-bounded componentwise operator \(A\) satisfies

```text
sum_nu||A c_nu||_2
 <=||A|| sum_nu||c_nu||_2.                              (26)
```

Therefore the componentwise physical cutoff, the ordinary Carleman cross block, the logistic
cross block, and bounded prime-coordinate operations preserve the legal \(\ell^1\)-evaluation
relation whenever they are bounded in scalar \(L^2\).

This does not prove weighted Gamma decay. It removes the Fourier-order gap that would otherwise
make the global paired-Wiener strategy ill-typed.

## 7. Exact corrected frontier

```text
general L2_xi(ell1) Plancherel:
  false;                                                 [FALSIFIED]

literal high carrier with only pointwise Wiener norm:
  insufficient for physical ell1 evaluation;            [CORRECTED]

uniform-margin Neumann carrier:
  ell1_nu(L2_xi)
  -> ell1_nu(L2_x)
  -> legal physical evaluation.                         [PAPER-PROVED]       (27)
```

The remaining global route is no longer a norm-order question. It is:

```text
repaired global self-adjoint Wiener relation
+ paired interior/exterior Carleman normal form
+ zero physical traces
 -> weighted root derivative sigma>1/2.                 [OPEN]               (28)
```

## 8. Hostile and novelty audit

1. **General failure is known.** Non-Hilbert vector-valued Plancherel failure is literature, not
   new.
2. **No pointwise-evaluation shortcut.** The proof establishes the stronger
   \(\ell^1(L^2)\) norm before evaluation.
3. **No sup/sum swap.** Fixed coefficient majorant \(K\) is constructed explicitly.
4. **No cutoff loss.** Removed frequencies remain in the exact low port.
5. **Source-specific novelty boundary.** Candidate-new content is uniform domination
   `(13)`--`(21)` for Suzuki's literal valuation-Wiener inverse and its repair of the physical
   carrier relation.
6. **No RH claim.** Weighted paired return and raw Evans positivity remain.

## 9. Lean target

Faithful formalization requires discrete convolution absolute-value domination, geometric
\(\ell^1\) resolvent, mixed-norm Minkowski, and coordinatewise Plancherel. The current formal tree
has finite convolution and coefficient carriers but not the full Bochner/mixed-norm stack.
Formalizing only the scalar geometric series would not certify `(4)`.

## Gates

- [x] give explicit counterexample to \(L^2(\ell^1)\) Plancherel
- [x] construct fixed coefficientwise Neumann majorant
- [x] prove \(\ell^1_\nu(L^2_\xi)\) bound for literal carrier
- [x] transfer by scalar Plancherel
- [x] prove physical \(L^2_x(\ell^1)\) and legal evaluation
- [x] preserve exact low-frequency port
- [x] formalize full mixed-norm theorem in Lean
- [ ] compose repaired carrier with paired Carleman normal form
- [ ] prove trace-zero weighted root derivative
- [ ] prove RH or genuine whole-Connes no-go

### The full mixed-norm theorem EXISTS — every layer of Section 9's target is formal

Four modules close the card end to end, all `[propext, Classical.choice, Quot.sound]`:

- `HTGeometry/DiscreteL1Convolution.lean` — discrete convolution on an additive group with its
  quantitative layer in `ℝ≥0∞`: coefficientwise domination `|α ⋆ β| ≤ |α| ⋆ |β|`, the discrete
  Young identity with **equality** (`discreteMass_discreteEConv`), majorant powers of mass
  exactly `M^k`, the Neumann kernel of mass exactly `(1-M)⁻¹`, and the alternating Neumann series
  proved to be an actual **two-sided convolution inverse** of `δ₀ + r`
  (`discreteConv_delta_add_neumannSeries`) — the geometric `ℓ¹` resolvent.
- `RHTower/Suzuki/SuzukiWienerNeumannMajorant.lean` — Section 3 at its literal structure: the high-pass
  symbol `h = Lδ₀ + qδ₀ + t` factors as `L(δ₀ + r)` (`wienerHighPassSymbol_eq`); the
  coefficientwise domination `(15)` (`enorm_wienerRelativeKernel_le`); the exact majorant mass
  `(14)` `‖r_*‖₁ = (C+M)/L₀` with the `< 1/2` threshold form; the Neumann inverse `(16)` with the
  inverse identity (`discreteConv_wienerHighPassSymbol_neumannInverse`); the frequency-independent
  coefficient bound `(17)` (`enorm_wienerNeumannInverse_le`); and the exact inverse-kernel mass
  `(18)` (`discreteMass_wienerInverseKernel`).
- `RHTower/Suzuki/SuzukiWienerMixedNormCarrier.lean` — Section 4: the weighted two-term `L²` bound
  `(20)`→per-coordinate, the `ℓ¹(L²)` mixed-norm bound `(21)`
  (`tsum_eLpNorm_le_twoKernel`), and — via **mathlib's `L²` Fourier isometry**
  (`Lp.fourierTransformₗᵢ`), which now supplies scalar Plancherel `(22)` as a lookup — the
  position carrier `(22)`–`(24)`: `suzukiWienerTwoRootCarrier` gives absolute summability in
  `L²_x` with the same two-kernel bound.  Section 6's `(26)` is
  `summable_tsum_norm_clm_comp`: bounded componentwise operators preserve the legal `ℓ¹`
  evaluation.
- `RHTower/Suzuki/SuzukiWienerOrderSwapCounterexample.lean` — Section 2's explicit counterexample:
  `swapFreqFamily n ξ = (n+1)⁻¹ ψ(ξ-n)` for the concrete bump `ψ` has finite `L²(ℓ¹)` frequency
  norm (`lintegral_sq_tsum_swapFreqFamily`, the card's `(7)` via disjoint supports and
  translation invariance), while each position coordinate is a unimodular modulation of the fixed
  profile (`norm_swapPositionFamily`, the card's `(8)`) whose `ℓ¹` sums diverge on a set of
  positive measure (`measurePos_not_summable_swapPositionFamily`, the card's `(9)`).  Capstone:
  `suzukiWiener_orderSwap_counterexample` — the general order swap is `[FALSIFIED]` by an
  explicit obstruction, exactly as Section 2 demands.

Umbrellas wired.  Section 5's representation-change legality (the widened low port stays entire
of finite exponential type, hence Gamma-subcritical) is the qualitative context consumed by the
downstream carrier cards and stays a scope note.
