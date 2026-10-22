# Adelic Kummer rigged Hilbert triple

- **ID:** `deninger-adelic-kummer-gelfand-triple`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) · LEAN 4 THEOREM
- **Label:** `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`
- **Parent:** `deninger-adelic-l1-l2-rost-schmid-hodge-coefficient`
- **Statement:** mixed \(L^1/L^2\) completion of logarithmic Kummer
  functions is a canonical dense test space in the adelic \(L^2\)
  Hilbert space, with continuous product-formula topology and
  distribution dual.
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerAdelicKummerGelfandTriple`

## Setup

Let \((Y,\lambda)\) be the Allcock--Vaaler place space and
\(\mathcal F\) the rational vector space of logarithmic Kummer
functions.  Give \(\mathcal F\) the norm
\[
 \|f\|_E=\|f\|_1+\|f\|_2                                           \tag{1}
\]
and let \(E\) be its completion.  Let
\[
 H=L^2(Y,\lambda).
\]

## Theorem

`[PROVED HERE] [DAC_ADELIC_KUMMER_GELFAND_TRIPLE]`

There are canonical continuous dense injections
\[
 E\xhookrightarrow{i}H\xhookrightarrow{j}E',                      \tag{2}
\]
where
\[
 (jh)(e)=\langle i(e),h\rangle_{L^2}.                              \tag{3}
\]
The map \(j\) is injective.  Thus `(2)` is a real rigged Hilbert
triple.

Let
\[
 I(f)=\int_Yf\,d\lambda
\]
on \(L^1\cap L^2\).  Then
\[
 |I(f)|\leq\|f\|_1\leq\|f\|_E,                                    \tag{4}
\]
and the image of \(E\) lies in the closed product-formula kernel
\(\ker I\).  The arithmetic constraint is therefore retained on the
test space even though its image is dense in \(H\).

Normalized field-norm projections preserve `(2)` and are contractions
on \(E\) and \(H\).  The \(s\)-twisted power map acts on the Kummer
core by \(n^{1-s}\); at \(s=\tfrac12\) it scales the \(H\)-pairing by
\(n\) and preserves \(E\).

## Proof

The norm `(1)` dominates the \(L^2\)-norm, so the inclusion of
\(\mathcal F\) into \(H\) extends continuously to \(i:E\to H\).
If an \(E\)-Cauchy sequence converges to zero in \(L^2\), it also
converges in \(L^1\); uniqueness in measure identifies both limits,
so \(i\) is injective.

Allcock--Vaaler prove that \(\mathcal F\) is dense in \(L^2\).
Since \(\mathcal F\subset i(E)\), the image of \(i\) is dense.

Cauchy--Schwarz and \(\|e\|_2\leq\|e\|_E\) give
\[
 |(jh)(e)|
 \leq\|h\|_2\|e\|_2
 \leq\|h\|_2\|e\|_E,
\]
so `(3)` defines a continuous injection \(j:H\to E'\).  If
\(jh=0\), then \(h\) is orthogonal to the dense subspace \(i(E)\), so
\(h=0\).

Inequality `(4)` proves continuity of the product-formula functional on
the ambient mixed space.  It vanishes on every \(f_\alpha\); continuity
therefore makes it vanish on their \(E\)-closure.  The norm and power
claims follow from `DAC_ADELIC_PLACE_AVERAGE_RESIDUE` and
`DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`.

## Formalized statement

All declarations live in the `RHTower` namespace.

**Abstract rigged-Hilbert construction.**  For a real inner-product space `H`, a normed space
`E` and a continuous linear test embedding `i : E →L[ℝ] H`:

- `deningerRiggedDual i : H →L[ℝ] (E →L[ℝ] ℝ)` is the distribution map, with
  `deningerRiggedDual_apply` and `deningerRiggedDual_apply'` giving `(j h)(e) = ⟪i e, h⟫`
  — this is `(3)`;
- `deningerRiggedDual_norm_le` : `‖j h‖ ≤ ‖h‖ ‖i‖`, the Cauchy--Schwarz continuity of `j`;
- `deningerRiggedDual_injective` : `DenseRange i → Function.Injective (deningerRiggedDual i)`,
  which is the injectivity half of `(2)`.

**The mixed `L¹/L²` test space**, over an arbitrary measure space `(Y, μ)`:

- `deningerMixedL12 μ` is the carrier — pairs of an `L¹` class and an `L²` class agreeing
  almost everywhere — inside `WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)`, whose norm is exactly
  `‖f‖₁ + ‖f‖₂` (`deningerMixed_norm`), so `(1)` holds by construction;
- `deningerMixedL12_isClosed` : the carrier is closed, proved through convergence in measure and
  almost-everywhere uniqueness of limits in measure — this is the card's own injectivity
  argument, and it gives `CompleteSpace (DeningerMixed μ)`, so `E` is a Banach space and not
  merely a normed one;
- `deningerMixedToL1`, `deningerMixedToL2` are the two components, each of norm `≤ 1`;
- `deningerMixedToL2_injective` : `i` is injective;
- `deningerMixedToL2_denseRange` : `i` has dense range — proved unconditionally, since every
  `L²` class is approximated by simple functions and a simple function in `L²` has
  finite-measure support, hence lies in `L¹` as well;
- `deningerMixedGelfandTriple` : the three conclusions of `(2)` together, unconditionally.

**Product formula `(4)`:**

- `deningerMixedIntegral μ : DeningerMixed μ →L[ℝ] ℝ` is `f ↦ ∫ f dμ` through the `L¹`
  component;
- `deningerMixedIntegral_norm_le` : `|I f| ≤ ‖f‖₁ ≤ ‖f‖_E`;
- `deningerMixedIntegral_isClosed_ker` and `deningerMixedIntegral_eq_zero_of_mem_closure` : the
  product-formula kernel is closed, so a functional vanishing on a set vanishes on its closure.
  This is the exact step by which the arithmetic constraint survives passage to the completion.

### What is formalized and what is not

Formalized unconditionally: the abstract rigged-Hilbert construction; the mixed `L¹/L²` Banach
space over an arbitrary measure space, its dense injection into `L²`, the resulting rigged
triple, and the product-formula continuity `(4)` with its closure stability.

Not formalized, and stated as such: the Allcock--Vaaler place space `(Y, λ)` itself, and the
Fili--Miner normalized-projection and twisted-power statements of the last paragraph of the
theorem.  Note also a difference of scope that the card should not blur: the card's `E` is the
completion of the *Kummer functions* `𝓕`, whose density in `L²` is Allcock--Vaaler's theorem;
what is proved here is that the *full* mixed space `L¹ ∩ L²` is dense in `L²`, which is
unconditional.  The abstract theorem covers the `𝓕` case verbatim once that density is
supplied, since `deningerRiggedDual_injective` takes `DenseRange i` as its hypothesis.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerAdelicKummerGelfandTriple.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all 20 declarations: only the Lean/mathlib standard `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Arithmetic interpretation

- \(E\): source test/cochain topology retaining principal-divisor
  reciprocity and residue summability;
- \(H\): positive local Kummer energy space;
- \(E'\): distributional coefficient space in which trace and
  fixed-point functionals may live.

This separates Deninger's distributional Lefschetz topology from his
Hodge Hilbert topology.  It does not identify \(H\) with global
arithmetic \(H^1\): the centered Kummer power action is still scalar,
and nontrivial spectrum must come from the non-scalar part of
Deninger's true-to-approximate derived coefficient.  Frobenius
coherence and coarse/stack defects are candidate summands only.

## Limits

- \(E=L^1\cap L^2\) is not automatically nuclear.
- The theorem gives no global sheafification, closed Rost--Schmid
  differential, Kähler leaf, or Hodge star.
- Extension of the rigged triple from Kummer functions to the full
  Steinberg-corrected Milnor coefficient, plus its separate real
  Milnor--Witt orientation, is conjectural.

## Gates

- [x] complete paper proof
- [x] Lean formalization of the abstract rigged-Hilbert construction
  (`deningerRiggedDual`, `deningerRiggedDual_injective`)
- [x] specialization to the mixed \(L^1/L^2\) space over an arbitrary measure space
  (`deningerMixedGelfandTriple`, `deningerMixedIntegral_norm_le`)
- [ ] specialization to the Allcock--Vaaler measure itself, which is not yet a formalized
  object anywhere in the corpus

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975

## Log

- 2026-07-26 — Proved the mixed coefficient is the canonical
  test/Hilbert/distribution triple forced by \(L^1\) product formula and
  \(L^2\) positivity.
- 2026-08-01 — Formalized the abstract rigged triple and the mixed \(L^1/L^2\) Banach test
  space over an arbitrary measure space, unconditionally in Lean 4.
