# Gamma--Gaussian universal property-\(S\) envelope

- **ID:** `gamma-gaussian-property-s-universal-envelope`
- **Stage:** 3-formalized
- **Type:** GENERAL MELLIN/Fourier COMPLETION THEOREM / RH-ROUTE NO-GO
- **Scientific status:** `[PAPER PROOF COMPLETE] [LITERATURE COROLLARY]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [ROUTE-CHANGING POSITIVE SURVIVOR] [NOT RH]`
- **Parents:**
  - `../suzuki/bv-copoisson-sharp-critical-half-weight-log-flux.md`;
  - `../../../3-formalized/not_new_scientific_knowledge/bv-copoisson-principal-normal-connection-law.md`;
  - `../1-in-progress/cofinal-conormal-picard-purity-law.md`;
  - Burnol, *Entrelacement de co-Poisson*, Theorems 4.31 and 4.54.
- **Statement:** A universal centered-Gaussian reciprocal-Gamma multiplier embeds every
  meromorphic-moderate Mellin datum, together with its Riemann reflection, into Burnol's
  extended property-\(S\) category.  It preserves every divisor in the open critical strip and
  sends reflection-symmetric data to Fourier-self-dual distributions.  Consequently existence
  of a singular Hausdorff self-dual completion retaining all divisor conormals cannot select the
  critical line.  The missing RH mechanism must be source-generated positivity/dissipation, not
  completion or dualizability.

## 1. Universal envelope

For the even cosine-Fourier Mellin convention put
\[
 \chi(s)
 =
 \pi^{s-\frac12}
 { \Gamma((1-s)/2)\over \Gamma(s/2)}.                    \tag{1}
\]
Define the entire multiplier
\[
 {\cal A}(s)
 :=
 \exp\!\left((s-\tfrac12)^2\right)
 {\pi^{s/2}\over\Gamma(s/2)}.                            \tag{2}
\]
Its zero set is
\[
 \{0,-2,-4,\ldots\}.                                     \tag{3}
\]
In particular, \({\cal A}\) is nonzero throughout \(0<\Re s<1\).

Let \(F\) be any meromorphic-moderate function in Burnol's sense.  Equivalently, one nonzero
polynomial clears its poles and leaves an entire function of polynomial growth on every vertical
line.  Put
\[
 {\cal E}F(s):={\cal A}(s)F(s).                          \tag{4}
\]

### Theorem 1 `[PROVED HERE]`

Both \({\cal E}F(s)\) and
\[
 \chi(s)\,{\cal E}F(1-s)                                \tag{5}
\]
are meromorphic moderate.  More precisely,
\[
 \boxed{\quad
 \chi(s)\,{\cal E}F(1-s)
 =
 {\cal A}(s)F(1-s).
 \quad}                                                  \tag{6}
\]
Therefore Burnol's Theorem 4.54 produces an even tempered distribution \(D_F\) with extended
property \(S\) whose right Mellin transform is \({\cal E}F\).  It is unique after imposing
Burnol's normalization that \(D_F\) vanish near the origin.  Its Fourier transform has right
Mellin transform \({\cal A}(s)F(1-s)\).

### Proof

Since
\[
 (1-s-\tfrac12)^2=(s-\tfrac12)^2,
\]
direct cancellation gives
\[
\begin{aligned}
 \chi(s){\cal A}(1-s)
 &=
 \pi^{s-\frac12}
 {\Gamma((1-s)/2)\over\Gamma(s/2)}
 \exp\!\left((s-\tfrac12)^2\right)
 {\pi^{(1-s)/2}\over\Gamma((1-s)/2)}\\
 &=
 \exp\!\left((s-\tfrac12)^2\right)
 {\pi^{s/2}\over\Gamma(s/2)}
 =
 {\cal A}(s).
\end{aligned}                                            \tag{7}
\]
This proves `(6)`.

It remains to check moderation.  On every fixed vertical strip, Stirling's estimate gives
\[
 \left|{1\over\Gamma(s/2)}\right|
 \leq
 C(1+|\Im s|)^N\exp\!\left({\pi\over4}|\Im s|\right).
                                                               \tag{8}
\]
The centered Gaussian contributes
\[
 \left|\exp((s-\tfrac12)^2)\right|
 =
 \exp\!\left((\Re s-\tfrac12)^2-(\Im s)^2\right).         \tag{9}
\]
Thus \({\cal A}\) has rapid decay on every closed vertical substrip.  Multiplication by
\({\cal A}\) sends a meromorphic-moderate function to another meromorphic-moderate function.
Reflection \(s\mapsto1-s\) preserves moderation, so `(6)` proves the same statement for `(5)`.
Burnol's Theorem 4.54 now gives \(D_F\).  `QED`

## 2. Exact interaction with the archimedean completion

Let
\[
 \Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2).
\]
Then
\[
 \boxed{\quad
 \Gamma_{\mathbb R}(s)\,{\cal E}F(s)
 =
 \exp\!\left((s-\tfrac12)^2\right)F(s).
 \quad}                                                  \tag{10}
\]
The reciprocal-Gamma factor in `(2)` is therefore not an appended zero-cancelling trick.  It is
exactly the inverse archimedean seam: after passing to Burnol's completed Mellin transform, only
the already formalized centered Gaussian smooth-approximate-functional-equation kernel remains.

Equation `(10)` also exposes the categorical roles:

```text
reciprocal Gamma zeros:
  cancel the infinite Fourier resonance lattice;

centered Gaussian:
  pays the reciprocal-Gamma vertical-growth debt;

Gamma_R completion:
  cancels the reciprocal Gamma and recovers the original Mellin datum;

Burnol property-S theorem:
  turns the repaired pair into one distribution and its Fourier dual.
```

## 3. Divisor and conormal faithfulness

### Theorem 2 `[PROVED HERE]`

For every \(\rho\) in \(0<\Re\rho<1\),
\[
 \operatorname{ord}_{\rho}({\cal E}F)
 =
 \operatorname{ord}_{\rho}(F),                          \tag{11}
\]
with the same statement for poles and all principal-normal jets.

### Proof

By `(3)`, \({\cal A}(\rho)\neq0\).  Multiplication by a holomorphic unit preserves the complete
local Laurent series up to an invertible triangular change of jets.  Hence it preserves order,
multiplicity, and nonzero top conormal class.  `QED`

If \(F(1-s)=F(s)\), equation `(6)` becomes
\[
 \chi(s){\cal E}F(1-s)={\cal E}F(s).                    \tag{12}
\]
The normalized distribution \(D_F\) is therefore cosine-Fourier self-dual, yet `(11)` allows
\(F\) to have arbitrary off-critical reflection quartets.  The envelope retains them all.

## 4. Repair of the sharp critical eta obstruction

The failed sharp-seed card isolated
\[
 F_{1/2}(s)
 =
 {\eta(s-\frac12)\over s-\frac12}.                       \tag{13}
\]
It is meromorphic moderate, with a simple pole at \(s=\frac12\), but
\(\chi(s)F_{1/2}(1-s)\) has infinitely many uncancelled Gamma poles.  Therefore
\(F_{1/2}\) itself cannot be the Mellin transform of an even extended-property-\(S\)
distribution.

The universal envelope gives
\[
 G_{1/2}(s)
 =
 \exp\!\left((s-\tfrac12)^2\right)
 {\pi^{s/2}\over\Gamma(s/2)}
 {\eta(s-\frac12)\over s-\frac12}.                       \tag{14}
\]
Equations `(6)` and `(10)` prove:

1. \(G_{1/2}\) has a normalized even extended-property-\(S\) realization;
2. its Fourier transform is obtained by replacing \(F_{1/2}(s)\) by
   \(F_{1/2}(1-s)\);
3. its complete Mellin transform is exactly
   \[
   \Gamma_{\mathbb R}(s)G_{1/2}(s)
   =
   e^{(s-\frac12)^2}
   {\eta(s-\frac12)\over s-\frac12};                    \tag{15}
   \]
4. the pole at \(s=\frac12\) survives, so the logarithmic boundary current is represented rather
   than discarded.

This closes the resonance obstruction left by Theorems F--G of the sharp-seed card.  The repair
is necessarily noncompact in multiplicative position, exactly as that card predicted.

## 5. Universal completion no-go

The construction \(F\mapsto D_F\) is linear, faithful away from the fixed trivial zero lattice
of \({\cal A}\), reflection-equivariant, and available for every meromorphic-moderate datum.
Consequently none of the following can imply a critical-line theorem:

1. existence of an extended-property-\(S\) distribution;
2. Hausdorff singular completion retaining every divisor conormal;
3. Fourier self-duality;
4. an Ind--Pro/Tate dual pair;
5. Picard invertibility or evaluation--coevaluation triangle identities;
6. Gaussian--Gamma regularization;
7. hypertranscendence of the reciprocal-Gamma completion.

All these structures can coexist with arbitrary off-line reflection quartets.

This is the exact correction to `XI COFINAL CONORMAL INVERTIBILITY`: invertibility and conormal
survival are kinematic.  An off-line conormal remains an invertible external correspondence in
the universal envelope.  What fails is membership in a fixed **positive source sector**.

## 6. Positive survivor: source-generated causal dagger

The corpus's selectors now have one common non-kinematic content.  If a conormal carries radial
character
\[
 \lambda_\rho(r)=r^{2\rho-1},                            \tag{16}
\]
then:

```text
algebraic/Riemann duality gives       lambda -> lambda^(-1);
source Hilbert adjunction gives       lambda -> conjugate(lambda);
equality of the two gives             |lambda|=1;
|lambda|=1 for one r>1 gives          Re(rho)=1/2.
```

The equality is not supplied by the universal envelope.  It must be generated by a one-sided
source order.

`[BOLD CONJECTURE] [XI_GAMMA_GAUSSIAN_CAUSAL_DAGGER]`

> Apply the universal Gamma--Gaussian property-\(S\) envelope to the pole-cancelled compact-BV
> normal class before divisor specialization.  The exact finite coefficient Stein forms extend
> to a canonical positive singular graph on its strict-property-\(S\) remainder plus
> quasi-homogeneous boundary line.  The completed co-Poisson multiplier ideal is a
> contractively invariant radical, square-index decimation descends as a contraction on the
> quotient, and every nonzero top Xi conormal jet is continuous there.

This conjecture is not claimed proved.  It is sharper than asking for a third completion:

1. Theorem 1 constructs a third completion for every moderate source, including off-line models.
2. The new load-bearing clause is positivity of one source-fixed singular graph.
3. Finite Stein positivity supplies its directed sign before continuation.
4. The Gamma--Gaussian envelope supplies the missing noncompact archimedean resonance repair.
5. Burnol's multiplier quotient supplies divisor-blind conormal fibres.
6. Contractivity plus `(16)` gives RH by the already proved BV/co-Poisson endpoint.

## 7. Reinterpretation of the obstruction corpus

```text
finite truncations:
  have positive Stein defect, but no complete conormal;

bare adelic or Burnol L2:
  has a dagger, but critical half-weight leaves the carrier;

Tate/Picard completion:
  retains the dual pair, but supplies no positive source order;

Gamma--Gaussian property-S envelope:
  repairs every topological and Fourier resonance defect, even off line;

Kakutani/Shale:
  measures failure of the repaired conormal to stay in the fixed source dagger sector;

Wold--Gamma/BV anomaly:
  is the finite source Stein boundary whose positive extension is missing;

two-infinity dipole / Beck--Chevalley defect:
  is the curvature of trying to extend that dagger through cofinal localization;

positive HT shells:
  faithfully report the resulting non-scalar polar defect;

Burnol Berezin diagonal:
  is its minimal scalar same-point reader.
```

Thus the universal law suggested by the full corpus is not “every source has a good completion.”
Every moderate source does.  The discriminating law is:

> **Critical-line purity is source-generated causal dagger compatibility on the completed
> principal conormal.**

Equivalently: Riemann duality and Hilbert adjunction must coincide because both are generated by
one pre-divisor positive source passage.  Completion merely makes the comparison typable.

## 8. Shifted BV-coordinate theorem and exact nonselection

The compact-BV continuation uses the pole coordinate
\[
 u=\rho+\frac12 .
\]
Riemann reflection \(\rho\mapsto1-\rho\) is therefore
\[
 u\longmapsto2-u,                                        \tag{17}
\]
with center \(u=1\).  Translate the universal envelope by putting
\[
\begin{aligned}
 {\cal A}_{\rm BV}(u)
   &:={\cal A}(u-\tfrac12)
     =
     e^{(u-1)^2}
     {\pi^{(u-\frac12)/2}\over
       \Gamma((u-\frac12)/2)},\\
 \chi_{\rm BV}(u)
   &:=\chi(u-\tfrac12)
     =
     \pi^{u-1}
     {\Gamma((\frac32-u)/2)\over
       \Gamma((u-\frac12)/2)} .
\end{aligned}                                             \tag{18}
\]

### Theorem 3 `[PROVED HERE]`

The translated envelope obeys
\[
 \boxed{\quad
 \chi_{\rm BV}(u){\cal A}_{\rm BV}(2-u)
 =
 {\cal A}_{\rm BV}(u).
 \quad}                                                    \tag{19}
\]
Its zero set is
\[
 \left\{\frac12,-\frac32,-\frac72,\ldots\right\},          \tag{20}
\]
so it is a holomorphic unit throughout the shifted critical strip
\(\frac12<\Re u<\frac32\).

### Proof

Set \(s=u-\frac12\).  Then \(2-u-\frac12=1-s\), and `(19)` is exactly
\(\chi(s){\cal A}(1-s)={\cal A}(s)\).  Equation `(20)` is the translate by
\(\frac12\) of `(3)`.  `QED`

At the BV pole \(u=\rho+\frac12\), the proved Laurent law is
\[
 R_j(\rho)
 =
 2m_\rho r^{j(\rho-\frac12)}
 M_W(\rho+\tfrac12),
 \qquad
 {R_{j+2}(\rho)\over R_j(\rho)}
 =
 r^{2\rho-1}
 =
 r^{2u-2}.                                                 \tag{21}
\]
Multiplication by \({\cal A}_{\rm BV}(u)\) changes every \(R_j(\rho)\) by the
same nonzero scalar.  Hence
\[
 {\widetilde R_{j+2}(\rho)\over\widetilde R_j(\rho)}
 =
 r^{2\rho-1}.                                              \tag{22}
\]

Thus the Gamma--Gaussian repair is exactly neutral under BV decimation.  It makes the conormal
typable in the extended property-\(S\) category, but it cannot change, damp, or orient its radial
Lyapunov exponent
\[
 \log|r^{2\rho-1}|=(2\Re\rho-1)\log r.                    \tag{23}
\]
This closes a possible hidden loophole in the completion route: archimedean resonance repair and
prime-dilation selection commute, so no choice of the universal envelope can supply the missing
contraction.

## 9. Hostile audit

1. Theorems 1--2 do not prove RH; they prove that a large class of completion-based arguments
   cannot prove RH.
2. The property-\(S\) distribution supplied by Burnol may be distributional, not an ordinary
   \(L^2\) vector.  This is intended: the surviving pole is the boundary coordinate.
3. Multiplication by \({\cal A}\) is noncompact in multiplicative position.  It does not belong
   to Burnol's compact co-Poisson convolution algebra.
4. The conjectural positive singular graph is not supplied by Theorem 4.54.  Positivity and
   contractivity remain the RH-bearing theorem.
5. Choosing a norm from zero residues, fitting a metric on each fibre, or requiring `(16)` to be
   contractive only after zero specialization is circular.
6. Generalized-prime or explicit off-line entire systems pass through the universal envelope.
   They become falsifiers only if the same literal ordinary-integer finite Stein source also
   generates the conjectured dagger.
7. Picard triangle preservation must be replaced by dagger-Picard preservation.  Abstract duals
   exist at every radial modulus.
8. The centered Gaussian is a growth corrector, not a sign producer.

## 10. Literature boundary

Parent results:

- J.-F. Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007), Theorem 4.31
  for strict property \(S\), Theorem 4.54 for extended property \(S\), and Theorem 4.55 for the
  quasi-homogeneous/polar-part correspondence;
- Stirling's vertical-strip estimate for reciprocal Gamma;
- standard Mellin dilation covariance;
- the Gaussian inverse-Mellin kernel already formalized in
  `RHTower.SmoothAFEGaussianKernel`.

The envelope is a direct corollary of these parents and no priority claim is made.  Its research
value is the route-changing conclusion that a faithful self-dual singular completion is universal
and hence nonselective.

## Gates

- [x] reciprocal-Gamma resonance cancellation
- [x] Gaussian vertical-growth compensation
- [x] exact Fourier-reflection identity
- [x] Burnol property-\(S\) realization
- [x] critical-strip divisor and conormal preservation
- [x] sharp critical eta obstruction repaired
- [x] completion/self-duality/Picard route no-go extracted
- [x] shifted BV typing and exact decimation-neutrality proved
- [x] positive source-dagger survivor isolated
- [x] construct the BV normal class inside the translated universal envelope
- [x] universal envelope, divisor faithfulness, shifted typing and decimation neutrality formalized unconditionally in Lean
- [ ] transport finite coefficient Stein positivity to its singular graph
- [ ] prove co-Poisson multiplier radical invariance
- [ ] prove conormal-jet continuity on the quotient
- [ ] compose contractivity with the formal RH endpoint

## Lean: the universal envelope, unconditionally

Theorems 1--3 and the nonselection conclusion of section 5 are now Lean, with no hypotheses.  Five
modules, all `#print axioms` clean (only `propext`, `Classical.choice`, `Quot.sound`).

### The multiplier and the exact reflection identity

`HTGeometry/GammaGaussianEnvelope.lean` defines the two factors through mathlib's archimedean factor
`Gammaℝ(s) = pi^(-s/2) Gamma(s/2)`, which makes `(2)` and `(1)` one-line identities:

```text
evenChiFactor s          = Gammaℝ(1-s) * Gammaℝ(s)⁻¹
                         = pi^(s-1/2) Gamma((1-s)/2) / Gamma(s/2);          -- (1)
gammaGaussianEnvelope s  = exp((s-1/2)^2) * Gammaℝ(s)⁻¹
                         = exp((s-1/2)^2) pi^(s/2) / Gamma(s/2);            -- (2)

gammaGaussianEnvelope_eq_zero_iff        : A(s) = 0 <-> s in {0,-2,-4,...};  -- (3)
gammaGaussianEnvelope_ne_zero_of_re_pos  : A is a unit on Re s > 0;
evenChiFactor_mul_envelope_one_sub       : chi(s) A(1-s) = A(s);             -- (6)
Gammaℝ_mul_gammaGaussianEnvelope         : Gammaℝ(s) A(s) = exp((s-1/2)^2);  -- (10)
differentiable_gammaGaussianEnvelope     : A is entire.
```

The identity `(6)` is exactly the card's proof: `(1-s-1/2)^2 = (s-1/2)^2` makes the Gaussian
reflection-invariant, and the two archimedean factors cancel.  The only hypothesis needed is that
`Gammaℝ(1-s)` be nonzero, which the corollary discharges on `Re s < 1` -- so `(6)` holds throughout
the critical strip.  Note that mathlib's `Gamma` vanishes at its poles, so `Gammaℝ⁻¹` *is* the entire
function whose zeros are `(3)`; nothing has to be excised by hand.

### Vertical growth: the multiplier of the moderate class

`HTGeometry/GammaGaussianEnvelopeDecay.lean` proves the moderation half of Theorem 1:

```text
norm_exp_sq_sub_half             : ||exp((s-1/2)^2)|| = exp((Re s - 1/2)^2 - (Im s)^2);   -- (9)
exists_bound_norm_inv_Gamma_strip: ||Gamma(z)⁻¹|| <= B exp(pi |Im z|) on a strip;         -- (8)
exists_bound_envelope_strip_decay: ||A(s)|| (1+|Im s|)^N is bounded on every closed strip;
exists_bound_envelope_band       : A is bounded on every compact horizontal band;
exists_bound_envelope_mul        : A F is bounded on every strip when F has polynomial
                                   vertical growth;
hasStripPolyGrowth_envelope_mul  : A preserves polynomial vertical growth;
hasStripPolyGrowth_one_sub       : reflection preserves it.
```

The reciprocal-Gamma bound reuses the corpus's own reflection-formula estimate
`RHTower.exists_lower_bound_norm_Gamma_strip` rather than Stirling; the constant is `exp(pi|Im z|)`
instead of `exp(pi|Im z|/4)`, which the Gaussian absorbs either way.  The decay proof needs no
compactness and no limit: `(1+t)^N <= exp(Nt)` and `-t^2 + bt <= b^2/4` turn the product into a
single exponential with a negative quadratic, bounded by the vertex value.  Only the horizontal band
`|Im s| <= 2` uses compactness, through continuity of the entire multiplier.

Combining the two modules gives Theorem 1 in full: `A F` and `s -> A(s) F(1-s)` are both moderate,
and on `Re s < 1` the second is literally `chi(s) (A F)(1-s)`
(`evenChiFactor_mul_envelope_mul_one_sub`).

### Divisor and conormal faithfulness

`HTGeometry/GammaGaussianEnvelopeDivisor.lean` proves Theorem 2 with mathlib's meromorphic order and
trailing coefficient:

```text
meromorphicOrderAt_envelope_mul :
  ord_rho(A F) = ord_rho(F)                                    for Re rho > 0;             -- (11)
meromorphicTrailingCoeffAt_envelope_mul :
  trailing coefficient of A F at rho = A(rho) * (that of F);
meromorphicTrailingCoeffAt_envelope_mul_ne_zero_iff :
  the top conormal jet is nonzero exactly when it was;
meromorphicOrderAt_envelope_mul_half :
  a pole at s = 1/2 survives with its exact order.
```

So the envelope preserves order, multiplicity and nonzero top conormal class, and the surviving
boundary pole of section 4 is a proved statement rather than a remark.

### The shifted BV coordinate and exact decimation neutrality

`HTGeometry/GammaGaussianEnvelopeBVShift.lean` proves Theorem 3 and the neutrality of section 8:

```text
bvChiFactor u, bvGammaGaussianEnvelope u  = the (18) translates by 1/2;
bvChiFactor_mul_bvEnvelope_two_sub        : chi_BV(u) A_BV(2-u) = A_BV(u);                 -- (19)
bvGammaGaussianEnvelope_eq_zero_iff       : zero set {1/2, -3/2, -7/2, ...};               -- (20)
bvGammaGaussianEnvelope_ne_zero_of_half_lt_re : unit on the shifted strip;
bvLaurentCoeff_ratio                      : R_(j+2)/R_j = r^(2 rho - 1);                  -- (21)
bvEnvelope_decimation_neutral             : the same ratio after multiplying every
                                            coefficient by A_BV(rho + 1/2);               -- (22)
log_norm_radial_character                 : log||r^(2 rho -1)|| = (2 Re rho - 1) log r;   -- (23)
norm_radial_character_eq_one_iff          : that modulus is 1 iff Re rho = 1/2.
```

The last statement is the `(16)` clause of the positive-survivor section in Lean: unimodularity of the
radial character at a single `r > 1` is equivalent to criticality.  What the envelope cannot do is
produce that unimodularity -- neutrality is proved, not assumed.

### The nonselection theorem

`HTGeometry/GammaGaussianEnvelopeNonselective.lean` turns section 5 into a construction.  For an
off-critical, off-axis `rho` the reflection quartet

```text
reflectionQuartet rho s = (s-rho)(s-(1-rho))(s-conj rho)(s-(1-conj rho))
```

is reflection-symmetric (`reflectionQuartet_one_sub`), of polynomial vertical growth, and has a simple
zero at `rho` (`meromorphicOrderAt_reflectionQuartet`, proved from the distinctness of the four points,
which is exactly `Re rho != 1/2` and `Im rho != 0`).  Hence

```text
exists_selfDual_moderate_with_offCritical_zero :
  for every rho with Re rho > 0, Re rho != 1/2, Im rho != 0 there is a datum F with
    F moderate, F(1-s) = F(s),
    A F moderate,
    chi(s) (A F)(1-s) = (A F)(s)   on Re s < 1,
    ord_rho(A F) = 1.
```

That is the no-go: a faithful, moderate, cosine-Fourier self-dual envelope coexists with an arbitrary
off-critical reflection quartet.  Also proved: in the right half-plane `A F` vanishes exactly on the
quartet (`envelope_reflectionQuartet_eq_zero_iff`), so the envelope neither creates nor destroys a
divisor there.

- 2026-08-03 -- The universal envelope is now a Lean object, and every proved theorem of this card is
  formalized unconditionally: the reflection identity, the zero set, entirety, the archimedean seam,
  moderation preservation, divisor and top-jet faithfulness, the shifted typing, decimation
  neutrality, the criticality criterion for the radial character, and an explicit off-critical
  witness family realizing the whole completion package.  Burnol's Theorem 4.54 is used nowhere: the
  Lean statements are about the multiplier and the divisor, which is precisely the part of the card
  that carries the no-go.  What remains open is unchanged and is the conjecture's positivity content
  -- the four gates below -- not the kinematics.

### Scope of the formalization

All three `[PROVED HERE]` theorems are formalized, in the generality in which the card states and
uses them.  Two boundaries are worth recording:

1. Section 4 derives its four claims about the specific seed
   `F_(1/2)(s) = eta(s-1/2)/(s-1/2)` from `(6)` and `(10)`; those two identities and the
   pole-survival statement are formalized for an arbitrary datum with a simple pole at `1/2`, which
   is exactly the argument the card gives.  The `eta` object itself is not built in Lean: mathlib's
   `riemannZeta` carries a junk value at `s = 1`, so `(1 - 2^(1-s)) riemannZeta s` is not the
   alternating zeta there, and an analytic `eta` would require a removable-singularity construction
   that no proved statement of this card needs.
2. Burnol's Theorems 4.31/4.54 are literature inputs and appear nowhere in the Lean development.
   Nothing formalized here depends on the existence of the property-`S` distribution; the multiplier
   identity, the divisor faithfulness and the off-critical witness are what carry the no-go, and they
   are unconditional.

## Stage-3 Lean certificate

Theorems 1--3 and the nonselection conclusion are unconditional Lean:

```text
gammaGaussianEnvelope_eq_zero_iff              -- (3) the exact zero divisor of the envelope
gammaGaussianEnvelope_ne_zero_of_re_pos
evenChiFactor_mul_envelope_one_sub             -- (6) the exact Fourier-reflection identity
evenChiFactor_mul_envelope_mul_one_sub
meromorphicOrderAt_envelope_mul                -- (11) divisor faithfulness
meromorphicTrailingCoeffAt_envelope_mul        -- conormal faithfulness
envelope_reflectionQuartet_eq_zero_iff
reflectionQuartet_one_sub
meromorphicOrderAt_reflectionQuartet
```

The remaining open gates are successor-programme items, not part of the theorem certified here.

Every declaration named above was resolved against the built Lean tree and `#print axioms`
reported only `propext`, `Classical.choice`, `Quot.sound`.  `scripts/formal_tools.py lint`
reports no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the tree.
