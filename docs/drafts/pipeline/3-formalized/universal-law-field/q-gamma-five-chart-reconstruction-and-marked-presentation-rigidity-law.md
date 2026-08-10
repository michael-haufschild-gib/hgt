# q-Gamma five-chart reconstruction and marked presentation-rigidity law

- **ID:** ULF-QG5R-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / PRESENTATION-INVARIANCE CALIBRATION
- **Source:** doctrine-change gate for Constitutive Process Mathematics
- **Statement:** Within the Jackson \(q\)-Gamma family, parameter, atomic probability law, characteristic process, minimal cyclic GNS realization, and analytic response germ determine one another; equal observed process responses force marked unitary equivalence and identical withheld tilt laws.
- **Status:** [PAPER-PROVED] [FIVE CHARTS] [EXACT RECONSTRUCTION] [MARKED PRESENTATION RIGIDITY] [WITHHELD RESPONSE INVARIANT] [CLASSICAL FOURIER/GNS/MOMENT PARENTS] [NOT RH] [LEAN CERTIFIED]

## 1. Five charts

For \(0<q<1\), retain the data from ULF-QGPRH-1:

\[
w_n(q)=(q;q)_\infty\frac{q^n}{(q;q)_n},
\qquad
x_n(q)=n\log q-\log(1-q),
\tag{1}
\]

\[
\mu_q=\sum_{n\ge0}w_n(q)\delta_{x_n(q)},
\qquad
C_q(t)=\int e^{itx}\,d\mu_q(x),
\tag{2}
\]

\[
F_q(s)=\Gamma_q(1+s)=\int e^{sx}\,d\mu_q(x)
\qquad(\operatorname{Re}s>-1),
\tag{3}
\]

and the minimal cyclic spectral realization

\[
\mathcal G_q=(\mathcal H_q,U^q,\Omega_q),
\qquad
C_q(t)=\langle\Omega_q,U_t^q\Omega_q\rangle.
\tag{4}
\]

The five presentations are:

1. parameter \(q\);
2. probability law \(\mu_q\);
3. characteristic process \(C_q\);
4. marked minimal GNS triple \(\mathcal G_q\);
5. analytic germ \([F_q]_0\).

## 2. Reconstruction theorem

### Theorem 2.1

Every one of the five presentations determines the other four. More precisely:

1. \(q\) gives (1)--(4) explicitly;
2. \(\mu_q\) recovers \(q\) from the unique maximal support point
   \[
   \max\operatorname{supp}\mu_q=x_0(q)=-\log(1-q);
   \tag{5}
   \]
3. \(C_q\) uniquely determines \(\mu_q\) by Fourier uniqueness;
4. \(\mathcal G_q\) determines \(C_q\) by its cyclic matrix coefficient;
5. the germ \([F_q]_0\) uniquely determines \(\mu_q\), because it is a moment-generating function
   finite on a neighborhood of \(0\).

Consequently all five recover

\[
\boxed{q=1-\exp(-x_0).}
\tag{6}
\]

### Proof

Only the reverse reconstructions require proof.

The support points satisfy

\[
x_{n+1}(q)-x_n(q)=\log q<0,
\]

so \(x_0(q)\) is the unique maximal point. Equation (6) follows from (5).

The uniqueness theorem for characteristic functions reconstructs a finite Borel measure from
\(C_q\). The marked GNS triple gives \(C_q\) directly by (4).

Finally, \(F_q\) is finite on the open half-plane \(\operatorname{Re}s>-1\), so in particular on
a real neighborhood of \(0\). Equality of two such germs gives equality of all moments and of the
moment-generating functions on a neighborhood of \(0\); the standard uniqueness theorem for
moment-generating functions gives equality of their probability laws. Equivalently, exponential
integrability makes the Hamburger moment problem determinate. QED.

## 3. Marked GNS presentation rigidity

Two marked cyclic unitary presentations

\[
(\mathcal H,U,\Omega),
\qquad
(\mathcal H',U',\Omega')
\tag{7}
\]

are **process equivalent** when

\[
\langle\Omega,U_t\Omega\rangle
=\langle\Omega',U'_t\Omega'\rangle
\qquad(t\in\mathbb R)
\tag{8}
\]

and the cyclic spans of \(\Omega,\Omega'\) are dense.

### Theorem 3.1

If (8) holds, there is a unique unitary

\[
V:\mathcal H\longrightarrow\mathcal H'
\tag{9}
\]

such that

\[
V\Omega=\Omega',
\qquad
VU_t=U'_tV
\qquad(t\in\mathbb R).
\tag{10}
\]

Hence two minimal GNS presentations of \(C_q\) are not merely analogous: they are uniquely
equivalent as marked process realizations.

### Proof

On the algebraic cyclic span define

\[
V_0\left(\sum_jc_jU_{t_j}\Omega\right)
=\sum_jc_jU'_{t_j}\Omega'.
\tag{11}
\]

All inner products between such vectors are determined by the common function in (8):

\[
\left\langle U_s\Omega,U_t\Omega\right\rangle=C(t-s).
\]

Thus \(V_0\) is well-defined and isometric. Cyclicity makes its domain and range dense, so it
extends to a unitary \(V\). Equations (10) hold on a dense spanning set and hence everywhere.
Uniqueness follows from the same cyclicity. QED.

## 4. Full five-chart rigidity

### Corollary 4.1

For \(q,q'\in(0,1)\), the following are equivalent:

\[
\boxed{
q=q'
\Longleftrightarrow
\mu_q=\mu_{q'}
\Longleftrightarrow
C_q=C_{q'}
\Longleftrightarrow
\mathcal G_q\simeq\mathcal G_{q'}
\Longleftrightarrow
[F_q]_0=[F_{q'}]_0.}
\tag{12}
\]

Here \(\simeq\) means the unique marked unitary equivalence of Theorem 3.1.

### Proof

Forward implications are explicit. Every reverse implication reconstructs \(\mu_q\), then \(x_0\),
then \(q\) by Theorem 2.1. QED.

This is the first concrete presentation-invariance theorem for the CPM field programme.

## 5. Invariance of memory and withheld interventions

Once any chart reconstructs \(q\), it reconstructs:

- every atom \(x_n(q)\) and weight \(w_n(q)\);
- the positive moment matrices;
- the compact-resolvent generator \(X_q\);
- the recurrent orbit and marked open lift;
- the full hypertranscendental germ \(F_q\);
- the exponential tilt
  \[
  \widetilde w_n=e^{x_n}w_n;
  \tag{13}
  \]
- its characteristic response and information costs
  \[
  \widetilde C_q(t)
  =\frac{1-q^{1+it}}{1-q}C_q(t),
  \tag{14}
  \]
  \[
  D(\widetilde w\|w)=F_q'(1),
  \qquad
  D(w\|\widetilde w)=-F_q'(0).
  \tag{15}
  \]

### Corollary 5.1

Every quantity above is invariant under marked process equivalence. In particular, the withheld
tilt response (14) is independent of whether the source was presented as a probability law,
positive kernel, cyclic operator system, analytic germ, or \(q\)-parameter.

This is stronger than chartwise agreement after fitting: a single observed complete response
\(C_q\) reconstructs the parameter and forces all other charts.

## 6. Doctrine atlas interpretation

Let \(\mathsf{Pres}_q\) be the groupoid with the five presentations as objects and the reconstruction
equivalences above as arrows. The response functor

\[
\mathcal R:\mathsf{Pres}_q\longrightarrow\mathsf{Proc},
\tag{16}
\]

sending each chart to the common characteristic process, is conservative on this groupoid:
an arrow is an equivalence exactly when it preserves the complete response.

This gives the smallest exact CPM doctrine atlas:

- probability and positive-kernel presentations are related by Fourier/Bochner reconstruction;
- positive-kernel and operator presentations are related by minimal GNS reconstruction;
- probability and analytic presentations are related by Mellin/moment-generating reconstruction;
- the \(q\)-difference law acts as a represented intervention on the reconstructed process.

No claim is made that an arbitrary doctrine equivalence preserves every chosen notion of memory.
The marking by the complete response and cyclic source vector is load-bearing.

## 7. Hostile boundaries

1. Minimality/cyclicity is required. One can add an arbitrary orthogonal spectator representation
   without changing \(C_q\).
2. The complete characteristic function is required. Finite samples or finitely many moments do
   not reconstruct an infinite atomic law.
3. The analytic germ must be known exactly, not through a finite jet.
4. The result proves marked presentation invariance inside one family, not a general Morita theorem
   for all process doctrines.
5. The tilt law is not determined by a bare positive-definite function outside the reconstructed
   \(q\)-Gamma family.
6. No higher-slot causal process, physical clock/cost, RH statement, or arithmetic zero consequence
   is obtained.

## Classical parents

- uniqueness of characteristic functions and moment-generating functions;
- Bochner/GNS reconstruction and uniqueness of minimal cyclic representations;
- determinate moment problems under exponential integrability;
- Jackson's \(q\)-Gamma and Pastro's \(q\)-Hölder theorem.

## Log

- 2026-08-09 — all five \(q\)-Gamma charts proved mutually reconstructive; minimal GNS
  equivalence and invariance of the entropy-tilt prediction closed the first marked
  presentation-rigidity gate.
- 2026-08-10 — every theorem of the card certified unconditionally in Lean; card promoted to
  stage 3.

## Lean certification status

**COMPLETE (2026-08-10).**  The card's objects are already owned by the corpus from
ULF-QGPRH-1 (`GaloisForLFunctions/HTGeometry/ConstitutiveQGammaProcess.lean`, now stage 3):
`qGammaAtom` (equation (1) `x_n`), `qGammaWeight` (`w_n`) with `qGammaWeight_pos` and
`qGammaWeight_hasSum_one`, `qGammaResponse`/`qResponseFun` (equation (3) `F_q`) with
`qResponseFun_eq`, `hasDerivAt_qResponseFun` on `qStrip = {−1/2 < Re s < 2}` (`isOpen_qStrip`,
`convex_qStrip`), `qChar` (equation (2)) with `qChar_hasSum`, the GNS data `QGammaSpace`, `qOmega`,
`qOrbit`, `inner_qOrbit` and equation (4) `qChar_eq_inner`, `qGammaAtom_injective`, `qTiltWeight`,
and **equation (14) is already certified** as `qTilt_response_eq`.

Audited mathlib inputs: `MeasureTheory.Measure.ext_of_charFun` (Fourier uniqueness for finite
Borel measures on a complete second-countable real inner-product space — so `ℝ` qualifies) exists;
`LinearIsometry.extend` is finite-dimensional only, so Theorem 3.1 needs a dense-subspace
extension built by hand.

Planned modules:

1. `QGammaFiveChart.lean` — the atom order and the parameter chart: `qGammaAtom_zero`
   (`x_0 = −log(1−q)`), strict antitonicity of `n ↦ x_n` (because `log q < 0`), hence `x_0` is the
   unique maximal atom; equation (6) `q = 1 − exp(−x_0)`; the law chart `qLaw q` as a
   `Measure.sum` of scaled Diracs, with total mass one, `qLaw q {x_k} = w_k` (through
   `qGammaAtom_injective`), and no mass above `x_0`; equation (5) and `qLaw q = qLaw q' → q = q'`;
   `charFun (qLaw q) = qChar q`, so `qChar q = qChar q' → q = q'` by `Measure.ext_of_charFun`; and
   the germ chart by the identity theorem on `qStrip` (which is open, connected, contains `0` and
   the whole imaginary axis), reducing chart 5 to chart 3.  Corollary 4.1 assembles the five
   equivalences.
2. `MarkedCyclicRigidity.lean` — Theorem 3.1 over an arbitrary group `G` acting by linear
   isometry equivalences on complex Hilbert spaces: equal cyclic matrix coefficients give a unique
   marked intertwining unitary.  Route: the linear map `T = Finsupp.linearCombination` from
   `G →₀ ℂ` to the cyclic span, the Gram identity `⟪U_g Ω, U_h Ω⟫ = ⟪Ω, U_{g⁻¹h} Ω⟫`, equality of
   kernels, the induced isometry between the two spans, and extension by density.
3. Corollary 5.1 — invariance of the reconstructed data under marked process equivalence.

### What was built

Four new modules, all wired through `GaloisForLFunctions.HTGeometry.UniversalLawField`.

**`QGammaFiveChart.lean` — the atom order and charts 1, 2, 3, 5.**

- `RealEulerNome.ext'`, `qGammaAtom_zero` (`x_0 = −log(1−q)`), `qGammaAtom_strictAnti` (the atoms
  strictly decrease because `log q < 0`), **equation (5)** `qGammaAtom_le_zero` (`x_0` is the
  largest atom), **equation (6)** `nome_eq_one_sub_exp_neg` (`q = 1 − exp(−x_0)`), and
  `nome_eq_of_atom_zero_eq`.
- The probability chart: **`qLaw`** — the atomic law `∑ w_n δ_{x_n}` as a `Measure.sum` of scaled
  Diracs — with `qLaw_apply`, `qLaw_univ`, the `IsProbabilityMeasure` instance, `qLaw_singleton`,
  `qLaw_singleton_atom` (`μ{x_k} = w_k`, through `qGammaAtom_injective`), `qLaw_singleton_eq_zero`,
  and **`nome_eq_of_qLaw_eq`**: two equal laws have the same largest atom, hence the same nome.
- The characteristic chart: `integrable_qCharKernel`, **`charFun_qLaw`** (the mathlib characteristic
  function of `qLaw q` *is* `qChar q`, by term-by-term integration against the Dirac sum), and
  **`nome_eq_of_qChar_eq`** through mathlib's Fourier uniqueness `Measure.ext_of_charFun`.
- The germ chart: `differentiableOn_qResponseFun`, `analyticOnNhd_qResponseFun`, `mem_qStrip_zero`,
  `mem_qStrip_I_mul`, `qChar_eq_qResponseFun`, and **`nome_eq_of_response_germ_eq`** — the germ at
  the origin continues analytically across `qStrip`, which is convex, hence connected, and carries
  the whole imaginary axis, so the germ determines the characteristic process.
- `qGamma_fourChart_tfae`.

**`MarkedCyclicRigidity.lean` — Theorem 3.1, over an arbitrary group.**

`cyclicMap` (the orbit map `(G →₀ ℂ) → H`), `range_cyclicMap`, **`inner_orbit`**
(`⟪U_g Ω, U_h Ω⟫ = ⟪Ω, U_{g⁻¹h} Ω⟫`), `inner_cyclicMap`, `norm_cyclicMap_eq`,
**`ker_cyclicMap_eq`** (equal matrix coefficients give equal kernels), `cyclicTransfer` (through
`Submodule.liftQ` and `LinearMap.quotKerEquivRange`), `norm_cyclicTransfer`, `cyclicIsometry`,
`markedMap` (extension by density, through `ContinuousLinearMap.extend`), `markedMap_cyclicMap`,
`norm_markedMap`, `markedMap_omega`, `markedMap_intertwine`, and the capstone

**`exists_unique_marked_intertwiner`** — for any group `G` acting by linear isometry equivalences
on complex Hilbert spaces `H`, `H'` with cyclic vectors `Ω`, `Ω'` and equal matrix coefficients,
there is **exactly one** unitary `V : H ≃ₗᵢ[ℂ] H'` with `VΩ = Ω'` and `V ∘ U_g = U'_g ∘ V`.

mathlib's `LinearIsometry.extend` is finite-dimensional only, so the extension is built here from
`ContinuousLinearMap.extend` plus the two-sided density argument; uniqueness is density again.

**`AbsConvergentPowerSeries.lean` — coefficients of an absolutely convergent power series.**

`powerCoeff_eq_zero_of_eventuallyEq_zero` (uniqueness of power-series coefficients through
`FormalMultilinearSeries.ofScalars`), `analyticOnNhd_powerSum`, `frequently_circle_ne_one` (points
of the unit circle accumulate at `1`), and **`powerCoeff_eq_zero_of_circle`**: a power series whose
coefficients decay geometrically past the unit circle and whose sum vanishes on that circle has all
coefficients zero.

**`QGammaGNSChart.lean` — chart 4 and the five-chart corollary.**

- Diagonal unitaries of `ℓ²`, absent from mathlib: `lpPhaseLM`, `norm_lpPhaseLM`, **`lpPhaseEquiv`**
  (multiplication by a unimodular sequence is a unitary).
- **`qUnitary`** — the q-Gamma unitary group `Multiplicative ℝ →* (ℓ² ≃ₗᵢ[ℂ] ℓ²)`, `U_t` being
  multiplication by `exp(i t x_n)`; `qUnitary_qOmega` identifies its orbit with `qOrbit`
  (equation (4)).
- **`dense_span_qOrbit`** — *the source vector is cyclic*: a vector `v` orthogonal to the whole
  orbit gives coefficients `a_n = √w_n · v_n` with `‖a_n‖ ≤ ‖v‖ (√q)ⁿ`, so `∑ a_n zⁿ` converges on
  a disc of radius `q^{−1/4} > 1`; the orthogonality relations say exactly that this sum vanishes on
  the whole unit circle, so every `a_n` vanishes and `v = 0`.  With
  `Submodule.topologicalClosure_eq_top_iff` this is density of the cyclic span.
- **`markedEquivalent_of_qChar_eq`** (chart 3 → chart 4, by Theorem 3.1) and
  **`qChar_eq_of_markedEquivalent`** (chart 4 → chart 3, because a marked unitary preserves the
  matrix coefficient).
- **Corollary 4.1** `qGamma_fiveChart_tfae`: `q = q' ↔ μ_q = μ_{q'} ↔ C_q = C_{q'} ↔ 𝓖_q ≃ 𝓖_{q'} ↔
  [F_q]_0 = [F_{q'}]_0`.
- **Corollary 5.1** `markedEquivalent_invariance`: marked process equivalence forces equality of the
  nome and therefore of the atoms, weights, moments, tilted law, probability law and analytic
  response.  Equation (14) — the withheld tilt response — was already certified in ULF-QGPRH-1 as
  `qTilt_response_eq`, so it is invariant as well.

`#print axioms` on `qGamma_fiveChart_tfae`, `qGamma_fourChart_tfae`,
`exists_unique_marked_intertwiner`, `dense_span_qOrbit`, `nome_eq_of_qChar_eq`,
`nome_eq_of_response_germ_eq`, `charFun_qLaw`, `markedEquivalent_invariance` and
`powerCoeff_eq_zero_of_circle` reports only `propext`, `Classical.choice`, `Quot.sound`.  The
`GaloisForLFunctions.HTGeometry.UniversalLawField` umbrella builds green (11,541 jobs).

§6 is the categorical restatement of Corollary 4.1 and §7 is commentary; neither adds a
mathematical claim beyond what is certified.
