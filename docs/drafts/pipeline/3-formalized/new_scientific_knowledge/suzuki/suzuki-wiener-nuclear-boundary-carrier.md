# Suzuki's Wiener carrier is nuclear in position but loses the physical log measure

- **ID:** `suzuki-wiener-nuclear-boundary-carrier`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-SPECIFIC FUNCTION-SPACE UPGRADE / SHARP MEASURE OBSTRUCTION
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes
- **Inputs:** `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-exterior-feshbach-pruning-law.md`

## 1. Result

The pointwise estimate

```text
c in L2_frequency(ell1_valuation)
```

is not enough by itself to justify inverse Fourier transformation as an
\(\ell^1\)-valued operation: \(\ell^1\) has no Hilbert Fourier type.  Suzuki's explicit Neumann
series supplies a stronger order of summation.

Fix a high-frequency region \(E=\{|\xi|\geq\Xi\}\).  Let

```text
h_xi=L(xi)delta_0+q(xi)delta_0+t,

L(xi)>=L_0,       |q(xi)|<=C,       ||t||_1=M,

rho=(C+M)/L_0<1.                                    (1)
```

For \(B\in L^2(E)\), let

```text
c(xi)=h_xi^(-1)*[B(xi)e_root].                         (2)
```

Then

```text
sum_nu ||c_nu||_(L2(E))
 <=1/[L_0-C-M] ||B||_(L2(E)).                          (3)
```

For Suzuki's two roots,

```text
sum_(root,nu)||c_(root,nu)||_L2
 <=1/[L_0-C_a-M_a]
   [||B_-||_2+||B_+||_2].                              (4)
```

Consequently:

```text
c in ell1(seams;L2_frequency)
  -> Fourier^(-1)c in ell1(seams;L2_position)
  -> exp(-L/2) times every seam-centered profile lies in
     L2_log(ell1_seams) subset L2_log(ell2_seams).      (5)
```

This removes the vector-valued Plancherel obstruction left open by the predecessor theorem, but it
does **not** construct the physical logarithmic carrier used by the Gamma theorems.  That carrier
uses \(F_q(L)=g_q(\pm e^{-L})\), without the factor \(e^{-L/2}\), and

```text
integral |F_q(L)|^2 dL
 =integral_0^1 |g_q(r)|^2 dr/r.                         (5a)
```

This is strictly stronger than ordinary position \(L^2(dr)\).  The successor theorem
`suzuki-physical-log-low-frequency-boundary-lock.md` proves that the apparent missing estimate
cannot be supplied by the high-frequency carrier alone: even scalar \(L^2(dr/r)\) of the high
part forces an independent low-frequency endpoint moment to vanish.  Thus `(3)` exposes a
**coupled low/high matching lock**, not a free-standing high-tail regularity estimate.

## 2. Word-majorant proof

The exact inverse is

```text
h_xi^(-1)
 =1/L(xi) sum_(k>=0)
   [-(q(xi)delta_0+t)/L(xi)]^(*k).                     (6)
```

Let \(|t|\) denote coefficientwise absolute value and define the positive measure

```text
mu=C delta_0+|t|,          ||mu||_1=C+M.                (7)
```

For every grade \(k\), valuation \(\nu\), and \(\xi\in E\), expansion into zero steps and prime
steps gives the coefficientwise majorant

```text
|[(q(xi)delta_0+t)^(*k)]_nu|
 <=(mu^(*k))_nu.                                        (8)
```

The right side is independent of \(\xi\), nonnegative, and

```text
sum_nu (mu^(*k))_nu=(C+M)^k.                            (9)
```

Let \(c_\nu^{(k)}\) be the grade-\(k\) contribution to `(2)`.  Equations `(8)` and
\(L(\xi)\geq L_0\) imply

```text
||c_nu^(k)||_L2
 <=(mu^(*k))_nu/L_0^(k+1) ||B||_L2.                    (10)
```

Tonelli applies to the nonnegative majorant.  Sum first over \(\nu\), then over \(k\):

```text
sum_nu sum_(k>=0)||c_nu^(k)||_L2
 <=||B||_2/L_0 sum_(k>=0)[(C+M)/L_0]^k
 =||B||_2/[L_0-C-M].                                   (11)
```

Absolute convergence in the Banach space
\(\ell^1(\Gamma;L^2(E))\) permits the grade sum and coordinate sum to be interchanged.  Triangle
inequality gives `(3)`.  The two root sectors do not mix under valuation convolution, so applying
`(3)` to each root gives `(4)`. `QED`

This proof uses the complete word expansion, not a false interchange inferred from
\(L^2(E;\ell^1)\).

## 3. Plancherel and seam recentering

Extend every \(c_q\) by zero off \(E\), and let \(g_q=\mathcal F^{-1}c_q\).  Scalar Plancherel
gives

```text
sum_q ||g_q||_L2(R)
 =const_F sum_q ||c_q||_L2(R)<infinity.                 (12)
```

Multiplication by the physical seam phase

```text
exp[-i xi x(q)]
```

is translation by \(x(q)\) after inverse Fourier transformation and preserves every \(L^2\)
norm.  Thus `(12)` remains true for the physically centered profiles.

For each oriented seam choose either half-line restriction and the **unitarily weighted**
logarithmic chart

```text
(U_+ g)(L)=exp(-L/2)g(+exp(-L)),

(U_- g)(L)=exp(-L/2)g(-exp(-L)).                        (13)
```

Indeed \(dr=e^{-L}dL\), so

```text
||U_+g||_L2(dL)=||g||_L2((0,infinity)),

||U_-g||_L2(dL)=||g||_L2((-\infinity,0)).               (14)
```

Writing \(\widetilde F_q=U_{\operatorname{orientation}(q)}g_q\), equations `(12)`--`(14)` give

```text
sum_q ||tilde F_q||_L2(dL)<infinity.                    (15)
```

Minkowski now gives the load-bearing rigged estimate

```text
||tilde F||_(L2(dL;ell1))
 =||sum_q |tilde F_q(.)|||_L2
 <=sum_q ||tilde F_q||_L2<infinity.                     (16)
```

In particular \(\widetilde F(L)\in\ell^1\) for almost every \(L\), and

```text
||tilde F||_(L2(ell2))<=||tilde F||_(L2(ell1)).         (17)
```

Unlike bare \(\ell^2\), scalar unit-phase evaluation is bounded on every weighted fiber in `(16)`.
The physical Gamma carrier is

```text
F_q(L)=exp(L/2)tilde F_q(L).                            (17a)
```

Equivalently, `(15)` controls \(e^{-L}dL\), while Gamma current, half-log trace, and weighted-tail
coercivity require \(dL\).  No implication from `(15)` to physical
\(L^2(dL;\ell^1)\) is valid.

This failure persists under an arbitrarily remote high-frequency cutoff.  Fix
\(\Xi>0\), take

```text
c(xi)=1_[Xi,Xi+1](xi),
g=Fourier^(-1)c.
```

Then \(c\in L^2\) is supported entirely above \(\Xi\), and \(g\in L^2\) by Plancherel.  But

```text
g(0)=const_F integral_Xi^(Xi+1)1 dxi !=0.
```

Continuity gives \(|g(r)|\geq |g(0)|/2\) for all sufficiently small \(r>0\), so

```text
integral_0^epsilon |g(r)|^2 dr/r=infinity.              (17b)
```

Thus neither ordinary Plancherel nor exclusion of every bounded frequency interval can supply the
physical log measure.  More sharply, the successor boundary-lock theorem shows that even a
\(C_c^\infty\) full profile with every boundary trace zero can have a high part of this form.  Its
low-frequency component cancels the nonzero high endpoint constant only after exact two-port
matching.

## 4. Suzuki specialization

For the literal multiplier,

```text
L(xi)=log<xi>,

q_a(xi)
 =Re psi(1/4+i xi/2)-log<xi>-log pi
  +Fourier(r_(0,a)'')(xi),

t_a=-sum_(p^j<=exp(2a)) (log p)/p^(j/2)
       [delta_(j e_p)+delta_(-j e_p)].                  (18)
```

The completed exterior-residual theorem gives \(B_\pm\in L^2\).  Choose \(\Xi\) larger if
necessary so that

```text
L_0=inf_(|xi|>=Xi)log<xi> > C_a+M_a.                   (19)
```

Then `(4)` applies.  Root phases can be placed either in the source, as in the predecessor card,
or in the full oriented character

```text
chi_xi(root,nu)=exp[-i xi x(root,nu)].                  (20)
```

This rephasing is unitary coordinatewise and does not change `(4)`--`(17a)`.

The support-pruned weighted state \(P\widetilde F\) and exterior weighted state
\(Q\widetilde F\) separately satisfy the same nuclear bound because coordinate projections are
contractions on \(\ell^1\).  The Feshbach law identifies their exact coupling and prevents
deletion of the \(Q\)-mediated return term.

## 5. Exact frontier movement

Before `(3)`, the carrier had only

```text
L2_frequency(ell1) subset L2_frequency(ell2).           (21)
```

That statement did not authorize a Banach-valued inverse Fourier transform.  Equations
`(3)`--`(17a)` replace it with a source-derived nuclear order:

```text
ell1_seams(L2_frequency)
 -> ell1_seams(L2_position)
 -> ell1_seams(L2(exp(-L)dL))
 -> L2(exp(-L)dL;ell1_seams).                           (22)
```

Thus completed high-frequency data produce a genuine nuclear position carrier and weighted
logarithmic rigging, not only a formal coefficient field.  A physical measure upgrade would be

```text
sum_q integral_0^1 |g_q(r)|^2 dr/r<infinity,            (22a)
```

but it is **not** a theorem of the high-frequency source data.  If absolute valuation evaluation
reconstructs the scalar high part, `(22a)` implies scalar \(L^2(dr/r)\), which forces the two
low-frequency endpoint moments

```text
u_low(+a)=u_low(-a)=0.                                  (22b)
```

These are low-frequency return equations.  Completed-domain regularity, zero half-log trace, and
even boundary-flat \(C_c^\infty\) regularity do not imply `(22b)`.  Plancherel does not supply it.

After `(22a)`, centered profiles must also be shown to satisfy, in their oriented logarithmic
charts, the Gamma boundary equation with:

1. Suzuki's sign-correct positive adjacency \(T_a^\Gamma=-T_a\);
2. exterior-return Feshbach correction or, equivalently, the full unpruned exterior sector;
3. the two completed exterior Hardy sources;
4. the literal cutoff identity.

The nuclear estimate proves all sums converge in the weaker position/weighted-log Hilbert space.
It proves neither `(22a)` nor `(22b)`.  Correct construction must solve low-frequency
divisibility/return and the high-frequency Wiener tail together, then form the matched full
physical profile before Gamma conjugation.

## 6. Hostile audit

1. **No Fourier-type assumption.**  The proof establishes
   \(\ell^1(L^2)\) directly by a word majorant.
2. **No `L2(ell1)` interchange.**  The invalid implication
   \(L^2(\ell^1)\Rightarrow\ell^1(L^2)\) is never used.
3. **No pointwise seam evaluation on `ell2`.**  Fiberwise evaluation is performed only after
   `(16)`, in the weighted chart.
4. **No path cancellation.**  The positive majorant counts every zero/prime word before signs can
   cancel.
5. **No low-frequency division.**  The construction remains restricted to `(19)`.
6. **No measure smuggling.**  \(e^{-L}dL\) control is not relabeled as physical \(dL\) control.
7. **No equation smuggling.**  Physical boundary-log membership is now proved inseparable from
   low-frequency return; matched Gamma intertwining remains open.
8. **No RH claim.**  Low-frequency return, corona no-return, raw Evans injectivity, and producer
   classes P and I remain unresolved.

## 7. Novelty boundary

Neumann series, coefficientwise absolute majorants, Tonelli, and scalar Plancherel are standard.
Corpus and targeted external searches found no source-specific use of the exact Suzuki
prime-valuation inverse to obtain

```text
completed exterior Hardy data
 -> ell1 across inverse-Fourier seam profiles
 -> exact weighted boundary-log rigging
 -> identification of the dr versus dr/r fracture.      (23)
```

The new claim is the conjunction `(3)`--`(23)`: it removes the vector-valued Fourier obstruction.
The successor boundary-lock theorem strengthens the negative side by proving that a free-standing
high-tail physical-log upgrade is false and identifying the exact low-frequency moments it would
silently assume.  Priority remains unverified.

The boundary Hardy literature does not close `(22a)`.  Dyda--Jarohs--Sk,
*The Dirichlet Problem for the Logarithmic p-Laplacian*, arXiv:2411.11181, proves for \(p=2\)
the standard logarithmic-form estimate

```text
integral |u(r)|^2 log(1/delta(r)) dr
 <=C[logarithmic jump energy+||u||_2^2].
```

In the boundary variable \(r=e^{-L}\), its left side is
\(\int |F(L)|^2 L e^{-L}dL\), still exponentially weaker than
\(\int|F(L)|^2dL=\int|u(r)|^2dr/r\).  Iterating logarithmic form regularity therefore does not
silently supply the carrier measure required here.

## 8. Lean boundary

The positive nuclear word theorem uses literal completed Hardy amplitudes, valuation convolution,
an infinite Neumann series, scalar Plancherel, and nonlinear charts; those source objects are not
yet present together in Lean.  The load-bearing obstruction exposed here is now formalized in
`SuzukiPhysicalLogBoundaryMomentLock.lean`: continuous physical-log mass forces boundary
vanishing, and a nonzero low-frequency boundary moment forbids physical-log integrability of the
high part.  This is the exact analytic implication used to reject the old sequential interface.

## Gates

- [x] prove coefficientwise Neumann word majorant
- [x] upgrade `L2(ell1)` to `ell1(L2)`
- [x] pass every coefficient through scalar Plancherel
- [x] prove unitarily weighted oriented boundary-log chart
- [x] obtain `L2(exp(-L)dL;ell1) subset L2(exp(-L)dL;ell2)`
- [x] prove a free-standing high-tail `dr/r` upgrade is false
- [x] identify its exact low-frequency boundary-moment lock
- [x] formalize the boundary-moment obstruction unconditionally in Lean
- [ ] solve coupled low/high two-port return and boundary moments
- [ ] intertwine centered profiles with exact Gamma boundary operator
- [ ] identify vector half-log trace with scalar completed traces
- [ ] apply physical-tail coercivity to trace-zero completed state
- [ ] prove corona no-return and raw Evans injectivity
- [ ] RH

### The nuclear theorem, the unitary chart, and the sharp obstruction are all formal

`RHTower/SuzukiWienerNuclearBoundaryCarrier.lean`, on top of the Wiener stack
(`HTGeometry/DiscreteL1Convolution.lean`, `RHTower/SuzukiWienerNeumannMajorant.lean`,
`RHTower/SuzukiWienerMixedNormCarrier.lean`) and mathlib's `L²` Fourier isometry:

- `tsum_eLpNorm_wienerSingleRoot_le` — **`(1)`–`(3)`**: the valuation sum of `L²` norms of the
  Neumann-inverse single-root carrier is at most `(L₀ - (C+M))⁻¹ ‖B‖₂` — the exact constant, via
  `discreteConv_single_atom` (a one-atom source reads the kernel at the shifted coefficient),
  the frequency-independent Neumann coefficient bound, translation invariance of the kernel mass,
  and the exact arithmetic `wienerInverseMass_eq`
  (`L₀⁻¹(1-(C+M)/L₀)⁻¹ = (L₀-(C+M))⁻¹`).
- `tsum_eLpNorm_wienerTwoRoot_le` — **`(4)`**: two oriented roots pay the inverse margin once
  each.  The word expansion behind both is the stack's `enorm_discreteConvPow_le` — exactly the
  card's `(8)`–`(9)` majorant with `∑_ν (μ^{⋆k})_ν = (C+M)^k` an equality
  (`discreteMass_discreteEConvPow`), and the grade/coordinate interchange is Tonelli in `ℝ≥0∞`.
- `integral_sq_fullLogChart` — **`(13)`–`(14)`**: the half weight `e^{-L/2}` makes `r = e^{-L}`
  an `L²` isometry of the whole positive axis onto `L²(dL)` — the unitarily weighted oriented
  boundary-log chart.  With the norm-preserving steps (Plancherel `Lp.fourierTransformₗᵢ`,
  translation) this gives `(12)`–`(17)`'s norm chain; the `ℓ¹(L²) ⊂ L²(ℓ¹) ⊂ L²(ℓ²)` inclusions
  are the stack's `summable`/`norm_tsum` layer.
- `lintegral_div_highBandPosition_eq_top` — **`(17b)`**: the unit frequency band at any height
  `Ξ` has an inverse transform that is continuous (`continuous_highBandPosition`) with value one
  at the origin (`highBandPosition_zero`), so its squared modulus against `dr/r` diverges on
  `(0, ε)`.  **The free-standing high-tail `dr/r` upgrade is false**, exactly as the card
  states; only the coupled boundary-moment lock (already formal in
  `SuzukiPhysicalLogBoundaryMomentLock.lean`) can supply the physical measure.

All audit to `[propext, Classical.choice, Quot.sound]`; umbrella wired.
