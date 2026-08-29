# Ultrametric thermal Mahler hypertranscendence

- **ID:** `ultrametric-thermal-mahler-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / PHYSICAL-MATHEMATICAL BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [PARENT-DERIVED] [NOVELTY UNVERIFIED]`
- **Scope:** general hypertranscendence in a source-natural quantum spectrum; no RH or
  distinguished special-function input
- **Statement:** The reduced one-particle heat trace of the exact Neumann-to-Dirichlet spectrum
  on the (p)-adic unit circle is the unique formal germ fixed by a finite polynomial boundary
  defect and one ultrametric scale constraint.  It is hypertranscendental, although the spectral
  zeta function of the same positive spectrum is differentially algebraic.

## Physical source

Let (p\ge 2) be prime.  Huang and Jepsen compute the positive spectrum of the
Neumann-to-Dirichlet operator on the (p)-adic unit circle, up to an energy scale
\(\varepsilon>0\), as

```text
E_n = epsilon p^n,                 n >= 0,
rho(0) = p-2,
rho(n) = (p-1)^2 p^(n-1),         n >= 1.                 (1)
```

There is also a zero mode, which is omitted from the reduced trace.  Formula `(1)` is not a
chosen geometric tower: it is the eigenvalue and character-multiplicity theorem for the boundary
operator.  The same paper associates harmonic oscillators to these modes and studies the full
many-body partition function.  The result below concerns the canonical one-particle trace of this
already-derived operator.

Put (w=e^{-\beta\varepsilon}), (0<|w|<1), and define

```text
K_p(w) = Tr' exp(-beta D_p)
       = (p-2) w + (p-1)^2 sum_(n>=1) p^(n-1) w^(p^n).    (2)
```

The series converges normally on compact subsets of the unit disc.  Indeed, for every
(0<r<1), the successive majorant ratio is

```text
p r^((p-1)p^n) -> 0.
```

Thus `(2)` defines a holomorphic germ and its displayed power series is its Taylor series.

## Exact constraint theorem

The trace satisfies

```text
K_p(w) = (p-2)w + w^p + p K_p(w^p).                       (3)
```

**Proof.** Substitution into `(2)` gives

```text
p K_p(w^p)
  = p(p-2)w^p
    + (p-1)^2 sum_(n>=1) p^n w^(p^(n+1)).
```

The coefficient of (w^p) after adding the boundary term in `(3)` is

```text
1 + p(p-2) = (p-1)^2,
```

and reindexing the remaining sum gives the coefficient
((p-1)^2p^{n-1}) at every (w^{p^n}), (n\ge2).  All other positive coefficients vanish.
This is `(2)`.  ∎

The constraint is rigid.  If two formal series satisfy `(3)`, their difference (Y) satisfies

```text
Y(w) = p Y(w^p).                                           (4)
```

The constant coefficient in `(4)` is zero because (p\ne1).  A coefficient whose index is not
divisible by (p) is zero.  Every remaining positive index descends finitely under
(m\mapsto m/p) to an index not divisible by (p).  Hence every coefficient of (Y) is zero.
Therefore `(3)` determines the complete thermal trace; it is a static constraint, not an
evolution law.

## Hypertranscendence theorem

Equation `(3)` is an affine Mahler equation over \(\mathbb C(w)\).  It can be converted to a
homogeneous scalar linear Mahler equation of order two by applying a first-order Mahler operator
that annihilates its nonzero rational forcing polynomial

```text
B_p(w) = (p-2)w + w^p.
```

The support of (K_p) contains every (p^n) for (n\ge1), with nonzero coefficient, and has
arbitrarily long zero gaps.  A rational power series has an eventually linearly recurrent
coefficient sequence, so it cannot have this support.  Thus (K_p\notin\mathbb C(w)).

The Mahler case of the Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental theorem now
implies

```text
K_p is hypertranscendental over C(w)
for the Euler derivation w d/dw.                            (5)
```

Adding back the single zero mode changes the trace by the constant (1), a differentially
algebraic term, and therefore does not change `(5)`.

## Thermal--Dirichlet observation fracture

The reduced spectral zeta function of the same positive spectrum is

```text
zeta_p(s)
  = (p-2) + (p-1)^2 sum_(n>=1) p^(n-1) p^(-ns)
  = (p-2) + (p-1)^2 p^(-s) / (1-p^(1-s)).                 (6)
```

Consequently \(\zeta_p(s)\) is rational in (u=p^{-s}), and hence differentially algebraic in
(s).  Equations `(5)` and `(6)` prove an exact reporter split:

```text
the Laplace/thermal reporter is HT;
the Dirichlet reporter is DA.                              (7)
```

The spectrum alone therefore has no absolute differential-algebraic type.  Hypertranscendence is
a property of the source together with its observation coordinate and transform.  The Mellin
relation between heat trace and spectral zeta is an infinite integral transform; `(7)` shows that
it cannot be replaced by a finite differential-algebraic observation equivalence.

Every finite mode truncation of `(2)` is a finite exponential sum in \(\beta\), hence
differentially algebraic.  Thus `(5)` is an exact certificate of irreducibly infinite
ultrametric field content.  Any finite change of the low-energy spectrum adds a finite
exponential sum and leaves hypertranscendence unchanged.

## QFT realization boundary

The operator in `(1)` supplies a source-natural quantum spectrum and the one-particle thermal
trace is a physical observable.  A free relativistic field on ordinary Euclidean spacetime with
this operator as a positive internal mass-squared operator has covariance

```text
(-Delta_x + m_0^2 + epsilon D_p)^(-1).                     (8)
```

Mode decomposition turns `(8)` into a positive direct sum of ordinary massive free covariances.
It is therefore reflection-positive in the Archimedean time coordinate and reconstructs a local
free field there.  Its Schwinger heat trace factorizes into the ordinary spacetime heat factor and
the ultrametric trace `(2)`, so the HT factor is not inserted as initial data or as a chosen
response function.

This does **not** yet construct an interacting Lorentzian (p)-adic string or prove locality in an
ultrametric internal coordinate.  The physical result is an exact free-field/spectral realization.
The interaction-preserving selection theorem remains open.

The companion theorem
`de-sitter-ultrametric-detailed-balance-hypertranscendence.md` supplies an exact operational
cosmological reporter for the same spectrum.  De Sitter KMS detailed balance evaluates `(2)` at
(w=\exp(-2\pi\varepsilon/H)), so the degeneracy-weighted trace of channelwise detector rate ratios
is hypertranscendental in both the Boltzmann coordinate and locally in (H).  It does not upgrade
the present free-field model to an interacting cosmological field theory: the ultrametric tower
is carried by the ideal detector apparatus.

The companion theorem
`ultrametric-one-loop-resolvent-hypertranscendence.md` instead puts the same spectrum inside the
field Hessian.  Its first ultraviolet-finite mass susceptibility satisfies a contractive affine
scale equation with a two-shell rational defect and is hypertranscendental.  For each Euclidean
de Sitter harmonic this gives an exact source-internal one-loop reporter.  The full de Sitter
harmonic sum is not covered by that theorem, and
`gaussian-influence-wick-kolchin-collapse.md` proves that the resulting Gaussian vertex hierarchy
still has zero interaction-relative profile.

The finite prefixes of `(2)` and their exact next-shell scale residual are formalized in
`../../3-formalized/not_new_scientific_knowledge/ultrametric-thermal-finite-resolution-residual.md`.
This gives a cofinal family of finite tests for the source constraint while preserving the sharp
fact that no one finite prefix is hypertranscendental.

## Anti-theatre and novelty verdict

The exponentially spaced spectrum, its degeneracies, the ultrametric oscillator model, and its
thermodynamics are parent literature.  The rational-or-HT theorem is also established.  Combining
them to obtain `(5)` is a rigorous physical bridge but is a short consequence once the two parent
theories are placed together.  It is therefore not labelled new scientific knowledge.

The result advances the foundational program in two ways:

1. it removes the previously chosen geometric spectrum and chosen residues from the Mahler
   collider toy model in an exact ultrametric quantum system;
2. it isolates the new open invariant: survival of the thermal Mahler constraint under a
   source-natural interacting, reflection-positive completion.

The one-loop resolvent companion now supplies a source-natural Gaussian completion.  Consequently
the remaining adjective in item 2 is exactly **interacting**, not merely field-theoretic.

## Primary sources

- A. Huang and C. B. Jepsen, *A glimpse into the Ultrametric spectrum*,
  <https://arxiv.org/abs/2601.03738>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin,
  *Hypertranscendence and linear difference equations*,
  <https://arxiv.org/abs/1910.01874>.
- J. Pearson and J. Bellissard,
  *Noncommutative Riemannian Geometry and Diffusion on Ultrametric Cantor Sets*,
  <https://arxiv.org/abs/0802.1336>.
- M. L. Mendoza-Martinez, J. A. Vallejo, and W. A. Zuniga-Galindo,
  *Acausal quantum theory for non-Archimedean scalar fields*,
  <https://arxiv.org/abs/1805.08613>.

## Lean status

Formalized unconditionally in `formal/GaloisForLFunctions/HTGeometry/`, for an arbitrary field of
characteristic zero and every integer `p ≥ 2`.  The Adamczewski–Dreyfus–Hardouin theorem is **not**
imported: the hypertranscendence is proved from the corpus's own automorphism-family Ostrowski
criterion, with the Mahler pair made to commute by the twisting coordinate.

| Card statement | Lean theorem |
|---|---|
| `(2)` the reduced trace `(p−2)w + (p−1)²Σ_{n≥1}p^{n−1}w^{p^n}` | `traceSeries`, `coeff_traceSeries_pow` (`MahlerTraceGerm`) |
| `(3)` `K(w) = (p−2)w + w^p + p·K(w^p)` | `traceSeries_mahler_equation` |
| `(4)` rigidity: the constraint has a unique solution | `traceSeries_unique` (`MahlerTraceCard`) |
| `K_p ∉ ℂ(w)` (lacunary support) | `traceSeries_not_ratFunc` |
| `(5)` **`K_p` is hypertranscendental over `k(w)` for the Euler derivation `w d/dw`** | `hypertranscendentalOver_traceSeries_kw` |
| the same, over the perfect two-variable base | `hypertranscendentalOver_traceSeries_euler`, `hypertranscendentalOver_traceGerm` |
| `(6)` `ζ_p(u) = (p−2) + (p−1)²u/(1−pu)` | `zetaSeries_eq_algebraMap` (`UltrametricSpectralZeta`) |
| `(7)` the Dirichlet reporter is DA while the thermal reporter is HT | `differentialAlgebraicOver_zetaSeries` together with `hypertranscendentalOver_traceSeries_kw` |

Supporting layers, all new in this pass: `MahlerPerfectBase` (the `p`-perfect rational base, on
which the substitution is an automorphism), `MahlerPerfectEmbedding`, `MahlerPerfectDerivation`,
`MahlerCommutingDerivation` (`δ = h⁻¹·θ` commutes with `σ` exactly), `MahlerPerfectDifferentialBridge`,
`MahlerOstrowski` (the criterion in the Mahler model), `MahlerRationalNoTelescoper` (no rational
solution of a two-term inhomogeneous Mahler equation unless the resonance `λa+b` vanishes),
`MahlerIncrementJets`, `MahlerPerfectNoTelescoper`, `MahlerBaseNoTelescoper`,
`ScaledDerivationTransfer`.

`#print axioms hypertranscendentalOver_traceSeries_kw` → `propext, Classical.choice, Quot.sound`.

The physical discussion (`(8)`, the free-field realization, and the open interacting completion)
is context, not a mathematical claim of the card.
