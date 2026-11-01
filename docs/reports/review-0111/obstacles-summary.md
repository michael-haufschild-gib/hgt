# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `fe2f109c3e`. Evidence: `[L]` Lean
source read (statement or module docstring); `[M]` frontier map or killed-routes entry, Lean not re-read; `[D]`
derived here from `[L]`, not formalized.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = #` distinct zeros right of the
   line. Glued at any place it is `κ + 1`. It is the Hodge defect on `v₁^⊥` and the number of zeros
   moved by `σ(ρ) = 1 − ρ̄`. RH ⇔ `σ` fixes every zero ⇔ every Hecke translation is a similitude of
   the collided form [L].
2. **Kernel, coupling and window error are one quantity.** RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` [L]. The
   inter-tower coupling `K(uv) − K(u) − K(v) + K(1)` is at most four times the kernel, and on two
   dense lattices the kernel deviation is at most half the coupling. The local Hyers–Ulam constant
   is `3`; no Diophantine input is needed [L]. One lattice `⟨p⟩ × ⟨q⟩` decides RH, and the coupling
   growth rate is the zero width [L]. On the integer cone `a, b ≥ 0`, boundedness gives RH unless
   the zero width is not attained [L]. Through the explicit formula, `K_ζ(u)` is the normalized
   smoothed prime error in a fixed-length multiplicative window at `u` [D]. The coupling target is
   therefore window PNT at square-root precision, and it is not softer than RH.
3. **The complete form on packets is an identity.** On atoms with amplitudes `F(n)/√n` the prime
   form is `Σ F²/n·(ψ₁(⌊N/n⌋) + log n) − J_N(F)`. This is exact because `Λ ∗ 1 = log`. At strict
   separation the counterterm `log N − γ` cancels the diagonal, leaving a remainder `R → 0` and a
   floor defect in `[0, log 2]` [L]. At every overlap:
   `E = J_N + ½A_N + bounded diagonal − Σ d_n F² + (center − far cross + pole error + near overlap)`.
   Here `A_N ≥ 0` is the affine incidence energy and the shell degree `d_n` is the only term that
   grows with the overlap [L]. On prime-incidence packets every jump is an incidence event, and the
   complete-period affine energy is an exact CRT sum of squares [L].
4. **Three exponents organize the sign problem.** The universal method proves positivity on all
   vectors for `c ≤ (log N)^{1/19}`. There the residual `c⁵/log N` meets the squared floor `c⁻¹⁴`
   [L]. Paying the shells apart from the pole is sharp at `c²/ε`, i.e. `c⁹` at the reserve fraction
   `c⁻⁷`. This forces confinement at `exp(Cc¹⁶)`, so the exponent `16` is intrinsic [L]. Paid
   jointly with the pole, the shells cost only `O(G(c + log N))` on the top band [L]. From
   `c⁴/log N → ∞` on, positivity is RH for every `C²` profile [L].
5. **Localization is the confinement.** Every nonpositive unit vector lies within `η` of a finite
   conductor sector. At growing overlap the sector has `log P ≍ c¹⁶/η` [L]. This is useful only
   below `(log N)^{1/16}` [D].
6. **The edge is a crossing.** At a finite first edge the complete form is PSD with a zero mode
   [L]. No edge ⇔ bounded coupling ⇔ RH [L]. Under ¬RH the tilted edge lies in
   `[(log N)^{1/19}, 2(log N)^{¼+}]` infinitely often [D]. An isolated off-line pair at depth `δ` and
   height `ξ` in an RVM background is seen at aperture `a` iff `sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)`
   [L]. The corresponding law at atomic resolution is not derived.
7. **The Hecke defect is a conjugate-diagonal functional.** `E_γ(L)` is linear in the divisor but
   non-holomorphic in `ρ`. At log scale the prime polynomial carries `O(1/log T)` of it [L]. A
   configuration with RVM counts and all of ζ's critical zeros violates every
   explicit-formula bound on `E` [L]. A fixed-scale bound ⇔ the log corridor ⇒ Lindelöf (≥qRH)
   [L]. One constant across all dyadic scales ⇔ RH [L].
8. **Selection of ζ among prime flips is closed; selection does not produce sign.** Every
   nontrivial prime-set flip is separated by the ordinary or the two-adic atomic margin, with no
   density assumption [L]. The diagonal coupling recovers any flip set prime by prime [L]. Gauge
   fixing by the successor works on entrywise signs [L]. Every selector is a margin or index on a
   partial form.
9. **Finite index has a classification at the bounded and index-one levels.** Bounded finite-index
   kernels on free abelian groups are PD minus `κ` unitary characters. At index one there is a
   unitary-or-hyperbolic dichotomy. Finite index plus cyclic subexponential growth gives polynomial
   growth of degree `≤ 2κ` [L].
10. **Reformulations do not soften.** The Künneth defect is `2n₊n₋` at every horizon [L]. A
    crossing-free deformation exists iff the form is positive [L]. The axial→coupled homotopy has
    the full index for every `t > 0` [L].
11. **Falsification certificates have no converse.** RH ⇒ `i` is the unique upper periodic point of
    the Xi Donoghue map; reversed Xi Jensen sections have only simple real roots; Ritz branches move
    left [L].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit horizon `N₀` for the `1/19` positivity theorem | HF, SRT, AIP, ACS, SC | proved mechanism; constants |
| A2 | Propagate `1/19` into the EHT edge window and crossing theorem (Lean uses `1/59`) | EHT, HF, SRT, SC | composition of proved theorems |
| A3 | Edge dictionary: compose the aperture visibility law `S_δ(a) > L` with the synthesis receivers to locate the overlap at which one off-line pair becomes visible to the tilted, sinc and Steklov families | HF, SRT, AIP, RW, SC, EHT | explicit model computation with proved ingredients |
| A4 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` | SRT, HF | synthesis error at one explicit scale |
| A5 | Size of the shell degree `d_n` at overlap `c`; comparison with `½A_N` and the pole term | HF, AIP, SRT, ACS | explicit arithmetic sums; no Lean bound exists |
| A6 | Compare CSAR rigidity and relative residuals with the complete energy through the packet identity, on fixed and slowly growing packets | HF, SRT, AIP, ACS | fixed-dimensional comparison |
| A7 | Universal-regime constants for other profiles without real Fourier zeros | HF, SRT, AIP | rerun of a proved argument |
| A8 | Explicit capture stage for complete-cell indices | AID, HF, CHMD | compactness transfer (card in progress) |
| A9 | Stronger subconvexity exponent for the heat floor `2/3` | WD, LA | known exponents |
| A10 | Certified de Bruijn–Newman bound (Polymath15, corpus normalization) as an index-one time | SC-heat, WD | certified numerics |
| A11 | One Lean statement: `ΔO = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf | WD, SRT | composition of `CollisionChargeIncrements` and `BacklundLindelofConverse` |
| A12 | Computable stopping prefix (interval bounds instead of compact minima) | WD | interval arithmetic |
| A13 | Same-order mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A14 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer | WL | Farkas / rounding |
| A15 | `𝔽_q(X)` calibration: higher-degree local walls, global Hecke product formula, archimedean Weil state of a curve | SC, ACS, RIT | curve coupling and curve edge proved |
| A16 | `𝔽₃` loop chain: Bruhat unfolding and constant-term evaluation | ACS | loop-group foundations in Lean |
| A17 | Certified Weil positivity past the two-prime aperture `r ≥ ½ log 3` | RW, EWU, OWU, CHMD | certified numerics |
| A18 | Theta Hankel rank-8 strictness, ranks 9 and 10 | TH | finite computations |
| A19 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF | effectivise eventual statements |
| A20 | The nine atom-dominated moduli of the collar shift | ACT | finite case analysis |
| A21 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A22 | Higher-iterate traces of the regularized Gauss–Mayer operator | PM | operator already nuclear with Fredholm determinant |
| A23 | Lean formalization of the WD mollified-corridor / finite-theta card in `2-fully-proven` | WD | paper proof exists |
| A24 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ (test of 2.4) | LA, 2.4 | certified computation |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH** (Lindelöf + zero-free half-plane); **LH** (Lindelöf); **sub**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| Σ-1 | Positivity on `v₁^⊥` across the detection edge (no zero mode of the overlap flow) | RH | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| Σ-2 | Signed low-band estimate beating the residual-versus-floor exponent `19` | sub | same |
| Σ-3 | Joint shell–pole payment inside the all-vector reserve, beating the confinement exponent `16` | sub; RH at RH-complete overlap | same |
| Σ-4 | Low-conductor spans below `(log N)^A` | sub | HF, SRT, AIP, ACS |
| Σ-5 | Conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) | sub | HF, SRT, AIP, SC |
| Σ-6 | Profile transfer between the tilted spline and `C^∞` receivers | sub | HF, SRT, AIP, ACS |
| Σ-7 | Polylogarithmic localization beyond `(log N)^{1/16}` | sub | HF, SRT, AIP, ACS |
| Σ-8 | Joint payment of non-arithmetic Gamma graph + signed diagonal + roots + poles on growing packets | sub | CHMD, AID, HF |
| Σ-9 | Exact sum-of-squares identity for Weil's dilation form on the boost hyperplane or on one two-prime lattice | RH | SC, HF, RIT |
| Σ-10 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| Σ-11 | All-rank / all-degree theta, heat, Jensen and PF signs | RH | TH, LA, HCF, PA, GTA |
| Σ-12 | Arithmetic index ceiling uniform in resolution | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | CHMD, SRT, WD, AID, SC |
| Σ-13 | Collision charge `< 2` per window; no heat-index jump; every `Λ_X = 0` | RH | WD, TG, SC-heat |
| Σ-14 | `ΔO = o(log T)` | LH | WD, census |
| Σ-15 | Cumulative charge `O(T) = o(N(T))` | sub | WD, census |
| Σ-16 | Subcritical heat count `a < 1` | sub | WD, SC-heat |
| Σ-17 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL |
| Σ-18 | Spectral reality of a realized operator | RH | RN, PTR, W1C, PM |
| Σ-19 | A source-defined noncrossing path to an index-one model | RH | SC, TG, WD |
| Σ-20 | Emptiness of the loop-Eisenstein band poles | RH | HF, ACS, SC |
| Σ-21 | Classification of unbounded finite-index kernels of higher index | sub | HKT, SC, ACS |

### Π — precision
| # | Problem | Strength | Routes |
|---|---|---|---|
| Π-1 | Unconditional one-sided count at square-root precision | RH | WL, PBM, RB, JAS, CTF |
| Π-2 | Square-root window PNT at every height (= bounded kernel = bounded coupling) | RH | SC, ACS, HKT |
| Π-3 | Cone attainment: bounded integer-cone coupling excludes the unattained-width case | sub | SC |
| Π-4 | `ε`-uniform producer | sub / RH | WL |
| Π-5 | Moving-scale half-power Möbius cancellation; near-band energy `O(N^{3/2+ε})` on a positive-power band | RH; ≥qRH | MC |
| Π-6 | Unconditional Serre-dual `h⁰` with quadratic RR | RH | ACS, RIT |
| Π-7 | Arithmetic access to the conjugate diagonal: bound the Hecke defect with an input beyond counts and the linear explicit formula | method; RH at all dyadic scales | WD, census, HEF |
| Π-8 | Hecke defect at doubly-logarithmic scale `o(log|γ|)` | sub | WD |
| Π-9 | Fixed-scale Hecke defect `E_γ(c log T) = O(1)` | ≥qRH | WD |
| Π-10 | 100% census; pointwise local count | sub | ACS, SRT, IGP, LA, WD |
| Π-11 | Gap-independent detection scale for collision readings | sub | WD |
| Π-12 | Pointwise heat horizon constant `< ½` | ≥qRH | WD, LA |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| Γ-1 | Zero-independent selection at the trivial gauge point | RH | MC, BAG, XN, PM |
| Γ-2 | Frobenius at infinity: a correspondence acting as conjugation on the divisor | RH | HF, PL, CDG, WD, EHT |
| Γ-3 | Pre-divisor sections / potentials coupled to Ξ | RH | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF |
| Γ-4 | A conformal correspondence over ℤ with factor `≠ 1` | RH | ACS |
| Γ-5 | A selector that is also a positivity producer for the complete form | RH | HF, SRT, AIP, ACS, SC |
| Γ-6 | Unimodular gauges with `S_N/H_N → 1`; functional-equation twins without Euler product | sub | HF, ACS, AIP, SRT, SC |
| Γ-7 | Half-parameter cusp selection / zero-selecting scattering rigidity | RH | PM |

## 2.3 The three questions to answer next

**Q1. Where is the edge of one off-line zero?** For a model configuration (an RVM background of
critical zeros plus one off-line pair of depth `δ` at height `ξ`), determine the least overlap
`c(N; δ, ξ)` at which the complete Weil family of the tilted spline, and of the sinc and Steklov
profiles, acquires a zero mode on `v₁^⊥`.
- What is in hand: the aperture visibility law `S_δ(a) > L` [L]; the synthesis receivers that turn
  a multiple `K` of the critical overlap into a visible aperture `½ log K − O(1)` [L]; the crossing
  theorem [L]; positivity to `(log N)^{1/19}` [L]; the edge ceiling `2(log N)^{¼+}` [L].
- Why first: the answer decides what the Σ problem is. If a fixed off-line zero is invisible below
  exponent `¼`, the interval `[1/19, ¼)` is estimate territory. RH is then concentrated in the
  constant at exponent `¼`, and pushing the universal regime is the right work. If a zero is
  visible earlier, every universal exponent is an unconditional zero-free statement. Then the
  universal method is information-limited, and the ceiling `19` or `16` is the place where zeros
  would appear.
- Character: mostly composition of proved statements (A3), with one genuinely open step: the
  interaction of the off-line pair with the critical background at atomic resolution.

**Q2. Which mechanism passes the two universal ceilings?** (a) Is there a signed (quadratic-form)
estimate on the low conductor band whose residual cost relative to the floor grows slower than
`c¹⁹/log N`? (b) On `v₁^⊥`, does `Σ d_n F(n)² ≤ J_N(F) + ½A_N(F) + (pole and boundary terms) +
C(c)·Σ F(n)²/n` hold with `C(c)` of degree `< 9`? This joint shell–pole payment is what removes the
confinement exponent.
- What is in hand: the packet identity at every overlap [L]; separate payment sharp at `c²/ε` [L];
  joint top-band coefficient `O(G(c + log N))` [L]; mean-zero periodic perturbations
  `O(BqUG(1 + log N))` [L]; quadratic confinement and reverse gap [M]; prefix/terminal reserve files
  [L].
- Why: these are the only two obstructions between the proved regime and the synthesis threshold.
  Part (b) is a Poincaré-type inequality for the affine–dilation graph of `[1, N]` with mass
  `d_n`, the only overlap-growing term of the identity.
- Character: open mathematics at strength **sub**, as long as the target stays below the synthesis
  threshold.

**Q3. Is there arithmetic access to the conjugate diagonal?** The Hecke defect pairs each zero with
its conjugate. It is invisible to counts and to the linear explicit formula: the cluster
configuration with RVM counts violates every such bound [L]. (a) Does that cluster configuration
violate the two-point statistics proved in the corpus (Montgomery pair correlation for `α < 1`,
triple and quadruple form factors)? (b) Is there a quadratic, prime-pair explicit formula for the
translates of the collided form whose error is uniform across dyadic scales?
- What is in hand: master inequality for fibre multiplicity [L]; prime-polynomial self-absorption
  [L]; fixed-scale TFAE and corridor [L]; dyadic RH equivalence [L]; Montgomery leading order and
  higher form factors [M].
- Why: RH ⇔ one constant bounds the Hecke defect at every dyadic scale [L]. The linear tools are
  proved insufficient, so the next input must be quadratic in the primes. A positive answer to (a)
  identifies that input and joins WD to the census at the bandwidth-one barrier. A negative answer
  shows that two-point data is blind too, so WD needs Euler-product structure beyond all
  correlation statistics.

## 2.4 A wildly different route

**Rigidity of `(×p, ×q)`-systems is not a separate route.** Suppose a measure-preserving system
reproduced the coupling as `⟨F∘u, F∘v⟩`. Its correlations would be bounded by `‖F‖²`, so the
coupling would be bounded, and RH would follow from the bounded-coupling theorem [L]. Conversely,
under RH, `K_ζ` is positive definite and the Gaussian construction realizes it. A positive
realization is the sign itself; a rigidity theorem has nothing left to do.

**Candidate: manifest positivity of Ξ by total positivity.**

*Receiver (in the corpus).* RH ⇔ every slice coefficient sequence of Ξ is a Pólya frequency
sequence [L: `riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff`]. The centre sequence is PF₃₇,
certified [L: `xi_centre_pfSeq_thirtySeven`]. Classically, a positive sequence is PF∞ iff its
generating function has the Edrei form `C e^{γz}∏(1 + α_iz)/∏(1 − β_iz)`. For an entire function of
genus zero this means only negative real zeros.

*Producer (absent from the corpus).* Total positivity by counting. By Lindström–Gessel–Viennot,
every minor of the path matrix of a planar network with nonnegative weights counts families of
non-intersecting paths. A network whose path matrix is the Toeplitz matrix of Ξ's Taylor data
certifies every minor of every order at once. There is no growing family, no floor, and no limit.

*Why it avoids the three walls.*
- **Σ**: the edge principle concerns estimates on growing families against a vanishing ground
  energy. A counting certificate is an identity and has no edge.
- **Π**: no prime statistic enters; the certificate counts paths, not primes.
- **Γ**: selection has to sit in the source. The natural source is the product structure of the
  theta function. `θ₃` is an eta-quotient (Jacobi triple product), and the kernel `e^{−πn²x}` is
  totally positive as an exponential kernel in `(−πn², x)` (Karlin's composition formula). Product
  formulas are the elementary building blocks of planar networks: each factor `(1 + αz)` is one.
  Heuristic: functional-equation twins without an Euler product, and Epstein zeta functions with
  off-line zeros, are not built from a one-variable triple product.

*Its own wall.* The Taylor coefficients of `Ξ(√−z)` are normalized moments `∫ u^{2k}Φ(u) du` of
Riemann's kernel `Φ`. The passage `θ → Φ → moments` uses differentiation and the substitution
`x = e^{2u}`, and neither preserves total positivity in general. No total-positivity-preserving
chain from the triple product to the moments is known. First steps:
- compute Toeplitz minors of the centre sequence beyond order 37 and their minimal normalized
  values (A24);
- decide whether `Φ`, or `x ↦ Φ(½ log x)`, is a Pólya frequency function, or is sign-regular of
  some order;
- look for a planar network or a Schur-positive model for the first moments that is built from the
  triple product.

This is the only candidate seen whose producer type is foreign to every route and whose selection
mechanism is a structural property of the source rather than a margin.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — universal positivity up to the synthesis threshold
**Question.** Prove positivity of the complete Weil matrix of a matched profile on `v₁^⊥` for all
`1 ≤ c ≤ (log N)^{¼}/ω(N)`, for some `ω(N) → ∞`. As a first stage, prove it beyond the confinement
exponent `1/16`.
- **Below RH**: positivity requires `c⁴/log N → 0`, whereas every RH receiver of this family needs
  `c⁴/log N → ∞` [L]. If Q1 places the edge of a fixed off-line zero at exponent `¼`, the statement
  is consistent with off-line zeros. If Q1 places it lower, the statement is an unconditional
  zero-free region, which is a breakthrough of its own.
- **Advance**: it needs both mechanisms missing from the universal method: a signed low-band
  estimate beyond `19`, and joint shell–pole payment beyond `16`. It collapses the edge window to
  `[(log N)^{¼}/ω, 2(log N)^{¼+}]`. The sign problem then sits at one exponent, and the remaining
  question is a constant.

### 2.5.2 Route SC — the integer-cone rate theorem
**Question.** Prove that `|C_{K_ζ}(p^a, q^b)| ≤ C e^{σ(a log p + b log q)}` for all `a, b ∈ ℕ` implies
`Re ρ − ½ ≤ σ` for every zero, with no attainment hypothesis on the zero width.
- **Below RH**: a pure implication about expansions in two incommensurable characters. It locates
  no zero.
- **Advance**: SC's target moves to the semigroup of integers `p^a q^b` (the Euler-product side,
  no inverse scales), as an exact RH and rate receiver. The cone theorem proves the deepest-zero
  case through a generating function with a double pole excluded by the irrationality of
  `log p/log q` [L]. The open step is the case where zeros accumulate at the maximal real part
  without attaining it: a Tauberian or almost-periodic replacement for the deepest-zero
  extraction.

### 2.5.3 Route WD — sublogarithmic multiplicity of zeros
**Question.** Prove `E_γ(¼ log log|γ|) = o(log|γ|)` uniformly in `γ`, and hence that every zero
has multiplicity `o(log|γ|)`.
- **Below RH / quasi-RH**: a pointwise multiplicity statement. It implies no Lindelöf statement
  and no zero-free region.
- **Advance**: the unconditional bound `m(ρ) ≪ log|γ|` has resisted improvement without RH. The
  master inequality turns the doubly-logarithmic Hecke defect into a multiplicity bound with no
  prime cancellation [L]. It would be the first unconditional output of the conjugate-diagonal
  object, and gives `ΔO(T) ≤ o(log T)·n_off(T)`. The log-scale no-go (cluster configuration) does
  not reach this scale.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a Liouville property for the Weil operator
**Question.** Let `x ∈ v₁^⊥` be a zero mode of `W_{c,N}` at the first overlap where positivity
fails. Must its dilation-jump energy `J_N` and affine incidence energy `A_N` vanish? If so,
successor/dyadic rigidity makes it the constant packet, which `v₁^⊥` excludes.
- **Why it opens the path**: positivity holds at small `c` [L], and a finite edge is a zero mode of
  a PSD form [L]. So RH ⇔ the overlap flow never has a zero mode on `v₁^⊥` [D]. A zero mode
  satisfies the linear arithmetic equation `W_{c,N}x = 0` on `[1, N]`. The packet identity writes
  `W` as incidence squares, a bounded diagonal, the shell degree and boundary terms [L]. The joint
  kernel of successor and dyadic incidence is the constant packet [M]. A Liouville theorem
  ("Weil-harmonic packets on `v₁^⊥` are trivial") turns the sign into a kernel statement, which is
  qualitative, holds at the edge, and needs no estimate against the ground energy.

### 2.6.2 Route SC — a sum-of-squares identity on the minimal carrier
**Question.** On one two-prime lattice `⟨p⟩ × ⟨q⟩`, the smallest object carrying the full index, is
Weil's dilation form on boost-mass-zero vectors a sum of squares of coupling differences
`(T_{p^a} − 1)(T_{q^b} − 1)f` plus a nonnegative remainder?
- **Why it opens the path**: the coupling polarization `C_K(u, v) = B(T_{u⁻¹}f − f, T_v f − f)`
  supplies the natural squares, and `κ(L_pL_qK_ζ) = κ` [L]. The archimedean form on `ℓ = 0` is
  already Weil's dilation form plus shell squares [M]. An identity on the minimal carrier is RH,
  with no estimate. The calibration is exact: over `𝔽_q` the tower coupling is bounded iff the
  Frobenius span satisfies Castelnuovo–Severi [L], a finite sum-of-squares statement on
  commensurable towers. Over ℤ the towers are incommensurable, and the identity must hold on a
  dense lattice.

### 2.6.3 Route WD — a non-holomorphic explicit formula
**Question.** Is there an arithmetic identity expressing the Hecke translates of the collided form
(equivalently `E_γ(L)`) through prime-pair sums, with an error uniform across all dyadic scales
`2^k c₀ log T`?
- **Why it opens the path**: RH ⇔ one constant bounds the dyadic Hecke defects [L]. Linear tools
  are proved insufficient [L]. A quadratic identity with a scale-uniform error converts the bound
  into a statement about prime pairs, where the corpus has form-factor theorems [M]. It is the
  analytic form of Frobenius at infinity: the identity of the conjugation and reflection pairings
  read through primes.

## 2.7 Does closing RH need a new field?

**Assessment: yes. The corpus lacks one type of positivity producer.** Every producer in the
corpus has one of three types, and each type has a proved limit:
1. *Estimates* stop at the edge. The universal regime is `(log N)^{1/19}`, and unconditional
   positivity cannot cross the edge.
2. *Counts* stop short of square-root precision. Producers reach the main term, the kernel equals
   the window error, and counts plus the linear explicit formula cannot bound the Hecke defect.
3. *Selectors* separate ζ from every prime-set flip but are margins on partial forms.

The reformulation theories are necessary and are not producers. EHT locates where positivity
fails and shows the failure is a zero mode. ACPL proves that the coupling is the kernel and that
the prime form is an identity of squares. RIT makes positivity a Hodge index on the primitive part
`v₁^⊥`. The missing type is exact local-to-global positivity with nondegeneracy. That type proved
Hodge–Riemann relations without varieties: for matroids (Adiprasito–Huh–Katz), for Soergel
bimodules (Elias–Williamson), and spectral gaps of buildings from their links (Garland).

**Working name: the arithmetic Kähler package** (Hodge theory without varieties over ℤ).

*What it is about.* Quadratic forms on the divisibility–successor complex of `[1, N]`:
- vertices: the atoms `log n`;
- dilation edges `(n, kn)` with weight `Λ(k)/k`;
- affine edges `(n, kn + h)` with the shell weights.
Weil's form is the intersection form, the pole `v₁` is the Kähler class, and `v₁^⊥` is the primitive
part. RH is the Hodge–Riemann relation on the primitive part, uniformly in `N`.

*What it would be like.* A positivity theory by induction across a self-similar family. Dilation
invariance makes the block on `pℤ ∩ [1, N]` a copy of horizon `N/p`. Prime sets grow `S → S ∪ {p}`.
Nondegeneracy (hard Lefschetz) is proved algebraically at each step. The signature is transported
along nondegenerate paths (EHT path invariance), starting from a base point in the universal
regime. Positivity comes from identities and an induction, never from an estimate against the
ground energy.

*Criteria it must meet.*
1. Exactness: positivity statements are identities or inductions, valid at the edge.
2. Local Hodge–Riemann: on links the form has the Lorentzian signature. The corpus has it for the
   matched prime form on every finite sieve (one positive direction) [L], the affine incidence
   energy as an exact CRT sum of squares [L], and local pole–successor signatures `κ₀ + 1` [M].
3. Arithmetic hard Lefschetz: an operator or flow parameter along which the form stays
   nondegenerate. This is the Liouville property of 2.6.1.
4. Level-independent constants: the induction runs through infinitely many levels without loss.
   Over ℤ the edge is unbounded, over a curve it is `≤ 2g` [L].
5. Selectivity through `Λ ∗ 1 = log`. The Mertens polarization is exact for ζ and fails for twins.
6. Compatibility with the no-gos: local forms do not sum, separable assemblies are blind, single
   towers already carry the full index. The induction must create rank-two coupling through the
   Lefschetz step, not through summation or tensoring, and single towers cannot serve as links.
7. Calibration: over `𝔽_q` it reproduces Weil's theorem, where buildings and Ramanujan complexes
   give Garland-type gaps and towers are commensurable. It fails on the golden datum at its first
   window.

*Questions it must answer.*
- What are the links of the arithmetic complex: finite sieves, coprime residue structures,
  conductor sectors?
- What is the Lefschetz operator: the dilation generator, the overlap derivative `∂_c W`, or the
  coupling Laplacian `L_pL_q`?
- Does the shell degree admit a Lefschetz-type decomposition that pays it jointly with the pole
  (Q2b)?
- Can the universal regime serve as the base point of the deformation, and the overlap flow as the
  path?
- What is the function-field model: Bruhat–Tits buildings or Ramanujan complexes with Frobenius
  acting on commensurable towers?

*Tools it aims to develop.*
- Inductive hard Lefschetz / Hodge–Riemann on arithmetic complexes.
- Garland's method and trickling-down for weighted divisibility graphs.
- Poincaré and Cheeger inequalities for the affine–dilation graph with shell-degree mass.
- Lorentzian forms beyond nonnegative coefficients. The local-factor Lorentzian closure is a
  proved boundary [M].
- Kernel theorems (successor/dyadic rigidity) as Liouville theorems.
- Interfaces to EHT (zero modes, paths) and ACPL (packet identities, coupling).

*Objects, language, mechanisms.*
- Objects: the divisibility–successor complex, incidence events, Ramanujan conductor packets as
  harmonic representatives, the pole class as Kähler class, the primitive part `v₁^⊥`, links and
  stars of the dilation action.
- Mechanisms:
  - local Hodge–Riemann + hard Lefschetz ⇒ global Hodge–Riemann by deformation;
  - local spectral gaps ⇒ global gap with level-independent constants;
  - selection by the divisor identity.

No result in the corpus shows that such a theory exists for ζ. Its first test is the Liouville
property of 2.6.1 at the first level beyond the universal regime.
