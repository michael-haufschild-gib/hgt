# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-27, corpus `7eaf4d7ef` with working tree. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes. Companions: [summary, next questions and new-field assessment](obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; the findings are recorded in `logs/review-2710-v3-research-log.md`. Nothing was compiled. Labels: `[L]` integrated source, `[S]` working or unintegrated source (as the frontier map marks it), `[P]` paper proof, `[R]` reading or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, explicit constants, classical ranges of known estimates. IDs `W1`–`W19`, defined in the [summary](obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

**Notation.** `Δ = sup_ρ |Re ρ − 1/2|` (zero width), `Θ = 1/2 + Δ` (zero abscissa). A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ` of multiplicity `m`: `ρ* = 1 − ρ̄` its reflection, `δ = Re ρ − 1/2` its depth. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`.

- **Two forms.** `W` is Weil's form; `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**; `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**; `T_L` translation by `L` (the Hecke action of the dilation `e^L`); `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` the **Hecke defect**; `M_f = Σ_ρ m_ρ δ_ρ² |f̂(ρ)|²` the **transverse moment of inertia** of the divisor seen by `f`.
- **Electrostatics.** For a zero `p`, `E(p) = Σ_{q ≠ p} m_q/(p − q)` (regularized) is the **field** of the other zeros; `Re E(p)` its **transverse field**. `𝓔 = ½ Σ_{ρ ≠ ρ′} (Re ρ − Re ρ′)²/|ρ − ρ′|²` (distinct zeros, unit charges) is the **transverse energy** of the divisor.
- **Torsion.** `O_n` is the orbit of primitive `n`-th roots of unity; `I(m, n) = Σ_{ζ ∈ O_m, η ∈ O_n} log |ζ − η|` the archimedean intersection; `c(n) = I(n, n)/φ(n)`; `P(m, n) = Λ(n/m)(n/m)^{−1/2}` Weil's prime kernel on orders; `β(n, t) = c(tn) − c(n)` the Hecke cocycle; `K_q = (q^{|i−j|})` the Kac–Murdock–Szegő (tower) matrix, `q = p^{−1/2}`; `G_r(z) = Σ_{k≥0} r^k/(k + z)` the archimedean lattice germ; `Λ₂ = Λ log + Λ ⋆ Λ` Selberg's source.
- **Other.** `σ_γ(s) = 1 + 2iγ − s` the elliptic localizer at ordinate `γ`; `ζ_γ(s) = ζ(s)²ζ(s + iγ)ζ(s − iγ)` the height-coupled carrier, `HeightCoupledSystem 2 1 1 γ` its class; `ν_N` the torsion measure of roots of unity of order `≤ N`.

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space, and how far each is computed

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH; finitely many negative directions at every aperture [L] | yes, for every zero configuration [L] | the explicit formula (primes, Gamma, poles) |
| Collided form `D` | yes; faithful; at each aperture equivalent to the logarithmic Sobolev norm [L] | iff RH [L] | the current `Δ log|ξ|` and polynomially many integer theta values, without zero indexing [L] |

- **Capacity identity** [L]. `Re W = D − Δ` on every compact `C²` test; RH iff `W = D` iff `D` is Hecke invariant iff some `T_L`, `L ≠ 0`, is a similitude of `D` (`riemannHypothesis_iff_W_eq_collided`, `riemannHypothesis_iff_collided_hecke_invariant`, `hecke_similitude_iff`).
- **`D` is the logarithmic Sobolev norm** [L] (`collidedForm_equiv_logSobolev`): at every aperture `A`, `c ∫|f̂(σ)|² log(|σ| + 4) dσ ≤ D(f) ≤ C ∫|f̂(σ)|² log(|σ| + 4) dσ`. `D(f) = 0` only for `f = 0`; the zeros with multiplicity sample every Paley–Wiener space. Gårding: `Re W ≥ 2π‖f‖² − K ∫_{−T₀}^{T₀} |f̂|²`; every orthonormal family on which `W` is negative has fewer than `2AT₀K/π` members (`card_negative_orthonormal_le`). Local Weyl law `(1 − η)‖f‖² log|γ| ≤ D(e^{−iγu} f) ≤ K_f log|γ|`.
- **`D` is computed** [L]. The Laplacian of `log|ξ|` evaluates compact test squares; a canonical exhaustion recovers `D` and every depth moment. Integer theta prefixes of size `(K + 4)(n + 1)^{20}` recover the `4^j`-normalized moments for `a + j|L| ≤ 2 log(n + 1)`, `|τ| ≤ n/2`, with error `O(n^{−2} + log n/n)` (`exists_polynomialThetaSource_aperture_logarithmic_bound`). A two-radius reading detects zeros in discs of radius `1/(16(n + 1)^6)` up to height `n/2` (`polynomialThetaLocalReading_uniform_zero_detector`). The readings are continuous integrals, not finite quadratures.
- **The Hecke defect is a moment of inertia** [L] (`heckeDefect_le_moment`, `moment_le_heckeDefect`). `E_f(L) = Σ m(2cosh(2δL) − 2)|f̂(ρ)|²` satisfies `4L² M_f ≤ E_f(L) ≤ 8(cosh L − 1) M_f`, and `E_f(L)/L² → 4M_f`. A bound on the equivariance defect at one scale is a bound on the second depth moment of the divisor seen by `f`; RH is `M_f = 0` for every test.
- **Depth geometry** [L, S]. `L ↦ D(T_L f)` is the Laplace transform of the depth measure. `E_f(L) ≤ k(L, 1/2) D(f)`, `k(L, d) = 2cosh(2dL) − 2`; two-scale rigidity `E(L)² ≤ D(E(2L) − 4E(L))`, equality at `L ≠ 0` iff all seen zeros share one absolute depth. The depth moments `m_j(L) = Σ w_ρ k_ρ^j` (`m₀ = D`, `m₁ = E(L)`, `m₂ = E(2L) − 4E(L)`) solve a Stieltjes problem: every shifted Hankel form is PSD and null vectors are the polynomials vanishing on the seen depths.
- **Dyadic amplification** [S]. Two-scale rigidity conjugates to angle doubling: `E(L) ≥ D(2cosh θ − 2)` implies `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` with the fixed loss `D(f)`; an upper bound at one dyadic scale transfers to `L` without loss (`heckeDefect_le_of_dyadic_le`). RH iff `E_f(2^k) = O(exp(ε 2^k))` for every test and `ε > 0` (`riemannHypothesis_iff_dyadic_subexp`). Integer theta readings transfer such bounds within `2^k|L| ≤ 2 log(n + 1)`, given an upper-reading inequality [S].
- **Reading [R].** `D` is the non-scaling invariant in a tensor-power amplification, as the genus is in Weil's argument; the amplification converts a dyadic growth rate into a depth bound and nothing stronger. What computes `D` is answered; what bounds `M_f` above by something that vanishes is not. Over `𝔽_q`, `D` is the Hermitian trace and `W` the Rosati trace on `H¹`; purity is their coincidence (`re_rosatiForm_eq_collided_sub_defect`, `collided_frob_invariant_iff_unitary` [L]).

### 1.2 Local type, elliptic localizers and the forcing gap

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, signature `(1, 1)`.

| Type | Action on the fibre | Correspondences | What positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost `diag(β, β̄⁻¹)`, `\|β\| ≠ 1` | Hecke operators, archimedean flow, gauge twists, exactly at off-line pairs | isotropy |
| Elliptic | rotation or swap | Hecke operators on the line; resonant symmetric dilations; `σ_γ` | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the additive successor | nothing |

- **Resonance** [L]. A symmetric dilation by `a > 1` is elliptic at an off-line point of ordinate `γ` iff `γ log a ∈ πℤ`.
- **Elliptic localizers** [L]. The stabilizer of an off-line pair among reflection-compatible affine maps is `{id, σ_γ}`; even sector `+2|G(ρ)|²` (cannot force), odd sector `−2|G(ρ)|²`. Hecke + `σ_γ` stability is blindness.
- **Symmetric squares** [L]. `(β − c)(β⁻¹ − c)` is a nonnegative real for every real `c` iff `|β| = 1`; for the Hecke symbol `p^{ρ − 1/2}` this is `Re ρ = 1/2` at one prime (`symSquare_heckeSymbol_nonneg_iff`).
- **Sparse annihilators** [L]. A `K`-term polynomial vanishes to order `< K` at every nonzero point; `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = 1/2` and `N Im ρ log p ∈ 2πℤ`.
- **Conductor horizon** [L]. `Re W_ζ(e^{−iγu} f) ≥ 0` for every `C²` test of aperture `a` once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)`; source-blind there; no eventual-in-height positivity for all tests beyond it (Kronecker peaks).
- **Forcing half and gap** [L]. One sign of `W` on the twisted odd detector, a local count `≤ A log(|t| + 3)` and depth dominance force an off-line companion within ordinate distance `R`. The certificate needs `768A log(|γ| + 3) < e^{2δa}`, which never coexists with the conductor horizon for `0 ≤ δ ≤ 1/2`, at any height (`conductor_forcing_disjoint`).
- **Reading [R].** Beyond the horizon the detector's prime side is a Dirichlet polynomial of length `(log γ)^{O(1)}` at the zero's ordinate; its sign is governed by how `γ log p` aligns modulo `2π`.

### 1.3 Electrostatics of the zero divisor

The zeros are the charges of one logarithmic potential `log|ξ|`. Its Laplacian is `D` (§1.1); its gradient at the charges is the field; its pairing with the reflection is `W`.

- **The field is computed** [L] (`TheRankinSelbergSquareSeesTheFieldOfTheOtherZeros`, `EveryXiZeroHasASourceField`). `L(Λ ⋆ Λ, s) = (ζ′/ζ)²` on `Re s > 1`; at every zero the simple Laurent coefficient of `(ζ′/ζ)²`, divided by `2m` and completed by the archimedean logarithmic derivative, is the absolutely convergent transverse field. Zero isolation suffices; no simplicity is needed. On finitely many copies the source work is the transverse pair energy plus a signed exterior term.
- **Virial laws** [L] (finite configurations). Newton's law `Σ m_j E_j = 0`; Stieltjes' virial `Σ m_j z_j E_j = ½((Σm)² − Σm²)`; the transverse virial `Σ m_j (Re z_j − c) Re E_j = ½ Σ_{j≠k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²`, a Dirichlet energy on the complete graph (`sum_mul_re_fieldAt_eq_transverseEnergy`).
- **Equilibrium is the critical line** [L] (reflection-closed finite configurations, `critical_iff_equilibrium`). Every transverse field vanishes iff every charge lies on `Re s = 1/2`; nonpositive total work already suffices; each off-line pair contributes exactly `m_j m_{σj}` to the energy at every depth, so the energy is `0` or at least `1`; off the line the deepest charge feels an outward field and the shallowest an inward one.
- **The energy of the actual divisor** [L]. `𝓔 = 0` iff RH iff `𝓔 < 1` (`divisorTransverseEnergy_eq_zero_iff`); `𝓔 < ∞` iff finitely many zeros are off the line (`divisorTransverseEnergy_lt_top_iff`); then work equals energy. Transverse force zero at every zero together with `𝓔 < ∞` gives RH. Damped arithmetic source work of the Laurent residues converges, for `R ≥ 4`, to a nonnegative absolutely summable reflected pair sum, and along `R = n + 4` exhausts the multiplicity-copy energy `𝓔_copy`, finite or not [L].
- **Quantization turns windows into points** [L]. The energy of a finite window of zeros bounds its number of off-line zeros; a window with an off-line zero has energy `≥ 2`; RH iff every unit window has energy `< 2` (`riemannHypothesis_iff_windowEnergy_lt_two`). One zero spacing suffices: a quantized statistic excludes individual zeros.
- **The field law has a threshold** [L]. RH iff every zero right of the line feels a transverse field `≤ 1` (`riemannHypothesis_iff_forall_transverseField_le_one`); for an explicit `c > 0`, iff every such field is `< √(2c log(|γ| + 4))` (`exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`). The excluding inequality is an upper bound of size `max(1, √log γ)`, not exact equilibrium.
- **Terminals, the outward ray and the terminal lens** [L, S]. Every right zero has, within `C log(|γ| + 3)`, a right zero `p` at least as deep with an empty quadratic ascent cone. On the ray `p + h`, `0 < h < 1/2 − a`, `ξ` and `ζ` do not vanish and `m/h + m/(2a + h) + c·a·log(|γ_p| + 4) ≤ Re(ζ′/ζ + Γ-part)(p + h)` (`exists_local_outward_zeta_ray`). Every off-line zero has such a terminal with transverse field `≥ m/(2a) + c·a·log(|γ| + 4)` (`exists_local_outward_field_witness`). Right of the line and outside every critical disc (radius `|b|` about the foot `1/2 + iγ` of the pair `1/2 ± b + iγ`) `Re ξ′/ξ ≥ 0` (`re_logDeriv_xi_nonneg_of_outside_discs`); terminals are the points outside every disc; the lens `{x > 0, |y − γ_p| ≤ T, x² − a² + (y − γ_p)² ≥ 2T|y − γ_p|}`, `T = √(1/4 − a²)`, is zero-free away from `p` [S].
- **The external field is a prime sum** [L] (`re_LSeries_vonMangoldt_le_at_zero_ordinate`). For `σ > 1` and a zero `β + iγ` of multiplicity `m`, `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re(Γ-part)′(σ + iγ) − m/(σ − β)`: a deep zero forces the primes out of alignment at its own ordinate. This exterior law does not continue into the strip.
- **The renormalized square is Selberg's source** [L]. `F″/F = (F′/F)² + (F′/F)′`; renormalization by the degree lowers the double-pole coefficient from `m²` to `m(m − 1)` and leaves the residue `2mR(ρ)` (twice the field) unchanged. On the arithmetic side the counterterm is `Λ log`, and `Λ₂ = Λ log + Λ ⋆ Λ = μ ⋆ log² ≥ 0` with `L(Λ₂, s) = ζ″/ζ(s)` (`selbergSource_nonneg`, `LSeries_selbergSource`).
- **Gauge behaviour** [L]. The reflection-commuting affine maps `s ↦ 1/2 + λ(s − 1/2) + iκ` preserve the transverse energy and scale the field by `λ⁻¹`: electrostatics is blind to the archimedean twist. For a completely multiplicative sign gauge `ω`, the twin's source is `ω Λ₂`, and its nonnegativity at a prime forces `ω(p) = 1` (`eq_one_of_twisted_selbergSource_nonneg`): coefficient positivity carries the charge, the geometry of the charges does not.
- **On the circle equilibrium is stable** [L]. For `N` distinct unit charges on the circle, `Σ_{i≠j} log|z_i − z_j| ≤ N log N`, attained by the `N`-th roots of unity.
- **Reading [R].** Equilibrium, quantization and the field are computed; stability is the sign. The witness, the reserve and the detectors detect off-line zeros; the inequality that would exclude them is an upper bound for the field of size `√log γ` at right zeros, or for `ζ′/ζ` on outward rays below `c·a·log γ`. Under RH, `‖ζ′/ζ(σ + iγ)‖ ≤ C log|γ|/(σ − 1/2)` (`exists_logDeriv_zeta_bound_rh`).

### 1.4 Torsion intersection and renormalization

- **`Λ` is an intersection number** [L]. `I(m, mt) = φ(m)Λ(t)`; `I(n, m) = log #(𝒪_{ℚ(ζ_n)}/(Φ_m(ζ_n)))` and `Λ(n) = log #(𝒪_{ℚ(ζ_n)}/(ζ_n − 1))` (`log_card_quotient_zeta_sub_one`): every entry of the prime kernel is the log-order of a finite ring.
- **Self-intersection and the different** [L, S]. `I(n, n) = log|disc Φ_n| = φ(n) log n − (φ ⋆ Λ)(n)`; per point `c(n) = Σ_{p^a ∥ n} (a − 1/(p − 1)) log p ≥ 0`, the canonical degree of `ℚ(ζ_n)` summed over places. Along the tower of `p` the self-intersection per point grows by exactly `log p`. Complex conjugation is the power map of degree `−1`, so on torsion cycles the collided and the reflection pairing coincide.
- **The tower form of a prime and local Hodge index** [L]. On a `p`-ladder `c, cp, cp², …` the prime kernel is `log p · (K_q − I)`; `K_q(x) = Σ_k φ(p^k)(Σ_{i≥k} x_i p^{−i/2})²` and `(1 − q)/(1 + q)|x|² ≤ K_q(x) ≤ (1 + q)/(1 − q)|x|²`. Two orders share a ladder for at most one prime, so `P = Σ_p L_p` with `L_p = log p (K_p − 1) ⊗ 1` on `ℓ²(⊕_p ℕ)` (`weilPrimeKernel_eq_sum_ladderKernel`), and each local form obeys `−2q log p |x|² ≤ (1 + q)Q_p(x)` and `(1 − q)Q_p(x) ≤ 2q log p |x|²` (`localForm_lower`).
- **The local forms do not sum** [S] (`not_exists_primeForm_le`). Along the pole direction `x_n = n^{−1/2}` on orders `≤ M²` the prime form is at least `H_M Σ_{t≤M} Λ(t)/t` against mass `H_{M²}`; no constant bounds the prime form by `C|x|²`. The local bounds sum to `Σ_p 2 log p/(√p ± 1)`, which diverges. The global sign is not the sum of local ones; it has to be paid by the archimedean place, whose self-energy of an atom of width `ε` is `log(1/ε)`.
- **Positive torsion energies and their renormalized limit** [L]. For `r < 1` the torsion energy `G∘T_r` is PSD; the full Abel energy is `T_r(A, B) = gcd(A, B) log(1/(1 − r^{lcm(A, B)}))`. Removing the diagonal self-energy and letting `r → 1` gives minus the prime kernel and the log-discriminant diagonal (`weilPrimeKernel_renormalized_torsion_energy`).
- **Power maps are similitudes up to the cutoff** [L]. `T_r(At, Bt) = t·T_{r^t}(A, B)` (`fullTorsionEnergy_mul`): Hecke correspondences are computed similitudes of a positive Hermitian structure, exactly up to `r ↦ r^t`. The projection formula `Σ_{ω∈μ_t} log|z − ωw| = log|z^t − w^t|` carries the regulator anomaly: the renormalized energy of a pulled-back cycle is `t` times its energy minus `t log t` times its mass.
- **The Hecke cocycle** [L]. Transport `n ↦ tn` changes the renormalized form by `−Σ x_n² β(n, t)`, `β(n, t) = log t − Σ_{p∣t, p∤n} log p/(p − 1)`: the anomaly `log t` minus the tame different. `β` is a cocycle, `0 ≤ c(t) ≤ β ≤ log t`, and it is not the coboundary of a bounded potential (`not_exists_bounded_potential`). On cycles saturated by the primes of `t` the variation is `−log t Σ x_n²`, and the degree-normalized limit is Hecke invariant there (`tendsto_heckeVariation_of_saturated`).
- **The survival law** [L]. If every `Q_r` is PSD and `Q_r − s_r B → A`, then `A ≥ 0` on the null cone of `B`; the cone is scheme-independent; for `B ⪰ 0` this is equivalent to eventual positivity of `A + sB + εI` (`quad_nonneg_of_regularized`). A scalar counterterm has survival cone `{0}`; a rank-`k` counterterm leaves codimension `k`.
- **The counterterm rank dichotomy** [L, S] (`counterterm_rank_dichotomy`). The torsion germ's counterterm is the identity: every renormalization has survival cone `{0}`, and the renormalized limit is indefinite on `{1, q}` for every prime power `q`. The archimedean lattice germ's counterterm is `𝟙𝟙ᵀ`: positivity survives exactly on the polar-neutral hyperplane `Σ c_i = 0`, where `Σ c_i c_j (−ψ(x_i + x_j)) ≥ 0` (`neg_digamma_hankel_nonneg`); off it, `G_r(2) + log(1 − r) → −1`. Adjoining the arithmetic point `{1}` as a node, whose self-energy is exactly the archimedean divergence, gives the kernel `H(x) + H(y) − H(x + y)`, `H(x) = ψ(1 + x) + γ`, PSD on all vectors [S].
- **Periodic germs** [S] (`periodicGerm_survival`). For periodic modes at nodes the counterterm is the Cesàro Gram and the survival cone is exactly the module of linear relations among the modes. Ramanujan modes of torsion orbits carry no relations; a twin keeps prime-side positivity only by adjoining modes that create relations.
- **The counterterm is logarithmic** [L, S]. The minimal constant counterterm making the torsion pairing on orders `≤ N` positive lies between `½ log(N/2)` and `4 log N + log 4 + 4`. A counterterm `c(n) > 0` per point satisfies `c(1) ≥ Σ_{2≤n≤N} Λ(n)²/(c(n)φ(n))`; a constant one satisfies `κ² ≥ log 2 · (log N − log 4 − 4)`: the divergence sits at the arithmetic point `z = 1`.
- **Gauss's digamma theorem is a Fourier transform** [L] (`gauss_digamma_theorem`). On `μ_N` the torsion energy's Fourier coefficients are the lattice germ at `k/N`; at `r → 1`, `Σ_{0<a<N} log|1 − ζ_N^a| cos(2πak/N) = log N + γ + ½(ψ(k/N) + ψ(1 − k/N))`. The archimedean local factor and the torsion of the circle are Fourier dual; `log N` is the anomaly of `[N]`.
- **Reading [R].** Every ingredient of Weil's argument over `𝔽_q` has a located counterpart: a positive Hermitian structure with Hecke similitudes (the Abel energies, regularized), local Hodge index at each prime (the tower forms), a finite self-intersection of the diagonal (over `ℤ`: an identity counterterm, survival cone `{0}`), a non-scaling loss for tensor amplification (`D(f)`). Positivity on the prime side is carried entirely by its divergence; the archimedean germ keeps it on a hyperplane; the arithmetic point is the node that cancels the archimedean divergence. A renormalization that keeps prime-side positivity must couple the two places so that the joint counterterm has lower rank and its finite part is Hecke covariant: on the circle the cocycle `β` is the regulator anomaly `log t` of `[t]` (the cutoff moves `r ↦ r^t`) minus the tame different, while Weil's form, whose archimedean term is translation invariant, has none.

### 1.5 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, `FF′ = q` | exact | no: hold on the golden datum `1 − 5X + 5X²` |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs; Tate's limit | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free: similitude law | no |
| L4 Kernel counts | `#ker ≥ 0`; exterior counts | collided; the complex fake has all kernel counts `≥ 0` and Rosati value `−2304` at `F² + 16` | collided positivity only |
| L5 Rosati positivity | polarization | `⇔` orbit Hodge index `⇔` RH; `⇔` nonnegative symmetric-square spectra | missing |
| L5′ Counting origin | RR on `C × C`; Stepanov count, `\|τ\|² = q` | section count, effectivity function, naive and convex heights, one-sided count, horizon torsion: each RH; Stepanov needs a lattice spectrum | each is RH |
| L5″ Diagonal | self-intersection `2 − 2g`, finite | torsion counterterm the identity, minimal value `≍ log N`, cocycle `β` nontrivial; archimedean germ positive on the polar hyperplane | missing: a coupled finite renormalization |
| L5‴ Local–global | the Frobenius acts on one `H¹` | each prime's tower form satisfies a local Hodge index; their sum has no `ℓ²` ceiling | missing: archimedean payment |
| L6 Base | fixed tensor loss | fixed tensor loss `⇔` RH; dyadic amplification has loss `D(f)` but converts only rates | missing |

**Calibration over `𝔽_q`** [L]. RH for odd-degree squarefree hyperelliptic curves over every finite field of odd characteristic by counting (`riemannHypothesis_oddHyperelliptic`), split case included through degree sums and Weil's bound for quadratic character sums; Hasse for elliptic curves; effectivity functions and naive heights exist there; `ℙ¹ × ℙ¹` has an exact effectivity function.

**Completion law** [L]. At finite level square-root cancellation of complete sums is a count (`|τ|² = q`), and completion transports it to incomplete sums (Pólya–Vinogradov). Burgess for quadratic characters on all intervals and `r ≥ 2`, and the least non-residue `≤ p^{1/(4√e) + ε}` (`eventually_exists_nonresidue_le`). The arithmetic point (`Σ μ(n)`, `ψ(x) − x`) has no period. Integrality gives the Stepanov floor `log(1/∫₀¹ P) ≤ ψ(n + 1)` (Nair's floor).

### 1.6 Counting is the sign

- **Section counts and effectivity** [L]. A count with RR and Bézout, or an effectivity function, exists iff the Hodge index; over `ℤ` iff RH.
- **Six currencies** [L]. An effectivity function, no abundant class, a naive height for every integral Rosati form, a fixed tensor loss, horizon torsion at `√N` precision and a midpoint-convex height at bounded distance are each RH.
- **The polar box** [L]. The box count is an effectivity function iff the Hodge index; subtracting the prime-power nodes gives `N − ψ(N)` and destroys the Riemann inequality.
- **Torsion potential** [L]. `Λ(n) = Σ_{μ primitive} log|1 − μ|`; RH iff the Farey sum `Σ_{n≤N} Σ_{(k,n)=1} log(2 sin(πk/n)) = N + O(√N log²N)`; `ν̂_N(1) = M(N)`.
- **Heights and sections on short cycles** [L]. Torsion-weighted Jacobi–Hurwitz packets are blind on degree zero or inflate quadratically; an unsigned large-sieve majorant forces `q_P(z) ≥ |z·z|/2`; RH iff a bounded-below asymptotic subquadratic height exists; section supply beyond the large-sieve diagonal is a zero-free strip; sign-free Serre-dual box cohomology fails Riemann–Roch on the golden datum.
- **Theta surface and lattice counts** [L]. The theta surface's counting polarization is the same on every fibre; lattice counts on the square give `ζ(s₁ + s₂)` or `ζ(s₁)ζ(s₂)`.

### 1.7 Budget currencies

A **budget** is a linear log-energy of a row: `∫_0^L e^{−u} g(⌊e^u⌋)² du ≤ S L + B`.

| Row | Over `ℤ` | Over `𝔽_q` |
|---|---|---|
| Prime error `ψ(n) − n` | a budget exists **iff RH** (`riemannHypothesis_of_primeError_budget`, `primeError_budget_of_riemannHypothesis`); every slope `S ≥ 2 + γ_E − log 4π` and pays the critical zeros (`not_forall_primeError_energy_le_linear`); RH with simple zeros iff the Abel slope tends to `2 + γ_E − log 4π` [L] | a budget is purity; slope `Σ_β mult(β)²`, `= 2g` iff simple [L] |
| Mertens `M(n)` | a budget forces RH, simple critical zeros and `Σ_ρ |ρζ′(ρ)|^{−2} ≤ S` [L]; the converse is not formalized | purity with simple spectrum; slope = repulsion energy; genus one: strict Hasse [L] |
| Successor shift | `D_Λ(s)/s ∈ H²(Re s > 1/2)` with `‖·‖² = 2πΣΛ(n)²/(n(n + 1))`; the shifted prime error carries the same cost [L] | — |

Reading [R]: the Mertens converse is classical under RH together with `J_{−1}(T) = Σ_{|γ|≤T} |ζ′(ρ)|^{−2} ≪ T` (Ng's method).

### 1.8 The gauge principle

- **Orbits, not points** [L]. Multiplicative data determine a source up to its gauge orbit; for `μ` the half-power law holds Haar-a.e., fails at the Liouville twin and at the gauge point `0` is RH. Gauge-charged boundaries normalize at weight `1/4`.
- **Which couplings are charged** [S]. A coupling `(n; a, b)` of a source kernel is blind under every real sign gauge iff `nab` is a perfect square (`realSignBlind_iff_isSquare`); diagonal, ratio and product couplings are square class, which is why multiplicative lattice forms are unitarily gauge-blind, and positivity of a square-class form holds for `Λ` iff for `λΛ`. Successor couplings `a(a + 1)` are charged for every `a ≥ 1`.
- **Cells fix the gauge** [S] (`cellDilate_two_covariant_iff`). Dilation by `m` on log-cells `[log n, log(n + 1))` is the lattice dilation spread over the successor orbit. Lattice dilation is gauge-covariant at every gauge; the dyadic cell dilation is covariant only at the Euler gauge, through `9 = 3²`; on profiles supported on `[1, X]`, `X ≥ 4`, covariance is equivalent to `ω(p) = 1` for every prime `p ≤ 2X + 1`. The successor connection is flat iff `ω(p) = 1` on `[1, N + 1]` and reconstructs `ω(2), ω(3)` on `2 → 3 → 4` [L].
- **First windows separate, and the separation persists** [L]. At `181/500` an odd smooth test has `W_ζ ≥ ‖F‖²/1000` and `W_λ = W_{flip 2} < −‖F‖²/1000`; the full-sector floor of `ζ` is `1/5000` there; a shifted pair is negative on an even test. At `23/40`, where the `{2, 3}` flip is not a height twist, one odd test has `W_ζ > ‖F‖²/25` and `W_λ < −(3/10)‖F‖²`; by support inclusion the Liouville ground eigenvalue is `< −3/10` at every aperture `r ≥ 23/40`. At `r = 2 log 2` the prime support is the nine-modulus collar `{2, 3, 4, 5, 7, 8, 9, 11, 13}`; `W_λ − W_Λ = 4Σ_{n∈{2,3,5,7,8,11,13}} Λ(n)n^{−1/2} autoCorr_F(log n)`; the Catalan forms `w(2)w(4)` and `w(8)w(9)` are positive on every real scale twist and negative at `λΛ`. The full floor of `ζ` at `23/40` is not certified.
- **Repulsion** [L]. `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50`; with enough primes the sum beats `exp(−|γ|^ε)`.
- **Worst twin; amplification** [L]. On nonnegative tests `Re W_Λ ≤ Re W_w` for `w ≤ Λ`. Moments, family averages, products and relative powers lose linearly; twists are rate neutral.

### 1.9 Positive systems: one variable, polar configurations, deformations

- **Degree-one rigidity and contraction** [L]. `CompletedPositiveSystem 1 d = ℝ^× · ζ`; pole order pays inserted zeros; a complex quartet contracts only against a real anchor; an anchored quartet forces `κ ≥ 3`; planting costs `Δκ ≥ 2`; coupled completions vanish to even real order; Fejér barrier; the global conjugate collision has no analytic carrier.
- **Positive polar configurations** [L]. One vertical section decides positivity; the leading line carries a nonnegative almost-periodic sum; commensurable positive lines are couplings. A positive packet on `ℚ`-independent ordinates buys at most its pole share, `Σ|a_j| ≤ a₀`, sharply; harmonic Fejér packets buy `M` times the pole share [S] (`sum_abs_le_of_packet_nonneg`): collective amortization exists only through arithmetic relations among ordinates.
- **Deformation principle** [L, S]. Landau–Wronskian principle; Abel–Gram law; critical conservation. Positive deformations form a monoid without nontrivial invertible elements (`not_positiveDeformation_of_ne` [S]).
- **The coupled class** [L]. `HeightCoupledSystem 2 1 1 γ` is not rigid at any critical-zero ordinate. Positive prime-mass rigidity at `γ` iff `ξ` has no zero at ordinate `γ`; positive chirality and the positive and rational central ceilings at `γ` each iff `ξ` has no off-line zero at ordinate `γ`; RH iff any of them holds at every `γ`.
- **Arithmetic members and quantization** [L]. Where `ξ` has no off-critical zero at ordinate `γ`, the Abel residue of the surplus of a positive deformation, and of an arithmetic member with zero-residue half-power deficit, equals the central drop, an even integer `≤ 2 ord_{1/2+iγ} ξ` (`tendsto_abel_excess_eq_centralDrop`, `tendsto_surplus_residue_eq_centralDrop`). A full-class central ceiling at `γ` transfers to entire factors `Λ = (2ξ)^k Λ_G`; neither the ceiling nor an actual Rankin–Selberg member is constructed. For `ζ^d`: `κ ≤ d` and a sub-half deficit force `F = Kζ^d`; boundary capacity `2Σ ord_{1+it}Λ ≤ κ − d`.

### 1.10 Escape

- **Location and classification** [L]. At damping `ε` the receiver escapes iff zeros lie right of `1/2 + ε`; RH iff admission at every damping iff every actual cofactor limit has positive gauge mass; power growth gives gauge mass zero (`gaugeMass_eq_zero_of_powerGrowth`). The receiver line symbol splits at every dominant translated simple zero into a pole plus a bounded remainder.
- **Energy-rate law** [L]. `E_ε(T) ≤ C_κ(T + 1)^κ` for every `κ > max(0, 2Θ − 2ε − 1)`, with its lower direction.
- **Abel atoms** [L]. Each dominant simple zero carries an atom `π‖r_ρ‖²`, `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`; capacity, endpoint and shadow laws; effective orders are visible translated-zero orders.
- **Infinite height** [L]. Non-summable residue masses, an unattained abscissa or unbounded visible orders send every compact window's share to zero. Escape classifies; it does not exclude.

### 1.11 Positivity: pointwise, averaged, statistical, quantized

- Windows: full `‖f‖²/5000` and odd `‖f‖²/1000` through `181/500`; primitive through `(log 2 + 1/50)/2`; non-localizing positivity (`a ≤ 3/10`) holds for every prime weight [L].
- Short-window averages on `Γ^{99/100} ≤ H ≤ Γ/8` (Selberg's near-line density formal on such windows); pointwise floor `−4(A + 1)²e^A N²Φ(γ)`; nonnegative tests positive at all but `CH/η` zero ordinates; a positive proportion of heights is Weil-positive for nonnegative tests [L].
- **Census** [L] (from the imported two-thirds certificate `Zeta23`). In `(T, 2T]`: `(2/3 − ε)N + M_off ≤ N₀ˢ`; `M_off ≤ (1/6 + ε)N`; at least `(4/5 − ε)` of the zero ordinates carry a critical zero (`four_fifths_critical_ordinates`); at least `3/4` of the zero copies lie within `4/log T` of the line (`three_quarters_within_four_div_log`); either `N₀ ≥ (3/4)N` or at least `(HD(1) − 1/2 − 1/A − ε)N` simple off-line zeros lie within `A/log T`.
- **Quantized windows** [L] (§1.3): RH iff every unit window has transverse energy `< 2`.
- Aperture flow `μ(A)` strictly decreasing; `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`; polar ground rate equals the width when off-line zeros do not cluster; form-norm rates equal it unconditionally.

### 1.12 Realization and duality

Maximal sharp-stable positive Meyer ideal = off-line-blind ideal; coupled point-stable carriers isotropic; every invariant carrier sees an off-line pair through a boost. Positive self-dual measures with a gap are Dirac combs; affine positivity on `Aff(ℚ)` is induced from dilations; Hecke states `(nd)^{−s}·1[db ∈ ℤ]` are positive definite iff `s ≥ 1/2`; Weil's extensions are a box over the critical zeros. Every nonzero `L²` wave has a visible successor; atomic spectra stay blind; singular-continuous spectra are unclassified [L].

**Every unconditional positivity in the corpus is one of:** invariant (blind, half-blind, isotropic); averaged or statistical; non-localizing; on nonnegative tests; collided (kernel counts, coupled counts, escape forms, `D`); twisted below the conductor horizon; a finite-window certificate; local at one prime (tower forms); positive before a renormalization whose counterterm is the identity (torsion energies) or on the survival cone of a rank-one counterterm (archimedean germ); coefficient positivity of a source (`Λ`, `Λ₂`); or a zero-side reserve (field, outward ray, lens, local detectors) that detects without bounding.

## 2. The 31 routes

Each entry: status; (a) just-work obstacles; (b) open obstacles; walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit, critical-energy and cross-work receivers read `Δ`; RH ⇔ critical energy bounded; high zeros contribute `O(1)`. RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually ⇔ horizon torsion ⇔ the Farey sum at `√N`. RH ⇔ a linear prime-error budget, slope `≥ 2 + γ_E − log 4π`; RH with simple zeros ⇔ the Abel slope tends to the genus. Filtered deficit `Γ^{−1/2}` on frequency averages.
**(a)** An averaged bounded-energy statement from the filtered deficit (W18); windows `Γ^{1/2+ε}` (W7); certified finite budgets (W2); census transport (W14).
**(b)** Signed lag cancellation at every slack (B1.1); an actual budget (B1.10); selection from averages to every height (B1.4); quasi-RH as the first rung (B2.1).
**Walls:** 1.0, 1.1, 1.15, 1.19, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; on the prime-threshold ladder RH ⇔ cumulative relaxation `≤ μ(3/10)`; ground rate = polar rate, equal to the width without clustering. Gårding and fewer than `2AT₀K/π` negative directions at aperture `A`; full floor `1/5000` through `181/500`; no positive exponential floor.
**(a)** Certified floors past `181/500`, including `23/40` (W5); one rate dictionary with SRT and ACS (W18); transport of the census and of the moment-of-inertia law (W4).
**(b)** Zero negative index at every aperture (B1.3); signed shell flux on the moving ladder (B3.4); `polarRate = Δ` for clustering zeros (B3.1); selection (B1.4).
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent; terminal primes realize graph sources; the isolated critical prime channel is negative on narrow windows, not on dyadic windows [S]; a bounded graph norm with vanishing diagonal is not compactness.
**(a)** Finite schedules and histories (W2); premise checks for wide-window channels (W3).
**(b)** Complete-history signed cancellation: seed, inter-cutoff drift, cross-block covariance and endpoints jointly (B1.1).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K + 2)` on the matched-quantile history is RH-equivalent; hyperbola, centroid, square-debt identities and low-LCM payment proved.
**(a)** Finite floors (W2); transport of the low-LCM payment (W4).
**(b)** Full-history floor with high-LCM pairs, moving core and singular transport (B1.1).
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers RH-equivalent; each fixed Hausdorff order is positive beyond its shift threshold.
**(a)** Fixed-order thresholds made explicit (W5); finite-order blocks (W2).
**(b)** Order-uniform thresholds, decoupling rank from shift (B3.10); the all-order passivity sign (B1.5).
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; a one-sided `O(√x)` forces RH with simple zeros; `ν̂_N(1) = M(N)` and RH ⇔ `M(N) = O(N^{1/2+δ})` for every `δ`. A linear Mertens budget forces RH, simple zeros and summable inverse-derivative residues; over `𝔽_q` it is purity with simple spectrum. Balanced and centred-prime bands ⇔ `Θ < 1`. Escaped Möbius pairings: growing-endpoint saving `θ` ⇔ `Θ ≤ 1 − θ`, `θ > 1/2` impossible; uniform VK-rate vanishing `Ce^{−κσ(M)/48}` in the escaped endpoint `M`, independent of the multiplier [L]. Pólya–Vinogradov, Burgess and the least non-residue bound proved; completion needs a period, which the arithmetic point lacks. Multi-modulus Kloosterman packets: two-sided Montgomery–Vaughan dispersion, non-cancellation for `p ≥ 67`, simultaneous omitted-class correction preserving the `17/30` transfer [L].
**(a)** The Mertens converse under RH and `J_{−1}(T) ≪ T` (W18); finite budgets (W2); VK as a range instance of the growth-to-forcing law (W16).
**(b)** Square-root cancellation at the gauge point `0` (B1.1); an actual Mertens budget (B1.10); quasi-RH (B2.1); power-saving sign correlations (B2.6); a gauge-charged statistic at `0` beyond the square-root threshold (B3.15); growing-packet signed compensation (B3.6).
**Walls:** 1.0, 1.1, 1.12, 1.18, 1.19, 1.20, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2`; RH ⇔ the bound at every `t ∈ (0, 1/2)`; one-sided `D_t(N) ≤ C` is RH-equivalent; restricted current signs and continuum light-cone positivity.
**(a)** Finite Wold covariances (W2); transport to ACT/OWU coordinates (W4).
**(b)** Signed nonlocal covariance, equivalently complete odd/primitive Weil positivity (B1.3).
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** RH ⇔ all-height head coefficient positivity at fixed `R² ≥ 1/2`; every positive heat repairs high heads; reality beyond `2π exp((27/40 + ε)/t)`.
**(a)** The explicit residual region (W18); finite heads (W2).
**(b)** Zero-heat sign on the residual region (B1.5, B3.7); better de Bruijn–Newman bounds (B2.9).
**Walls:** 1.2, 1.6, 1.14.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace = winding; an integral nonnegative residual below one vanishes; neither the residual sign nor the sub-unit bound is derived.
**(a)** Disc-wise finite traces (W2); Gaussian covariance transport (W4).
**(b)** Residual sign and sub-unit bound for a pre-divisor source (B1.6).
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** Prime-blind and odd receivers; `D_idx` even when finite and RH ⇔ `D_idx < 2`; one-prime Lefschetz receivers; symmetric-square spectra are the sign at one prime. Counting (§1.6): section count, effectivity, naive and convex heights each RH. Two forms (§1.1): RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ `M_f = 0` for every test ⇔ dyadic Hecke defects sub-doubly-exponential. Electrostatics (§1.3): RH ⇔ every right-zero field `≤ 1` ⇔ `< √(2c log γ)` ⇔ `𝓔 < 1` ⇔ every unit window has energy `< 2`; `𝓔 < ∞` ⇔ finite off-line index; arithmetic source work exhausts the copy energy. Torsion (§1.4): `Λ` as log-order of finite rings; prime kernel = sum of local tower forms with local Hodge index; renormalized torsion limit; rank dichotomy; Hecke cocycle.
**(a)** Copy energy versus distinct-point energy (W13); finite quadrature for the readings (W8); finite counterterm and survival-cone computations (W11, W12); transport of the moment-of-inertia, field-threshold and window laws into HF coordinates (W4).
**(b)** The Lefschetz part / zero negative index (B1.3); `D_idx < 2` (B1.7); counting forms (B1.9); equivariance of `D` (B1.11); the field and energy forms (B1.13); finite off-line index (B2.2); compatible oriented families (B3.8); positivity of `Λ ⋆ Λ` as a form (B3.17); a non-classical bound on `M_f` (B3.21); a selective counting polarization (B3.23); alignment at zero ordinates (B3.24); coupled renormalization of the two places (B3.25); anomaly cancellation (B3.26); outward upper control (B3.27).
**Walls:** 1.3, 1.4, 1.16, 1.17, 1.21, 3.13, 3.20, 3.22, 3.23, 14.2, 14.4, 14.18, 14.21, 14.24, 14.26, 14.27.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state above `1/2`; fixed-aperture completion, sharp cuts, domain preservation and nodal convergence proved.
**(a)** Domain and premise checks (W3); transport from RW/SZ (W4).
**(b)** The nodal / reflected-prime inequality, i.e. odd Weil positivity (B1.3).
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the orthant at small time; fixed-rank coercivity; rank-`N` tests blind above height `O(N√log N)`.
**(a)** Explicit fixed-rank regions (W5).
**(b)** Signed coefficients at all degrees under one heat time (B1.5); decoupling rank from time (B3.10).
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** A compact cone-positive renewal operator realizes the denominator through `det₂`; cone positivity does not confine resonances.
**(a)** Finite packets (W2); transport of `det₂` laws (W4).
**(b)** Boundary-current orientation for the actual source (B1.6).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH; collision masses even; Hermite barrier, optimal heat and large-height repair proved.
**(a)** The explicit residual region (W18); finite heads (W2).
**(b)** Cap vanishing for the actual source (B1.6); the residual heat-region sign (B1.5).
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate; off-line reciprocal-depth rates `≤ 1/431`.
**(a)** Finite floors (W2); explicit constants (W5).
**(b)** The subexponential Li floor (B1.7).
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint limits; RH ⇔ nonnegative first variation on RH-complete tent families.
**(a)** Premise checks for limit families (W3); RW transport (W4).
**(b)** The first-variation sign, i.e. Weil positivity on an RH-complete cone (B1.3).
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal admission and Haar approximation RH-equivalent; RH ⇔ admission at every damping ⇔ positive gauge mass of every escape state. Energy-rate law in both directions; Abel atoms; capacity, endpoint, shadow and infinite-height laws; escape forms are collided; escape Laplace split.
**(a)** Premise checks for cofactor families (W3); transport of VK-rate escaped decay and Kloosterman dispersion (W4); completion of working sources (W19).
**(b)** Signed small-damping energy / positive gauge mass (B1.2); exclusion of infinite-height escape (B3.2); quantitative inverse coercivity (B3.3); sub-half signed control (B3.9); a nonzero paid ideal on escape (B3.12).
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** Positive level-one budget ⇔ half-plane bound `< 1/2`; half-power endpoint is RH; Gamma–theta source admitted at all finite supports; unconditional positivity reaches a growing logarithmic prime budget.
**(a)** Finite budgets (W2).
**(b)** The half-power budget (B1.1); quasi-RH as the first rung (B2.1).
**Walls:** 1.0, 1.1, 3.4.

### CTF — Chronological tail and Báez–Duarte approximation
**Status.** Residual = `(1 − readout)² + centred energy`; RH ⇔ both small; floor `κ/log N` exact.
**(a)** Finite dilates (W2).
**(b)** Readout → 1 and centred energy → 0 together (B1.2); quantitative reconstruction (B3.3).
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat trace / critical feature variance
**Status.** All-degree positivity of the two literal grids (`log 2`, `log 3`) on their polar hyperplanes is RH-equivalent; one grid aliases.
**(a)** Finite-degree signs (W2).
**(b)** Both grids at all degrees (B1.5).
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton invariant discs
**Status.** Line-centred Newton discs covering every zero ⇔ RH; the interior margin is subharmonic.
**(a)** Finite disc covers (W2).
**(b)** Covering discs with nonnegative margin (B1.5).
**Walls:** 1.2, 3.2, 14.3.

### BAG — Deterministic zeta self-return
**Status.** Strong, local and cutoff-uniform positive-mass recurrence each RH-equivalent; recurrence exactly at non-zeros; sharp threshold on zero-free discs.
**(a)** Transport of the threshold laws (W4).
**(b)** Returns near possible zeros (B1.7).
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; high-window positivity; full-cone source selection; finite-level existence ⇔ RH; full/even floor `1/5000` through `181/500`, shared by every weight with `w(2) = log 2`.
**(a)** Certified floors past `181/500` (W5); two-prime margin table (W6).
**(b)** Low and mixed modes on an RH-complete cone (B1.3).
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay RH-equivalent; an off-line zero forces a late positive charge floor.
**(a)** Finite truncations (W2).
**(b)** Rank-uniform decay (B1.5).
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity RH-equivalent; light-cone variation positive. At `181/500` the Liouville twin is a height twist of `ζ` plus corrections and is separated by an odd witness; at `23/40` a witness has `W_ζ > ‖F‖²/25`, `W_λ < −(3/10)‖F‖²`, and the Liouville ground eigenvalue stays `< −3/10` at every larger aperture; at `2 log 2` the exact `Λ`/Liouville difference has seven signed autocorrelation terms and the Catalan `(8, 9)` form separates real scale twists from Liouville. The companion certificate and the conductor horizon have no common aperture; the outward-field reserve and the exterior anti-alignment law are zero-side detectors at the same ordinates.
**(a)** The full floor at `23/40` and the margin table of the four `{2, 3}` sign twins; the `{2, 3, 5}` window (W5, W6); moments of the detector polynomial over zero ordinates (W9); the interior prime reading of the reserve (W10).
**(b)** Odd Weil positivity (B1.3); the non-archimedean gauge charge with a surviving margin (B3.16); the odd-sector sign beyond the horizon (B3.20); alignment at zero ordinates (B3.24); outward upper control (B3.27).
**Walls:** 1.3, 1.18, 1.21, 3.4, 3.19.

### PBM — Regularized prime/log-ζ abscissa
**Status.** Half-plane bound at `α` ⇔ convergence on `Re s > 1/2 + α`; RH is `α = 0`; raw positive series diverge at every `Re s < 1`.
**(a)** Transport of the width functor (W4).
**(b)** Quasi-RH (B2.1); critical cancellation (B1.1).
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas divisor-sum criterion
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need growing lcm cores and small moving valuation defects.
**(a)** Finite verifications (W2).
**(b)** The eventual Robin tail (B1.7).
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH; smooth detector at aperture `Cδ^{−2}(4 + |γ|)²`; single-height phase-selective law; eventual all-height saving refuted (Kronecker peaks); one- and two-prime Lefschetz receivers are the strip. The detector twisted to its ordinate is the odd sector of `σ_γ`; conductor-horizon positivity; forcing half; the forcing gap at every height. Zero side: the exterior anti-alignment law at `σ > 1`; the terminal lens; Kronecker dilution of companion clouds with independent ordinates.
**(a)** One rate dictionary (W18); moments over zero ordinates and the interior prime reading of the reserve (W9, W10); windows `Γ^{1/2+ε}` (W7).
**(b)** Selection (B1.4); critical cancellation (B1.1); Weil positivity (B1.3); counting forms (B1.9); signed near-coincidence beyond `½ log Γ` (B3.14); the odd-sector sign beyond the horizon (B3.20); alignment at zero ordinates (B3.24); outward upper control (B3.27).
**Walls:** 1.17, 1.21, 3.1, 3.2, 3.14, 3.19.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** Explicit collar constants (W5); TT/OWU transport (W4).
**(b)** The uniform all-profile reflected collar, i.e. Weil positivity (B1.3).
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation to `Ke^r e^{−c√r}`; Schur payment to a finite head; shared-budget descent; joint signed `2, 3` payment at `23/40` with `1/62` margin; the nine-modulus comb ledger at `2 log 2`. The linear diagonal reserve cancels on the polar-neutral hyperplane; raw continuum prime towers have negative edge energy of order `e^A`; the pole-neutralized full form retains the zero-width criterion. Finite prime forms split into local tower forms with two-sided bounds; their sum has no uniform `ℓ²` ceiling [S]. Square-class couplings are gauge-blind; log-cell covariance fixes the Euler gauge [S].
**(a)** Certified joint payments at larger apertures (W5); coupled finite-part computations on finite order sets (W12); premise checks for the pole-neutralized form (W3).
**(b)** Weil positivity (B1.3); a nonlocal shared-budget calculus with prime-weighted remainder, paying the pole-neutralized continuum form (B3.6); archimedean payment of the local-to-global divergence (B3.25).
**Walls:** 1.3, 3.4, 3.21, 3.23.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; non-localizing positivity; Lefschetz receivers at one and two primes; Weil's layers (§1.5); faithful degree needs RH + simple zeros.
- Counting (§1.6): six currencies; polar box; Jacobi–Hurwitz dichotomy.
- One-variable systems and deformations (§1.9): `κ = 1` class `ℝ^× · ζ`; contraction and collision calculus; polar-configuration cone; Kronecker dilution; coupled class not rigid; per-ordinate equivalences; critical transfer and conservation; quantization of surplus residues; ceiling transfer; `ζ^d` rigidity; irreversibility of positive deformations.
- Two forms, electrostatics and torsion (§1.1–§1.4): `W = D − Δ`; `D` the log-Sobolev norm; the moment-of-inertia law; the field and energy laws; Selberg's source; local tower forms; survival law and rank dichotomy.
- Census (§1.11).
**(a)** The selectivity battery (W1); the full-class ceiling at zero-free ordinates as central nonvanishing and the quantization law in ACS coordinates (W18); contraction calculus last items (W17); survival-cone computations (W12); completion of working sources (W19).
**(b)** Forcing for a realization (B1.6); RH with simple zeros for the faithful branch (B1.8); counting forms (B1.9); equivariance of `D` (B1.11); ceilings and chirality (B1.12); the field and energy forms (B1.13); the equality case of collar capacity (B3.13); form positivity of `Λ ⋆ Λ` (B3.17); the full coupled class at the centre (B3.22); a selective counting polarization (B3.23); coupled renormalization (B3.25); anomaly cancellation (B3.26); the `3/4` proportion (B2.5).
**Walls:** 1.3, 1.15, 1.16, 1.17, 1.21, 3.8, 3.14, 3.18, 3.23, 14.4, 14.8, 14.10–14.27.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing; each faces B1.6. Fourteen theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- multiplicative correspondences act hyperbolically at every off-line pair; elliptic localization in correspondence-closed carriers is resonance; the only reflection-compatible affine localizer is `σ_γ`, whose odd-sector certificate is separated from the conductor horizon at every height;
- positivity on nonnegative tests is shared by every dominated twin; a square-class coupling cannot tell `ζ` from Liouville's twin;
- finite multiplicative certificates are capped by growth input; positive packets on independent ordinates buy at most their pole share;
- a mechanism must separate `ζ` from the relaxation models, `W_β`-deformed coupled members and the sign twins (which unconditional positivity of `ζ` already separates at `181/500` and from `23/40` on);
- a mechanism built from multiplicative data proves its conclusion for the whole gauge orbit;
- kernel, coupled and escape-form positivity and `D` are collided and see no sign; `D` is computed, positive, faithful, the log-Sobolev norm, and its equivariance is RH;
- a section count, effectivity function, naive or convex height, one-sided count, fixed tensor loss or horizon torsion is the sign; Stepanov auxiliaries need a lattice spectrum;
- a counting polarization that is the same on every fibre is not selective; a large-sieve majorant inflates quadratically;
- positive one-variable constructions remove a complex quartet only against a real anchor;
- positive deformations keep the off-line divisor and cannot be reversed; at zero-free ordinates surplus residues are even central drops;
- positivity of torsion energies is carried entirely by an identity counterterm (survival cone `{0}`); the archimedean germ keeps positivity only on the polar hyperplane;
- local positivity at each prime does not sum to a global bound;
- zero-side reserves (the field, the outward ray, the lens, local detectors) detect an off-line zero; they supply no upper bound that excludes it.

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; Fredholm trace receiver exact. | W1–W3 | Annihilation of the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support; finite cutoffs trace-blind. | W1, W2 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W1, W2 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; capped atlas. | W2, W3 | Global compatible roots, i.e. the regularized abscissa (B2.1, B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation; centred exterior decay. | W2–W4 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W1, W2 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = sum over off-line zeros of `log\|ρ/(1−ρ)\|`, zero on critical zeros. | W2 | Cofinal contrast equality (B1.7); the contrast is a depth capacity like `Δ` and `𝓔`. |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W1, W2 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W1, W2 | Source lift with integral count (B1.6); an integral count is the sign (B1.9). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source; critical logarithmic discrepancy in `L²`. | W2, W3 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained; strong finite-prime convergence with norm gap. | W2 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; Ξ-limit ⇔ RH; prime-log stacks cannot converge to Ξ. | W2 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Full finite-support admission; energy probabilities erase grade. | W2 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0; canonical polarization wall-singular. | W2, W3 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W1, W2 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centred real compact-uniform convergence suffices. | W2, W4 | Arithmetic couplings with a centred limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W2 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic, with exact depth laws; they detect, they do not force. FEL's contrast, the defect `Δ`, the moment of inertia `M_f` and the transverse energy `𝓔` are nonnegative depth capacities vanishing exactly on critical zeros; none has an arithmetic upper bound. ConjugateDiagonalGeometry computes zero-indexed depth functionals from `ξ` and polynomially many theta values; the Rankin–Selberg square computes the field. Both remove the circularity of zero-indexed definitions, not the missing bound.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; bands ⇔ `Θ < 1`; half-damping transition; every power improvement ⇔ a fixed strip; escaped-μ VK decay uniform in `N, a, b`; seven-way quasi-RH equivalence [L]. | W4, W16 | B2.1; B1.2 |
| **ACCE / ACCC** aperture flow, rates, long moduli, compensation | §1.11; long-modulus decomposition, integrable producer, bounded square-root head energy; multi-modulus Kloosterman dispersion and simultaneous omitted-class correction [L]. | W18 | B3.1, B3.4, B3.6; B1.2 |
| **ADR / AOT** cofactor modules | Record minima, contraction calculus, eigencharacter moduli, translated-zero escape rows, Mellin residues pin power-like solutions to translated zeros, two-factor pole trace. | — | B3.2, B3.3, B3.12 |
| **ACS / Meyer** | §1.5, §1.11, §1.12; Lefschetz sequences grow at the zero width. | W1 | B1.6, B1.8 |
| **ACP** correspondence positivity | Normalized graphs, budget, local types, resonance, section and Stepanov counts, symmetric-square spectra, sparse annihilators, escape alternative, Abel atoms, budget currencies, successor defect in `H²`; terminals and the outward ray; `Λ ⋆ Λ` and the source field at every zero. | W10, W18 | B1.10, B3.16, B3.18, B3.19, B3.27; B1.9 |
| **AES** arithmetic electrostatics | §1.3 and the torsion side of §1.4: virial laws, equilibrium ⇔ critical (finite), divisor energy and its threshold forms, work exhaustion, window quantization, field threshold, external field law, moment-of-inertia law, Selberg's source, self-intersection, logarithmic counterterm, arithmetic point, power-map similitudes, Fekete equilibrium [L/S]. | W11, W13 | B1.13, B3.21, B3.24, B3.25 |
| **AIT** arithmetic intersection theory | §1.4: log-orders, different, projection formula and regulator anomaly, Hecke cocycle, tower form, local Hodge index per prime, local forms do not sum [S], Gauss digamma duality [L/S]. | W11, W12 | B3.25, B3.26 |
| **RBG** renormalized biarithmetic geometry | Survival law; counterterm rank dichotomy; archimedean germ on the polar hyperplane; pole node; periodic germs; dyadic amplification and its RH equivalence; Hecke moment problem; lossless theta transfer; gauge charge of couplings; cells fix the gauge; critical discs and terminal lens; irreversibility; Kronecker dilution [L/S]. | W12 | B3.16, B3.21, B3.25, B3.26 |
| **PL** arithmetic polarization | Polarization law, elliptic localizers, twisted sectors, conductor horizon, forcing half, collision law, rate neutrality, oscillatory capacity; `D` faithful, coercive, the log-Sobolev norm; Gårding; finite negative index; local Weyl law; depth profile; polar-configuration cone; selectivity battery. | W5, W18 | B1.11, B3.20, B3.21 |
| **CDG** conjugate-diagonal geometry | §1.1: `ξ` current, finite and polynomial theta metrics, local zero detector, depth distribution, two-scale rigidity, conductor–forcing gap. | W8 | B3.21, B3.20 |
| **AE** arithmetic effectivity | §1.5–§1.6: effectivity calculus, Tate, naive and convex heights, polar box, torsion potential and intersections, renormalized torsion energy, completion law, Burgess, least non-residue, Stepanov over `ℤ`, hyperelliptic calibration. | — | B1.9, B3.19, B3.23 |
| **BGG** biarithmetic gauge geometry | §1.8, §1.9: gauge torus, successor holonomy, Catalan and multi-prime repulsion; deformation principle, Abel–Gram law, coupled-class equivalences, strong multiplicity one, square-root deficit law, critical conservation, quantization, ceiling transfer, `ζ^d` boundary capacity, polar-neutral collapse, Ramanujan torsion. | W18 | B1.12, B3.16, B3.22 |
| **SP** selective positivity and thresholds | `181/500` full floor and twin separation; `23/40` separation and continuum-tower obstruction; escaped Möbius three-regime law; parity-lobe obstruction; escape Laplace split; Serre-dual box cohomology; Jacobi–Hurwitz heights. | W5, W6 | B3.6, B3.16, B3.23 |
| **APD** positive duality | §1.12; Hecke states positive definite iff `s ≥ 1/2`; Kakutani wall; Bost–Connes temperature = Hecke exponent. | — | B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, decay-exponent mass law, Beurling threshold, families, Siegel exception; independent-frequency packets and Fejér packets. | W16 | — (complete below RH strength) |
| **SBWF** strip Bochner–Weil forcing | Completed-system collars; `κ = 1` class; `5d < 9κ`. | — | B3.13 |
| **ACG** correlation geometry | Gauge invariance, a.e. laws, comeager-null exceptions, prime pole, archimedean-line threshold, charged boundaries at `1/4`, loss law, gauge-mass criterion, coalescent surplus as gauge charge. | W15 | B1.2, B3.15 |
| **AKT** Künneth theory | Product receivers see depth only through total length; Künneth positivity = point-count positivity. | W15 | — |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; base theta `h⁰`. | W4 | B3.8; B2.2 |
| **ALDG** local divisor heat | Hermite barrier, optimal heat, residual region model complete. | W18 | B3.7; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; phase-selective single height; finite-level existence. | W4 | B1.4, B3.14 |
| **BiScale** lag, packet, filtering, observation | Endpoints; high-zero tail; filtered deficit; closed-cycle recovery; binary-parent coercivity with constant `8`; exact-doubling incidence and its discontinuous constant. | W7, W18 | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt. | W2 | B3.6, B3.9 |
| **SSA** signed successor | Odd-shift `1/3`, lag-2 `1/4` floors exact. | — | B3.11, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half. | — | B3.9 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure. | — | B3.3 |
| **TTPC** coalescent pairs and census | `N₀* ≥ (29/36 − ε)N − surplus`; parity-blind dispersion cannot give `β < 5/36` at `λ = 4/3`; parity-locked even-shift Ramanujan transfer; census of §1.11. | W14 | B2.5, B2.7, B3.15 |
| **HTG** tools | Fejér–Riesz; Bochner uniqueness for Laplace weights; lattice Fourier vanishing ⇒ absolute continuity; planar log-square bounds; quadratic ascent. | — | — |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density on windows `≥ U^{99/100}`; Heath-Brown; KKL; dlVP, Littlewood, VK; smoothed Landau formula (`exists_smoothedLandau_le`); Cramér mean square under RH; the two-thirds certificate. | W7, W9, W16 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - What computes `D` (the `ξ` current and polynomially many theta values, with local zero detection) and which norm it is (the log-Sobolev norm at each aperture).
  - What the Hecke defect measures: the transverse moment of inertia `M_f`, within the factor between `4L²` and `8(cosh L − 1)`; and how it amplifies (dyadically, with the fixed loss `D(f)`; RH is sub-doubly-exponential growth).
  - Whether `W` can have infinitely many negative directions at one aperture: no, fewer than `2AT₀K/π`.
  - The forcing gap: the companion certificate and the conductor horizon are disjoint at every height.
  - The electrostatic forms of RH: zero energy, energy below one quantum, unit-window energy below two, right-zero field at most one or below `√(2c log γ)`; finite energy is finite off-line index; equilibrium of finite reflection-closed configurations is criticality.
  - Whether an off-line zero leaves an arithmetic trace at its own height: yes, a terminal with positive field, an outward reserve, a zero-free lens; and, outside the strip, an exterior anti-alignment of the primes at its ordinate.
  - Whether torsion-side renormalization can keep positivity: no. The torsion counterterm is the identity, every renormalization has survival cone `{0}`, the minimal counterterm on orders `≤ N` is `≍ log N`, its divergence sits at the arithmetic point, and the Hecke cocycle is not a bounded coboundary.
  - Whether the archimedean germ is positive after renormalization: only on the polar hyperplane; with the arithmetic-point node, everywhere.
  - Whether local positivity at each prime gives a global bound: no; the prime form has no `ℓ²` ceiling.
  - Which couplings carry gauge charge: exactly the non-square-class ones; successor and cell structure fix the gauge.
  - The edge problem at `181/500` and the first non-archimedean twin at `23/40`: both twins fail on explicit witnesses on which `ζ` is positive; the Liouville separation persists at every larger aperture.
  - Whether the prime-error budget is weaker than RH: no; with the Abel slope at the genus it is RH with simple zeros.
  - Escape at the zero abscissa (both directions of the energy-rate law) and at infinite height (complete classification).
  - Positive and rational deformations of the coupled carrier: rigid exactly at zero-free ordinates; surplus residues are even central drops; positive deformations are irreversible.
  - How far statistics reach: `3/4` of the copies within `4/log T`, `4/5` of the ordinates critical.
  - Budget currencies over `𝔽_q`; hyperelliptic RH by counting; kernel counts are not naive heights (complex fake); section counts, effectivity, naive heights and one-sided counts are the sign; elliptic localization is resonance; contraction and collision calculus; theta `h⁰` does not extend; multiplicative lattice forms are blind; the first gauge charge is a twist; theorem of the square and budget free; positivity beyond isotropy only without localization; `κ = 1` class; one- and two-prime Lefschetz receivers; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`.
- **Excluded mechanisms** (in addition to the [killed-routes catalogue](../rh-killed-routes.md)):
  - collided coercivity, sampling, log-Sobolev equivalence or finite negative index offered as Weil's sign;
  - the computed `D`, `E_f`, `M_f`, the field, the transverse energy or the local readings offered as bounds on themselves;
  - dyadic amplification offered as an output stronger than a rate;
  - the companion-forcing certificate spliced with the conductor horizon;
  - the outward-field witness, the terminal lens or a local zero detector offered as exclusion; the exterior anti-alignment law continued into the strip without an interior estimate;
  - torsion-energy positivity, or any renormalization with scalar counterterm, offered as Weil positivity; local tower bounds offered as a global bound;
  - square-class (diagonal, ratio, product) couplings offered as gauge selectors; gauge fixing by cells offered as positivity;
  - positive or rational deformations of `ζ_γ`, or surplus quantization, offered as forcing;
  - budget currencies, convex heights or Farey sums offered as inputs weaker than the sign; large-sieve majorants offered as sections;
  - raw continuum prime towers as sub-half floors; completion at the arithmetic point; sparse annihilators as Stepanov auxiliaries over `ℤ`;
  - zero statistics (census, averages, almost-every-ordinate positivity) offered as exclusion of an individual zero; collective packets on independent ordinates offered as amortization.
- **Substitutions that do not hold.** Computed for bounded; detected for excluded; collided for Rosati; positive for equivariant; equivariant for positive; norm for sign; sampling for positivity; finite index for zero index; resonance for localization; twist for gauge charge beyond the first prime; gauge fixing for positivity; soft polarization for selective polarization; positive deformation for arbitrary member; rational ceiling for full ceiling; one-sided ceiling for two-sided rigidity; classification of escape for its exclusion; budget for sign; regularized limit for limit of positivity; scalar counterterm for renormalized positivity; local Hodge index for global; exterior estimate for interior; amplification for improvement of rate; finite-level count for the arithmetic point; finite window separation for all-aperture selection; averages and proportions for individual zeros; nonnegative tests for the full cone; zero-indexed objects for pre-divisor constructions; reserve for contradiction.
