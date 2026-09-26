# Off-line zeros of the theta-power family at transcendental parameters

- **ID:** theta-power-transcendental-offline-zeros
- **Stage:** 1-in-progress
- **Type:** CONJECTURE → THEOREM (paper) → THEOREM (Lean)
- **Source:** 1/theta-power-family-hardy-threshold (C7, survivor C7*).
- **Statement (C7*-T):** for every transcendental a ∈ (0, 1/2) the transform Λ_a of
  F_a = θ₃^{1−2a}(θ₂θ₄)^a has a zero w with Im w ≠ 0 (equivalently M_a(z) = ∫₀^∞ F_a(iy) y^{z−1} dy has a
  zero with Re z > 1/4).

## Goal
Answers the C7 question "does holomorphy at every cusp force RH?" negatively for a co-countable set of parameters,
inside a family where each member spans a one-dimensional space (weight 1/2, Γ_θ, unitary character e^{πia/2} on T²),
has Riemann's functional equation, is holomorphic and vanishing at both cusps, and is zero-free on ℍ. The Euler
points a ∈ {0, 1/6, 1/3, 1/2} are exactly the congruence points (F_a = 2^a η(τ)^{5−12a}(η(τ/2)η(2τ))^{6a−2} has integer
exponents iff 6a ∈ ℤ). So neither modularity, cusp holomorphy nor multiplicity one forces RH; arithmetic does.
Literature: Nakamura's quadrilateral zeta Q(s,a) (arXiv 1712.05169, 1910.09837; jxiv 238) is the closest analogue
(exceptional set {1/2,1/3,1/4,1/6}); its proof uses explicit Hurwitz coefficients. Here no coefficient asymptotics
are known; the proof below is coefficient-free.

## Paper proof
Notation: 0 < a < 1/2, α = a/4 ∈ (0, 1/8), F = F_a (holomorphic, zero-free on ℍ, F(τ+2) = e^{2πiα}F(τ),
F(−1/τ) = (−iτ)^{1/2}F(τ), |F(iy)| ≤ C e^{−παy} for y ≥ 1).

(P1) q-expansion. G(τ) = e^{−πiατ}F(τ) is 2-periodic and bounded for Im τ ≥ 1, so G(τ) = Σ_{n≥0} b_n e^{πinτ},
b_0 = 2^a. F(τ) = Σ_{n≥0} b_n e^{πi(n+α)τ}. Parseval on Im τ = y:  ∫₀² |F(x+iy)|² dx = 2 Σ |b_n|² e^{−2π(n+α)y}.

(P2) Two-sided modular bound. For every g ∈ SL₂(ℤ) the modulus law ‖θ_j(τ)‖ = |cτ+d|^{−1/2}‖θ_{π(j)}(gτ)‖
(corpus `thetaModulusLaw`) gives Φ(τ) := |F(τ)|² Im(τ)^{1/2} = Im(gτ)^{1/2}(A^a C^a B^{1−2a})² with {A,B,C} the three
theta moduli at gτ. With gτ in the SL₂(ℤ) fundamental domain (Im ≥ 4/5): |θ₃|,|θ₄| ∈ [1/2, 3], e^{−πIm/4} ≤ |θ₂| ≤ 3e^{−πIm/4}.
(a) Hecke: θ₂'s modulus carries exponent a or 1−2a > 0, so Φ ≤ C_H for all τ (0 < a < 1/2).
(b) Lower: if Im(gτ) ≤ K then Φ(τ) ≥ c_K := (4/5)^{1/2} min(e^{−πK/4}, 1/2)².

(P3) Horocycle mass. For 0 < y ≤ 1/16: the set of x ∈ [0,2] whose reducing g has Im(g(x+iy)) > K = 16 lies in
⋃_{1≤c≤(Ky)^{−1/2}} ⋃_d {|cx+d| < (y/K)^{1/2}}, of measure ≤ 8/K = 1/2. Hence ∫₀² Φ(x+iy) dx ≥ c_16 and
Σ|b_n|² e^{−2π(n+α)y} ≥ (c_16/2) y^{−1/2}.

(P4) Coefficients. |b_n|² e^{−2π(n+α)y} ≤ Σ ≤ (C_H/1) y^{−1/2}; y = 1/(n+α) gives |b_n| ≤ C_b (n+α)^{1/4}. Also
Σ_{n+α≤X}|b_n|² ≤ e^{2π}C_H X^{1/2}, so Σ|b_n|²(n+α)^{−2σ} < ∞ for σ > 1/4. And Σ|b_n|²(n+α)^{−1/2} = ∞: otherwise
y^{1/2}Σ|b_n|²e^{−2π(n+α)y} → 0 by dominated convergence, contradicting (P3). With |b_n| ≤ C_b(n+α)^{1/4}:
S(σ) := Σ_{n≥1}|b_n|(n+α)^{−σ} ≥ C_b^{−1}Σ_{n≥1}|b_n|²(n+α)^{−σ−1/4} → ∞ as σ ↓ 1/4. Since every term r_n(σ) =
|b_n|(n+α)^{−σ} ≤ R := max(2^a α^{−1/2}, C_b) for σ ∈ [1/4, 1/2], there is σ₀ ∈ (1/4, 1/2) with Σ_{n≥0} r_n(σ₀) > 2R + 1
(polygon condition).

(P5) Dirichlet series. For Re z > 5/4: M(z) = Γ(z)π^{−z}D(z), D(z) = Σ b_n (n+α)^{−z}; D := π^z M/Γ is entire.
For δ > 0, D^δ(z) := Σ b_n e^{−πδ(n+α)}(n+α)^{−z} (entire), E^δ := D − D^δ = π^z M^δ/Γ with
M^δ(z) = ∫₀^∞ [F(iy) − F(i(y+δ))] y^{z−1} dy.

(P6) Mean square. Rotating the Mellin ray to arg τ = φ (strip contour shift in log coordinates; decay at both ends
for Re z > 1/4 + η) and applying the Plancherel inequality ∫|𝓕g|² ≤ ∫|g|² (Gaussian regularisation: Fubini,
Gaussian kernel of mass one, Schur) to g(u) = e^{σu}H(e^{u+iφ}), H = F(·) − F(·+iδ):
  ∫_ℝ |M^δ(σ+it)|² e^{2(π/2−φ)t}·(dt/2π) ≤ ∫₀^∞ |H(ye^{iφ})|² y^{2σ−1} dy.
Cauchy estimate |F'(τ)| ≤ C Im(τ)^{−5/4} and |H| ≤ 2C_H^{1/2} Im^{−1/4} give |H(τ)| ≤ C δ^η Im(τ)^{−1/4−η}; with
exponential decay for Im τ ≥ 1 the right side is ≤ C δ^{2η}(sin φ)^{−2σ}/(σ−1/4−η). Stirling |Γ(σ+it)| ≥ c|t|^{σ−1/2}e^{−π|t|/2}
and φ = 1/T give ∫_T^{2T}|E^δ(σ+it)|² dt ≤ C δ^{2η} T, uniformly for σ in compacts of (1/4+η, ∞) (and t ↦ −t by
conjugation symmetry b_n ∈ ℝ).

(P7) Target. Disc K' = closedBall(σ₀, ρ) ⊂ {Re z > 1/4 + η}, K = closedBall(σ₀, ρ/2), β_n(z) = b_n(n+α)^{−z}.
Blocks N_k < n ≤ N_{k+1} with Σ_block ‖β_n‖²_{L²(K')} ≤ 4^{−k}; choose phases greedily inside each block
(Re⟨partial, β_n e^{iθ_n}⟩ ≤ 0) so ‖block sum‖ ≤ 2^{−k}: f = Σ β_n e^{iθ_n} converges in L²(K'), hence locally uniformly
on K. Re-choose the phases n ≤ N₀ (N₀ a block end with |f − S_{N₀}|(σ₀) ≤ 1) by the polygon lemma so that f(σ₀) = 0
(vectors of lengths r_0..r_{N₀} reach any v with 2r_max − Σr ≤ |v| ≤ Σr). Two distinct polygon solutions exist; by linear
independence of distinct exponentials at most one gives f ≡ 0, so f ≢ 0 and σ₀ is an isolated zero.

(P8) Transfer. λ_n = log(n+α) are ℚ-independent (a transcendental; corpus `log_shifts_independent`). Let
r = min_{|z−σ₀|=ρ'}|f| > 0. With N a block end (‖f − S_N‖ < r/8, Σ_{n>N}‖β_n‖² < r²/64), a nonnegative trigonometric
polynomial ψ in φ_1..φ_N (product of Fejér kernels at θ_n, ∫ψ = 1, ∫ψ Σ‖β_n‖²|e^{iφ_n}−e^{iθ_n}|² small), and
δ small, the average over t ∈ [T,2T] of ψ(−tλ)·‖D(·+it) − f‖²_{L²(K')} is < r²·avg ψ /16 for T large: all trigonometric
cross terms have nonzero frequencies k·λ (independence), whose averages are O(1/T); the middle block contributes
(∫ψ)Σ_{N<n≤M}‖β_n e^{−πδ(n+α)}‖² ; E^δ contributes ≤ ‖ψ‖_∞ C δ^{2η}. Hence some t has ψ > 0 and ‖D(·+it) − f‖_{L²(K')} < r/4.

(P9) Conclusion. Bergman sub-mean value turns L²(K') closeness into sup closeness on |z − σ₀| = ρ'; Rouché (corpus
sphere-domination / `eventually_exists_zero_closedBall_of_tendstoLocallyUniformly`) gives a zero of D(·+it) in K, i.e.
a zero z* of M with Re z* ∈ (1/4, 1/2); w* = i(2z* − 1/2) has Im w* ≠ 0 and Λ_a(w*) = M(z*)/4 = 0.

## Lean plan (descriptive module names)
1. ThetaPowerModularTwoSidedBound — (P2) Hecke bound and compact-part lower bound.
2. ThetaPowerHorocycleMass — (P3).
3. ThetaPowerFourierExpansion — (P1), (P4).
4. ThetaPowerDirichletSeries — (P5).
5. PlancherelInequalityReal — Plancherel inequality by Gaussian regularisation.
6. ThetaPowerMeanSquare — (P6).
7. DirichletTargetConfiguration — (P7), generic in (b_n, λ_n).
8. IndependentFrequencyTransfer — (P8), generic.
9. ThetaPowerTranscendentalOfflineZeros — (P9) and the final theorem.

## Log
- 2026-09-26 — created; paper proof complete modulo routine estimates; Lean bricks 1–9 open.
- 2026-09-26 — bricks [L]: ThetaPowerModularTwoSidedBound (Hecke |F_a|Im^{1/4} ≤ C_H, compact-part lower bound),
  ThetaPowerHorocycleMass (∫₀²|F_a(x+iy)|² ≥ L²(2−6/K)y^{−1/2}, bad set ≤ 6/K), ThetaHauptmodulLogTranslation
  (log h = log16 + πiτ + Log Q near i∞; log h(τ+2) = log h(τ) + 2πi; F_a(τ+2) = e^{πia/2}F_a(τ)),
  ThetaPowerFourierExpansion (F_a = Σ b_n e^{πi(n+a/4)τ} via cusp function), AbsoluteTrigSeriesParseval,
  ThetaPowerCoefficientMass (horizontal Parseval, C_H²y^{−1/2} ≥ M(y) ≥ c y^{−1/2}, |b_n| ≤ C(n+α)^{1/4},
  Σ|b_n|²(n+α)^{−1/2} = ∞, Σ|b_n|(n+α)^{−1/4} = ∞, polygon mass `exists_sigma_partial_mass_ge`),
  HTGeometry/GammaVerticalSharpBound (|Γ(σ+it)|⁻¹ ≤ C|t|^{1/2−σ}e^{π|t|/2}, 0 ≤ σ ≤ 1, via Phragmén–Lindelöf on
  Γ(z)⁻¹(z+2)^{z−1/2}). Open: Dirichlet series D, rotated Mellin mean square, Plancherel inequality, target, transfer.
- 2026-09-26 — bricks [L]: ThetaPowerDirichletSplit (M entire = 4Λ_a(i(2z−1/2)); termwise M_δ = Γπ^{−z}D^δ;
  D = D^δ + E^δ on Re z > 0; off-line D-zeros ⇒ off-line Λ_a zeros), HTGeometry/PlancherelInequalityReal
  (∫|Ĝ|² ≤ 2π∫|g|², Gaussian regularization), ThetaPowerShiftDifferenceBound (envelope, Cauchy F', |F(τ)−F(τ+iδ)| ≤
  3C₁δ^ηIm^{−1/4−η}e^{−(πa/16)Im}), ThetaPowerMeanSquare (rotation to angle π/2+2c via strip shift, Plancherel,
  translation by (log cos2c)/2, sharp Γ ⇒ `exists_lintegral_thetaPowerDirichletError_le`: ∫_T^{2T}|E^δ(σ+it)|² ≤ Cδ^{2η}T).
  Remaining plan (revised, no area integrals): (A1) Cauchy circle-average sup bound; (A2) greedy phases in
  L²(circle R₂) block-wise ⇒ convergent target, uniform on closedBall R; (A3) polygon closure with one fixed side
  (greedy partition + triangle); (A4) two reflected solutions + independence of (n+α)^{−z} ⇒ f ≢ 0; (A5) isolated zero
  ⇒ sphere radius r with min|f| = m > 0; (B) averaging of products of one-coordinate trig polynomials in ℚ-independent
  frequencies (limit = product of constant terms), Fejér weights ψ = ∏F_L(φ_n − θ*_n) (mean 1, weighted miss 2/L),
  mean-square for E^δ, circle Cauchy bound ⇒ ∃t: 3|D(·+it) − f| ≤ |f| on sphere ⇒ `exists_zero_of_sphere_domination`.
- 2026-09-26 — **C7*-T PROVED IN LEAN.** `RHTower.thetaPowerXiC_offline_zero_of_transcendental : 0 < a → a < 1/2 →
  Transcendental ℚ a → ∃ w, 0 < w.im ∧ w.im < 1/2 ∧ thetaPowerXiC a w = 0`; axioms [propext, Classical.choice,
  Quot.sound]; `lake build` of the module passes; lint clean. Final bricks: RHTower/ThetaPowerSmoothDirichletBounds
  (|(n+α)^{-z}| ≤ α^{-2}, D^δ bounded/continuous on 0<Re<2, vertical-shift decomposition),
  RHTower/ThetaPowerErrorCesaroMeanSquare (∫₀ᵀ|E^δ(z+it)|² ≤ C₀(δ) + 4Cδ^{2η}T via dyadic blocks),
  HTGeometry/FejerWeightedQuadraticAverage (ψ-averages: mean 1, unit distance 2/L, quadratic form → diagonal),
  HTGeometry/WeightedDoubleIntegralBound (Tonelli bound for ∫ψ·∫q), RHTower/ThetaPowerFejerTransfer (circle
  majorant, averaging lemma, `exists_shift_near_target`), RHTower/ThetaPowerTranscendentalOffLineZero (Q-independence
  of log(n+a/4) from transcendence, target parameters, sphere domination).
  Consequence for C7: holomorphy at every cusp does not force RH — every transcendental a ∈ (0,1/2) has an off-line
  zero at 0 < Im w < 1/2. C7 as stated (all interior a) implies ¬GRH(χ₁₂) (a = 1/3) and stays CIRCULAR.
  Next: openness of the off-line set in a (Hurwitz/sphere domination) ⇒ RH-exceptional set is closed, countable,
  algebraic; unboundedly many good translates ⇒ infinitely many off-line zeros.
- 2026-09-26 — upgrades [L]: `thetaPowerXiC_offline_zeros_infinite_of_transcendental` (infinitely many zeros with
  0 < Im w < 1/2; the transfer now yields translates t ≥ T₀ for every T₀); RHTower/ThetaPowerOffLineParameterSet:
  `isOpen_thetaPowerOffLineSet`, `countable_thetaPower_exceptional`, `thetaPower_exceptional_algebraic`,
  `isClosed_thetaPower_exceptional_in_interval` — the RH-exceptional set E ⊂ (0,1/2) is closed, countable, algebraic.
  Successor card: 0-backlog/theta-power-exceptional-set-integral-exponent.md (C7**: E ⊆ {1/6, 1/3}; η-form
  F_a = 2^a η g^{6a−2}).
