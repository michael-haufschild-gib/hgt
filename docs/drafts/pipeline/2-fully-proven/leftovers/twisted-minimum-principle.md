# The twisted minimum principle on the modular bottom arc

**Status:** fully proven on paper. The only external inputs are the classical potential-theory facts (C1)–(C4). The 1D core
is in Lean. Producer for (N1) of route HF.

## Statement
Let A = {e^{iα} : π/3 ≤ α ≤ 2π/3}. For u = cos α ∈ [−½, ½], let M_n(u) = ∫ g_u(x) cos(2π(n+2)x) dx be the
twisted moments (`twArcMoment`).

**Theorem (TMP).** There is a nonzero finite positive measure κ on [−½, ½] with ∫ M_n dκ = 0 for every n ≥ 0.

Consequences:
- `TwistedArcMinimumPrinciple` holds.
- By `riemannHypothesis_iff_primeBlindPositive_of_twistedArcMinimumPrinciple` [L], RH ⟺ PBAP.

## Setting
- **Fundamental strip.** F = {|u| ≤ ½, u² + y² ≥ 1} with u ↦ u+1 identified: a half-cylinder whose boundary is A, with the
  corner P = ½ + i√3/2 glued (interior angle 2π/3) and a cusp at y = ∞.
- **Operator.** Lf := div(y∇f) = y(f_uu + f_yy) + f_y, the axisymmetric 3D Laplacian; it has no zeroth-order term.
- **Periodic solutions.**
  - m = 0 modes: 1 and log y.
  - Decaying modes: Φ_m = K₀(2πmy) cos 2πmu.
  - Growing mode: J = I₀(2πy) cos 2πu.
- **Arc coordinates.** On A use s = log tan(α/2) ∈ [−S, S], S = ½ log 3. The spherical Laplacian is
  𝔐 = cosh²s ∂_s² = ∂_u(1−u²)∂_u, and the surface measure is sin α dα = sech²s ds.

## Classical inputs
- **(C1) Dirichlet problem.** For continuous even g on A there is a unique bounded L-harmonic D_g on F, continuous on F̄,
  with D_g = g on A. Above y = 1 it expands as ω(g) + Σ_m d_m Φ_m, where ω is the cusp harmonic measure (a probability
  measure on A). Its flux is continuous on the open arc and O(r^{½}) at P when g is smooth.
  - *Grounds:* Perron's method for uniformly elliptic operators on the Lipschitz domain F ∩ {y < Y}, plus separation of
    variables above y = 1 and Phragmén–Lindelöf at the cusp (log y is unbounded).
- **(C2) Corner Martin kernel.** There is a unique positive L-harmonic K̃_P on F with:
  - K̃_P = 0 on A ∖ {P};
  - K̃_P → 1 at the cusp, with no log term;
  - K̃_P = C̃ r^{−3/2} sin(3θ/2) + O(r^{−½}) at P, with C̃ > 0;
  - flux > 0 on the open arc (Hopf).
  - *Grounds:* Martin boundary of Lipschitz domains (Hunt–Wheeden), and the corner expansion for an angle 2π/3 with
    analytic sides and analytic coefficients (Kondratiev).
- **(C3) Corner regularity.** A solution vanishing on A near P is c r^{3/2} sin(3θ/2) + O(r^{5/2}).
- **(C4) Analyticity.** L-harmonic functions are real-analytic in F, and up to the analytic arc A away from P.
  No longer needed: the stream-function argument in Step 5 replaces the nodal lemma.
- **(C2)/(C3) are elementary.** With g = √y·f, L f = 0 ⟺ (Δ_hyp + ¼)g = 0. In hyperbolic polar coordinates (R, θ) at P
  both arcs are geodesic rays, so the equation separates.
  - The symmetric Dirichlet modes are sin(μθ), μ = 3(k+½).
  - The radial parts are (sinh R)^{−½}·{P_n, Q_n}(coth R), n = 3k+1.
  - For μ = 3/2 these are (sinh R)^{−½}coth R (the corner Martin singularity, ~R^{−3/2}) and (sinh R)^{−½}(R coth R − 1)
    (regular, ~R^{3/2}/3).
  - The sector expansion holds for R < log 3 = d(P, ρ).

## Proof

### Step 1 (Legendre bridge)
- 𝒟_x Q_u(x)^{−½} = 𝔐_u Q_u(x)^{−½}, with Q_u = x² − 2ux + 1, so τ_u = 𝔐_u² Q_u^{−½}
  [L: `twPointVec_eq_legendreOp_sq`].
- With ∫ P_u' sin(ax) = −4aK₀(ay_u)cos(au) [L: `integral_circlePairDeriv_mul_sin`], this gives
  M_n(u) = 4√y·𝔐²ṽ_m(u), where m = n+2 and ṽ_m = Φ_m|_A.
- The integrated form against the clamped Legendre kernels is [L: `integral_twArcMoment_mul_legendreKernel`].

### Step 2 (the potential)
- Let g = J|_A and β := ω(g). Then β > 0 [L: `exists_arcWitness_growingWhittakerCos_pos`, cosine rearrangement, which
  applies to ω because ω annihilates all Φ_m].
- Put Ψ̃₁ := J − D_g. It vanishes on A, is regular at P, and has cusp expansion J − β + Σ K-modes.
- Put Ṽ* := Ψ̃₁ + β K̃_P. It vanishes on A∖{P}, its cusp expansion is J + Σ K-modes (no constant, no log term), and its
  corner coefficient is βC̃ > 0.

### Step 3 (load and deflection)
- Let σ*(s) := sech²s · (r∂_r Ṽ*)|_A, the flux density in ds. It satisfies σ* ~ +c r^{−5/2} at the ends.
- Let κ̃ be the even solution of (cosh²κ̃'')'' = σ* on (−S, S) with κ̃ = κ̃' = 0 at ±S. Write M := cosh²κ̃''.
- Then M'' = σ*, and M'(s) = Φ(s) := ∫_0^s σ*. Here M(0) is fixed by ∫ M sech² = 0 and the additive constant by κ̃(S) = 0.
- M ~ +r^{−½} at the ends, κ̃' is continuous on [−S, S], and κ̃ ~ r^{3/2}.

### Step 4 (blindness)
- For an even smooth trace ṽ, four integrations by parts give
  ∫(𝔐²ṽ)κ̃ sin α dα = lim_{s→S}[∫_{−s}^{s} ṽσ* + 2(ṽ'M − ṽM')(s)].
- Green's identity on F with the corner excised and the cusp truncated gives, for every smooth periodic L-harmonic W near
  F̄ with trace ṽ:
  lim_ε[∫_{A∖B_ε} ṽσ* + (small-arc term)] = (cusp term).
- **Jet matching.** Both regularisations are exact for W with zero 1-jet at P. Hence they differ by a linear functional D
  of the 1-jet (W(P), ∂_yW(P)); evenness gives ∂_uW(P) = 0.
- D vanishes on W = 1 and W = log y. For these 𝔐²ṽ = 0, and the cusp terms vanish because Ṽ* has no m = 0 mode, so
  ∫Ṽ* du = 0 at every height y > 1. The two jets are independent, so D ≡ 0.
- For W = Φ_m with m ≥ 2, the cusp term is 0 at every height (orthogonality of cos 2πmu with the modes of Ṽ*).
- Hence ∫(𝔐²ṽ_m)κ̃ sin α dα = 0 for all m ≥ 2.

### Step 5 (positivity)
- Φ(s) = ∫_0^s flux(Ψ̃₁) + β∫_0^s flux(K̃_P). The second term is > 0 by (C2).
- **Stream-function argument** (replaces the nodal two-domain lemma; no topology and no (C4) needed).
  - Let χ* be the stream function of Ṽ*: χ*_u = yṼ*_y, χ*_y = −yṼ*_u, normalised by χ*(0, y) = 0. It is single-valued
    and periodic because Ṽ* has no log term.
  - It solves L*χ* := χ*_uu + χ*_yy − χ*_y/y = 0 in F.
  - It is odd in u and about u = ½, so χ* = 0 on u = 0 and on u = ½.
  - Ṽ* = 0 on A gives a Neumann condition: the radial derivative of χ* vanishes on the open arc.
  - At the cusp, χ* ~ yI₁(2πy) sin 2πu, which is > 0 on 0 < u < ½.
  - At P, χ* ~ βC̃ r^{−3/2}cos(3θ/2) ≥ 0 on the π/3 sector between A and u = ½. The corrections vanish on u = ½.
  - On the arc, χ*(s) = Φ(s), the cumulative flux counted from u = 0.
  - **Mixed minimum principle** [L: `nonneg_of_neumann_on_modularHalfArc`] gives χ* ≥ 0 on F₊ = F ∩ {u ≥ 0}.
    - The barrier is −(u² + y²): L* of it is −2, and its radial derivative on the arc is −2.
    - So Φ ≥ 0 on [0, S]. Strictness follows from the Hopf lemma at u = 0, or from M(0) < 0 below.
- Therefore Φ ≥ 0 on (0, S), M is nondecreasing on [0, S), and M → +∞ at the ends.
- M(0) < 0: otherwise κ̃ would be convex and clamped, hence ≡ 0.
- So κ̃'' has sign pattern (+, −, +), and κ̃ ≥ 0, κ̃ ≢ 0
  [L: `nonneg_of_coshSq_clampedBeam_of_cumulativeLoad`, which allows the singular ends].
- Equivalently κ̃ = ∫ k_c dν(c) with dν = c·dM ≥ 0: a positive superposition of clamped Legendre running-mean kernels.

### Step 6
dκ := κ̃ sin α dα / √y, transported to u ∈ [−½, ½], is positive, nonzero, and satisfies
∫M_n dκ = 4∫(𝔐²ṽ_{n+2})κ̃ sin α dα = 0. ∎

## Remarks
- Pointwise positivity of the load σ* is not needed; this was the quantitative obstruction in the earlier attempts (C242).
- **Explicit dual.**
  - A certificate whose trace decreases inward from P is refuted with explicit functions alone: clamped beam, minimum
    principle and a corner Hopf lemma.
  - Certificates increasing inward from P provably need the corner Martin potential, because the corner-slope functional
    is positively representable.
  - So the potential theory (C1)–(C4) is indispensable.
- **Rigidity.** κ is the unique twisted-blind measure up to scale, and every compactly supported arc producer reduces to
  it.

## Lean status
- **The theorem is formalised by the dual route:** `RHTower/TwistedArcMinimumPrincipleProof.twistedArcMinimumPrinciple_holds`
  (stream certificate plus minimum principle, no potential theory). The primal construction on this card is
  independent paper mathematics; it gives the explicit annihilator κ̃* and its positivity mechanism.
- [L] Steps 1 (pointwise and kernel form), the positivity conclusion of Step 5, the mixed minimum principle for the
  stream function, and the consequence TMP ⟹ RH ⟺ PBAP.
- Open:
  - (C1) global existence of D_g and K̃_P in Lean;
  - the corner sector expansion (C2)/(C3) with the elementary modes;
  - the Green and jet-matching identity of Step 4;
  - the regularity of the stream function needed for the minimum principle.
