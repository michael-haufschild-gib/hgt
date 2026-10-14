# The modular null face of the Weil cone is a single ray

- **ID:** modular-null-face-ray
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** rh-goal-loop-opus-2026-09-29.md rows 1188, 1189 (C1189b), 1195, 1198
- **Statement:** The finite measures ν on the modular bottom arc u ∈ [−½, ½] that annihilate every twisted moment M_n (`twArcMoment n`, n ≥ 0) form a one-dimensional space spanned by the TAMP measure ν*.

## Goal
- **Cone geometry.** It would make the twisted-arc null test T canonical, so ζ's datum is exposed by a unique arc functional (row 1188: smoothness of the admissible cone at A within the arc family).
- **Pole-sign law.** Every arc-blind positive-definite null test would have pole ∝ m₀(ν*) > 0. So no "odd" arc test exists, and pole weights β > 1 cannot be excluded by arc null tests (C1195 answered negatively within the family).
- **Not an RH producer.** It is a uniqueness-side structure theorem.

## Gates
- [ ] 0 → 1  in-progress: reduction below checked against the Lean definitions
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
1. **Reduction [P].**
   - twPointVec c x = 𝔐_c² Q_c(x)^{−1/2}, where Q_c(x) = x² − 2cx + 1 = |x − z_c|² and z_c = c + i√(1−c²) lies on the unit circle.
   - So M_n(c) is the Fourier transform in x at k = 2π(n+2) of the 𝔐_c²-image of 1/|x − z_c|, which by Basset's integral is 2K₀(k y_c) cos(k c).
   - Hence ν annihilates every M_n ⟺ the witness W_ν(x) = ∫ twArcVector(u, x) dν(u) has Fourier transform vanishing at 2πN for all N ≥ 2.
   - By Poisson summation this holds ⟺ the 1-periodization Σ_m W_ν(x + m) is a trigonometric polynomial of degree ≤ 1.
2. **Carlson edge.**
   - G_ν(k) = ∫ 𝔐²[K₀(k y_c) cos(k c)] dν(c) has exponential type ½ in Im k, because |c| ≤ ½.
   - So z ↦ G_ν(2πz) has type exactly π. Carlson's theorem (type < π) just fails, which explains why ν* ≠ 0 exists.
   - Expected rigidity at the edge: G_ν(2πz) = sin(πz)·g(z) with g of type 0 and controlled growth. Polynomial-growth control would force a finite-dimensional, conjecturally one-dimensional, annihilator.
3. **Modular reading.**
   - The arc |z| = 1 is the fixed curve of z ↦ 1/z̄. A one-dimensional annihilator is expected to match the absence of Maass cusp forms with eigenvalue ¼ on SL₂(ℤ), with the Eisenstein series E*(z, ½) as the surviving object (Lewis–Zagier period functions; card n1-voronoi row 1015).
4. **Consequences to formalize.** If the annihilator is ℝ·ν*, then:
   - every arc-blind PD null test has positive pole;
   - the canonical null test is unique.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-10-14 — created in 0-backlog (row 1198)
- 2026-10-14 — [P] Legendre form of the arc modes. Write u = sin φ, so y = cos φ and φ ∈ [−π/6, π/6].
  - ∫₀^∞ K₀(ky)cos(ku) k^{w−1} dk = 2^{w−2}Γ(w/2)² y^{−w} ₂F₁(w/2, w/2; ½; −u²/y²).
  - By Pfaff this equals 2^{w−2}Γ(w/2)² · F_w(u), with F_w(u) = ₂F₁(w/2, (1−w)/2; ½; u²): the even solution of the Legendre equation ((1−u²)F′)′ + (w−1)w·F = 0 with F(0) = 1. The height drops out (y^{−w}cos^w φ = 1).
  - (An elementary closed form cos((w−½)φ)/cos(φ/2), first tried, is wrong: at w = ½ the function is elliptic.)
  - With 𝒟 = −(x∂_x)(x∂_x+1) ↔ −θ(θ+1) (θ = k∂_k), the Mellin transform of Ŵ_ν is c·(w(w−1))²·2^{w−2}Γ(w/2)²·A_ν(w), where A_ν(w) = ∫ √y F_w(u) dν(u) is a Legendre (conical, at w = ½+it) transform of ν. It is entire of exponential type ≤ π/6 in Im w.
  - This matches K_t(u) = √(y/2)·₂F₁(¼+it/2, ¼−it/2; ½; u²) from row 1198 (w = ½ + it).
- 2026-10-14 — the β > 1 motivation is resolved without odd null tests. MUST-1458 [L] `RHTower/WeilPoleWeightAtMostOne` proves β ≤ 1 for every Herglotz datum, by the pole-free density ceiling plus an Abelian argument. This card keeps only its structural question: is the arc null face one ray?
