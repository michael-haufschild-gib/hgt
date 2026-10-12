# (N1) as degree-2 Voronoi interpolation at the integers

- **ID:** n1-voronoi-maass-interpolation
- **Stage:** 1-in-progress
- **Type:** REFORMULATION (paper) + CONJECTURE
- **Source:** Opus RH goal loop rows 1003–1013 (`rh-goal-loop-opus-2026-09-29.md`); HF (N1) from route-candidates loop row 715 and `hf-positive-hodge-attack/krein-producer-loops.md`.
- **Statement (reformulation; corpus [L] up to the T₂ reading, see Corpus audit):** a strictly positive prime-blind radical multiplier exists ((N1)) iff there is a function `f` on `(0,∞)` such that
  1. `f` is self-dual under the degree-2 Voronoi transform `T₂`, i.e. `E_f(w) := 𝓜[f](w)/Γ_ℝ(w)²` satisfies `E_f(w) = E_f(1−w)`;
  2. `f(n) = 0` for every integer `n ≥ 2`;
  3. `E_f(½+it) > 0` for all real `t`, with `E_f` analytic on `0 ≤ Re w ≤ 1` and of growth `< e^{π|t|/2}` there (the class of row 715: `R` analytic on `|Im t| ≤ ½`, `Ξ²R` integrable).
- **Conjecture C1013 (REFUTED as stated, row 1019):** `T₂`-self-dual functions (in a Schwartz-type class) are determined by their values at the positive integers, up to a finite-dimensional exceptional space coming from the Eisenstein series at `s = ½`. Then (N1) reduces to the sign of the critical-line symbol on one explicit finite-dimensional affine family (the node-1 Lagrange function `f*` plus exceptional functions).

## Corpus audit (row 1017) — what was already owned
- **[L] owned:** prime-blindness ⟺ `Ψ_R = 𝓜^{−1}[G²R]` vanishes at every integer `n ≥ 2` (`ExactNullCertificateDivisorTransfer.logNode_blind_iff_certKernel_vanishes`, via `ζ² = Σd(m)m^{−s}` and the Dirichlet inverse `μ⋆μ`). Its docstring already records that `Ψ_R` is a fixed point of the Voronoi involution of `ζ²` for even `R`. The reformulation below (rows 1012–1013) rederives this through Hurwitz/Poisson and is **not new**. `f = Ψ_R` and `E_f = (s(s−1)/2)²R`.
- **[L] owned, the uniqueness half of C1013 in a growth class:** `ExactNullCertificateLogRoomGrowth`, a critical logarithmic Carlson theorem for `log ℕ`. Blindness at `log ℕ_{≥2}` together with `∫|G(½+it)|²|R|e^{(π/2)(|t|−|t|/log(|t|+3))}dt < ∞` gives `Ψ_R(1) = 0`. So positive (N1) witnesses need `R` to grow at least like `e^{(π/2)|t|/log|t|}` (times powers). `ExactNullCertificateOrderTransfer`: order 2 is exactly critical.
- **New here:** the `π(½)` / Kirillov / line-model reading (S = Voronoi involution, T = `e^{2πix}`, torus positivity = Mellin positivity); the no-relations lemma; the compact-spectrum no-go; the Farkas dual in `π(½)` language; the Lewis–Zagier/BLZ mechanism for existence.
- **Refocused open core:** existence of a self-dual `f` with `f(n) = 0` (`n ≥ 2`), `f(1) ≠ 0` and positive critical-line symbol, inside the room `e^{(π/2)|t|/log|t|} ≲ |E_f| < e^{(π/2)|t|}`. Below the room it is impossible (log-Carlson). Above it, row 715's class is violated.

## Why it matters
- Row 715: (N1) ⇒ every Weil-positive producer is `Λ`, so RH ⟺ PBAP. PBAP is numerically certified with margin ≈ 0.15 (not in Lean). So (N1) is RH-strength modulo PBAP numerics.
- Under C1013, RH ⟸ PBAP ∧ (sign of one explicit symbol on the critical line). That symbol is pinned at the integers, so it must carry ζ²-arithmetic. Its sign should therefore be RH-strength or false, never free.
- The new language is Fourier interpolation (Radchenko–Viazovska type), at integer nodes and for the `Γ_ℝ²` transform. This is a Maass-form (weight 0, `λ = ¼`) analogue rather than the holomorphic theta-form setting.

## Derivation of the reformulation (rows 1012–1013)
1. ζ-free form (corpus `logNode_blind_iff_certKernel_vanishes`, row 1004): with `ρ = R|G|²`, `G = ½s(s−1)Γ_ℝ(s)`, prime-blindness ⟺ `∫ρ(t)e^{i(2θ(t)−t log n)}dt = 0` for `n ≥ 2`. `|ζ|² = e^{2iθ}ζ²` on the line, and Dirichlet convolution with `d(m)m^{−½}` is triangular-invertible.
2. `2𝓜[cos 2πx](½+it) = e^{2iθ(t)}` (row 1005). With `ν(y) = ρ̂(log y)` and `h(y) = |y|^{−½}ν(|y|)`, Hurwitz's formula (`ζ(s,x)+ζ(s,1−x)` as a cosine series; Mathlib `completedHurwitzZetaEven_one_sub`) gives `Σ_k h(x+k) = Σ_n cos(2πnx)·n^{−½}·2∫ρ e^{i(2θ−t log n)}dt`. So prime-blind ⟺ `ĥ(n) = 0` for `|n| ≥ 2` ⟺ the periodization of `h` is `A + B cos 2πx`.
3. Mellin–cosine duality: `𝓜[h](w) = 𝓜[ĥ](1−w)Γ_ℝ(w)/Γ_ℝ(1−w)`. Even `ρ` (`ν(1/y) = ν(y)`) ⟺ `𝓜[h]` symmetric ⟺ `𝓜[ĥ]/Γ_ℝ²` symmetric, i.e. `f := ĥ|_{(0,∞)}` is `T₂`-self-dual. On the line, `ρ(t) ∝ 𝓜[h](½−it) = |Γ_ℝ(½+it)|²E_f(½+it)`.

## Proved here (paper)
- **Compact-spectrum no-go (any support).** No `h ≠ 0` with compactly supported `ĥ` satisfies S-invariance `h(x) = h(1/x)/x` on `(0,∞)`. Proof: `h` is entire (Paley–Wiener). By the identity theorem, `h(z) = h(1/z)/z` on the connected set `ℂ∖{0}`. Then `|h(w)| ≤ max_{|z|≤1}|h| / |w|` for `|w| ≥ 1`, so `h` is a bounded entire function, hence constant (Liouville), hence `0`. So (N1) witnesses must have non-compact Kirillov support, i.e. infinitely many integer constraints really bind. This supersedes the earlier Bessel-analyticity argument, which only covered `supp ⊂ [0,2)`.

- **No relations among integer values (half of C1013).** Read `T₂` as the Weyl element in the Kirillov model of the `s = ½` principal series `π` (trivial central character; the Bessel transform with multiplier `Γ_ℝ(w)²/Γ_ℝ(1−w)²`). The unipotent `T = n(1)` acts by `e^{2πix}`. Suppose a tempered functional `D = Σ_{n≥1} a_n(δ_n + δ_{−n})` annihilates every self-dual vector. Then `D∘π(S) = −D` and `D∘π(T) = D`, hence `D∘π(ST)³ = −D`. But `(ST)³ = −I` acts trivially, so `D = 0`. Parity is preserved because the central character is trivial. So integer values of self-dual vectors satisfy no linear relation, and the evaluation map has dense image. This is the abstract reason there is no S-odd automorphic distribution for `SL₂(ℤ)`.
- **Positivity identity.** Write `Λ₂(w) = (Γ_ℝ(w)ζ(w))²`, which is symmetric, with `Λ₂(½+it) = (Ξ(t)/(−(t²+¼)/2))² ≥ 0`. For self-dual `f` (symbol `E`), `Σ_n d(n)f(n) − Res_{w=1}[Λ₂E] = (1/2π)∫Λ₂(½+it)E(½+it)dt`. Under (N1) the right side is `> 0`, so `f(1) > Res_{w=1}[Λ₂E] = E'(1) + 2c₀E(1)` (`c₀` from the Laurent expansion of `Γ_ℝζ` at 1). This is a constraint, not a contradiction. Moving the contour symmetrically shows the Voronoi main terms of self-dual vectors cancel (`Res₁ + Res₀ = 0`).

- **Line-model form (row 1015).** In the line model of `π(½)` (`n(t)` = translation, `S: φ ↦ |x|^{−1}φ(−1/x)`, Poisson transform at `s = ½` = pairing with the Whittaker family `g_τ`), the witness is `h` itself:
  (N1) ⟺ ∃ even `h` on ℝ with `h(x) = |x|^{−1}h(1/x)` (S-invariant), `Σ_k h(x+k) = A + B cos 2πx`, and `v ↦ e^{v/2}h(e^v)` strictly positive definite.
  The kernel half of C1013 becomes: S-invariant `h` with constant T-periodization. Writing `h = (1−T)ψ` with `ψ = Σ_{k≥0}T^k h` turns this into the four-term equation `(1−S)(1−T)ψ = 0`, i.e. `ψ(x) = |x|^{−1}ψ(−1/x) + ψ(x−1) − |x|^{−1}ψ(−1/x−1)`. This is a period-function / `SL₂(ℤ)` 1-cohomology problem in the sense of Lewis–Zagier and Bruggeman–Lewis–Zagier.
  At `s = ½`, `SL₂(ℤ)` has no cusp forms and `E(τ,½) ≡ 0`, so the only automorphic input is `∂_sE(τ,s)|_{s=½}`, whose Fourier coefficients are `d(n)√y K₀(2πny)`, the ζ² object. Expected: the exceptional space has dimension `≤ 2`, generated by `∂_sE`-data.
  The spherical vector `(1+x²)^{−½}` is S-invariant, but its periodization diverges logarithmically, since line-model vectors decay like `|x|^{−1}`. So the class of `h` (row 715: `R` analytic on the closed strip gives `h(y) = o(1/y)`) sits exactly at this logarithmic edge.

- **Farkas dual in `π(½)` language (row 1016).** (N1) fails iff some nonzero 1-periodic even `F = Σ_{n≥2}c_n cos 2πnx` (T-invariant, no modes `0, ±1`) has `(1+S)F` torus-nonnegative, i.e. `Re(e^{2iθ(t)}C(½+it)) ≥ 0` with `C(s) = Σ c_n n^{−s}`; this is row 1007's `D_c`. Duality check: `⟨h,F⟩ = ∫_0^1(Σ_k h(x+k))F = 0` and `⟨h,F⟩ = ⟨h,SF⟩`, so `⟨h,(1+S)F⟩ = 0`, which is a positive spectral measure against a nonnegative one.
  The ζ²-built candidates `C = ζ² − Pζ` with `p₁ = 1` give `Re = Z² − Z·Re(e^{iθ}P)`. This is negative near the simple zeros of `Z` unless `Re(e^{iθ}P)` tracks `Z`, which forces `C = 0`. So the known near-certificate (row 1007) does not close.

## Row 1019: C1013 refuted as stated
- **Torsion obstruction (corpus [L]: MUST-930 add. 2 odd case, `oddInversion_packet_identity`; row 1021).** An integer-node interpolation formula `f = Σf(n)b_n` for self-dual `f` needs `B(τ,x)` 1-periodic with `B + B∘S = Q_x`. On a free `PSL₂(ℤ)`-orbit, `U = ST` with `U³ = 1` forces `b(g) = ½[q(g)+q(Ug)−q(U²g)]` together with a four-point equation on `Q`, which generic `Q_x` violates. Radchenko–Viazovska use the theta group, which has no order-3 torsion. `T₂W_τ = W_{−1/τ}` holds exactly, since `W₀` is K-fixed.
- **Recount.** Bandwidth `2√X` in `u = √x` gives `≈ 2X` degrees of freedom against `X` nodes, so the integers are subcritical by a factor 2 (critical lattice `½ℤ`). Expected: infinite-dimensional kernel in the growth room, trivial kernel below it (log-Carlson).
- **Consequence.** (N1) is positivity on an infinite-dimensional affine space, not one sign.
- **Construction lead (open).** At the κ-saddle `Im x = −π/2`, `sin(πeˣ)sin(πe^{−x}) = sinh(t/2)sinh(2π²/t) > 0`, but it oscillates on scale `2/t ≪ 1/√t`, so saddle factorization fails.

## Row 1022: certificates are `Z²·Re Q`
- Every chirp combination over `n ≥ 2` is `Z(t)²·Re Q(½+it)` with `Q = C/ζ²` a Dirichlet series with `q₁ = 0`.
- Near-certificate `Q = −ζ'/ζ`: `D = θ'(t)Z(t)² ≥ 0` for `|t| ≥ 6.29`, negative only on `|t| < 6.29`.
- Pairing identity for prime-blind even `R`: `∫θ'Ξ²R dt = −(π/2)R(i/2)`.
- Repairing the compact defect is a Weil-positivity question on the window `(−log 2, log 2)`, the same window as PBAP.

## Evidence for C1013 (superseded by row 1019)
- **Phase-space count.** In `u = √x` the kernel is `≈ cos(4πuv)`. A self-dual `f` on `u ≤ U` has `≈ U²` degrees of freedom, and the nodes `n ≤ U²` give `U²` constraints. This is critical density, as in Radchenko–Viazovska and as in L394 ("critical for k = 2").
- **Modular mechanism.** `g_τ(x) = √y K₀(2π|x|y)e^{2πixu}` (`τ = u+iy`) is the `s = ½` Whittaker mode, a `Δ`-eigenfunction with eigenvalue `¼` for every real `x`. The Voronoi formula for `d(n)` is the modularity of `E(τ,½)`, which suggests `T₂g_τ = g_{−1/τ}`. At integer `x = n`, `g_τ(n)` is 1-periodic in `τ`. Interpolation at the integers thus becomes the `SL₂(ℤ)` cocycle problem `F(τ,x) + F(−1/τ,x) = g_τ(x)` with `F(·,x)` 1-periodic and expanded in `s = ½` Maass modes. This is the Lewis–Zagier period-function setting at `λ = ¼`. `SL₂(ℤ)` has no cusp forms at `λ = ¼` (`λ₁ ≈ 91.14`), so the obstruction and exceptional spaces come only from `E(τ,½)` and `∂_sE(τ,½)`, which are finite-dimensional.

## Open points / Phase 4 attack list
- Verify `T₂g_τ = g_{−1/τ}` (Weber-type integral of `K₀ × 𝓙`).
- Function class: Schwartz-type versus the class in (3). Uniqueness can fail in weak classes.
- The exceptional space: compute the self-dual functions vanishing at all positive integers (from `E(τ,½)`, `∂_sE`) and their symbols. If a symbol involves `ζ(w)²` or `1/ζ(w)²`, record exactly how the zeros of ζ enter the sign question.
- Novelty: external literature unaudited (corpus-only directive). Candidates to compare when allowed: Radchenko–Viazovska, Bondarenko–Radchenko–Seip (interpolation with nodes `log n`), Lewis–Zagier.

## Gates
- [x] 0 → 1  in-progress: reformulation derived, one no-go proved on paper.
- [ ] 1 → 2  fully-proven: complete proof of the reformulation (function classes, Fubini/regularization at `Re s = ½`).
- [ ] 2 → 3  formalized.

## Log
- 2026-10-12 — created from loop rows 1012–1013.
- 2026-10-12 — row 1021: torsion step = MUST-930 add. 2 (rediscovered). Link: (N1) interpolation and twin-door infinite deficits are the same s = ½ SL₂(ℤ) cocycle image problem (the packet identity).
- 2026-10-12 — row 1019: C1013 refuted as stated (torsion obstruction; integers subcritical ×2); (N1) = positivity on an infinite-dimensional affine space.
- 2026-10-12 — row 1017: corpus audit. The reformulation and log-Carlson uniqueness are owned ([L] ExactNullCertificate*); refocused on existence in the growth room.
- 2026-10-12 — row 1015: line-model form; kernel half = (1−S)(1−T)ψ = 0 period-function problem; ζ² enters only through ∂_sE(τ,½).
- 2026-10-12 — row 1014: no-relations lemma ((ST)³ = −I) and the positivity identity added. Uniqueness, i.e. the kernel of the evaluation map, remains the open half.
- 2026-10-12 — row 1027: certificate legitimacy. Genuine Farkas certificates need `Q` analytic at `s = 1`, since a residue `κR(1)` is not sign-controlled. The Laguerre candidate `(ζ'/ζ)'` has `κ ≠ 0`. Its unique analytic repair `(ζ'/ζ)' − (ζ'/ζ)² + 2γζ'/ζ` is negative at the peaks of `Z` (one-cosine model). No low-order certificate exists; consistent with (N1).
- 2026-10-12 — row 1030: Plemelj atoms. Poles of `C = Qζ²` on the line add atoms `π Re(e^{2iθ}r_γ)δ_γ` to the dual distribution. The large-`t`-positive candidate `Q₁ = −LL' + ½L'' + γ₀L'` (analytic at 1, smooth part `(θ'+γ₀)(Z'² − ZZ'') ≥ 0` under RH) has atoms `−2πZ'(γ)²`. Blind weights satisfy `∫ρZ²Re Q₁ = 2πΣρ(γ)Z'(γ)²`. The zero atoms are the zero-faithfulness obstruction.
