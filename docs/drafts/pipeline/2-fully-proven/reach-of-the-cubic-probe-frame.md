# Reach of the cubic probe frame: Grossencharacter coupling and the three-fifths tower boundary

- **ID:** reach-of-the-cubic-probe-frame
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1111/obstacles-summary.md` §3 (Question B184)
- **Statement:** No form of the cubic-theta probe over `K = ℚ(ω)` produces a correction whose Euler product converges on `Re s > 1/2` to read the zeros of `L(s, η)` alone: every form is a coupled Grossencharacter system. For the canonical cubic-sextic probe, `H_η^S(s) = L^S(6s - 3, ψ₆ η⁶) · E_η^S(s)` where `E_η^S` is holomorphic, bounded on `Re s ≥ 2`, and everywhere nonvanishing on `Re s > 1/2` for every finite prime set `S`, while `L(w, ψ₆^k χ)` (`k ≥ 1`) extends to an entire completed `L`-function of order `1`, is zero-free on the closed half-plane `Re w ≥ 1`, and has infinitely many zeros with unbounded ordinates in `1/2 ≤ Re w < 1`. Consequently, the uncoupled frame reaches the closed boundary `Re s ≥ 2/3` with fixed cutoff `N₀ = 160` and fails unconditionally below `2/3`; inverting `L^S(6s - 3, ψ₆ η⁶)` incurs an unconditional `Z^{2/3}` squarefree Möbius norm floor; and coupling across the infinite-order Grossencharacter tower `{ψ₆^{k_r} η^{6^r}}` (`k_0 = 0`, `k_{r+1} = 6 k_r + 1`) reaches `max(σ₀, 3/5)` unconditionally (`max(σ₀, 7/12)` under tower GRH) and cannot pass `3/5` across all contour shears, `6r`-periodic Gauss pairings, and multi-theta cubings.

## Exact mathematical laws

Let `K = ℚ(ω)` (`ω² + ω + 1 = 0`), `O = ℤ[ω]`, `λ = 1 - ω`, and let `𝔪` be any ray class modulus of `K` and `η` any ray class character modulo `𝔪`. Since `O` is a principal ideal domain with unit group `Oˣ = ⟨-ω⟩` of order `6`, the archimedean sixth-power phase
`ψ₆((a)) = (ā / |a|)^6` (`a ≠ 0`, `ψ₆(0) = 0`)
is invariant under `Oˣ`, strictly multiplicative on all ideals of `O`, and of infinite order on prime ideals. For any integer `k ≥ 1` and ray class character `ψ` modulo `𝔪` with finite conductor `𝔣 = (f₀)` and primitive reduction `χ_prim : (O / 𝔣)ˣ → ℂˣ`, define the primitive Grossencharacter prime coefficient
`ψ_{6k, ψ}(𝔭) = ψ₆(𝔭)^k · χ_prim(𝔭 mod 𝔣)` for `𝔭 ∤ 𝔣` and `0` for `𝔭 ∣ 𝔣`.

1. **Exact Grossencharacter factorization and cutoff-free residual nonvanishing.** At every prime `v` of `O` with `λ ∉ v`, the local phase `κ_η(v) = (π̄_v / √N(v)) · η(v)` (`π_v ≡ 1 (mod 3)`) satisfies
   `κ_η(v)^6 = ψ₆(v) · η^6(v)`.
   Writing `Q = N(v)` and `A = κ_η(v)^6`, the principal local factor splits identically as
   `F(Q, A, η(v), s) = (1 - A Q^{3 - 6s})⁻¹ · E_loc(Q, A, η(v), s)`,
   where
   `E_loc(Q, A, η, s) = (1 - Q^{-2}) · (1 - (A Q^{2 - 6s} + η (1 - Q⁻¹) Q^{-s})) / (1 - η Q^{-s})`.
   For every `Q ≥ 2`, `|A| ≤ 1`, `|η| ≤ 1`, and `Re s ≥ 1/2`,
   `|A Q^{2 - 6s} + η (1 - Q⁻¹) Q^{-s}| ≤ Q⁻¹ + (1 - Q⁻¹) Q^{-1/2} < Q⁻¹ + (1 - Q⁻¹) = 1`,
   so `E_loc(Q, A, η, s) ≠ 0` at every prime without norm cutoff. Its local defect `(E_loc - 1)` is `O(Q^{-min(6σ - 2, 1 + σ, 2)})` uniformly on `Re s ≥ σ > 1/2`. Therefore, for **every** finite set `S` of primes of `O` containing `{v | λ ∈ v}`, the residual Euler product `E_η^S(s) = ∏_{v ∉ S} E_loc(N(v), κ_η(v)^6, η(v), s)` converges absolutely to a holomorphic, everywhere nonvanishing function on `{s : ℂ | 1/2 < Re s}` that is bounded on `Re s ≥ 2`, and on `Re s > 2/3` (`Re s ≥ 7/8` on the `N₀ = 160` deleted product)
   `H_η^S(s) = L_{𝔪}^S(6s - 3, ψ₆ η⁶) · E_η^S(s)`.
   The identical factorization holds for any tower input `ψ₆^k η` (`k ≥ 0`), mapping angular weight `k` to `6k + 1` and character `η` to `η^6`.

2. **Global harmonic-theta continuation and functional equation of `L(w, ψ₆^k ψ)`.** On `ℝ² ≅ ℂ`, let `z̄(x) = x_0 - i x_1`. For `s > 0` and `t ∈ (-1, 1)`, Fubini's theorem and the 1D Gaussian Fourier transform yield
   `∫_{ℝ²} e^{t z̄(x)} e^{-π s ‖x‖² - 2π i ⟨x, ξ⟩} dx = s⁻¹ e^{-(π/s) ‖ξ‖²} e^{t (-i z̄(ξ) / s)}`
   because the quadratic exponent `t² + (-i t)² = 0` vanishes identically. Differentiating `m` times at `t = 0` gives exact harmonic self-duality:
   `𝓕(z̄^m · e^{-π s ‖·‖²})(ξ) = s⁻¹ (-i / s)^m z̄(ξ)^m e^{-(π/s) ‖ξ‖²}`.
   For `k ≥ 1`, summing `m = 6k` over the cosets of `𝔣 = (f₀)` against the primitive additive trace character `a ↦ e^{2π i Tr_{K/ℚ}(a / (λ f₀))}` and the primitive multiplicative character `χ_prim` (trivial on `Oˣ` because `K` is totally complex, so `𝔪.inf` is empty) gives, at scale `α_𝔣 = 2π / √(3 N(𝔣))`, the harmonic theta transformation
   `Θ_{ψ, k}(1/t) = ε(ψ, k) · t^{6k + 1} · conj(Θ_{ψ, k}(t))` (`t > 0`),
   with zero constant terms at both `0` and `∞` (`0^{6k} = 0`) and root number `|ε(ψ, k)| = 1` (`ε(ψ, k) = (-1)^k (f₀ / |f₀|)^{6k} τ(χ_prim) / √N(𝔣)`). Mellin inversion produces an entire completed function
   `Λ(w, ψ₆^k ψ) = (1/6) ∫_0^∞ Θ_{ψ, k}(t) t^{w + 3k - 1} dt = α_𝔣^{-(w + 3k)} Γ(w + 3k) L(w, ψ₆^k ψ)`
   of order at most `1` satisfying `Λ(1 - w, ψ₆^k ψ) = ε(ψ, k) · conj(Λ(conj w, ψ₆^k ψ))`. Dividing by `α_𝔣^{-(w + 3k)} Γ(w + 3k)` continues `L(w, ψ₆^k ψ)` holomorphically to `{w : ℂ | -3k < Re w}` (`Re w > -3` for all `k ≥ 1`), with Euler product `∏_{𝔭 ∤ 𝔣} (1 - ψ_{6k, ψ}(𝔭) N(𝔭)^{-w})⁻¹` on `Re w > 1`.

3. **Closed half-plane `Re w ≥ 1` nonvanishing and right-half-strip zeros.** Because `k ≥ 1` implies `2k ≥ 2 ≥ 1`, both `L(w, ψ₆^k ψ)` and `L(w, ψ₆^{2k} ψ²)` are holomorphic at `w = 1` (neither has a pole). Applying `3 + 4 cos θ + cos 2θ ≥ 0` on `1 < σ ≤ 2` against `ζ_{K, 𝔣}(σ)³ L(σ + i t, ψ₆^k ψ)⁴ L(σ + 2i t, ψ₆^{2k} ψ²)` eliminates zeros on the entire closed half-plane `Re w ≥ 1` (including `w = 1`). Conversely, `Λ(w, ψ₆^k ψ)` has order at most `1`, no zeros outside `0 < Re w < 1`, and superlinear logarithmic ray growth `Γ(n + 3k) / n! ≥ 1` along positive integers; by Hadamard/Phragmén–Lindelöf subquadratic rigidity (`zeroSet_infinite_of_subquadratic_superlinear_ray`), `Λ(w, ψ₆^k ψ)` has infinitely many zeros in `0 < Re w < 1`, and reflecting any zero with `Re w < 1/2` via `w ↦ 1 - conj w` gives infinitely many zeros with unbounded ordinates `|Im w| > T` in `1/2 ≤ Re w < 1`.

4. **Sharp uncoupled reach `2/3`, failure below `2/3`, zero-transfer law, and `Z^{2/3}` Möbius barrier.**
   - *Sharp `2/3` uncoupled endpoint:* For `S` containing `{v | λ ∈ v ∨ N(v) ≤ 160}`, `H_{η, cont}^S(s) := L_{𝔪}^S(6s - 3, ψ₆ η⁶) · E_η^S(s)` continues `probeCorrection 𝔪 η S` holomorphically to `Re s > 1/2`, is bounded on `Re s ≥ 2`, and is **zero-free on the closed half-plane `Re s ≥ 2/3`** (`Re(6s - 3) ≥ 1`). Thus the uncoupled two-estimate implication holds all the way down to `2/3 ≤ σ₀ < 1` with fixed cutoff `N₀ = 160`.
   - *Unconditional failure below `2/3`:* On `Re s > 1/2`, `H_{η, cont}^S(s) = 0 ⟺ L(6s - 3, ψ₆ η⁶) = 0`. Hence `H_{η, cont}^S` has infinitely many zeros with unbounded ordinates in `7/12 ≤ Re s < 2/3`, so no holomorphic continuation of `probeCorrection 𝔪 η S` can be nonvanishing on `Re s > σ₀` for any `σ₀ < 7/12` (or below `(3 + Θ_{ψ₆ η⁶})/6`).
   - *Zero-transfer below `2/3`:* If the signal of `e^{(s-c)²} H_{η, cont}^S(s) / L(s, η)` has direct and comparison bounds below `Re ρ` (`1/2 < Re ρ < 2/3`, `ρ ≠ 1`), holomorphy of `e^{(s-c)²} H_{η, cont}^S(s) / L(s, η)` at `ρ` forces `L(s, η) = 0 ⟹ L(6ρ - 3, ψ₆ η⁶) = 0`. Under sextic Grossencharacter GRH (`Re w = 1/2`), this yields zero-freeness on `Re s > max(σ₀, 7/12)`.
   - *`Z^{2/3}` Möbius inversion barrier:* Clearing `L^S(6s - 3, ψ₆ η⁶)` in the family multiplies the signal by `(Z / N(J)^6)^a` summed over squarefree ideals `J` of `O` weighted by `μ(J) ψ₆(J) η^6(J) N(J)^3`. For every `a < 2/3`, the absolute coefficient sum up to `N(J)^6 ≤ Z` satisfies `Z^a ∑_{J squarefree, N(J) ≤ Z^{1/6}} N(J)^{3 - 6a} ≥ c · Z^{2/3}` (`c > 0`), since every rational prime `p ≡ 1 (mod 3)` splits into two distinct degree-1 primes of `O` of norm `p`.

5. **Coupled Grossencharacter tower endpoint `3/5` and universal probe classification.**
   - *Tower iteration:* Define `k_0 = 0`, `k_{r+1} = 6 k_r + 1 = (6^{r+1} - 1)/5`. At level `r`, the cubic probe with local input `ψ₆^{k_r} η^{6^r}` has continued correction `L_{𝔪}^S(6s - 3, ψ₆^{k_{r+1}} η^{6^{r+1}}) · E_{r, η}^S(s)` with `E_{r, η}^S` holomorphic and nonvanishing on `Re s > 1/2`. If the coupled tower has reciprocal-signal estimates down to `σ₀ ∈ [1/2, 1)`, zero-transfer gives `Θ_r ≤ max(σ₀, (3 + Θ_{r+1})/6)` with unconditional seed `Θ_R ≤ 1`. Iterating `R` steps contracts `(3 + ·)/6` to its unique fixed point `3/5` (`1/6^R → 0`), yielding `HeckeHalfPlane K (max(σ₀, 3/5))` and `zetaZeroAbscissa ≤ max(σ₀, 3/5)` unconditionally (`max(σ₀, 7/12)` under tower GRH), and `b = (3 + b)/6 ⟺ b = 3/5` forbids passing `3/5` without zero-free input inside `Re w < 1` at arbitrarily high tower levels.
   - *Universal classification of probe variants:*
     1. **3-variable contour shear:** Shifting `(x, z) ↦ (x - δ, z + δ)` preserves `x + z`: the sextic denominator exponent `κ_η(v)^6 N(v)^{-(6(x + z - 1) + 2)}` depends solely on `t = x + z - 1`, and its prime norm series `∑_v |κ_η(v)^6 N(v)^{-(6t + 2)}|` diverges for every `Re t ≤ -1/6` (`Re x ≤ 2/3` at `z = 1/6`).
     2. **General `6r`-periodic Gauss pairing:** Pairing cubic `γ₂` with `φ` of order `3` (`γ₂ φ = χ_3` of order `3`, not quadratic) yields Jacobi sign `+1` instead of Möbius `-1`. Any `6r`-periodic Jacobi-sign pairing (`r ≥ 1`, minimal cube layer `l = 2r`) has leading resonance `R_{6r} = κ^{6r} Q^{(4r - 1) - 6r s}`, whose Euler-product convergence boundary is `(4r) / (6r) = 2/3` for every `r ≥ 1`, and whose coupled tower map `Θ ↦ ((4r - 1) + Θ) / (6r)` has fixed point `(4r - 1) / (6r - 1) ≥ 3/5` (strictly worse than `3/5` for all `r ≥ 2`).
     3. **Multi-theta cubing (`l = 1`):** Cubing three cubic theta functions puts the cube at `v_P = 1` with `R_mult = Q^{3/2 - 3s}`, whose Euler product diverges at `Re s = 5/6 > 2/3` and whose coupled map `(3/2 + Θ)/3` has fixed point `3/4 > 3/5`.

## Gates
- [x] 0 → 1  in-progress: well-posed dichotomy from `obstacles-summary.md` §3
- [x] 1 → 2  fully-proven: complete dependency-closed paper proof `[PROVED HERE]`
- [ ] 2 → 3  formalized: Lean 4 modules in `GaloisForLFunctions.FamilyContinuationTheory`, direct `lake --old env lean` checks and `#print axioms` audit clean

## No-go closure
- **Failed claim:** Existence of a cubic-theta probe over `ℚ(ω)` whose principal row carries `1 / L(s, η)` with a correction Euler product converging (or continuing nonvanishingly) on all of `Re s > 1/2` without Grossencharacter coupling, or a coupled cubic tower passing `Re s = 3/5` without external critical-strip zero-free input.
- **Exact killing theorem/mechanism:** The sextic residue reciprocity phase `(π̄_v / √N(v))^6 = ψ₆(v)` is an infinite-order Hecke Grossencharacter; factoring out `(1 - ψ₆(v) η^6(v) N(v)^{3 - 6s})⁻¹` leaves a nonvanishing residual Euler product on `Re s > 1/2`, so the continued correction vanishes on `Re s > 1/2` at and only at the zeros of `L(6s - 3, ψ₆ η⁶)`, which are infinite in `1/2 ≤ Re w < 1` (`7/12 ≤ Re s < 2/3`). Across the tower, the map `Θ ↦ (3 + Θ)/6` fixes `3/5`.
- **Strongest positive survivor:** Exact cutoff-free Grossencharacter factorization `H_η^S(s) = L^S(6s - 3, ψ₆ η⁶) E_η^S(s)` on `Re s > 1/2`; global harmonic-theta functional equation, order-`1` continuation, and closed `Re w ≥ 1` nonvanishing for all infinite-order Eisenstein Grossencharacters `ψ₆^k ψ` (`k ≥ 1`); sharp uncoupled continuation to `Re s ≥ 2/3` with fixed cutoff `N₀ = 160`; exact zero-transfer law below `2/3`; unconditional `max(σ₀, 3/5)` coupled Grossencharacter tower continuation theorem; and complete classification across contour shears, `6r`-periodic Gauss pairings, and multi-theta cubings.
- **New insight:** Moves the `2/3` barrier from a local defect-estimate limitation (with diverging cutoff `N₀ → ∞`) to an exact global Grossencharacter zero locus: `2/3` is reached unconditionally with fixed cutoff `N₀ = 160`, the region `(3/5, 2/3]` is crossed cleanly by coupling the infinite-order Grossencharacter tower `{ψ₆^{k_r} η^{6^r}}`, and `3/5` is the exact invariant structural ceiling of every cubic metaplectic producer frame.
- **Status:** Dependency-closed paper proof complete; proceeding immediately to Lean 4 formalization in `GaloisForLFunctions.FamilyContinuationTheory`.
