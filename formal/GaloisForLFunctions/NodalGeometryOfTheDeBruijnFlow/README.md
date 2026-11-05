# Nodal Geometry of the de Bruijn Flow (NGF)

Namespace `GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow`; umbrella
`NodalGeometryOfTheDeBruijnFlow.lean`. Status labels: **[L]** proved in this corpus, **[T]** target of
the programme, **[D]** derived on paper, not a theorem here.

## 1. Motivation

Let `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` (`RHTower.DeBruijn.riemannHeat`). It solves `∂_t H = −∂_z² H`, so
`u(x, t) = H_t(x)` is a caloric function and *decreasing* `t` is forward parabolic time. RH says that
the nodal curves `{u = 0}` in the half-plane `t > 0` have no turning points. Every present bound on
the half-Gaussian source of route ZCG is a size bound, and size stops at the saddle `½/log X`:
lowering the coefficient by size needs Lindelöf-strength input, and below a fixed coefficient it forces
a zero-free strip. NGF supplies the first tools below the saddle that do not rest on size. They read
the flow as a parabolic object: monotone quantities, zero numbers, blow-up profiles and zero dynamics.

NGF is a programme, not a new field. It does not exclude a collision by itself. Its identities hold for
every caloric function, including `H_{−τ}`, which does collide. Arithmetic can enter only through data.

## 2. Objects

| Object | Meaning |
|---|---|
| Nodal set | `{(x, t) : t > 0, H_t(x) = 0}`; below the horizon it is a forest opening upward in `t` |
| Collision | a real multiple zero of `H_{t₀}`; local model `x² − 2(t − t₀)` at order two |
| Caloric transform | `∫ g(x) e^{tx²} e^{izx} dx` for `g` of super-Gaussian decay; `g = Φ` gives `H_t` at every real `t` |
| Fock energy | `F(σ) = Σ_n (2σ)^n/n! ‖∂ⁿu(z₀, t₀)‖²` |
| Gaussian line energy | `∫ ‖u(x + iy₀, t₀ + σ)‖² G_σ(x − x₀) dx`, `G_σ` of variance `2σ` |
| Frequency | `N(σ) = σ F′(σ)/(2F(σ))`, half the mean Taylor degree of the Fock measure |
| Zero number | real zeros with multiplicity in a buffered window |
| Gap, compression | `g` for adjacent real zeros; `S = 4 Σ_k 1/((x₂ − z_k)(x₁ − z_k))` |
| Mesh | the least gap of a real configuration or window |
| Depth energies | `E_p = Σ_k w(Re z_k − X) (Im z_k)^{2p}`, the localized moments of the depth |
| Nonreal time | `ℓ_X`, the measure of heats at which `H_s` has a nonreal zero within `1` of `X` |

## 3. Language

- **Buffered window**: a window whose boundary curves carry no zero of `H_t` for the times considered.
- **Normalized time** `τ = t log²X`: gap fluctuations relax at `τ ≍ 1`; the open region runs to `τ ≍ log X`.
- **Parabolic order** at a point: the Taylor order in `x` of `H_{t₀}`; the frequency reads it as `σ → 0⁺`.
- **Compression**: `g²S`, the force of the neighbours on a gap; the lattice has `g²S = 8`, so its gaps are stationary.
- **Saddle, horizon**: `½/log X`, where the Gaussian mass of `H_t` leaves the strip; `(6600/9991 + ε)/log X`,
  above which `H_t` is proved real and simple near `X`.
- **Blind law**: an identity or monotonicity that also holds for `H_{−τ}`.

## 4. Mechanisms

1. **The Gaussian energy is a Fock norm.** Fubini and the Gaussian transform give
   `∫ ‖u(x + iy₀, t₀ + σ)‖² G_σ(x − x₀) dx = Σ_n (2σ)^n/n! ‖∂ⁿu(z₀, t₀)‖²`, at every complex `z₀`. This is
   the chaos expansion of the variance, with the Hermite functions of `G_σ` as chaos. **[T]**
2. **Frequency is a chaos level.** So `N(σ)` is half the mean degree of an exponential family: its
   monotonicity is one line, its limit at `σ → 0⁺` is half the order of `u` at `z₀`, and the Almgren–Poon
   theorem has no PDE content beyond this reading. A collision forces `N(σ) ≥ 1` at every scale. **[T]**
3. **Zero number.** As `t` decreases the real zero count in a buffered window falls only at collisions,
   by exactly `2⌊k/2⌋` at a zero of order `k`. The unbuffered law is false. **[T]**
4. **Blow-up.** At a zero of order `k`, `H_{t₀ ± q²}(x₀ + qσ)/q^k` tends to the heat polynomial of
   degree `k`: `k` real roots above `t₀`, `k mod 2` below. At order two `g² ∼ 8(t − t₀)`. **[T]**
5. **Zero dynamics.** `ẋ = H″/H′`, and for an adjacent pair `d(g²)/dt = 8 − g²S`, where `S` converges
   absolutely and is `≥ 0` once the window is real. So gaps cannot open faster than `8` per unit time. **[T]**
6. **Gap comparison.** At the mesh pair the neighbours are at least lattice-spaced, so the compression
   is below that of a finite lattice: `d(mesh²)/dt ≥ 16/n` in degree `n`, exact at `n = 2, 3`. **[T]**
7. **Depth moments.** The zeros attract vertically, so `E_p` is dissipated: a conjugate pair loses
   `4p·b^{2p−2}`, and cutoffs cost only `O(log X)·E_p`, with no inverse gap. The pair `(E₁, E₂)` then bounds the
   time spent nonreal by `√E₂`, which is much smaller than `E₁` near the line. **[T]**

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Real zeros persist; backward local count; collision jump law; finitely many collisions after `t` | `exists_ball_real_zeros_forward`, `exists_ball_nonreal_count_backward`, `exists_left_nonrealZeroCount`, `finite_collisionTimes` | [L] (RHTower) |
| RH ⇔ no positive-time collision ⇔ `Λ_X = 0` for all `X` | `riemannHypothesis_iff_forall_collisionMass_eq_zero`, `riemannHypothesis_iff_forall_localNewmanConstant_eq_zero` | [L] (RHTower) |
| Actual collision criterion; horizon `6600/9991`; order-two pair model | `riemannHeat_ofReal_collision_iff_halfGauss`, `riemannHeat_zeros_real_simple_subWeyl`, `pairModelHeat_orderTwo_collision` | [L] (ZCG) |
| Averaged repulsion; mesh never shrinks (polynomials) | `spread_roots_heatFlow`, `meshGe_heatStep` | [L] (ZCG) |
| Localized `E₁` dissipation through collisions | `exists_uniform_heatLocalizedVerticalEnergy_evolution` | [L] (RHTower) |
| Fock identity; frequency monotonicity; order bound | — | [T] |
| Sturm drop law in buffered windows; nodal forest | — | [T] |
| Hermite blow-up at actual collisions | — | [T] |
| Local zero ODE and gap law for `H_t` | — | [T] |
| Mesh growth `16/n`; Hermite mesh pinch `16/k ≤ μ²/t ≤ 24/(k+1)` | — | [T] |
| Depth law for polynomials: depth `< √(8nt)` from real-rooted data | — | [T] |
| Localized `E₂` dissipation; nonreal time `ℓ_X = o(1/log X)` on density-one windows | — | [T] |

## 6. Questions the programme aims to answer

1. **Central question.** Is there `c > 0` with `g_t² ≥ c·min(t, log⁻²X)` for every adjacent pair near height `X`
   and every `t > 0`? It implies no positive-time collision, hence RH. It also bounds the multiplicity
   of the zeros of `ζ`, so it is stronger than RH; see §8.
2. **Depth law.** Lean has `Λ_X ≥ c d²/log X`, and the model gives `d/log X` when `d log X ≫ 1`. What decides between
   them? The cluster model says local count does: the expected law is `Λ_X ≳ min(d²/(1 + m), d/log X)`, with
   `m` the number of zeros within `O(d)`.
3. **Compression.** How large can `g²S` be on a cluster? At the mesh pair it is below `8`.
4. **B73.** Does `Λ_X log X → 0` on density-one heights? Depth moments reduce this to mean values of `δ_ρ⁴`
   given by Selberg's near-line density, plus lateral control of nonreal zeros.
5. **Orders.** How large can a collision be, in terms of the horizon? The frequency gives about `0.33 log X` [D].

## 7. Tools to develop

Parabolic frequency and doubling index; Sturm drop law with moving buffers; blow-up classification;
local Dyson ODE with an `O(log X)` exterior force; gap comparison principle; depth-moment hierarchy;
Grace–Walsh–Szegő depth bound; relaxation at normalized time.

## 8. Traps

- **Blindness.** Every monotone identity here holds for `H_{−τ}`, which collides at positive time. A proof
  of a sign must use data: the proved region above the horizon, RvM counts, the Euler product in `Q`.
- **Degeneration at `t = 0`.** Collisions occur below `t = 0` (`newmanConstant_nonneg`, under RH `Λ = 0`), so any
  repulsion inequality must degenerate exactly at `t = 0`.
- **The central inequality is too strong as stated.** An `m`-fold zero of `H_{t₀}` gives Hermite gaps with
  `g² ≤ 24(t − t₀)/(m + 1)`, so `c` bounds multiplicities. Under GUE statistics clusters of growing size are
  expected, and the uniform constant is then expected to fail [D]; the density-one form is unaffected.
- **Dimension count.** Collisions are generic in the `(X, t)` plane, so Diophantine repulsion alone
  cannot exclude them [D].
- **Unbuffered windows.** Zeros cross fixed lines at speed `≈ π/2`, and nonreal counts in fixed windows can rise.
- **Frequency is three circles.** `F` is also a Bargmann–Fock area norm of `u(·, t₀)`, so the frequency adds no
  information about `H_{t₀}` beyond its Taylor data; its value is that it can be read on the real line at the
  later time `t₀ + σ`, without any information in the strip.
- **Lateral entry.** Vertical dissipation controls depth, not the horizontal path of a nonreal zero.

## 9. Open research topics

The local repulsion law on density-one heights; control of the compression on clusters away from the
mesh pair; lateral control of nonreal zeros (the gap between nonreal time and `Λ_X`); a depth law at
height-uniform count; relaxation at normalized time for the actual source.

## 10. Position in the corpus

NGF is the parabolic side of ZCG. ZCG's camera fixes the configuration at `t = 0`; ZCG's horizon fixes it at
`t ≍ 1/log X`; NGF studies the region between them. RHTower supplies the source estimates and collision
law, HTGeometry the polynomial heat calculus, FFP the finite-free view of the same flow, and
SquareRootThreshold and the Selberg near-line density the off-line moments. By ZCG's rule, no Weil positivity
or spectral sign enters here.

## 11. Success criteria and contributions

The programme succeeds when the tools of §7 exist for the actual source, the questions of §6 are answered
or reduced to one precise open input, and the reach and failure of each law are shown on the fakes.

A contribution must be unconditional in Lean; state its law for a class containing both `H_t` and a fake
when the law is blind; and say which datum of `ζ` it uses when it is not. A new identity counts only if it
yields a bound the previous tools could not state.
