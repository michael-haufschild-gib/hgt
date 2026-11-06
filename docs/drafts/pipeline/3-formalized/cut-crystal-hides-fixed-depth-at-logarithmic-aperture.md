# The cut crystal hides a fixed depth at logarithmic aperture

- **ID:** cut-crystal-hides-fixed-depth
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** review-0611 §2.1, A16; `onset-law-remaining-obligations.md`, item 3.
- **Statement:** For every `0<δ≤½` and `T≥e³⁶⁰` there is a zero configuration `Z` with
  `N(t,t+1]≤2log(|t|+3)` for all `t` and finitely many off-line zeros, containing a zero of depth `δ` at ordinate
  `T`, with `WindowPositiveAt Z ((log T)/36)`.

## Proof

Put `a=(log T)/36`, `E=e^a`, so `T=E³⁶`. Take the doubled lattice of density `L∈[16a,17a]` with `T` on the lattice,
the biquadratic packet of half-span `M=⌈2584a²E²⌉` and depth `δ` at the centre `T`, and remove the on-line points with
`|x_k|<t₀=e^L`. Every kept ordinate is above `t₀`, so each unit window holds at most `6(L/2π+1)≤2log(|t|+3)` zeros.

Let `τ=π/(2T)`, `N=⌈13at₀⌉`, and let `g` be the finite difference of `f` with transform `sin(τz)^N f̂(z)`. Its support
is `[−A,A]`, `A=a+Nτ≤2a`, and `k̂_g=sin(τz)^{2N} k̂_f` for the autocorrelation `k`.

1. **On-line terms.** `|sin(τx)|≤1` on the real line, so `|ĝ(x)|≤|f̂(x)|`. Summing against grid Parseval gives
   `Σ_U(2|f̂|²−2|ĝ|²)≤2L(‖f‖²−‖g‖²)` on any finite `U`.
2. **Removed points.** `k̂_g(z)=z^{2N}H(z)` with `H` entire. On the circle of radius `R=e·r`, `r=2t₀`,
   `|k̂_g|≤4A‖g‖²e^{2AR}`. The maximum principle gives `|ĝ(x)|²≤e^{−2N}4A‖g‖²e^{2AR}` for `|x|≤r`. With `2N≥26at₀` and
   `2AR≤24at₀`, the total is at most `(L/4)‖g‖²`.
3. **Packet.** With `w=τ(z−T)`, `sin(τz)=cos w`, so `|1−sin(τz)^{2N}|≤4N|w|²`. Off-line terms of `f` and `g` differ by at
   most `(L/4)‖g‖²` in total.
4. **Floor.** The crystal floor at `A` gives `Re W_cluster(g,g)≥(7/4)L‖g‖²`.

Together, `Re W_Z(f,f)≥(5/4)L‖g‖²≥0`.

The zero of the localizer makes hiding below `t₀` harmless without any lower bound for `f̂` near `T`, so no
Turán–Nazarov inequality is needed.

## Lean

`GaloisForLFunctions.WindowVisibilityLaw.exists_hidden_fixed_depth_zero_at_logarithmic_aperture`, with
`windowPositiveAt_cutCrystal` and `cutCluster_local_count`, in `WindowVisibilityLaw/TheCutCrystalHidesFixedDepth.lean`;
`norm_paperFT_sinePower_sq_le` and `norm_one_sub_sin_pow_le` in `WindowVisibilityLaw/TheSineLocalizerOfATest.lean`.
