# The top spectrum of the prime form is exhausted by the integers

- **ID:** rapt-exhaustion-of-the-top-spectrum
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** RAPT §9 topic 2 ("Open: exhaustion of the bounded renormalized spectrum");
  `0-backlog/rapt-top-spectrum-of-prime-form-is-log-integers.md`; RP37.
- **Statement:** For every `T > 0` and `ε > 0`, eventually in `N`, there are vectors `v_m`,
  `m ∈ S_T = {m ≥ 1 : log m + d(m) < T}` (`d` the tame different), such that every `x` orthogonal to
  all `v_m` satisfies `P_N(x) ≤ (log N − γ − T + ε)|x|²`. So at most `#S_T` eigenvalues of `P_N` lie
  above `log N − γ − T + ε`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Proof plan

Work in the pole gauge `y = √n x`, with the harmonic measure `1/n` and `D = Σ Λ(t)/(mt)(y_{mt} − y_m)²`.
The target is `D(y) ≥ (T − ε)‖y‖²_μ` for `y ⊥_μ Ψ_m(a(·))`, `m ∈ S_T`, where `a(n)` is the
`Q`-smooth part. Then the ground-state identity gives the bound on `P_N`, as in RP37.

1. **Truncated ladder, exact eigenbasis.** On `{0..J}` with `π_j = p^{−j}` and
   `E(g) = Σ_{i<j} log p p^{−j}(g_j − g_i)²`, set `ψ_k = 1_{j≥k} − c_k 1_{j=k−1}` with
   `c_k = (1 − p^{−(J−k+1)})/(p − 1)`. Then `⟨1, ψ_k⟩_π = 0`, and `⟨ψ_k, ψ_l⟩_π = ⟨1, ψ_l⟩_π = 0`
   for `k < l`. Each `ψ_k` is an exact eigenvector, `Lψ_k = log p (k + c_k) ψ_k`; this was checked on
   the plateau, at `k − 1` and below. Completeness is by downward induction on the tail sums
   `S_k = Σ_{j≥k} π_j r_j`. Consequence:
   `E(g) ≥ T‖g‖² − Σ_{λ_k<T} (T − λ_k)⟨g,ψ_k⟩²/‖ψ_k‖²`.
2. **Finite prime box.** Product modes `Ψ_m(a) = Π_{p<Q} ψ_{p,v_p(m)}(v_p(a))`, indexed by
   `m ∈ smoothBox J Q`, with `λ(m) = Σ_p λ_{p,v_p(m)}`. Induction over primes, using
   `f(a p^j) = Σ_k c_k(a) ψ_k(j)` and orthogonality, gives
   `E_box(f) ≥ T‖f‖² − Σ_{λ(m)<T} (T − λ(m))⟨f,Ψ_m⟩²/‖Ψ_m‖²` for every real `T`. As `J → ∞`,
   `λ(m) → log m + d(m)`. The modes with `λ^J(m) < T ≤ λ^∞(m)` cost at most `(λ^∞ − λ^J)‖f‖²`.
3. **Horizon and fibres.** Zero extension to the box with the halo, as in Module A. Rough
   fibres are tensorized at cost `K/log Q`; choose `log Q/K > T`. Fibre means are compared by
   Jensen, as in RP37. Orthogonality transfers exactly from `y` to the fibre means `h`, because the
   modes depend only on the smooth part (`⟨y, Ψ_m∘a⟩_μ = ⟨h, Ψ_m⟩_ν`). From `ν` on `a ≤ N` to `1/a`
   on `a ≤ X`, the transfer is approximate, with errors `ρ − 1` and the halo, and `#S_T` is finite.

## Log
- 2026-10-28 — created; plan above.
