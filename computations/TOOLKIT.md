# HGT reciprocal-seam computation toolkit

Reusable tooling for the bridge / boundary-Weyl computations (gpt/37–39 agendas, comps #35–59).
**The Runpod and sessions are ephemeral — this directory is the durable copy.** Everything needed to
reconstitute the work on a fresh machine is here: the libraries, the cached zeros, and the scripts.

## 1. Reconstitute on a fresh node
```bash
# remote was: ssh root@<host> -p <port>  (Runpod, ephemeral). python3 was 3.8 (no pip);
# the working interpreter was python3.13.
python3.13 -m pip install mpmath numpy scipy gmpy2
# copy the toolkit up:
scp hgtlib.py hgtlib_L.py hurwitz_batch.py zeros400.txt zeros.txt <node>:~/work/
# then any comp script runs from that dir, e.g.:
python3.13 2026-06-22-comp53-54-weyl.py
```
Scripts import the libs by RELATIVE path (`spec_from_file_location("hgtlib","hgtlib.py")`), so run
them from the directory containing `hgtlib.py` / `hgtlib_L.py`. The batched-Hurwitz module is imported
as a file named `2026-06-22-hurwitz-batch.py` in the DH scripts; `hurwitz_batch.py` is the stable copy.
Verified env (2026-06-22): mpmath 1.4.1, numpy 2.5.0, scipy 1.18.0, gmpy2, 16 cores.

## 2. Data cache (expensive — keep it)
- **`zeros400.txt`** — first 400 nontrivial ζ zeros (ordinates γ_n), dps≈240, one per line, high precision.
  Verified genuine (max |ζ(½+iγ)| ~1e-238). First line = 14.13472514173469379...  (~44s to recompute).
- `zeros.txt` — copy of `zeros400.txt` (older comp scripts load this name).
- Regenerate: `python3.13 2026-06-22-build-zeros.py 400 240` → writes `zeros.txt` (then `mv zeros.txt zeros400.txt`).
  **Note:** the EXACT moments (below) do NOT use these zeros — the cache is only for γ_d normalization,
  truncated-sum cross-checks, and the fake-divisor battery.

## 3. Core libraries

### `hgtlib.py` — ζ reciprocal-seam machinery (all SPD under RH, mpmath high precision)
- `T_moments_exact(kmax)` — **EXACT** zero moments `T_k = 2 Σ_{γ>0} γ^{-2k}`, k=1..kmax, with NO
  zero-truncation, via `c_{2k}=[w^{2k}] log Ξ(w)`, Ξ(w)=ξ(½+w):
  closed pieces `log(1-4w²)`, `logΓ(¼+w/2)`, and `g_{2k}=[w^{2k}] log ζ(½+w)` by a log-of-series
  recurrence on `a_m = ζ^{(m)}(½)/m!`. (An 80-zero truncated sum corrupts T_1 by 15% — always use this.)
  Cancellation ~0.6·2k digits ⟹ set `mp.mp.dps` high enough.
- `H0_matrix(d,T)` — moment matrix `H^0_{ij}=T_{i+j+1}` (the Q_0 form, Hankel).
- `Mtriv_matrix(d)` — trivial-zero protector `M_{ij}=(-1)^{i+j} P_{i+j+1}`, `P_m=4^{-m}ζ(2m,5/4)` (exact).
- `add_quartet_moments(T, beta, gamma0, weight=2)` — inject an off-line FE quartet {½±(β-½)±iγ0}.
- `gen_eig_sym(A,B)` — generalized symmetric eigenproblem A x = μ B x (A,B SPD) via Cholesky+eigsy.
- `overlap_with_pole(c)` — |cos| between coeff vector c and pole vector u_i=(-4)^i.
- `load_zeros(path,n)`, `y_atoms(gammas)` (y=1/γ²), `T_moments(ys,kmax)` (truncated, for fakes/injection).

### `hgtlib_L.py` — Dirichlet L-function analogue (real primitive characters)
- `CHARS` — chi3, chi4(=β), chi5, chi7, chi8 (q, parity a, χ values).
- `T_moments_L(name, kmax)` — exact L-zero moments via `[w^{2k}] log Ξ_χ`, completion
  (q/π)^{(s+a)/2}Γ((s+a)/2)L(s,χ); NO log(1-4w²) (L has no pole).
- `Mtriv_L_matrix(d, a)` — L protector, `P_m=4^{-m}ζ(2m,(a+½)/2)` (even a=0→ζ(2m,¼), odd a=1→ζ(2m,¾)).
- `xi_chi(name, s)` — completed L (real on critical line; for zero-finding cross-checks).
- Coarsest trivial-zero (rank-one boundary) point: `y_{*,χ}=-(a+½)^{-2}`, mass `a_{*,χ}=|y_{*,χ}|`.

### `hurwitz_batch.py` — moment-build accelerator (the DH compute fix)
- `hurwitz_taylor(a, s0, M, N=None, J=None)` — ALL M Taylor coeffs `ζ^{(n)}(s0,a)/n!` in ONE
  Euler–Maclaurin sweep (main sum + g^{1-s}/(s-1) + ½g^{-s} + Σ B_{2j}/(2j)! (s)_{2j-1} g^{-s-2j+1}).
  mpmath's `mp.zeta(s,a,n)` redoes a full sweep per derivative order — O(M) sweeps; this is O(1).
  Verified vs mpmath to rel 2.7e-499 at dps=500. For a mod-q L-function only q-1 calls are needed
  (one per residue r/q, reused for χ and χ̄). Removes the high-order L-moment-build bottleneck.

## 4. Math objects (what the numbers mean)
- Reciprocal seam-squared coordinate `y_ρ=-(ρ-½)^{-2}`; on-line y=1/γ²>0. RH ⟺ `Q_0[p]=Σc_ic_j T_{i+j+1}≥0 ∀p`.
- `Q_0 = M_triv + R^P`. `K_d = M_triv^{-1/2}(-R^P)M_triv^{-1/2}`; margin = λ_min(H^0,M_triv) = 1-λ_max(K_d).
- **Rank-one boundary form:** `H^0_d = H^- + a_* v_* v_*^T`, v_*=e(-0.16), a_*=(2.5)^{-2}=0.16,
  inertia(H^-)=(d,1). Scalar Weyl gap `s_d = a_* + 1/(v_*^T(H^-)^{-1}v_*) = 1/K_{ν'}(-0.16) = a_*·margin`
  (Sherman–Morrison; all three forms equal exactly). RH ⟺ s_d>0 ∀d.
- Boundary atom = the j=1 term of the archimedean square-sum (source-built, Γ-factor, no zero-feeding).
- Exponent law (margin ~ ∏γ_n^{-α}): `α ≈ 4.31 + ½·ln|y_*|`, y_* = Γ-selected coarsest trivial-zero image.

## 5. Reusable patterns / gotchas
- **Precision:** for margin/rank-one work set `dps ≈ 6.5·d + 120` (the margin reaches ~(d!)^{-3.5}≈10^{-6.5d};
  M_triv conditioning eats more). Self-check by recomputing at dps and dps+80 (must agree).
- **Chunking (<5 min rule):** build moments/matrices ONCE at the chunk's max dps; degree-d matrices are leading
  principal submatrices — slice, don't rebuild. The L/DH moment build is the cost — use `hurwitz_batch`.
- **Background polling gotcha:** `pgrep -f comp58` inside an until-loop matches its OWN command string →
  the monitor spins forever. Match a more specific pattern or check the output file's last line instead.
- mpmath `Date.now`-free: fine; but `mp.eigsy` needs an exactly-symmetric matrix — symmetrize `(C+C.T)/2`.

## 6. Script index (computations/2026-06-22-*)
build-zeros · hgtlib(+_L) · hurwitz-batch · moments-verify (T_k exact vs truncated)
comp7/7b (K_d spectral law) · comp8a/8b/8b2 (Dirichlet+DH) · comp9 (Weil-pullback) ·
comp10 (protector) · comp11 (detection law) · comp13 (fakes) · comp14 (basis) · comp16-12-15
(Schur/Christoffel/Gram-Heine) · comp45 (Jacobi J+E) · comp48 (criticality) · comp49 (parity α) ·
comp50 (sign-tail) · comp51/59 (Gram-Heine d≤6) · comp52 (rank-one boundary) · comp53-54 (scalar
Weyl + unification) · comp55 (L rank-one) · comp56 (tail E Hankel) · comp57 (source-boundary) ·
comp58 (DH scalar-gap, d*=62). Each writes a `.txt` sibling; full narrative in
`../logs/gpt37-computations-worklog.md`.
