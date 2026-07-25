# Selberg Orthogonality Conjecture — long-running working log

- **Opened:** 2026-07-25
- **Goal (user):** prove or disprove Selberg's orthogonality conjecture (Conjecture B) for the
  Selberg class `S`.
- **Mode:** multi-session, survives compaction. THIS FILE IS THE MEMORY. Append findings + dead
  ends here; never re-derive what is already recorded.

---

## 0. Target, stated exactly

`S` = Selberg class (Dirichlet series, meromorphic continuation with at most a pole at `s=1`,
Riemann-type functional equation with gamma factor `γ(s)=Q^s ∏_{j≤r} Γ(λ_j s+μ_j)`, Euler product
`log F(s)=Σ_n b_F(n) n^{-s}` supported on prime powers with `b_F(n) ≪ n^θ`, `θ<1/2`, and Ramanujan
`a_F(n) ≪_ε n^ε`).

- degree `d_F = 2 Σ λ_j`; conductor `q_F = (2π)^{d_F} Q^2 ∏ λ_j^{2λ_j}`.
- **Conjecture A (normality):** `Σ_{p≤x} |a_F(p)|²/p = n_F log log x + O(1)`, `n_F ∈ Z_{≥0}`.
- **Conjecture B (orthogonality, THE TARGET):** for primitive `F,G ∈ S`,
  `Σ_{p≤x} a_F(p) conj(a_G(p))/p = δ_{F,G} log log x + O(1)`.

---

## 1. External SOTA as of July 2026 (audited 2026-07-25)

**Automorphic side is CLOSED.**
- Liu–Ye (Amer. J. Math. 2005) proved SOC for automorphic `L`-functions under GRC; Liu–Wang–Ye
  replaced GRC by Hypothesis H (Rudnick–Sarnak); Avdispahić–Smajlović removed self-contragredience.
- **Yujiao Jiang, "On Hypothesis H of Rudnick and Sarnak", arXiv:2507.20653 (28 Jul 2025)** proves
  Hypothesis H in full generality for `GL_n` over any number field (power sieve + iteration,
  bypassing the functoriality barrier that capped earlier work at `n ≤ 4`). Consequences claimed:
  unconditional GUE for automorphic zeros, first effective polynomial strong-multiplicity-one bound,
  **and SOC for automorphic L-functions with stronger error terms.**
- ⟹ **The ONLY remaining gap is the non-automorphic part of `S`.** SOC for `S` is now, in effect,
  equivalent to "enough of the classification/automorphy conjecture".

**Selberg-class side (all still open):**
- Conrey–Ghosh 1993: `F=1` or `d_F ≥ 1`. So factorization into primitives exists (Prop.); uniqueness
  is exactly what B gives.
- Kaczorowski–Perelli: degree-1 classification (`ζ`, `L(s+iθ,χ)`); `1 ≤ d_F < 2 ⟹ d_F = 1`;
  density theorem `N_F(σ,T) ≪ T^{(4d_F+12)(1-σ)+ε}`; PNT for `F` ⟺ `F(1+it) ≠ 0` (**still open**);
  PNT follows from a weakened Conjecture A ("normality conjecture").
- K–P, "Classification of L-functions of degree 2 and conductor 1" (Adv. Math. 2022;
  arXiv:2009.12329; streamlined + a slip corrected in arXiv:2503.02492, Mar 2025).
- Murty–Murty: strong multiplicity one from `a_F(p)=a_G(p)` AND `a_F(p²)=a_G(p²)`.
  Soundararajan, then M. Farmer (arXiv:2101.02771) weaken the `p²` hypothesis; full SMO open.
- K–P: SMO from `a_F(p)=a_G(p)` alone, ASSUMING polynomial Euler products.
- B ⟹ unique factorization; B ⟹ Artin holomorphy (M.R. Murty); B ⟹ Langlands reciprocity for
  solvable `K/Q`; B ⟹ generalized PNT; B ⟹ algebraic independence of primitives (Molteni).
- Murty–Perelli (IMRN 1999): a pair-correlation conjecture for two primitives implies Selberg's
  conjectures. (So "explicit formula ⟹ SOC" is a KNOWN, already-explored route — do not re-invent.)
- K–P, "The standard twist of L-functions revisited", arXiv:1911.10497 (Acta Arith. 201, 2021):
  for `F ∈ S^♯` of degree `d`, `F(s,α) = Σ a_F(n)n^{-s}e(-α n^{1/d})` continues meromorphically;
  `Spec(F) = { d(m/q)^{1/d} : a_F(m) ≠ 0 }`; at most simple poles at `s*_ℓ = (d+1)/(2d) − ℓ/d − iθ_F`;
  `ρ_0(α) ≠ 0` for `α ∈ Spec(F)`; polynomial growth in vertical strips; new Hurwitz–Lerch-type
  functional equation.

**Internal corpus:** the HGT corpus's "orthogonality" cards (`orthogonality-meta-theorem`,
`universal-prime-side-orthogonality`) are about RH-positivity/polarization, NOT Selberg orthogonality.
Nothing in `formal/` or the pipeline addresses `S` / Conjecture A / Conjecture B. Topic is fresh here.

---

## 2. Structural analysis (own work, 2026-07-25)

### 2.1 The linearity obstruction (organizing principle)
`S` is a monoid under multiplication and the prime-coefficient map `𝔞: F ↦ (a_F(p))_p` is a monoid
homomorphism into `(C^P, +)`: `a_{FG}(p) = a_F(p) + a_G(p)`. Conjecture B is a statement about a
**Hermitian quadratic form** on the image. Nothing in the monoid structure produces the products
`a_F(p) conj(a_G(p))`. Only a Rankin–Selberg-type construction does. This is why B is "as hard as
functoriality", and it predicts that every purely axiomatic/linear manoeuvre must fail.

### 2.2 The bilinear form and what Conjecture A already gives (elementary, likely folklore)
Put `B(F,G) := lim_x (log log x)^{-1} Σ_{p≤x} a_F(p) conj(a_G(p))/p` when it exists. `B` is
biadditive on the monoid and positive semidefinite. Since `a_{FG}=a_F+a_G`,
`2 Re Σ_{p≤x} a_F conj(a_G)/p = (n_{FG} − n_F − n_G) log log x + O(1)`,
so **Conjecture A alone forces `Re B(F,G) ∈ (1/2)Z`**, and Cauchy–Schwarz gives
`|B(F,G)|² ≤ n_F n_G`. For primitives (`n=1`) this pins `Re B ∈ {0,±1/2,±1}`. Conjecture A gives
NO information on `Im B`; that is exactly the residual gap. (⟹ A ⇏ B by this route.)

### 2.3 Exact identity: B is the non-additivity defect of the `p²`-functional  [OWN, 2026-07-25]
Since `a_{F conj(G)} = a_F * a_{conj G}` (Dirichlet convolution),
```
a_F(p) · conj(a_G(p))  =  a_{F·conj(G)}(p²) − a_F(p²) − conj(a_G(p²)).
```
Hence with `T_H(x) := Σ_{p≤x} a_H(p²)/p`,
```
Σ_{p≤x} a_F(p) conj(a_G(p))/p  =  T_{F conj(G)}(x) − T_F(x) − conj(T_G(x)).
```
**So Conjecture B is equivalent to a statement about the single-function LINEAR sums `T_H(x)`,
`H ∈ S`.** (Automorphic sanity check: `T_H(x) ~ ord_{s=1} L(s,Sym² H) · log log x`, and
`Sym²(π ⊞ ~π') = Sym²π ⊞ (π ⊗ ~π') ⊞ Sym²~π'` reproduces the RS pole exactly.)
Caveat recorded: the identity is a tautology at the level of information (`a_H(p²)` still contains
`a_H(p)²/2`), so it is a *reformulation*, not a gain — but it moves the target to a linear functional
of one element, which is the natural home for explicit-formula/Tauberian technology.

### 2.4 The real linchpin: the Energy Bound  [named 2026-07-25]
> **(EB)** For every `F ∈ S`:  `Σ_{p≤x} |a_F(p)|²/p ≪_F log log x`.

Equivalently (essentially) `Σ_{n≤x} |a_F(n)|² ≪ x (log x)^{O(1)}` — the *abstract Rankin–Selberg
upper bound* inside `S`. From the axioms only `≪ x^{1+ε}` is available (Ramanujan). EB is the
upper half of Conjecture A, and it is the input needed for every soft argument below.
**Status: believed open. Not found in the surveyed literature.**

### 2.5 Why EB cannot be proved from axioms 1,4,5 alone (own, 2026-07-25)
Counterexample to "axioms minus continuation": `F(s) = exp(Σ_p (log p)^{10} p^{-s})` satisfies
Dirichlet-series convergence, Ramanujan (`a_F(p^k) = a_F(p)^k/k! ≪_ε p^ε`), and the Euler-product
axiom with `b_F(p^k)=0`, `k≥2`, yet `Σ_{p≤x}|a_F(p)|²/p ≍ (log x)^{20}`. It fails ONLY axiom 2:
`log F` has a pole of order 10 at `s=1`, so `F` has an essential singularity there.
⟹ **EB must be forced by meromorphic continuation + functional equation, i.e. by the ZEROS.**

### 2.6 Abstract Rankin–Selberg = Bohr–Parseval pairing of an almost-periodic form  [OWN]
Let `d = d_F = d_G` and set `R_{F,G}(w) := Σ_n a_F(n) conj(a_G(n)) n^{-w}` (abs. conv. `Re w>1`).
Define the **degree-`d` form** `𝔣_F(z) := Σ_n a_F(n) e(z n^{1/d})`, `Im z > 0`. Then
`M_α( 𝔣_F(α+iy) conj(𝔣_G(α+iy)) ) = Σ_n a_F(n)conj(a_G(n)) e^{-4π y n^{1/d}}`
(`M_α` = Bohr mean), whose Mellin transform in `y` is `Γ(u)(4π)^{-u} R_{F,G}(u/d)`.
So: **continuation of `R_{F,G}` past `w=1` ⟺ the `y→0` mass asymptotics of the almost-periodic
form `𝔣_F`.** For `d=1` the frequency set is `Z` (a group) ⟹ periodicity ⟹ `Γ`-action ⟹ classical
Rankin–Selberg unfolding. For `d ≥ 2` the frequency set `Λ_d = {n^{1/d}}` is **not a group**, there
is no `Γ`, and the unfolding dies. *This is the precise structural reason SOC is open for `d ≥ 2`.*
K–P's standard-twist functional equation is exactly the surviving substitute for modularity.
`𝔣_F(α+iy)` is the standard twist `F(s,α)` continued to complex `α`; its poles in `s` at
`s_0=(d+1)/(2d)` with residues `∝ conj(a_F(n_α))` on `Spec(F)` say that `𝔣_F` develops a Dirac-comb
singularity on `Spec(F)` as `y→0`; the RS residue is the `L²`-mass of that comb.

### 2.7 Vertical-mean route and why it stops exactly at the abscissa
`R_{F,G}(2σ) = lim_T (2T)^{-1}∫_{-T}^{T} F(σ+it) conj(G(σ+it)) dt` (Carlson) for `σ>1/2`; below
`σ=1/2` the functional equation forces growth `T^{d(1-2σ)}`, so the limit does not exist. Also:
if `d_F=d_G` and `q_F=q_G` the archimedean phases `X_F conj(X_G)` cancel exactly; if
`d_F ≠ d_G` a residual phase `exp(it(d_G−d_F)log t)` survives. **Recorded conjecture PTO** (§3).

---

## 3. Conjectures on the table

- **(EB) Energy Bound** — §2.4. Status: OPEN, primary target.
- **(PTO) Phase-transversality orthogonality** — if `(d_F,q_F) ≠ (d_G,q_G)` then `F ⊥ G`.
  Mechanism: incompatibility of the functional-equation phases / of the standard-twist spectra
  `Spec(F)`, `Spec(G)`. Would give orthogonality for all pairs outside the "same (d,q)" diagonal.
- **(MASS) Standard-twist mass law** — the `y→0` asymptotics of `M_α|𝔣_F(α+iy)|²` is
  `c_F y^{-d}(log 1/y)^{n_F−1}`; this IS Conjecture A in the almost-periodic picture.

---

## 4. Dead ends / traps already checked (do not repeat)

1. `A ⟹ B` by the monoid identity: gives only `Re B ∈ (1/2)Z`; `Im B` untouched. DEAD as stated.
2. Vertical-shift family `G_θ(s)=G(s+iθ)`: under Conjecture A one gets, by dominated convergence +
   Riemann–Lebesgue, `∫ φ(θ)w(θ)dθ = 0` for every `w ∈ L¹`, hence `Re B(F,G_θ)=0` for **a.e.** `θ`.
   `φ` is Baire-1 and `(1/2)Z`-valued, so its non-zero set is measure-zero — but `θ=0` is exactly the
   allowed exceptional point. No contradiction; consistent with B. Positive residue: recorded as a
   conditional theorem candidate (a.e. shift-orthogonality) — needs a novelty check.
3. Carlson / mean-square in vertical strips: cannot cross `Re w = 1` (abscissa of `R_{F,F}` is
   exactly 1 because the coefficients are `≥ 0`). DEAD for continuation.
4. Borel–Carathéodory bound on `log F` near `σ=1`: loses a factor `1/(σ-1)`; needs a zero-free
   region, which is the (open) generalized PNT. DEAD without new input.
5. Pointwise coefficient bounds (`a_F(p) ≪ p^ε`, `b_F(p^k) ≪ p^{kθ}`, contour extraction from the
   local factor `F_p`): all give `Σ_{p≤x}|a_F(p)|²/p ≪ x^ε`. No cancellation ⟹ DEAD.
6. Explicit-formula / pair-correlation route to B: ALREADY DONE by Murty–Perelli (IMRN 1999).
   Do not re-derive.
7. `Rankin–Selberg problem` is a *taken* name (error term in `Σ_{n≤x}|a_f(n)|²` for cusp forms).
   Use "Energy Bound / abstract RS upper bound" for the `S`-version.

---

## 5. Session log

- 2026-07-25 — cycle 1. Phase 1 (corpus) + Phase 2 (external SOTA) done; §2 structural analysis
  produced; EB named as the linchpin; §2.3 identity and §2.6 almost-periodic reframing recorded.

---

## 6. Cycle 1 result (2026-07-25): the **Monodromy Integrality** conjecture

Card: `selberg-monodromy-integrality.md`.

> **(MI)** For all `F,G ∈ S`, `R_{F,G}(w) = Σ_n a_F(n) conj(a_G(n)) n^{-w}` is **meromorphic**
> (single-valued) on a neighbourhood of `{Re w ≥ 1}`, holomorphic and non-vanishing on
> `{Re w = 1}\{1}`.

**The move:** the received missing ingredient is "`S` is closed under Rankin–Selberg convolution"
or "`S` is automorphic" — both demand of `R_{F,G}` a functional equation, an Euler product of the
right degree, entirety, and a spectral model. MI demands **only single-valuedness**. Isolated claim:
*the whole arithmetic content of Selberg's Conjecture A is the absence of a branch point of
`R_{F,F}` at `w=1`.* `n_F` becomes an order of a pole (a winding number), not a representation
multiplicity.

**Proved (paper, dependency-closed as implications):**
- **Thm 1.** MI(F,F) ⟹ Conjecture A for `F`, with `n_F = −ord_{w=1}R_{F,F} ∈ Z_{≥0}` and error
  `C_F + o(1)`. (Landau for non-negative coefficients gives the singularity; MI turns it into a
  pole; `−P'(w) = Σ_p |a_F(p)|²(log p)p^{-w}` has non-negative coefficients and a simple pole of
  residue `n_F`, so Wiener–Ikehara applies; partial summation.)
- **Thm 2.** MI(F,G) ⟹ `Σ_p a_F(p)conj(a_G(p))p^{-w} = κ_{F,G} log(1/(w−1)) + O(1)` with
  `κ_{F,G} ∈ Z`. **This kills the imaginary part**, which Conjecture A alone cannot reach
  (Conjecture A only gives `Re B ∈ (1/2)Z`, §2.2).
- **Cor 3.** Under MI the Selberg pairing is an **integral** PSD Hermitian form on the monoid `S`;
  Conjecture B then needs exactly two further statements: **(P1)** `n_F = 1` for primitive `F`;
  **(P2)** quantitative strong multiplicity one — `Σ_p|a_F(p)−a_G(p)|²/p = O(1) ⟹ F = G`.
  (P2) strictly strengthens the Murty–Murty / Soundararajan / Farmer line, which assumes
  `a_F(p)=a_G(p)` off a thin set.
- **Thm 4 (axiom-necessity).** `F(s)=exp(Σ_p (log p)^{10}p^{-s})` satisfies Selberg axioms (1),(4),(5)
  and has `Σ_{p≤x}|a_F(p)|²/p ≍ (log x)^{20}`. Hence Conjecture A / EB is **not** a consequence of
  the Dirichlet-series + Euler-product + Ramanujan axioms; every proof must use axiom (2) or (3).

**Lean (certified, unconditional).** `formal/GaloisForLFunctions/RHTower/SelbergPairingPrimeSquare.lean`
- `RHTower.divisorsAntidiagonal_prime_sq`
- `RHTower.arithmeticFunction_mul_apply_prime_sq`
- `RHTower.selberg_pairing_prime_sq` : `f p * conj (g p) = (f * conjArith g)(p²) − f(p²) − conj(g(p²))`
- `RHTower.selberg_pairing_sum_eq`
`lake build` green; `#print axioms` = `[propext, Classical.choice, Quot.sound]` only.
(The remaining `formal_tools.py lint` umbrella errors — `SmoothAFE*`, `WeilIndexBudgetBridge` —
are pre-existing and unrelated.)

## 7. Additional dead ends closed in cycle 1

8.  **APR (archimedean phase rigidity)** — FALSE. `R_{ζ,ζ²}(w)=ζ(w)²` has a double pole although
    `d_ζ=1 ≠ 2=d_{ζ²}`. Correlation tracks divisibility in the monoid, not `(d,q,θ)`.
9.  **`σ_a(F) ≥ 1/2` via "no zeros ⟹ `N_F(T)` bounded"** — REDISCOVERED; K–P (Math. Z. 285 (2017)
    1345–1355, arXiv:1506.07630) prove `σ_a ≥ 1/2 + 1/(2d_F)`.
10. **`ζ^{1/2}` as an axiom-sharpness witness** — FALSE: it fails axiom (3) (a Selberg `Γ`-factor
    quotient cannot equal `χ(s)^{1/2}`) and `d=1/2` is already barred by Conrey–Ghosh. Fractional
    powers cannot produce non-integral `n_F`.
11. **Weak-\* / a.e. shift orthogonality** (`∫Ψ_x(θ)w(θ)dθ → 0` for `w ∈ L¹`, under EB) —
    TRUE but TRIVIAL: it only expresses that the prime measure `m_x` escapes to `u=∞` vaguely.
    Not a step toward `θ=0`.
12. **Equivalence chain** (recorded, probably folklore): EB ⟺ `Σ_{n≤x}|a_F(n)|² ≪ x log^{O(1)}x`
    ⟺ `∫_0^T|F(1/2+it)|²dt ≪ T log^{O(1)}T` (mean-Lindelöf). For `d=2` this is "Good's theorem
    without modularity". Do not expect EB to fall to soft arguments.
13. **Named in the literature:** the "prime mean-square condition (S.6)" and Selberg's
    "prime coefficient condition (S.6*)" already exist as *hypotheses* in the conditional-estimates
    literature for `S`. So EB is a known-open assumption, not a new problem — MI is the new item.

## 8. Next cycle (cycle 2) target

Attack MI itself, on the two fronts the analysis identified:
- (a) **(P1)/(P2)** are now the only gap between MI and Conjecture B. (P2) — "ℓ²-close coefficients
  force equality" — looks the most attackable with existing technology (Farmer/Soundararajan
  explicit-formula method + K–P density theorem). **Make (P2) the concrete theorem target.**
- (b) For MI itself: the almost-periodic reframing §2.6 says MI ⟺ the `y→0` mass law for
  `M_α|𝔣_F(α+iy)|²`. Single-valuedness in `w` should correspond to an *integrality of the
  exponent in the `y→0` expansion*. Look for a mechanism producing meromorphy without an
  integral representation (holonomicity / Nilsson class / finite-dimensional monodromy).
