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

---

## 9. Cycle 2 (2026-07-25)

### 9.1 The degree-multiplicativity obstruction  [OWN — explains every dead end so far]

Every route tried for constructing `R_{F,G}` — the Bohr mean of standard twists (§2.6), the
vertical mean `lim (2T)^{-1}∫F conj(G)` (§2.7), the α-integral of the twist residues, the
contour/diagonal extraction of K–P residues — is **linear in `F` and linear in `G` separately**.
Under such a map the archimedean invariants of the inputs can only be transported *additively*.
But the target object has degree `d_F · d_G` (the Rankin–Selberg `L`-function of two degree-`d`
objects has degree `d²`, and its `Γ`-factor is a `d²`-fold product). **A separately-linear
construction cannot make degrees multiply.** Hence no diagonal-extraction argument can ever
produce the *functional equation* of `R_{F,G}`.

This is the structural reason to weaken the target: **meromorphy is reachable by such methods in
principle; a functional equation is not.** It is precisely the justification for MI, which asks
only for single-valuedness. Recorded as the organizing no-go for the whole programme.

### 9.2 Abel vs. Tauber split of Selberg's conjectures  [OWN]

Conjecture B has two genuinely different layers:
```
(B-Abel)    Σ_p a_F(p)conj(a_G(p)) p^{-w} = δ_{F,G}·log(1/(w−1)) + O(1)   as w → 1+
(B-Tauber)  Σ_{p≤x} a_F(p)conj(a_G(p))/p  = δ_{F,G}·log log x + O(1)
```
`MI-loc` (meromorphy at the single point `w=1`) already gives (B-Abel); the passage to (B-Tauber)
needs the *line* version of MI (no zeros/poles on `Re w = 1` off `w=1`) — this is exactly where the
generalized PNT lives. Consequence: **(B-Abel) for the pair `(F, ζ)` is unconditional and trivial**
(`R_{F,ζ}(w) = F(w)` and `log F(w) = m_F log(1/(w−1)) + O(1)`), while (B-Tauber) for the same pair
is open. Any future claim must say which layer it proves.

### 9.3 The unconditional instances of MI  [OWN, with verification against the classical case]

- `R_{F,ζ}(w) = Σ_n a_F(n)·1·n^{-w} = F(w)`. **MI(F,ζ) is automatic** from Selberg axiom (2), and
  `κ_{F,ζ} = m_F` = pole order of `F` at `s=1`. So the `ζ`-column of the Selberg Gram matrix is
  unconditionally integral.
- **MI holds on the submonoid generated by the degree-1 elements.** For `F = ∏_i L(s,χ_i)^{e_i}`,
  `G = ∏_j L(s,ψ_j)^{f_j}` the local computation gives
  `R_{F,G}(w) = ∏_{i,j} L(w, χ_i conj(ψ_j))^{e_i f_j} · (holomorphic, non-vanishing on Re w > 1/2)`,
  hence meromorphic, with `κ_{F,G} = Σ_{i,j} e_i f_j δ_{χ_i,ψ_j}`. Theorem 1 then returns *exactly*
  the classical degree-1 case of Selberg's conjectures. MI meets the strongest parent theory.
- `R_{F, L(·,χ)}(w) = F^{conj χ}(w)` — the **Dirichlet twist**. So `MI(F, L(·,χ))` ⟺ the χ-twist of
  `F` is meromorphic at `w=1`. **Not free for `d_F ≥ 2`:** K–P obtain continuation only for
  nonlinear twists with exponents `≤ 1/d`; the Dirichlet twist is built from *linear* twists
  (exponent 1), covered only when `d ≤ 1`. Confirmed against arXiv:1304.4734 / 1507.07177 /
  1911.10497. So "SOC against all degree-1 elements" is **not** obtainable this way.
- `R_{F, ζ^a}(w) = Σ_n a_F(n) d_a(n) n^{-w}` for `a ≥ 2` is **not** free either: `Σ_k (k+1)h_k(α)x^k`
  is a product of `L`-factors only in special cases (e.g. degree 2 with `αβ = 1`, where it equals
  `(1−x²)L_p(x)²`, giving `Σ_n a(n)d(n)n^{-s} = L(s,f)²/ζ(2s)`); no general identity.

### 9.4 K–P residue formula (recorded — the exact tool)

Kaczorowski–Perelli, *The standard twist of L-functions revisited*, Thm 3: for `F ∈ S^♯`,
`d ≥ 1`, `α ∈ Spec(F)`,
```
ρ_ℓ(α) = (d_ℓ/d) · (ω_F/√(2π)) · e^{−iπ(ξ_F + d s*_ℓ)/2} · (q^{1/d}/(2πd))^{d/2 − d s*_ℓ}
         · conj(a_F(n_α)) / n_α^{1 − s*_ℓ}
```
with `n_α = q d^{−d} α^d`. **The prefactor depends only on the invariants `(d, q, ξ_F, ω_F)`, not on
`α` nor on the coefficients.** Hence for `F,G` with equal `(d,q,θ)`:
`conj(a_F(m)) a_G(m) = C · m^{1−1/d} · ρ_0^F(α_m) conj(ρ_0^G(α_m))`, i.e. the Selberg pairing is
literally a pairing of standard-twist residues over the common spectrum lattice
`{d(m/q)^{1/d}}`. Exact and unconditional — but §9.1 says this cannot yield the RS functional
equation, only (at best) meromorphy.

### 9.5 New side conjecture: **(BS) Bounded Satake**

> For every `F ∈ S` there is `B_F` with `|a_F(p)| ≤ B_F` for all primes `p`.

**BS ⟹ EB** immediately (`Σ_{p≤x}|a_F(p)|²/p ≤ B_F² log log x + O(1)`). BS is strictly weaker than
the polynomial-Euler-product conjecture, and is implied by it together with Ramanujan (Ramanujan at
*high* prime powers forces the local roots to satisfy `|α_j| ≤ 1`, since
`h_k(α) ≍ (max|α_j|)^k k^{∂−1}` and `h_k(α) ≪_ε p^{kε}`). Unconditionally the axioms give only
```
|a_F(p)| ≤ 4 C_{ε(p)}   with  ε(p) = 1/(2 log₂ p),
```
(Cauchy on `|x| = 1/2` for the local factor `F_p(x)=Σ_k a_F(p^k)x^k`, using
`|a_F(p^k)| ≤ C_ε p^{kε}` and choosing `ε` so that `p^ε ≤ √2`), where `C_ε` is the Ramanujan
constant — no boundedness. So BS is genuinely open.

### 9.6 Cycle-2 blockers, recorded

- **(P2) is blocked by convergence, not by ingenuity.** `Σ_p|c(p)|²/p < ∞` gives
  `Σ_p |c(p)| p^{-σ} < ∞` only for `σ > 1` (Cauchy–Schwarz against `Σ_p p^{1−2σ}`), so
  `log(F/G)` does *not* continue past `σ = 1` and the Soundararajan/Farmer explicit-formula method
  (which needs the prime part analytic in `σ > 1/2 − δ`, obtained there from *exact* equality off a
  thin set) does not start. Any proof of (P2) needs a new idea, not a sharpening.
- **(P1) is the "cuspidal ⟹ Schur" content.** Under MI, `n_H ≤ Ω(H)·Σ_i n_{F_i}` (Cauchy–Schwarz on
  the factorisation), and Conrey–Ghosh gives `Ω(H) ≤ d_H`; but SOC needs the *reverse* inequality
  `n_H ≤ Ω(H)`. Lattice theory alone cannot give it: an integral PSD form with generators of norm 2
  and inner product −1 (the `A₂` root lattice) is not excluded by any formal property of the monoid.
  So (P1) needs arithmetic input, and specifically an upper bound on `n_F` in terms of `d_F`.

### 9.7 Cycle-3 target

`n_F ≤ d_F²` unconditionally — equivalently, "Ramanujan on `L²`-average at primes":
`Σ_{p≤x}|a_F(p)|²/p ≤ (d_F² + o(1)) log log x`. This is the *one* inequality that ties the
archimedean invariant `d_F` to the prime-side energy, it implies EB, and combined with MI + (P1)
it closes Conjecture B for primitive elements of degree 1 automatically. Attack route: BS, or the
`ε(p)`-explicit Ramanujan bound above combined with the K–P residue formula (which expresses
`a_F(m)` as a residue whose prefactor is built from `(d,q,ξ_F,ω_F)` alone — the only place in the
axioms where `d_F` can meet `a_F(p)`).

---

## 10. Cycle 3 (2026-07-25)

### 10.1 The linear-moment closure principle  [OWN — sharpest form of the obstruction]

For `H ∈ S`, the Euler-product axiom gives, unconditionally,
`Σ_p a_H(p) p^{-w} = log H(w) + (holomorphic on Re w > 1/2)`.
So the axioms deliver *exactly* the **linear** prime-moments `M_{1,0}, M_{0,1}` of any element and,
by the monoid structure and vertical shifts, every ℂ-linear combination of them. Selberg's
Conjecture A asks for the **quadratic** moment `M_{1,1}(w) = Σ_p |a_F(p)|² p^{-w}`, which lies in the
*square* of that space. There is no operation inside `S` producing it: the span of
`{log H : H ∈ S}` is a vector space, not an algebra.

> **Consequence.** A proof of Conjecture A must exhibit *one new meromorphic function* whose
> prime-log-coefficients are `|a_F(p)|²`. There is no way around it. MI is the minimal such demand
> (meromorphy only, no functional equation — cf. §9.1, which shows a functional equation is
> unreachable by any separately-linear construction).

### 10.2 Twist-diagonal reduction  [OWN]

Let `F,G ∈ S^♯` of degree `d`, `φ ∈ C_c^∞((0,∞))`, and let `F(s,α)`, `G(u,α)` be the K–P standard
twists. For `Re s, Re u > 1`,
```
J(s,u;φ) := ∫_0^∞ F(s,α) conj(G(conj u,α)) φ(α) dα
          = Σ_{m,n} a_F(m) conj(a_G(n)) m^{-s} n^{-u} · φ̂(n^{1/d} − m^{1/d}),
```
so, isolating the diagonal,
```
φ̂(0) · R_{F,G}(s+u) = J(s,u;φ) − Σ_{m≠n} a_F(m)conj(a_G(n)) m^{-s}n^{-u} φ̂(n^{1/d}−m^{1/d}).
```
`J` is built from the K–P continuations on a **compact** α-range, and the twist is entire for
`α ∉ Spec`, a finite subset of that range. Hence:

> **MI for `(F,G)` reduces to the meromorphy at `w = 1` of the off-diagonal (shifted-convolution)
> series, whose effective shift range is `|h| = |m−n| ≲ n^{1−1/d}`.**

For `d = 1` the range is empty — the diagonal is isolated — which is exactly why degree 1 is the
solved case, and it recovers the classical result through this mechanism. For `d ≥ 2` the range is
non-empty and grows with `d`; dilating `φ` to `[A,2A]` shrinks the range to `|h| ≲ n^{1−1/d}/A`
but never to zero in the `n → ∞` limit that produces the pole. Note the direction is the reverse of
the usual one: here shifted convolutions are the **input** and Rankin–Selberg the **output**.

**[OPEN CORE of this reduction]** uniform-in-`α` bounds for the continued standard twist near
`Spec(F)`: for `s` fixed off the `s_ℓ`, is `α ↦ F(s,α)` locally bounded on compacta? K–P state only
"polynomial growth on every vertical strip, although the known bounds are weak in general" and do
not address `α`-uniformity. Without it `J` is not known to be entire. **This is now the single most
concrete unsolved technical point in the programme.**

### 10.3 Function-field calibration  [OWN — what the model says the number-field difficulty is]

Over `F_q` the analogue of SOC is a theorem, proved by: (i) a sheaf/motive, (ii) Deligne purity,
(iii) Schur's lemma for the geometric monodromy group. Two features are automatic there and absent
over `Q`: local factors are polynomials of bounded degree (so `BS` holds by construction), and the
tensor product of sheaves exists (so `R_{F,G}` exists and is rational, hence MI is free). So the
model isolates exactly the two number-field obstructions: **(a) unbounded local data — conjecture
BS; (b) no tensor product — conjecture MI.** Nothing else is missing.

### 10.4 Lean additions (certified this cycle)

`formal/GaloisForLFunctions/RHTower/SelbergPairingPrimeSquare.lean` now also contains
- `RHTower.arithmeticFunction_mul_apply_prime'` — additivity of the prime coefficient;
- `RHTower.selberg_energy_polarization` — `Σ|a_{FG}(p)|²/p = Σ|a_F|²/p + Σ|a_G|²/p +
  2 Re Σ a_F conj(a_G)/p` over any finite prime set: the exact mechanism by which Conjecture A
  constrains only the **real** part of the pairing (§2.2).
`lake build` green; `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all four
theorems.

### 10.5 Cycle-4 target

Settle §10.2's [OPEN CORE]: **`α`-uniform bounds for the continued standard twist.** Concretely,
for `F ∈ S^♯` of degree `d ≥ 2` and `s` in a compact set disjoint from `{s*_ℓ}`, prove
`F(s,α) ≪_{F,s,K} 1` uniformly for `α` in a compact `K ⊂ (0,∞)`, or exhibit the blow-up rate near
`Spec(F)`. Route: K–P's new Hurwitz–Lerch functional equation (arXiv:1911.10497, Thm 2) expresses
`F(s,α)` as `Σ_ℓ d_ℓ Γ(d(1−s)−e_ℓ) \bar F_ℓ(1−s,α) + R(1−s,α) + H_k(s,α)` with `H_k ≪ |t|^{−θ}`;
the `α`-dependence sits in the entire functions `\bar F_ℓ(1−s,α)` and in `R`. Bounding those in `α`
is the concrete task. If it succeeds, §10.2 makes `J` entire and MI becomes exactly a
shifted-convolution statement.

---

## 11. Cycle 4 (2026-07-25) — §10.2 partially SELF-KILLED, with the exact reason

### 11.1 Lemma A′ (PROVED HERE, elementary): the standard-twist family jumps at its spectrum

> Let `F ∈ S^♯` have degree `d ≥ 1`, let `α₀ ∈ Spec(F)`, and let `r > 0` be small enough that the
> circle `C_r = {|s − s*₀| = r}` encloses no pole of `F(·,α)` other than possibly `s*₀`. Then for
> **every** `α ∉ Spec(F)`,
> ```
> sup_{s ∈ C_r} | F(s,α₀) − F(s,α) |  ≥  |ρ₀(α₀)| / r  > 0.
> ```

*Proof.* `F(·,α)` is entire for `α ∉ Spec(F)`, so `∮_{C_r} F(s,α) ds = 0`, while
`∮_{C_r} F(s,α₀) ds = 2πi ρ₀(α₀)`. Hence
`2π|ρ₀(α₀)| = |∮_{C_r}(F(s,α₀) − F(s,α))ds| ≤ 2πr · sup_{C_r}|F(s,α₀) − F(s,α)|`.
`ρ₀(α₀) ≠ 0` is K–P's theorem for `α₀ ∈ Spec(F)`. ∎

**Consequences.**
1. `α ↦ F(·,α)` is discontinuous at every point of `Spec(F)`, in the sup-norm on any small circle
   around `s*₀`, with a *uniform* jump `≥ |ρ₀(α₀)|/r`. Since `|ρ₀(α₀)| = C_F |a_F(m)| m^{(1−d)/(2d)}`
   with `m = n_{α₀}`, the jump size is an explicit multiple of the coefficient being detected.
2. Therefore the family `{F(·,α)}` is **not** locally uniformly bounded near `Spec(F)` on any domain
   containing `s*₀` and meeting `{σ>1}` (else Montel + continuity of `F(s,α)` in `α` on `σ>1` would
   force `F(·,α₀)` holomorphic at `s*₀`, i.e. `ρ₀(α₀)=0`).
3. **Correction to §10.2:** the claim there that `J(s,u;φ) = ∫F(s,α)conj(G(conj u,α))φ(α)dα` is
   *entire* is **FALSE**. The identity
   `φ̂(0)·R_{F,G}(s+u) = J(s,u;φ) − Σ_{m≠n}(…)` remains valid for `Re s, Re u > 1`, but `J` cannot be
   continued past `Re s, Re u > 1` by dominated convergence: the integrand is unbounded in `α` at
   every spectral point in `supp φ` as soon as `s` approaches `s*₀`.

### 11.2 What survives, and why this is the right kind of failure

The blow-up is not a technical nuisance — it is **the mechanism itself**. The α-integral must
diverge at `Spec(F)`, because the divergence is exactly the diagonal it is supposed to produce.
So the correct object is a **regularised** α-pairing, and the regularisation *is* `R_{F,G}`.
Positive residue extracted:

> The abstract Rankin–Selberg convolution of `F` and `G` is the regularised α-pairing of their
> standard twists across the common spectrum lattice `{d(m/q)^{1/d}}`, and the size of the required
> regularisation at the point `α_m` is exactly `|ρ₀^F(α_m) conj(ρ₀^G(α_m))| = C·|a_F(m)a_G(m)|
> m^{(1−d)/d}`.

Any future attempt must therefore supply a *regularisation scheme* (a Hadamard finite part, a
zeta-regularised pairing, or a contour deformation in `α`), not a domination argument. **Recorded so
that no later cycle re-attempts a domination/Fubini proof: it cannot work.**

### 11.3 Standing status of the programme

| statement | status |
|---|---|
| SOC (Conjecture B) | OPEN |
| Conjecture A | OPEN; **implied by MI** (Thm 1, cycle 1) |
| MI | OPEN — the [OPEN CORE] |
| MI ⟹ A ⟹ (K–P) generalized PNT | PROVED (cycle 1) |
| B ⟸ MI + (P1) + (P2) | PROVED (cycle 1, Cor 3) |
| EB ⟸ BS | PROVED (cycle 2) |
| functional equation for `R_{F,G}` by any separately-linear construction | IMPOSSIBLE (§9.1) |
| `J(s,u;φ)` entire | **FALSE** (Lemma A′) |
| domination/Fubini proof of MI via α-integrals | **RULED OUT** (Lemma A′) |

---

## 12. Cycle 5 (2026-07-25) — the regularised two-parameter pairing (replaces the broken §10.2)

### 12.1 The right object: the twist family on the upper half-plane

For `F ∈ S^♯` of degree `d ≥ 1` put
```
Φ_F(s,z) := Σ_{n≥1} a_F(n) n^{-s} e(z n^{1/d}),        z ∈ H = {Im z > 0}.
```
Because `|e(zn^{1/d})| = e^{−2π (Im z) n^{1/d}}`, the series converges absolutely for **every**
`s ∈ C` when `Im z > 0`. So `Φ_F` is holomorphic on `C_s × H_z`, and **entire in `s` for each fixed
`z ∈ H`**. The K–P standard twist is its boundary value: `F(s,α) = lim_{y→0+} Φ_F(s, −α + iy)`.
This is the correct home for the construction: all the analytic difficulty is pushed into the single
limit `y → 0`, and nothing is singular before it.

### 12.2 The regularised pairing  [OWN, PROVED HERE for `y>0`]

For `F,G ∈ S^♯` of the same degree `d`, and `y > 0`, `Re β > 1`, `s ∈ C`, define
```
K(s,β,y) := ∫_1^∞ Φ_F(s, α+iy) · conj( Φ_G(conj s, α+iy) ) · α^{−β} dα .
```

> **(i)** `K` is well defined and holomorphic in `(s,β)` for every `y > 0`, `Re β > 1`, `s ∈ C`.
> **(ii)** `K(s,β,y)` continues meromorphically in `β` to all of `C`, with a **single simple pole at
> `β = 1`**, and
> ```
> Res_{β=1} K(s,β,y) = Σ_n a_F(n) conj(a_G(n)) n^{−2s} e^{−4π y n^{1/d}}  =:  D_y(2s).
> ```
> **(iii)** `∫_0^∞ D_y(w) y^{v−1} dy = Γ(v)(4π)^{−v} R_{F,G}(w + v/d)`.

*Proof.* Expanding both series (absolutely convergent for `y>0`, all `s`):
`K = Σ_{m,n} a_F(m)conj(a_G(n)) (mn)^{−s} e^{−2πy(m^{1/d}+n^{1/d})} I_β(m^{1/d}−n^{1/d})`
with `I_β(δ) = ∫_1^∞ e(αδ) α^{−β} dα`. For `δ = 0`, `I_β(0) = 1/(β−1)` — a simple pole at `β=1`.
For `δ ≠ 0`, repeated integration by parts gives `I_β(δ) = Σ_{j<N} c_j(β) (2πiδ)^{−j−1} +
O_N((1+|β|)^N |δ|^{−N})`, entire in `β`. For `m ≠ n`,
`|m^{1/d} − n^{1/d}| ≫ |m−n| / max(m,n)^{1−1/d} ≫ max(m,n)^{1/d−1}`, so `|δ|^{−N} ≪ max(m,n)^{N(1−1/d)}`
— polynomial, and annihilated by `e^{−2πy max(m,n)^{1/d}}` for every fixed `y>0`. Hence the
off-diagonal sum converges absolutely after continuation and is entire in `(s,β)`; only the diagonal
contributes a `β`-pole, with residue `Σ_n a_F(n)conj(a_G(n))n^{−2s}e^{−4πy n^{1/d}}`. (iii) is the
Mellin transform of `e^{−4πyn^{1/d}}`. ∎

### 12.3 What this buys

`R_{F,G}` is now presented, with no convergence sleight of hand, as
```
R_{F,G}(w)  =  lim_{y→0+}  Res_{β=1} K(w/2, β, y),
```
where for each `y>0` the right-hand side is an **entire** function of `w`. So:

> **MI for `(F,G)` ⟺ the `y → 0` asymptotic expansion of `K(s,β,y)` has coefficients that are
> meromorphic in `s` with integer pole orders.**

Three points make this the right formulation:
1. It is a genuine **regularisation**, not a domination argument, so Lemma A′ (§11.1) does not
   obstruct it. The blow-up is now *quantified*: near a spectral point `α₀ ∈ Spec(F)` the boundary
   limit develops a Poisson-type spike of width `y` and height `≍ |ρ₀(α₀)|/|s − s*₀|`, so
   `∫ |Φ_F|² dα` acquires a `π/y` term whose coefficient is exactly the spectrum-localised
   Rankin–Selberg pairing `Σ_{α₀} ρ₀^F(α₀) conj(ρ₀^G(α₀)) α₀^{−β}` — which by the K–P residue formula
   equals `C · Σ_m a_F(m)conj(a_G(m)) m^{(1−d)/d − β/d}`. **The divergence *is* the convolution.**
2. It is **quadratic** in the pair `(F,G)` — the two twists are paired *before* any analytic
   continuation is applied — so the separately-linear obstruction of §9.1 (degrees add, but the RS
   object has degree `d_F·d_G`) does **not** apply. This is the first construction in the programme
   that is not killed by §9.1.
3. It is uniform in the degree: `d = 1` makes the off-diagonal `δ`-range empty at bounded height and
   recovers the classical case; `d ≥ 2` leaves exactly the shift range `|m−n| ≲ max^{1−1/d}`.

### 12.4 Cycle-6 target (the [OPEN CORE], now sharp)

Prove an asymptotic expansion
```
K(s,β,y) = Σ_{j} c_j(s,β) y^{−λ_j} + O(y^{A}) ,   y → 0+,
```
with `c_j` meromorphic in `s` — equivalently, meromorphic continuation in `v` of
`∫_0^∞ K(s,β,y) y^{v−1} dy` past the first pole. Input available: K–P's Hurwitz–Lerch functional
equation for the standard twist (arXiv:1911.10497 Thm 2) describes the `y→0` boundary data of `Φ_F`
in terms of the dual coefficients `conj(a_F(m))`; the task is to feed it into the α-integral. The
`α`-integral is over `[1,∞)` and the boundary data are spikes at `Spec(F)`, so the natural technique
is a **Hadamard finite part in `y` combined with a Voronoi/dual expansion in `α`.**

### 12.5 Lean state after cycle 5

`formal/GaloisForLFunctions/RHTower/SelbergPairingPrimeSquare.lean` (registered in the `RHTower`
umbrella; `lake build` green; every theorem `#print axioms` = `[propext, Classical.choice,
Quot.sound]`):

| theorem | content |
|---|---|
| `divisorsAntidiagonal_prime_sq` | divisor pairs of `p²` |
| `arithmeticFunction_mul_apply_prime_sq` | three-term convolution expansion at `p²` |
| `arithmeticFunction_mul_apply_prime'` | additivity of the prime coefficient |
| `selberg_pairing_prime_sq` | `a_F(p)conj(a_G(p)) = a_{F·conj G}(p²) − a_F(p²) − conj(a_G(p²))` |
| `selberg_pairing_sum_eq` | the same, summed over any finite prime set with weight `1/p` |
| `selberg_energy_polarization` | `Σ|a_{FG}(p)|²/p = Σ|a_F|²/p + Σ|a_G|²/p + 2Re Σ a_F conj(a_G)/p` |
| `selberg_pairing_cauchy_schwarz` | `‖Σ a_F conj(a_G)/p‖² ≤ (Σ‖a_F‖²/p)(Σ‖a_G‖²/p)` |
| `int_eq_zero_or_one_or_neg_one_of_sq_le_one` | `k ∈ Z, k² ≤ 1 ⟹ k ∈ {0,±1}` |

Together these certify the **entire algebraic bridge of Corollary 3** (cycle 1): polarisation ⟹
only `Re B` is reached by Conjecture A; Cauchy–Schwarz ⟹ `|κ_{F,G}|² ≤ n_F n_G`; integrality (from
MI) ⟹ `κ ∈ {0,±1}` for unit-energy systems. The only non-certified steps of Corollary 3 are the two
analytic ones (Landau, Wiener–Ikehara), which are standard.

### 12.6 Hand-off state (read this first after a compaction)

- **Target:** Selberg Conjecture B. Status OPEN.
- **Best current statement:** MI (§card `selberg-monodromy-integrality.md`). MI ⟹ Conjecture A
  (proved); B ⟸ MI + (P1) + (P2) (proved).
- **Best current mechanism:** §12.2, the regularised pairing `K(s,β,y)` — rigorous for `y>0`,
  with `R_{F,G}(w) = lim_{y→0+} Res_{β=1} K(w/2,β,y)` and each `y>0` slice entire in `w`.
- **Next concrete task:** §12.4 — the `y→0` asymptotic expansion of `K`, via K–P's Hurwitz–Lerch
  functional equation for the standard twist.
- **Do not retry:** anything in §4 (items 1–7), §7 (8–13), §9.1, §9.6, §11.1 (domination/Fubini).

---

## 13. Cycle 6 (2026-07-25) — the cusp expansion and the α-monodromy of the standard twist

### 13.1 Theorem C6.1 (cusp expansion of `Φ_F` at `z = 0`)  [OWN]

> Let `F ∈ S^♯` have degree `d ≥ 1`, conductor `q`, and polar part `Σ_{m≤m_F} γ_m (s−1)^{−m}` at
> `s = 1`. For `z ∈ H` with `|z|` small and every `s ∈ C`,
> ```
> Φ_F(s,z) = P_F(s,z) + Σ_{k≥0} ((2πiz)^k / k!) · F(s − k/d) ,
> ```
> where `P_F(s,z)` is the explicit contribution of the pole of `F` at `s'=1`, namely
> `P_F(s,z) = d·Σ_{m≤m_F} γ_m · (1/(m−1)!)·(d/du)^{m−1}[ Γ(u)(−2πiz)^{−u} ]|_{u=d(1−s)}`,
> and the series converges absolutely.

*Proof.* Insert `e^{−x} = (2πi)^{−1}∫_{(c)}Γ(u)x^{−u}du` with `x = −2πiz n^{1/d}` (legitimate:
`Re(−2πiz) = 2π Im z > 0`), and sum over `n` in the region of absolute convergence to get
`Φ_F(s,z) = (2πi)^{−1}∫_{(c)}Γ(u)(−2πiz)^{−u}F(s+u/d)du` for `c` large.
Shift the contour to `Re u = −M`. The crossed poles are `u = d(1−s)` (from the pole of `F`,
contributing `P_F`) and `u = 0,−1,…,−(M−1)` (from `Γ`), contributing
`((2πiz)^k/k!)F(s−k/d)`. Stirling on `Γ(u)` and the convexity bound on `F` show the shifted
integral is `≪ (C_F|z|)^M`, so the series converges and the remainder vanishes as `M→∞`. ∎

**Radius.** The Stirling bookkeeping gives, with `σ_k = Re s − k/d → −∞`,
`|F(s−k/d)| ≍ (q^{1/d}/(2π))^{k}·(k/d)^{k}e^{−k}` and `k! ≍ (k/e)^k`, so the `k`-th term is
`≍ (2π|z| q^{1/d}/(2π d))^k = (|z| q^{1/d}/d)^k`. Hence the radius of convergence is
```
r(F) = d · q^{−1/d} = min Spec(F).
```
(The equality `min Spec(F) = d(1/q)^{1/d}` holds because `a_F(1) = 1`.) **The cusp expansion
converges exactly up to the first spectral point** — the series "sees" the spectrum as its natural
boundary of convergence. This is a clean structural statement: *the whole spectrum of the standard
twist is encoded in the radius of convergence of the shift-lattice expansion of `F` at the cusp.*

### 13.2 The α-monodromy exponent  [OWN]

K–P's formula (1.19)–(1.20) for `F_ℓ(s,α)` contains, for `j = −N` (i.e. `ω_j = −1/2`), the factor
`(1 − (n_α/n)^{1/d})^{d(1−s−s*_ℓ)}`, and the term `n = n_α` is *omitted* (their `♭`) precisely
because this factor is singular there. Since `1 − (n_α/n)^{1/d} ≍ c·(α − α₀)` near `α₀ ∈ Spec(F)`
with `n = n_{α₀}`, we get:

> **The standard-twist family has a branch point in `α` at every spectral point, with local exponent
> ```
> E_ℓ(s) = d(1 − s − s*_ℓ) ,
> ```
> which is affine in `s`.** At `s = s*_ℓ` it equals `−1` (a simple pole), recovering the K–P residue
> `ρ_ℓ(α₀) ≠ 0`; for generic `s` it is not an integer, so `Φ_F(s,·)` genuinely has **non-trivial
> monodromy in `α`** around each spectral point.

This is the same phenomenon MI is about, transported to the other variable: MI asks for *trivial*
monodromy of `R_{F,G}` in `w`; the twist has *explicitly computable, affine-in-`s`* monodromy in `α`.

### 13.3 The bridge  [OWN — the mechanism for MI]

Combining §12.2 with §13.2: near a spectral point the paired integrand behaves like
`|α−α₀+iy|^{2E(s)}`, so
`∫_{|α−α₀|<ε} Φ_F conj(Φ_G) dα ≍ B(E(s)) · y^{2E(s)+1} · ρ`-data, giving a `y→0` expansion of
`K(s,β,y)` whose **exponents are affine in `s`**: the leading one is
`y^{2E(s)+1} = y^{−d(2s−1)}`. Consequently the Mellin transform
`𝒦(s,β,v) := ∫_0^∞ K(s,β,y) y^{v−1} dy` has poles in `v` on the *explicit affine loci* `v = λ_j(s)`,
while by §12.2(ii)–(iii)
```
Res_{β=1} 𝒦(s,β,v) = Γ(v)(4π)^{−v} R_{F,G}(2s + v/d) .
```
> **Therefore:** `R_{F,G}` continues meromorphically in `w = 2s + v/d` exactly as far as the `y→0`
> expansion of `K` extends, with poles at the explicit points `w = 2s + λ_j(s)/d`; and MI holds iff
> that expansion is of **Nilsson type with integer log-powers** — i.e. iff the `α`-monodromy
> exponents `2E(s)+1`, which are affine in `s`, produce integer-order poles after the `β`-residue.

This closes the logical loop of the programme: MI ⟸ (Nilsson-type `y→0` expansion of `K`) ⟸
(uniform local expansion of the standard twist at its spectrum). The last item is the only missing
input, and it is a *stated* gap in the literature: K–P give the **residue at `s*_ℓ`** but not a
uniform local expansion in `α` with error control.

### 13.4 Cycle-7 target

Prove the **uniform local expansion of the standard twist at a spectral point**: for `α₀ ∈ Spec(F)`
and `s` in a compact set,
```
F(s,α) = c(s) · (α − α₀)^{E_0(s)} · (1 + O(α − α₀)) + (holomorphic in α near α₀),
```
with `c(s*_0) ∝ ρ_0(α₀)`. Route: K–P (1.19) already isolates the singular factor; what is missing is
the convergence/uniformity of the residual series `Σ^♭` near `α = α₀` together with the `H_k(s,α)`
error. Once this is available, §13.3 gives MI, §12.2 gives the continuation of `R_{F,G}`, and cycle
1's Theorem 1 gives Selberg's Conjecture A; Conjecture B then needs only (P1) and (P2).

---

## 14. Cycle 7 (2026-07-25) — the local expansion at a spectral point (the §13.4 gap, now CLOSED)

### 14.0 Correction to §13.2

The exponent read off there from K–P's (1.19) — `d(1−s−s*_ℓ)` — is **wrong**: that exponent belongs
to the auxiliary functions `F_ℓ(s,α)`, not to the local behaviour of the twist in `α`.
The correct local exponent is derived below and is `d(s − s*_ℓ)`. Everything downstream of §13.2 must
use the corrected value.

### 14.1 Theorem C7.1 (Lerch-type expansion of `Φ_F` at a spectral point)  [OWN, PROVED HERE]

> Let `F ∈ S^♯` have degree `d ≥ 1`, let `α₀ > 0`, and let `F(·,α₀)` be its standard twist with
> poles at `s*_ℓ` and residues `ρ_ℓ(α₀)`. Then for `ζ ∈ H` with `|ζ|` small and `s ∉ {s*_ℓ + k/d}`,
> ```
> Φ_F(s, −α₀+ζ) =  d · Σ_ℓ ρ_ℓ(α₀) · Γ(d(s*_ℓ − s)) · (−2πiζ)^{d(s − s*_ℓ)}
>                 + Σ_{k≥0} ((2πiζ)^k / k!) · F(s − k/d, α₀) ,
> ```
> as an asymptotic expansion (truncating the `ℓ`-sum at `Re(d(s*_ℓ−s)) > −M` leaves `O(|ζ|^M)`).
> The first sum is the **singular part**: branch points in `ζ` with exponents `d(s − s*_ℓ)`, affine
> in `s`. The second sum is holomorphic in `ζ` near `0`.

*Proof.* Write `z = −α₀+ζ`; then `e(zn^{1/d}) = e(−α₀n^{1/d}) e(ζ n^{1/d})`, so the Dirichlet series
attached to the coefficients is exactly the standard twist `F(·,α₀)`. Apply the Mellin–Barnes
representation as in Theorem C6.1:
`Φ_F(s,−α₀+ζ) = (2πi)^{−1}∫_{(c)} Γ(u)(−2πiζ)^{−u} F(s+u/d, α₀) du`, `c` large.
Shift to `Re u = −M`. The poles crossed are `u = 0,−1,−2,…` (from `Γ`), giving the holomorphic
series, and `u = d(s*_ℓ − s)` (from the poles of the standard twist), giving
`d·ρ_ℓ(α₀)Γ(d(s*_ℓ−s))(−2πiζ)^{d(s−s*_ℓ)}`. Stirling on `Γ(u)` together with K–P's polynomial
growth of `F(·,α₀)` in vertical strips and their functional equation (1.24) (whose `Γ(d(1−s)−e_ℓ)`
factor controls the growth as `σ → −∞`) bound the shifted integral by `≪ (C_{F,α₀}|ζ|)^M`. ∎

**Verification against the classical case.** `F = ζ`, `d = 1`, `q = 1`, `Spec(ζ) = N`, `α₀ ∈ N`,
`s*_0 = 1`, `ρ_0 = 1`, and `ζ(s,α₀) = ζ(s)`. C7.1 becomes
`Σ_n n^{−s} e(nζ) = Γ(1−s)(−2πiζ)^{s−1} + Σ_{k≥0} ζ(s−k)(2πiζ)^k/k!`,
which is precisely the classical Lerch/Hurwitz expansion. So **C7.1 is the exact Selberg-class
generalisation of the Lerch expansion, valid at every point of the standard-twist spectrum**, with
the pole `s=1` of `ζ` replaced by the ladder of twist poles `s*_ℓ`.

### 14.2 What C7.1 gives the programme

1. It **closes the §13.4 gap**: the uniform local expansion of the twist at its spectrum is not a
   missing input — it follows from K–P's polar data by Mellin–Barnes.
2. The local exponent is `d(s − s*_ℓ)`, so near `α₀` the paired integrand of §12.2 behaves like
   `|ζ|^{2d Re(s − s*_0)}` with `ζ = (α₀−α)+iy`, hence
   `∫_{|α−α₀|<ε} Φ_F conj(Φ_G) dα ≍ B·y^{2d(s−s*_0)+1}`, convergent iff `Re s < 1/2`.
3. Summing the spikes with the weight `α^{−β}` and using the K–P residue formula
   (`ρ_0(α_m) = c_F conj(a_F(m)) m^{s*_0−1}`) gives, for `Re β > d` and `Re s < 1/2`,
   ```
   K(s,β,y) = A(s) · y^{2d(s−s*_0)+1} · Ξ(β) · (1+o(1)),
   Ξ(β) = C · Σ_m conj(a_F(m)) a_G(m) m^{(1−d)/d − β/d} = C · conj(R_{F,G})((d−1+β)/d).
   ```

### 14.3 The exact remaining obstacle, now isolated to one uniformity statement

By §12.2, for each `y>0` and `s`, `K(s,β,y)` is **meromorphic in `β` on all of `C` with a single
simple pole at `β = 1`**. If the asymptotic of §14.2(3) held *locally uniformly in `β`* on compact
subsets of `C ∖ {1}`, then
`Ξ(β) = lim_{y→0} y^{−(2d(s−s*_0)+1)} K(s,β,y)/A(s)` would be a locally uniform limit of functions
holomorphic in `β`, hence holomorphic on `C∖{1}` — i.e. **`R_{F,G}` would be meromorphic on all of
`C` with a single pole at `w = 1`, which is MI in its strongest form.**

The uniformity fails as stated, and the reason is now completely explicit: the spike sum `Ξ(β)`
converges only for `Re β > d`, so for `Re β ≤ d` the `α → ∞` tail of the integral and the `y → 0`
limit interact. (Consistency check: for `d = 1` the abscissa of `Ξ` is `β = 1`, exactly the pole of
`K` — the two structures coincide and degree 1 is the solved case. For `d ≥ 2` the abscissa `β = d`
and the pole `β = 1` are different points, and the gap between them is precisely the unsolved
region.)

> **Cycle-8 target.** The two-variable Mellin analysis of `K(s,β,y)`: split the `α`-integral at a
> threshold `Y(y)`, Mellin-transform in `y` on the spike range and in `α` on the tail, and move the
> `β`-contour from `Re β > d` to `Re β > 1`. The width of the gap to be crossed is exactly `d − 1`,
> which is `0` in the solved case and grows with the degree. **This is the first time in the
> programme that the obstruction has a quantitative width equal to `d − 1`.**

### 14.4 Corpus machinery found (search these before building anything analytic)

Folders to check for existing Lean work (per project owner):
- `formal/GaloisForLFunctions/HTGeometry` — general hypertranscendence + reusable analysis
- `formal/GaloisForLFunctions/RHTower` — zeta / L-function specific
- `formal/GaloisForLFunctions/HilbertMetric` — Hilbert spaces and metrics

Directly relevant to this programme, already present:
- `HTGeometry/BohrAlmostPeriodic.lean` — `IsBohrAlmostPeriodic`, vanishing lemma, closure under
  uniform limits. (§2.6/§12 live in this category.)
- `HTGeometry/AlmostPeriodicHull.lean` — Bochner criterion (`IsBohrAP` via relatively compact
  translation orbit), `bohrHull`, translation isometry, point-value return.
- `RHTower/SecondMoment.lean` — `secondMoment_eq`, `secondMoment_meanValue`: the **exact** diagonal /
  off-diagonal split for classical Dirichlet polynomials (frequencies `log n`, real coefficients).
- `RHTower/FourthMoment.lean` — Montgomery–Vaughan style fourth-moment diagonal.
- `RHTower/SmoothAFEZetaContour.lean`, `SmoothAFEZetaInfiniteContour.lean`, `SmoothAFEZetaStripBound.lean`
  — rectangle → infinite-vertical-line contour-shift identities for a Gaussian-smoothed AFE
  (the machinery a Lean version of Theorems C6.1/C7.1 would build on).
- `RHTower/MobiusLaplaceCriterionFrontier.lean` — `mellin_… = Γ(s)·LSeries` Mellin–Dirichlet bridge.
- `Hurwitz/HurwitzZeta.lean` — Hurwitz series summability.

### 14.5 New Lean infrastructure (cycle 7)

`formal/GaloisForLFunctions/HTGeometry/GeneralizedDirichletMeanValue.lean` (registered in the
`HTGeometry` umbrella; `lake build` green; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`):

- `HTGeometry.genPoly` — `P(t) = ∑_{n∈s} a n · exp(i λ_n t)`, **arbitrary real frequencies**;
- `HTGeometry.oscInt`, `oscInt_zero`;
- `HTGeometry.genPoly_mul_conj` — exact expansion of `|P|²` over frequency differences;
- `HTGeometry.genPoly_meanValue` — **exact** mean value
  `∫_T^{T+U}|P|² = U·∑_n a_n conj(a_n) + ∑_n ∑_{m≠n} a_m conj(a_n)·oscInt(λ_m−λ_n)`,
  with **no hypothesis on the frequencies**.

This generalises `RHTower/SecondMoment.secondMoment_meanValue` from `λ_n = log n` (real
coefficients) to arbitrary real frequencies and complex coefficients, and it is the **exact engine
of §12.2**: taking `λ_n = n^{1/d}` and integrating in the `α` variable is the diagonal extraction
that produces `R_{F,G}`. The frequency-difference asymptotic recorded in the module docstring,
`|m^{1/d} − n^{1/d}| ≍ |m−n|·max(m,n)^{1/d−1}`, is exactly the statement that the diagonal is
isolated only for `d = 1`.

---

## 15. Cycle 8 (2026-07-25) — the framework predicts the pole structure, and self-validates

### 15.1 Internal consistency check (PASSED)

Two independent extractions of `R_{F,G}` from `𝒦(s,β,v) := ∫_0^∞ K(s,β,y) y^{v−1} dy`:

1. **Diagonal / `β`-residue (§12.2):** `Res_{β=1} 𝒦(s,β,v) = Γ(v)(4π)^{−v} R_{F,G}(2s + v/d)`.
2. **Spike / `y→0` (C7.1):** the leading spike term is `K ≍ A(s)·y^{2d(s−s*_0)+1} = A(s)·y^{d(2s−1)}`
   (using `s*_0 = (d+1)/(2d)`), which diverges as `y→0` exactly when `Re s < 1/2` — the same
   condition under which the spike integral `∫(u²+y²)^{d(s−s*_0)}du` converges. Hence `𝒦` has a
   `v`-pole at `v = d(1−2s)`.

At that `v`, the argument in (1) is `2s + v/d = 2s + (1−2s) = 1`. **The `v`-pole produced by the
spectral spikes sits exactly at the Rankin–Selberg pole `w = 1`.** The two descriptions — the
diagonal extraction of §12.2 and the boundary-singularity analysis of C7.1 — therefore describe the
same object, with no free parameters. This is the first end-to-end consistency test of the
construction and it passes.

### 15.2 Exponent bookkeeping ⟹ predicted pole family

C7.1 gives, near a spectral point, singular exponents `d(s − s*_ℓ) = d(s − s*_0) + ℓ` (`ℓ ≥ 0`) and a
holomorphic part with integer exponents `k ≥ 0`. Pairing the `ℓ`-term of `F` with the `ℓ'`-term of
`G` and integrating in `α` gives `y`-exponents
`d(2s−1) + ℓ + ℓ'`, hence `v`-poles at `v = d(1−2s) − ℓ − ℓ'`, hence, through
`w = 2s + v/d`, poles of `R_{F,G}` at
```
w = 1 − j/d ,   j = ℓ + ℓ' ∈ Z_{≥0} .
```
All such coincidences produce log-powers, i.e. **integer** pole orders.

### 15.3 The naive global version is FALSE — and the correct refinement

> **Killed:** "`R_{F,G}` is meromorphic on `C` with poles only in `1 − (1/d)Z_{≥0}`."
> Counterexample: for a holomorphic newform `f` (degree 2), `R_{F,F}(w) = Σ_n|a_f(n)|² n^{−w}
> = ζ(w) L(w,sym²f) / ζ(2w)`, so `1/ζ(2w)` contributes a pole at `w = ρ/2` for **every** zeta zero
> `ρ` — not an arithmetic progression.

But every such pole has `Re w = Re ρ/2 < 1/2` (since `Re ρ < 1` unconditionally). So the correct
statement is:

> **(MI⁺⁺) Refined Monodromy Integrality.** For all `F,G ∈ S` of equal degree `d` and conductor,
> `R_{F,G}` continues meromorphically to `{Re w > 1/2}`, its poles there are contained in
> `{1 − j/d : j ∈ Z_{≥0}} ∩ {Re w > 1/2}`, and every pole has **integer** order.

**Verification on the classical cases.**
- `F = G = ζ` (`d=1`): `R = ζ(w)`; pole at `w=1`, order `1 = n_ζ` ✓, and `1 ∈ 1 − Z_{≥0}` ✓.
- `F = ζ`, `G = L(·,χ)` (`d=1`): `R = L(w, conj χ)`, entire ✓ (orthogonality).
- `F = G = ζ²` (`d=2`): `R = ζ(w)^4/ζ(2w)`; in `Re w > 1/2` the only pole is `w=1` of order
  `4 = n_{ζ²}` ✓, matching `Σ e_i² = 4`.
- `F = G = L(·,f)` newform (`d=2`): `R = ζ(w)L(w,sym²f)/ζ(2w)`; in `Re w > 1/2` the only pole is
  `w=1` of order `1 = n_F` ✓ (primitivity), since `L(·,sym²f)` is entire and `ζ(2w)` is zero-free
  for `Re w > 1/2`.

MI⁺⁺ is bolder than MI (it names the pole locations and the half-plane), is falsifiable, and is
exactly what the C7.1 exponent bookkeeping predicts. It still implies Conjecture A via cycle 1's
Theorem 1, since only the order of the pole at `w=1` is used there.

### 15.4 Where the proof still stops

The bookkeeping above is *formal*: it lists which `y`-exponents can occur. To convert it into a
theorem one needs the C7.1 expansion **uniformly over the spectral points**, i.e. summable error
terms in
```
K(s,β,y) = Σ_{α₀ ∈ Spec ∩ [1,∞)} (spike contribution at α₀) + (non-spike part),
```
with the `α₀`-sum and the `y→0` limit interchangeable down to `Re β > 1`. The obstruction retains
the width `d − 1` measured in §14.3: the spike sum converges only for `Re β > d`, while `K`'s only
`β`-pole is at `β = 1`. **Cycle-9 target: prove the interchange on `Re β > d`, then continue in `β`
by moving the contour, using that `K` itself is `β`-holomorphic there.**

---

## 16. Cycle 9 (2026-07-25) — the width-`(d−1)` gap was an arithmetic error; the real obstruction is spectral accumulation, with threshold `d = 2`

### 16.1 CORRECTION: there is no width-`(d−1)` gap (§14.3, §15.4 were wrong)

Recompute the abscissa of the spike sum. By the K–P residue formula,
`|ρ_0(α_m)| = C_F |a_F(m)| m^{Re s*_0 − 1}` with `Re s*_0 = (d+1)/(2d)`, so
`ρ_0^F(α_m) conj(ρ_0^G(α_m))` carries `m^{2(Re s*_0 − 1)} = m^{(1−d)/d}`, and
`α_m^{−β} = (d q^{−1/d})^{−β} m^{−β/d}`. Hence
```
Ξ(β) = C · Σ_m conj(a_F(m)) a_G(m) · m^{(1−d)/d − β/d} = C · conj(R_{F,G})((d−1+β)/d),
```
which converges iff `Re((d−1+β)/d) > 1` iff **`Re β > 1`** — *not* `Re β > d`.
Cross-check with Ramanujan: `Σ_m m^{(1−d−Re β)/d + 2ε}` converges iff `Re β > 1`. ✓

So the abscissa of the spike sum and the (unique) `β`-pole of `K` **coincide at `β = 1`**.
The claimed gap of width `d − 1` in §14.3 and §15.4 does not exist; delete it.

### 16.2 The correct extraction, and the correct obstruction

With both abscissae at `β = 1`, the two-term `y→0` structure is
```
K(s,β,y) = A(s) y^{λ(s)} Ξ(β)  +  B(s) y^{λ(s)+β−1}/(1−β)  +  (smaller),
λ(s) = d(2s−1),
```
the first term dominating for `Re β > 1` and the second for `Re β < 1` (where the spike sum is
truncated by the `y`-damping at `α ≍ 1/y`, giving `∫^{1/y} u^{−β}du ≍ y^{β−1}/(1−β)`). For `β ≠ 1`
the two `y`-exponents are **distinct**, so the Mellin transform in `y` separates them:
`Ξ(β) = Res_{v=−λ(s)} 𝒦(s,β,v)/A(s)`. Since `K(·,β,·)` is `β`-holomorphic on `C∖{1}` (§12.2), the
residue is `β`-holomorphic wherever the two `v`-poles do not collide — i.e. on `C∖{1}` — which is
exactly MI.

**What actually blocks this is the geometry of `Spec(F)`, not any abscissa gap.**
Consecutive spectral points satisfy
```
α_{m+1} − α_m = d q^{−1/d}((m+1)^{1/d} − m^{1/d}) ≍ q^{−1/d} m^{(1−d)/d},
```
while each spike has width `≍ y`. So the spikes are **isolated** only for
`m ≪ (y q^{1/d})^{−d/(d−1)}`, whereas the `y`-damping `e^{−4πy m^{1/d}}` only kicks in at
`m ≫ y^{−d}`. Comparing the two thresholds:
```
d/(d−1)  <  d   ⟺  d > 2 ;      d/(d−1) = d  ⟺  d = 2 ;      d = 1 : spacing is constant q^{−1}.
```

> **Trichotomy (own).**
> - `d = 1`: spectral spacing is the constant `q^{−1}`; spikes are isolated for all `m` once
>   `y ≪ q^{−1}`. The whole analysis is uniform — this is exactly why degree 1 is the solved case.
> - `d = 2`: the isolation threshold `m ≍ y^{−2}` **coincides** with the exponential-damping
>   threshold `m ≍ y^{−2}`. Every overlapping spike lies inside the exponentially damped tail, so
>   overlap never contributes. The analysis should go through.
> - `d ≥ 3`: `y^{−d/(d−1)} ≪ y^{−d}`, so there is a genuine intermediate range
>   `y^{−d/(d−1)} ≪ m ≪ y^{−d}` in which the spikes overlap while still undamped. **This is the true
>   obstruction.**

This reproduces, from the internal geometry of the construction alone, the known accessibility
boundary of the Selberg class (degree 1 classified; degree 2 conductor 1 classified; degree ≥ 3 wide
open) — strong evidence the framework is tracking the right structure.

### 16.3 Consequence and the concrete degree-2 target

Because the overlap regime is empty for `d ≤ 2`, the construction is expected to yield
**MI, hence Selberg's Conjecture A, unconditionally for every `F ∈ S` of degree 2** — and therefore,
by Kaczorowski–Perelli, the generalized prime number theorem for all degree-2 elements. That is a
genuine open problem (only degree 2 with **conductor 1** is currently classified, by K–P 2022).

> **Cycle-10 target (now fully concrete).** For `d = 2`, prove:
> 1. C7.1 with error terms uniform over `α₀ ∈ Spec(F)` — i.e. `Φ_F(s,−α₀+ζ) = (singular part) +
>    O(|ζ|^M)` with an implied constant `≪ |ρ_0(α₀)| · α₀^{A}` for an explicit `A`;
> 2. the non-spike part of `∫_1^∞ Φ_F conj(Φ_G) α^{−β} dα` is `O(y^{λ(s)+δ})` for some `δ>0`;
> 3. conclude the two-term expansion of §16.2 and extract `Ξ(β)` by the Mellin transform in `y`.
> Items (1),(2) are pure analysis on top of K–P's Theorem 2 (the Hurwitz–Lerch functional equation
> of the standard twist) and Theorem 1 (the bound `F_ℓ(s,α) ≪ e^{(π/2)d|t|}|t|^{c(σ)}` with `c`
> independent of `ℓ` and `α`, whose `α`-dependence K–P state can be made explicit).

---

## 17. Cycle 10 (2026-07-25) — the α-uniformity is available, and item 2 dissolves

### 17.1 The α-dependence of K–P's Theorem 1 is POLYNOMIAL (read off from their §2.2)

Their proof of `F_ℓ(s,α) ≪ e^{(π/2)d|t|}|t|^{c(σ)}` splits `F_ℓ = F_ℓ^{(1)} + F_ℓ^{(2)}`. Tracking where
`α` (through `n_α = q d^{−d} α^d`) can enter:

- the tail term: `Σ_{n>n_α} |a(n)| n^{−σ−(R+1)/d}` with `R > d−1−dσ`, hence `σ+(R+1)/d > 1`, so the
  sum is bounded by `Σ_{n≥1}|a(n)|n^{−c}` with `c>1` — **bounded uniformly in `α`, in fact decreasing
  in `n_α`**;
- `F_ℓ^{(1)}(s,α) ≪ Σ_j Σ_{n ≤ n_α} e^{(π/2 − η_{n,j})d t}` — the **only** genuinely `α`-dependent
  piece: a sum with `n_α` terms, hence `≪ n_α · e^{(π/2)d|t|}`;
- the third-row term `≪ Σ_r (1+|t|)^r (|F(s+r/d)|+1)` — no `α` at all.

> **Consequence.** K–P's Theorem 1 holds with an implied constant `≪_{F,σ} n_α^{A} = O(α^{dA})` for
> an explicit `A` (`A = 1` from the display above, before optimising). **The `α`-uniformity demanded
> by item 1 of the cycle-10 target is not a missing input — it is already inside K–P's proof.**

### 17.2 The truncation parameter absorbs any polynomial in α

In the Mellin–Barnes derivation of C7.1 the error after shifting to `Re u = −M` is
`E_M ≪ |2πζ|^{M} ∫ |Γ(−M+iτ)| · |F(s − M/d + iτ/d, α₀)| dτ ≪ n_{α₀}^{A} (C|ζ|)^{M}`.
Summing over the spectral points in the effective range `α₀ ≲ 1/y`, with `|ζ| ≍ y` and weight
`α₀^{−β}`:
```
Σ_{α₀ ≲ 1/y} α₀^{dA − β} · y^{M}  ≍  y^{M − (dA+1−Re β)} .
```
Since `M` is arbitrary, choosing `M > dA + 1 − Re β + |λ(s)| + δ` makes the total truncation error
`≪ y^{λ(s)+δ}` — strictly smaller than the main term `y^{λ(s)}`. **Item 1 is therefore resolved in
principle: polynomial `α`-growth is harmless because `M` is free.**

### 17.3 Item 2 dissolves: the "non-spike" region is part of the same integral

Between consecutive spectral points, C7.1 gives `Φ_F(s,−α₀+ζ) ≍ |ρ_0(α₀)| |2πζ|^{d Re(s−s*_0)}` with
`|ζ|` running from the spike width `y` up to the local spacing `Δ_{α₀}`. Then
```
∫_y^{Δ} u^{2d Re(s−s*_0)} du   is dominated by the lower endpoint  u = y
```
precisely when `2d Re(s−s*_0) < −1`, i.e. `Re s < 1/2` — the same condition as everywhere else.
So the between-spike region contributes at the **same** order `y^{2dRe(s−s*_0)+1} = y^{λ(s)}` and is
not a separate estimate: the spike integral and the non-spike integral are one computation.

### 17.4 The radius of C7.1 equals the local spectral spacing

The `k`-series of C7.1 cannot converge in a disc of `α₀`-independent radius, because
`Φ_F(s,−α₀+ζ)` is singular at `ζ = α₀ − α₀'` for every other spectral point `α₀'`, and for `d ≥ 2`
the spacing tends to `0`. Hence the constant `C_{F,α₀}` in the remainder bound must grow with `α₀`
so that the radius `≍ 1/C_{F,α₀}` matches the local spacing `Δ_{α₀} ≍ q^{−1}(α₀/d)^{1−d}`.
**Verification at `d = 1`:** for `F = ζ`, `Spec = N`, spacing `1`, and the classical Lerch expansion
`Σ_n n^{−s}e(nζ) = Γ(1−s)(−2πiζ)^{s−1} + Σ_k ζ(s−k)(2πiζ)^k/k!` has radius exactly `1`. ✓
So C7.1 covers each spectral gap exactly, and no more. The analysis is critical — but it is
*exactly* critical, not deficient, and this is the same criticality already recorded in §16.2
(isolation threshold = damping threshold for `d = 2`).

### 17.5 Status of the cycle-10 target

| item | status |
|---|---|
| (1) C7.1 with `α₀`-uniform errors | **resolved in principle** (§17.1–17.2): polynomial in `α`, absorbed by `M` |
| (2) non-spike part `O(y^{λ+δ})` | **dissolved** (§17.3): same integral, same order |
| (3) two-term expansion + Mellin extraction | remaining |

> **Cycle-11 target.** Item (3) for `d = 2`, written out with all constants: assemble
> `K(s,β,y) = A(s)y^{λ(s)}Ξ(β) + B(s)y^{λ(s)+β−1}/(1−β) + O(y^{λ(s)+δ})` from §17.1–17.4, then
> extract `Ξ(β) = Res_{v=−λ(s)}𝒦(s,β,v)/A(s)` and conclude MI for degree 2 — hence Selberg's
> Conjecture A, hence the generalized PNT, for every degree-2 element of `S`.

---

## 18. Cycle 11 (2026-07-25) — the degree-2 assembly, computed

Take `d = 2`, `θ_F = θ_G = 0`, equal conductor `q`, and **`s` real with `s < 1/2`** (legitimate: the
continuation of `R_{F,G}` along a real segment determines it by the identity theorem, and real `s`
kills the phase `e^{−4t·arg(−2πiζ)}` coming from `Im E`).

Constants: `s*_0 = 3/4`, `α_m = 2√(m/q)`, `n_α = qα²/4`, `ρ_0(α_m) = c_F conj(a_F(m)) m^{−1/4}`,
local spacing `Δ_m = α_{m+1} − α_m ≍ 2/(q α_m)`, and the local exponent
```
E(s) = d(s − s*_0) = 2s − 3/2 ,      λ(s) = 2E(s) + 1 = 4s − 2 .
```
Note `2E + 1 < 0 ⟺ s < 1/2` — the convergence condition for the spike integral is **exactly** the
condition `Re s < 1/2` that appeared in §15.1. ✓

### 18.1 The cell integral

With `ζ = (α_m − α) + iy`, over the cell `|α − α_m| < Δ_m/2`:
```
∫ (u² + y²)^{E} du = y^{2E+1} [ B(E) − ∫_{|v|>Δ_m/(2y)} (v²+1)^E dv ] ,
B(E) = √π Γ(−E−1/2)/Γ(−E)  (finite exactly because 2E+1<0),
```
so cell integral `= y^{λ}B(E) + O(Δ_m^{λ})`, and the relative error is `(Δ_m/y)^{λ} ≪ 1` in the
isolated regime `Δ_m ≫ y` — which for `d = 2` holds up to the damping cutoff (§16.2). ✓

### 18.2 The two families, computed

Summing the cells with weight `α_m^{−β}` and `|ρ_0(α_m)|² ≍ C|a_F(m)a_G(m)| α_m^{−1}`, and using the
spectral density `#{α_m ≤ A} ≍ qA²/4`:
```
main       :  C_1(s) · y^{λ} · Ξ(β),           Ξ(β) = Σ_m ρ_0^F(α_m) conj(ρ_0^G(α_m)) α_m^{−β}
                                                     = C · conj(R_{F,G})((1+β)/2)   [d=2]
background :  Σ_m |ρ_0(α_m)|² α_m^{−β} Δ_m^{λ} ≍ ∫_1^{1/y} ⟨|a_F a_G|⟩ α^{−β−2E−1} dα ≍ y^{β+2E}
             = y^{λ + β − 1} .
```
`Ξ(β)` converges iff `Re β > 1`; the background integral diverges at the top iff `Re β < 3 − 4s`, and
is cut off by the damping at `α ≍ 1/y`. Ratio background/main `= y^{β−1}`:
**`Re β > 1` ⟹ background is genuinely smaller; `Re β < 1` ⟹ the roles swap.** This is exactly the
two-term structure predicted in §16.2, now derived rather than guessed.

Including the `ℓ ≥ 1` terms of C7.1 (exponents `E + ℓ`) and the Mellin truncation error (`y^{M}`,
`M` free, §17.2), the full expansion is
```
K(s,β,y)  ~  Σ_{j≥0} c_j(β) y^{λ+j}  +  Σ_{j≥0} e_j(β) y^{λ+β−1+j} ,     c_0(β) = C_1(s) Ξ(β).
```
The two families collide exactly when `β − 1 ∈ Z`, i.e. **`β ∈ Z`**.

### 18.3 The extraction, and what it yields

Fix `v` with `Re v` large: then `𝒦(s,β,v) = ∫_0^∞ K(s,β,y) y^{v−1} dy` converges and is
`β`-holomorphic on `C ∖ {1}` (§12.2). Continue in `v` using §18.2: `𝒦` acquires poles at
`v = −λ−j` (residues `c_j(β)`) and `v = −λ−β+1−j` (residues `e_j(β)`). Away from the collision locus
`β ∈ Z` these are distinct, so
```
Ξ(β) = Res_{v = −λ(s)} 𝒦(s,β,v) / C_1(s)
```
is a residue of a `β`-holomorphic family, hence holomorphic in `β` off `Z`. Therefore
`R_{F,G}((1+β)/2)` is meromorphic in `β` on `C` with poles only in `Z`, i.e.
```
R_{F,G}(w) is meromorphic on C with poles only in  w ∈ 1 + (1/2)Z ,
```
matching the family `1 − j/d` predicted by MI⁺⁺ (§15.2) exactly. Feeding the order at `w = 1` into
cycle-1 Theorem 1 gives **Selberg's Conjecture A for every degree-2 element of `S`**, hence (K–P)
the generalized PNT for all of them.

### 18.4 The one soft spot that remains

The background coefficients `e_j(β)` involve `⟨|a_F a_G|⟩`, i.e. the partial sums of
`|a_F(m)a_G(m)|` up to `m ≍ y^{−2}` — the very quantity the argument computes. This is **not** a
circularity for the extraction (the `e_j` sit at `v`-poles distinct from `v = −λ` whenever `β ∉ Z`),
but it does mean the background family is not known to have a clean power-law form: it could carry
`log(1/y)` factors of unknown order, i.e. the `v`-singularities at `v = −λ−β+1−j` are not known to
be poles of finite order. **What must be proved:** the singularity of `𝒦` at `v = −λ` is isolated,
i.e. the background family contributes nothing at `v = −λ` for `β ∉ Z`. A sufficient statement is
an a-priori upper bound `Σ_{m≤M}|a_F(m)a_G(m)| ≪ M^{1+ε}` — which is immediate from Ramanujan — used
to show the background contributes only to `Re v ≤ −λ−Re β+1+ε`.

> **Cycle-12 target.** Make §18.4 precise: prove that for `β ∉ Z` with `Re β` in a fixed compact
> range, the background family contributes to `𝒦(s,β,·)` only singularities with real part
> `≤ −λ − Re β + 1 + ε`, using only the Ramanujan bound. Then `Res_{v=−λ}𝒦 = C_1 Ξ(β)` is clean and
> the degree-2 case of MI — hence Conjecture A in degree 2 — is a theorem.

---

## 19. Cycle 12 (2026-07-25) — the background is not an obstruction: it is an explicit entire
correction, and the degree-2 argument closes into a limit formula

### 19.1 Identifying the background exactly

The §18.2 "background" is the sum of the *cell-tail* corrections
`−Σ_m ρ_0^F(α_m) conj(ρ_0^G(α_m)) α_m^{−β} ∫_{|v|>Δ_m/(2y)}(v²+1)^E dv`. Evaluating the tail integral
as `≍ (Δ_m/y)^{λ}` and inserting `|ρ_0(α_m)|² ↦ ρ_0^F conj(ρ_0^G) = |c|² a_F(m)conj(a_G(m)) m^{−1/2}`,
`α_m^{−β} ∝ m^{−β/2}`, `Δ_m^{λ} ∝ m^{−λ/2}` gives, with `λ = 4s−2`,
```
background  ≍  −C₂(s) · Σ_m a_F(m) conj(a_G(m)) · m^{−(β+4s−1)/2} · e^{−4πy√m}
            =  −C₂(s) · D_y( (β+4s−1)/2 ) ,
```
where `D_y(w) := Σ_m a_F(m)conj(a_G(m)) m^{−w} e^{−4πy√m}` is **entire in `w` and in `β` for every
`y>0`** (exponential damping). It is *not* a sum of absolute values and *not* an unknown quantity.

**Consistency check.** `D_y(w) ≍ y^{−2(1−w)}` as `y→0` (Mellin: the pole of `R_{F,G}` at `w'=1` sits
at `v = 2(1−w)`), and with `w = (β+4s−1)/2` this is `y^{β+4s−3} = y^{λ+β−1}` — exactly the background
exponent computed in §18.2. ✓ So the "unknown `⟨|a_F a_G|⟩`" of §18.4 was an artefact of taking
absolute values in an error bound; the signed object is explicit.

### 19.2 The limit formula (degree 2)

Assembling §18.1–18.2 with §19.1:
```
K(s,β,y) = C₁(s) · y^{4s−2} · Ξ(β)  −  C₂(s) · D_y((β+4s−1)/2)  +  (corrections),
Ξ(β) = C · conj R_{F,G}((1+β)/2),
```
and therefore
```
conj R_{F,G}((1+β)/2)
   =  lim_{y→0+}  y^{2−4s} · [ K(s,β,y) + C₂(s) D_y((β+4s−1)/2) ] / (C·C₁(s)) .      (★)
```
Both objects in the bracket are, for each `y>0`, **holomorphic in `β` on `C ∖ {1}`**: `K` by §12.2,
`D_y` because it is an exponentially damped Dirichlet series. Hence, if the limit (★) is locally
uniform in `β`, the left-hand side extends holomorphically — which is MI for degree 2.

### 19.3 Which corrections must vanish, and where

The correction families are `y^{λ+j}` (`j ≥ 1`, from the `ℓ ≥ 1` terms of C7.1), `y^{λ+β−1+j}`
(`j ≥ 1`, higher cell-tail corrections), and the Mellin truncation `y^{M}` with `M` free (§17.2).
Relative to the main term `y^{λ}` these are `y^{j}`, `y^{β−1+j}`, `y^{M−λ}`. So:
```
j ≥ 1 first family:   y^{j} → 0            always;
j ≥ 1 second family:  y^{β−1+j} → 0        iff Re β > 1 − j, weakest case j = 1: Re β > 0;
truncation:           free.
```
The `j = 0` member of the second family is exactly the background, which (★) **subtracts
explicitly**. Hence every correction is `o(y^{λ})` precisely on
```
Re β > 0 ,  β ≠ 1  ⟺  Re w > 1/2 ,  w ≠ 1 ,   (w = (1+β)/2).
```

> **Conclusion of the degree-2 line.** Modulo the uniformity of the C7.1 cell expansion summed over
> the spectrum (§17.1–17.3, resolved in principle) and a rigorous derivation of the cell-tail
> identification in §19.1, formula (★) gives:
> **for `F,G ∈ S` of degree 2 with equal conductor, `R_{F,G}` is holomorphic on
> `{Re w > 1/2} ∖ {1}`** — i.e. MI⁺⁺ in degree 2 — and hence, by cycle-1 Theorem 1, **Selberg's
> Conjecture A for every degree-2 element of `S`**, hence the generalized PNT for all of them.
> The half-plane `Re w > 1/2` produced by the argument is exactly the half-plane predicted
> independently in §15.3 from the `ζ(2w)^{−1}` factor of the automorphic model. Two independent
> derivations of the same boundary.

### 19.4 Honest status

- §19.1's identification of the cell-tail sum with `−C₂(s)D_y((β+4s−1)/2)` was obtained by matching
  the tail integral `∫_{|v|>Δ/(2y)}(v²+1)^E dv ≍ (Δ/y)^{λ}` and re-summing; the constant `C₂(s)` and
  the sub-leading structure of that matching are **not yet computed rigorously**. This is the one
  step of the degree-2 chain that is still heuristic.
- Everything else in the chain is either proved (§12.2, C6.1, C7.1, §17.1–17.3, §18.1–18.2) or
  reduced to K–P's published theorems.

> **Cycle-13 target.** Compute the cell-tail sum rigorously: expand
> `∫_{|v|>X}(v²+1)^E dv = Σ_{i≥0} b_i(E) X^{λ−2i}` for `X = Δ_m/(2y) → ∞`, insert `Δ_m` exactly
> (not just `≍`), and verify that the `i = 0` term re-sums to `C₂(s) D_y((β+4s−1)/2)` with an
> explicit `C₂(s)`, the `i ≥ 1` terms giving the `j ≥ 1` second family. This is elementary but must
> be done with the exact spectral spacing `Δ_m = 2q^{−1/2}((m+1)^{1/2} − m^{1/2})`, not its
> asymptotic.

---

## 20. Cycle 13 (2026-07-25) — the exact computation KILLS the degree-2 line. Phase-4 verdict: CIRCULAR

### 20.1 The exact cell-tail expansion

With `u = α − α_m`, cell `(−a_m, b_m)`, `a_m = Δ_{m−1}/2`, `b_m = Δ_m/2`:
```
∫_{−a}^{b}(u²+y²)^E du = y^{λ}B(E) − y^{λ}[∫_{−∞}^{−a/y} + ∫_{b/y}^{∞}](v²+1)^E dv ,
∫_X^∞ (v²+1)^E dv = Σ_{i≥0} binom(E,i) X^{λ−2i}/(2i−λ)   (X > 1).
```
So the cell integral is `y^{λ}B(E) + Σ_{i≥0} binom(E,i)(a^{λ−2i}+b^{λ−2i}) y^{2i}/(λ−2i)`.
The `i = 0` term is **`y`-independent**, and re-summing it over the spectrum against
`ρ_0^F conj(ρ_0^G)α_m^{−β}` and the damping `e^{−4πy√m}` gives exactly
`C₂(s)·D_y((1+β+λ)/2) = C₂(s)·D_y((β+4s−1)/2)` — **confirming §19.1 rigorously**, with `C₂(s)`
explicit. ✓

### 20.2 …but the `i`-family does not decay

Using `D_y(w) ≍ y^{−2(1−w)}`, the `i`-th term contributes
`y^{2i}·y^{β+λ−1−2i} = y^{β+λ−1}` — **the same order for every `i`**. So the `i`-expansion is not an
asymptotic expansion in `y`: the whole tail sits at one order, `y^{λ+β−1}`. Its relative size is
`(y/Δ_m)^{2}` per step, i.e. `≍ y² m`, which is `≪1` only for `m ≪ y^{−2}` — and `m ≍ y^{−2}` is
exactly where the damping `e^{−4πy√m}` is of size `e^{−4π}`, i.e. **a constant, not negligible**.

### 20.3 The transition region contributes at the background order

At `m ≍ y^{−2}` the cells have size `≍ y`, the spikes merge, and the expansion breaks. Bounding that
region with Ramanujan only (`Σ_{m≤M}|a_F a_G(m)| ≪ M^{1+ε}`):
```
transition ≍ y^{λ} · Σ_{m≍y^{−2}} |a_F a_G(m)| m^{−(1+β)/2} e^{−4πy√m} ≪ y^{λ}·y^{1+β}·y^{−2−ε}
           = y^{λ+β−1−ε} .
```
This is the **same order as the background**, not smaller. So the transition region is part of the
background, and only an *upper bound* is available for it — no asymptotic.

### 20.4 Verdict: `CIRCULAR`

Consequently the corrections in the limit formula (★) of §19.2 are `o(y^{λ})` only for
`Re β > 1 + ε`, i.e. `Re w > 1 + ε/2` — **where `R_{F,G}` already converges**. Formula (★) therefore
reproduces `R_{F,G}` where it is already defined and does not continue it.

Trying to remove the transition region by replacing the `y`-damping with a free smooth cutoff at
`m ≤ N` (choosing `y ≪ N^{−1/2}` so that every spike with `m ≤ N` is isolated) does not help: the
main term then becomes the **truncated** sum `Ξ_N(β) = Σ_{m≤N} a_F(m)conj(a_G(m)) m^{−(1+β)/2}`, and
letting `N → ∞` for `Re β < 1` requires precisely the asymptotics of the partial sums of
`a_F conj(a_G)` — the Rankin–Selberg problem itself.

> **Third structural obstruction (own, joining §9.1 and §10.1).**
> **No construction that reads `R_{F,G}` off truncated spectral data of the standard twist can
> cross the abscissa `Re w = 1`.** The spectral-spike sum *is* a partial sum of `R_{F,G}`; its
> `y → 0` (or `N → ∞`) behaviour is exactly what the continuation of `R_{F,G}` encodes. Any such
> construction yields an identity, never a continuation.

**This kills the cycle-5–12 line as a route to MI.** Recorded so no later cycle re-attempts it.

### 20.5 What survives (positive residue — all still valid)

- **§12.2** — the regularised pairing: `K(s,β,y)` is `β`-meromorphic on `C` with a single simple
  pole at `β = 1` and `Res_{β=1}K = D_y(2s)`. A theorem; an exact identity; unaffected.
- **C6.1** — cusp expansion of `Φ_F` at `z = 0` with radius exactly `min Spec(F) = d q^{−1/d}`.
  A theorem; independently interesting (it identifies the spectrum as the natural boundary of the
  shift-lattice expansion), and verified against the Lerch/Hurwitz case.
- **C7.1** — the Lerch-type expansion of `Φ_F` at every spectral point, with local exponents
  `d(s − s*_ℓ)`; verified to reduce to the classical Lerch expansion for `F = ζ`, `d = 1`.
- **§16.2** — the trichotomy `d = 1 / d = 2 / d ≥ 3` for spectral accumulation, and §17.1–17.2
  (K–P's Theorem 1 constant is polynomial in `α`; the Mellin truncation absorbs it).
- **MI, MI⁺⁺** — unaffected as conjectures; §15.1 and §19.3 remain two independent derivations of
  the boundary `Re w = 1/2`.
- **Cycle-1 Theorems 1, 2, 4 and Corollary 3** — unaffected: they are implications *from* MI.

### 20.6 Cycle-14 direction

The three recorded obstructions now say the same thing from three angles:
§9.1 (no separately-linear construction gives the functional equation), §10.1 (the axioms deliver
only linear prime moments), §20.4 (no truncated-spectral construction crosses the abscissa).
Every route that builds `R_{F,G}` *out of* `F` and `G` by analysis of their twists is blocked.
**The next cycle must therefore change the input, not the technique**: look for a source of
quadratic information that is not a construction out of `F` and `G` — e.g. a positivity/extremal
principle, an operator-theoretic realisation, or an arithmetic input (Chebotarev-type) that supplies
`|a_F(p)|²` directly. Restart at Phase 1 with that constraint explicit.

---

## 21. Cycle 14 (2026-07-25) — Phase-1 restart under the three obstructions

Constraint carried in from §20.6: **the new input may not be a construction of `R_{F,G}` out of `F`
and `G`.** Every such route is blocked by §9.1 (degrees multiply, separately-linear maps add),
§10.1 (the axioms deliver only linear prime moments) and §20.4 (truncated spectral data cannot cross
the abscissa).

### 21.1 By-product of C6.1: why linear twists work only in degree 1  [OWN]

Apply the Mellin–Barnes argument of C6.1 to the **degree-1** theta `Σ_n a_F(n) e(nz)` of an element
of degree `d`. The shift lattice is now `F(s−k)` (spacing 1) instead of `F(s−k/d)` (spacing `1/d`),
and the same Stirling bookkeeping gives `k`-th term `≍ (dk)^{dk}e^{-dk}/k!·|2πz|^k ≍
(d^{d}k^{d−1}|2πz|)^{k}`. So
```
radius of convergence  =  positive for d = 1,   ZERO for d ≥ 2 .
```
This is exactly the reason the Dirichlet-character twist `F^χ = (1/τ(\barχ))Σ_a \barχ(a) F(s,a/q)`
is available in degree 1 and open for `d ≥ 2` (§9.3): the linear twist expands on a lattice of
spacing 1, while a degree-`d` functional equation only supports spacing `1/d`. Recorded because it
gives a *quantitative* reason (radius `0`), not merely "K–P's theorem does not apply".

### 21.2 The candidate new inputs, ranked

Sources of quadratic information that are **not** constructions out of `F` and `G`:

1. **(FIN) Finiteness.** For all `D,Q`, the set `{F ∈ S : d_F ≤ D, q_F ≤ Q}` modulo vertical shifts
   is finite. *Status:* known for degree 1 (K–P classification) and for degree 2 with conductor 1
   (K–P 2022); **open in general.** Bold, falsifiable, and about `S` as a whole rather than about a
   pair.
2. **(LS) A large sieve for Selberg-class families.** For a finite `𝔉 ⊂ S` with bounded invariants,
   `Σ_{F∈𝔉}|Σ_{n≤N} c_n a_F(n)|² ≪ (|𝔉| + N)(log)^{A} Σ|c_n|²`. This is orthogonality **on average**
   over a family, the standard tool in the automorphic setting (Duke–Kowalski; Iwaniec–Kowalski
   ch. 7; arXiv:2508.14888 *Large sieves for GL_n and applications*, 2025). It needs FIN even to be
   stated. It is genuinely new input: it produces quadratic information from a *family*, not from a
   pair, so §9.1/§10.1/§20.4 do not apply to it.
3. **Positivity / extremal principles.** Weil-type explicit-formula positivity gives inequalities
   for quadratic forms in the *test function*, not in `F` — checked, does not supply `|a_F(p)|²`.
   Recorded as not viable.
4. **GRH as input.** Under GRH one gets `log F(1/2+it) ≪ log t/loglog t`, so the second moment of
   `log F` is `≪ (log t/loglog t)²` — **worse** than the target `loglog t`. GRH does not imply EB by
   this route. Recorded as not viable.

### 21.3 What FIN + LS would give

LS with `c_n` supported on primes and `|𝔉|` of the size predicted by FIN yields
`Σ_{F ∈ 𝔉} |Σ_{p≤N} c_p a_F(p)|² ≪ (|𝔉| + N)(log)^A Σ_p |c_p|²`. Taking `c_p = conj(a_G(p))/p` for a
fixed `G ∈ 𝔉` and isolating the `F = G` term gives an upper bound for
`Σ_{F ≠ G} |Σ_{p≤N} a_F(p)conj(a_G(p))/p|²` — i.e. **orthogonality for all but `O(1)` members of the
family**, which is a genuine partial form of Conjecture B, obtained without ever constructing
`R_{F,G}`. It does not give a *named* pair, but combined with the integrality of the Gram matrix
under MI (Corollary 3, cycle 1) it would force the exceptional set to be empty whenever the family
is complete.

> **Cycle-15 target.** Attack **FIN** directly. It is the gateway: without it LS cannot even be
> stated. Concretely: is `{F ∈ S : d_F ≤ D, q_F ≤ Q}/(vertical shifts)` finite? Note that the
> analogous statement in the **extended** class `S^♯` is FALSE in general (linear combinations), so
> any proof must use the Euler product and Ramanujan axioms essentially — the two axioms that
> §20.5's surviving results have so far used least.

---

## 22. Cycle 15 (2026-07-25) — FIN as stated is FALSE; the equivalence web

### 22.1 Phase-4 kill of §21.2(1)

> **FIN (as stated) is FALSE.** Maass forms of level 1 have degree 2 and conductor 1, and there are
> infinitely many of them (Laplace eigenvalues `1/4 + r²`, `r → ∞`), with distinct `L`-functions.
> Their `L`-functions lie in `S` as soon as Ramanujan holds for them, and in any case in `S^♯`.
> Bounding `(d_F, q_F)` alone therefore does **not** give a finite set.

**Corrected statement.** `FIN′`: for all `D, Q, M`, the set
`{F ∈ S : d_F ≤ D, q_F ≤ Q, max_j |μ_j| ≤ M}` — i.e. bounded **analytic** conductor — is finite.
(Bounding `Im μ_j` also bounds the vertical shift, so no quotient is needed.)

**But `FIN′` is not new input.** Finiteness of a set of elements with bounded analytic conductor is
exactly a *discreteness* statement: two distinct elements must differ by a definite amount in the
prime-side metric. That is `(P2)` (quantitative strong multiplicity one), which §9.6 showed is
blocked by the convergence obstruction (`Σ_p|c(p)|²/p < ∞` gives absolute convergence of
`Σ_p c(p)p^{−σ}` only for `σ>1`, so the explicit-formula method never starts).
**So `FIN′ ⟸ (P2)` and the proposed "new input" of cycle 14 collapses onto an old hard core.**
`LS` (§21.2(2)) cannot even be stated without `FIN′`. Recorded; do not re-attempt.

### 22.2 The equivalence web (consolidated state of the problem)

All routes examined in 15 cycles terminate in one of four hard cores, and the arrows between them
are now mapped (own contributions marked ★):

```
        (iv) AUTOMORPHY of S  ──────────────────────────► SOC          [Jiang 2025, arXiv:2507.20653]
              │                                            ▲
              ├──► (iii) TWIST: F^χ ∈ S^♯ ──► PEP ──► BS ★──► EB ★     [K–P 2023; BS/EB named §2.4, §9.5]
              │            ▲                                ▲
              │            └── blocked: C6.1 gives radius 0 for the
              │                degree-1 shift lattice when d ≥ 2 ★     [§21.1]
              │
              └──► (i) MI ★ ──► Conjecture A ★ ──► GPNT               [Thm 1, cycle 1; K–P for GPNT]
                        │
                        └── + (P1) + (P2) ──► SOC ★                    [Cor 3, cycle 1]

        (ii) (P2) quantitative SMO ──► FIN′ ──► (LS large sieve) ──► SOC on average ★
```

Three structural obstructions block every attempt to *construct* the missing quadratic object:
`§9.1` (degrees multiply, separately-linear maps add), `§10.1` (the axioms deliver only linear prime
moments), `§20.4` (truncated spectral data cannot cross the abscissa). Two convergence obstructions
block the two "cheap" routes: `§9.6` (the `ℓ²` hypothesis of (P2) gives absolute convergence only
for `σ>1`) and `§21.1` (radius `0` for the linear twist when `d ≥ 2`).

### 22.3 Net theorems produced in cycles 1–15 (all still standing)

Paper, dependency-closed as stated:
- **Thm 1** MI ⟹ Selberg's Conjecture A, with `n_F = −ord_{w=1}R_{F,F} ∈ Z_{≥0}` (Landau + Wiener–Ikehara).
- **Thm 2** MI ⟹ `B(F,G) = κ_{F,G} ∈ Z` — including the imaginary part, which Conjecture A alone
  cannot reach.
- **Cor 3** B ⟸ MI + (P1) + (P2), isolating the only two remaining ingredients.
- **Thm 4** Conjecture A is not a consequence of Selberg axioms (1),(4),(5) — explicit witness
  `exp(Σ_p (log p)^{10}p^{−s})`.
- **§12.2** the regularised pairing `K(s,β,y)`: `β`-meromorphic on `C` with a single simple pole at
  `β=1`, `Res_{β=1}K = D_y(2s)`.
- **C6.1** cusp expansion of `Φ_F` at `z=0`, radius exactly `min Spec(F) = d q^{−1/d}`; recovers
  the Lerch expansion at `d=1`, and gives radius `0` for the degree-1 shift lattice when `d ≥ 2`.
- **C7.1** Lerch-type expansion of `Φ_F` at every spectral point, local exponents `d(s−s*_ℓ)`;
  reduces to the classical Lerch expansion for `F = ζ`.
- **Lemma A′** the standard-twist family jumps by `≥ |ρ_0(α₀)|/r` at every spectral point.
- **§16.2** the `d = 1 / d = 2 / d ≥ 3` trichotomy for spectral accumulation.

Lean, `lake build` green, axioms `[propext, Classical.choice, Quot.sound]`:
`RHTower.SelbergPairingPrimeSquare` — `divisorsAntidiagonal_prime_sq`,
`arithmeticFunction_mul_apply_prime_sq`, `arithmeticFunction_mul_apply_prime'`,
`selberg_pairing_prime_sq`, `selberg_pairing_sum_eq`, `selberg_energy_polarization`,
`selberg_pairing_cauchy_schwarz`, `int_eq_zero_or_one_or_neg_one_of_sq_le_one`;
`HTGeometry.GeneralizedDirichletMeanValue` — `genPoly`, `oscInt`, `oscInt_zero`,
`genPoly_mul_conj`, `genPoly_meanValue`.

### 22.4 Cycle-16 direction

The web says: attack `(i) MI` or `(ii) (P2)`, and every *construction* route into MI is closed.
What is NOT closed is a **non-constructive** route: proving `R_{F,G}` is meromorphic at `w=1` by an
indirect argument (a dichotomy, a compactness/normal-families argument on the set of possible
singularity types, or an integrality-forcing argument) rather than by exhibiting the continuation.
That is the one shape of argument the three obstructions do not touch, because they all forbid
*building* the continuation, not *proving it exists*.

---

## 23. Cycle 16 (2026-07-25) — C6.1 sharpened to a two-sided theorem

Non-constructive routes to MI were surveyed (dichotomy on the singularity type; Bochner/positive-
definiteness of `μ(θ) = B(F,F_θ)`; moment/Sato–Tate forcing; multiplicativity `n_{F^k} = k² n_F`).
All were checked and none yields integrality:
- `μ` positive-definite with `Re μ ∈ (1/2)Z`, `Re μ = 0` a.e., `μ(0) = n_F`: the period group
  `G = {θ : μ(θ) = μ(0)}` is a closed null subgroup, hence `{0}` or `aZ`; both are consistent with
  Conjecture A. **No contradiction, no proof.** Recorded as checked.
- `n_{F^k} = k² n_F` gives nothing (`k=1` already forces the conclusion it would need).
- Moment/Sato–Tate forcing is circular (higher moments are coefficients of hypothetical lifts).

The cycle's positive output is a sharpening of C6.1 into a two-sided statement.

### 23.1 Theorem C6.1′ (sharp cusp radius)  [OWN, PROVED HERE]

> Let `F ∈ S^♯` have degree `d ≥ 1` and conductor `q`, and let
> `T_F(s,z) := Σ_{k≥0} ((2πiz)^k/k!) · F(s − k/d)`.
> Then for every `s ∈ C` the radius of convergence of `T_F(s,·)` is **exactly**
> ```
> R(F) = d · q^{−1/d} = min Spec(F) ,
> ```
> and `Φ_F(s,z) = P_F(s,z) + T_F(s,z)` on `|z| < R(F)`, where `P_F` is the explicit polar
> contribution of `F` at `s' = 1` (singular only at `z = 0`).

*Proof.* **Lower bound (`≥`), from the archimedean data.** By the functional equation
`F(s) = X(s)\bar F(1−s)` with `|\bar F(1−s)| → 1` as `σ → −∞` (absolute convergence and `F(w) → 1`
as `Re w → ∞`), and
`|X(σ+it)| = Q^{1−2σ}∏_j |Γ(λ_j(1−s)+\barμ_j)| / |Γ(λ_j s + μ_j)|`.
Uniform Stirling on both `Γ`-products, with `Σ_j 2λ_j = d` and
`q = (2π)^d Q² ∏_j λ_j^{2λ_j}`, gives for `σ → −∞` with `t` fixed
```
|X(σ+it)| ≍ C · [ q/(2π)^d ]^{|σ|} · |σ|^{d|σ|} e^{−d|σ|} .
```
Setting `|σ| = k/d + O(1)` and using `k! ≍ √(2πk)(k/e)^k`,
```
| F(s − k/d) / k! |^{1/k}  →  q^{1/d} / (2π d) ,
```
so the `k`-th term of `T_F(s,z)` is `≍ (|z| q^{1/d}/d)^k` and the series converges for
`|z| < d q^{−1/d}`. (The trivial zeros of `F` at the poles of `γ` only make some terms smaller; the
statement is about `limsup`, which is attained along the `k` avoiding them.)

**Upper bound (`≤`), from the coefficients.** `Φ_F(s,·)` is singular at `z = −α` for every
`α ∈ Spec(F)` — by Lemma A′ (§11.1), the twist family jumps by `≥ |ρ_0(α)|/r > 0` there — while
`P_F(s,·)` is singular only at `z = 0`. Hence `T_F = Φ_F − P_F` is singular at `z = −α_min`, so its
radius is at most `α_min`. Since `a_F(1) = 1`, `α_min = min Spec(F) = d(1/q)^{1/d}`. ∎

### 23.2 Why this is worth stating separately

The two bounds come from **disjoint data**: the lower bound uses only `(d, q, λ_j, μ_j)` — the
archimedean/functional-equation side — and the upper bound uses only `a_F(1) = 1` and the location
of the first prime-side singularity. Their coincidence is a **local–global identity for the Selberg
class**:
```
the archimedean invariants (d, q) compute the position of the first prime-side singularity of the
degree-d theta function, and conversely.
```
Verifications: `ζ` (`d=1,q=1`) → `R = 1`, and `Σ_n n^{−s}e(nz)` (Lerch) is singular exactly at
`z ∈ Z` ✓. `L(·,χ)` mod `q` (`d=1`) → `R = 1/q`, and the singularities sit at `z ∈ (1/q)Z` ✓.
Degree-`d` case: `R = d q^{−1/d}` is precisely `min Spec` from K–P's `Spec(F) = {d(m/q)^{1/d}}` ✓.

Corollary (already used in §21.1): for the **degree-1** shift lattice `Σ_k ((2πiz)^k/k!)F(s−k)` the
same computation gives `k`-th term `≍ (d^d k^{d−1}|2πz|)^k`, hence radius `0` when `d ≥ 2` — the
quantitative reason the Dirichlet-character twist is available only in degree 1.

### 23.3 Cycle-17 direction

C6.1′ is the cleanest standalone result of the programme and is independent of MI. Next: check its
novelty against the literature (K–P's twist papers, the Lerch/Hurwitz literature, and converse-theorem
work), and see whether the local–global identity it expresses can be **inverted** — i.e. whether
knowing the radius of the shift-lattice expansion pins the conductor, giving a new handle on the
conductor from prime-side data. That would be a genuinely new direction, and it uses only surviving
(unblocked) machinery.

---

## 24. Cycle 17 (2026-07-25) — the Cusp–Spectrum Radius Law (C6.1′ and C17 unified)

### 24.1 Novelty check on C6.1′

Searched: K–P's twist papers (arXiv:1911.10497, 1304.4734, 1507.07177, 2303.02417/20), the degree-2
conductor-1 classification (arXiv:2009.12329, 2503.02492), the Annals paper on `1<d<2`, and the
Selberg-class surveys (Dixit; Zheng; Perelli). No statement of the form "the radius of the
shift-lattice expansion equals `d q^{−1/d} = min Spec(F)`" appears. Both ingredients
(Mellin–Barnes; uniform Stirling on the functional equation) are standard, so the *combination*
is the new item; it could be folklore among specialists. Recorded honestly as **plausibly new,
not certainly new.**

### 24.2 Theorem (Cusp–Spectrum Radius Law)  [OWN, PROVED HERE]

For `F ∈ S^♯` of degree `d ≥ 1` write `F_{α}(w) := F(w,α)` for the K–P standard twist
(`F_0 = F`), and for a base point `α₀ ≥ 0` put
```
Δ(α₀) := dist( α₀ , Spec(F) \ {α₀} )      (so Δ(0) = min Spec(F)).
```

> **Theorem.** For every `s ∈ C` off the exceptional lattice `{s*_ℓ + k/d}`,
> ```
> limsup_{k→∞} | F_{α₀}(s − k/d) / k! |^{1/k}  =  1 / ( 2π · Δ(α₀) ) .
> ```
> Equivalently: after subtracting the explicit singular part (the `P_F` of C6.1 when `α₀ = 0`, the
> `ℓ`-sum of C7.1 when `α₀ ∈ Spec(F)`), the shift-lattice expansion
> `Σ_k ((2πiζ)^k/k!) F_{α₀}(s − k/d)` of `Φ_F(s, −α₀+ζ)` has radius of convergence **exactly**
> `Δ(α₀)`.

*Proof.* By C6.1/C7.1 the difference `T_{α₀}(s,ζ) := Φ_F(s,−α₀+ζ) − (singular part at α₀)` is given
by that power series, and the singular part is singular only at `ζ = 0`. `Φ_F(s,·)` is holomorphic
on `H` and, by K–P, continues across every boundary point `−α` with `α ∉ Spec(F)` (there `F(s,α)` is
entire), while by Lemma A′ (§11.1) it is genuinely singular at `−α` for every `α ∈ Spec(F)`, since
`ρ_0(α) ≠ 0`. Hence the nearest singularity of `T_{α₀}(s,·)` is at distance `Δ(α₀)`, and Hadamard's
formula for the radius of a power series gives the displayed `limsup`. ∎

### 24.3 What it says

- **At the cusp `α₀ = 0`:** `Δ(0) = min Spec(F) = d q^{−1/d}` (because `a_F(1) = 1`), so the theorem
  reads `limsup_k |F(s−k/d)/k!|^{1/k} = q^{1/d}/(2πd)`. The left side is computed purely from the
  **archimedean** data by uniform Stirling on the functional equation (§23.1), the right side purely
  from the **conductor**. A local–global identity. Checks: `ζ` → radius 1, Lerch singular exactly on
  `Z` ✓; `L(·,χ)` mod `q` → radius `1/q`, singularities on `(1/q)Z` ✓.
- **At a spectral point:** `Δ(α_m) ≍ q^{−1}(α_m/d)^{1−d}` → `0` for `d ≥ 2`. So
  ```
  limsup_k |F(s−k/d, α_m)/k!|^{1/k}  ≍  q (α_m/d)^{d−1} / 2π  →  ∞ .
  ```
  **The far-left growth of the standard twist blows up as `α` runs through the spectrum, at a rate
  equal to the reciprocal of the local spectral spacing.** This is a *lower* bound on the growth of
  `F(s,α)` as `σ → −∞`, complementary to K–P's upper bounds, and it shows those bounds *must*
  degrade in `α` — quantifying their remark that "the known bounds are weak in general".
- **Degree-1 shift lattice:** the same argument with spacing `1` instead of `1/d` gives radius `0`
  for `d ≥ 2` (§21.1), the quantitative reason Dirichlet-character twists are unavailable there.

### 24.4 Status

The Cusp–Spectrum Radius Law is **independent of MI and of Selberg's conjectures**: it is a theorem
about the analytic geometry of the standard twist. It is the cleanest standalone output of the
programme so far. It does **not** advance Conjecture B — the three structural obstructions of §22.2
are untouched by it — but it is new knowledge about `S`, and it supplies the sharp `α`-dependence
that any future spike-type analysis would need (and which §20.4 showed is not by itself enough).

> **Cycle-18 direction.** Two options, both unblocked: (a) write the Radius Law up as a standalone
> result with full constants and check it against the degree-2 conductor-1 classification, where
> `Spec` is explicitly known; (b) return to the equivalence web (§22.2) and attack `(iii)` the twist
> conjecture, now that §21.1/§24.3 give the exact obstruction to it (radius `0` on the spacing-1
> lattice) — i.e. look for a *different* lattice, of spacing `1/d`, that still detects Dirichlet
> characters.

---

## 25. Cycle 18 (2026-07-25) — the Radius Law verified with explicit constants on degree 2, conductor 1

K–P's classification says the degree-2, conductor-1 elements of `S^♯` (normalised `θ_F = 0`) are
shifts of `L`-functions of level-1 Hecke or Maass eigenforms. Both families are checked against the
Cusp–Spectrum Radius Law **independently of its proof**, by computing the left-hand `limsup`
directly from the functional equation.

**Holomorphic case (`f = Δ`, weight 12).** `Λ(s) = (2π)^{−s}Γ(s+11/2)L(s,Δ) = Λ(1−s)`, so
`Q = (2π)^{−1}`, `λ_1 = 1`, `μ_1 = 11/2`; hence `d = 2λ_1 = 2` and
`q = (2π)^d Q² ∏λ_j^{2λ_j} = (2π)²(2π)^{−2}·1 = 1` ✓.
`X(s) = γ(1−s)/γ(s) = (2π)^{2s−1} Γ(13/2−s)/Γ(s+11/2)`. At `s = −k/2 → −∞`, using
`|1/Γ(11/2−k/2)| ≈ Γ(k/2−9/2)/π`,
```
|F(−k/2)| ≍ |X(−k/2)| ≍ (2π)^{−k} (k/2)^{k} e^{−k} ,      k! ≍ (k/e)^k ,
⟹ |F(−k/2)/k!|^{1/k} → (2π)^{−1}·(1/2)·e^{−1}·e = 1/(4π) .
```
The Law predicts `q^{1/d}/(2πd) = 1/(4π)` ✓ and radius `= 2 = d q^{−1/d} = min Spec(F)` ✓
(`Spec = {2√m}`, minimum `2` since `a_F(1)=1`).

**Maass case (level 1, spectral parameter `r`).** `γ(s) = π^{−s}Γ((s+ir)/2)Γ((s−ir)/2)`, so
`Q = π^{−1}`, `λ_1 = λ_2 = 1/2`, `μ_{1,2} = ±ir/2`; `d = 2` and
`q = (2π)²π^{−2}·((1/2)^{1})² = 4·(1/4) = 1` ✓. The Law again gives `1/(4π)` and radius `2`,
**independently of `r`** — as it must, since it depends only on `(d,q)`. ✓

Both checks are with explicit constants and come out exact. Together with the `d=1` checks
(`ζ` → radius 1, Lerch singular exactly on `Z`; `L(·,χ)` mod `q` → radius `1/q`, singularities on
`(1/q)Z`), the Cusp–Spectrum Radius Law is now verified on every family of `S` for which the
spectrum is explicitly known.

> **Cycle-19 note on the twist route (§24.4(b)).** Detecting Dirichlet characters requires additive
> characters in `n`; the standard twist supplies additive characters in `n^{1/d}`. Matching them
> would need `α n^{1/d} ≈ n a/q`, i.e. `α ∝ n^{1−1/d}` — not a constant. **The two twist structures
> are genuinely incompatible for `d ≥ 2`**, which is the structural content behind the radius-0
> computation of §21.1. Where the linear twist *does* continue in degree 2 it is because the gamma
> factor is of Hecke type (a single `Γ(s+μ)`, `λ = 1`), so Hecke's correspondence makes
> `Σ a_F(n)e(nz)` modular; the `Γ_R Γ_R` (Maass) shape is exactly the case Hecke does not reach, and
> is why K–P's degree-2 work is hard. Recorded: option (b) of §24.4 collapses onto converse theorems.

---

## 26. Cycle 19 (2026-07-25) — the Radius Law detects lacunarity; a Serre-type conjecture for `S`

### 26.1 Observation

`Δ(α₀)` is the gap between consecutive points of `Spec(F) = {d(m/q)^{1/d} : a_F(m) ≠ 0}`, so it is
sensitive to the **support** of `a_F`, not just to `(d,q)`:
- at the cusp, `Δ(0) = min Spec` uses only `a_F(1) = 1`, so the cusp radius `d q^{−1/d}` is
  support-independent (verified in §25 on four families);
- at a spectral point, `Δ(α_m)` is the gap to the next `m'` with `a_F(m') ≠ 0`. For a **CM** modular
  form the support has density `0` (`≍ x/√log x`), so `Δ(α_m) ≍ √(log m) ×` (generic spacing).

Hence, by the Cusp–Spectrum Radius Law, **the far-left growth constant of the standard twist detects
lacunarity of the coefficients**: `limsup_k |F_{α_m}(s−k/d)/k!|^{1/k} = 1/(2πΔ(α_m))` is smaller by
the lacunarity factor. This is a genuinely new use of the twist: an analytic invariant reading off
the *support* of `a_F`.

### 26.2 Conjecture (Serre lacunarity for the Selberg class)

> A primitive `F ∈ S` has coefficient support of density `0` **iff** `F` is of CM type — i.e. `F`
> is the automorphic induction of a degree-1 element from an imaginary quadratic field.

This abstracts Serre's lacunarity theorem for modular forms to `S`. It is exact, falsifiable, and
independently meaningful: it would classify the elements of `S` for which the twist-growth constants
are subgeneric. **[OPEN CORE]** the classical proof runs through Rankin–Selberg / Sato–Tate, so this
conjecture inherits the same hard core as the rest of the programme; it is recorded as a *structural*
target, not as a route to Conjecture B.

### 26.3 A bound attempt that fails (recorded so it is not retried)

Comparing the singular and regular parts of C7.1 at the edge `|ζ| ≍ Δ(α₀)` gives
`|ρ_0(α₀)| ≲ Δ^{−E−d(1−σ)} = Δ^{(1−d)/2}`, and with `Δ(α_m) ≍ m^{(1−d)/d)}`,
`|ρ_0(α_m)| = c|a_F(m)|m^{(1−d)/(2d)}` this yields only `|a_F(m)| ≲ m^{(d−1)/2}` —
far weaker than the Ramanujan axiom. **Dead end.**

### 26.4 Standing deliverables

`docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md` now carries the Radius Law as a
standalone paper-proved theorem with its four verifications, consequences, and novelty assessment.
The Selberg-orthogonality programme itself remains at the state mapped in §22.2: four hard cores
(automorphy / twist / MI / (P2)), three structural obstructions forbidding any *construction* of the
quadratic object, and two convergence obstructions closing the cheap routes.

---

## 27. Cycle 20 (2026-07-25) — Lemma A′ certified in Lean

`formal/GaloisForLFunctions/HTGeometry/ResidueJumpLowerBound.lean` (registered in the `HTGeometry`
umbrella; `lake build` green; `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

- `HTGeometry.residue_jump_bound` — if `∮_{C(c,r)} h = 2πi·ρ` and `‖h‖ ≤ C` on the circle, then
  `‖ρ‖/r ≤ C`;
- `HTGeometry.residue_jump_of_integral_eq_zero` — if `∮ f = 0`, `∮ g = 2πi·ρ`, and
  `‖g − f‖ ≤ C` on the circle, then `‖ρ‖/r ≤ C`.

This is exactly Lemma A′ (§11.1) in abstract form: a family of functions with vanishing contour
integral cannot approximate, uniformly on the circle, a member with non-zero residue. Applied to
the standard twist — `g = F(·,α₀)` with `α₀ ∈ Spec(F)` (residue `ρ_0(α₀) ≠ 0` by K–P) and
`f = F(·,α)` with `α ∉ Spec(F)` (entire, so the integral vanishes) — it is the obstruction to
continuity of the twist family at its spectrum, and it is the ingredient that makes the upper bound
in the Cusp–Spectrum Radius Law (§24.2, step 2) work.

Lean inventory of the programme is now:
- `RHTower.SelbergPairingPrimeSquare` — 8 theorems (prime-square pairing identity, energy
  polarisation, Cauchy–Schwarz, integrality trichotomy);
- `HTGeometry.GeneralizedDirichletMeanValue` — exact mean value of a generalized Dirichlet
  polynomial with arbitrary real frequencies;
- `HTGeometry.ResidueJumpLowerBound` — the residue-jump obstruction.
All unconditional, all `#print axioms` clean.

---

## 28. Cycle 21 (2026-07-25) — the diagonal as a frequency class, and why it is not spectrally isolated

### 28.1 A cleaner description of the Rankin–Selberg coefficients  [OWN]

Let `\bar G(s',z) := Σ_n conj(a_G(n)) n^{−s'} e(z n^{1/d})` — **holomorphic** on `H` (unlike
`conj Φ_G(\bar s, \bar z)`, which is antiholomorphic). Then
```
H(s,s',z) := Φ_F(s,z) · \bar G(s',z) = Σ_{m,n} a_F(m) conj(a_G(n)) m^{−s} n^{−s'} e( z (m^{1/d}+n^{1/d}) )
```
is a holomorphic almost-periodic function on `H` with frequency set `{m^{1/d}+n^{1/d}}`, and the
**diagonal `m = n` is exactly the frequency class `2Λ_d`, `Λ_d = {n^{1/d}}`**, carrying the
coefficients `a_F(n) conj(a_G(n)) n^{−s−s'}` — the Rankin–Selberg data.

> So: `R_{F,G}` is the `2Λ_d`-frequency part of a single **holomorphic** function built from `F`
> and `G`. This is a cleaner statement of the target than the `α`-average of cycle 5, and it makes
> the question sharp: *is the frequency class `2Λ_d` separated from the rest of the frequency set?*

### 28.2 It is not. Quantitative form of the obstruction  [OWN]

Write `m = k+h`, `n = k−h`. Then
```
(k+h)^{1/d} + (k−h)^{1/d} − 2k^{1/d}  ≍  (1/d)(1/d − 1) h² k^{1/d − 2} ,
```
so an off-diagonal frequency sits at distance `≍ h² k^{1/d−2}` from the diagonal frequency
`2k^{1/d}`. For `h = 1` this is `k^{1/d−2} → 0` for every `d ≥ 1`.

> **The diagonal frequency class is never spectrally isolated.** A smooth Fourier cutoff of width
> `δ` around `2k^{1/d}` captures all shifts with `h ≲ (δ k^{2−1/d})^{1/2}`; isolating the diagonal
> (`h < 1`) forces `δ < k^{1/d−2}`, i.e. a cutoff whose width must shrink with `k`. That is exactly
> the `α`-integral over a range `A ≍ k^{2−1/d}` — the same object §20.4 showed cannot cross the
> abscissa. Consistent with the shifted-convolution range `|h| ≲ n^{1−1/d}` found in §10.2.

This closes the "extract by frequency" idea, which was the last variant of the constructive route
not previously ruled out explicitly. Recorded so it is not re-attempted.

### 28.3 Positive residue

The holomorphic reformulation `H = Φ_F · \bar G` is worth keeping: it replaces the real-analytic
`|Φ|²` of cycles 5–13 by a genuinely holomorphic object on `H`, to which C6.1 and C7.1 apply
factor-by-factor (singular exponents at a boundary point `−α₀` are `E_F(s) + E_G(s')` when
`α₀ ∈ Spec(F) ∩ Spec(G)`, and `E_F(s)` or `E_G(s')` alone otherwise). In particular the
Cusp–Spectrum Radius Law applies to `H` with `Δ_H(0) = min(min Spec F, min Spec G) = d q^{−1/d}`
when the conductors agree — a further consistency check of the Law.

---

## 29. Cycle 22 (2026-07-25) — preprint assembled

`docs/drafts/pipeline/4-publication-ready/monodromy-integrality-selberg.md` now carries the whole
paper-proved output as a single draft: MI and MI⁺⁺; Theorems 1, 2, 4, 5 and Corollary 3 with proofs;
the list of machine-checked components; and the four obstructions (degree multiplicativity,
linear-moment closure, truncated spectral data, frequency non-isolation) that justify MI as the
right weakening. Open items at the end: MI, (P1), (P2).

The programme's state is stable and fully recorded. A future session should read, in order:
1. §22.2 (the equivalence web) — what implies what;
2. §4, §7, §9.6, §11.1, §20.4, §21.1, §22.1, §26.3, §28.2 — the do-not-retry list;
3. the preprint draft — the standing results;
4. §22.4 / §24.4 — the open directions.

---

## 30. Cycle 23 (2026-07-25) — MI is consistent, with a third derivation of the boundary `Re w = 1/2`

### 30.1 MI holds for automorphic pairs, and the correction factor is exactly the `Re w > 1/2` object

For `F = L(·,π)`, `G = L(·,π')` write `R_{F,G}(w) = L(w, π × \tildeπ') · U(w)`,
`U(w) = ∏_p R_p(w) L_p(w,π×\tildeπ')^{−1}`. Locally,
```
R_p(w)   = 1 + a_F(p)conj(a_G(p)) p^{−w} + O(p^{−2w+ε}),
L_p(w)   = ∏_{i,j}(1 − α_i conj(β_j) p^{−w})^{−1} = 1 + a_F(p)conj(a_G(p)) p^{−w} + O(p^{−2w}),
```
so `R_p/L_p = 1 + O(p^{−2w+ε})` and `Σ_p |R_p/L_p − 1| < ∞` for `Re w > 1/2`. Hence `U` is
**holomorphic and non-vanishing on `Re w > 1/2`**, and MI holds for automorphic pairs by
Jacquet–Piatetski-Shapiro–Shalika.

> **Third independent derivation of the MI⁺⁺ half-plane.** The boundary `Re w = 1/2` is forced by
> the `k ≥ 2` local corrections, exactly as it was forced (i) by the `ζ(2w)^{−1}` factor in the
> newform model (§15.3) and (ii) by the correction bookkeeping of the regularised pairing (§19.3).
> Three unrelated computations give the same half-plane, which is strong evidence that MI⁺⁺ is
> correctly calibrated.

**Corollary (under the polynomial-Euler-product conjecture).** `MI ⟺ the Rankin–Selberg
`L`-function `L(w,π×\tildeπ')` is meromorphic near the 1-line`, since the two differ by `U`, which
is holomorphic and non-vanishing there.

### 30.2 (P1) requires an algebra, not just an integer

Under MI, `n_F = −ord_{w=1}R_{F,F} ∈ Z_{≥0}`. Suppose `F` is primitive with `n_F = k ≥ 2`. In the
automorphic dictionary `n_F = dim End(π)`, and `k ≥ 2` produces a non-trivial idempotent, hence a
decomposition, hence non-primitivity. **The shape of the argument is: `n_F ≥ 2 ⟹ idempotent ⟹
factorisation.** MI supplies only the integer `k`, not the algebra whose dimension it is. So (P1)
needs a Tannakian/endomorphism structure on `S` — i.e. functoriality — and is not reachable from MI
alone. Recorded: **do not attempt (P1) from MI by counting arguments.**

This leaves (P2) as the only one of the two residual ingredients of Corollary 3 that is not
*visibly* equivalent to functoriality — though §9.6 shows the convergence obstruction blocks the
known method there too.

---

## 31. Cycle 24 (2026-07-25) — a Carlson-type attack on (P2), and exactly why it fails

**Attempt.** Assume MI, `F,G` primitive, `n_F = n_G = 1`, and the equality case
`Σ_p |a_F(p) − a_G(p)|²/p = O(1)`, i.e. `κ_{F,G} = 1`. Put
`Δ(w) := R_{F,F}+R_{G,G}−R_{F,G}−R_{G,F} = Σ_n |a_F(n)−a_G(n)|² n^{−w}` — meromorphic (MI) with
**non-negative** coefficients. Its residue at `w=1` is `A + B − 2Re C ≥ (√A−√B)² ≥ 0`
(Cauchy–Schwarz on residues). If that residue vanishes, `Δ` is holomorphic at `w=1`, so by **Landau**
its abscissa is `< 1` and
```
Σ_{n≤x}|a_H(n)|² ≪ x^{1−δ}  ⟹  Σ_{n≤x}|a_H(n)| ≪ x^{1−δ/2}  ⟹  σ_a(H) ≤ 1 − δ/2 < 1,
```
where `H := F − G`. One then hopes for a contradiction: for `σ < 1/2` the functional equation forces
the mean square of `H` to grow like `T^{d(1−2σ)}`, while the coefficient sum
`Σ|a_H(n)|² n^{−2σ}` is finite for `σ > (1−δ)/2 < 1/2`.

**Why it fails.** The two quantities are not the same object in that range. Equating them needs
Carlson's theorem, whose hypothesis is `∫_0^T |H(σ+it)|² dt ≪ T^{1+ε}` — and that is precisely what
the functional-equation growth violates. Below `σ_a(H)` the Dirichlet series is not `H`, so the
finiteness of `Σ|a_H(n)|²n^{−2σ}` says nothing about `H` there. The mean square of `H` is decreasing
in `σ`, finite on the right and infinite on the left: **no contradiction.**

**Recorded:** the Carlson/mean-square route to (P2) is closed. Together with §9.6 (the `ℓ²`
hypothesis gives absolute convergence of `Σ_p c(p)p^{−σ}` only for `σ>1`, so the
Soundararajan/Farmer explicit-formula method never starts), both known approaches to (P2) are now
explicitly ruled out. Any proof of (P2) needs a genuinely new mechanism.

**Positive residue.** The computation does establish, unconditionally on the hypothesis of the
equality case: under MI with `n_F = n_G = 1` and `κ_{F,G} = 1`, either
(a) `Res_{w=1}Δ > 0`, i.e. `Σ_{n≤x}|a_F(n)−a_G(n)|² ≍ x` — the coefficients differ at full density —
or (b) `Res_{w=1}Δ = 0`, forcing `Res R_{F,F} = Res R_{G,G}` and `Res R_{F,G}` equal and positive,
and then `σ_a(F−G) < 1`. **Case (b) is a strong rigidity statement: two distinct primitives with
equal-and-matching Rankin–Selberg residues would have an absolutely convergent difference beyond the
abscissa `1`.** Since `σ_a(F) ≥ 1/2 + 1/(2d_F)` for elements of `S` (K–P, Math. Z. 2017) but no such
lower bound is known for *differences*, case (b) is not yet excluded — it is the sharpest form of
(P2) now available and is the recommended target.

---

## 32. Cycle 25 (2026-07-25) — case (b) of §31 in degree 1; the `S^♯` form of the Radius Law

### 32.1 The Radius Law in `S^♯` (first non-vanishing coefficient)

For `H ∈ S^♯` the normalisation `a_H(1)=1` may fail. Let `m_0 = min{m : a_H(m) ≠ 0}`. Then in the
Stirling computation `|\bar H(1−s)| → |a_H(m_0)| m_0^{σ−1}` as `σ → −∞`, contributing `m_0^{−k/d}`,
so
```
limsup_k |H(s−k/d)/k!|^{1/k} = (q_H/m_0)^{1/d} / (2π d) ,   radius = d (m_0/q_H)^{1/d} = min Spec(H).
```
The Law is therefore self-correcting: both sides shift by `m_0^{1/d}` and continue to agree. (For
`F ∈ S`, `a_F(1)=1` forces `m_0 = 1` and one recovers §24.2.) **Consequence:** the far-left growth
of `H` determines `m_0`, the first non-vanishing coefficient, from the archimedean data.

### 32.2 Case (b) is impossible in degree 1

Recall case (b) of §31: `F ≠ G` primitive with `Res_{w=1}Δ = 0`, forcing `σ_a(F−G) < 1`. Suppose
`d_F = d_G = 1`. By the Kaczorowski–Perelli classification, `F` and `G` are `ζ` or shifts
`L(s+iθ,χ)` with `χ` primitive. If they share a gamma factor, `H := F − G` lies in `S^♯` and its
coefficients are a non-zero periodic function of `n` (a non-trivial linear combination of characters
and shifts), whence `Σ_{n≤x}|a_H(n)| ≍ x` and `σ_a(H) = 1`. Contradiction. If they do not share a
gamma factor, the leading growth of `F` and `G` on the far left differs and `H ≠ 0` cannot be
absolutely convergent past `σ = 1` either. **So (P2) holds in degree 1** — consistent with
Selberg's conjectures being classical there, and a check that the dichotomy of §31 is the right
formulation.

### 32.3 Status of case (b) for `d ≥ 2`

Open. What is needed is: *a non-zero `H ∈ S^♯` of degree `d` has `σ_a(H) = 1`.* Known for `d = 1`
(above). For `F ∈ S` (with Euler product) K–P prove `σ_a(F) ≥ 1/2 + 1/(2d_F)` (Math. Z. 285 (2017)
1345–1355), which is `< 1` for `d ≥ 2` and in any case does not apply to differences, which have no
Euler product. The Radius Law does **not** give a contradiction here (§32.1 shows it self-corrects).

> **Cycle-26 target.** `σ_a(H) = 1` for `0 ≠ H ∈ S^♯`, or a counterexample. Equivalent formulation:
> *can a non-zero element of the extended Selberg class have absolutely convergent Dirichlet series
> in a half-plane `σ > 1 − δ`?* For `d = 1` no. This is a clean, self-contained question about
> `S^♯` — it does not mention Selberg's conjectures — and by §31 it would settle case (b), hence the
> equality case of (P2).

---

## 33. Cycle 26 (2026-07-25) — `σ_a ≥ 1/2` in `S^♯` by a μ-function argument; (P2) is a
pretentious-rigidity statement

### 33.1 Theorem: `σ_a(H) ≥ 1/2` for every non-zero `H ∈ S^♯` of positive degree  [PROVED HERE]

Suppose `σ_a(H) = σ_0 < 1/2`. Then `H` is bounded on `σ ≥ σ_0+ε`, so `μ_H(σ) = 0` there. The
functional equation gives, uniformly in `σ`,
```
μ_H(σ) = d(1/2 − σ) + μ_H(1 − σ).
```
Pick `σ ∈ (σ_0, 1/2)`. Then `1 − σ ∈ (1/2, 1−σ_0) ⊂ (σ_0,∞)`, so `μ_H(1−σ) = 0` and also
`μ_H(σ) = 0`. The displayed identity forces `d(1/2 − σ) = 0`, i.e. `σ = 1/2` — contradicting
`σ < 1/2`. ∎

*Remarks.* (i) The argument uses **no Euler product**, so it applies to differences `F − G` of
elements of `S`, unlike the cycle-1 zero-counting version and unlike K–P's
`σ_a(F) ≥ 1/2 + 1/(2d_F)` for `F ∈ S` (Math. Z. 285 (2017)). Given that K–P's paper is precisely
about the `S` versus `S^♯` distinction for `σ_a`, this `1/2` bound in `S^♯` is likely known;
recorded as **probably known, proof included for self-containedness**.
(ii) The method **stops at `1/2`**: for `σ_a ∈ [1/2,1)` and `σ > σ_a` one has `1−σ < σ_a`, so
`μ_H(1−σ)` is unconstrained and the identity is satisfiable. Case (b) of §31 needs `σ_a ≥ 1` and is
therefore **not** settled by this route.

### 33.2 (P2) is a pretentious-rigidity statement  [OWN reformulation]

The hypothesis of (P2), `Σ_{p≤x}|a_F(p) − a_G(p)|²/p = O(1)`, is exactly the statement that the
Granville–Soundararajan **pretentious distance** between the multiplicative functions `a_F` and
`a_G` is bounded:
```
D(a_F, a_G ; x)² := Σ_{p≤x} ( |a_F(p)|² + |a_G(p)|² − 2 Re( a_F(p) conj(a_G(p)) ) ) / (2p) = O(1).
```

> **(P2) restated.** *Two elements of the Selberg class at bounded pretentious distance are equal.*

This is a genuinely different framing: it places the residual ingredient of Corollary 3 inside
pretentious multiplicative number theory (Halász; Granville–Soundararajan), where "bounded distance"
has strong consequences for mean values — `Σ_{n≤x}a_F(n)` and `Σ_{n≤x}a_G(n)` are then comparable in
the Halász sense. In general bounded distance does **not** force equality (perturb one prime), so any
proof must use the analytic axioms; but the framing supplies a toolbox (Halász's theorem, the
Lipschitz/Granville–Soundararajan structure theorems, the pretentious large sieve) that the programme
has not yet touched and which is *not* blocked by any of the four structural obstructions — those
forbid constructing `R_{F,G}`, whereas pretentious methods work directly with the multiplicative
functions.

> **Cycle-27 target.** Combine: for `F,G ∈ S` with `D(a_F,a_G) = O(1)`, the Perron/convexity
> asymptotic `Σ_{n≤x}a_F(n) = (residue term) + O(x^{1−c(d)})` holds for each of `F,G` separately;
> pretentious theory relates the two partial sums. Look for a contradiction between the
> pretentious comparison and the two independent power-saving asymptotics when `F ≠ G`.

---

## 34. Cycle 27 (2026-07-25) — the pretentious hypothesis propagates by the functional equation, but
not through the strip

### 34.1 What the hypothesis gives on the right, and (by the FE) on the left

Assume `F,G ∈ S` with `D(a_F,a_G) = O(1)`, i.e. `Σ_p |c(p)|²/p < ∞`, `c(p) := a_F(p) − a_G(p)`.
Both are non-vanishing for `σ > 1` (Euler products), so `Q := F/G` and `log Q` are analytic there and
`log Q(s) = Σ_p c(p)p^{−s} + O(1)`. By the mean-value theorem for Dirichlet series,
```
lim_T (2T)^{−1}∫_{−T}^{T} |log Q(σ+it)|² dt = Σ_p |c(p)|² p^{−2σ} + O(1) ≤ Σ_p |c(p)|²/p + O(1) = O(1)
```
**uniformly for `σ > 1`** — the mean square of `log(F/G)` is bounded up to the 1-line.

If moreover `F,G` share gamma factor and root number, then `X_F = X_G` and the functional equations
give `Q(s) = \bar Q(1−s)`: `Q` is self-dual of degree `0`. Hence the same bounded mean square holds
for `σ < 0`.

### 34.2 Why the strip is still closed

The natural next step — Hadamard three-lines for the `L²`-mean of `log Q` between `σ = 1+ε` and
`σ = −ε` — **fails**: `log Q` is not analytic in the strip. It has branch points at every zero of
`F` and of `G`, of which there are `≍ (d/π)T log T` in `[0,T]`. So the bounded mean square does not
propagate to `σ = 1/2`, and the hypothesis does not become a statement about the critical line.

*(Consistency note: had it propagated, one would obtain bounded variance for
`S_F(t) − S_G(t) = π^{−1} Im log Q(1/2+it)`, which is exactly what Selberg's machinery predicts from
`Σ_p|c(p)|²/p < ∞`. So the desired conclusion is true — it just cannot be **derived** this way; the
propagation and the prediction are the same statement, and the strip is where the content sits.)*

### 34.3 Why the Murty–Murty route does not close it either

Murty–Murty: if `D_{F,G}(T) := Σ_ρ |m_F(ρ) − m_G(ρ)| = o(T)` then `F = G`. One would like
"bounded variance of `S_F − S_G`" `⟹` `D_{F,G}(T) = o(T)`. **False as an implication:** a function
with `≫ T` unmatched `±1` jumps in `[0,T]` can still have bounded variance if the `+1` and `−1`
jumps interleave closely. So bounded variance does not by itself bound `D_{F,G}`. Recorded.

### 34.4 Net

The pretentious framing (§33.2) survives as the right language, and it does deliver a genuinely new
*unconditional* statement — bounded mean square of `log(F/G)` on `σ > 1` and (with equal gamma
factors) on `σ < 0` — but the two routes out of it, three-lines and Murty–Murty, are both closed.
The obstruction is again the critical strip: the zeros make `log(F/G)` multivalued exactly where the
information is needed. **This is the same shape as the monodromy obstruction that MI addresses**:
in both cases what is missing is single-valuedness across the region carrying the arithmetic.

> **Cycle-28 note.** That coincidence is worth stating: MI asks for single-valuedness of `R_{F,G}`
> at `w = 1`; §34.2 needs single-valuedness of `log(F/G)` across the critical strip. Both are
> monodromy statements, and both are exactly what the axioms fail to supply. Recorded as the
> unifying description of the residual difficulty of the whole programme.

---

## 35. Cycle 28 (2026-07-25) — the degree-0 route: (P2) reduces to a holomorphy statement

### 35.1 The quotient has a degree-0 functional equation

If `F,G ∈ S` share gamma factor and root number, dividing their functional equations gives
```
Q(s) := F(s)/G(s)  satisfies  Q(s) = \bar Q(1−s) ,
```
a functional equation of **degree 0** with trivial gamma factor and root number `1`. `Q` is
meromorphic of finite order, has an Euler product `∏_p F_p/G_p`, and `log Q = log F − log G` has
coefficients `b_F(n) − b_G(n) ≪ n^θ`, `θ < 1/2` — so the Euler-product axiom holds for `Q`.

### 35.2 Ramanujan holds for `Q` under PEP

If `F,G` have polynomial Euler products with Ramanujan-bounded roots, then
`F_p/G_p = ∏_j(1 − β_j x) / ∏_i(1 − α_i x)` with `|α_i|,|β_j| ≤ 1`, whose Taylor coefficients are
`≪ k^{d−1}`; hence `a_Q(n) ≪_ε n^ε` and `σ_a(Q) ≤ 1`. **So axioms (1), (3), (4), (5) all hold for
`Q`.**

### 35.3 The only failing axiom is (2), and that is exactly the division problem

`Q = F/G` has a **pole at every zero of `G`** that is not a zero of `F`. So axiom (2) — `(s−1)^m Q`
entire — fails unless `F` vanishes on the zero set of `G` to at least the same order, i.e. unless
`F/G` is entire. This is precisely the Artin-holomorphy-shaped "division problem" already flagged in
cycle 1.

> **Reduction (own).** Under the polynomial Euler product conjecture, for `F,G ∈ S` with equal gamma
> factor and root number:
> ```
> F/G entire   ⟹   F/G ∈ S^♯ with degree 0   ⟹   F/G is a Dirichlet polynomial (K–P degree-0
> classification)   ⟹   F and G differ at only finitely many primes   ⟹   F = G
> ```
> (the last step by comparing conductors: a non-trivial finite Euler factor changes `q`). Hence
> **(P2) ⟸ PEP + "the quotient of two equal-conductor elements of `S` is entire".**

### 35.4 Placement

This is the third distinct reduction of (P2) found in the programme —
(a) explicit-formula/strong-multiplicity-one (§9.6, blocked by convergence),
(b) Carlson/mean-square (§31, blocked because the Carlson hypothesis fails),
(c) degree-0 quotient (here, blocked by holomorphy of `F/G`).
All three terminate in a statement of Artin-holomorphy type, which is the same hard core as
functoriality. Recorded: **(P2) is not an independent ingredient — it is equivalent, in every
formulation found, to a division/holomorphy statement.** Corollary 3's decomposition
`B ⟸ MI + (P1) + (P2)` therefore has both residual ingredients now identified with the
functoriality core: (P1) needs the endomorphism algebra (§30.2), (P2) needs holomorphy of quotients.

> **Consequence for the programme.** MI is the only one of the three that is *not* visibly
> equivalent to functoriality: it asks solely for single-valuedness, and §30.1 shows it is implied by
> automorphy but not obviously equivalent to it. MI therefore remains the single most valuable open
> statement produced here.

---

## 36. Cycle 29 (2026-07-25) — an EXPLICIT Rankin–Selberg object built from the axioms, with
positivity  [OWN — best construction of the programme]

### 36.1 The identity that makes it possible

For a polynomial Euler product `F_p(x)^{-1} = ∏_i(1 − α_i x)` one has `log F_p(x) = Σ_k b_F(p^k)x^k`
with `b_F(p^k) = (1/k)Σ_i α_i^k`, i.e. `Σ_i α_i^k = k·b_F(p^k)`. Therefore
```
log L(w, π × \tildeπ) = Σ_p Σ_{k≥1} (1/k) | Σ_i α_i^k |² p^{−kw}
                      = Σ_p Σ_{k≥1} k · | b_F(p^k) |² · p^{−kw} .
```
**The right-hand side involves only `b_F(p^k)` — data supplied directly by the Selberg Euler-product
axiom.** No Satake parameters, no polynomial Euler product, no functoriality.

### 36.2 Definition and basic properties  [PROVED HERE]

For `F ∈ S` define
```
𝔏_F(w) := Σ_{p} Σ_{k≥1} k |b_F(p^k)|² p^{−kw} ,        ℛ_F(w) := exp( 𝔏_F(w) ) .
```

1. **`𝔏_F` has non-negative coefficients**, and so does `ℛ_F` (exponential of a non-negative
   Dirichlet series).
2. **`𝔏_F(w) = Σ_p |a_F(p)|² p^{−w} + (holomorphic on Re w > 2θ)`**: the `k=1` terms are
   `|b_F(p)|² = |a_F(p)|²` and converge for `Re w > 1` (Ramanujan); the `k ≥ 2` terms are
   `≪ k p^{k(2θ − Re w)}`, convergent for `Re w > 2θ`, and `2θ < 1`.
3. **`σ_a(ℛ_F) ≤ 1`**: split `ℛ_F = exp(Σ_p|a_F(p)|²p^{−w}) · H(w)` with `H` holomorphic and
   non-vanishing on `Re w > 2θ`; the first factor has coefficients `∏ A_{p_i}^{k_i}/k_i! ≪_ε n^ε`
   by Ramanujan.
4. **`ℛ_F` agrees with `R_{F,F}` up to a harmless factor:** `log R_{F,F} − 𝔏_F = Σ_p O(p^{−2w+max(ε,2θ)})`
   converges for `Re w > 1/2 + θ < 1`, so the ratio is holomorphic and non-vanishing there.
5. **When `F` is automorphic with a polynomial Euler product, `ℛ_F(w) = L(w, π × \tildeπ)`.**

> **Consequence.** `MI` (for the diagonal) `⟺` `ℛ_F` **is meromorphic at `w = 1`** — where `ℛ_F` is
> now an *explicitly constructed* Dirichlet series with non-negative coefficients whose logarithm
> also has non-negative coefficients. This is the first time in the programme that the
> Rankin–Selberg object is written down from the axioms rather than postulated.

### 36.3 Why this evades the four obstructions

- §9.1 (separately-linear constructions add degrees): `𝔏_F` is **quadratic** in `b_F`, not
  separately linear. Not blocked.
- §10.1 (only linear prime moments are available): `𝔏_F` is built from `b_F(p^k)` for **all** `k`,
  which the Euler-product axiom supplies; the quadratic combination is formed *pointwise at each
  prime power*, not by pairing two elements of `S`. Not blocked.
- §20.4 (truncated spectral data): no spectral truncation is used. Not blocked.
- §28.2 (frequency non-isolation): no frequency extraction is used. Not blocked.

### 36.4 What is now unconditionally available

Because `log ℛ_F` has non-negative coefficients, the **Mertens 3–4–1 inequality holds
unconditionally**:
```
3 log ℛ_F(σ) + 4 Re log ℛ_F(σ+it) + Re log ℛ_F(σ+2it) ≥ 0     (σ > 1),
i.e.  ℛ_F(σ)³ |ℛ_F(σ+it)|⁴ |ℛ_F(σ+2it)| ≥ 1 .
```
For the *classical* consequence (non-vanishing on `Re w = 1`) one still needs continuation; but the
inequality itself is a genuinely new unconditional tool for `S`, and it is exactly the input that
makes the Wiener–Ikehara step of cycle-1 Theorem 1 available once continuation is granted.

> **Cycle-30 target.** Prove `ℛ_F` continues meromorphically to a neighbourhood of `w = 1`. The
> object is now explicit and positive, which brings Tauberian and positivity machinery (Landau,
> Mertens, Ikehara) into play for the first time. Landau already gives: `w = σ_c(ℛ_F)` **is** a
> singularity; the content is that it is a **pole**.

---

## 37. Cycle 30 (2026-07-25) — correction to §36.2, and the exact limit of positivity

### 37.1 CORRECTION to §36.2(2)

The claim "the `k ≥ 2` terms converge for `Re w > 2θ`" conflated the `k`-sum with the `p`-sum. Using
only the Euler-product bound `|b_F(p^k)| ≪ p^{kθ}`, the `k=2` term is `≍ p^{2(2θ−Re w)}` and
`Σ_p p^{2(2θ−Re w)}` converges only for `Re w > 2θ + 1/2`, which exceeds `1` once `θ ≥ 1/4`.

**Repaired proof.** Use **Ramanujan** instead: `b_F(p^k)` is a universal polynomial (Newton
relations) in `a_F(p),…,a_F(p^k)` with `≍ e^{c√k}` terms, each of total degree `≤ k`, so
`|b_F(p^k)| ≪ C_ε^{k} p^{kε}`. Then the `k=2` term is `≪ p^{4ε − 2Re w}` and `Σ_p` converges for
`Re w > 1/2 + 2ε`; the `k ≥ 3` terms converge for `Re w > 1/2` once `p` is large, and for each fixed
small `p` the `k`-sum converges for `Re w > 2θ` by the Euler-product bound. Hence
```
𝔏_F(w) − Σ_p |a_F(p)|² p^{−w}   is holomorphic on   Re w > max(1/2, 2θ) ,
```
and `max(1/2, 2θ) < 1` because `θ < 1/2`. **The conclusion of §36.2 stands**, with the region
`Re w > max(1/2, 2θ)` in place of `Re w > 2θ`. All downstream statements (§36.2(3),(4), §36.3,
§36.4) are unaffected.

### 37.2 Positivity alone cannot prove MI — an explicit witness

Is there a theorem "non-negative coefficients + non-negative log-coefficients + abscissa 1 ⟹
meromorphic at `w=1`"? **No.** Take
```
ℛ(w) = exp( Σ_p (1/2) p^{−w} ) = ζ(w)^{1/2} · (holomorphic, non-vanishing on Re w > 1/2) .
```
Both `ℛ` and `log ℛ` have non-negative coefficients, the abscissa is `1`, and `ℛ` has a **branch
point** at `w=1`. So Landau + Mertens + Ikehara cannot suffice: MI needs input beyond positivity.
Recorded — this closes the "positivity route" opened in §36.4.

### 37.3 The sharpest concrete form of Conjecture A

The witness in §37.2 is realised as `ℛ_F` precisely when `|a_F(p)|² = 1/2` for all `p`. Hence:

> **Test case.** *Can an element `F ∈ S` satisfy `|a_F(p)| = 1/√2` for every prime `p`?*
> If yes, `n_F = 1/2 ∉ Z` and Selberg's Conjecture A is **false**. If no — and more generally if
> `Σ_{p≤x}|a_F(p)|²/p` cannot have a non-integral density — Conjecture A holds.

This is the most concrete formulation the programme has reached: a single, checkable question about
the possible sizes of the prime coefficients of a Selberg-class element, with the disproof of
Conjecture A as one of its two outcomes. Note that Theorem 4 (§ cycle 1) already shows axioms
(1),(4),(5) alone permit wild `|a_F(p)|`; what must be shown is that the **continuation and
functional equation** forbid the value `1/√2` (and every other non-integral mean square).

> **Cycle-31 target.** Attack the test case directly: assume `F ∈ S` with `|a_F(p)| = c` constant
> for all `p`, and derive a contradiction from the functional equation unless `c² ∈ Z`. The
> constant-modulus hypothesis is a drastic simplification — `ℛ_F(w) = ζ(w)^{c²}·H(w)` exactly, with
> `H` holomorphic non-vanishing on `Re w > max(1/2,2θ)` — so `F`'s own Dirichlet series is
> "`ζ^{c²}`-pretentious", and the Selberg–Delange machinery gives
> `Σ_{n≤x}|a_F(n)|² ~ C x (log x)^{c²−1}`. The question is whether a degree-`d` functional equation
> can coexist with a non-integral exponent `c²`.

---

## 38. Cycles 31–32 (2026-07-25) — the pretentious/Halász attack on the test case: two dead ends

### 38.1 The Landau power saving vs. Halász — DEAD END

For entire `F ∈ S`, Perron plus the convexity bound `μ_F(σ) ≤ (d/2)(1−σ)` gives the classical
Landau saving
```
Σ_{n≤x} a_F(n) ≪ x^{d/(d+2)+ε} .
```
Attempted contradiction with the test case `|a_F(p)| = c`: Halász's theorem for multiplicative `f`
gives `x^{−1}|Σ_{n≤x}f(n)| ≪ (1+m)e^{−m} + (log x)^{−1/2}` with `m = min_{|t|≤T} D(f,n^{it};x)²`, and
`m ≪ log log x` always (since `Σ_p(1+|f(p)|)/p ≍ log log x`). One hopes the mean is then forced to be
`≫ x(log x)^{−A}`, contradicting the power saving.

**Dead end.** Halász's theorem is an **upper** bound with a floor of `(log x)^{−1/2}`; it never
forces a mean to be large. A power saving is simply "beyond Halász" and carries no pretentious
information. (Sanity check: `F = L(·,f)` for a cusp form has `|a_f(p)| ≤ 2` bounded *and*
`Σ_{n≤x}a_f(n) ≪ x^{1/3+ε}` — a genuine power saving with bounded prime coefficients. So no such
contradiction can exist.) Recorded; do not retry.

### 38.2 Local obstructions to the test case — NONE

`|a_F(p)| = c` for all `p` has **no local obstruction**: with a polynomial Euler product of local
degree `∂_p` and `|α_i| ≤ 1`, any `c ≤ ∂_p` is attainable, and Ramanujan at `p²` only gives
`|a_F(p)|²/2 = |a_F(p²) − b_F(p²)| ≪ p^{2θ}`, which is vacuous. So the test case must be excluded
**globally**, by the continuation or the functional equation — consistent with Theorem 4.

### 38.3 The self-referential exits

- Under MI, `c² = n_F ∈ Z` immediately — circular.
- The conjugate pairing `Σ_p a_F(p)²/p = c² Σ_p e^{2iφ_p}/p` is controlled by MI for `(F,\bar F)`,
  again circular.
- With a polynomial Euler product, `c² = ∫|tr|²` over the Satake data, and integrality is Schur's
  lemma — i.e. it needs the compact group. Circular.

**Net.** The test case `|a_F(p)| ≡ 1/√2` (§37.3) is the sharpest concrete form of the problem, it has
no local obstruction, and every route to excluding it found so far is either circular or blocked by
one of the recorded structural obstructions. It stands as the recommended focal point: *a single
explicit question whose resolution decides Selberg's Conjecture A.*
